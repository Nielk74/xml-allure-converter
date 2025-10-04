"""
JUnit XML -> Allure Results converter (minimal but practical)

Usage:
  python junit_xml_to_allure.py --input junit-xml-dir --output allure-results \
      [--suite-split " / "] [--default-parent "Tests"] [--framework-name "junit-xml"]

What it does
- Reads .xml files that contain <testsuites>/<testsuite>/<testcase>.
- Emits Allure result files into --output (test-result.json & test-container.json),
  plus optional executor.json.
- Builds hierarchy using Allure labels (parentSuite/suite/subSuite, package/testClass/testMethod).
- Maps failures/errors/skips to Allure "status" and statusDetails.
- Derives start/stop timestamps (ms) from time attributes if present; otherwise uses now().
- Optionally maps certain <property> elements to labels/links/parameters with a simple convention.

python3 junit_xml_to_allure.py --input xml/myTest.xml --output allure-results --write-exe
cutor
allure generate allure-results --clean -o allure-report
allure open allure-report
Tested with Python 3.8+ and plain ElementTree (no external deps).

"""

import argparse
import json
import os
import re
import time
import uuid
import hashlib
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Dict, List, Tuple, Optional

# ----------------------------- Helpers -----------------------------

def ms_now() -> int:
    return int(time.time() * 1000)

def stable_hash(s: str) -> str:
    """Return a stable short-ish hexadecimal hash for historyId."""
    return hashlib.md5(s.encode("utf-8")).hexdigest()

def split_classname(classname: str) -> Tuple[str, str]:
    """Split fully-qualified classname into (package, class)."""
    if not classname:
        return ("", "")
    if "." in classname:
        pkg, cls = classname.rsplit(".", 1)
        return (pkg, cls)
    return ("", classname)

def derive_suite_labels(ts_name: str, sep: str, default_parent: str) -> List[Dict[str,str]]:
    """
    Derive parentSuite/suite/subSuite from testsuite name.
    Examples:
      name="Web / Checkout / Cart" with sep=" / " => parentSuite=Web, suite=Checkout, subSuite=Cart
      name="Checkout" => parentSuite=default_parent, suite=Checkout
    """
    labels = []
    parts = [p.strip() for p in ts_name.split(sep)] if ts_name else []
    if len(parts) >= 3:
        labels.append({"name":"parentSuite","value":parts[0]})
        labels.append({"name":"suite","value":parts[1]})
        labels.append({"name":"subSuite","value":sep.join(parts[2:])})
    elif len(parts) == 2:
        labels.append({"name":"parentSuite","value":parts[0]})
        labels.append({"name":"suite","value":parts[1]})
    elif len(parts) == 1 and parts[0]:
        labels.append({"name":"parentSuite","value":default_parent})
        labels.append({"name":"suite","value":parts[0]})
    # If empty, skip; Allure will still show Packages tree.
    return labels

def map_status(tc_elem: ET.Element) -> Tuple[str, Dict[str,str]]:
    """
    Inspect <failure>, <error>, <skipped> to compute Allure status and statusDetails.
    Prefers 'failed' over 'broken' for <failure>; uses 'broken' for <error>.
    """
    failure = tc_elem.find("failure")
    error = tc_elem.find("error")
    skipped = tc_elem.find("skipped")
    details = {}
    if failure is not None:
        msg = (failure.get("message") or "").strip()
        text = (failure.text or "").strip()
        details = {"message": msg, "trace": text}
        return "failed", details
    if error is not None:
        msg = (error.get("message") or "").strip()
        text = (error.text or "").strip()
        details = {"message": msg, "trace": text}
        return "broken", details  # 'error' -> 'broken' in Allure semantics
    if skipped is not None:
        msg = (skipped.get("message") or skipped.get("type") or "").strip()
        text = (skipped.text or "").strip()
        details = {"message": msg, "trace": text}
        return "skipped", details
    return "passed", {}

def to_ms(seconds_str: Optional[str]) -> Optional[int]:
    try:
        if seconds_str is None:
            return None
        return int(float(seconds_str) * 1000.0)
    except Exception:
        return None

def testcase_timing(tc: ET.Element, suite_start_ms: int) -> Tuple[int, int]:
    """
    Derive start/stop for a testcase.
    If <testcase time="s"> exists, add to suite_start for stop.
    Otherwise, set short duration of 1ms.
    """
    duration = to_ms(tc.get("time"))
    if duration is None:
        start = suite_start_ms
        stop = max(start + 1, start)  # ensure > 0 duration
    else:
        start = suite_start_ms
        stop = start + duration
    return start, stop

def collect_properties(tc: ET.Element) -> Dict[str,str]:
    props = {}
    props_elem = tc.find("properties")
    if props_elem is not None:
        for p in props_elem.findall("property"):
            name = p.get("name")
            value = p.get("value")
            if name:
                props[name] = value or ""
    return props

def map_properties_to_labels_links_params(props: Dict[str,str]) -> Tuple[List[Dict[str,str]], List[Dict[str,str]], List[Dict[str,str]]]:
    """
    Simple convention to enrich hierarchy/metadata from <properties>:
      - label: "allure.label.X" => {"name":"X","value":value}
      - link:  "allure.link.ISSUE" => {"name":"ISSUE","url":value}
      - param: "allure.param.foo" => {"name":"foo","value":value}
    This lets you drive epic/feature/story/etc. from plain JUnit XML.
    """
    labels, links, params = [], [], []
    for k, v in props.items():
        if k.startswith("allure.label."):
            labels.append({"name": k[len("allure.label.") :], "value": v})
        elif k.startswith("allure.link."):
            links.append({"name": k[len("allure.link.") :], "url": v})
        elif k.startswith("allure.param."):
            params.append({"name": k[len("allure.param.") :], "value": v})
    return labels, links, params

# ----------------------------- Core conversion -----------------------------

def convert_file(xml_path: Path, out_dir: Path, suite_sep: str, default_parent: str, framework_name: str) -> None:
    tree = ET.parse(xml_path)
    root = tree.getroot()

    # Normalize possible top-level <testsuite> vs <testsuites>
    suites = []
    if root.tag == "testsuite":
        suites = [root]
    elif root.tag == "testsuites":
        suites = list(root.findall("testsuite"))
    else:
        # Try to be resilient (some producers wrap differently)
        suites = list(root.findall(".//testsuite"))

    for ts in suites:
        ts_name = ts.get("name") or xml_path.stem
        suite_uuid = str(uuid.uuid4())
        suite_start = ms_now()

        container = {
            "uuid": suite_uuid,
            "name": ts_name,
            "children": [],
            "befores": [],
            "afters": [],
            "links": [],
            "start": suite_start,
            "stop": suite_start,  # will be updated as we add tests
        }

        # derive common suite labels
        suite_labels = derive_suite_labels(ts_name, suite_sep, default_parent)

        # Optional: suite-level properties -> labels/links/params (rare in JUnit XML)
        suite_props = {}
        sp = ts.find("properties")
        if sp is not None:
            for p in sp.findall("property"):
                name = p.get("name"); value = p.get("value") or ""
                if name: suite_props[name] = value
        sp_labels, sp_links, _ = map_properties_to_labels_links_params(suite_props)

        last_stop = suite_start
        for tc in ts.findall("testcase"):
            classname = tc.get("classname") or ""
            name = tc.get("name") or "test"
            pkg, cls = split_classname(classname)
            method = name

            status, statusDetails = map_status(tc)
            start, stop = testcase_timing(tc, last_stop or suite_start)
            last_stop = stop

            # Params from <properties> under <testcase>
            props = collect_properties(tc)
            p_labels, p_links, params = map_properties_to_labels_links_params(props)

            # Allure required-ish fields
            tr_uuid = str(uuid.uuid4())
            full_name = ".".join([x for x in [pkg, cls, method] if x])
            history_id = stable_hash(full_name or (classname + "::" + name))

            labels = [
                {"name":"framework","value":framework_name},
                {"name":"language","value":"unknown"},
            ]

            # Package hierarchy
            if pkg: labels.append({"name":"package","value":pkg})
            if cls: labels.append({"name":"testClass","value":cls})
            if method: labels.append({"name":"testMethod","value":method})

            # Suite hierarchy
            labels.extend(suite_labels)

            # Optional suite/test labels from properties
            labels.extend(sp_labels)
            labels.extend(p_labels)

            result = {
                "uuid": tr_uuid,
                "historyId": history_id,
                "name": method,
                "fullName": full_name or method,
                "status": status,
                "statusDetails": statusDetails,
                "stage": "finished",
                "steps": [],
                "attachments": [],
                "parameters": params,
                "labels": labels,
                "links": sp_links + p_links,
                "start": start,
                "stop": stop,
            }

            # Write test-result.json
            with open(out_dir / f"{tr_uuid}-result.json", "w", encoding="utf-8") as f:
                json.dump(result, f, ensure_ascii=False, indent=2)

            # Add to container
            container["children"].append(tr_uuid)
            container["stop"] = max(container["stop"], stop)

        # Write test-container.json
        with open(out_dir / f"{suite_uuid}-container.json", "w", encoding="utf-8") as f:
            json.dump(container, f, ensure_ascii=False, indent=2)

def write_executor(out_dir: Path, name: str = "XML Converter", type_: str = "other") -> None:
    executor = {
        "name": name,
        "type": type_,
        "buildName": "",
        "buildUrl": "",
        "reportUrl": "",
    }
    with open(out_dir / "executor.json", "w", encoding="utf-8") as f:
        json.dump(executor, f, ensure_ascii=False, indent=2)

def find_xml_files(input_path: Path) -> List[Path]:
    if input_path.is_file() and input_path.suffix.lower() == ".xml":
        return [input_path]
    return sorted(input_path.rglob("*.xml"))

def main():
    ap = argparse.ArgumentParser(description="Convert JUnit XML to Allure results JSON.")
    ap.add_argument("--input", required=True, help="JUnit XML file or directory")
    ap.add_argument("--output", required=True, help="Output directory for allure-results")
    ap.add_argument("--suite-split", default=" / ", help="Separator to split testsuite name into parent/suite/subSuite")
    ap.add_argument("--default-parent", default="Tests", help="Default parentSuite if testsuite has a single name part")
    ap.add_argument("--framework-name", default="junit-xml", help="Label value for framework")
    ap.add_argument("--write-executor", action="store_true", help="Also write executor.json")
    args = ap.parse_args()

    in_path = Path(args.input)
    out_dir = Path(args.output)
    out_dir.mkdir(parents=True, exist_ok=True)

    files = find_xml_files(in_path)
    if not files:
        print("No XML files found.", file=sys.stderr)
        sys.exit(2)

    for p in files:
        convert_file(p, out_dir, suite_sep=args.suite_split, default_parent=args.default_parent, framework_name=args.framework_name)

    if args.write_executor:
        write_executor(out_dir)

    print(f"Wrote Allure results to: {out_dir.resolve()}")

if __name__ == "__main__":
    main()
