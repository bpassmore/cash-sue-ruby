import os
import json
import logging
from datetime import datetime, timezone
import re
import fnmatch
import statistics
from collections import Counter
import subprocess

# Version History:
# Version 1.0: Initial code base as provided, with basic pattern matching, truncation handling, fuzzy title matching via Levenshtein, and rename logic. Includes user input for directory and dry-run mode.
# Version 1.1: Added strict extension matching in is_matching_title to ensure title ends with expected_ext (e.g., to distinguish .MOV vs .MP4).
# Version 1.2: Introduced used_jsons set to track assigned JSONs and prevent double-assignment in duplicate scenarios.
# Version 1.3: Added sorting of media_files with custom_media_sort to process non-duplicates before duplicates, ensuring base files claim JSONs first.
# Version 1.4: Pre-filtered json_files list in process_directory to reduce os.listdir calls inside find_misnamed_json, improving speed.
# Version 1.5: Adjusted expected_title to exclude num_suffix (as titles often omit it), and refined patterns/candidates to better handle duplicate numbering in JSON names.
# Version 1.6: Optimized truncation loops by stepping -5 in length range for faster execution on large directories, while maintaining accuracy.
# Version 1.7: Added version history comments at top, with VERSION variable logged at start.
# Version 1.8: Merged with alternate branch: Tightened fuzzy matching thresholds to reduce false positives; added media sorting and used_jsons prevention; pre-lowercasing for efficiency; case-insensitive JSON filtering; dry-run used marking; syntax fixes.
# Version 1.9: Added optional pre-analysis phase for dynamic tuning (suffix priority, truncation step) based on dataset stats, for auto-optimization across exports without accuracy loss.
# Version 2.0: Merged metadata embedding (from exif-work.py) into a 1-step workflow: Optional pre-analysis, rename JSONs, then optional embed/verify with exiftool. Added prompts for embed and backups (default no backup). Dry-run supports all steps with logging only.
# Version 2.1: Fixed NameError for create_backup when embed=n (set default False early); clarified logging for embed prompt in dry-run.
# Version 2.2: Fixed NameError for pre_analyze by ensuring function definition order; minor log improvements for clarity.
# Version 2.3: Fixed dry-run embed errors by skipping JSON open and actual embed logic in dry-run (log "Would embed" only); ensured preferred_path used correctly after simulated rename; removed stray exiftool log.
# Version 2.4: Fixed extra embed logs for base files in duplicates; clarified dry-run embed logs (e.g., "from simulated renamed path"); ensured embed only triggers after successful (simulated) rename.
# Version 2.5: Restored missing custom_media_sort function and applied it to media_files sorting (from v1.3/v1.8) to prioritize non-duplicates.
# Version 2.6: Fixed UnicodeDecodeError by using encoding='utf-8', errors='ignore' in subprocess.run. Added pre-embed check to rename misnamed .HEIC (actually JPEG) to .JPG. Improved verify_embed: use utcfromtimestamp for dates, float tolerance (1e-6) for GPS, handle empty exiftool output, log mismatch details.
# Version 2.7: Added JSON title caching per directory to avoid repeated file reads in find_misnamed_json, improving performance.

VERSION = "2.7"

# Setup logging to file with real-time flushing
timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
log_file = f'rename_and_embed_log_{timestamp}.txt'
logging.basicConfig(filename=log_file, level=logging.INFO, format='%(asctime)s - %(message)s', filemode='w')
logger = logging.getLogger(__name__)
handler = logging.getLogger().handlers[0]
handler.flush = lambda: handler.stream.flush()  # Ensure real-time flushing
logger.info(f"Script started. Running version {VERSION}. Logging renames and embeds in real time.")

def levenshtein_distance(s1, s2):
    if len(s1) < len(s2):
        return levenshtein_distance(s2, s1)
    if len(s2) == 0:
        return len(s1)
    previous_row = range(len(s2) + 1)
    for i, c1 in enumerate(s1):
        current_row = [i + 1]
        for j, c2 in enumerate(s2):
            insertions = previous_row[j + 1] + 1
            deletions = current_row[j] + 1
            substitutions = previous_row[j] + (c1 != c2)
            current_row.append(min(insertions, deletions, substitutions))
        previous_row = current_row
    return previous_row[-1]

def common_prefix_len(a, b):
    return sum(1 for x, y in zip(a, b) if x == y)

def is_matching_title(title, expected_title, expected_ext):
    t = title.lower()
    e = expected_title.lower()
    dist = levenshtein_distance(t, e)
    cp_len = common_prefix_len(t, e)
    len_diff = abs(len(t) - len(e))
    if len(e) >= 30:
        max_dist = int(len(e) * 0.15)  # Tightened from 0.2 to reduce false positives
        max_len_diff = int(len(e) * 0.25)  # Tightened from 0.3
        min_cp = int(len(e) * 0.85)  # Tightened from 0.8 for stricter prefix match
        if not t.endswith(expected_ext.lower()):
            return False  # Require exact extension match in title
        return dist <= max_dist and cp_len >= min_cp and len_diff <= max_len_diff
    else:
        if not t.endswith(expected_ext.lower()):
            return False
        return dist <= max(2, len_diff) and cp_len >= int(len(min(t, e)) * 0.85)  # Tightened from max(3, len_diff) and 0.8 for short titles

def is_media_file(filename):
    extensions = {'.jpg', '.jpeg', '.png', '.gif', '.bmp', '.tiff', '.heic', '.heif', '.mp4', '.mov', '.avi'}
    return os.path.splitext(filename)[1].lower() in extensions

def parse_duplicate_number(name):
    match = re.match(r'^(.*?)(\(\d+\))?$', name)
    if match:
        base = match.group(1).strip()
        num_suffix = match.group(2) or ''
        return base, num_suffix
    return name, ''

def get_json_title(json_path):
    try:
        with open(json_path, 'r', encoding='utf-8') as f:
            data = json.load(f)
            return data.get('title', '')
    except Exception as e:
        logger.error(f"Error reading JSON title from {json_path}: {e}")
        return ''

def load_json_titles(dir_path, json_files):
    cache = {}
    for jf in json_files:
        json_path = os.path.join(dir_path, jf)
        cache[jf] = get_json_title(json_path)
    return cache

def extract_suffix(filename):
    base, ext = os.path.splitext(filename)
    if ext.lower() == '.json':
        parts = base.split('.')
        if len(parts) > 1:
            return '.'.join(parts[1:])
    return None

def pre_analyze(root_dir):
    filename_lengths = []
    json_suffixes = Counter()
    subdir_count = 0
    total_jsons = 0

    for subdir, _, files in os.walk(root_dir):
        subdir_count += 1
        json_files = [f for f in files if f.lower().endswith('.json')]
        total_jsons += len(json_files)
        filename_lengths.extend(len(f) for f in files[:1000])  # Sample per dir for speed

        for jf in json_files:
            suffix = extract_suffix(jf)
            if suffix:
                json_suffixes[suffix] += 1

    if filename_lengths:
        avg_len = statistics.mean(filename_lengths)
        median_len = statistics.median(filename_lengths)
    else:
        avg_len = median_len = 30  # Default fallback

    # Dynamic: Top common suffixes + core fallbacks
    core_variants = ['supplemental-metadata', 'metadata', 'suppl']  # Always include
    common_variants = [s for s, _ in json_suffixes.most_common(10) if s not in core_variants]
    suffix_variants = core_variants + common_variants

    # Dynamic step: Larger for longer avgs, capped for accuracy
    min_prefix_factor = 0.7 if avg_len < 50 else 0.75
    step_divisor = 15 if avg_len < 50 else 10  # Coarser for long names
    logger.info(f"Pre-analysis: Subdirs={subdir_count}, JSONs={total_jsons}, Avg len={avg_len:.2f}, Suffixes={suffix_variants}")
    handler.flush()

    return suffix_variants, avg_len, min_prefix_factor, step_divisor

def find_misnamed_json(dir_path, base_name, media_ext, num_suffix, json_files, json_titles, used_jsons, suffix_variants, avg_len, min_prefix_factor, step_divisor):
    full_prefix = base_name + media_ext
    expected_title = base_name + media_ext  # For duplicates, title may lack num_suffix
    expected_title_lower = expected_title.lower()
    
    patterns = []
    for suffix in suffix_variants:
        patterns.extend([
            f"{base_name}{media_ext}.{suffix}{num_suffix}.json",
            f"{base_name}{media_ext}.{suffix}.json",
            f"{base_name}.{suffix}{num_suffix}.json",
            f"{base_name}.{suffix}.json"
        ])
    patterns.append(f"{base_name}{media_ext}.*metadata{num_suffix}*.json")
    patterns.append(f"{base_name}{media_ext}.*metadata*.json")
    patterns.append(f"{base_name}{media_ext}.*.json")
    patterns.append(f"{base_name}.*metadata{num_suffix}*.json")
    patterns.append(f"{base_name}.*metadata*.json")
    patterns.append(f"{base_name}.*.json")
    
    candidates = []
    for pattern in patterns:
        for file in json_files:
            if fnmatch.fnmatch(file.lower(), pattern.lower()):
                json_path = os.path.join(dir_path, file)
                if json_path in used_jsons:
                    continue
                title = json_titles.get(file, '')
                title_lower = title.lower()
                if title_lower == expected_title_lower:
                    return json_path
                dist = levenshtein_distance(title_lower, expected_title_lower)
                candidates.append((json_path, title, dist))
    
    for json_path, title, dist in candidates:
        if is_matching_title(title, expected_title, media_ext):
            return json_path

    # Truncated base
    min_prefix_length = max(20, int(len(base_name) * min_prefix_factor))
    step = max(1, (len(base_name) - min_prefix_length) // step_divisor)
    for length in range(len(base_name), min_prefix_length - 1, -step):
        truncated_prefix = base_name[:length]
        pattern = f"{truncated_prefix}*.json"
        for file in json_files:
            if fnmatch.fnmatch(file.lower(), pattern.lower()):
                json_path = os.path.join(dir_path, file)
                if json_path in used_jsons:
                    continue
                title = json_titles.get(file, '')
                if title.lower() == expected_title_lower:
                    return json_path
                if is_matching_title(title, expected_title, media_ext):
                    return json_path

    # Truncated full_prefix
    min_prefix_length = max(20, int(len(full_prefix) * min_prefix_factor))
    step = max(1, (len(full_prefix) - min_prefix_length) // step_divisor)
    for length in range(len(full_prefix), min_prefix_length - 1, -step):
        truncated_prefix = full_prefix[:length]
        pattern = f"{truncated_prefix}*.json"
        for file in json_files:
            if fnmatch.fnmatch(file.lower(), pattern.lower()):
                json_path = os.path.join(dir_path, file)
                if json_path in used_jsons:
                    continue
                title = json_titles.get(file, '')
                if title.lower() == expected_title_lower:
                    return json_path
                if is_matching_title(title, expected_title, media_ext):
                    return json_path
    
    return None

def run_exiftool(args, dry_run=False):
    cmd = ['exiftool'] + args
    if dry_run:
        logger.info(f"DRY-RUN: Would execute exiftool with command: {' '.join(cmd)}")
        handler.flush()
        return None
    try:
        result = subprocess.run(cmd, check=True, capture_output=True, text=True, encoding='utf-8', errors='ignore')
        logger.info(f"exiftool executed: {result.stdout.strip()}")
        handler.flush()
        return result
    except subprocess.CalledProcessError as e:
        logger.error(f"exiftool failed: {e.stderr}")
        handler.flush()
        raise
    except FileNotFoundError:
        logger.error("exiftool not found. Please install it and ensure it's in PATH.")
        handler.flush()
        raise

def verify_embed(media_path, json_data):
    try:
        cmd = ['exiftool', '-json', media_path]
        result = subprocess.run(cmd, check=True, capture_output=True, text=True, encoding='utf-8', errors='ignore')
        if not result.stdout.strip():
            raise ValueError("Empty output from exiftool -json")
        embedded = json.loads(result.stdout)[0]
        
        checks = []
        mismatches = []
        
        title_check = 'XMP:Title' in embedded and embedded['XMP:Title'] == json_data.get('title', '')
        checks.append(title_check)
        if not title_check:
            mismatches.append(f"Title: embedded={embedded.get('XMP:Title', 'N/A')} vs json={json_data.get('title', 'N/A')}")
        
        desc_check = 'XMP:Description' in embedded and embedded['XMP:Description'] == json_data.get('description', '')
        checks.append(desc_check)
        if not desc_check:
            mismatches.append(f"Description: embedded={embedded.get('XMP:Description', 'N/A')} vs json={json_data.get('description', 'N/A')}")
        
        if 'photoTakenTime' in json_data and 'timestamp' in json_data['photoTakenTime']:
            timestamp = datetime.fromtimestamp(int(json_data['photoTakenTime']['timestamp']), tz=timezone.utc).strftime('%Y:%m:%d %H:%M:%S')
            date_check = 'EXIF:DateTimeOriginal' in embedded and embedded['EXIF:DateTimeOriginal'] == timestamp
            checks.append(date_check)
            if not date_check:
                mismatches.append(f"DateTimeOriginal: embedded={embedded.get('EXIF:DateTimeOriginal', 'N/A')} vs json={timestamp}")
        
        if 'geoData' in json_data and 'latitude' in json_data['geoData'] and 'longitude' in json_data['geoData']:
            lat_check = 'EXIF:GPSLatitude' in embedded and abs(float(embedded['EXIF:GPSLatitude']) - float(json_data['geoData']['latitude'])) < 1e-6
            lon_check = 'EXIF:GPSLongitude' in embedded and abs(float(embedded['EXIF:GPSLongitude']) - float(json_data['geoData']['longitude'])) < 1e-6
            checks.append(lat_check)
            checks.append(lon_check)
            if not lat_check:
                mismatches.append(f"GPSLatitude: embedded={embedded.get('EXIF:GPSLatitude', 'N/A')} vs json={json_data['geoData']['latitude']}")
            if not lon_check:
                mismatches.append(f"GPSLongitude: embedded={embedded.get('EXIF:GPSLongitude', 'N/A')} vs json={json_data['geoData']['longitude']}")
        
        verified = all(checks)
        if verified:
            logger.info(f"Verification succeeded for {media_path}")
        else:
            logger.warning(f"Verification failed for {media_path} (mismatches: {'; '.join(mismatches)})")
        handler.flush()
        return verified
    except json.JSONDecodeError as e:
        logger.error(f"Verification failed for {media_path}: Invalid JSON from exiftool - {str(e)} (output: {result.stdout})")
        handler.flush()
        return False
    except Exception as e:
        logger.error(f"Verification failed for {media_path}: {str(e)}")
        handler.flush()
        return False

def embed_metadata(media_path, json_path, dry_run=False, create_backup=False):
    if dry_run:
        logger.info(f"DRY-RUN: Would embed metadata for {media_path} from simulated path {json_path} (backup: {create_backup})")
        handler.flush()
        return  # Skip actual logic in dry-run

    # Pre-check for misnamed HEIC
    check_cmd = ['exiftool', '-FileType', media_path]
    check_result = subprocess.run(check_cmd, capture_output=True, text=True, encoding='utf-8', errors='ignore')
    if 'JPEG' in check_result.stdout and media_path.lower().endswith('.heic'):
        new_path = os.path.splitext(media_path)[0] + '.jpg'
        try:
            os.rename(media_path, new_path)
            logger.info(f"Renamed misnamed HEIC to JPG: {media_path} -> {new_path}")
            media_path = new_path
        except Exception as e:
            logger.error(f"Failed to rename {media_path}: {e}")
            return

    try:
        with open(json_path, 'r', encoding='utf-8') as f:
            data = json.load(f)
        
        args = ['-backup_original'] if create_backup else []
        if 'title' in data:
            args.extend(['-XMP:Title=' + data['title']])
        if 'description' in data:
            args.extend(['-XMP:Description=' + data['description']])
        if 'photoTakenTime' in data and 'timestamp' in data['photoTakenTime']:
            timestamp = datetime.fromtimestamp(int(data['photoTakenTime']['timestamp']), tz=timezone.utc).strftime('%Y:%m:%d %H:%M:%S')
            args.extend(['-EXIF:DateTimeOriginal=' + timestamp])
        if 'geoData' in data and 'latitude' in data['geoData'] and 'longitude' in data['geoData']:
            args.extend([
                '-EXIF:GPSLatitude=' + str(data['geoData']['latitude']),
                '-EXIF:GPSLongitude=' + str(data['geoData']['longitude'])
            ])
        
        if args:
            args.extend(['-overwrite_original', media_path])
            run_exiftool(args, dry_run=False)
            
            if verify_embed(media_path, data):
                logger.info(f"Embedded metadata for {media_path} from {json_path}")
            else:
                logger.warning(f"Embed succeeded but verification failed for {media_path}")
            handler.flush()
    except Exception as e:
        logger.error(f"Error embedding for {media_path}: {str(e)}")
        handler.flush()

def custom_media_sort(filename):
    media_name, _ = os.path.splitext(filename)
    base_name, num_suffix = parse_duplicate_number(media_name)
    has_dup = bool(num_suffix)
    dup_num = int(num_suffix.strip('()')) if num_suffix else 0
    return (has_dup, dup_num, filename)

def process_directory(root_dir, dry_run=False, suffix_variants=None, avg_len=30, min_prefix_factor=0.7, step_divisor=20, do_embed=False, create_backup=False):
    for subdir, _, files in os.walk(root_dir):
        media_files = [f for f in files if is_media_file(f)]
        media_files = sorted(media_files, key=custom_media_sort)
        json_files = [f for f in files if f.lower().endswith('.json')]
        json_titles = load_json_titles(subdir, json_files)
        used_jsons = set()
        
        for file in media_files:
            full_media_path = os.path.join(subdir, file)
            media_name, media_ext = os.path.splitext(file)
            base_name, num_suffix = parse_duplicate_number(media_name)
            
            json_path = find_misnamed_json(
                subdir,
                base_name,
                media_ext,
                num_suffix,
                json_files,
                json_titles,
                used_jsons,
                suffix_variants,
                avg_len,
                min_prefix_factor,
                step_divisor,
            )
            if json_path:
                preferred_json_name = f"{base_name}{num_suffix}{media_ext}.supplemental-metadata.json"
                preferred_json_path = os.path.join(subdir, preferred_json_name)
                
                renamed = False
                if json_path != preferred_json_path:
                    if os.path.exists(preferred_json_path):
                        logger.warning(f"Preferred path already exists, skipping rename for {json_path}")
                        handler.flush()
                        continue
                    action = "DRY-RUN: Would rename" if dry_run else "Renamed"
                    if not dry_run:
                        try:
                            os.rename(json_path, preferred_json_path)
                            logger.info(f"{action}: {json_path} -> {preferred_json_path}")
                            handler.flush()
                            used_jsons.add(preferred_json_path)
                            renamed = True
                        except Exception as e:
                            logger.error(f"Error renaming {json_path}: {e}")
                            handler.flush()
                    else:
                        logger.info(f"{action}: {json_path} -> {preferred_json_path}")
                        handler.flush()
                        used_jsons.add(json_path)
                        renamed = True  # Simulated
                else:
                    used_jsons.add(json_path)
                    renamed = True  # Already correct
                
                # Embed only if rename "succeeded" (actual or simulated)
                if do_embed and renamed:
                    embed_metadata(full_media_path, preferred_json_path, dry_run, create_backup)
            else:
                logger.warning(f"No JSON found for {full_media_path}")
                handler.flush()

if __name__ == "__main__":
    root_dir = input("Enter the starting directory (default: current): ") or '.'
    dry_run_input = input("Run in dry-run mode? (y/n, default: n): ").lower() or 'n'
    dry_run = dry_run_input == 'y'
    pre_analyze_input = input("Run pre-analysis for auto-optimization? (y/n, default: y): ").lower() or 'y'
    do_pre_analyze = pre_analyze_input == 'y'
    embed_input = input("Embed metadata with exiftool after rename? (y/n, default: y): ").lower() or 'y'
    do_embed = embed_input == 'y'
    create_backup = False  # Default no backup, as requested
    if do_embed:
        backup_input = input("Create backups during metadata embed? (y/n, default: n): ").lower() or 'n'
        create_backup = backup_input == 'y'

    if dry_run:
        logger.info("Running in DRY-RUN mode: No actual changes will occur (includes renames and embeds).")
        handler.flush()

    if do_pre_analyze:
        logger.info("Running pre-analysis for dynamic tuning...")
        suffix_variants, avg_len, min_prefix_factor, step_divisor = pre_analyze(root_dir)
    else:
        suffix_variants = [
            'supplemental-metadata', 'supplemental-metadat', 'supplemental-meta', 'supplemental-met',
            'supplemental-me', 'supplemental-m', 'supplemental-', 'supplementa', 'supplement',
            'supplemen', 'suppleme', 'supplem', 'supple', 'suppl', 'supp', 'sup', 'su', 's'
        ]
        avg_len = 30
        min_prefix_factor = 0.7
        step_divisor = 20

    process_directory(root_dir, dry_run, suffix_variants, avg_len, min_prefix_factor, step_divisor, do_embed, create_backup)
    logger.info("Script completed.")
