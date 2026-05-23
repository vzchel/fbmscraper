# Facebook Marketplace Monitor

A Python-based Facebook Marketplace monitoring tool that continuously scans listings and sends alerts when items match your search criteria.

Features:
- Multi-query monitoring
- Price and keyword filtering
- Persistent Facebook login via cookies
- Discord, desktop, and email alerts
- Config and credential persistence
- Automatic browser recovery
- Headless and visible Chrome support

# Get Started

pip install -r requirements.txt

python fbm_monitor.py

python fbm_monitor.py --config my_search.json   # reload a saved search