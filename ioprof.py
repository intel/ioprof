#!/usr/bin/python -tt
# I/O Profiler for Linux
# Copyright (c) 2017, Intel Corporation.
#
# This program is free software; you can redistribute it and/or modify it
# under the terms and conditions of the GNU General Public License,
# version 2, as published by the Free Software Foundation.
#
# This program is distributed in the hope it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
# more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.

import sys, getopt, os, re, string, stat, subprocess, math, shlex, time
from multiprocessing import Process, Lock, Manager, Value, Array
import multiprocessing

# Global Variables

class global_variables:
	#VERBOSE   = False
	def __init__(self):
		self.verbose           = False                       # Verbose logging (-v flag)
		self.debug             = False                       # Debug log level (-x flag)
		self.single_threaded   = False                       # Single threaded for debug/profiling
		self.manager           = Manager()                   # Multiprocess sync object

		self.io_total          = Value('L', 0)               # Number of total I/O's
		self.read_total        = Value('L', 0)               # Number of buckets read (1 I/O can touch many buckets)
		self.write_total       = Value('L', 0)               # Number of buckets written (1 I/O can touch many buckets)
		self.reads             = self.manager.dict()         # Array of read hits by bucket ID
		self.writes            = self.manager.dict()         # Array of write hits by bucket ID
		self.r_totals          = self.manager.dict()         # Hash of read I/O's with I/O size as key
		self.w_totals          = self.manager.dict()         # Hash of write I/O's with I/O size as key
		self.bucket_hits_total = Value('L', 0)               # Total number of bucket hits (not the total buckets)
		self.total_blocks      = Value('L', 0)               # Total number of LBA's accessed during profiling
		self.files_to_lbas     = self.manager.dict()         # Files and the lba ranges associated with them
		self.max_bucket_hits   = Value('L', 0)               # The hottest bucket
		self.bucket_to_files   = self.manager.dict()         # List of files that reside on each bucket
		self.term              = Value('L', 0)               # Thread pool done with work
		self.trace_files       = False                       # Map filesystem files to block LBAs

		### Semaphores: These are the locks for the shared variables
		self.read_semaphore            = self.manager.Lock() # Lock for the global read hit array
		self.write_semaphore           = self.manager.Lock() # Lock for the global write hit array
		self.read_totals_semaphore     = self.manager.Lock() # Lock for the global read totals
		self.write_totals_semaphore    = self.manager.Lock() # Lock for the global write totals
		self.total_semaphore           = self.manager.Lock() # Lock for the global I/O totals
		self.total_blocks_semaphore    = self.manager.Lock() # Lock for the global total LBA's accessed
		self.files_to_lbas_semaphore   = self.manager.Lock() # Lock for the global file->lba mapping hash
		self.max_bucket_hits_semaphore = self.manager.Lock() # Lock for the global maximum hits per bucket
		self.bucket_to_files_semaphore1 = self.manager.Lock() # Lock for the global bucket_to_files
		self.bucket_to_files_semaphore2 = self.manager.Lock() # Lock for the global bucket_to_files
		self.term_semaphore            = self.manager.Lock() # Lock for the global TERM
		self.trace_files_semaphore     = self.manager.Lock() # Lock for the global trace_files
		self.file_hit_count_semaphore  = self.manager.Lock() # Lock for the global file_hit_count

		# Thread-local variables.  Use these to avoid locking constantly
		self.thread_io_total   = 0          # Thread-local total I/O count (I/O ops)
		self.thread_r_totals   = {}         # Thread-local read I/O size counts (ops)
		self.thread_w_totals   = {}         # Thread-local write I/O size counts (ops)
		self.thread_bucket_hits_total = 0   # Thread-local total bucket hits (buckets)
		self.thread_read_total = 0          # Thread-local total read count (I/O ops)
		self.thread_write_total = 0         # Thread-local total write count (I/O ops)
		self.thread_reads = {}              # Thread-local read count hash (buckets)
		self.thread_writes = {}             # Thread-local write count hash (buckets)
		self.thread_total_blocks = 0        # Thread-local total blocks accessed (lbas)
		self.thread_max_bucket_hits = 0     # Thread-local maximum bucket hits (bucket hits)

		# Globals
		self.file_hit_count    = {}         # Count of I/O's to each file
		self.cleanup           = []         # Files to delete after running this script
		self.total_lbas        = 0          # Total logical blocks, regardless of sector size
		self.tarfile           = ''         # .tar file outputted from 'trace' mode
		self.fdisk_file        = ""         # File capture of fdisk tool output

		self.top_files         = []         # Top files list
		self.device            = ''         # Device (e.g. /dev/sdb)
		self.device_str        = ''         # Device string (e.g. sdb for /dev/sdb)

		# Unit Scales
		self.KiB               = 1024       # 2^10
		self.MiB               = 1048576    # 2^20
		self.GiB               = 1073741824 # 2^30

		# Config settings
		self.bucket_size        = 1 * self.MiB # Size of the bucket for totaling I/O counts (e.g. 1MB buckets)
		self.num_buckets        = 1            # Number of total buckets for this device
		self.timeout            = 3            # Seconds between each print
		self.runtime            = 0            # Runtime for 'live' and 'trace' modes
		self.live_itterations   = 0            # How many iterations for live mode.  Each iteration is 'timeout' seconds long
		self.sector_size        = 0            # Sector size (usually obtained with fdisk)
		self.percent            = 0.020        # Histogram threshold for each level (e.g. 0.02% of total drive size)
		self.total_capacity_gib = 0            # Total drive capacity
		self.mode               = ''           # Processing mode (live, trace, post)
		self.pdf                = False        # Generate a PDF report instead of a text report
		self.top_count_limit    = 10           # How many files to list in Top Files list (e.g. Top 10 files)
		self.thread_count       = 0            # Thread Count
		self.cpu_affinity       = 0            # Tie each thread to a CPU for load balancing
		self.thread_max         = 32           # Max thread cout
		self.buffer_size        = 1024         # blktrace buffer size
		self.buffer_count       = 8            # blktrace buffer count

		# Gnuplot settings
		self.x_width            = 800          # gnuplot x-width
		self.y_height           = 600          # gnuplot y-height

		### ANSI COLORS
		self.black   = "\e[40m"
		self.red     = "\e[41m"
		self.green   = "\e[42m"
		self.yellow  = "\e[43m"
		self.blue    = "\e[44m"
		self.magenta = "\e[45m"
		self.cyan    = "\e[46m"
		self.white   = "\e[47m"
		self.none    = "\e[0m"

		### Heatmap Key
		self.colors = [self.black, self.red, self.green, self.yellow, self.blue, self.magenta, self.cyan, self.white, self.none]

		### Heatmap Globals (TODO)
		self.color_index = 0
		self.choices = len(self.colors)
		self.vpc = 1
		self.cap = 0
		self.rate = 0

		self.mount_point        = ""
		self.extents            = []
		self.files              = []
# global_variables

### Print usage
def usage(g, argv):
	name = os.path.basename(__file__)
	#name = argv[0]
	print "Invalid command\n"
	#print name + " " + str(argv)
	print name,
	for opt in argv:
		print opt,
	print "\n\nUsage:"
	print name + " -m trace -d <dev> -r <runtime> [-v] [-f] # run trace for post-processing later"
	print name + " -m post  -t <dev.tar file>     [-v] [-p]   # post-process mode"
	print name + " -m live  -d <dev> -r <runtime> [-v]        # live mode"
	print "\nCommand Line Arguments:"
	print "-d <dev>            : The device to trace (e.g. /dev/sdb).  You can run traces to multiple devices (e.g. /dev/sda and /dev/sdb)"
	print "                      at the same time, but please only run 1 trace to a single device (e.g. /dev/sdb) at a time"
	print "-r <runtime>        : Runtime (seconds) for tracing"
	print "-t <dev.tar file>   : A .tar file is created during the 'trace' phase.  Please use this file for the 'post' phase"
	print "                      You can offload this file and run the 'post' phase on another system."
	print "-v                  : (OPTIONAL) Print verbose messages."
	print "-f                  : (OPTIONAL) Map all files on the device specified by -d <dev> during 'trace' phase to their LBA ranges."
	print "                       This is useful for determining the most fequently accessed files, but may take a while on really large filesystems"
	print "-p                  : (OPTIONAL) Generate a .pdf output file in addition to STDOUT.  This requires 'pdflatex', 'gnuplot' and 'terminal png'"
	print "                       to be installed."
	sys.exit(-1)
# usage (DONE)

### Check arguments
def check_args(g, argv):

	# Gather command line arguments
	try:
		opts, args = getopt.getopt(argv,"m:d:t:fr:vpx")
	except getopt.GetoptError as err:
		print str(err)
		usage(g,argv)

	# Parse arguments
	for opt, arg in opts:
		if opt == '-m':
			g.mode = arg
		elif opt == '-d':
			g.device = arg
		elif opt == '-t':
			g.tarfile = arg
		elif opt == '-f':
			g.trace_files= True
		elif opt == '-r':
			g.runtime = int(arg)
			if g.runtime < 3:
				g.runtime = 3 # Min runtime
		elif opt == '-v':
			g.verbose = True
		elif opt == '-p':
			g.pdf = True
		elif opt == '-x':
			g.verbose = True
			g.debug = True
		else:
			usage(g,argv)

	# Check arguments
	if g.verbose == True or g.debug == True:
		verbose_print(g, "verbose: " + str(g.verbose) + " debug: " + str(g.debug))

	if g.mode == 'live':
		verbose_print(g, "LIVE")
		if g.device == '' or g.runtime == '':
			usage(g,argv)
		debug_print(g, "Dev: " + g.device + " Runtime: " + g.runtime)
		match = re.search("\/dev\/(\S+)", g.device)
		try: 
			debug_print(g,match.group(1))
			g.device_str = string.replace(match.group(1), "/", "_")
		except:
			print "Invalid Device Type"
			usage(g, argv)
		statinfo = os.stat(g.device)
		if not stat.S_ISBLK(statinfo.st_mode):
			print "Device " + g.device + " is not a block device"
			usage(g,argv)
	elif g.mode == 'post':
		verbose_print(g, "POST")
		if g.tarfile == '':
			usage(g,argv)
		match = re.search("(\S+).tar", g.tarfile)
		try:
			debug_print(g,match.group(1))
			g.device_str = match.group(1)
		except:
			print "ERROR: invalid tar file" + g.tarfile
		if g.pdf == True:
			verbose_print(g, "PDF Report Output")
			check_pdf_prereqs(g)

			print "PDF Report Output - COMING SOON..." # COMING SOON
			sys.exit(-1) # COMING SOON
		g.fdisk_file = "fdisk." + g.device_str
		debug_print(g, "fdisk_file: " + g.fdisk_file)
		g.cleanup.append(g.fdisk_file)
	elif g.mode == 'trace':
		verbose_print(g, "TRACE")
		check_trace_prereqs(g)
		if g.device == '' or g.runtime == '':
			usage(g,argv)
		debug_print(g, "Dev: " + g.device + " Runtime: " + str(g.runtime))
		match = re.search("\/dev\/(\S+)", g.device)
		try: 
			debug_print(g,match.group(1))
			g.device_str = string.replace(match.group(1), "/", "_")
		except:
			print "Invalid Device Type"
			usage(g, argv)
		statinfo = os.stat(g.device)
		if not stat.S_ISBLK(statinfo.st_mode):
			print "Device " + g.device + " is not a block device"
			usage(g,argv)
	else:
		usage(g,argv)
	return
# check_args (DONE)

def debug_print(g, message):
	if g.debug == True:
		print message
# debug_print (DONE)

def verbose_print(g, message):
	if g.verbose == True:
		print message
# verbose_print (DONE)

### Check prereqs for gnuplot and latex
def check_pdf_prereqs(g):
	debug_print(g, "check_pdf_prereqs")

	rc = os.system("which gnuplot &> /dev/null")
	if rc != 0:
		print "ERROR: gnuplot not installed.  Please offload the trace file for processing."
		sys.exit(1)
	else:
		debug_print(g, "which gnuplot: rc=" + str(rc))
	rc = os.system("which pdflatex &> /dev/null")
	if rc != 0:
		print "ERROR: pdflatex not installed.  Please offload the trace file for processing."
		sys.exit(1)
	else:
		debug_print(g, "which pdflatex: rc=" + str(rc))
	rc = os.system("echo 'set terminal png' > pngtest.txt; gnuplot pngtest.txt >/dev/null 2>&1")
	if rc != 0:
		print "ERROR: gnuplot PNG terminal not installed.  Please offload the trace file for processing."
		sys.exit(1)
	else:
		debug_print(g, "gnuplot pngtest.txt: rc=" + str(rc))
	return
# check_pdf_prereqs (DONE)

### Check prereqs for blktrace
def check_trace_prereqs(g):
	debug_print(g, "check_trace_prereqs")
	rc = os.system("which blktrace &> /dev/null")
	if rc != 0:
		print "ERROR: blktrace not installed.  Please install blktrace"
		sys.exit(1)
	else:
		debug_print(g, "which blktrace: rc=" + str(rc))
	rc = os.system("which blkparse &> /dev/null")
	if rc != 0:
		print "ERROR: blkparse not installed.  Please install blkparse"
		sys.exit(1)
	else:
		debug_print(g, "which blkparse: rc=" + str(rc))
# check_trace_prereqs (DONE)

### Check if debugfs is mounted
def mount_debugfs(g):
	rc = os.system("mount | grep debugfs &> /dev/null")
	if rc != 0:
		debug_print(g, "Need to mount debugfs")
		rc = os.system("mount -t debugfs debugfs /sys/kernel/debug")
		if rc != 0:
			print "ERROR: Failed to mount debugfs"
			sys.exit(2)
		else:
			verbose_print(g, "Mounted debugfs successfully")
	return
# mount_debugfs (DONE)

### Translate LBA to Bucket
def lba_to_bucket(g, lba):
	bucket = (int(lba) * int(g.sector_size)) / int(g.bucket_size)
	if bucket > g.num_buckets:
		#printf("ERROR: lba=%d bucket=%d greater than num_buckets=%d\n", int(lba), bucket, g.num_buckets)
		bucket = g.num_buckets - 1
	return bucket
# lba_to_bucket (DONE)

### Translate Bucket to LBA
def bucket_to_lba(g, bucket):
	lba = (bucket * g.bucket_size) / g.sector_size
	return lba
# bucket_to_lba (DONE)

### debugfs method
### # This method can only be used on ext2/ext3/ext4 filesystems
### I don't plan on using this method, long term
### In testing the debugfs method, I found it to be approximately 30% slower than the ioctl method in perl
def debugfs_method(g, file):
	extents = []
	file = string.replace(file, g.mountpoint, "")
	debug_print(g, "file: " + file)
	cmd = 'debugfs -R "dump_extents ' + file + '" ' + g.device + '  2>/dev/null'
	debug_print(g, cmd)
	(rc, extent_out) = run_cmd(g, cmd)
	for line in extent_out:
		debug_print(g, line)
		match = re.search("\s+\d+\/\s+\d+\s+\d+\/\s+\d+\s+\d+\s+-\s+\d+\s+(\d+)\s+-\s+(\d+)", line)
		try:
			g.extents.append(match.group(1) + ":" + match.group(1))
		except:
			debug_print(g, "no match")
	return
# debugfs_method (DONE)

### Translate FS cluster to LBA
def fs_cluster_to_lba(g, fs_cluster_size, sector_size, io_cluster):
	lba = io_cluster * (fs_cluster_size / sector_size)
	return lba
# fs_cluster_to_lba (DONE)

### ioctl method (COMING SOON...)
### # This method "should" be usable regardless of filesystem
### There is some risk that FIBMAP!=1.  Need to address this later
### I plan to use the ioctl method because it is 30% faster than the debugfs method
def ioctl_method(g, file):
	print "ext3 will be supported once ioctl_method() is supported"
	sys.exit(-1)
	return
# ioctl_method (COMING SOON...)

### Print filetrace files
def printout(g, file):
	debug_print(g, "printout: " + file)
	cpu_affinity = 0
	filetrace = "filetrace." + g.device_str + "." + str(cpu_affinity) + ".txt"
	fo = open(filetrace, "a")
	try:
		fo.write(file + " :: " + g.extents)
		fo.close()
	except:
		print "ERROR: Failed to open " + filetrace
		sys.exit(3)
# printout (DONE)

def block_ranges(g, file):
	debug_print(g, "block_ranges: " + file)
	# TODO: exclude /proc and /sys mountpoints
	statinfo = os.stat(file)
	mode = statinfo.st_mode
	if stat.S_ISLNK(mode) or stat.ST_SIZE == 0 or not stat.ST_ISREG(mode):
		debug_print(g, "Disqualified file: " + file)
		return
	mounttype = os.system("mount | grep " + g.device + " | awk '{ print \$5 }'")
	if mounttype == "ext4":
		debugfs_method(g, file)
	elif mounttype == "ext3":
		ioctl_method(g, file)
	else:
		print "ERROR: " + mounttype + " is not supported yet"
		sys.exit(4)
	printout(file)
	return
# block_ranges (DONE)

def find_all_files(g):
	files = []
	print "FIND ALL FILES"
	os.system("rm -f filetrace.* &>/dev/null")
	cpu_affinity = 0
	filetrace = "filetrace." + g.device_str + "." + str(cpu_affinity) + ".txt"
	os.system("touch " + filetrace)
	cmd = "cat /proc/cpuinfo | grep processor | wc -l"
	(rc, cpu_count) = run_cmd(g, cmd)

	cmd = "mount | grep " +  g.device + "| awk '{ print \$3 }'"
	(rc, mountpoint) = run_cmd(g, cmd)
	if rc != 0:
		print g.device + " not mounted"
		os.system("gzip --fast filetrace.* &>/dev/null")
		return
	verbose_print(g, "mountpoint: " + mountpoint)

	cmd = 'mount | grep ' + g.device + " | awk '{ print \$5 }'"
	(rc, mounttype)  = run_cmd(g, cmd)
	verbose_print(g, "mounttype: " + mounttype)

	ioprof_file = 'ioprof_files.' + g.device_str + '.txt'
	cmd = 'find ' + mountpoint + ' -xdev -name "*" > ' + ioprof_file
	rc = os.system(cmd)
	with open(ioprof_file, "r") as fo:
		for line in fo:
			g.files.append(line)
			debug_print(g, line)
	fo.close()

	file_count = len(g.files)
	debug_print(g, "filecount: " + file_count)

	# Single Threaded Method (TODO: Make Multi-threaded)
	k=0
	for i in range(0..file_count):
		if (k > 100):
			progress = (i / file_count) * 100
			printf("\r%05.2f%% COMPLETE", progress)
			k=0
		k = k + 1
		file = g.files[i]
		debug_print("file: " + file)
		block_ranges(file)
		
	os.system("gzip --fast filetrace.* &>/dev/null")
	return
# find_all_files (DONE)

### Translate a bucket ID to a list of files
def bucket_to_file_list(g, bucket_id):
	list=""
	try:
		 list = g.bucket_to_files[bucket_id]
	except:
		pass
	return list
# bucket_to_file_list (DONE)

def file_to_bucket_helper(g, f):
	for file, r in f.iteritems():
		#g.file_hit_count_semaphore.acquire()
		#g.file_hit_count[file]=0 # Initialize file hit count
		#g.file_hit_count_semaphore.release()
		tempstr = f[file]
		debug_print(g, "f=" + file + " r=" + r)
		x=0
		for range in tempstr.split(' '):
			if range == ' ' or range == '':
				continue # TODO
			debug_print(g, 'r(' + str(x) + ')=' + range)
			x+=1
			try:
				(start, finish) = range.split(':')
			except:
				continue
			debug_print(g, file + " start=" + start + ", finish=" + finish)
			if start == '' or finish == '':
				continue
			start_bucket  = lba_to_bucket(g, start)
			finish_bucket = lba_to_bucket(g, finish)
	
			debug_print(g, file + " s_lba=" + start + " f_lba=" + finish + " s_buc=" + str(start_bucket) + "f_buc=" + str(finish_bucket ))
			#print "WAITING ON LOCK"
			i=start_bucket
			#print "GOT LOCK!"
			while i<= finish_bucket:
				if (i < (g.num_buckets/2)):
					g.bucket_to_files_semaphore1.acquire()
				else:
					g.bucket_to_files_semaphore2.acquire()
				try:
					g.bucket_to_files[i] = g.bucket_to_files[i] + file + " "
				except:
					g.bucket_to_files[i] = file + " "
				if (i < (g.num_buckets/2)):
					g.bucket_to_files_semaphore1.release()
				else:
					g.bucket_to_files_semaphore2.release()
				i+=1
				continue

				debug_print(g, "i=" + str(i))
				if i in g.bucket_to_files:
					pattern = re.escape(file)
					match = re.search(pattern, g.bucket_to_files[i])
					try:
						match.group(0)
					except:
						debug_print(g, "No Match!  FILE=" + pattern + " PATTERN=" + g.bucket_to_files[i])
						g.bucket_to_files[i] = g.bucket_to_files[i] + file + " "
				else:
					g.bucket_to_files[i] = file + " "
				debug_print(g, "i=" + str(i) + "file_to_buckets: " + g.bucket_to_files[i])
				i+=1
	return

### Tranlate a file to a list of buckets
def file_to_buckets(g):
	k=0
	size = len(g.files_to_lbas)
	print "Moving some memory around.  This will take a few seconds..."
	f = dict(g.files_to_lbas)
	temp = {}
	plist = []
	g.thread_max = 1024

	#if g.single_threaded == False:
	if False:
		for file, r in f.iteritems():
			g.file_hit_count[file]=0 # Initialize file hit count
			temp[file] = r
			k+=1
			if k % 10 == 0:
				p = Process(target=file_to_bucket_helper, args=(g, temp))
				plist.append(p)
				p.start()
				printf("\rfile_to_buckets: %d %% (%d of %d)", (k*100 / size), k, size)
				sys.stdout.flush()
			#if False:
			while len(plist) > g.thread_max:
				for p in plist:
					try:
						p.join(0)
					except:
						pass
					else:
						if not p.is_alive():
							plist.remove(p)
					time.sleep(0.10)
		x=1
		while len(plist) > 0:
			dots=""
			for i in xrange(x):
				dots = dots + "."
			x+=1
			if x>3:
				x=1
			printf("\rWaiting on %3d threads to complete processing%-3s", len(plist), dots)
			printf("    ")
			sys.stdout.flush()
			for p in plist:
				try:
					p.join(0)
				except:
					pass
				else:
					if not p.is_alive():
						plist.remove(p)
			time.sleep(0.10)
	
		print "\rDone correlating files to buckets.  Now time to count bucket hits"
		return
	else:
	
		for file, r in f.iteritems():
			k+=1
			if k % 100 == 0:
				printf("\rfile_to_buckets: %d %% (%d of %d)", (k*100 / size), k, size)
				sys.stdout.flush()
			g.file_hit_count[file]=0 # Initialize file hit count
			tempstr = f[file]
			debug_print(g, "f=" + file + " r=" + r)
			x=0
			for range in tempstr.split(' '):
				if range == ' ' or range == '':
					continue # TODO
				debug_print(g, 'r(' + str(x) + ')=' + range)
				x+=1
				try:
					(start, finish) = range.split(':')
				except:
					continue
				debug_print(g, file + " start=" + start + ", finish=" + finish)
				if start == '' or finish == '':
					continue
				start_bucket  = lba_to_bucket(g, start)
				finish_bucket = lba_to_bucket(g, finish)
	
				debug_print(g, file + " s_lba=" + start + " f_lba=" + finish + " s_buc=" + str(start_bucket) + "f_buc=" + str(finish_bucket ))
				i=start_bucket
				while i<= finish_bucket:
					debug_print(g, "i=" + str(i))
					if i in g.bucket_to_files:
						pattern = re.escape(file)
						match = re.search(pattern, g.bucket_to_files[i])
						try:
							match.group(0)
						except:
							debug_print(g, "No Match!  FILE=" + pattern + " PATTERN=" + g.bucket_to_files[i])
							g.bucket_to_files[i] = g.bucket_to_files[i] + file + " "
					else:
						g.bucket_to_files[i] = file + " "
					debug_print(g, "i=" + str(i) + "file_to_buckets: " + g.bucket_to_files[i])
					i+=1
		print "\rDone correlating files to buckets.  Now time to count bucket hits"
		return
# file_to_buckets (DONE)

### Add up I/O hits to each file touched by a bucket
def add_file_hits(g, bucket_id, io_count):
	list = bucket_to_file_list(g, bucket_id)
	size = len(list)
	#print list
	if size == 0 and io_count != 0:
		debug_print(g, "No file hit.  bucket=" + str(bucket_id) + ", io_cnt=" + str(io_count))

	for file in list.split(' '):
		if file != '': 
			debug_print(g, "file=" + file)
			try:
				g.file_hit_count[file] += io_count
			except:
				g.file_hit_count[file] = io_count
	return
# add_file_hits (DONE)

### Get logrithmic theta for Zipfian distribution
def theta_log(g, base, value):
	debug_print(g, "base=" + str(base) + ", value=" + str(value))
	if value == 0 or base == 0:
		return 0
	else:
		result = math.log(value) / math.log(base)
		return result
# theta_log (DONE)

### Print Results
def print_results(g):
	num=0
	sum=0
	k=0
	buffer=''
	row=0
	column=0
	bw_total=0
	counts={}
	read_sum=0
	write_sum=0
	row=column=0
	bw_total=0
	histogram_iops=[]
	histogram_bw=[]
	

	g.verbose=True
	verbose_print(g, "num_buckets=" + str(g.num_buckets) + " bucket_size=" + str(g.bucket_size))
	g.verbose=False
	if g.pdf == True:
		# TODO
		pass
	x=0
	threshold = g.num_buckets / 100
	i=0
	while i<g.num_buckets:
		x+=1
		if x > threshold:
			printf("\rBucket Percent: %d %% (%d of %d)", ((i * 100)/ g.num_buckets), i, g.num_buckets)
			sys.stdout.flush()
			x=0
		if i != 0 and (i % g.x_width) == 0:
			if g.pdf == True:
				# TODO
				pass
			buffer=''
			row += 1
			column=0
		

		r=0
		if i in g.reads:
			r=g.reads[i]
		w=0
		if i in g.writes:
			w=g.writes[i]

		bucket_total = r + w
		bw_total += bucket_total * g.bucket_size
		if g.trace_files:
			add_file_hits(g, i, bucket_total)
		if bucket_total in counts:
			counts[bucket_total] += 1
		else:
			counts[bucket_total] = 1
		debug_print(g, "bucket_total=" + str(bucket_total) + " counts[b_bucket_total]=" + str(counts[bucket_total]))
		read_sum += r
		write_sum += w
		buffer = buffer + ("%d " %  bucket_total)
		column += 1
		i+=1

	print "\r                             "
	while (i % g.x_width) != 0:
		i+=1
		buffer = buffer + "0 "

	if g.pdf:
		# TODO
		pass

	verbose_print(g, "num_buckets=%s pfgp iot=%s bht=%s r_sum=%s w_sum=%s yheight=%s" % (g.num_buckets, g.io_total.value, g.bucket_hits_total.value, read_sum, write_sum, g.y_height))

	t=0
	j=0
	section_count=0
	b_count=0
	gb_tot = 0
	bw_tot = 0
	bw_count = 0
	io_sum = 0
	tot = 0
	if g.pdf:
		# TODO
		pass

	max_set = 0
	max = 0
	theta_count = 1
	theta_total = 0
	min = 1
	max_theta = 0
	min_theta = 999

	# %counts is a hash
	# each key "bucket_total" represents a particular I/O count for a bucket
	# each value represents the number of buckets that had this I/O count
	# This allows me to quickly tally up a histogram and is pretty
	# space efficient since most buckets tend to have zero I/O that
	# key tends to have the largest number of buckets
	#
	# Iterate through each key in decending order
	for total in sorted(counts, reverse=True):
		debug_print(g, "total=" + str(total) + " counts=" + str(counts[total]))
		if total > 0:
			tot += total * counts[total]
			if max_set == 0:
				max_set=1
				max = total
			else:
				theta_count += 1
				min = total
				cur_theta = theta_log(g, theta_count, max) - theta_log(g, theta_count, total)
				if cur_theta > max_theta:
					max_theta = cur_theta
				if cur_theta < min_theta:
					min_theta = cur_theta
				debug_print(g, "cur_theta=" + str(cur_theta))
				theta_total += cur_theta
			i=0
			while i<counts[total]:
				section_count += total
				b_count += 1
				bw_count += total * g.bucket_size
				if ((b_count * g.bucket_size )/ g.GiB) > (g.percent * g.total_capacity_gib):
					debug_print(g, "b_count:" + str(b_count))
					bw_tot += bw_count
					gb_tot += (b_count * g.bucket_size)
					io_sum += section_count
	
					gb = "%.1f" % (gb_tot / g.GiB)
					if g.bucket_hits_total.value == 0:
						io_perc = "NA"
						io_sum_perc = "NA"
						bw_perc = "NA"
					else:
						debug_print(g, "b_count=" + str(b_count) + " s=" + str(section_count) + " ios=" + str(io_sum) + " bwc=" + str(bw_count))
						io_perc = "%.1f" % ((float(section_count) / float(g.bucket_hits_total.value)) * 100.0)
						io_sum_perc = "%.1f" % ((float(io_sum) / float(g.bucket_hits_total.value)) * 100.0)
						if bw_total == 0:
							bw_perc = "%.1f" % (0)
						else:
							bw_perc = "%.1f" % ((bw_count / bw_total) * 100)
	
					if g.pdf:
						# TODO
						pass
					
					histogram_iops.append(str(gb) + " GB " + str(io_perc) + "% (" + io_sum_perc + "% cumulative)")
					histogram_bw.append(str(gb) + " GB " + str(bw_perc) + "% ")

					b_count=0
					section_count=0
					bw_count=0
					
				i += 1
	if b_count:
		debug_print(g, "b_count: " + str(b_count))
		bw_tot += bw_count
		gb_tot += b_count * g.bucket_size
		io_sum += section_count

		gb = "%.1f" % (gb_tot / g.GiB)
		if g.bucket_hits_total.value == 0:
			io_perc = "NA"
			io_sum_perc = "NA"
			bw_perc = "NA"
		else:
			io_perc = "%.1f" % ((section_count / g.bucket_hits_total.value) * 100)
			io_sum_perc = "%.1f" % ((io_sum / g.bucket_hits_total.value) * 100)
			if bw_total == 0:
				bw_perc = "%.1f" % (0)
			else:
				bw_perc = "%.1f" % ((bw_count / bw_total) * 100)

		if g.pdf:
			# TODO
			pass

		histogram_iops.append(str(gb) + " GB " + str(io_perc) + "% (" + str(io_sum_perc) + "% cumulative)")
		histogram_bw.append(str(gb) + " GB " + str(bw_perc) + "% ")

		b_count = 0
		section_count = 0
		bw_count = 0

	if g.pdf:
		# TODO
		pass

	debug_print(g, "t=" + str(t))

	print "--------------------------------------------"
	print "Histogram IOPS:"
	for entry in histogram_iops:
		print entry
	print "--------------------------------------------"

	# TODO: Check that this is consistent with Perl version
	if (theta_count):
		avg_theta = theta_total / theta_count
		med_theta = ((max_theta - min_theta) / 2 ) + min_theta
		approx_theta = (avg_theta + med_theta) / 2
		#string = "avg_t=%s med_t=%s approx_t=%s min_t=%s max_t=%s\n" % (avg_theta, med_theta, approx_theta, min_theta, max_theta)
		verbose_print(g, "avg_t=%s med_t=%s approx_t=%s min_t=%s max_t=%s\n" % (avg_theta, med_theta, approx_theta, min_theta, max_theta))
		analysis_histogram_iops = "Approximate Zipfian Theta Range: %0.4f-%0.4f (est. %0.4f).\n" % (min_theta, max_theta, approx_theta)
		print analysis_histogram_iops

	debug_print(g, "Trace_files: " + str(g.trace_files))
	if g.trace_files:
		top_count=0
		print "--------------------------------------------"
		print "Top files by IOPS:"
		print "Total I/O's: " + str(g.bucket_hits_total.value)
		if g.bucket_hits_total.value == 0:
			print "No Bucket Hits"
		else:	
			for filename in sorted(g.file_hit_count, reverse=True, key=g.file_hit_count.get):
				hits = g.file_hit_count[filename]
				if hits > 0:
					hit_rate = (float(hits) / float(g.bucket_hits_total.value)) * 100.0
					print "%0.2f%% (%d) %s" % (hit_rate, hits, filename)
					if g.pdf:
						g.top_files = append("%0.2f%%: (%d) %s\n" % (hit_rate, hits, filename))
				top_count += 1
				if top_count > g.top_count_limit:
					break
		print "--------------------------------------------"
	
	return
# print_results (IN PROGRESS)

### Print heatmap header for PDF
def print_header_heatmap(g):
	return
# print_header_heatmap (TODO)

### Print histogram header for PDF
def print_header_histogram_iops(g):
	return
# print_header_histogram_iops (TODO)

### Print stats header for PDF
def print_header_stats_iops(g):
	return
# print_header_stats_iops (TODO)

### Create PDF Report
def create_report(g):
	return
# create_report (TODO)

### Print I/O statistics
def print_stats(g):
	return
# print_stats (TODO)


### Combine thread-local counts into global counts
def total_thread_counts (g, num):

	g.max_bucket_hits_semaphore.acquire()
	debug_print(g, "Thread " + str(num) + " has max_bucket_hits lock t=" + str(g.thread_max_bucket_hits) + " g=" + str(g.max_bucket_hits.value))
	if(g.thread_max_bucket_hits > g.max_bucket_hits.value):
		g.max_bucket_hits.value = g.thread_max_bucket_hits
	debug_print(g, "Thread " + str(num) + " releasing max_bucket_hits lock t=" + str(g.thread_max_bucket_hits) + " g=" + str(g.max_bucket_hits.value))
	g.max_bucket_hits_semaphore.release()

	g.total_blocks_semaphore.acquire()
	debug_print(g, "Thread " + str(num) + " has total_blocks lock t=" + str(g.thread_total_blocks) + " g=" + str(g.total_blocks.value))
	g.total_blocks.value += g.thread_total_blocks
	debug_print(g, "Thread " + str(num) + " releasing total_blocks lock t=" + str(g.thread_total_blocks) + " g=" + str(g.total_blocks.value))
	g.total_blocks_semaphore.release()

	g.total_semaphore.acquire()
	debug_print(g, "Thread " + str(num) + " has total lock t=" + str(g.thread_io_total) + " g=" + str(g.io_total.value))
	g.io_total.value += g.thread_io_total
	debug_print(g, "Thread " + str(num) + " releasing total lock t=" + str(g.thread_io_total) + " g=" + str(g.io_total.value))
	g.total_semaphore.release()

	g.read_totals_semaphore.acquire()
	debug_print(g, "Thread " + str(num) + " has read_totals lock t=" + str(g.thread_read_total) + " g=" + str(g.read_total.value))
	g.read_total.value += g.thread_read_total
	for io_size, hits in g.thread_r_totals.iteritems():
		if io_size in g.r_totals:
			g.r_totals[io_size] += hits
		else:
			g.r_totals[io_size] = hits
	debug_print(g, "Thread " + str(num) + " releasing read_totals lock t=" + str(g.thread_read_total) + " g=" + str(g.read_total.value))
	g.read_totals_semaphore.release()

	g.write_totals_semaphore.acquire()
	debug_print(g, "Thread " + str(num) + " has write_totals lock t=" + str(g.thread_write_total) + " g=" + str(g.write_total.value))
	g.write_total.value += g.thread_write_total
	for io_size, hits in g.thread_w_totals.iteritems():
		if io_size in g.w_totals:
			g.w_totals[io_size] += hits
		else:
			g.w_totals[io_size] = hits
	debug_print(g, "Thread " + str(num) + " releasing write_totals lock t=" + str(g.thread_write_total) + " g=" + str(g.write_total.value))
	g.write_totals_semaphore.release()

	g.read_semaphore.acquire()
	debug_print(g, "Thread " + str(num) + " has read lock.")
	for bucket,value in g.thread_reads.iteritems():
		try:
			g.reads[bucket] += value
		except:
			g.reads[bucket] = value
		debug_print(g, "Thread " + str(num) + " has read lock.  Bucket=" + str(bucket) + " Value=" + str(value) + " g.reads[bucket]=" + str(g.reads[bucket]))
	g.read_semaphore.release()

	g.write_semaphore.acquire()
	debug_print(g, "Thread " + str(num) + " has write lock.")
	for bucket,value in g.thread_writes.iteritems():
		try:
			g.writes[bucket] += value
		except:
			g.writes[bucket] = value
		debug_print(g, "Thread " + str(num) + " has write lock.  Bucket=" + str(bucket) + " Value=" + str(value) + " g.writes[bucket]=" + str(g.writes[bucket]))
	g.write_semaphore.release()

	g.total_semaphore.acquire()
	debug_print(g, "Thread " + str(num) + " has total lock t=" + str(g.thread_bucket_hits_total) + " g=" + str(g.bucket_hits_total.value))
	g.bucket_hits_total.value += g.thread_bucket_hits_total
	debug_print(g, "Thread " + str(num) + " releasing total lock t=" + str(g.thread_bucket_hits_total) + " g=" + str(g.bucket_hits_total.value))
	g.total_semaphore.release()

	return
# total_thread_counts (DONE)

### Thread parse routine for blktrace output
def thread_parse(g, file, num):
	#print "thread_parse\n"
	linecount = 0
	os.system("gunzip " + file + ".gz")
	debug_print(g, "\nSTART: " +  file + " " + str(num) + "\n")
	try:
		fo = open(file, "r")
	except:
		print "ERROR: Failed to open " + file
		sys.exit(3)
	else:
		count=0
		hit_count = 0
		for line in fo:
			count += 1
			try:
				#(a, b, c) = regex_find('.*Q.*', line)
				set = regex_find('(\S+)\s+Q\s+(\S+)\s+(\S+)$', line)
			except:
				pass
			else:
				hit_count += 1
				#print len(set)
				#print "a=" + a + " b=" + b + " c=" + c + "\n"
				#print set
				#sys.stdout.flush()
				try:
					parse_me(g, set[0], int(set[1]), int(set[2]))
				except:
					pass
			#sys.stdout.flush()
		fo.close()
		total_thread_counts(g, num)
		debug_print(g,  "\n FINISH" + file +  " (" + str(count) + " lines) [hit_count=" + str(hit_count) + "]" + str(g.thread_io_total) + "\n")
		rc = os.system("rm -f " + file)
	return

# thread_parse (DONE)

### Parse blktrace output
def parse_me(g, rw, lba, size):
	debug_print(g,  "rw=" + rw + " lba=" + str(lba) + " size=" + str(size))
	if (rw == 'R') or (rw == 'RW'):
		# Read
		g.thread_total_blocks += int(size)
		g.thread_io_total += 1
		g.thread_read_total += 1
		if size in g.thread_r_totals:
			g.thread_r_totals[size] += 1
		else:
			g.thread_r_totals[size] = 1
		bucket_hits = (size * g.sector_size) / g.bucket_size
		if ((size * g.sector_size) % g.bucket_size) != 0:
			bucket_hits += 1
		for i in xrange(0, bucket_hits):
			bucket = int((lba * g.sector_size) / g.bucket_size) + i
			if bucket > g.num_buckets:
				# Not sure why, but we occassionally get buckets beyond our max LBA range
				bucket = g.num_buckets - 1
			if True:
				if bucket in g.thread_reads:
					g.thread_reads[bucket] += 1
				else:
					g.thread_reads[bucket] = 1
			else:
				try:
					g.thread_reads[bucket] += 1
				except:
					g.thread_reads[bucket] = 1
			if(g.thread_reads[bucket] > g.thread_max_bucket_hits):
				g.thread_max_bucket_hits = g.thread_reads[bucket]
			g.thread_bucket_hits_total += 1
	elif (rw == 'W') or (rw == 'WS'):
		# Write
		g.thread_total_blocks += int(size)
		g.thread_io_total += 1
		g.thread_write_total += 1
		if size in g.thread_w_totals:
			g.thread_w_totals[size] += 1
		else:
			g.thread_w_totals[size] = 1
		bucket_hits = (size * g.sector_size) / g.bucket_size
		if ((size * g.sector_size) % g.bucket_size) != 0:
			bucket_hits += 1
		for i in xrange(0, bucket_hits):
			bucket = int((lba * g.sector_size) / g.bucket_size) + i
			if bucket > g.num_buckets:
				# Not sure why, but we occassionally get buckets beyond our max LBA range
				bucket = g.num_buckets - 1
			if True:
				if bucket in g.thread_writes:
					g.thread_writes[bucket] += 1
				else:
					g.thread_writes[bucket] = 1
			else:
				try:
					g.thread_writes[bucket] += 1
				except:
					g.thread_writes[bucket] = 1
			if(g.thread_writes[bucket] > g.thread_max_bucket_hits):
				g.thread_max_bucket_hits = g.thread_writes[bucket]
			g.thread_bucket_hits_total += 1
	return
# parse_me (DONE)

## File trace routine
def parse_filetrace(g, file, num):
	thread_files_to_lbas = {}
	os.system("gunzip " + file + ".gz")
	debug_print(g, "tracefile = " + file + " " + str(num) + "\n")
	try:
		fo = open(file, "r")
	except Exception as e:
		print "ERROR: Failed to open " + file + " Err: ", e
		sys.exit(3)
	else:
		for line in fo:
			try:
				set = regex_find('(\S+)\s+::\s+(.+)', line)
			except:
				pass
			else:
				object = set[0]
				ranges = set[1]
				thread_files_to_lbas[object] = ranges
				debug_print(g, file + ": obj=" + object + " ranges:" + ranges + "\n")
		fo.close()

		debug_print(g, "Thread " + str(num) + "wants file_to_lba lock for " + file + "\n")
		g.files_to_lbas_semaphore.acquire()
		for key,value in thread_files_to_lbas.iteritems():
			g.files_to_lbas[key] = value
			debug_print(g, "k=" + str(key) + " value=" + str(g.files_to_lbas[key]))
		g.files_to_lbas_semaphore.release()
		debug_print(g, "Thread " + str(num) + "freed file_to_lba lock for " + file + "\n")

	return
# parse_filetrace (DONE)

### Choose color for heatmap block
def choose_color(g, num):
	if num == -1 or num == 0:
		return g.black
	g.color_index = num / g.vpc
	if (g.color_index > (g.choices - 1)):
		g.debug = True
		debug_print(g, "HIT! num=" + num)
		g.debug = False
		g.color_index=7
		return g.red
	color = g.colors[g.color_index]
	debug_print(g, "cap=" + g.cap + " num=" + num + " ci=" + g.color_index + " vpc=" + g.vpc + " cap=" + g.cap)
	return color
# choose_color (DONE)

### Clear Screen for heatmap (UNUSED)
def clear_screen(g):
	print "\033[2J"
	print "\[\033[0;0f\]\r"
	return
# clear_screen (DONE)

### Get block value by combining buckets into larger heatmap blocks for term
def get_value(g, offset, rate):
	start = offset * rate
	end = start + rate
	sum = 0

	g.debug = True
	debug_print(g, "start=" + start + " end=" + end)
	g.debug = False

	index=start
	while(index <= end):
		index+=1
		r = 0
		w = 0
		if index in g.reads:
			r = g.reads[index]
		if index in g.writes:
			w = g.writes[index]
		sum = sum + r + w

	g.debug = True
	debug_print(g, "s=" + sum)
	g.debug = False

	return sum
# get_value (DONE)

### Draw heatmap on color terminal
def draw_heatmap(g):
	return
# draw_heatmap (TODO)

### Cleanup temp files
def cleanup_files(g):
	verbose_print(g, "Cleaning up temp files\n")
	for file in g.cleanup:
		debug_print(g, file)
		os.system("rm -f " + file)
	os.system("rm -f filetrace.*.txt")
	return
# cleanup_files (DONE)

### run_cmd
def run_cmd(g, cmd):
	rc  = 0
	out = ""
	debug_print(g, "cmd: " + cmd)
	args = shlex.split(cmd)
	
	try:
		p = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
	except:
		print "ERROR: problem with Popen"
		sys.exit(1)
	try: 
		out, error = p.communicate()
	except:
		print "ERROR: problem with Popen.communicate()"
	rc = p.returncode
	if rc == 0:
		debug_print(g, "rc=" + str(p.returncode))
	return (rc, out)
		
# run_cmd

### regex_find
def regex_find(pattern, input):
	output = ()
	for line in input.split("\n"):
		match = re.search(pattern, line)
		try:
			output =  match.groups()
		except:
			pass
	return output
# regex_find

def printf(format, *args):
    sys.stdout.write(format % args)
# printf (DONE)

### MAIN
def main(argv):
	g = global_variables()

	check_args(g, argv)

	if g.mode == 'live' or g.mode == 'trace':
		mount_debugfs(g)

	if g.mode == 'trace':
		# Trace

		# Check sudo permissions
		rc = os.system("sudo -v &>/dev/null")
		if rc != 0:
			print "ERROR: You need to have sudo permissions to collect all necessary data.  Please run from a privilaged account."
			sys.exit(6)
		# Save fdisk info
		debug_print(g, "Running fdisk")
		fdisk_version = ""
		(rc, fdisk_version) = run_cmd(g, "fdisk -v")
		match = re.search("util-linux-ng", fdisk_version)
		if match:
			# RHEL 6.x
			os.system("fdisk -ul "+g.device+" > fdisk."+g.device_str)
		else:
			# RHEL 7.x
			os.system("fdisk -l -u=sectors "+g.device+" > fdisk."+g.device_str)

		os.system("rm -f blk.out.* &>/dev/null") # Cleanup previous mess
		runcount = g.runtime / g.timeout
		while runcount > 0:
			time_left = runcount * g.timeout
			percent_prog = (g.runtime - time_left) * 100  / g.runtime
			printf( "\r%d %% done (%d seconds left)", percent_prog, time_left)
			# BEN
			sys.stdout.flush()
			cmd = "blktrace -b " + str(g.buffer_size) + " -n " + str(g.buffer_count) + " -a queue -d " + str(g.device) + " -o blk.out." + str(g.device_str) + ".0 -w " + str(g.timeout) + " &> /dev/null"
			rc = os.system(cmd)
			if rc != 0:
				print "Unable to run the 'blktrace' tool required to trace all of your I/O"
				print "If you are using SLES 11 SP1, then it is likely that your default kernel is missing CONFIG_BLK_DEV_IO_TRACE"
				print "which is required to run blktrace.  This is only available in the kernel-trace version of the kernel."
				print "kernel-trace is available on the SLES11 SP1 DVD and you simply need to install this and boot to this"
				print "kernel version in order to get this working."
				print "If you are using a differnt distro or custom kernel, you may need to rebuild your kernel with the 'CONFIG_BLK 1f40 _DEV_IO_TRACE'"
				print "option enabled.  This should allow blktrace to function\n"
				print "ERROR: Could not run blktrace"
				sys.exit(7)
			cmd = "blkparse -i blk.out." + g.device_str + ".0 -q -f " + '" %d %a %S %n\n" | grep -v cfq | gzip --fast > blk.out.' + g.device_str + ".0.blkparse.gz;"
			rc = os.system(cmd)
			runcount -= 1
		print "\rMapping files to block locations                "
		if g.trace_files:
			find_all_files(g)
		tarball_name = g.device_str + ".tar"
		print "\rCreating tarball " + tarball_name
		filetrace = ""
		if g.trace_files:
			filetrace = "filetrace." + g.device_str + ".*.txt.gz"
		cmd = "tar -cf " + tarball_name + " blk.out." + g.device_str + ".*.gz fdisk." + g.device_str + " " + filetrace + " &> /dev/null"
		print cmd
		rc = os.system(cmd)
		if rc != 0:
			print "ERROR: failed to tarball " + tarball_name
			sys.exit(8)
		cmd = "rm -f blk.out." + g.device_str + ".*.gz; rm -f fdisk." + g.device_str + "; rm -f filetrace." + g.device_str + ".*.gz"
		rc = os.system(cmd)
		print "\rFINISHED tracing: " + tarball_name
		name = os.path.basename(__file__)
		print "Please use this file with " + name + " -m post -t " + tarball_name + " to create a report"

	elif g.mode == 'post':
		# Post 
		g.THREAD_MAX = multiprocessing.cpu_count() * 4
		cmd = 'tar -tf ' + g.tarfile 
		print g.tarfile
		(rc, file_text) = run_cmd(g, cmd)
		debug_print(g, file_text)
		file_list = []
		for i in file_text.split("\n"):
			debug_print(g, "i=" + i)
			if i != "":
				file_list.append(i)
		if rc != 0:
			print "ERROR: Failed to test input file: " + g.tarfile
			sys.exit(9)
		print "Unpacking " + g.tarfile + ".  This may take a minute"
		cmd = 'tar -xvf ' + g.tarfile
		(rc, out) = run_cmd(g, cmd)
		if rc != 0:
			print "ERROR: Failed to unpack input file: " + g.tarfile
			sys.exit(9)

		rc=0
		out=""
		(rc, out) = run_cmd(g, 'cat '+ g.fdisk_file )
		try:
			g.sector_size = int(regex_find("Units = sectors of \d+ \S \d+ = (\d+) bytes", out)[0])
		except:
			print "ERROR: Sector Size Invalid"
			sys.exit()
		try:
			g.total_lbas  = int(regex_find(".+ total (\d+) sectors", out)[0])
		except:
			print "ERROR: Sector Size Invalid"
			sys.exit()
		try:
			g.device      = regex_find("Disk (\S+): \S+ GB, \d+ bytes", out)[0]
		except:
			print "ERROR: Sector Size Invalid"
			sys.exit()
		verbose_print(g, "dev="+ g.device + " lbas=" + str(g.total_lbas) + " sec_size=" + str(g.sector_size))

		g.total_capacity_gib = g.total_lbas * g.sector_size / g.GiB
		printf("lbas: %d sec_size: %d total: %0.2f GiB\n", g.total_lbas, g.sector_size, g.total_capacity_gib)

		g.num_buckets = g.total_lbas * g.sector_size / g.bucket_size

		# Make the PDF plot a square matrix to keep gnuplot happy
		g.y_height = g.x_width = int(math.sqrt(g.num_buckets))
		debug_print(g, "x=" + str(g.x_width) + " y=" + str(g.y_height))

		g.debug=True
		debug_print(g, "num_buckets=" + str(g.num_buckets) + " sector_size=" + str(g.sector_size) + " total_lbas=" + str(g.total_lbas) + " bucket_size=" + str(g.bucket_size))
		g.debug=False
		rc = os.system("rm -f filetrace." + g.device_str + ".*.txt")
		rc = os.system("rm -f blk.out." + g.device_str + ".*.blkparse")
		print "Time to parse.  Please wait...\n"

		size = len(file_list)
		file_count = 0

		plist = []
		for file in file_list:
			file_count += 1
			perc = file_count * 100 / size
			printf("\rInput Percent: %d %% (File %d of %d) threads=%d", (file_count*100 / size), file_count, size, len(plist))
			sys.stdout.flush()
			try:
				new_file = regex_find("(blk.out.\S+).gz", file)[0]
			except:
				pass
			else:
				if g.single_threaded:
					thread_parse(g, new_file, file_count)
					debug_print(g, "blk.out hit = " + file + "\n")
				else:
					p = Process(target=thread_parse, args=(g, new_file, file_count))
					plist.append(p)
					p.start()
			try:
				new_file = regex_find("(filetrace.\S+.\S+.txt).gz", file)[0]
			except:
				pass
			else:
				g.trace_files=True
				debug_print(g, "filetrace hit = " + file + "\n")
				if g.single_threaded:
					parse_filetrace(g, new_file, file_count)
					debug_print(g, "blk.out hit = " + file + "\n")
				else:
					p = Process(target=parse_filetrace, args=(g, new_file, file_count))
					plist.append(p)
					p.start()
			while len(plist) > g.thread_max:
				for p in plist:
					try:
						p.join(0)
					except:
						pass
					else:
						if not p.is_alive():
							plist.remove(p)
				time.sleep(0.10)
		if g.single_threaded == False:
			x=1
			while len(plist) > 0:
				dots=""
				for i in xrange(x):
					dots = dots + "."
				x+=1
				if x>3:
					x=1
				printf("\rWaiting on %3d threads to complete processing%-3s", len(plist), dots)
				printf("    ")
				sys.stdout.flush()
				for p in plist:
					try:
						p.join(0)
					except:
						pass
					else:
						if not p.is_alive():
							plist.remove(p)
				time.sleep(0.10)
		print "\rFinished parsing files.  Now to analyze         \n"
		file_to_buckets(g)
		print_results(g)
		print_stats(g)
		draw_heatmap(g)
		if g.pdf == True:
			print_header_heatmap(g)
			print_header_histogram_iops(g)
			print_header_stats_iops(g)
			create_report(g)
		cleanup_files(g)
		
	elif g.mode == 'live':
		# Live
		print "Live Mode - Coming Soon ..."

	sys.exit()
# main (IN PROGRESS)

### Start MAIN
if __name__ == "__main__":
	main(sys.argv[1:])
