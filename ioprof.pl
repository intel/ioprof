#!/usr/bin/perl -w
# I/O Profiler
# Copyright (c) 2014, Intel Corporation.
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

### I/O profing tool
my $VERSION = '2.0.4';
print "$0 ($VERSION)\n";

my $VERBOSE         = 0;
my $DEBUG           = 0;
my $FASTFILE        = 1;
my $SINGLE_THREADED = 0;
my $READAHEAD       = 1;
my $THREAD_POOL     = 1;

use strict;
use POSIX ":sys_wait_h";
use Getopt::Std;
use threads;
use threads::shared;
use Thread::Semaphore;
use Thread::Queue;
$| = 1; # Force flush after every write/print

### Shared Variables: Locking requird when multi-threaded
my $io_total          :shared; # Number of total I/O's
my $read_total        :shared; # Number of buckets read (1 I/O can touch many buckets)
my $write_total       :shared; # Number of buckets written (1 I/O can touch many buckets)
my @reads             :shared; # Array of read hits by bucket ID
my @writes            :shared; # Array of write hits by bucket ID
my %r_totals          :shared; # Hash of read I/O's with I/O size as key
my %w_totals          :shared; # Hash of write I/O's with I/O size as key
my $bucket_hits_total :shared; # Total number of bucket hits (not the total buckets)
my $total_blocks      :shared; # Total number of LBA's accessed during profiling
my %files_to_lbas     :shared; # Files and the lba ranges associated with them
my $max_bucket_hits   :shared; # The hottest bucket
my @bucket_to_files   :shared; # List of files that reside on each bucket
my $TERM              :shared = 0; # Thread pool done with work
my $trace_files       :shared = 0; # Map filesystem files to block LBAs

### Semaphores: These are the locks for the shared variables
my $read_semaphore;            # Lock for the global read hit array
my $write_semaphore;           # Lock for the global write hit array
my $read_totals_semaphore;     # Lock for the global read totals
my $write_totals_semaphore;    # Lock for the global write totals
my $total_semaphore;           # Lock for the global I/O totals
my $total_blocks_semaphore;    # Lock for the global total LBA's accessed
my $files_to_lbas_semaphore;   # Lock for the global file->lba mapping hash
my $max_bucket_hits_semaphore; # Lock for the global maximum hits per bucket
my $bucket_to_files_semaphore; # Lock for the global bucket_to_files;
my $term_semaphore;            # Lock for the global TERM;
my $trace_files_semaphore;     # Lock for the global trace_files;

### Thread Queue
my $IDLE_QUEUE = Thread::Queue->new();

### Thread-local Variables: We use these to avoid locking constantly
my $thread_io_total=0;                   # Thread-local total I/O count (I/O ops)
my (%thread_r_totals, %thread_w_totals); # Thread-local I/O size counts (ops)
my $thread_bucket_hits_total=0;          # Thread-local total bucket hits (buckets)
my $thread_read_total=0;                 # Thread-local total read count (I/O ops)
my $thread_write_total=0;                # Thread-local total write count (I/O ops)
my %thread_reads;                        # Thread-local read count hash (buckets)
my %thread_writes;                       # Thread-local write count hash (buckets)
my $thread_total_blocks=0;               # Thread-local total blocks accessed (lbas)
my $thread_max_bucket_hits=0;            # Thread-local maximum bucket hits (bucket hits)

# Globals (Single-threaded, so no locking required)
my %file_hit_count;   # Count of I/O's to each file
my @files_to_cleanup; # Files to delete after running this script
my $CMD;              # Command to run
my $total_lbas;       # Total logical blocks, regardless of sector size
my $tar_file;         # .tar file outputted from 'trace' mode
my $fdisk_file;       # File capture of fdisk tool output
my @pidlist;          # Multi-process PID array, to keep track


my $top_files       = ""; # Top files list
my $dev             = ""; # Device (e.g. /dev/sda1)
my $dev_str         = ""; # Device string (e.g. sda1 for /dev/sda1)

### Unit Scales
my $KiB             = 1024;
my $MiB             = 1048576;
my $GiB             = 1073741824;

### Config Settings
my $bucket_size        = 10 * $MiB;   # Size of the bucket for totaling I/O counts (e.g. 1MB buckets)
my $num_buckets        = 1;          # Number of total buckets for this device
my $timeout            = 3;          # Seconds between each print
my $runtime            = 0;          # Runtime for 'live' and 'trace' modes
my $live_iterations    = 0;          # How many iterations for live mode.  Each iteration is $timeout seconds long
my $sector_size        = 512;        # Sector size (usually obtained with fdisk)
my $live               = 0;          # Live mode 0=disabled, 1=enabled (command line arg)
my $percent            = 0.020;      # Histogram threshold for each level (e.g. 0.02% of total drive size)
my $total_capacity_GiB = 0;          # Total drive capacity
my $mode               = "unknown";  # Processing mode (live, trace, post)
my $pdf_report         = 0;          # Generate a PDF report instead of a text report
my $top_count_limit    = 10;         # How many files to list in Top Files list (e.g. Top 10 files)
my $thread_count       = 0;          # Thread count
my $cpu_affinity       = 0;          # Tie each thread to a CPU for load balancing
my $thread_max         = 128;        # Maximum thread count
my $buffer_size        = 1024;       # blktrace buffer size
my $buffer_count       = 8;          # blktrace buffer count

### Gnuplot Settings
my $xwidth             = 800;        # gnuplot x-width
my $yheight            = 600;        # gnuplot y-height

### Analysis strings
my $analysis_histogram_iops = "Histogram analysis coming soon.\n";
my $analysis_heatmap        = "Heatmap analysis coming soon.\n";
my $analysis_stats_iops     = "IOPS analysis coming soon.\n";
my $analysis_stats_bw       = "Bandwidth analysis coming soon.\n";

### Heatmap Globals
my $SCALEX=5;  # Scale heatmap to term width - $SCALEX chars
my $SCALEY=20; # Scale heatmap to term height - $SCALEY chars
my $min_x=5;   # Minium terminal width in chars
my $min_y=5;   # Minimum terminal height in chars

### ANSI COLORS
my $black   = "\e[40m";
my $red     = "\e[41m";
my $green   = "\e[42m";
my $yellow  = "\e[43m";
my $blue    = "\e[44m";
my $magenta = "\e[45m";
my $cyan    = "\e[46m";
my $white   = "\e[47m";
my $none    = "\e[0m";

### Heatmap Key
my @colors=($white,$blue,$cyan,$green,$yellow,$magenta,$red);

### Heatmap Globals
my $color_index;              # Index in heatmap array
my $choices=scalar(@colors);  # Number of color choices
my $vpc;                      # VPC=Values Per Choice.  IOPS Range for each color
my $cap=0;                    # Maximum IOPS per heatmap block
#my @map;                      # IOPS map
my $rate;                     # How densely we pack buckets into heatmap blocks
my @block_map;                # Heatmap to print

### File Mapping Globals
my $fibmap       = 1;                   # FIBMAP ioctl number
my @ignorelist   = ("/sys", "/proc");   # Filesystem ignore list
my $extents;                            # EXT extents
my $mounttype;                          # Filesystem type (e.g. ext4)
my $mountpoint;                         # Mountpoint

### Print usage
sub usage
{
        print "Invalid command\n\n";
        print @ARGV;
        print "Usage:\n";
        print "$0 -m trace -d <dev> -r <runtime> [-v] [-f]   # run trace for post-processing later\n";
        print "$0 -m post  -t <dev.tar file>     [-v] [-p]   # post-process mode\n";
        print "$0 -m live  -d <dev> -r <runtime> [-v]        # live mode\n";
        print "\nCommand Line Arguments:\n";
        print "-d <dev>            : The device to trace (e.g. /dev/sdb).  You can run traces to multiple devices (e.g. /dev/sda and /dev/sdb)\n";
        print "                      at the same time, but please only run 1 trace to a single device (e.g. /dev/sdb) at a time\n";
        print "-r <runtime>        : Runtime (seconds) for tracing\n";
        print "-t <dev.tar file>   : A .tar file is created during the 'trace' phase.  Please use this file for the 'post' phase\n";
        print "                      You can offload this file and run the 'post' phase on another system.\n";
        print "-v                  : (OPTIONAL) Print verbose messages.\n";
        print "-f                  : (OPTIONAL) Map all files on the device specified by -d <dev> during 'trace' phase to their LBA ranges.\n";
        print "                       This is useful for determining the most fequently accessed files, but may take a while on really large filesystems\n";
        print "-p                  : (OPTIONAL) Generate a .pdf output file in addition to STDOUT.  This requires 'pdflatex', 'gnuplot' and 'terminal png'\n";
        print "                       to be installed.\n";
        exit;
} # sub usage

### Check arguments
sub check_args
{
        my %opt;
        getopts('m:d:t:fr:vpx', \%opt) or usage();
        print "check args\n" if ($VERBOSE);

        if(defined($opt{'v'}))
        {
                $VERBOSE=1;  # Enable verbose messaging, may slow things down
                print "VERBOSE enabled\n";
        }

	# Hidden DEBUG switch
	if(defined($opt{'x'}))
	{
                $VERBOSE=1;  # Enable verbose messaging, may slow things down
		$DEBUG=1;    # Enable debug messaging, will slow things down
                print "VERBOSE and DEBUG enabled\n";
	}

        if(!$opt{'m'}) { usage(); }
        $mode = $opt{'m'};
        print "Mode: $mode\n" if ($VERBOSE);

        if($mode eq 'live')
        {
                # Check for invalid args
                if(!$opt{'d'} || !$opt{'r'}) { usage(); }

                $dev = $opt{'d'};
                $runtime = $opt{'r'};
                print "Dev: $dev Runtime: $runtime\n" if ($DEBUG);

                $live=1;
                if ($dev =~ /\/dev\/(\S+)/) { $dev_str = $1; }
                $dev_str =~ s/\//_/g;
                print "str: $dev_str\n" if($DEBUG);
		die("ERROR: dev_str=$dev_str invalid") if ($dev_str eq "");

                # Check if $dev is not a block special file
        	die("ERROR: Cannot find $dev or $dev is not a block special file") if (! -b $dev);
        }
        elsif($mode eq 'post')
        {
                # Check Args
                if (!$opt{'t'}) { usage(); }
                $tar_file = $opt{'t'};

                if($tar_file =~ /(\S+).tar/)
                {
                        $dev_str = $1;
                }
		die("ERROR: dev_str=$dev_str invalid") if ($dev_str eq "");

                if ($opt{'p'})
                {
                        check_pdf_prereqs();
                        $pdf_report = 1;
                }
                $fdisk_file = "fdisk.$dev_str";
                print "fdisk_file: $fdisk_file\n" if ($DEBUG);
                print "Option -t $tar_file\n" if($DEBUG);
                push(@files_to_cleanup, $fdisk_file);

                die("ERROR: Cannot find $tar_file or $tar_file is not a plain file") if (! -f $tar_file);
        }
        elsif($mode eq 'trace')
        {
                check_trace_prereqs();
                # Check for invalid args
                if(!$opt{'d'} || !$opt{'r'}) { usage(); }

                if($opt{'f'}) { $trace_files = 1 ;}
                print "Trace files = $trace_files\n" if($DEBUG);

                $dev = $opt{'d'};
                $runtime = $opt{'r'};
                print "Runtime: $runtime\n" if ($DEBUG);

                if ($dev =~ /\/dev\/(\S+)/) { $dev_str = $1; }
                $dev_str =~ s/\//_/g;
                print "Option -d $dev\n" if($DEBUG);
                print "str: $dev_str\n" if($DEBUG);
		die("ERROR: dev_str=$dev_str invalid") if ($dev_str eq "");

                # Check if $dev is not a block special file
        	die("ERROR: Cannot find $dev or $dev is not a block special file") if (! -b $dev);
        }
        else
        {
                usage();
        }

        return;
}

### Check prereqs for gnuplot and latex
sub check_pdf_prereqs
{
        `which gnuplot`;
        if ($? != 0) { die("ERROR: gnuplot not installed.  Please offload the trace file for processing."); }
        `which pdflatex`;
        if ($? != 0) { die("ERROR: pdflatex not installed.  Please offload the trace file for processing."); }
        `echo 'set terminal png' > pngtest.txt; gnuplot pngtest.txt >/dev/null 2>&1`;
        if ($? != 0) { `rm -f pngtest.txt`; die("ERROR: gnuplot PNG terminal not installed.  Please offload the trace file for processing."); }
        `rm -f pngtest.txt`;
}

### Check prereqs for blktrace
sub check_trace_prereqs
{
        `which blktrace`;
        if ($? != 0) { die("ERROR: blktrace not installed.  Please install blktrace"); }
        `which blkparse`;
        if($? != 0) { die("ERROR: blkparse not installed.  Please install blkparse"); }
}

### Check if debugfs is mounted
sub mount_debugfs
{
        `mount | grep debugfs >/dev/null`;
        if($?)
        {
                print "Need to mount debugfs\n" if ($VERBOSE);
                `mount -t debugfs debugfs /sys/kernel/debug`;
                if($? !=0 ) { die("ERROR: Failed to mount debugfs"); }
                print "mounted debugfs successfully\n" if ($VERBOSE);
        }
        return;
}

sub lba_to_bucket
{
        my $lba = shift;
        return int($lba * $sector_size / $bucket_size);
}

sub bucket_to_lba
{
        my $bucket = shift;
        return int($bucket * $bucket_size / $sector_size);
}

# debufs method
# This method can only be used on ext2/ext3/ext4 filesystems
# I don't plan on using this method right now
# In testing the debugfs method, I found it to be approximately 30% slower than the ioctl method
sub debugfs_method
{
        my $file = shift;
        $extents = "";
        $file =~ s/$mountpoint//;
        print "file: $file\n" if ($DEBUG);
        my @extent_out = `debugfs -R "dump_extents $file" $dev 2>/dev/null`;

        # Pattern
        #0/ 0   1/  1     0 -  3701  7440384 -  7444085   3702
        foreach my $line (@extent_out)
        {
                print $line if ($DEBUG);
                if($line =~ /\s+\d+\/\s+\d+\s+\d+\/\s+\d+\s+\d+\s+-\s+\d+\s+(\d+)\s+-\s+(\d+)/)
                {
                        $extents .= "$1:$2 ";
                        print "$extents\n" if ($DEBUG);
                }
        }
}

# Filesystem cluter (io_block_size) to LBA
sub fs_cluster_to_lba
{
        my $fs_cluster_size = shift;
        my $sector_size     = shift;
        my $io_cluster      = shift;

        return $io_cluster * ($fs_cluster_size / $sector_size);
}

# ioctl method
# This method "should" be usable regardless of filesystem
# There is some risk that FIBMAP!=1.  Need to address this later
# I plan to use the ioctl method because it is 30% faster than the debugfs method
sub ioctl_method
{
        my $file = shift;
        my $FH;
        my $output = "";
        my $start=-1;
        my $end=-1;
        my $prev=-1;
        my $cluster_id;
        #my $contig = "Contig";


       print "#$file#\n" if ($DEBUG);
       #my $fs_cluster_size = `stat '$file' | grep "IO Block"| awk '{ print \$7 }'`;
       #my $file_blocks = `stat '$file' | grep Blocks | awk '{ print \$4 }'`;

	my ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size, $atime,$mtime,$ctime,$blksize,$blocks) = stat($file);
	my $fs_cluster_size = $blksize;
	my $file_blocks = $blocks;

	my $file_size = -s $file;
	my $io_blocks = ($file_blocks * $sector_size) / $fs_cluster_size;
	if (!defined($fs_cluster_size) || $fs_cluster_size == 0) { return; }
	my $file_clusters = ($file_blocks * $sector_size) / $fs_cluster_size;

	open($FH, "<", $file) or die("ERORR: Failed to open file $file");

	my $log_id_a = 0;
	my $log_id_b = int($file_clusters);
	my $arg_a = pack "I", $log_id_a;
	my $arg_b = pack "I", $log_id_b;
	ioctl($FH, $fibmap, $arg_a) or die("ERROR: ioctl failed $!");
	ioctl($FH, $fibmap, $arg_b) or die("ERROR: ioctl failed $!");
	my $cluster_id_a = unpack "I", $arg_a;
	my $cluster_id_b = unpack "I", $arg_b;
	if($file_clusters == ($cluster_id_b - $cluster_id_a))
	{
		close($FH);
		my $start_lba = fs_cluster_to_lba($fs_cluster_size, $sector_size, $cluster_id_a);
		my $end_lba   = fs_cluster_to_lba($fs_cluster_size, $sector_size, $cluster_id_b);
		$output = "$start_lba:$end_lba";
		return;
	}

	if ($READAHEAD)
	{
		my $log_id = 0;
		my $skip   = 1;
		my $prev_log_id = -1;
		while ($log_id <= int($file_clusters))
		{
                        my $arg = pack "I", $log_id;
                        ioctl($FH, $fibmap, $arg) or die("ERROR: ioctl failed $!");
                        if($? != 0) { next; }
                        $cluster_id = unpack "I", $arg;
                        print "$file : log=$log_id prev=$prev_log_id : cid=$cluster_id previd=$prev: skip=$skip\n" if ($DEBUG);
			

                        if ($start == -1)
                        {
                                $start = fs_cluster_to_lba($fs_cluster_size, $sector_size, $cluster_id);
                                $output .= "$start:";
                        }

                        if ($cluster_id == ($prev + $skip))
                        {
                                print "Contig!\n" if ($DEBUG);
				$prev_log_id = $log_id;
                        	$prev = $cluster_id;

				# Keep doubling readahead value (aka skip)
				$skip = ($skip == (1<<16)) ? 32 : $skip << 1;

				$log_id += $skip;
				next;
                        }
			elsif(($skip != 1) && ($prev != -1))
			{
				print "Not Contig, skip miss, skip=$skip\n" if ($DEBUG);
				$log_id = $prev_log_id;
				$skip = 1;
			}
                        elsif($prev != -1)
                        {
                                my $prev_lba = fs_cluster_to_lba($fs_cluster_size, $sector_size, $prev);
                                my $curr_lba = fs_cluster_to_lba($fs_cluster_size, $sector_size, $cluster_id);

                                if($prev_lba != 0)
                                {
                                        $output .= "$prev_lba ";
                                }
                                if($cluster_id != 0)
                                {
                                        $output .= "$curr_lba:";
                                }
                                print "Not Contig, skip=$skip\n" if ($DEBUG);
                                #$contig = "Not Contig";
                        }

                        $prev = $cluster_id;
			$log_id += $skip;
		}

                $end = fs_cluster_to_lba($fs_cluster_size, $sector_size, $cluster_id);
                if ($end != 0)
                {
                        $output .= "$end";
                }
	}
	else
	{
                for (0 .. int($file_clusters))
                {
                        my $log_id = $_;
                        my $arg = pack "I", $log_id;
                        ioctl($FH, $fibmap, $arg) or die("ERROR: ioctl failed $!");
                        if($? != 0) { next; }
                        $cluster_id = unpack "I", $arg;
                        print "$file : $log_id : $cluster_id\n" if ($DEBUG);
                        if ($start == -1)
                        {
                                $start = fs_cluster_to_lba($fs_cluster_size, $sector_size, $cluster_id);
                                $output .= "$start:";
                        }

                        if ($cluster_id == ($prev + 1))
                        {
                                print "Contig!\n" if ($DEBUG);
                        }
                        elsif($prev != -1)
                        {
                                my $prev_lba = fs_cluster_to_lba($fs_cluster_size, $sector_size, $prev);
                                my $curr_lba = fs_cluster_to_lba($fs_cluster_size, $sector_size, $cluster_id);

                                if($prev_lba != 0)
                                {
                                        $output .= "$prev_lba ";
                                }
                                if($cluster_id != 0)
                                {
                                        $output .= "$curr_lba:";
                                }
                                print "Not Contig\n" if ($DEBUG);
                                #$contig = "Not Contig";
                        }
                        $prev = $cluster_id;
                }
                $end = fs_cluster_to_lba($fs_cluster_size, $sector_size, $cluster_id);
                if ($end != 0)
                {
                        $output .= "$end";
                }
	}

	close($FH);
	print "$output\n" if ($DEBUG);
	$extents = $output;

}

### Print filetrace files
sub printout
{
        my $file = shift;
        my $OUT;
        print "printout: $file\n" if($DEBUG);
        open ($OUT,">>", "filetrace.$dev_str.$cpu_affinity.txt") ||  die("ERROR: Failed to open filetrace.$dev_str.$cpu_affinity.txt");
        print $OUT "$file :: $extents\n";
        close($OUT);
}

### Find block ranges of each file
sub block_ranges
{
        my $file = shift;
        print "block_ranges: $file\n" if($DEBUG);

        if ($file =~ /^\/proc/) { print "/proc file: $file\n" if($DEBUG); return; }
        if ($file =~ /^\/sys/)  { print "/sys file: $file\n" if ($DEBUG); return; }
        if ((-l $file) || (!-f $file) || (-z $file)) { print "Disqualified file: $file\n" if ($DEBUG); return; }


        if ($mounttype eq "ext4")
        {
                #debugfs_method($file);
                ioctl_method($file);
        }
        elsif ($mounttype eq "ext3")
        {
                ioctl_method($file);
        }
        else
        {
                die("ERROR: $mounttype is not supported yet");
        }

        printout($file);
}

### Find all files on device
sub find_all_files
{
        my @FILES;
        `rm -f filetrace.*`;
        my $cpu_count = `cat /proc/cpuinfo | grep processor | wc -l`;

        $mountpoint = `mount | grep $dev | awk '{ print \$3 }'`;
        if ($? != 0 )
        {
                print "$dev not mounted\n";
                return;
        }
        chomp($mountpoint);
        print "\nmountpoint: $mountpoint\n" if ($VERBOSE);
        $mounttype = `mount | grep $dev | awk '{ print \$5 }'`;
        chomp($mounttype);
        print "mounttype: $mounttype\n" if ($VERBOSE);

        if($FASTFILE)
        {
                my $FH;
                `find $mountpoint -xdev -name "*" > ioprof_files.$dev_str.txt`;
                open($FH, "<", "ioprof_files.$dev_str.txt") or die("ERROR: Failed to open file ioprof_files.$dev_str.txt");
                while (<$FH>)
                {
                        push(@FILES, $_);
                }
                close($FH);
        }
        else
        {
                @FILES = `find $mountpoint -mount -name "*"`;
        }

        my $file_count = scalar(@FILES);
        print "filecount=$file_count\n" if($VERBOSE);
        print @FILES if($DEBUG);

        my $set_count = int($file_count / $cpu_count) + 1;
        print "set_count=$set_count\n" if ($DEBUG);

	if($SINGLE_THREADED)
	{
		my $k = 0;
        	for (0 .. $file_count)
        	{
        		my $progress = $_ / $file_count * 100;
                	if ($k > 100)
                        {
                        	printf "\r%05.2f%% COMPLETE", $progress;
                        	$k =0;
                        }
                        $k++;
                        my $file = $FILES[$_];
                        if (defined $file)
                        {
				chomp($file);
				print "$file\n" if($DEBUG);

				block_ranges($file);
                        }
		}
	}
	else
	{

        	for(0 .. ($cpu_count-1))
        	{
                	$cpu_affinity = $_ % $cpu_count;
                	print "$cpu_affinity\n" if ($DEBUG);
                	my $pid = fork();
                	if($pid < 0)
                	{
                        	# Failed to fork
                        	die("ERROR: Failed to fork process\n");
                	}
                	elsif($pid == 0)
                	{
                        	# Child process
                        	my $start = 0 + ($set_count * $cpu_affinity);
                        	if($start > $file_count) {exit; }
                        	my $end = ($set_count * ($cpu_affinity + 1)) - 1;
                        	$end = ($end >= $file_count) ? $file_count : $end;
                        	print "$cpu_affinity: start=$start end=$end\n" if ($VERBOSE);
				my $range = $end - $start;
	
                        	#if ($range == 0) { exit; }
                        	my $k = 0;
	
                        	for ($start .. $end)
                        	{
                                	if ($range >0)
                                	{
                                        	my $progress = ($_ - $start) / $range * 100;
                                        	if ($k > 100)
                                        	{
                                                	printf "\r%05.2f%% COMPLETE", $progress;
                                                	$k =0;
                                        	}
                                        	$k++;
                                	}
                                	my $file = $FILES[$_];
                                	if (defined $file)
                                	{
                                        	chomp($file);
                                        	print "$cpu_affinity: $file\n" if($DEBUG);
	
                                        	block_ranges($file);
                                	}
                        	}
                        	exit;
                	}
                	else
                	{
                        	# Parent process
                        	print "pid=$pid CPU=$cpu_affinity\n" if ($DEBUG);
                        	push(@pidlist, $pid);
                        	my $hexcpu = sprintf("0x%08x", (1 << $cpu_affinity));
                        	print "hexcpu=$hexcpu\n" if ($DEBUG);
                        	`taskset -p $hexcpu $pid`;
                        	print "running $cpu_affinity\n" if ($DEBUG);
                	}
        	}

        	print "\n\nWaiting on threads to finish\n\n";
        	foreach my $pid (@pidlist)
        	{
                	do
                	{
                        	print("\rWaiting on $pid                   ");
                	} while (!waitpid($pid, 0));
        	}
        	print "\nDONE!\n";
        	print "Compressing files\n";
	}
        `gzip --fast filetrace.*`;
}

### Translate a bucket ID to a list of files
sub bucket_to_file_list
{
        my $bucket_id = shift;
        my @list;
        if(defined($bucket_to_files[$bucket_id]))
        {
                @list = split(" ", $bucket_to_files[$bucket_id]);

        }
        if (scalar(@list) == 1 && $list[0] eq ' ')
        {
                undef(@list);
        }

        return @list;
}


### Translate a file to a list of buckets
sub file_to_buckets
{
        my $k=0;
        my @threads;
        my $size = scalar(keys %files_to_lbas);

        foreach my $file (keys %files_to_lbas)
        {
                $k++;
                if($k % 100 == 0) { printf( "\rfile_to_buckets: %d %% (%d of %d)", ($k*100 / $size), $k, $size); }
		
                	$file_hit_count{$file}=0; # Initialize file hit count
	
                	foreach my $range (split(" ", $files_to_lbas{$file}))
                	{
                        	my ($start, $finish) = split(':', $range);
                        	print "$file start=$start, finish=$finish\n" if ($DEBUG);
                        	next if ($start eq '' || $finish eq '');
                        	my $start_bucket = lba_to_bucket($start);
                        	my $finish_bucket = lba_to_bucket($finish);
	
                        	print "$file s_lba=$start f_lba=$finish s_buc=$start_bucket f_buc=$finish_bucket\n" if ($DEBUG);
	
                        	for(my $i=$start_bucket; $i<=$finish_bucket; $i++)
                        	{
                                	if (defined($bucket_to_files[$i]))
                                	{
                                        	# Wrap $file in \Q \E to quote meta chars, trust me
                                        	if(!$bucket_to_files[$i] =~ /\Q$file\E/)
                                        	{
                                                	$bucket_to_files[$i] .= "$file ";
                                        	}
                                	}
                                	else
                                	{
                                        	$bucket_to_files[$i] .= "$file ";
                                	}
                        	}
                	}
	}


        print "\rDone correlating files to buckets.  Now time to count bucket hits.\n";

        # Print all files
        if($trace_files && $DEBUG)
        {
                print "--------------------------------------\n";
                print "Buckets to file list:\n";
                for(my $i=0; $i<$num_buckets; $i++)
                {
                        my @list = bucket_to_file_list($i);
                        my $length = @list;
                        if ($length > 0)
                        {
                                print "$i($length): ";
                                print @list;
                                print "\n";
                        }
                }
                print "--------------------------------------\n";
        }
        return;
}

## Add up I/O hits to each file touched by a bucket
sub add_file_hits
{
        my $bucket_id = shift;
        my $io_count  = shift;
        my @list      = bucket_to_file_list($bucket_id);
        if(scalar(@list) == 0 && $io_count != 0) { print "No file hit.  bucket=$bucket_id, io_cnt=$io_count\n" if ($DEBUG);}
        foreach my $file (@list)
        {
                $file_hit_count{$file} += $io_count;
        }
}

### Get logrithmic theta for Zipfian distribution
sub theta_log
{
        my $base = shift;
        my $value = shift;
        print "base=$base, value=$value\n" if($DEBUG);
        return log($value)/log($base);
}

### Print results
sub print_results
{
        my $num = defined($1) ? $1 : 0;
        my $sum;
        my $k=0;
        my ($DATA, $DATA2, $HEADER, $STATS);
        my $buffer = "";
        my $i;
        my ($read_sum, $write_sum);
        my %counts;
        $read_sum = $write_sum = 0;
        my ($row, $column);
        $row=$column=0;
        my $bw_total=0;
        my @histogram_iops;
        my @histogram_bw;

        print "num_buckets=$num_buckets bucket_size=$bucket_size\n" if($VERBOSE);
        print `date` if ($DEBUG);

        if($pdf_report)
        {
                open($DATA, ">data.$dev_str.$num") || die ("ERROR: Could not open: data");
        }

	my $x=0;
	my $threshold = $num_buckets / 100;
        for($i=0; $i<$num_buckets; $i++)
        {
		$x++;
                if ($x > $threshold)
                {
                        printf( "\rBucket Percent: %d %%", ($i / $num_buckets * 100));
			$x=0;
                }
                if ($i!=0 && ($i % $xwidth) == 0)
                {
                        if($pdf_report)
                        {
                                print $DATA "$buffer\n";
                        }
                        $buffer="";
                        $row++;
                        $column=0;
                }
                my $r = defined($reads[$i]) ? $reads[$i] : 0;
                my $w = defined($writes[$i]) ? $writes[$i] : 0;
                my $bucket_total = $r + $w;
                $bw_total += $bucket_total * $bucket_size;
                print "$i: bt=$bucket_total\n" if ($DEBUG);
                add_file_hits($i, $bucket_total) if ($trace_files);
                $counts{$bucket_total}++;
                $read_sum  += $r;
                $write_sum += $w;

                $buffer .= sprintf("%d ", $bucket_total);
                #push(@map,$bucket_total);

                #$reads[$i]=0;
		#$writes[$i]=0;
		#undef($reads[$i]);
		#undef($writes[$i]);

                $column++;
        }
        print "\r                    \n";
        while (($i % $xwidth) != 0) { $i++; $buffer .= "0 "; }
        if($pdf_report)
        {
                print $DATA "$buffer\n";
                close($DATA);
                push(@files_to_cleanup, "data.$dev_str.$num");
        }

        print "num_buckets=$num_buckets pfgp iot=$io_total bucket_hits_total=$bucket_hits_total r_sum=$read_sum w_sum=$write_sum yheight=$yheight\n" if($VERBOSE);

        print `date` if ($DEBUG);
        my $t=0;
        my $j=0;
        my $section_count=0;
        my $b_count=0;
        my $GB_tot=0;
        my $bw_tot=0;
        my $bw_count=0;
        my $io_sum=0;
        my $tot=0;
        if($pdf_report)
        {
                open($DATA, ">histogram_iops.$dev_str.$num") || die("ERROR: Could not open: histogram_iops.$dev_str.$num");
                open($DATA2, ">histogram_bw.$dev_str.$num") || die("ERROR: Could not open: histogram_bw.$dev_str.$num");
        }

        # %counts is a hash
        # each key "bucket_total" represents a particular I/O count for a bucket
        # each value represents the number of buckets that had this I/O count
        # This allows me to quickly tally up a histogram and is pretty
        # space efficient since most buckets tend to have zero I/O that
        # key tends to have the largest number of buckets
        #
        # Iterate through each key in decending order
        my $max_set=0;
        my $max=0;
        my $theta_count=1;
        my $theta_total=0;
        my $min=1;
        my $max_theta=0;
        my $min_theta=999;
        for my $total ( sort {$b<=>$a} keys %counts)
        {
                if ($total)
                {
                        print "$total: $counts{$total}\n" if ($DEBUG);
                        $tot += $total * $counts{$total};
                        print "tot=$tot\n" if($DEBUG);

                        if (!$max_set)
                        {
                                $max_set = 1;
                                $max = $total;
                        }
                        else
                        {
                                $theta_count++;
                                $min = $total;
                                my $cur_theta = theta_log($theta_count, $max) - theta_log($theta_count, $total);
                                $max_theta = ($cur_theta > $max_theta) ? $cur_theta : $max_theta;
                                $min_theta = ($cur_theta < $min_theta) ? $cur_theta : $min_theta;
                                print "cur_theta: $cur_theta\n" if ($DEBUG);
                                $theta_total += $cur_theta;
                        }

                        for(my $i=0; $i< $counts{$total}; $i++)
                        {
                                $section_count += $total;
                                $b_count++;
                                $bw_count += $total * $bucket_size;
                                if(($b_count*$bucket_size/$GiB) > ($percent * $total_capacity_GiB))
                                {
                                        print "b_count: $b_count\n" if ($DEBUG);
                                        $bw_tot += $bw_count;
                                        $GB_tot += ($b_count * $bucket_size);
                                        $io_sum += $section_count;

                                        my $GB = sprintf("%.1f", $GB_tot / $GiB);
                                        my $io_perc = sprintf("%.1f", ($section_count / $bucket_hits_total)*100);
                                        my $bw_perc = sprintf("%.1f", ($bw_count / $bw_total)*100);
                                        my $io_sum_perc = sprintf("%.1f", ($io_sum/($bucket_hits_total))*100);

                                        if($pdf_report)
                                        {
                                                print $DATA "\"$GB GB\" $io_perc $section_count $io_sum_perc $io_sum\n";
                                                print $DATA2 "\"$GB GB\" $bw_perc $bw_count\n";
                                        }
                                        push(@histogram_iops, "$GB GB $io_perc% ($io_sum_perc% cumulative)");
                                        push(@histogram_bw,   "$GB GB $bw_perc%");

                                        $b_count=0;
                                        $section_count=0;
                                        $bw_count=0;
                                }
                        }
                }
        }
        if ($b_count)
        {
                print "b_count: $b_count\n" if ($DEBUG);
                $bw_tot += $bw_count;
                $GB_tot += ($b_count * $bucket_size);
                $io_sum += $section_count;

                my $GB = sprintf("%.1f", $GB_tot / $GiB);
                my $io_perc = sprintf("%.1f", ($section_count / $bucket_hits_total)*100);
                my $bw_perc = sprintf("%.1f", ($bw_count / $bw_total)*100);
                                        my $io_sum_perc = sprintf("%.1f", ($io_sum/($bucket_hits_total))*100);

                if($pdf_report)
                {
                        print $DATA "\"$GB GB\" $io_perc $section_count $io_sum_perc $io_sum\n";
                        print $DATA2 "\"$GB GB\" $bw_perc $bw_tot\n";
                }
                push(@histogram_iops, "$GB GB $io_perc% ($io_sum_perc% cumulative)");
                push(@histogram_bw,   "$GB GB $bw_perc%");

                $b_count=0;
                $section_count=0;
                $bw_count=0;
        }
        if($pdf_report)
        {
                print $DATA "\" \" 0 0 0 0\n";
                close($DATA);
        }
        print "t=$t\n" if($DEBUG);
        print `date` if($DEBUG);

        print "--------------------------------------------\n";
        print "Histogram IOPS:\n";
        foreach my $entry (@histogram_iops)
        {
                print "$entry\n";
        }
        print "--------------------------------------------\n";

        #print "Histogram BW:\n";
        #print "--------------------------------------------\n";
        #foreach my $entry (@histogram_bw)
        #{
                #print "$entry\n";
        #}
        #print "--------------------------------------------\n";

        if ($theta_count)
        {
                #my $cur_theta = theta_log($theta_count, $max) - theta_log($theta_count, $min);
                my $avg_theta = $theta_total / $theta_count;
                my $med_theta = (($max_theta - $min_theta) / 2) + $min_theta;
                my $approx_theta = ($avg_theta + $med_theta) / 2;
                print "avg_t=$avg_theta med_t=$med_theta approx_t=$approx_theta min_t=$min_theta max_t=$max_theta\n" if ($VERBOSE);
                $analysis_histogram_iops = sprintf("Approximate Zipfian Theta Range: %0.4f-%0.4f (est. %0.4f).\n", $min_theta, $max_theta, $approx_theta);
                print "$analysis_histogram_iops";
        }

        # Print top hit files by sorting hash in numerical order by value
	print "Trace_files: $trace_files\n";
        if($trace_files)
        {
                my $top_count=0;
                print "--------------------------------------------\n";
                print "Top files by IOPS:\n";
                print "Total Hits: $bucket_hits_total\n";
                foreach my $filename (sort {$file_hit_count{$b} <=> $file_hit_count{$a}} keys %file_hit_count)
                {
                        my $hits = $file_hit_count{$filename};
                        #if ($hits > ($bucket_hits_total/ 100))
                        if ($hits > 0)
                        {
                                my $hit_rate = $hits / $bucket_hits_total * 100;
                                printf "%0.2f%% (%d) %s\n", $hit_rate, $hits, $filename;
                                $top_files .= sprintf "%0.2f%%: (%d) %s\n", $hit_rate, $hits, $filename;
                        }
                        $top_count++;
                        if($top_count > $top_count_limit) { last; }
                }
                print "--------------------------------------------\n";
        }
        if($pdf_report)
        {
                push(@files_to_cleanup, "histogram_iops.$dev_str.$num", "histogram_bw.$dev_str.$num");
        }

} # print_results

### Print heatmap header for PDF
sub print_header_heatmap
{
        my ($DATA, $HEADER, $STATS);
        my $num = defined($1) ? $1 : 0;

        open($HEADER, ">header_heatmap.$dev_str.$num");
        print $HEADER "set terminal pngcairo enhanced font \"arial,10\" fontscale 1.0 size 800, 600\n";
        #print $HEADER "set terminal x11 size 800, 600\n";
        print $HEADER "set output 'heatmap_${dev_str}_${num}.png'\n";
        print $HEADER "unset key\n";
        print $HEADER "set view map\n";
        print $HEADER "set format x ''\n";
        print $HEADER "set format y ''\n";
        #print $HEADER "set xtics border in scale 0,0 mirror norotate  offset character 0, 0, 0 autojustify\n";
        #print $HEADER "set ytics border in scale 0,0 mirror norotate  offset character 0, 0, 0 autojustify\n";
        print $HEADER "set ztics border in scale 0,0 nomirror norotate  offset character 0, 0, 0 autojustify\n";
        #print $HEADER "set nocbtics\n";
        print $HEADER "set rtics axis in scale 0,0 nomirror norotate  offset character 0, 0, 0 autojustify\n";
        print $HEADER "set title \"Heat Map of IOPS over $dev\"\n";
        print $HEADER "set xrange [ 0 : $xwidth] noreverse nowriteback\n";
        print $HEADER "set yrange [ 0 : $yheight ] noreverse nowriteback\n";
        print $HEADER "set cblabel \"Total I/O's during test\"\n";
        print $HEADER "set palette defined (1 'white', 10 'blue', 20 'green', 60 'yellow', 70 'orange', 100 'red')\n";
        print $HEADER "plot 'data.$dev_str.$num' matrix with image\n";
        #print $HEADER "pause 1\n";
        close($HEADER);
        push(@files_to_cleanup, "header_heatmap.$dev_str.$num", "heatmap_${dev_str}_${num}.png");

        `gnuplot header_heatmap.$dev_str.$num`;
        if($? != 0 ) { die("ERROR: Failed to run gnuplot header_heatmap.$dev_str.$num Error: $!"); }

        print "ph iot=$io_total\n" if ($DEBUG);
} # print_header

### Print histogram header for PDF
sub print_header_histogram_iops
{
        my $HEADER;
        my $num = defined($1) ? $1 : 0;
        print "HEADER TIME!\n" if ($DEBUG);

        open($HEADER, ">header_histogram_iops.$dev_str.$num");
        print $HEADER "set terminal pngcairo enhanced font 'arial,10' fontscale 1.0 size 800, 600\n";
        print $HEADER "set output \'histogram_iops_${dev_str}_${num}.png\'\n";
        print $HEADER "set auto x\n";
        print $HEADER "set xlabel 'GB of capacity accessed by I/O'\n";
        print $HEADER "set ylabel '% of Total I/O'\n";
        print $HEADER "set title 'I/O distribution throughout total disk space'\n";
        print $HEADER "set style histogram clustered\n";
        print $HEADER "set boxwidth 0.95 relative\n";
        print $HEADER "set style fill transparent solid 0.5 noborder\n";
        #print $HEADER "set style fill transparent solid 0.5 noborder\n";
        print $HEADER "set xtics rotate by -90\n";
        #print $HEADER "set auto y\n";
        #print $HEADER "plot \'histogram_iops.$dev_str.$num\' using 2:xticlabels(1) with boxes lc rgb'blue90'\n";
        #print $HEADER "set y2range [0:100]\n";
        #print $HEADER "set yrange [0:9.0]\n";
        #print $HEADER "set y2tics 10 nomirror tc lt 2\n";
        #print $HEADER "set ytics 5 nomirror tc lt 1\n";
        #print $HEADER "set y2label 'stuff' tc lt 2\n";
        #print $HEADER "plot \'histogram_iops.$dev_str.$num\' using 2:xticlabels(1) with boxes lc rgb'blue90' linetype 1, '' u 0:4 with lines linetype 2\n";
        print $HEADER "plot \'histogram_iops.$dev_str.$num\' using 2:xticlabels(1) with boxes lc rgb'blue90'\n";
        close($HEADER);
        push(@files_to_cleanup, "header_histogram_iops.$dev_str.$num", "histogram_iops_${dev_str}_${num}.png");

        `gnuplot header_histogram_iops.$dev_str.$num`;
        if($? != 0 ) { die("ERROR: Failed to run gnuplot header_histogram_iops.$dev_str.$num Error: $!"); }

} # print_header_histogram_iops

### Print stats header for PDF
sub print_header_stats_iops
{
        my $HEADER;
        my $num = defined($1) ? $1 : 0;
        print "HEADER TIME!\n" if ($DEBUG);

        open($HEADER, ">header_stats_iops.$dev_str.$num");
        print $HEADER "set terminal pngcairo enhanced font 'arial,10' fontscale 1.0 size 800, 600\n";
        print $HEADER "set output \'stats_iops_${dev_str}_${num}.png\'\n";
        print $HEADER "set auto x\n";
        print $HEADER "set yrange [0:100]\n";
        print $HEADER "set ylabel '% of Total I/O'\n";
        print $HEADER "set xlabel 'I/O Size'\n";
        print $HEADER "set title 'I/O Distribution by I/O Size'\n";
        print $HEADER "set style histogram clustered\n";
        print $HEADER "set boxwidth 0.95 relative\n";
        print $HEADER "set style fill transparent solid 0.5 noborder\n";
        print $HEADER "set xtics rotate by -90\n";
        print $HEADER "set grid\n";
        print $HEADER "set ytics 5\n";
        #print $HEADER "plot \'histogram_iops.$dev_str.$num\' using 2:xticlabels(1) with boxes lc rgb'blue90', ""  notitle\n";
        print $HEADER "plot \'stats_iops.$dev_str.$num\' using 2:xticlabels(1) with boxes lc rgb'blue90' notitle\n";
        #print $HEADER "plot \'stats_iops.$dev_str.$num\' using 2:xticlabels(1) with labels lc rgb'blue90'\n";
        close($HEADER);
        push(@files_to_cleanup, "header_stats_iops.$dev_str.$num", "stats_iops_${dev_str}_${num}.png");

        `gnuplot header_stats_iops.$dev_str.$num`;
        if($? != 0 ) { die("ERROR: Failed to run gnuplot header_histogram_iops.$dev_str.$num Error: $!"); }

} # print_header_histogram_iops

### Create PDF report
sub create_report
{
        my $LATEX;
        my $num = defined($1) ? $1 : 0;

        print "REPORT TIME!\n" if ($DEBUG);

        open($LATEX, ">report.$dev_str.tex");
        print $LATEX "\\documentclass{article}\n";
        print $LATEX "\\usepackage{graphicx}\n";
        print $LATEX "\n";
        print $LATEX "\\begin{document}\n";
        print $LATEX "\\section{IO Profiling Report}\n";
        print $LATEX "\\subsection{Summary}\n";
        print $LATEX "$analysis_stats_iops\n";
        print $LATEX "\n\nPlease make sure to review the important notes in the section \"Caveat Emptor\" at the bottom of this document.\n";
        print $LATEX "\\subsection{Top Files}\n";
        if ($trace_files)
        {
                print $LATEX "The following files were the top $top_count_limit most accessed files by IOPS\n";
                print $LATEX "\\begin{verbatim}\n";
                print $LATEX "$top_files\n";
                print $LATEX "\\end{verbatim}\n";
        }
        else
        {
                print $LATEX "Tracing was done without 'File tracing' enabled.  To enable file tracing, please use the -f flag.  Please note that it may take 3-5 minutes to gather information about file placement on large filesystems.\n";
        }
        print $LATEX "\\subsection{IOPS Histogram}\n";
        print $LATEX "$analysis_histogram_iops\n";
        print $LATEX "\\includegraphics[width=\\textwidth]{histogram_iops_${dev_str}_${num}}\n";
        print $LATEX "\\subsection{IOPS Heatmap}\n";
        print $LATEX "$analysis_heatmap\n";
        print $LATEX "\\includegraphics[width=\\textwidth]{heatmap_${dev_str}_${num}}\n";
        print $LATEX "\\subsection{IOPS Statistics}\n";
        print $LATEX "\\includegraphics[width=\\textwidth]{stats_iops_${dev_str}_${num}}\n";
        print $LATEX "\\subsection{Bandwidth Statistics}\n";
        print $LATEX "$analysis_stats_bw\n";
        #print $LATEX "\\includegraphics[width=\\textwidth]{heatmaps_input}\n";
        #print $LATEX "\\includegraphics[width=\\textwidth]{heatmaps_output}\n";
        #print $LATEX "\\includegraphics[width=\\textwidth]{heatmaps_saswork}\n";
        print $LATEX "\\subsection{Caveat Emptor}\n";
        print $LATEX "This tool is intended to provide the user with additional insight into their own workload.  This tool has the following limitations:\n";
        print $LATEX "\\begin{itemize}\n";
        print $LATEX "\\item In order to limit the trace impact on performance, blktrace is run as a collection of 3 second traces.  Thus, there may be I/O's missed between runs.\n";
        print $LATEX "\\item Larger $bucket_size byte buckets are used to count logical sector hits instead of $sector_size bytes.  This improves post processing times, but produces less granular results.\n";
        print $LATEX "\\item Translating files into logical block ranges may rely on FIBMAP ioctl() calls.\n";
        print $LATEX "\\item Translating file logical block ranges into $bucket_size byte buckets may result in some bucket overlap.  Cross-correlating this with bucket I/O hits may result in some files being identified as being top hits without any file access.  Please keep this in mind when making important migration or caching decisions.\n";
        print $LATEX "\\end{itemize}\n";
        print $LATEX "\\end{document}\n";
        close($LATEX);

        `pdflatex -interaction batchmode report.$dev_str.tex`;
        if($? != 0 ) { die("ERROR: Failed to run report Error: $!"); }

        `rm -f report.$dev_str.tex`;
        `rm -f report.$dev_str.aux`;
        `rm -f report.$dev_str.log`;

        print "Your I/O profiling report is now available: report.$dev_str.pdf\n";

} # create_report

### Print I/O statistics
sub print_stats
{
        my ($STATS_IOPS, $STATS_BW);
        my $total_r_bw = 0;
        my $total_w_bw = 0;
        my $rtot=0;
        my $wtot=0;
        my $tot=0;
        my $num = defined($1) ? $1 : 0;
        my $stats_iops = "";
        my $stats_bw = "";

        if($pdf_report)
        {
                open($STATS_IOPS, ">stats_iops.$dev_str.$num");
                open($STATS_BW, ">stats_bw.$dev_str.$num");
        }

        foreach my $j (sort {$a<=>$b} keys %r_totals)
        {
                $rtot += $r_totals{$j};
                #my $stuff = $r_totals{$j};
                my $r_perc = ($io_total) ? $r_totals{$j} / $io_total * 100 : 0;
                print "r_perc=$r_perc\n" if ($DEBUG);
                if ($r_perc > 0.5)
                {
                        if($pdf_report)
                        {
                printf($STATS_IOPS "\"%dK READ\" %d %d\n", ($j * $sector_size / $KiB),
                        (($io_total) ? $r_totals{$j}/$io_total*100 : 0),
                        (defined($r_totals{$j}) ? $r_totals{$j} : 0));
                printf($STATS_BW "\"%dK READ\" %d %d\n", ($j * $sector_size / $KiB),
                        ($total_blocks) ? ($j*$r_totals{$j}/$total_blocks*100):0, ($j*$KiB * $r_totals{$j}) );
                        }
                        else
                        {
                $stats_iops .= sprintf("\"%dK READ\" %0.2f%% (%d IO's)\n", ($j * $sector_size / $KiB),
                        (($io_total) ? $r_totals{$j}/$io_total*100 : 0),
                        (defined($r_totals{$j}) ? $r_totals{$j} : 0));
                $stats_bw .= sprintf("\"%dK READ\" %0.2f%% (%0.2f GiB)\n", ($j * $sector_size / $KiB),
                        ($total_blocks) ? ($j*$r_totals{$j}/$total_blocks*100):0, (($j*$sector_size) * $r_totals{$j} / $GiB) );

                        }
                }
                # BEN $r_totals{$j}=0;
                $total_r_bw += $j * $sector_size * $r_totals{$j}/ $GiB;
        }
        foreach my $j (sort {$a<=>$b} keys %w_totals)
        {
                $wtot += $w_totals{$j};
                my $w_perc = ($io_total) ? $w_totals{$j} / $io_total * 100 : 0;
                print "w_perc=$w_perc\n" if ($DEBUG);
                if ($w_perc > 0.5)
                {
                        if($pdf_report)
                        {
                printf($STATS_IOPS "\"%dK WRITE\" %d %d\n", ($j * $sector_size / $KiB),
                        (($io_total) ? $w_totals{$j}/$io_total*100 : 0),
                        (defined($w_totals{$j}) ? $w_totals{$j} : 0));
                printf($STATS_BW "\"%dK WRITE\" %d %d\n", ($j * $sector_size / $KiB),
                        ($j*$w_totals{$j}/$total_blocks*100), ($j*$KiB * $w_totals{$j}) );
                        }
                        else
                        {

                $stats_iops .= sprintf("\"%dK WRITE\" %0.2f%% (%d IO's)\n", ($j * $sector_size / $KiB),
                        (($io_total) ? $w_totals{$j}/$io_total*100 : 0),
                        (defined($w_totals{$j}) ? $w_totals{$j} : 0));
                $stats_bw .= sprintf("\"%dK WRITE\" %0.2f%% (%0.2f GiB)\n", ($j * $sector_size / $KiB),
                        ($j*$w_totals{$j}/$total_blocks*100), (($j*$sector_size) * $w_totals{$j} / $GiB) );
                        }

                }
                # BEN $w_totals{$j}=0;
                $total_w_bw += $j * $sector_size * $w_totals{$j}/ $GiB;
        }

        if($pdf_report)
        {
                print $STATS_IOPS "\"\" 0 0\n";
                print $STATS_BW "\"\" 0 0\n";
                close($STATS_IOPS);
                close($STATS_BW);

                push(@files_to_cleanup, "stats_iops.$dev_str.$num");
                push(@files_to_cleanup, "stats_bw.$dev_str.$num");
        }
        else
        {
                print "Stats IOPS:\n";
                print $stats_iops;

                print "Stats BW:\n";
                print $stats_bw;
        }

        $tot = $rtot + $wtot;
        print "rtot=$rtot wtot=$wtot tot=$tot ps iot=$io_total\n" if ($DEBUG);
        my $caching_score=0;
        my $ssd_score=0;

        # Analyze read percentage statistics
        my $read_percent = sprintf("%0.2f", ($io_total) ? $read_total / $io_total * 100 : 0);
        my $write_percent = sprintf("%0.2f", ($io_total) ? $write_total / $io_total * 100 : 0);
        $analysis_stats_iops = "Your workload was approximately $read_percent\\% reads and $write_percent\\% writes.  ";
        if ($read_percent > 95)
        {
                #$analysis_stats_iops .= "Your workload was very read intensive.  This indicates that write-through caching could improve your workload up to 20X.\n";
                $analysis_stats_iops .= "Your workload was very read intensive.\n";
                $caching_score += 20;
                $ssd_score += 100;
        }
        elsif($read_percent > 70)
        {
                $analysis_stats_iops .= "Your workload was moderately read intensive.\n";
                $caching_score += 3;
                $ssd_score += 70;
        }
        elsif($read_percent > 50)
        {
                $analysis_stats_iops .= "Your workload was evenly split between reads and writes.\n";
                $caching_score += 2;
                $ssd_score += 50;
        }
        else
        {
                $analysis_stats_iops .= "Your workload was write intensive.\n";
                $caching_score += 1;
                $ssd_score += 20;
        }

        # Analyze IOPS distribution
        my $sectors_per_4k = 4096 / $sector_size;
        my $read_4k  = (($io_total) ? (defined($r_totals{$sectors_per_4k}) ? $r_totals{$sectors_per_4k}: 0)/$io_total*100 : 0);
        my $read_8k  = (($io_total) ? (defined($r_totals{$sectors_per_4k*2}) ? $r_totals{$sectors_per_4k*2}: 0)/$io_total*100 : 0);
        my $read_16k  = (($io_total) ? (defined($r_totals{$sectors_per_4k*4}) ? $r_totals{$sectors_per_4k*2}: 0)/$io_total*100 : 0);
        my $read_32k  = (($io_total) ? (defined($r_totals{$sectors_per_4k*8}) ? $r_totals{$sectors_per_4k*2}: 0)/$io_total*100 : 0);
        my $read_4k_total = (defined($r_totals{$sectors_per_4k})) ?  $r_totals{$sectors_per_4k} : 0;
        print "4k read: $read_4k 4k_total: $read_4k_total io_total: $io_total sectors_per_4k: $sectors_per_4k \n" if ($VERBOSE);
        for my $bs ( sort {$a<=>$b} keys %r_totals)
        {
                print "bs: $bs count: $r_totals{$bs}\n" if($DEBUG);
        }


        if ($read_4k > 90)
        {
                $analysis_stats_iops .= "You workload was $read_4k\\% 4k reads.\n";
                $caching_score *= 1;
                $ssd_score *= 1;
        }
        elsif(($read_4k + $read_8k ) > 90)
        {
                $analysis_stats_iops .= "You workload was greater than 90\\% 4k+8k reads.\n";
                $caching_score *= 0.7;
                $ssd_score *= 0.7;
        }
        elsif(($read_4k + $read_8k + $read_16k ) > 90)
        {
                $analysis_stats_iops .= "You workload was greater than 90\\% 4k+8k+16k reads.\n";
                $caching_score *= 0.5;
                $ssd_score *= 0.5;
        }
        elsif(($read_4k + $read_8k + $read_16k ) > 50)
        {
                $analysis_stats_iops .= "You workload was greater than 50\\% 4k+8k+16k reads.\n";
                $caching_score *= 0.3;
                $ssd_score *= 0.3;
        }
        else
        {
                #$analysis_stats_iops .= "Your workload consists of primarily larger packet sizes.\n";
                $caching_score *= 0.1;
                $ssd_score *= 0.1;
        }
        #$analysis_stats_iops .= "This workload is likely to see a $caching_score X benefit from caching or $ssd_score X benefit from SSDs\n";


        return;

} # print_stats

### Combine thread-local counts into global counts
sub total_thread_counts
{
        my $num = shift;
        $max_bucket_hits_semaphore->down();
                print "Thread $num has a max_bucket_hits lock\n" if ($DEBUG);
                if ($thread_max_bucket_hits > $max_bucket_hits) { $max_bucket_hits = $thread_max_bucket_hits; }
                print "Thread $num releasing max_bucket_hits lock" if ($DEBUG);
        $max_bucket_hits_semaphore->up();

        $total_blocks_semaphore->down();
                print "Thread $num has total_blocks lock\n" if ($DEBUG);
                $total_blocks += $thread_total_blocks;
                print "Thread $num releasing total_blocks lock" if ($DEBUG);
        $total_blocks_semaphore->up();

        $total_semaphore->down();
                print "Thread $num has total lock\n" if($DEBUG);
                $io_total += defined($thread_io_total) ? $thread_io_total : 0;
                print "Thread $num releasing total lock\n" if ($DEBUG);
        $total_semaphore->up();

        $read_totals_semaphore->down();
                print "Thread $num has read_totals lock\n" if ($DEBUG);
                $read_total += defined($thread_read_total) ? $thread_read_total : 0;
                foreach my $j (keys %thread_r_totals)
                {
                        $r_totals{$j} = defined($r_totals{$j}) ? $thread_r_totals{$j} + $r_totals{$j} : $thread_r_totals{$j};
                }
                print "Thread $num releasing read_totals lock\n" if($DEBUG);
        $read_totals_semaphore->up();

        $write_totals_semaphore->down();
                print "Thread $num has write_totals lock\n" if ($DEBUG);
                $write_total += defined($thread_write_total) ? $thread_write_total : 0;
                foreach my $j (keys %thread_w_totals)
                {
                        $w_totals{$j} = defined($w_totals{$j}) ? $thread_w_totals{$j} + $w_totals{$j} : $thread_w_totals{$j};
                }
                print "Thread $num releasing write_totals lock\n" if ($DEBUG);
        $write_totals_semaphore->up();

        $total_semaphore->down();
                print "Thread $num has bucket_hits_total lock\n" if ($DEBUG);
                $bucket_hits_total += defined($thread_bucket_hits_total) ? $thread_bucket_hits_total : 0;
                print "Thread $num releasing bucket_hits_total lock\n" if ($DEBUG);
        $total_semaphore->up();

        $read_semaphore->down();
                print "Thread $num has read lock\n" if ($DEBUG);
                for my $b( keys %thread_reads)
                {
                        $reads[$b] = defined($reads[$b]) ? $reads[$b] + $thread_reads{$b} : $thread_reads{$b};
                }
                print "Thread $num releasing read lock\n" if ($DEBUG);
        $read_semaphore->up();

        $write_semaphore->down();
                print "Thread $num has write lock\n" if ($DEBUG);
                for my $b(keys %thread_writes)
                {
                        $writes[$b] = defined($writes[$b]) ? $writes[$b] + $thread_writes{$b} : $thread_writes{$b};
                }
                print "Thread $num releasing write lock\n" if ($DEBUG);
        $write_semaphore->up();

        return;


}

### Thread parse routine for blktrace output
sub thread_parse
{
        my $file = shift;
        my $num = shift;
        my $linecount=0;
	my ($a, $b, $c, $d);
	my $re = qr/Q/;
        chomp($file);
        `gunzip $file.gz`;

        print "\nSTART: $file $num\n" if ($DEBUG);
        open($CMD, "<$file");
        while(<$CMD>)
        {
		if($DEBUG)
		{
                	print "\r$file: $linecount";
                	$linecount++;
		}
		if ($_ =~ /(\S+)\s+Q\s+(\S+)\s+(\S+)$/)
		{
			parse_me($1, $2, $3);
		}
        }
        close($CMD);

        total_thread_counts($num);
        print "\nFINISH $file: $linecount lines\n" if ($DEBUG);
        print "Remove $file\n" if ($DEBUG);
        `rm -f $file`;
        return;
} # thread_parse

### Parse blktrace output
sub parse_me
{
        my $rw = shift;
        my $lba = shift;
        my $size = shift;

        print "rw=$rw lba=$lba size=$size\n" if($DEBUG);

        if ($rw eq "R" || $rw eq "RW")
        {
                $thread_total_blocks += $size;
                $thread_io_total++;
                $thread_read_total++;
                $thread_r_totals{$size}++;

                my $bucket_hits = ($size * $sector_size) / $bucket_size;
                if (($size * $sector_size) % $bucket_size != 0) { $bucket_hits++; }

                for(my $i=0; $i<$bucket_hits; $i++)
                {
                        my $bucket = int(($lba * $sector_size)/ $bucket_size) + $i;
                        $thread_reads{$bucket} = defined($thread_reads{$bucket}) ? $thread_reads{$bucket} + 1 : 1;
                        if($thread_reads{$bucket} > $thread_max_bucket_hits) { $thread_max_bucket_hits = $thread_reads{$bucket}; }

                        $thread_bucket_hits_total++;
                }
        }
        if ($rw eq "W" || $rw eq "WS")
        {
                $thread_total_blocks += $size;
                $thread_io_total++;
                $thread_write_total++;
                $thread_w_totals{$size}++;

                my $bucket_hits = ($size * 512) / $bucket_size;
                if (($size * 512) % $bucket_size != 0) { $bucket_hits++; }

                for(my $i=0; $i<$bucket_hits; $i++)
                {
                        my $bucket = int(($lba * $sector_size)/ $bucket_size) + $i;

                        $thread_writes{$bucket} = defined($thread_writes{$bucket}) ? $thread_writes{$bucket} + 1 : 1;
                        if($thread_writes{$bucket} > $thread_max_bucket_hits) { $thread_max_bucket_hits = $thread_writes{$bucket}; }

                        $thread_bucket_hits_total++;
                }
        }
        return;
}

### File trace routine
sub parse_filetrace
{
        my $file = shift;
        my $num = shift;
        my %thread_files_to_lbas;
        `gunzip $file.gz`;
        print "tracefile = $file $num\n" if($DEBUG);
        my $FH;
        open ($FH,"<", $file);
        while (<$FH>)
        {
                print "$file: $_\n" if($DEBUG);;
                if ($_ =~ /(\S+)\s+::\s+(.+)/)
                {
                        my $object = $1;
                        my $ranges = $2;
                        $thread_files_to_lbas{$object} = $ranges;
                        print "$file: obj=$object ranges:$ranges\n" if($DEBUG);
                }
        }
        close($FH);
        print "Thread $num wants file_to_lba lock\n" if ($DEBUG);
        $files_to_lbas_semaphore->down();
        print "Thread $num has file_to_lba lock\n" if ($DEBUG);
        foreach my $object (keys %thread_files_to_lbas)
        {
                my $ranges = $thread_files_to_lbas{$object};
                $files_to_lbas{$object} = $ranges;
        }
        $files_to_lbas_semaphore->up();
        print "Thread $num freed file_to_lba lock\n" if ($DEBUG);

        return;
}

### Cleanup temp files
sub cleanup_files
{
        print "Cleaning up temp files\n" if ($VERBOSE);
        foreach my $file (@files_to_cleanup)
        {
                print "$file\n" if ($DEBUG);
                `rm -f $file`;
        }
        `rm -f filetrace.*.txt`;
}

### Choose color for heatmap block
sub choose_color
{
        my $num = shift;
        if(!defined($num)|| $num == -1 || $num == 0)
        {
                $color_index=" ";
                return $black;
        }
        $num = int($num);
        $color_index = int($num / $vpc );

        if($color_index > ($choices-1))
        {
                print "num=$num\n" if($DEBUG);
                print "HIT!\n" if ($DEBUG);
                $color_index=7;
                return $red;
        }
        #print "num=$num ";
        my $color =$colors[$color_index];
        print "cap=$cap num=$num color_index=$color_index\n" if($DEBUG);
        if(!defined($color))
        {
                print "ch=$choices num=$num ci=$color_index vpc=$vpc cap=$cap\n";
                return $black;
        }
        return $color;

}

### Clear screen for heatmap (UNUSED)
sub clear_screen
{
        print "\033[2J";
        print "\[\033[0;0f\]\r";
}

### Get block value by combining buckets into larger heatmap blocks for term
sub get_value
{
        my $offset = int(shift);
        my $rate = int(shift);
        my $start = $offset * $rate;
        my $end = $start+$rate;
        my $sum = 0;
        print "s=$start e=$end\n" if($DEBUG);
        for($start..$end)
        {
		my $index = $_;
		if(defined($reads[$index]) || defined($writes[$index]))
		{
			my $r = defined($reads[$index]) ? $reads[$index] : 0;
			my $w = defined($writes[$index]) ? $writes[$index] : 0;
                	$sum = $sum + $r + $w;
		}
                #my $i=$map[$_];
        }
	print "s=$sum " if($DEBUG);
        #my $value = ($sum) ? $sum / $rate : -1;
        return int($sum);
}

### Draw heatmap on color terminal
sub draw_heatmap
{
        print "max_bucket_hits=$max_bucket_hits\n" if($DEBUG);
        print_map() if ($DEBUG);

        #my $pigeons = scalar(@map);
        my $pigeons = $num_buckets;
        my $term_x = `tput cols` -$SCALEX;
        my $term_y = `tput lines` -$SCALEY;
        if($term_x < $min_x)
        {
                print "Make the terminal wider please\n";
                return;
        }
        elsif($term_y < $min_y)
        {
                print "Make the terminal taller please\n";
                return;
        }

        my $holes = int($term_x * $term_y);
        $rate = int($pigeons / $holes);
        #$cap = int($choices * $vpc * $rate);

        my $i=0;
        my $square_size = ($rate) ? (($rate * $bucket_size) / $MiB ): ($bucket_size / $MiB);
        #clear_screen();
        #print "Heatmap: x:$term_x,y:$term_y       \n";
        printf "This heatmap can help you 'see' hot spots.  It is adjusted to terminal size, so each square = %0.2f MiB\n", $square_size;
        print "The PDF report may be more precise with each pixel=1MB\n";
        print "Heatmap Key: Black (No I/O), white(Coldest),blue(Cold),cyan(Warm),green(Warmer),yellow(Very Warm),magenta(Hot),red(Hottest)\n";
        $cap=0;

        for(my $y=0; $y<$term_y; $y++)
        {
                #print "|";
                for(my $x=0; $x<$term_x; $x++)
                {
                        my $index = $x + ($y * $term_x);
                        my $value=0;
                        print "y=$y, x=$x, i=$index\n" if ($DEBUG);
                        if($rate > 1)
                        {
                                $value = get_value($index, $rate);
                        }
                        else
                        {
                                #if(defined($map[$index]))
                                if(defined($reads[$index]) || defined($writes[$index]))
                                {
					my $r = defined($reads[$index]) ? $reads[$index] : 0;
					my $w = defined($writes[$index]) ? $writes[$index] : 0;
                                        $value = $r + $w;
                                }
                                else
                                {
                                        $value=-1;
                                }
                        }
                        $cap = ($value > $cap) ? $value : $cap;
                        $block_map[$index]=$value;

			print "v=$value " if ($DEBUG);
			if ($x % 20 == 0) { print "\n" if($DEBUG); }
                        #my $color = choose_color($value);
                        #print "${color}$color_index";
                        #print "v=$value $color_index";
                }
                #print "${none}|\n";

        }

        print "cap=$cap vpc=$vpc pigeons=$pigeons holes=$holes rate=$rate max_bucket_hits=$max_bucket_hits\n" if($VERBOSE);
        $vpc = int($cap / $choices) ? int($cap / $choices) : 1; # values per choice

        print "+" . "-" x $term_x . "-+\n";
        for(my $y=0; $y<$term_y; $y++)
        {
                print "|";
                for(my $x=0; $x<$term_x; $x++)
                {
                        my $index = $x + ($y * $term_x);
                        my $value = $block_map[$index];
                        my $color = choose_color($value);
                        print "${color}$color_index";
                }
                print "${none}|\n";
        }
        print "${none}+" . "-" x $term_x . "-+\n";
}

sub worker
{
	my ($work_q) = @_;
	# This thread's ID
	my $tid = threads->tid();
	#print "tid $tid started\n" if ($VERBOSE);

	do
	{
        	# Indicate that were are ready to do work
        	#printf("Idle     -> %2d\n", $tid);
        	#$IDLE_QUEUE->enqueue($tid);
	
        	# Wait for work from the queue
		my $tasks;
		#$tasks = $work_q->pending();
		#print "t=$tasks\n";
        	my $file = $work_q->dequeue_nb();
		#$tasks = $work_q->pending();
		#print "t=$tasks\n";
	
        	# If no more work, exit
        	if (!defined($file ))
		{
        		$term_semaphore->down();
			$TERM=1;
        		$term_semaphore->up();
			print "Finished with work queue\n" if($DEBUG);
			return;
		}
	#
        	# Do some work while monitoring $TERM
		print "started file $file, left=$tasks\n" if ($DEBUG);
        	#printf("Working  -> %2d\n", $tid);
                if ($file =~ /(blk.out.\S+).gz/)
                {
                        my $new_file = $1;
                        thread_parse($new_file, $tid);
                }
                elsif ($file =~ /(filetrace.\S+.\S+.txt).gz/)
                {
                        my $new_file = $1;
			$trace_files_semaphore->down();
                        	$trace_files = 1;
			$trace_files_semaphore->up();
                        print "\nFound some filetrace files $trace_files\n" if ($DEBUG);
                        parse_filetrace($new_file, $tid);
                }
	} while (!$TERM);
	print "tid: $tid finished\n" if ($DEBUG);
	return;

}



############
### MAIN ###
############

### Check command line arguments
check_args();

### Check if debugfs is mounted
if ($mode eq "live" || $mode eq "trace")
{
        mount_debugfs();
}


### Get block count and logical block size
if($mode eq 'trace')
{

        my $thread_count=0;
        my $pid=-1;
        #my $cpu_affinity=0;

        ### Check if sudo permissions
        `sudo -v`;
        if($? != 0 ) { die("ERROR: You need to have sudo permissions to collect all necessary data.  Please run from a privilaged account."); }

        ### Save fdisk info
        print "Running fdisk\n" if ($DEBUG);
        my $fdisk_version = `fdisk -v`;
        if($fdisk_version =~ /util-linux-ng/)
        {
                `fdisk -ul $dev > fdisk.$dev_str`;
        }
        else
        {
                `fdisk -l -u=sectors $dev > fdisk.$dev_str`;
        }

        ### Cleanup previous mess
        `rm -f blk.out*`;

        my $cpu_count = `cat /proc/cpuinfo | grep processor | wc -l`;
        my $runcount=$runtime/$timeout;
        print "\n";
        while ($runcount > 0)
        {
                my $percent = $thread_count * $timeout * 100 / $runtime;
                my $time_left = $runcount * $timeout;
                print "\r$percent % done ($time_left seconds left)    ";
                if ($cpu_affinity >= $cpu_count) { $cpu_affinity=0; }
                if ($cpu_affinity == 0) { $cpu_affinity++; }

                `taskset -c $cpu_affinity blktrace -b $buffer_size -n $buffer_count -a queue -d  $dev -o blk.out.$dev_str.$thread_count -w $timeout`;
                if($? != 0)
                {
                        print "$0 was not able to run the 'blktrace' tool required to trace all of your I/O\n\n";
                        print "If you are using SLES 11 SP1, then it is likely that your default kernel is missing CONFIG_BLK_DEV_IO_TRACE\n";
                        print "which is required to run blktrace.  This is only available in the kernel-trace version of the kernel.\n";
                        print "kernel-trace is available on the SLES11 SP1 DVD and you simply need to install this and boot to this\n";
                        print "kernel version in order to get this working.\n\n";
                        print "If you are using a differnt distro or custom kernel, you may need to rebuild your kernel with the 'CONFIG_BLK 1f40 _DEV_IO_TRACE'\n";
                        print "option enabled.  This should allow blktrace to function\n";
                        die("ERROR: Could not run blktrace");
                }

                $pid = fork();
                if($pid < 0)
                {
                        # Failed to fork
                        print "Failed to fork process... Exiting";
                        exit(-1);
                }
                elsif ($pid ==0)
                {
                        #child process
                        `nice -n 19 taskset -c $cpu_affinity blkparse -i blk.out.$dev_str.$thread_count -q -f \"%d %a %S %n\n\" | nice -n 19 taskset -c $cpu_affinity grep -v cfq| nice -n 19 taskset -c $cpu_affinity gzip --fast > blk.out.$dev_str.$thread_count.blkparse.gz; nice -n 19 taskset -c $cpu_affinity rm -f blk.out.$dev_str.$thread_count.blktrace.*; `;
                        exit(1);
                }
                else
                {
                        print "PID=$pid CPU=$cpu_affinity\n" if ($DEBUG);
                        push(@pidlist, $pid);
                }

                $thread_count++;
                $cpu_affinity++;
                $runcount--;
        }
        print "\rWaiting on threads to finish                ";
        foreach $pid (@pidlist)
        {
                do
                {
                        print("\rWaiting on $pid                   ");
                } while (!waitpid($pid, 0));
        }
        undef(@pidlist);
        print "\rMapping files to block locations           ";
        find_all_files() if($trace_files);
        my $tarball_name = "$dev_str.tar";
        print "\rCreating tarball: $tarball_name            ";
        my $filetrace = "";
        if ($trace_files) { $filetrace = "filetrace.$dev_str.*.txt.gz"; }
        `tar -cf $tarball_name blk.out.$dev_str.*.gz fdisk.$dev_str $filetrace`;
        if ($? != 0) { die ("ERROR: failed to tarball $tarball_name"); }
        print "\rCleaning up leftover files                         ";
        `rm -f blk.out.$dev_str.*.gz`;
        `rm -f fdisk.$dev_str`;
        `rm -f filetrace.$dev_str.*.gz`;
        print "\rFINISHED tracing: $tarball_name         \n";
        print "Please use this file with $0 -m post -t $tarball_name to create a report\n";
        exit();
}

# Initialize Thread Semaphores
$read_semaphore = Thread::Semaphore->new();
$write_semaphore = Thread::Semaphore->new();
$read_totals_semaphore = Thread::Semaphore->new();
$write_totals_semaphore = Thread::Semaphore->new();
$total_semaphore = Thread::Semaphore->new();
$total_blocks_semaphore = Thread::Semaphore->new();
$files_to_lbas_semaphore = Thread::Semaphore->new();
$max_bucket_hits_semaphore = Thread::Semaphore->new();
$bucket_to_files_semaphore = Thread::Semaphore->new();
$term_semaphore = Thread::Semaphore->new();
$trace_files_semaphore = Thread::Semaphore->new();

if ($mode eq "post")
{
        $read_total=0;
        $write_total=0;
        $max_bucket_hits=$io_total=0;
        $bucket_hits_total=0;
        $total_blocks=0;
        $thread_total_blocks=0;
        $thread_max_bucket_hits=0;
        #my $cpu_affinity=1;
        my $pid=-1;
        my $cpu_count = `cat /proc/cpuinfo | grep processor | wc -l`;
        $thread_max = $cpu_count;
        my $file_count=0;
        my @threads;

        my @file_list = `tar -tf $tar_file`;

        print "Unpacking $tar_file.  This may take a minute.\n";
        `tar -xvf $tar_file`;
        if($?)
        {
                die("ERROR: Failed to unpack input file: $tar_file");
        }
        $sector_size=`cat $fdisk_file | grep 'Units'| awk '{ print \$9 }'`;
	my $lba_line = `cat $fdisk_file | grep "sectors\$"`;
	print "$lba_line\n" if ($DEBUG);
	if ($lba_line =~ /(\d+) sectors$/) { $total_lbas=$1; }
        $dev = `cat $fdisk_file | grep Disk | awk '{ print \$2 }'| head -1 | tr ':' ' '`;
        chomp($dev);
        chomp($total_lbas);
        chomp($sector_size);
	print "dev=$dev lbas=$total_lbas sec_size=$sector_size\n" if ($VERBOSE);
        $total_capacity_GiB = $total_lbas * $sector_size / $GiB;
        #print "lbas: $total_lbas sec_size: $sector_size total: $total_capacity_GiB GB\n";
        printf("lbas: %d sec_size: %d total: %0.2f GiB\n", $total_lbas, $sector_size, $total_capacity_GiB);

        $num_buckets = $total_lbas * $sector_size / $bucket_size;

        # Make the plot a matrix to keep gnuplot happy
        $yheight=$xwidth = int(sqrt($num_buckets));
        print "x=$xwidth y=$yheight\n" if ($DEBUG);

        print "num_buckets=$num_buckets sector_size=$sector_size total_lbas=$total_lbas bucket_size=$bucket_size\n" if ($VERBOSE);

        `rm -f filetrace.$dev_str.*.txt`;
        `rm -f blk.out.$dev_str.*.blkparse`;
        print "Time to parse.  Please wait...\n";
        my $size = scalar(@file_list);

my $q;
if($THREAD_POOL && !$SINGLE_THREADED)
{
	my %work_queues;
	$q = Thread::Queue->new();


        #foreach my $file (@file_list)
        ##{
                #$file_count++;
                #chomp($file);
                #printf "\rInput Percent: %d %% (File %d of %d)", ($file_count*100 / $size), $file_count, $size;
                # Wait for an available thread

                # Check for termination condition
                #last if ($tid < 0);

                # Give the thread some work to do
		#$q->enqueue($file);

                #$work_queues{$tid}->enqueue($file) or die("enqueue failed: $!");
        #}
	$q->enqueue(@file_list);

        for(my $i=0; $i<$cpu_count; $i++)
        {
                #my $wq = Thread::Queue->new();
                my $t = threads->create('worker', $q);
                push(@threads, $t);

                #$work_queues{$t->tid()} = $wq;
        }





if(0)
{
	for(my $i=0; $i<$cpu_count; $i++)
	{
		my $wq = Thread::Queue->new();
		my $t = threads->create('worker', $wq);
		push(@threads, $t);

		$work_queues{$t->tid()} = $wq;
	}

	foreach my $file (@file_list)
	{
		$file_count++;
		chomp($file);
		printf "\rInput Percent: %d %% (File %d of %d)\n", ($file_count*100 / $size), $file_count, $size;
                # Wait for an available thread
                my $tid = $IDLE_QUEUE->dequeue();
		if ($tid < 0 ) { die ("tid $tid: $!"); }

                # Check for termination condition
                #last if ($tid < 0);

                # Give the thread some work to do
		my $tasks = $work_queues{$tid}->pending();
		print "tid: $tid, file: $file tasks: $tasks\n" if($VERBOSE);
		
                #$work_queues{$tid}->enqueue($file) or die("enqueue failed: $!");
		sleep(3);
	}

        # Signal all threads that there is no more work
        #$work_queues{$_}->enqueue(-1) foreach keys(%work_queues);
	$work_queues{$_}->end() foreach keys(%work_queues);
}

}
else
{

        foreach my $file (@file_list)
        {
		printf "\rInput Percent: %d %% (File %d of %d)", ($file_count*100 / $size), $file_count, $size;
                #print "\r$file_count of $size\n";
                if ($file =~ /(blk.out.\S+).gz/)
                {
                        my $new_file = $1;
                        $file_count++;

			if($SINGLE_THREADED)
			{
                                thread_parse($new_file, $file_count);
			}
			else
			{
                        	my $t=threads->new(\&thread_parse, $new_file, $file_count);
                        	push(@threads, $t);
			}
                        #thread_parse($new_file, $file_count);
                }
                elsif ($file =~ /(filetrace.\S+.\S+.txt).gz/)
                {
                        my $new_file = $1;
                        $file_count++;
                        #`gunzip $file`;
                        $trace_files = 1;
                        print "\nFound some filetrace files\n" if ($DEBUG);
			if($SINGLE_THREADED)
			{
                        	parse_filetrace($new_file, $file_count);
			}
			else
			{
                        	my $t=threads->new(\&parse_filetrace, $new_file, $file_count);
                        	push(@threads, $t);
			}
                }
		if(!$SINGLE_THREADED)
		{
                	if(scalar @threads > $thread_max)
                	{
                        	printf "\rInput Percent: %d %% (File %d of %d)", ($file_count*100 / $size), $file_count, $size;
                        	foreach my $x (0 .. $#threads)
                        	{
                                	if(defined($threads[$x]))
                                	{
                                        	if($threads[$x]->is_joinable())
                                        	{
                                                	my $name = $threads[$x]->join();
                                                	delete ($threads[$x]);
                                        	}
                                	}
                        	}
                	}
		}
        }
}

	
	if($SINGLE_THREADED)
	{
		total_thread_counts(0);
	}
	else
	{
        	while(scalar(@threads) && !$SINGLE_THREADED)
        	{
			
			if($THREAD_POOL)
			{
				my $tasks = $q->pending();
				printf "\rInput Percent: %d %% (Thread Count: %d)", (($size-$tasks)*100/$size),  scalar(@threads);
				sleep(1);
			}
			else
			{
                		printf "\rInput Percent: %d %% (Thread Count: %d)", ($file_count*100 / $size), scalar(@threads);
			}
                	foreach my $x (0 .. $#threads)
                	{
                        	if(defined($threads[$x]))
                        	{
                                	if($threads[$x]->is_joinable())
                                	{
                                        	my $name = $threads[$x]->join();
                                        	delete ($threads[$x]);
                                	}
                        	}
                	}
        	}
        	print "\rFinished parsing files.  Now to analyze\n";
        	undef(@threads);
	}

        file_to_buckets();

        print_results();
        print_stats();
        draw_heatmap();
        if($pdf_report)
        {
                print_header_heatmap();
                print_header_histogram_iops();
                print_header_stats_iops();
                create_report();
        }
        cleanup_files();

        exit;

}

if ($mode eq 'live')
{
	$timeout=1; 
        my $fdisk_version = `fdisk -v`;
        if($fdisk_version =~ /util-linux-ng/)
        {
                $sector_size = `fdisk -ul $dev 2>/dev/null| grep 'Units' | awk '{ print \$9 }'`;
                $total_lbas  = `fdisk -ul $dev | grep total | awk '{ print \$8 }'`;
        }
        else
        {
                $sector_size = `fdisk -l -u=sectors $dev 2>/dev/null| grep 'Units' | awk '{ print \$9 }'`;
		my $lba_line = `fdisk -l -u=sectors $dev 2>/dev/null| grep "sectors\$"`;
		if ($lba_line =~ /(\d+) sectors$/) { $total_lbas=$1; }
		print "$lba_line\n" if ($DEBUG);
        }
 
        my $term_x = `tput cols` -$SCALEX;
        my $term_y = `tput lines` -$SCALEY;


        chomp($total_lbas);
        chomp($sector_size);
        $total_capacity_GiB = $total_lbas * $sector_size / $GiB;
        print "lbas: $total_lbas sec_size: $sector_size total: $total_capacity_GiB GB\n";

        #$num_buckets = int($total_lbas * $sector_size / $bucket_size);
        $num_buckets = `tput cols` * `tput lines`;
        $bucket_size = $total_lbas * $sector_size / $num_buckets;

        # Make the plot a matrix to keep gnuplot happy
        $yheight=$xwidth = int(sqrt($num_buckets));
        print "x=$xwidth y=$yheight\n" if ($DEBUG);

        print "num_buckets=$num_buckets sector_size=$sector_size total_lbas=$total_lbas bucket_size=$bucket_size\n" if ($VERBOSE);

        while(1)
        {
                $max_bucket_hits=$total_blocks=$read_total=$write_total=$io_total=$bucket_hits_total=0;
                $thread_max_bucket_hits=$thread_io_total=$thread_bucket_hits_total=$thread_read_total=$thread_write_total=$thread_total_blocks=0;

                $live_iterations++;
                if (($runtime!= 0) && (($live_iterations*$timeout) > $runtime))
                {
                        print "Exceeded $runtime runtime.  Exiting.\n" if ($VERBOSE);
                        exit();
                }

                open ($CMD, "blktrace -b $buffer_size -n $buffer_count -a queue -w $timeout -d $dev -o -  | blkparse -q -i - -f \"%d %a %S %n\n\" | grep -v cfq |");

                while (<$CMD>)
                {
                        if ($_ =~ /(\S+)\s+Q\s+(\S+)\s+(\S+)$/)
                        {
                                parse_me($1, $2, $3);
                        }
                }
                close($CMD);
                total_thread_counts(0);

                print_results();
                print_stats();
                draw_heatmap();

                undef(%thread_r_totals);
                undef(%thread_w_totals);
                undef(%thread_reads);
                undef(%thread_writes);
                undef($thread_max_bucket_hits);
                #undef(@map);
		undef(@reads);
		undef(@writes);
		undef(%r_totals);
		undef(%w_totals);
        }
}
