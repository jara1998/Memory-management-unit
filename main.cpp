#include <iostream>
#include <fstream>
#include <string>
#include <stdlib.h>
#include <vector>
#include <list>
#include <queue>
#include <iterator> 
#include <getopt.h>
#include <string.h>
#include <stdio.h>
#include <limits>

using namespace std;

const int PT_LEN = 64;
int MAX_FRAMES;
bool opt_O;
bool opt_P;
bool opt_F;
bool opt_S;
unsigned long long ctx_switches = 0;
unsigned long long process_exits = 0;
unsigned long long total_cost = 0;
unsigned long long inst_count = 0;

vector<int> rand_arr;
int random_counter = 0;
int myrandom() {
    return (random_counter == rand_arr.size()) ? ((rand_arr[(random_counter = 0)++] % MAX_FRAMES)): (rand_arr[random_counter++] % MAX_FRAMES); 
}

class VMA {
    public:
        int vp_start;
        int vp_end;
        int w_protected;
        int file_mapped;

        VMA (int vp_start, int vp_end, int w_protected, int file_mapped) {
            this->vp_start = vp_start;
            this->vp_end = vp_end;
            this->w_protected = w_protected;
            this->file_mapped = file_mapped;
        }
};

class PTE {
    public:
        unsigned present:1;
        unsigned write_protected:1;
        unsigned modified:1;
        unsigned ref:1;
        unsigned pout:1;
        unsigned fmapped:1;
        unsigned physical_frame:7; // supports up to 128 frames
        unsigned vpage_id:6; // 64 vitural pages
        unsigned vma_valid:1;
        unsigned vaddr:12; // 4096 vmas

        PTE() {
            this->reset();
        }

        void reset() {
            present = 0;
            write_protected  = 0;
            ref = 0;
            modified = 0;
            pout = 0;
            physical_frame = 0;
            fmapped = 0;
            vpage_id = 0;
            vma_valid = 0;
            vaddr = 0;
        }

        void set(int f_id, unsigned f_mapped, unsigned w_prot) {
            this->present = 1;
            this->physical_frame = f_id;
            this->ref = 0;
            this->modified = 0;
            this->fmapped = f_mapped;
            this->write_protected = w_prot;
        }
};


class Process {
    public:
        int pid;
        vector<VMA> vma_table;
        PTE* pageTable = new PTE[PT_LEN];
        vector<int> pte_2_vma;

        unsigned long maps = 0;
        unsigned long unmaps = 0;
        unsigned long ins = 0;
        unsigned long outs = 0;
        unsigned long fins = 0;
        unsigned long fouts = 0;
        unsigned long zeros = 0;
        unsigned long segv = 0;
        unsigned long segprot = 0;

        Process(int pid) {
            this->pid = pid;
            for(int i = 0; i < PT_LEN; i++) {
                pageTable[i].vpage_id = i;
                pte_2_vma.push_back(-1);
            }

        }

        void set_bit_map(int start, int end, int i) {
            std::fill(pte_2_vma.begin() + start, pte_2_vma.begin() + end + 1, i);
        }

        void print_proc() {
            printf("PROC[%d]: U=%lu M=%lu I=%lu O=%lu FI=%lu FO=%lu Z=%lu SV=%lu SP=%lu\n", 
                        pid, unmaps, maps, ins, outs, fins, fouts, zeros, segv, segprot);
        }
};

vector<Process> proc_arr;

class Frame {
    public:
        // reverse mapping
        int proc_id;
        PTE *vpage;
        int frame_id;
        int TAU;
    
    public:
        Frame() {
            this->reset();
        }

        void reset() {
            this->proc_id = -1;
            this->vpage = NULL;
            TAU = 0;
        }
};

Frame* frame_table;

class Pager {
    public:
        virtual Frame* select_victim_frame() = 0;
};


class FIFO: public Pager {
    int hand = 0;
    public:
        Frame* select_victim_frame() {
            Frame *res = &frame_table[hand++];
            hand %= MAX_FRAMES;
            return res;
        }
};


class Random: public Pager {
    public:
        Frame* select_victim_frame() {
            return &frame_table[myrandom()];
        }
};

class Clock: public Pager {
    int hand = 0;
    public:
        Frame* select_victim_frame() {
            bool found = false;
            Frame* res;
            while(!found) {
                if(frame_table[hand].vpage->ref) {
                    // reset ref if current ref is 1
                    frame_table[hand++].vpage->ref = 0;
                    hand %= MAX_FRAMES;
                } else {
                    found = true;
                    res = &frame_table[hand++];
                    hand %= MAX_FRAMES;
                }  
            }
            return res;
        }
};


class NRU: public Pager {
    int hand = 0;
    int last_inst_count = 0;
    Frame** class_level; 
    public:
        int calculate_class() {
            int res = 0;
            if (frame_table[hand].vpage->ref) res += 2;
            if (frame_table[hand].vpage->modified) res++;
            return res;    
        }
        
        Frame* select_victim_frame() {
            bool reset_ref = false;
            class_level = new Frame*[4]();

            if(inst_count - last_inst_count >= 50) {
                reset_ref = true;
                last_inst_count = inst_count;
            }

            int counter = 0;
            int lowest_level = 5;
            // check through all frames
            while (counter++ < MAX_FRAMES) {
                int frame_class = calculate_class();
                lowest_level = std::min(lowest_level, frame_class);
                // clear ref bit after considered the class of that frame/page
                if(reset_ref) {
                    frame_table[hand].vpage->ref = 0;
                }

                if(!class_level[frame_class]) {
                    class_level[frame_class] = &frame_table[hand];
                }
                if (lowest_level == 0 && !reset_ref) break;
        
                hand++;
                hand %= MAX_FRAMES;
            }
            if (lowest_level == 5) {
                return NULL;
            }

            hand = (class_level[lowest_level]->frame_id + 1) % MAX_FRAMES;
            return class_level[lowest_level];
            
        }
};

vector<uint32_t> age_table;
class Aging: public Pager {
    int hand = 0;
    public:
        Frame* select_victim_frame() {
            Frame *res = NULL;
            int counter = 0;
            int curr_age = std::numeric_limits<int>::max();
            while (counter++ < MAX_FRAMES) {
                age_table[hand] = age_table[hand] >> 1;
                if(frame_table[hand].vpage->ref) {
                    age_table[hand] |= 0x80000000;
                    frame_table[hand].vpage->ref = 0;
                }

                if(!res || age_table[hand] < curr_age) {
                    res = &frame_table[hand];
                    curr_age = age_table[hand];
                }
                hand++;
                hand %= MAX_FRAMES;
            }

            hand = (res->frame_id + 1) % MAX_FRAMES; // move hand to the next position of the selected frame
            return res;
        }
};


class Working_Set: public Pager {
    int hand = 0;
    public:
        Frame* select_victim_frame() {
            Frame *res = NULL;
            int target_age = 0;
            bool found = false;
            int counter = 0;
            bool valid_res = false;
            while (counter < MAX_FRAMES && !found) {
                Frame *curr = &frame_table[hand];

                int time = inst_count - curr->TAU;
                if (inst_count - curr->TAU >= 50 && !curr->vpage->ref) {
                    res = curr;
                    found = true; 
                } else if (curr->vpage->ref) {
                    curr->TAU = inst_count;
                    curr->vpage->ref = 0;
                } 

                if (inst_count - curr->TAU > target_age) {
                    res = curr;
                    target_age = inst_count - curr->TAU;
                    valid_res = true;
                }
                hand++;
                hand %= MAX_FRAMES;
                counter++;
            }
        
            if(!found && !valid_res) res = &frame_table[hand];

            hand = (res->frame_id + 1) % MAX_FRAMES;
            return res;
        }
};


deque<Frame *> free_pool;

Frame* allocate_frame_from_free_list() {
    if (free_pool.empty()) {
        return NULL;
    }
    Frame* result = free_pool.front();
    free_pool.pop_front();
    return result;
}

// Returns the frame to be used to handle page fault
Frame* get_frame(Pager *pager) {
    Frame *frame = allocate_frame_from_free_list();
    if (frame == NULL) frame = pager->select_victim_frame();
    return frame; 
} 

PTE* pgfault_handler(Pager *pager, Process *curr_proc, int opt_arg, PTE* pte) {

    // vpage can be accessed or not
    VMA* vma = curr_proc->pageTable[opt_arg].vma_valid ? &curr_proc->vma_table[curr_proc->pageTable[opt_arg].vaddr] : NULL;
    if (!vma){
        if (curr_proc->pte_2_vma[opt_arg] == -1) {
            total_cost += 340;
            curr_proc->segv++;
            if(opt_O) printf(" SEGV\n"); 
            return pte;
        } else {
            curr_proc->pageTable[opt_arg].vma_valid = 1;
            curr_proc->pageTable[opt_arg].vaddr = curr_proc->pte_2_vma[opt_arg];
            vma = &curr_proc->vma_table[curr_proc->pte_2_vma[opt_arg]];
        }
    }

    // If it is part of a VMA then the page must be instantiated, i.e. a frame must be allocated,
    // assigned to the PTE belonging to the vpage of this instruction (i.e. currentproc->pagetable[vpage].frame = allocated_frame ) and
    // then populated with the proper content. 
    Frame *newframe = get_frame(pager);
    if(newframe->vpage) {
        if(opt_O) printf(" UNMAP %d:%d\n", newframe->proc_id, newframe->vpage->vpage_id);
        proc_arr[newframe->proc_id].unmaps++;
        total_cost += 400;
        newframe->vpage->present = 0;

        if (!newframe->vpage->fmapped && newframe->vpage->modified) {
            if(opt_O) printf(" OUT\n");
            proc_arr[newframe->proc_id].outs++;
            total_cost += 2700;
            newframe->vpage->pout = 1;
        }
        
        if(newframe->vpage->modified && newframe->vpage->fmapped) {
            if(opt_O) printf(" FOUT\n");
            total_cost += 2400;
            proc_arr[newframe->proc_id].fouts++;
        }
    }

    pte->set(newframe->frame_id, vma->file_mapped, vma->w_protected);
    age_table[newframe->frame_id] = 0;
    newframe->TAU = inst_count; // creation time
    newframe->proc_id = curr_proc->pid;
    newframe->vpage = pte;

    if(pte->pout) {
        if(opt_O) printf(" IN\n");
        total_cost += 3100;
        curr_proc->ins++;
    }

    if(pte->fmapped) {
        if(opt_O) printf(" FIN\n");
        curr_proc->fins++;
        total_cost += 2800;
    } 
    if (!pte->fmapped && !pte->pout) {
        if(opt_O) printf(" ZERO\n");
        curr_proc->zeros++;
        total_cost += 140;
    }
    curr_proc->maps++;
    if(opt_O) printf(" MAP %d\n", newframe->frame_id);
    total_cost += 300;

    return pte;
}

string next_valid_line(ifstream& inputFile) {
    string line_str;
    getline(inputFile, line_str);
    while ((line_str[0] == '#' || line_str.empty()) && inputFile.peek() != EOF) getline(inputFile, line_str);
    return line_str;
}

void simulate(Pager *pager, ifstream& inputFile) {
    Process *curr_proc;
    PTE* pte;
    while(inputFile.peek() != EOF) {  
        // process next instruction
        string line_str = next_valid_line(inputFile);
        if (line_str.empty() || line_str[0] == '#') break;
        char operation;
        int opt_arg;
        sscanf(line_str.c_str(), "%c%d", &operation, &opt_arg);

        if(opt_O){
            printf("%lu: ==> %c %d\n", inst_count, operation, opt_arg);
        }
        inst_count++;
        
        switch (operation) {

            case 'r':
                total_cost++;
                pte = &curr_proc->pageTable[opt_arg];
                if(!pte->present) {
                    pte = pgfault_handler(pager, curr_proc, opt_arg, pte);
                }
                pte->ref = 1;

            break;

            case 'w':
                total_cost++;
                pte = &curr_proc->pageTable[opt_arg];
                if(!pte->present) {
                    pte = pgfault_handler(pager, curr_proc, opt_arg, pte);
                }
                pte->ref = 1;
                if(pte->write_protected) {
                    total_cost += 420;
                    curr_proc->segprot++;
                    if(opt_O) printf(" SEGPROT\n");
                } else {   
                    pte->modified = 1;
                } 

            break;
            
            case 'c':
                ctx_switches++;
                total_cost += 130;
                curr_proc = &(proc_arr[opt_arg]);
            break;
            
            case 'e':
                process_exits++;  
                total_cost += 1250;
                PTE *pte;
                std::cout << "EXIT current process " << curr_proc->pid << endl;
                for(int i = 0; i < PT_LEN; i++) {  
                    pte = &curr_proc->pageTable[i]; 
                    if(pte->present) {
                        // unmap current frame
                        Frame* curr_frame = &(frame_table[pte->physical_frame]);
                        curr_proc->unmaps++;
                        if(opt_O) printf(" UNMAP %lu:%lu\n", curr_proc->pid, pte->vpage_id);

                        total_cost += 400;

                        curr_frame->reset();
                        free_pool.push_back(curr_frame);

                    
                        // write back to the file
                        if(pte->modified && pte->fmapped) {
                            total_cost += 2400;
                            curr_proc->fouts++;
                            std::cout << " FOUT" << endl;
                        }
                    }
                    pte->reset();
                }
                curr_proc = NULL;  
            break;
        }
    }
}



int main(int argc, char *argv[]) {

    Pager* pager;
    const char *optstring = "f:a:o:";
    int opt;
    while((opt = getopt(argc, argv, optstring)) != -1) {
        switch(opt) {   
            case 'f': 
                MAX_FRAMES = std::stoi(optarg);
                break;

            case 'o': 
                if(optarg != NULL) {
                for(int i=0; i < sizeof(optarg); i++) {
                    switch(optarg[i])
                        {
                            case 'O':   
                            opt_O = true;
                            break;

                            case 'P':   
                            opt_P = true;
                            break;

                            case 'F':   
                            opt_F = true;
                            break;

                            case 'S':   
                            opt_S = true;
                            break;
                        }
                    }
                }
                break;
            
            case 'a':   
                if(optarg!=NULL) {
                    switch(optarg[0]) {
                        case 'f':   
                        pager = new FIFO();
                        break;

                        case 'r':   
                        pager = new Random();
                        break;
                        
                        case 'c':   
                        pager = new Clock();
                        break;

                        case 'e':   
                        pager = new NRU();
                        break;

                        case 'a':   
                        pager = new Aging();
                        break;

                        case 'w':  
                        pager = new Working_Set();
                        break;

                        }
                } 
                break;
        }
    }


    // read input files
    const char *input_file_name = argv[optind];
    const char *rand_file_name = argv[optind+1];

    // create random table
    ifstream randFile;
    randFile.open(rand_file_name);
    string r_int;
    // process first token
    randFile >> r_int;
    while(randFile >> r_int) {
        rand_arr.push_back(stoi(r_int));
    }

    //  initialize frames and freeList
    frame_table = new Frame[MAX_FRAMES];
    for(int i = 0; i < MAX_FRAMES; i++) {
        frame_table[i].frame_id = i;
        free_pool.push_back(&frame_table[i]);
    }

    // read processes
    ifstream inputFile;
    inputFile.open(input_file_name);
    string line_str;
    int i = 0;
    // get the number of processes
    int total_proc;
    total_proc = std::stoi(next_valid_line(inputFile));

    // read processes
    for (int i = 0; i < total_proc; i++) {
        int VMA_num;
        Process process(i);
        VMA_num = std::stoi(next_valid_line(inputFile));
        for (int j = 0; j < VMA_num; j++) {
            int vp_start, vp_end, w_prot, file_mapped;
            sscanf(next_valid_line(inputFile).c_str(), "%d%d%d%d", &vp_start, &vp_end, &w_prot, &file_mapped);  
            VMA vma(vp_start, vp_end, w_prot, file_mapped);  
            process.vma_table.push_back(vma);
            process.set_bit_map(vp_start, vp_end, j);
        }
        proc_arr.push_back(process);
    }
    
    for (int i = 0; i < MAX_FRAMES; i++) {
        age_table.push_back(0);
    }

    simulate(pager, inputFile);

    // print stats
    if(opt_P) {
        for(Process proc: proc_arr) {
            std::cout << "PT[" << proc.pid << "]:";
            int i;
            for(i = 0; i < PT_LEN; i++) {
                if(proc.pageTable[i].present) {
                    std::cout << " "<< i << ":";
                    std::cout << (proc.pageTable[i].ref ? "R" : "-");
                    std::cout << (proc.pageTable[i].modified ? "M" : "-");
                    std::cout << (proc.pageTable[i].pout ? "S" : "-");
                } else if(proc.pageTable[i].pout) {
                        cout << " #";
                } else {
                        cout << " *";
                }
            }
            cout << endl;
        }
    }

    if(opt_F) {
        cout << "FT:";
        for(int i = 0; i < MAX_FRAMES; i++) {
            if(frame_table[i].proc_id == -1) {
                cout << " *";
            } else {
                cout << " " << frame_table[i].proc_id << ":" << frame_table[i].vpage->vpage_id;
            }
        }
        cout << endl;
    }

    if(opt_S) {
        // calculate summary
        for(Process proc: proc_arr) {
            proc.print_proc();
        }
        printf("TOTALCOST %lu %lu %lu %llu %lu\n", inst_count, ctx_switches, process_exits, total_cost, sizeof(PTE));
    }

    return 0;
}