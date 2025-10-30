#include <bits/stdc++.h>
using namespace std;

static const int H = 12, W = 12;
int board[H][W];               // 0 free, 1 wall, 2 target
int MAX_TURNS = 22;            // we’ll try 22 first, then 23
bool found_solution = false;

enum Dir { UP=0, DOWN=1, LEFT=2, RIGHT=3, NONE=4 };
struct Step { int r,c; };
vector<Step> solution;

// --- utilities
inline int idx(int r,int c){ return r*W + c; }
inline bool inb(int r,int c){ return (unsigned)r < H && (unsigned)c < W; }
inline void dir_delta(Dir d,int &dr,int &dc){
    switch(d){ case UP: dr=-1; dc=0; break; case DOWN: dr=1; dc=0; break;
    case LEFT: dr=0; dc=-1; break; case RIGHT: dr=0; dc=1; break; default: dr=0; dc=0; }
}
inline int turn_cost(Dir prev, Dir next){ return (prev==NONE || prev==next)?0:1; }

int count_goal_cells(){
    int cnt=0; for(int r=0;r<H;++r) for(int c=0;c<W;++c) if(board[r][c]!=1) ++cnt; return cnt;
}

// Precompute neighbors for speed
array<array<array<pair<int,int>,4>,W>,H> NEI;
array<array<int, W>, H> NEI_CNT;

void build_neighbors(){
    for(int r=0;r<H;++r) for(int c=0;c<W;++c){
        int k=0;
        auto push=[&](int rr,int cc){ if(inb(rr,cc) && board[rr][cc]!=1) NEI[r][c][k++] = {rr,cc}; };
        push(r-1,c); push(r+1,c); push(r,c-1); push(r,c+1);
        NEI_CNT[r][c]=k;
    }
}

// BFS over “available” cells: current head + all unvisited free cells
int components_with_head(const bitset<144>& visited, int head_r, int head_c){
    static int vismark[H][W], curmark=0; ++curmark;
    auto mark_used=[&](int r,int c){ vismark[r][c]=curmark; };
    auto is_marked=[&](int r,int c){ return vismark[r][c]==curmark; };

    int comps=0;
    // iterate over head and all unvisited frees
    for(int sr=0; sr<H; ++sr) for(int sc=0; sc<W; ++sc){
        if (!inb(sr,sc) || board[sr][sc]==1) continue;

        bool is_head = (sr==head_r && sc==head_c);
        bool avail = is_head || !visited.test(idx(sr,sc));
        if(!avail) continue;
        if(is_marked(sr,sc)) continue;

        // new component BFS
        ++comps;
        queue<pair<int,int>> q; q.push({sr,sc}); mark_used(sr,sc);
        while(!q.empty()){
            auto [r,c]=q.front(); q.pop();
            for(int i=0;i<NEI_CNT[r][c];++i){
                auto [nr,nc]=NEI[r][c][i];
                bool n_is_head = (nr==head_r && nc==head_c);
                bool n_avail = n_is_head || !visited.test(idx(nr,nc));
                if (!n_avail) continue;
                if(!is_marked(nr,nc)){ mark_used(nr,nc); q.push({nr,nc}); }
            }
        }
    }
    return comps;
}

// Compute degree (unvisited neighbors count) quickly
inline int unvisited_degree(int r,int c,const bitset<144>& visited){
    int d=0;
    for(int i=0;i<NEI_CNT[r][c];++i){
        auto [nr,nc]=NEI[r][c][i];
        if(!visited.test(idx(nr,nc))) ++d;
    }
    return d;
}

// Find target and (for your special 3x3) its forced predecessor (south neighbor inside the 3x3)
pair<pair<int,int>, pair<int,int>> find_target_and_forced_prev(){
    int tr=-1, tc=-1;
    for(int r=0;r<H;++r) for(int c=0;c<W;++c) if(board[r][c]==2){ tr=r; tc=c; }
    // default: no forced predecessor
    pair<int,int> forced = {-1,-1};
    if(tr!=-1){
        // In your pattern 111/121/100, only (tr+1, tc) is free inside that 3×3
        int rr = tr+1, cc = tc;
        if(inb(rr,cc) && board[rr][cc]==0) forced = {rr,cc};
    }
    return {{tr,tc}, forced};
}

// DFS with strong pruning & move ordering
void dfs(int r, int c, Dir d, int turns_used, bool teleport_used,
         bitset<144>& visited, vector<Step>& path,
         int goal_cells, int tr, int tc, int fpr, int fpc)
{
    if(found_solution) return;

    // success: all non-walls visited and on target
    if((int)path.size()==goal_cells && r==tr && c==tc){
        found_solution = true;
        solution = path;
        return;
    }

    // Connectivity prune (with teleport awareness)
    int comps = components_with_head(visited, r, c);
    int tele_left = teleport_used ? 0 : 1;
    if (comps > 1 + tele_left) return;

    // Generate candidate directed moves
    struct Cand{ Dir ndir; int nr,nc; int deg; int straight_bias; };
    vector<Cand> cand;
    for(int nd=0; nd<4; ++nd){
        Dir ndir = (Dir)nd;
        int dr,dc; dir_delta(ndir,dr,dc);
        int nr=r+dr, nc=c+dc;
        if(!inb(nr,nc) || board[nr][nc]==1) continue;
        if(visited.test(idx(nr,nc))) continue;

        // Gate final predecessor: delay taking it until near the end
        if (fpr!=-1 && nr==fpr && nc==fpc){
            int remain = goal_cells - (int)path.size();
            if (remain > 2) continue; // keep last-but-one
        }

        int deg = unvisited_degree(nr,nc,visited);
        int straight_bias = (d!=NONE && ndir==d) ? -1 : 0; // prefer straight
        cand.push_back({ndir,nr,nc,deg,straight_bias});
    }

    if(cand.empty()){
        // Try teleport if available; cost = +2 turns
        if(!teleport_used && turns_used+2 <= MAX_TURNS){
            // teleport to any unvisited free cell (don’t jump into forced-prev too early)
            for(int nr=0; nr<H; ++nr) for(int nc=0; nc<W; ++nc){
                if(board[nr][nc]==1) continue;
                if(visited.test(idx(nr,nc))) continue;
                if (fpr!=-1 && nr==fpr && nc==fpc){
                    int remain = goal_cells - (int)path.size();
                    if (remain > 2) continue;
                }
                // connectivity after teleport is checked at next recursion
                visited.set(idx(nr,nc));
                path.push_back({nr,nc});
                dfs(nr,nc,NONE, turns_used+2, true, visited, path, goal_cells, tr, tc, fpr, fpc);
                path.pop_back();
                visited.reset(idx(nr,nc));
                if(found_solution) return;
            }
        }
        return;
    }

    // Order: straight-first, then lowest onward degree
    sort(cand.begin(), cand.end(), [&](const Cand& a, const Cand& b){
        if(a.straight_bias != b.straight_bias) return a.straight_bias < b.straight_bias;
        return a.deg < b.deg;
    });

    for(const auto& mv : cand){
        int new_turns = turns_used + turn_cost(d, mv.ndir);
        if(new_turns > MAX_TURNS) continue;

        visited.set(idx(mv.nr,mv.nc));
        path.push_back({mv.nr,mv.nc});
        dfs(mv.nr, mv.nc, mv.ndir, new_turns, teleport_used,
            visited, path, goal_cells, tr, tc, fpr, fpc);
        path.pop_back();
        visited.reset(idx(mv.nr,mv.nc));
        if(found_solution) return;
    }

    // If normal moves didn’t work, consider teleport as a branch *after* trying moves
    if(!found_solution && !teleport_used && turns_used+2 <= MAX_TURNS){
        for(int nr=0; nr<H; ++nr) for(int nc=0; nc<W; ++nc){
            if(board[nr][nc]==1) continue;
            if(visited.test(idx(nr,nc))) continue;
            if (fpr!=-1 && nr==fpr && nc==fpc){
                int remain = goal_cells - (int)path.size();
                if (remain > 2) continue;
            }
            visited.set(idx(nr,nc));
            path.push_back({nr,nc});
            dfs(nr,nc,NONE, turns_used+2, true, visited, path, goal_cells, tr, tc, fpr, fpc);
            path.pop_back();
            visited.reset(idx(nr,nc));
            if(found_solution) return;
        }
    }
}

// --- plug in your actual board construction here
void build_board(){
    // Fill with your 4×4 of 3×3 logic. For now: all free.
    for(int r=0;r<H;++r) for(int c=0;c<W;++c) board[r][c]=0;

    // Example: one special 3×3 at submatrix (1,2)
    // local pattern 111/121/100:
    int R=1, C=2; // place the special block
    int base_r = R*3, base_c = C*3;
    int pat[3][3] = {{1,1,1},{1,2,1},{1,0,0}};
    for(int i=0;i<3;++i)for(int j=0;j<3;++j) board[base_r+i][base_c+j] = pat[i][j];
}
void print_board(){
    for(int r=0;r<H;++r){
        for(int c=0;c<W;++c){
            cout<<board[r][c];
        }
        cout<<"\n";
    }
}
void print_solution(){
    //print the solution as an overlay on the board with direction changes and ansi colors
    vector<string> disp(H, string(W, ' '));
    for(size_t i=1;i<solution.size();++i){
        auto [pr,pc]=solution[i-1];
        auto [cr,cc]=solution[i];
        char sym=' ';
        if(cr==pr-1 && cc==pc) sym='^';
        else if(cr==pr+1 && cc==pc) sym='v';
        else if(cr==pr && cc==pc-1) sym='<';
        else if(cr==pr && cc==pc+1) sym='>';
        disp[cr][cc]=sym;
    }
    for(const auto& row : disp){
        for(char c : row) cout<<c;
        cout<<"\n";
    }
}
int main(){
    build_board();
    build_neighbors();
    print_board();
    // start (11,7), first forced step up (10,7)
    int sr=11, sc=7;
    if(board[sr][sc]==1){ cerr<<"Start in wall\n"; return 1; }

    auto [tgt, forced_prev] = find_target_and_forced_prev();
    int tr=tgt.first, tc=tgt.second;
    if(tr==-1){ cerr<<"No target (2) on board\n"; return 1; }

    int fpr = forced_prev.first, fpc = forced_prev.second;

    int goal_cells = count_goal_cells();

    for(MAX_TURNS=22; MAX_TURNS<=23; ++MAX_TURNS){
        found_solution=false; solution.clear();

        bitset<144> visited; vector<Step> path;
        // start
        visited.set(idx(sr,sc)); path.push_back({sr,sc});
        // initial step up
        int fr=sr-1, fc=sc;
        if(!inb(fr,fc) || board[fr][fc]==1 || visited.test(idx(fr,fc))){
            cerr<<"Cannot start upward\n"; return 1;
        }
        visited.set(idx(fr,fc)); path.push_back({fr,fc});

        dfs(fr, fc, UP, 0, false, visited, path, goal_cells, tr, tc, fpr, fpc);

        if(found_solution){
            cout<<"Found full-coverage with ≤"<<MAX_TURNS<<" turns.\n";
            cout<<"Steps: "<<solution.size()<<"\n";
            print_solution();
            return 0;
        }else{
            cout<<"No full-coverage with ≤"<<MAX_TURNS<<" turns.\n";
        }
    }
    return 0;
}
