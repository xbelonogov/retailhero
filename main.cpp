#include <algorithm>
#include <bitset>
#include <cassert>
#include <chrono>
#include <cmath>
#include <complex>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <fstream>
#include <iostream>
#include <map>
#include <queue>
#include <random>
#include <set>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#define all(a) (a).begin(), (a).end()

using namespace std;
const int MAX_N = 5000;
const int MAX_CAT = 50;
const int MAX_BRAND = 50;

double getTime() { return clock() * 1.0 / CLOCKS_PER_SEC; }

bool eq(double a, double b) { return abs(a - b) < 1e-9; }

bool eq_rel(double a, double b) {
    double norm = max(1.0, max(abs(a), abs(b)));
    return abs(a - b) / norm < 1e-9;
}

bool ls(double a, double b) { return a < b && !eq(a, b); }

bool le(double a, double b) { return a < b || eq(a, b); }


typedef long long ll;
typedef double dbl;
const int INF = static_cast<int>(1.01e9);
const int dx[4] = {1, 0, -1, 0};
const int dy[4] = {0, 1, 0, -1};
mt19937 rnd(19);

double brandF(int k) {
    assert(0 <= k && k <= 5000);
    if (k == 0) {
        return 0;
    }
    return 1 + log2(k);
}

vector<double> normArray(vector<double> a) {
    double sum = 0;
    for (auto x: a) {
        sum += x;
    }
    for (auto& x: a) {
        x /= sum;
    }
    return a;
}


int randInt(int l, int r) {
    uniform_int_distribution<> dist(l, r);
    return dist(rnd);
}

vector<int> randPerm(int n) {
    vector<int> perm(n);
    iota(all(perm), 0);
    shuffle(all(perm), rnd);
    return perm;
}


double randDouble(double l, double r) {
    uniform_real_distribution<double> dist(l, r);
    return dist(rnd);
}
template <typename T> vector<vector<T>> simBoard(const vector<vector<T>>& a) {
    vector<vector<T>> ret(a[0].size(), vector<T>(a.size()));
    for (int i = 0; i < (int)a.size(); i++) {
        for (int j = 0; j < (int)a[i].size(); j++) {
            ret[j][i] = a[i][j];
        }
    }
    return ret;
}

template <typename T>
void copyBoard2D(vector<vector<T>>& target, const vector<vector<T>>& source, int shiftX, int shiftY) {
    assert(target.size() >= source.size() + shiftX);
    assert(target[0].size() >= source[0].size() + shiftY);
    for (size_t i = 0; i < source.size(); i++) {
        copy(all(source[i]), target[i + shiftX].begin() + shiftY);
    }
}


void printBoard(const vector<vector<int>>& board) {
    cerr << "--------------- board --------------" << endl;
    for (int i = 0; i < (int)board.size(); i++, cerr << endl) {
        for (int j = 0; j < (int)board[i].size(); j++) {
            fprintf(stderr, "%2d ", board[i][j]);
        }
    }
}


struct pt {
    int x {0}, y {0};
    pt() = default;
    pt(int x, int y)
        : x(x)
        , y(y) {}
    bool operator==(pt A) const { return x == A.x && y == A.y; }
    bool operator!=(pt A) const { return x != A.x || y != A.y; }
    pt operator+(pt A) const { return {x + A.x, y + A.y}; }
    pt operator-(pt A) const { return {x - A.x, y - A.y}; }
    pt operator*(int k) const { return {x * k, y * k}; }
    pt operator/(int k) const {
        assert(x % k == 0 && y % k == 0);
        return {x / k, y / k};
    }
    int lenInt() const {
        assert(x == 0 || y == 0);
        return abs(x) + abs(y);
    }
    int l1() const { return abs(x) + abs(y); }
    pt norm() const { return (*this) / lenInt(); }
    pt turn() const { return {-y, x}; }
    void print() { cerr << "x: " << x << "   y: " << y << endl; }
};

struct Item {
    int cat {-1};
    int brand {-1};
    int c {0};
    int id {-1};
    bool operator<(const Item& other) const { return c > other.c; }
};

struct Score {
    double s1 {0};
    double s2 {0};
    double sum {0};
    double cover {0};
};

void printBoard(const vector<vector<Item>>& board) {
    cerr << "--------------- board --------------" << endl;
    for (int i = 0; i < (int)board.size(); i++, cerr << endl) {
        for (int j = 0; j < (int)board[i].size(); j++) {
            fprintf(stderr, "%2d ", board[i][j].id);
        }
    }
}

vector<vector<int>> toRowId(const vector<vector<Item>>& board) {
    vector<vector<int>> a(board.size(), vector<int>(board[0].size(), -1));
    for (size_t i = 0; i < board.size(); i++) {
        for (size_t j = 0; j < board[i].size(); j++) {
            a[i][j] = board[i][j].id;
        }
    }
    return a;
}

struct Rect {
    int x {0}, y {0}, h {0}, w {0};
};

struct Board {
    vector<vector<Item>> board;
    Score score;

    vector<Rect> rects;
    Board(vector<vector<Item>> board, const Score& score)
        : board(std::move(board))
        , score(score) {}

    void addRects(const vector<Rect>& newRects, int ddx, int ddy) {
        for (auto r: newRects) {
            r.x += ddx;
            r.y += ddy;
            rects.push_back(r);
        }
    }
    bool operator<(const Board& rhs) const { return score.sum < rhs.score.sum; }
};


struct BrandState {
    int cntItems {0};
    int totalCost {0};
    BrandState() = default;
    BrandState(int cnt_items, int total_cost)
        : cntItems(cnt_items)
        , totalCost(total_cost) {}
    BrandState operator+(const BrandState& other) const {
        return {cntItems + other.cntItems, totalCost + other.totalCost};
    }
    double getScore() const { return brandF(cntItems) * totalCost; }
};

struct Edge {
    int v, u;
    double cost;
};

struct Task {
    int n, nCat, nBrand, h, w, D0;
    vector<Item> items;

    vector<Item> itemById;
    vector<vector<Item>> itemsByCat;
    vector<int> brandUp;
    vector<int> brandDown;
    vector<int> brandLeft;
    vector<int> brandRight;

    double realD = -1;

    Task() = default;
    Task(int n, int nCat, int nBrand, int h, int w, int D0, const vector<Item>& items)
        : n(n)
        , nCat(nCat)
        , nBrand(nBrand)
        , h(h)
        , w(w)
        , D0(D0)
        , items(items) {
        compute();
    }
    [[nodiscard]] vector<int> toArray() const {
        vector<int> ret = {n, nCat, nBrand, h, w, D0};
        for (auto item: items) {
            ret.push_back(item.cat);
            ret.push_back(item.brand);
            ret.push_back(item.id);
            ret.push_back(item.c);
        }
        return ret;
    }
    vector<Edge> categoryEdges() const {
        vector<int> nonEmptyCats;
        for (int i = 0; i < nCat; i++) {
            if (!itemsByCat[i].empty()) {
                nonEmptyCats.push_back(i);
            }
        }
        //        vector<vector<BrandState>> bs(nonEmptyCats.size(), vector<BrandState>(nBrand));
        vector<vector<double>> bs2(nonEmptyCats.size(), vector<double>(nBrand));
        for (int i = 0; i < (int)nonEmptyCats.size(); i++) {
            int catId = nonEmptyCats[i];
            assert(!itemsByCat[catId].empty());
            for (const auto& item: itemsByCat[catId]) {
                //                bs[i][item.brand] = bs[i][item.brand] + BrandState(1, item.c);
                bs2[i][item.brand]++;
            }
            bs2[i] = normArray(bs2[i]);
        }
        vector<Edge> edges;
        for (int i = 0; i < (int)nonEmptyCats.size(); i++) {
            for (int j = i + 1; j < (int)nonEmptyCats.size(); j++) {
                double score = 0;
                for (int k = 0; k < nBrand; k++) {
                    //                    double localState = (bs[i][k] + bs[j][k]).getScore() - bs[i][k].getScore() -
                    //                    bs[j][k].getScore();
                    double localState = min(bs2[i][k], bs2[j][k]);
                    assert(localState >= 0);
                    score += localState;
                }
                if (le(0, score)) {
                    score += randDouble(0, 0.1);
                    edges.push_back({nonEmptyCats[i], nonEmptyCats[j], score});
                }
            }
        }
        sort(all(edges), [](Edge A, Edge B) { return A.cost > B.cost; });

        return edges;
    }


    int nUniqueCat() const {
        int ret = 0;
        for (const auto& ids: itemsByCat) {
            ret += !ids.empty();
        }
        return ret;
    }
    void compute() {
        itemsByCat.assign(nCat, vector<Item>());
        itemById.resize(n);
        for (auto item: items) {
            itemsByCat[item.cat].push_back(item);
            assert(item.id < n);
            itemById[item.id] = item;
        }
        realD = D0 / sqrt(h * w);
        brandRight.resize(h, -1);
        brandLeft.resize(h, -1);
        brandUp.resize(w, -1);
        brandDown.resize(w, -1);
    }

    void read() {
        cin >> n >> nCat >> nBrand >> h >> w >> D0;
        items.resize(n);
        for (int i = 0; i < n; i++) {
            cin >> items[i].cat >> items[i].brand >> items[i].c;
            items[i].id = i;
            items[i].cat--;
            items[i].brand--;
        }
        compute();
    }
    void debug() const {
        cerr << "n: " << n << "   nCat: " << nCat << "  brandCount: " << nBrand << endl;
        cerr << "h: " << h << "   w: " << w << "  D0: " << D0 << endl;
        map<int, int> catSize;
        map<int, int> brandSize;
        for (auto x: items) {
            catSize[x.cat]++;
            brandSize[x.brand]++;
        }
        int dd = 0;
        for (auto x: items) {
            cerr << "cat: " << x.cat << "   brand: " << x.brand << "   c: " << x.c << "    id: " << x.id << endl;
            dd++;
            if (dd > 5) {
                break;
            }
        }
    }
    [[nodiscard]] int getCat(int id) const {
        if (id == -1) {
            return -1;
        }
        return itemById.at(id).cat;
    }
    [[nodiscard]] int getBrand(int id) const {
        if (id == -1) {
            return -1;
        }
        return itemById.at(id).brand;
    }
    int getCost(int id) const {
        if (id == -1) {
            return -1;
        }
        return itemById.at(id).c;
    }

    [[nodiscard]] double catUplift(int cnt) const {
        assert(cnt >= 0);
        return D0 / sqrt(h * w) * (sqrt(cnt + 1) - sqrt(cnt));
    }
    [[nodiscard]] vector<vector<int>> emptyBoard() const { return vector<vector<int>>(h, vector<int>(w, -1)); }
    [[nodiscard]] vector<vector<Item>> emptyBoardNew() const { return vector<vector<Item>>(h, vector<Item>(w)); }
    [[nodiscard]] Board emptyBoardBoard() const { return {vector<vector<Item>>(h, vector<Item>(w)), {}}; }

    struct BrandCount {
        int brand;
        int count;
    };
    [[nodiscard]] vector<BrandCount> brandWithCount() const {
        vector<BrandCount> ret(nBrand);
        for (int i = 0; i < nBrand; i++) {
            ret[i].brand = i;
        }
        for (const auto& item: items) {
            ret[item.brand].count++;
        }
        sort(all(ret), [](BrandCount A, BrandCount B) { return A.count > B.count; });
        return ret;
    }
};

struct DSU {
    vector<int> p;
    explicit DSU(int n) {
        p.resize(n);
        iota(all(p), 0);
    }
    int getId(int v) { return p[v] == v ? v : p[v] = getId(p[v]); }
    void merge(int v, int u) {
        v = getId(v);
        u = getId(u);
        p[v] = u;
    }
};


void printCat(const Task& task, const vector<vector<int>>& board) {
    cerr << "--------------- cat --------------" << endl;
    for (int i = 0; i < (int)board.size(); i++, cerr << endl) {
        for (int j = 0; j < (int)board[i].size(); j++) {
            int id = board[i][j];
            int cat = (id == -1) ? -1 : task.getCat(id);
            fprintf(stderr, "%2d ", cat);
        }
    }
}

void printBrand(const Task& task, const vector<vector<int>>& board) {
    cerr << "--------------- brand --------------" << endl;
    for (int i = 0; i < (int)board.size(); i++, cerr << endl) {
        for (int j = 0; j < (int)board[i].size(); j++) {
            int id = board[i][j];
            int cat = (id == -1) ? -1 : task.getBrand(id);
            fprintf(stderr, "%2d ", cat);
        }
    }
}

vector<vector<int>> computeMaxBox(const Task& task, const vector<vector<int>>& board) {
    vector<vector<int>> maxBox(task.h, vector<int>(task.w));
    for (int i = 0; i < task.h; i++) {
        vector<int> eqCol(task.w, 1);
        for (int j = i + 1; j <= task.h; j++) {
            for (int k = 0; k < task.w; k++) {
                if (j == i + 1) {
                    eqCol[k] &= board[j - 1][k] != -1;
                } else {
                    if (eqCol[k] != 0) {
                        if (board[j - 1][k] == -1) {
                            eqCol[k] = 0;
                        } else {
                            eqCol[k] &= task.getBrand(board[j - 1][k]) == task.getBrand(board[j - 2][k]);
                        }
                    }
                }
            }
            for (int k = 0; k < task.w;) {

                int st = k;
                if (eqCol[k] == 0) {
                    k++;
                    continue;
                }
                //                int base = task.items[board[i][k]].brand;
                int base = task.getBrand(board[i][k]);
                //                for (; k < task.w && eqCol[k] && task.items[board[i][k]].brand == base; k++);
                for (; k < task.w && eqCol[k] && task.getBrand(board[i][k]) == base; k++)
                    ;

                int area = (j - i) * (k - st);
                for (int x = i; x < j; x++) {
                    for (int y = st; y < k; y++) {
                        maxBox[x][y] = max(maxBox[x][y], area);
                    }
                }
            }
        }
    }
    return maxBox;
}

template <size_t N> struct FastClearBoolArray {
    int used[N];
    int timeCur {0};
    void clear() { timeCur++; }
    void setBit(int pos) { used[pos] = timeCur; }
    bool getBit(int pos) const { return used[pos] == timeCur; }
};


FastClearBoolArray<MAX_N> dpfc;

struct BrandDP {
    vector<Item> items;
    map<int, vector<Item>> mpItemsByBrand;
    vector<vector<Item>> itemsByBrand;
    vector<vector<double>> prefSum;
    vector<vector<double>> dp;
    vector<vector<int>> par;

    BrandDP() = default;
    BrandDP(vector<Item> _items, int w)
        : items(std::move(_items)) {
        for (int i = 0; i < (int)items.size(); i++) {
            assert(items[i].cat == items[0].cat);
        }
        for (auto item: items) {
            mpItemsByBrand[item.brand].push_back(item);
        }
        for (const auto& x: mpItemsByBrand) {
            itemsByBrand.push_back(x.second);
        }
        prefSum.resize(itemsByBrand.size());

        for (int i = 0; i < (int)itemsByBrand.size(); i++) {
            sort(all(itemsByBrand[i]));
            prefSum[i].resize(itemsByBrand[i].size() + 1);
            double ss = 0;
            for (int j = 0; j < (int)itemsByBrand[i].size(); j++) {
                ss += itemsByBrand[i][j].c;
                prefSum[i][j + 1] = ss * brandF(j + 1);
            }
        }

        w = min(w, (int)items.size());
        dp.resize(itemsByBrand.size(), vector<double>(w + 1, -1));
        par.resize(itemsByBrand.size(), vector<int>(w + 1));
        for (int k = 0; k < (int)itemsByBrand.size(); k++) {
            for (int i = 0; i <= w; i++) {
                for (int j = 0; j <= (int)itemsByBrand[k].size() && i + j <= w; j++) {
                    double prevDp = (k == 0) ? 0.0 : dp[k - 1][i];
                    if (prevDp + prefSum[k][j] > dp[k][i + j]) {
                        dp[k][i + j] = prevDp + prefSum[k][j];
                        par[k][i + j] = j;
                    }
                }
            }
        }
    }

    double getScore(int k) {
        assert(k <= (int)dp[0].size());
        return dp.back()[k];
    }

    vector<Item> getPath(int nItems) const {
        assert(nItems < (int)dp[0].size());
        vector<Item> answer;
        for (int brandId = (int)dp.size() - 1; brandId >= 0; brandId--) {
            int curCount = par[brandId][nItems];
            assert(curCount >= 0 && curCount <= nItems);
            for (int i = 0; i < curCount; i++) {
                answer.push_back(itemsByBrand[brandId][i]);
            }
            nItems -= curCount;
        }
        assert(nItems == 0);
        return answer;
    }

    vector<Item> subtract(const vector<int>& id) const {
        dpfc.clear();
        for (auto x: id) {
            dpfc.setBit(x);
        }
        vector<Item> ret;
        for (auto x: items) {
            if (dpfc.getBit(x.id)) {
                ret.push_back(x);
            }
        }
        return ret;
    }
};

bool checkBoardUsedId[MAX_N];
int chbmnX[MAX_CAT];
int chbmnY[MAX_CAT];
int chbmxX[MAX_CAT];
int chbmxY[MAX_CAT];
int chbCnt[MAX_CAT];

void checkBoard(const Task& task, const vector<vector<int>>& board) {
    assert(task.realD > 0);
    assert((int)board.size() == task.h);
    memset(checkBoardUsedId, 0, task.n);
    for (int i = 0; i < task.h; i++) {
        assert((int)board[i].size() == task.w);
        for (int j = 0; j < task.w; j++) {
            int id = board[i][j];
            if (id != -1) {
                assert(!checkBoardUsedId[id]);
                assert(0 <= id && id < (int)task.n);
                checkBoardUsedId[id] = true;
            }
        }
    }

    fill(chbmnX, chbmnX + task.nCat, INF);
    fill(chbmnY, chbmnY + task.nCat, INF);
    fill(chbmxX, chbmxX + task.nCat, -1);
    fill(chbmxY, chbmxY + task.nCat, -1);
    fill(chbCnt, chbCnt + task.nCat, 0);

    for (int i = 0; i < task.h; i++) {
        for (int j = 0; j < task.w; j++) {
            int id = board[i][j];
            if (id != -1) {
                int catId = task.getCat(id);
                chbmnX[catId] = min(chbmnX[catId], i);
                chbmxX[catId] = max(chbmxX[catId], i);
                chbmnY[catId] = min(chbmnY[catId], j);
                chbmxY[catId] = max(chbmxY[catId], j);
                chbCnt[catId]++;
            }
        }
    }
    for (int i = 0; i < task.nCat; i++) {
        if (chbCnt[i] > 0) {
            int area = (chbmxX[i] - chbmnX[i] + 1) * (chbmxY[i] - chbmnY[i] + 1);
            assert(area >= chbCnt[i]);
            assert(area == chbCnt[i]);
        }
    }
}

double totalInComputeScore = 0;


vector<pt> mbPos[MAX_CAT][MAX_BRAND];
vector<Item> mbItems[MAX_CAT][MAX_BRAND];

Score computeScore(const Task& task, vector<vector<int>>& board, const vector<vector<int>>* maxBoxHelp = nullptr,
                   bool debug = false) {
    totalInComputeScore -= getTime();
    checkBoard(task, board);
    vector<int> catCount(task.nCat);
    for (const auto& row: board) {
        for (auto id: row) {
            if (id != -1) {
                catCount[task.getCat(id)]++;
            }
        }
    }
    double s1 = 0;
    for (auto x: catCount) {
        s1 += sqrt(x) * task.realD;
    }

    vector<vector<int>> maxBox = (maxBoxHelp == nullptr) ? computeMaxBox(task, board) : *maxBoxHelp;

    for (int i = 0; i < task.nCat; i++) {
        for (int j = 0; j < task.nBrand; j++) {
            mbPos[i][j].clear();
            mbItems[i][j].clear();
        }
    }
    for (int i = 0; i < task.h; i++) {
        for (int j = 0; j < task.w; j++) {
            int id = board[i][j];
            if (id != -1) {
                auto item = task.itemById[id];
                assert(item.id == id);
                mbPos[item.cat][item.brand].push_back({i, j});
                mbItems[item.cat][item.brand].push_back(item);
            }
        }
    }
    for (int i = 0; i < task.nCat; i++) {
        for (int j = 0; j < task.nBrand; j++) {
            assert(mbPos[i][j].size() == mbItems[i][j].size());
            if (mbPos[i][j].empty()) {
                continue;
            }
            sort(all(mbPos[i][j]), [&](const pt& A, const pt& B) { return maxBox[A.x][A.y] > maxBox[B.x][B.y]; });
            sort(all(mbItems[i][j]), [&](const Item& A, const Item& B) { return A.c > B.c; });
            for (int k = 0; k < (int)mbPos[i][j].size(); k++) {
                pt A = mbPos[i][j][k];
                board[A.x][A.y] = mbItems[i][j][k].id;
            }
        }
    }


    auto boardItem = task.emptyBoardNew();
    for (int i = 0; i < task.h; i++) {
        for (int j = 0; j < task.w; j++) {
            if (board[i][j] != -1) {
                boardItem[i][j] = task.itemById[board[i][j]];
            }
        }
    }
    if (debug) {
        assert(task.n == (int)task.items.size());
        cerr << endl;
        cerr << "------ cat -----" << endl;
        for (int i = 0; i < task.h; i++, cerr << endl) {
            for (int j = 0; j < task.w; j++) {
                int val = (board[i][j] == -1) ? -1 : task.items[board[i][j]].cat;
                fprintf(stderr, "%2d ", val);
            }
        }
        vector<vector<int>> brandAdv(task.h * 2 - 1, vector<int>(task.w * 2 - 1, -10));
        for (int i = 0; i < task.h; i++) {
            for (int j = 0; j < task.w; j++) {
                brandAdv[i * 2][j * 2] = (board[i][j] == -1) ? -1 : task.items[board[i][j]].brand;
                if (i + 1 < task.h && boardItem[i][j].cat != boardItem[i + 1][j].cat) {
                    brandAdv[i * 2 + 1][j * 2] = -9;
                }
                if (j + 1 < task.w && boardItem[i][j].cat != boardItem[i][j + 1].cat) {
                    brandAdv[i * 2][j * 2 + 1] = -8;
                }
            }
        }
        cerr << "------ brand adv -----" << endl;
        for (int i = 0; i < task.h * 2 - 1; i++, cerr << endl) {
            for (int j = 0; j < task.w * 2 - 1; j++) {
                int xx = brandAdv[i][j];
                if (xx == -10) {
                    cerr << "   ";
                }
                if (xx == -9) {
                    cerr << "---";
                }
                if (xx == -8) {
                    cerr << " | ";
                }
                if (xx >= -1) {
                    fprintf(stderr, "%2d ", xx);
                }
            }
        }
        cerr << "------ maxBox -----" << endl;
        for (int i = 0; i < task.h; i++, cerr << endl) {
            for (int j = 0; j < task.w; j++) {
                fprintf(stderr, "%2d ", maxBox[i][j]);
            }
        }
    }

    double s2 = 0;
    double sumLog = 0;
    int cntLog = 0;
    int notEmpty = 0;
    for (int i = 0; i < task.h; i++) {
        for (int j = 0; j < task.w; j++) {
            int id = board[i][j];
            if (id != -1) {
                notEmpty++;
                //                s2 += task.items[id].c * brandF(maxBox[i][j]);
                s2 += task.getCost(id) * brandF(maxBox[i][j]);
                sumLog += brandF(maxBox[i][j]);
                cntLog++;
            }
        }
    }
    int cc = 0;
    for (int i = 0; i < task.h; i++) {
        for (int j = 0; j < task.w; j++) {
            cc += board[i][j] != -1;
        }
    }

    Score score;
    score.s1 = s1;
    score.s2 = s2;
    score.sum = s1 + s2;
    assert(notEmpty <= task.h * task.w);
    score.cover = notEmpty * 1.0 / (task.h * task.w);
    totalInComputeScore += getTime();
    return score;
}
Score computeScore(const Task& task, vector<vector<Item>> board, const vector<vector<int>>* maxBoxHelp = nullptr,
                   bool debug = false) {
    vector<vector<int>> tmp = toRowId(board);


    Score score = computeScore(task, tmp, maxBoxHelp, debug);
    for (int i = 0; i < task.h; i++) {
        for (int j = 0; j < task.w; j++) {
            assert((tmp[i][j] == -1) == (board[i][j].id == -1));
            if (tmp[i][j] != -1) {
                board[i][j] = task.itemById[tmp[i][j]];
            }
        }
    }
    return score;
}

vector<Item> select(const Task& task, double avgLog) {

    vector<Item> tmpItems = task.items;
    vector<Item> items;
    int batchSize = max(1, task.n / 20);
    vector<int> countByCat(task.nCat);

    auto catImp = [&](int catId) { return task.realD * (sqrt(countByCat[catId] + 1) - sqrt(countByCat[catId])); };

    for (; !tmpItems.empty();) {
        sort(tmpItems.begin(), tmpItems.end(),
             [&](const Item& A, const Item& B) { return avgLog * A.c + catImp(A.cat) > avgLog * B.c + catImp(B.cat); });
        int cc = min((int)tmpItems.size(), batchSize);
        for (int i = 0; i < cc; i++) {
            countByCat[tmpItems[i].cat]++;
        }
        items.insert(items.end(), tmpItems.begin(), tmpItems.begin() + cc);
        tmpItems.erase(tmpItems.begin(), tmpItems.begin() + cc);
    }
    assert((int)items.size() == task.n);
    return items;
}

vector<vector<int>> makeBoard(const vector<int>& targetCat, const Task& task, const vector<Item>& items) {
    vector<vector<int>> board(task.h, vector<int>(task.w, -1));
    vector<int> progress(task.h, task.w);
    vector<pair<int, int>> targetOrder;
    for (int i = 0; i < task.nCat; i++) {
        targetOrder.emplace_back(targetCat[i], i);
    }
    sort(all(targetOrder));
    reverse(all(targetOrder));
    struct Node {
        int catCount {-1};
        int where {-1};
    };
    vector<Node> revCat(task.nCat);
    vector<int> multiLineShift(task.h);
    for (auto x: targetOrder) {
        if (x.first > task.w) {
            int nRow = (x.first + task.w - 1) / task.w;
            int rowLen = x.first / nRow;
            assert(nRow * rowLen <= x.first);
            int fullRows = 0;
            int upRow = task.h;
            for (int i = 0; i < task.h; i++) {
                if (progress[i] == task.w) {
                    fullRows++;
                    upRow = min(i, upRow);
                }
            }
            assert(task.h - upRow == fullRows);
            if (fullRows >= nRow) {
                for (int i = 0; i < nRow; i++) {
                    progress[i + upRow] -= rowLen;
                    multiLineShift[i + upRow] = rowLen;
                    for (int j = 0; j < rowLen; j++) {
                        board[i + upRow][j] = x.second;
                    }
                }
            } else {
                return vector<vector<int>>();
            }
        } else {
            int bestId = -1;
            int bestDiff = INF;
            for (int i = 0; i < task.h; i++) {
                if (progress[i] >= x.first && (bestDiff > progress[i] - x.first)) {
                    bestId = i;
                    bestDiff = progress[i] - x.first;
                }
            }
            if (bestId == -1) {
                return vector<vector<int>>();
            }
            progress[bestId] -= x.first;
            revCat[x.second] = {x.first, bestId};
        }
    }
    for (auto item: items) {
        int rowId = revCat[item.cat].where;
        if (rowId != -1 && progress[rowId] > 0) {
            progress[rowId]--;
            revCat[item.cat].catCount++;
        }
    }
    for (int i = 0; i < task.nCat; i++) {
        if (revCat[i].where == -1) {
            continue;
        }
        int rowId = revCat[i].where;
        for (int j = 0; j < revCat[i].catCount; j++) {
            board[rowId][multiLineShift[rowId]++] = i;
        }
    }
    return board;
}

vector<vector<int>> fillBoard(const vector<vector<int>>& boardCat, const vector<Item>& items, const Task& task) {
    vector<vector<pair<int, int>>> catPos(task.nCat);
    assert((int)boardCat.size() == task.h);
    for (int i = 0; i < task.h; i++) {
        assert((int)boardCat[i].size() == task.w);
        for (int j = 0; j < task.w; j++) {
            if (boardCat[i][j] != -1) {
                catPos[boardCat[i][j]].push_back({i, j});
            }
        }
    }
    for (int i = 0; i < task.nCat; i++) {
        sort(all(catPos[i]), [](pair<int, int> A, pair<int, int> B) {
            return A.second < B.second || (A.second == B.second && A.first < B.first);
        });
    }
    vector<vector<Item>> itemByCat(task.nCat);
    for (int i = 0; i < (int)items.size(); i++) {
        int catId = items[i].cat;
        if (itemByCat[catId].size() < catPos[catId].size()) {
            itemByCat[catId].push_back(items[i]);
        }
    }
    for (int i = 0; i < task.nCat; i++) {
        sort(all(itemByCat[i]), [](Item A, Item B) { return A.brand < B.brand; });
    }

    vector<vector<int>> finalBoard(task.h, vector<int>(task.w, -1));
    for (int i = 0; i < task.nCat; i++) {
        assert(itemByCat[i].size() == catPos[i].size());
        for (int j = 0; j < (int)catPos[i].size(); j++) {
            auto x = catPos[i][j];
            finalBoard[x.first][x.second] = itemByCat[i][j].id;
        }
    }
    return finalBoard;
}

vector<vector<int>> fillBoardV2(const vector<vector<int>>& boardCat, const vector<Item>& items, const Task& task) {
    vector<int> catSize(task.nCat);
    assert((int)boardCat.size() == task.h);
    for (int i = 0; i < task.h; i++) {
        assert((int)boardCat[i].size() == task.w);
        for (int j = 0; j < task.w; j++) {
            if (boardCat[i][j] != -1) {
                catSize[boardCat[i][j]]++;
            }
        }
    }
    vector<vector<Item>> allByCat(task.nCat);
    for (auto x: items) {
        allByCat[x.cat].push_back(x);
    }
    vector<vector<Item>> itemByCat(task.nCat);
    for (int i = 0; i < task.nCat; i++) {
        vector<int> brandCount(task.nBrand);
        vector<double> curW(task.nBrand);
        for (int j = 0; j < catSize[i]; j++) {
            double bestImp = 0;
            double bestId = -1;
            for (int k = 0; k < (int)allByCat[i].size(); k++) {
                auto x = allByCat[i][k];
                double newCof = brandF(brandCount[x.brand] + 1);
                double oldCof = 0;
                if (brandCount[x.brand] > 0) {
                    oldCof = brandF(brandCount[x.brand]);
                }
                double curImp = (x.c + curW[x.brand]) * newCof - oldCof * curW[x.brand];
                if (curImp > bestImp) {
                    bestImp = curImp;
                    bestId = k;
                }
            }
            assert(bestId != -1);
            itemByCat[i].push_back(allByCat[i][bestId]);
            auto x = allByCat[i][bestId];
            brandCount[x.brand]++;
            curW[x.brand] += x.c;
            allByCat[i].erase(allByCat[i].begin() + bestId);
        }
        assert(catSize[i] == (int)itemByCat[i].size());
    }

    for (int i = 0; i < task.nCat; i++) {
        sort(all(itemByCat[i]), [](Item A, Item B) { return A.brand < B.brand; });
    }

    auto getWithBrand = [&](int curCat, int curBrand) {
        int bestPos = -1;
        for (int i = 0; i < (int)itemByCat[curCat].size(); i++) {
            const auto& x = itemByCat[curCat][i];
            if (x.brand == curBrand && (bestPos == -1 || itemByCat[curCat][bestPos].c < x.c)) {
                bestPos = i;
            }
        }
        return bestPos;
    };

    vector<vector<int>> finalBoard(task.h, vector<int>(task.w, -1));
    for (int i = 0; i < task.h; i++) {
        bool change = true;
        for (; change;) {
            change = false;
            for (int j = 0; j < task.w; j++) {
                if (finalBoard[i][j] != -1 || boardCat[i][j] == -1) {
                    continue;
                }
                int curCat = boardCat[i][j];
                //                assert((upId == -1) == (curCat == -1));
                if (i > 0 && finalBoard[i - 1][j] != -1) {
                    int upId = finalBoard[i - 1][j];
                    int tmpId = getWithBrand(curCat, task.items[upId].brand);
                    if (tmpId != -1) {
                        finalBoard[i][j] = itemByCat[curCat][tmpId].id;
                        itemByCat[curCat].erase(itemByCat[curCat].begin() + tmpId);
                        change = true;
                        continue;
                    }
                }
                for (int dj: {-1, 1}) {
                    int nj = j + dj;
                    if (0 <= nj && nj < task.w && finalBoard[i][nj] != -1) {
                        int needBrand = task.items[finalBoard[i][nj]].brand;
                        int tmpId = getWithBrand(curCat, needBrand);
                        if (tmpId != -1) {
                            finalBoard[i][j] = itemByCat[curCat][tmpId].id;
                            itemByCat[curCat].erase(itemByCat[curCat].begin() + tmpId);
                            change = true;
                            break;
                        }
                    }
                }
            }
        }

        for (int j = 0; j < task.w; j++) {
            if (boardCat[i][j] != -1 && finalBoard[i][j] == -1) {
                int curCat = boardCat[i][j];
                assert(!itemByCat[curCat].empty());
                int tmpId = itemByCat[curCat].back().id;
                itemByCat[curCat].pop_back();
                finalBoard[i][j] = tmpId;
            }
        }
    }
    for (int i = 0; i < task.h; i++) {
        for (int j = 0; j < task.w; j++) {
            assert((finalBoard[i][j] == -1) == (boardCat[i][j] == -1));
        }
    }
    return finalBoard;
}


FastClearBoolArray<MAX_CAT> fillUpBlockedCat;

vector<vector<int>> fillUp(const Task& task, vector<vector<int>> board) {
    fillUpBlockedCat.clear();
    for (int i = 0; i < task.h; i++) {
        for (int id: board[i]) {
            if (id != -1) {
                fillUpBlockedCat.setBit(task.getCat(id));
            }
        }
    }
    vector<vector<Item>> itemByCat(task.nCat);
    for (auto item: task.items) {
        itemByCat[item.cat].push_back(item);
    }
    vector<pair<int, vector<Item>>> eligibleCat;
    vector<BrandDP> dp;

    for (int i = 0; i < task.nCat; i++) {
        if (!fillUpBlockedCat.getBit(i) && !itemByCat[i].empty()) {
            dp.emplace_back(itemByCat[i], task.w);
        }
    }
    sort(all(eligibleCat), [](const pair<int, vector<Item>>& A, const pair<int, vector<Item>>& B) {
        return A.second.size() > B.second.size();
    });
    struct Hole {
        int rowId, L, R;
        bool operator<(Hole other) const {
            if (len() != other.len()) {
                return len() > other.len();
            }
            if (rowId != other.rowId) {
                return rowId < other.rowId;
            }
            return L < other.L;
        }
        int len() const { return R - L; }
    };
    set<Hole> holes;
    for (int i = 0; i < task.h; i++) {
        for (int j = 0; j < task.w;) {
            for (; j < task.w && board[i][j] != -1; j++)
                ;
            if (j == task.w) {
                break;
            }
            int st = j;
            for (; j < task.w && board[i][j] == -1; j++)
                ;
            holes.insert({i, st, j});
        }
    }
    while (!holes.empty() && !dp.empty()) {
        Hole curHole = *holes.begin();
        assert(curHole.len() > 0);
        holes.erase(holes.begin());
        int fullHoleId = -1;
        double fullHoleScore = 0;
        for (int i = 0; i < (int)dp.size(); i++) {
            int realSize = min(curHole.len(), (int)dp[i].items.size());
            if (fullHoleScore < dp[i].getScore(realSize)) {
                fullHoleScore = dp[i].getScore(realSize);
                fullHoleId = i;
            }
        }
        assert(fullHoleId != -1);
        int realSize = min(curHole.len(), (int)dp[fullHoleId].items.size());
        vector<Item> pathItem = dp[fullHoleId].getPath(realSize);
        vector<int> path;
        for (auto x: pathItem) {
            path.push_back(x.id);
        }
        for (int i = 0; i < (int)path.size(); i++) {
            board[curHole.rowId][curHole.L + i] = path[i];
        }
        if (realSize < curHole.len()) {
            holes.insert({curHole.rowId, curHole.L + realSize, curHole.R});
        }
        dp.erase(dp.begin() + fullHoleId);
    }
    return board;
}

bool isRect(const vector<pair<int, int>>& pos) {
    assert(!pos.empty());
    int mnX = INF;
    int mnY = INF;
    int mxX = -1;
    int mxY = -1;
    for (auto A: pos) {
        mnX = min(mnX, A.first);
        mnY = min(mnY, A.second);
        mxX = max(mxX, A.first);
        mxY = max(mxY, A.second);
    }
    int area = (mxX - mnX + 1) * (mxY - mnY + 1);
    assert(area >= (int)pos.size());
    return area == (int)pos.size();
}

set<int> getUsedFromBoard(const vector<vector<int>>& board) {
    set<int> ret;
    for (const auto& row: board) {
        for (int id: row) {
            if (id != -1) {
                ret.insert(id);
            }
        }
    }
    return ret;
}

vector<vector<int>> fixCategoryBalance(const Task& task, vector<vector<int>> board) {
    struct CostRemove {
        int x, y;
        double cost;
    };
    auto initBoard = board;
    Score initScore = computeScore(task, initBoard);
    bool change = true;
    vector<vector<bool>> changedToday(task.h, vector<bool>(task.w, false));
    while (change) {
        change = false;
        auto maxBox = computeMaxBox(task, board);
        vector<Item> bestNonUsedCat(task.nCat, {-1, -1, -1, -1});
        set<int> usedInBoard = getUsedFromBoard(board);
        for (auto item: task.items) {
            if (usedInBoard.count(item.id) == 0) {
                if (bestNonUsedCat[item.cat].c < item.c) {
                    bestNonUsedCat[item.cat] = item;
                }
            }
        }
        vector<vector<pair<int, int>>> categoryPositions(task.nCat);
        for (int i = 0; i < task.h; i++) {
            for (int j = 0; j < task.w; j++) {
                int id = board[i][j];
                if (id != -1) {
                    categoryPositions[task.items[id].cat].push_back({i, j});
                }
            }
        }
        vector<CostRemove> toRemove;
        for (int i = 0; i < task.h; i++) {
            for (int j = 0; j < task.w; j++) {
                if (changedToday[i][j]) {
                    continue;
                }
                if (board[i][j] == -1) {
                    toRemove.push_back({i, j, 0});
                } else {
                    int curCat = task.items[board[i][j]].cat;
                    int cntCat = 0;
                    for (int tt = 0; tt < 4; tt++) {
                        int x = dx[tt] + i;
                        int y = dy[tt] + j;
                        if (0 <= x && x < task.h && 0 <= y && y < task.w && board[x][y] != -1) {
                            cntCat += task.items[board[x][y]].cat == curCat;
                        }
                    }
                    if (cntCat <= 1) {
                        double cost = brandF(maxBox[i][j]) * task.items[board[i][j]].c;
                        cost += task.catUplift((int)categoryPositions[task.items[board[i][j]].cat].size() - 1);
                        toRemove.push_back({i, j, cost});
                    }
                }
            }
        }
        sort(all(toRemove), [](const CostRemove& A, const CostRemove& B) { return A.cost < B.cost; });
        vector<bool> blockedCategory(task.nCat, false);
        for (CostRemove removeCand: toRemove) {
            int remCat = task.getCat(board[removeCand.x][removeCand.y]);
            if (remCat != -1 && blockedCategory[remCat]) {
                continue;
            }
            double maxUp = 0;
            int maxUpId = -1;
            int removeCat = (board[removeCand.x][removeCand.y] == -1)
                ? -1
                : task.items[board[removeCand.x][removeCand.y]].cat;
            for (int i = 0; i < task.nCat; i++) {
                if (removeCat == i || bestNonUsedCat[i].id == -1) {
                    continue;
                }
                auto catPos = categoryPositions[i];
                catPos.emplace_back(removeCand.x, removeCand.y);
                if (isRect(catPos)) {
                    double costUp = task.catUplift(categoryPositions[i].size()) + bestNonUsedCat[i].c;
                    if (costUp > maxUp) {
                        maxUp = costUp;
                        maxUpId = i;
                    }
                }
            }
            if (maxUp - removeCand.cost > 1000) {
                blockedCategory[task.getCat(bestNonUsedCat[maxUpId].id)] = true;
                board[removeCand.x][removeCand.y] = bestNonUsedCat[maxUpId].id;
                changedToday[removeCand.x][removeCand.y] = true;
                bestNonUsedCat[maxUpId].id = -1;
                if (removeCat != -1) {
                    bestNonUsedCat[removeCat].id = -1;
                }
                change = true;
            }
        }
    }
    Score finalScore = computeScore(task, board);
    if (initScore.sum > finalScore.sum) {
        return initBoard;
    }
    return board;
}

void testMetrics() {
    int h = 4;
    int w = 4;
    int n = 9;
    int nCat = 3;
    int nBrand = 3;
    int D0 = 50;
    vector<Item> items(n);
    vector<int> t = {1, 1, 1, 1, 2, 2, 2, 3, 3};
    vector<int> b = {1, 1, 2, 3, 1, 1, 3, 2, 2};
    vector<int> c = {2, 3, 5, 10, 4, 3, 9, 6, 7};
    for (int i = 0; i < n; i++) {
        items[i] = {t[i] - 1, b[i] - 1, c[i], i};
    }
    Task task(n, nCat, nBrand, h, w, D0, items);

    vector<vector<int>> board = {
        {0, 5, 6, 7},
        {0, 1, 2, 0},
        {0, 4, 3, 8},
        {0, 0, 0, 9},
    };
    for (auto& row: board) {
        for (auto& x: row) {
            x--;
        }
    }
    auto res = computeScore(task, board);
    cerr << "expected 155.328:     computed score: " << res.sum;
}

struct CategNCols {
    int catId {-1};
    int h {0};
    int w {0};
};


struct BorderBrand {
    pt L {-1, -1}, R {-1, -1}; // [L, R)
    int len() const { return (L - R).lenInt(); }
    bool empty() const { return L == pt(-1, -1) && R == pt(-1, -1); }
    bool operator<(const BorderBrand& rhs) const { return len() < rhs.len(); }
};


vector<vector<Item>> fillSubboardSmart(vector<vector<Item>> board, vector<vector<Item>> itemsByBrand) {
    if (board.size() > board[0].size()) {
        return simBoard(fillSubboardSmart(simBoard(board), itemsByBrand));
    }
    struct Segment {
        int x {-1};
        int y {-1};
        int len {0};
    };
    vector<Segment> segments;
    for (size_t i = 0; i < board.size(); i++) {
        for (size_t j = 0; j < board[i].size();) {
            for (; j < board[i].size() && board[i][j].id != -1; j++)
                ;
            size_t st = j;
            if (st == board[i].size()) {
                break;
            }
            for (; j < board[i].size() && board[i][j].id == -1; j++)
                ;
            segments.push_back({(int)i, (int)st, (int)(j - st)});
        }
    }
    struct BrandCount {
        int brand {-1};
        int count {0};
        bool operator<(const BrandCount& rhs) const {
            return count > rhs.count || (count == rhs.count && brand < rhs.brand);
        }
    };
    set<BrandCount> brandCounts;
    for (int i = 0; i < (int)itemsByBrand.size(); i++) {
        if (!itemsByBrand[i].empty()) {
            brandCounts.insert({i, (int)itemsByBrand[i].size()});
        }
    }
    for (; !brandCounts.empty();) {
        auto brandCount = *brandCounts.begin();
        brandCounts.erase(brandCounts.begin());
        int bestId = -1;
        int bestScore = -1;
        for (int i = 0; i < (int)segments.size(); i++) {
            int candScore = (segments[i].len >= brandCount.count) ? 1000 - (segments[i].len - brandCount.count)
                                                                  : segments[i].len;
            if (candScore > bestScore) {
                bestScore = candScore;
                bestId = i;
            }
        }
        assert(bestId != -1);
        auto curSegment = segments[bestId];
        int go = min(curSegment.len, brandCount.count);
        for (int j = 0; j < go; j++) {
            assert(!itemsByBrand[brandCount.brand].empty());
            board[curSegment.x][curSegment.y + j] = itemsByBrand[brandCount.brand].back();
            itemsByBrand[brandCount.brand].pop_back();
        }
        segments.erase(segments.begin() + bestId);
        if (go < curSegment.len) {
            curSegment.len -= go;
            curSegment.y += go;
            segments.push_back(curSegment);
        }
        if (go < brandCount.count) {
            brandCount.count -= go;
            assert(brandCount.count == (int)itemsByBrand[brandCount.brand].size());
            assert(brandCounts.insert(brandCount).second);
        }
    }
    assert(brandCounts.empty() && segments.empty());
    return board;
}

void optimizeOneCategory(const Task& task, vector<vector<Item>>& board, int mnX, int mnY, int mxX, int mxY) {
    for (int i = mnX; i <= mxX; i++) {
        for (int j = mnY; j <= mxY; j++) {
            assert(board[i][j].cat == board[mnX][mnY].cat);
        }
    }

    auto check = [&](pt A) { return 0 <= A.x && A.x < task.h && 0 <= A.y && A.y < task.w; };
    auto checkCat = [&](pt A) { return mnX <= A.x && A.x <= mxX && mnY <= A.y && A.y <= mxY; };

    int catArea = (mxX - mnX + 1) * (mxY - mnY + 1);
    vector<pt> corn = {{mnX, mnY}, {mnX, mxY}, {mxX, mxY}, {mxX, mnY}};
    vector<pt> vv = {{0, 1}, {1, 0}, {0, -1}, {-1, 0}};
    vector<vector<Item>> itemsByBrand(task.nBrand);
    for (int i = mnX; i <= mxX; i++) {
        for (int j = mnY; j <= mxY; j++) {
            itemsByBrand[board[i][j].brand].push_back(board[i][j]);
            board[i][j] = Item();
        }
    }
    int dd = 0;
    for (int i = 0; i < task.nBrand; i++) {
        sort(all(itemsByBrand[i]), [](const Item& lhs, const Item& rhs) { return lhs.c < rhs.c; });
        dd += itemsByBrand[i].size();
    }
    assert(catArea == dd);

    vector<BorderBrand> borderBrand(task.nBrand);
    for (int i = 0; i < 4; i++) {
        pt A = corn[i];
        pt B = corn[(i + 1) % 4];
        if ((B - A).lenInt() > 0) {
            assert(vv[i] == (B - A).norm());
        }
        pt v = vv[i];
        pt AA = A + v.turn();
        if (!check(AA)) {
            continue;
        }
        int edgeLen = (B - A).lenInt();
        for (int j = 0; j < edgeLen;) {
            pt stp = AA + v * j;
            int segBrand = board[stp.x][stp.y].brand;
            for (; j < edgeLen && segBrand == board[(AA + v * j).x][(AA + v * j).y].brand; j++) {
            }
            if (segBrand != -1) {
                pt enp = AA + v * j;
                borderBrand[segBrand] = max(borderBrand[segBrand], {stp, enp});
            }
        }
    }

    struct BrandCount {
        int brand;
        int count;
    };
    vector<BrandCount> brandCount;
    for (int i = 0; i < task.nBrand; i++) {
        if (!itemsByBrand[i].empty()) {
            brandCount.push_back({i, (int)itemsByBrand[i].size()});
        }
    }
    shuffle(all(brandCount), rnd);
    for (const auto& bc: brandCount) {
        if (borderBrand[bc.brand].empty()) {
            continue;
        }
        int curBrand = bc.brand;

        int curX = 0, curY = 0;
        int segLen = borderBrand[curBrand].len();
        vector<bool> failed(segLen, 0);
        pt v = (borderBrand[curBrand].R - borderBrand[curBrand].L).norm();
        pt u = v.turn() * -1;
        pt A = borderBrand[curBrand].L + u;
        for (; !itemsByBrand[curBrand].empty();) {
            pt B = A + v * curX + u * curY;
            if (!checkCat(B)) {
                break;
            }
            if (!failed[curX]) {
                if (board[B.x][B.y].id == -1) {
                    board[B.x][B.y] = itemsByBrand[curBrand].back();
                    itemsByBrand[curBrand].pop_back();
                } else {
                    failed[curX] = true;
                }
            }
            curX++;
            if (curX == segLen) {
                curX = 0;
                curY++;
            }
        }
        if (!itemsByBrand[curBrand].empty()) {
            vector<pt> posCand;
            for (int i = mnX; i <= mxX; i++) {
                for (int j = mnY; j <= mxY; j++) {
                    if (board[i][j].id == -1) {
                        posCand.push_back({i, j});
                    }
                }
            }
            pt mid = A + v * (segLen / 2);
            sort(all(posCand), [&mid](pt lhs, pt rhs) { return (lhs - mid).l1() < (rhs - mid).l1(); });
            for (int cur = 0; !itemsByBrand[curBrand].empty(); cur++) {
                assert(cur < (int)posCand.size());
                pt G = posCand[cur];
                assert(board[G.x][G.y].id == -1);
                assert(checkCat(G));
                board[G.x][G.y] = itemsByBrand[curBrand].back();
                assert(board[G.x][G.y].id != -1);
                itemsByBrand[curBrand].pop_back();
            }
        }
    }
    vector<vector<Item>> subboard(mxX - mnX + 1);
    for (int i = mnX; i <= mxX; i++) {
        subboard[i - mnX] = vector<Item>(board[i].begin() + mnY, board[i].begin() + mxY + 1);
    }
    subboard = fillSubboardSmart(subboard, itemsByBrand);
    copyBoard2D(board, subboard, mnX, mnY);
}


vector<CategNCols> solveOptimalInit(const Task& task, const vector<int>& catCount,
                                    const vector<vector<double>>& catScores) {
    assert((int)catScores.size() == task.nCat);
    vector<vector<double>> dp(task.nCat + 1, vector<double>(task.w + 1, -INF));
    dp[0][0] = 0;
    vector<vector<int>> par(task.nCat + 1, vector<int>(task.w + 1, -1));
    for (int catId = 0; catId < task.nCat; catId++) {
        int cntColTry = catCount[catId] / task.h + 3;
        cntColTry = min(task.w, min(cntColTry, catCount[catId]));
        for (int go = 0; go <= cntColTry; go++) {
            int nh = (go == 0) ? 0 : catCount[catId] / go;
            assert(go == 0 || nh >= 1);
            nh = min(nh, task.h);
            int useItems = nh * go;
            assert(useItems <= catCount[catId]);
            double profit = catScores[catId][useItems];
            profit += task.realD * sqrt(useItems);
            for (int j = 0; j + go <= task.w; j++) {
                if (dp[catId + 1][j + go] < dp[catId][j] + profit) {
                    dp[catId + 1][j + go] = dp[catId][j] + profit;
                    par[catId + 1][j + go] = go;
                }
            }
        }
    }
    double bestScore = -1;
    int bestWhere = -1;
    for (int i = 0; i <= task.w; i++) {
        if (dp[task.nCat][i] > bestScore) {
            bestScore = dp[task.nCat][i];
            bestWhere = i;
        }
    }
    assert(bestWhere != -1);
    vector<CategNCols> ret;
    for (int i = task.nCat; i > 0; i--) {
        int nw = par[i][bestWhere];
        assert(nw != -1);
        if (nw > 0) {
            bestWhere -= nw;
            int nh = catCount[i - 1] / nw;
            assert(nh >= 1);
            nh = min(nh, task.h);
            ret.push_back({i - 1, nh, nw});
        }
    }
    return ret;
}

struct CatSize {
    int h {0};
    int w {0};
    int mult() const { return h * w; }
};


pair<vector<CatSize>, vector<int>> initialCatSizeDP(const Task& task, const vector<BrandDP>& fullDP) {
    vector<vector<double>> catScores(task.nCat);
    vector<int> catCount(task.nCat);
    for (const auto& item: task.items) {
        catCount[item.cat]++;
    }

    for (int i = 0; i < task.nCat; i++) {
        if (catCount[i] != 0) {
            assert(min(task.h * task.w, catCount[i]) + 1 == (int)fullDP[i].dp.back().size());
            catScores[i] = fullDP[i].dp.back();
        } else {
            catScores[i] = {0};
        }
    }
    auto ret = solveOptimalInit(task, catCount, catScores);
    vector<CatSize> catSize(task.nCat);
    for (auto x: ret) {
        catSize[x.catId] = {x.h, x.w};
    }
    return {catSize, catCount};
}

vector<Item> apoCatId[MAX_CAT][MAX_BRAND];
int fastClear2d[MAX_CAT][MAX_BRAND];
int fcCur2d = 0;

void applyBrandOrder(const Task& task, vector<vector<Item>>& board, const vector<int>& brandOrder, int catId,
                     CatSize catSize, int shift, int snakeBit) {
    assert(catSize.w != 0);

    int curBrand1 = 0;
    int curBrand2 = 0;
    auto getNext = [&]() {
        for (;;) {
            assert(curBrand1 < (int)brandOrder.size());
            int bb = brandOrder[curBrand1];
            if (curBrand2 < (int)apoCatId[catId][bb].size()) {
                return apoCatId[catId][bb][curBrand2++];
            } else {
                curBrand2 = 0;
                curBrand1++;
            }
        }
    };

    assert(snakeBit == 0 || snakeBit == 1);
    for (int i = 0; i < catSize.h; i++) {
        if ((i + snakeBit) % 2 == 0) {
            for (int j = 0; j < catSize.w; j++) {
                board[i][j + shift] = getNext();
            }
        } else {
            for (int j = catSize.w - 1; j >= 0; j--) {
                board[i][j + shift] = getNext();
            }
        }
    }
    for (int i = catSize.h; i < task.h; i++) {
        for (int j = 0; j < catSize.w; j++) {
            board[i][j + shift] = Item();
        }
    }
}


vector<Edge> buildBaseGraph(const Task& task, const vector<CatSize>& catSize, const vector<BrandDP>& fullDp,
                            vector<vector<Item>>& catIds) {
    vector<vector<double>> newCB(task.nCat, vector<double>(task.nBrand));
    for (int i = 0; i < task.nCat; i++) {
        if (catSize[i].w > 0) {
            assert((int)task.itemsByCat[i].size() >= catSize[i].w * catSize[i].h);
            if (catIds[i].empty()) {
                catIds[i] = fullDp[i].getPath(catSize[i].w * catSize[i].h);
            }
            assert((int)catIds[i].size() == catSize[i].w * catSize[i].h);
            for (const Item& item: catIds[i]) {
                newCB[i][item.brand]++;
            }
        }
        newCB[i] = normArray(newCB[i]);
    }
    vector<Edge> edges;
    for (int i = 0; i < task.nCat; i++) {
        for (int j = i + 1; j < task.nCat; j++) {
            if (catSize[i].w == 0 || catSize[j].w == 0) {
                continue;
            }
            double totalUp = 0;
            for (int t = 0; t < task.nBrand; t++) {
                totalUp += min(newCB[i][t], newCB[j][t]);
            }
            if (ls(0, totalUp)) {
                totalUp += randDouble(0, 0.15);
            }
            edges.push_back({i, j, totalUp});
        }
    }
    sort(all(edges), [](const Edge& A, const Edge& B) { return A.cost > B.cost; });
    return edges;
}

template <typename T> T getWithWeights(const vector<T>& a, vector<double> weights) {
    assert(!a.empty());
    if (weights.size() > a.size()) {
        weights.resize(a.size());
    }
    double sum = accumulate(all(weights), 0);
    for (auto& x: weights) {
        x /= sum;
    }
    double p = randDouble(0, 1);
    for (size_t i = 0; i < weights.size(); i++) {
        if (p > weights[i]) {
            p -= weights[i];
        } else {
            return a[i];
        }
    }
    assert(false);
}


vector<int> getOrder(const Task& task, const vector<Edge>& edges, const vector<CatSize>& catSize) {
    vector<vector<int>> e(task.nCat);
    DSU dsu(task.nCat);
    for (auto edge: edges) {
        if (dsu.getId(edge.v) == dsu.getId(edge.u)) {
            continue;
        }
        if (e[edge.v].size() >= 2 || e[edge.u].size() >= 2) {
            continue;
        }
        dsu.merge(edge.v, edge.u);
        e[edge.v].push_back(edge.u);
        e[edge.u].push_back(edge.v);
    }
    vector<int> ends;

    for (int i = 0; i < task.nCat; i++) {
        if (catSize[i].w > 0) {
            assert(e[i].size() == 1 || e[i].size() == 2 || e[i].empty());
            if (e[i].size() < 2) {
                ends.push_back(i);
            }
            if (e[i].size() == 0) {
                ends.push_back(i);
            }
        }
    }
    assert(ends.size() == 2);
    vector<int> catOrder;
    int v = ends[0];
    int prev = -1;
    for (;;) {
        catOrder.push_back(v);
        int go = -1;
        for (auto u: e[v]) {
            if (u != prev) {
                assert(go == -1);
                go = u;
            }
        }
        if (go == -1) {
            break;
        }
        prev = v;
        v = go;
    }
    return catOrder;
}

map<int, double> getCatRelProfit(const Task& task, const vector<vector<Item>>& board, const vector<vector<int>>& maxBox,
                                 const vector<CatSize>& catSize) { // profit for one column
    vector<double> catProfit(task.nCat);
    vector<int> itemsInCat(task.nCat);
    for (size_t i = 0; i < board.size(); i++) {
        for (size_t j = 0; j < board[i].size(); j++) {
            Item item = board[i][j];
            if (item.id != -1) {
                catProfit[item.cat] += item.c * brandF(maxBox[i][j]);
                itemsInCat[item.cat]++;
            }
        }
    }
    map<int, double> ret;
    for (int catId = 0; catId < task.nCat; catId++) {
        if (catSize[catId].w > 0) {
            double profit = catProfit[catId];
            profit += sqrt(itemsInCat[catId]) * task.realD;
            ret[catId] = profit / catSize[catId].w;
        }
    }
    return ret;
}

vector<int> globalInsert;
vector<int> globalUse;
map<vector<int>, Board> hashMaster;


void recomputeCatSizeH(const Task& task, vector<CatSize>& catSize, const vector<int>& catCount) {
    for (int i = 0; i < (int)catCount.size(); i++) {
        if (catSize[i].w == 0) {
            catSize[i].h = 0;
        } else {
            catSize[i].h = min(task.h, catCount[i] / catSize[i].w);
        }
    }
}

int sumCatSize(const vector<CatSize>& catSize) {
    int ss = 0;
    for (auto x: catSize) {
        ss += x.w;
    }
    return ss;
}

Board solveV5NoRec(const Task& task) {
    if (task.items.size() == 0) {
        return task.emptyBoardBoard();
    }
    const vector<int> taskHash = task.toArray();

    vector<BrandDP> fullDp(task.nCat);
    for (int i = 0; i < task.nCat; i++) {
        fullDp[i] = BrandDP(task.itemsByCat[i], task.h * task.w);
    }
    auto [catSize, catCount] = initialCatSizeDP(task, fullDp);
    assert(sumCatSize(catSize) != 0);
    Board bestBoard = task.emptyBoardBoard();

    vector<vector<Item>> catIds;
    catIds.assign(task.nCat, vector<Item>());
    for (int ff = 0; ff < 3; ff++) {
        catIds.assign(task.nCat, vector<Item>());
        auto edges = buildBaseGraph(task, catSize, fullDp, catIds);
        auto catOrder = getOrder(task, edges, catSize);

        fcCur2d++;
        for (int catId = 0; catId < task.nCat; catId++) {
            for (const Item& item: catIds[catId]) {
                if (fastClear2d[catId][item.brand] != fcCur2d) {
                    fastClear2d[catId][item.brand] = fcCur2d;
                    apoCatId[catId][item.brand].clear();
                }
                apoCatId[catId][item.brand].push_back(item);
            }
        }

        if (randInt(0, 1) == 0) {
            reverse(all(catOrder));
        }
        int shift = 0;
        auto board = task.emptyBoardNew();
        for (int catId: catOrder) {
            assert(!task.brandLeft.empty());
            vector<int> prevBrand(task.h, -1);
            prevBrand = task.brandLeft;
            if (shift != 0) {
                for (int i = 0; i < task.h; i++) {
                    prevBrand[i] = board[i][shift - 1].brand;
                }
            }
            vector<int> curBrands;
            for (auto id: catIds[catId]) {
                assert(id.cat == catId);
                curBrands.push_back(id.brand);
            }
            sort(all(curBrands));
            curBrands.erase(unique(all(curBrands)), curBrands.end());

            vector<int> bestOrder;
            int bestBit = 0;
            int bestScore = -1;
            for (int tt = 0; tt < 120; tt++) {
                shuffle(all(curBrands), rnd);
                int curBit = randInt(0, 1);
                applyBrandOrder(task, board, curBrands, catId, catSize[catId], shift, curBit);
                int cntMatch = 0;
                for (int i = 0; i < task.h; i++) {
                    cntMatch += prevBrand[i] == board[i][shift].brand;
                }
                assert(!task.brandUp.empty());
                assert((int)task.brandUp.size() == task.w);
                for (int j = 0; j < catSize[catId].w; j++) {
                    cntMatch += task.brandUp[shift + j] == board[0][j].brand;
                }

                assert(!task.brandDown.empty());
                assert((int)task.brandDown.size() == task.w);
                assert((int)board.size() == task.h);
                for (int j = 0; j < catSize[catId].w; j++) {
                    cntMatch += task.brandDown[shift + j] == board[task.h - 1][j].brand;
                }
                assert(!task.brandRight.empty());
                if (shift + catSize[catId].w == task.w) {
                    assert((int)task.brandRight.size() == task.h);
                    for (int j = 0; j < task.h; j++) {
                        cntMatch += task.brandRight[j] == board[j].back().brand;
                    }
                }
                if (cntMatch > bestScore) {
                    bestScore = cntMatch;
                    bestOrder = curBrands;
                    bestBit = curBit;
                }
            }
            applyBrandOrder(task, board, bestOrder, catId, catSize[catId], shift, bestBit);
            shift += catSize[catId].w;
        }
        auto maxBox = computeMaxBox(task, toRowId(board));

        //        vector<vector<double>> averageF = getAverageF(task, board, maxBox);
        //        getAverageF(task, board, maxBox);
        map<int, double> catRelProfit = getCatRelProfit(task, board, maxBox, catSize);
        auto score = computeScore(task, board, &maxBox);
        Board bBoard(board, score);
        bestBoard = max(bestBoard, bBoard);
        struct ScoreCat {
            double score {0};
            int catId {-1};
        };

        vector<ScoreCat> addCatCand;
        vector<ScoreCat> remCatCand;
        vector<int> notUsedCat;
        for (int i = 0; i < task.nCat; i++) {
            if (catSize[i].w == 0 && catCount[i] > 0) {
                notUsedCat.push_back(i);
            }
            if (catSize[i].w > 0) {
                remCatCand.push_back({catRelProfit[i], i});
                if (catCount[i] >= (catSize[i].w + 1) * task.h) {
                    assert(catRelProfit.count(i));
                    addCatCand.push_back({catRelProfit[i], i});
                }
            }
        }
        sort(all(addCatCand), [](ScoreCat A, ScoreCat B) { return A.score > B.score; });
        sort(all(remCatCand), [](ScoreCat A, ScoreCat B) { return A.score < B.score; });
        shuffle(all(notUsedCat), rnd);
        assert(!remCatCand.empty());
        if (!notUsedCat.empty() || !addCatCand.empty()) {
            int remId = getWithWeights(remCatCand, {5.0, 1.0}).catId;
            int addId = -1;
            if (addCatCand.empty() || (randDouble(0, 1) < 0.2 && !notUsedCat.empty())) {
                addId = notUsedCat[0];
            } else {
                addId = getWithWeights(addCatCand, {5.0, 1.0}).catId;
            }
            if (ff >= 3) { // TODO remove it
                catSize[remId].w--;
                catSize[addId].w++;
            }
        } else {
            break;
        }
        recomputeCatSizeH(task, catSize, catCount);
    }
    globalInsert.back()++;
    bestBoard.rects.push_back({0, 0, task.h, task.w});
    return bestBoard;
}

vector<Item> subtractBoard(const Task& task, const Board& board) {
    vector<int> usedCat(task.nCat, 0);
    for (const auto& row: board.board) {
        for (const auto& item: row) {
            if (item.cat != -1) {
                usedCat[item.cat] = 1;
            }
        }
    }
    vector<Item> ret;
    for (const auto& item: task.items) {
        if (usedCat[item.cat] == 0) {
            ret.push_back(item);
        }
    }
    return ret;
}


Board solveV5WithRec(const Task& task);

struct CountCat {
    int count;
    int catId;
};

set<int> splitDp(vector<CountCat> tmp, const map<int, vector<int>>& clusterMembers, double p) {
    int sumTmp = 0;
    for (auto x: tmp) {
        sumTmp += x.count;
    }
    vector<vector<bool>> dp(tmp.size() + 1, vector<bool>(sumTmp + 1));
    vector<vector<int>> par(tmp.size() + 1, vector<int>(sumTmp + 1, -1));
    dp[0][0] = true;
    for (int i = 0; i < (int)tmp.size(); i++) {
        for (int j = 0; j <= sumTmp; j++) {
            if (dp[i][j]) {
                dp[i + 1][j] = true;
                par[i + 1][j] = 0;
                int nj = j + tmp[i].count;
                assert(tmp[i].count > 0);
                if (nj <= sumTmp) {
                    dp[i + 1][nj] = true;
                    par[i + 1][nj] = tmp[i].count;
                }
            }
        }
    }
    double bestScore = INF;
    int bestWhere = -1;
    for (int i = 0; i <= sumTmp; i++) {
        if (dp[tmp.size()][i] && abs(i - sumTmp * p) < bestScore) {
            bestScore = abs(i - sumTmp * p);
            bestWhere = i;
        }
    }
    assert(bestWhere != -1);
    set<int> g1Cat;
    for (int i = tmp.size(); i > 0; i--) {
        assert(dp[i][bestWhere]);
        if (par[i][bestWhere] != 0) {
            bestWhere -= par[i][bestWhere];
            int clusterId = tmp[i - 1].catId;
            auto members = clusterMembers.at(clusterId);
            //            assert(members.size() == 1);
            g1Cat.insert(all(members));
        }
    }
    return g1Cat;
}

set<int> splitGreedy(vector<CountCat> tmp, const map<int, vector<int>>& clusterMembers, int cntCall, double p) {
    int nSwap = 0;
    if (cntCall >= 2)
        nSwap = tmp.size() / 2;
    if (cntCall >= 5)
        nSwap = tmp.size();
    if (cntCall >= 10)
        nSwap = tmp.size() * 2;

    sort(all(tmp), [](CountCat A, CountCat B) { return A.count > B.count; });

    if (tmp.size() >= 2) {
        for (int i = 0; i < nSwap; i++) {
            int pos = randInt(0, (int)tmp.size() - 2);
            swap(tmp[pos], tmp[pos + 1]);
        }
    }

    int group1 = 0;
    int group2 = 0;
    set<int> g1Cat;
    for (auto x: tmp) {
        if (group1 * 1.0 / (group1 + group2) < p) {
            group1 += x.count;
            auto members = clusterMembers.at(x.catId);
            g1Cat.insert(all(members));
        } else {
            group2 += x.count;
        }
    }
    return g1Cat;
}

vector<int> averageDiff;

pair<vector<Item>, vector<Item>> splitItems(const Task& task, int A, int B) {
    auto taskHash = task.toArray();
    taskHash.push_back(A);
    taskHash.push_back(B);
    double p = A * 1.0 / B;
    assert(0 < p && p < 1);

    vector<CountCat> tmpBase;
    for (int i = 0; i < task.nCat; i++) {
        if (!task.itemsByCat[i].empty()) {
            tmpBase.push_back({(int)task.itemsByCat[i].size(), i});
        }
    }
    int mergeCat = tmpBase.size() / 2;
    mergeCat = 0;
    if (tmpBase.size() >= 5) {
        double pp = randDouble(0.2, 0.5);
        mergeCat = tmpBase.size() * pp;

        mergeCat = max(mergeCat, (int)tmpBase.size() - 12);
    }
    vector<Edge> edges = task.categoryEdges();
    DSU dsu(task.nCat);
    for (size_t tt = 0; tt < edges.size() && mergeCat > 0; tt++) {
        auto edge = edges[tt];
        int v = dsu.getId(edge.v);
        int u = dsu.getId(edge.u);
        if (v != u) {
            dsu.merge(v, u);
            mergeCat--;
        }
    }
    map<int, int> clusterSize;
    map<int, vector<int>> clusterMembers;
    for (int i = 0; i < task.nCat; i++) {
        if (!task.itemsByCat[i].empty()) {
            int rootId = dsu.getId(i);
            clusterSize[rootId] += task.itemsByCat[i].size();
            clusterMembers[rootId].push_back(i);
        }
    }
    vector<CountCat> tmp;
    for (int i = 0; i < task.nCat; i++) {
        if (!task.itemsByCat[i].empty()) {
            if (dsu.getId(i) == i) {
                tmp.push_back({clusterSize.at(i), i});
            }
        }
    }
    auto g1Cat = splitDp(tmp, clusterMembers, p);

    vector<Item> items1;
    vector<Item> items2;
    for (auto item: task.items) {
        if (g1Cat.count(item.cat)) {
            items1.push_back(item);
        } else {
            items2.push_back(item);
        }
    }
    return {items1, items2};
}

vector<int> vseg(const vector<int>& v, int l, int r) {
    assert(0 <= l && l <= r && r <= (int)v.size());
    return vector<int>(v.begin() + l, v.begin() + r);
}

Board splitStrategyV2(const Task& task) {
    auto bestBoard = task.emptyBoardBoard();

    if (randInt(0, 1) == 0) {
        if (task.h >= 2) { /// horizontal split
            int hUp = randInt(1, task.h - 1);
            int hDown = task.h - hUp;
            auto [itemsUp, itemsDown] = splitItems(task, hUp, task.h);
            Task taskUp(task.n, task.nCat, task.nBrand, hUp, task.w, task.D0, itemsUp);
            taskUp.brandUp = task.brandUp;
            taskUp.brandLeft = vseg(task.brandLeft, 0, hUp);
            taskUp.brandRight = vseg(task.brandRight, 0, hUp);
            auto boardUp = solveV5WithRec(taskUp); ///////////// main call


            Task taskDown(task.n, task.nCat, task.nBrand, hDown, task.w, task.D0, itemsDown);
            taskDown.brandUp.resize(task.w);
            for (int i = 0; i < task.w; i++) {
                taskDown.brandUp[i] = boardUp.board.back()[i].brand;
            }
            taskDown.brandDown = task.brandDown;
            taskDown.brandLeft = vseg(task.brandLeft, hUp, task.h);
            taskDown.brandRight = vseg(task.brandRight, hUp, task.h);
            auto boardDown = solveV5WithRec(taskDown); //////////// main call

            auto curBoard = task.emptyBoardNew();
            copyBoard2D(curBoard, boardUp.board, 0, 0);
            copyBoard2D(curBoard, boardDown.board, hUp, 0);
            Score curScore = computeScore(task, curBoard);
            Board tmpBoard(curBoard, curScore);
            tmpBoard.addRects(boardUp.rects, 0, 0);
            tmpBoard.addRects(boardDown.rects, hUp, 0);
            bestBoard = max(tmpBoard, bestBoard);
        }
    } else {
        if (task.w >= 2) { // vertical split
            int wLeft = randInt(1, task.w - 1);
            int wRight = task.w - wLeft;
            auto [itemsLeft, itemsRight] = splitItems(task, wLeft, task.w);
            Task taskLeft(task.n, task.nCat, task.nBrand, task.h, wLeft, task.D0, itemsLeft);
            taskLeft.brandLeft = task.brandLeft;
            taskLeft.brandUp = vseg(task.brandUp, 0, wLeft);
            taskLeft.brandDown = vseg(task.brandDown, 0, wLeft);
            auto boardLeft = solveV5WithRec(taskLeft); ///////// main call

            Task taskRight(task.n, task.nCat, task.nBrand, task.h, wRight, task.D0, itemsRight);
            taskRight.brandLeft.resize(task.h);
            for (int i = 0; i < task.h; i++) {
                taskRight.brandLeft[i] = boardLeft.board[i].back().brand;
            }
            taskRight.brandRight = task.brandRight;
            taskRight.brandUp = vseg(task.brandUp, wLeft, task.w);
            taskRight.brandDown = vseg(task.brandDown, wLeft, task.w);
            auto boardRight = solveV5WithRec(taskRight); ////////// main call

            auto curBoard = task.emptyBoardNew();
            copyBoard2D(curBoard, boardLeft.board, 0, 0);
            copyBoard2D(curBoard, boardRight.board, 0, wLeft);
            Score curScore = computeScore(task, curBoard);
            Board tmpBoard(curBoard, curScore);
            tmpBoard.addRects(boardLeft.rects, 0, 0);
            tmpBoard.addRects(boardRight.rects, 0, wLeft);
            bestBoard = max(tmpBoard, bestBoard);
        }
    }
    return bestBoard;
}

Board solveV5WithRec(const Task& task) {
    assert(task.h == (int)task.brandLeft.size() && task.h == (int)task.brandRight.size());
    assert(task.w == (int)task.brandUp.size() && task.w == (int)task.brandDown.size());
    int cc = 0;
    for (int i = 0; i < task.nCat; i++) {
        cc += task.itemsByCat[i].size();
    }
    assert(cc == (int)task.items.size());
    if (task.items.empty()) {
        return task.emptyBoardBoard();
    }
    if (task.h > task.w) {
        Task taskSwap = task;
        swap(taskSwap.h, taskSwap.w);
        taskSwap.brandUp = task.brandLeft;
        taskSwap.brandLeft = task.brandUp;
        taskSwap.brandRight = task.brandDown;
        taskSwap.brandDown = task.brandRight;

        auto ret = solveV5WithRec(taskSwap);
        ret.board = simBoard(ret.board);
        return ret;
    }

    auto bestBoard = solveV5NoRec(task);
    if (task.nUniqueCat() >= 2) {
        auto recBoard = splitStrategyV2(task);
        bestBoard = max(bestBoard, recBoard);
    }
    return bestBoard;
}


bool debugTaskV5Rect = false;
int cntImprove = 0;
int cntFailToImprove = 0;


vector<vector<Item>> fillSubboardGreedy(vector<vector<Item>> board, vector<vector<Item>> itemsByBrand) {
    if (board.size() > board[0].size()) {
        return simBoard(fillSubboardGreedy(simBoard(board), itemsByBrand));
    }
    vector<Item> greedyOrder;
    for (int i = 0; i < (int)itemsByBrand.size(); i++) {
        for (auto item: itemsByBrand[i]) {
            greedyOrder.push_back(item);
        }
    }
    for (int i = 0; i < (int)board.size(); i++) {
        for (int j = 0; j < (int)board[i].size(); j++) {
            if (board[i][j].id == -1) {
                assert(!greedyOrder.empty());
                board[i][j] = greedyOrder.back();
                greedyOrder.pop_back();
            }
        }
    }
    assert(greedyOrder.empty());
    return board;
}


Board postBrandOptimizing(const Task& task, const Board& inputBoard) {
    bool change = true;
    vector<int> mnX(task.nCat, INF);
    vector<int> mnY(task.nCat, INF);
    vector<int> mxX(task.nCat, -1);
    vector<int> mxY(task.nCat, -1);
    vector<int> cnt(task.nCat, 0);
    vector<vector<Item>> board = inputBoard.board;
    for (int i = 0; i < task.h; i++) {
        for (int j = 0; j < task.w; j++) {
            if (board[i][j].id != -1) {
                int catId = board[i][j].cat;
                mnX[catId] = min(mnX[catId], i);
                mnY[catId] = min(mnY[catId], j);
                mxX[catId] = max(mxX[catId], i);
                mxY[catId] = max(mxY[catId], j);
                cnt[catId]++;
            }
        }
    }
    for (int i = 0; i < task.nCat; i++) {
        if (cnt[i] > 0) {
            assert(cnt[i] == (mxX[i] - mnX[i] + 1) * (mxY[i] - mnY[i] + 1));
        }
    }


    Score bestScore = inputBoard.score;
    auto perm = randPerm(task.nCat);
    for (int tt = 0; change && tt < 5; tt++) {
        change = false;
        for (int catId: perm) {
            if (cnt[catId] == 0) {
                continue;
            }
            auto saveBoard = board;
            optimizeOneCategory(task, board, mnX[catId], mnY[catId], mxX[catId], mxY[catId]);

            Score improveCand = computeScore(task, board);
            if (improveCand.sum > bestScore.sum) {
                //                cerr << "Improvments: " << bestScore.sum << "  ->  " << improveCand.sum << endl;
                cntImprove++;
                change = true;
                bestScore = improveCand;
            } else {
                cntFailToImprove++;
                board = saveBoard;
            }
        }
    }
    auto justCheck = computeScore(task, board);
    assert(eq(bestScore.sum, justCheck.sum));
    return {board, bestScore};
}

vector<double> postProcessImp;

vector<vector<int>> solveV5(const Task& task, int overwriteCntIter = -1) {
    hashMaster.clear();
    globalUse.push_back(0);
    globalInsert.push_back(0);
    Board globalBest = task.emptyBoardBoard();
#ifdef HOME
    int cntIter = 20;
    bool brakeByTime = false;
#else
    int cntIter = 1000000;
    bool brakeByTime = true;
#endif
    if (overwriteCntIter != -1) {
        cntIter = overwriteCntIter;
    }
    for (int ii = 0; ii < cntIter; ii++) {
        if (brakeByTime && getTime() > 14.0) {
            break;
        }
        Board res = solveV5WithRec(task);
        Board optRes = postBrandOptimizing(task, res);
        postProcessImp.push_back(optRes.score.sum - res.score.sum);
        assert(le(res.score.sum, optRes.score.sum));
        res = max(res, optRes);
        globalBest = max(res, globalBest);
    }
    if (debugTaskV5Rect) {
        cerr << "*************** rects recipe ***************** " << endl;
        for (auto rect: globalBest.rects) {
            cerr << "x: " << rect.x << "   y: " << rect.y << "   h: " << rect.h << "   w: " << rect.w << endl;
        }
    }

    auto board = task.emptyBoard();
    for (int i = 0; i < task.h; i++) {
        for (int j = 0; j < task.w; j++) {
            board[i][j] = globalBest.board[i][j].id;
        }
    }
    return board;
}

vector<double> rndWeight(int cnt, int L, int R) {
    vector<double> a(cnt);
    for (int i = 0; i < cnt; i++) {
        a[i] = randInt(L, R);
    }
    return a;
}


int sampleWeight(const vector<double>& w) {
    double x = randDouble(0, 1);
    for (int i = 0; i < (int)w.size(); i++) {
        if (x > w[i]) {
            x -= w[i];
        } else {
            return i;
        }
    }
    assert(false);
}

Task generateTask(int _h = -1, int _w = -1, int _n = -1, int _nCat = -1, int _nBrand = -1, int _D0 = -1) {
    int h = (_h != -1) ? _h : randInt(1, 10);
    int w = (_w != -1) ? _w : randInt(1, 100);
    int n = (_n != -1) ? _n : int(h * w * randDouble(0.8, 1.8));
    int nCat = (_nCat != -1) ? _nCat : randInt(1, 50);
    int nBrand = (_nBrand != -1) ? _nBrand : randInt(1, 50);
    int D0 = (_D0 != -1) ? _D0 : randInt(1, 1000000); // fix it
    if (randInt(1, 2) == 1) {
        const int BOUND = 1000000;
        double D0Log = randDouble(7, log(BOUND));
        D0 = int(exp(D0Log));
        assert(1 <= D0 && D0 <= BOUND);
    }
    vector<double> p = normArray(rndWeight(nCat, 20, 100));
    vector<double> q = normArray(rndWeight(nBrand, 20, 100));
    vector<double> A = rndWeight(nCat, 100, 500);
    vector<double> B = rndWeight(nBrand, 100, 500);

    vector<set<int>> brandProd(nBrand);
    for (int i = 0; i < nBrand; i++) {
        int needCat = randInt(1, min(10, nCat));
        for (; (int)brandProd[i].size() < needCat;) {
            brandProd[i].insert(randInt(0, nCat - 1));
        }
    }

    vector<Item> items;
    for (; (int)items.size() < n;) {
        int curCat = sampleWeight(p);
        int curBrand = sampleWeight(q);
        if (brandProd[curBrand].count(curCat) == 0) {
            continue;
        }
        int curCost = round(randDouble(0.5, 1) * (A[curCat] + B[curBrand]));
        int id = items.size();
        items.push_back({curCat, curBrand, curCost, id});
    }
    Task task(n, nCat, nBrand, h, w, D0, items);
    return task;
}

Task generateSmallTask() {
    int h = randInt(1, 4);
    int w = randInt(1, 4);
    int n = randInt(1, 20);
    int nCat = randInt(1, 5);
    int nBrand = randInt(1, 5);
    int D0 = randInt(1, 10000);
    return generateTask(h, w, n, nCat, nBrand, D0);
}

template <typename T> double vMean(const vector<T>& a) {
    assert(!a.empty());
    double sum = 0;
    for (auto x: a)
        sum += x;
    return sum / a.size();
}

vector<vector<int>> maxBoard(vector<vector<int>> b1, vector<vector<int>> b2, const Task& task) {
    auto s1 = computeScore(task, b1);
    auto s2 = computeScore(task, b2);
    if (s1.sum > s2.sum) {
        return b1;
    }
    return b2;
}


void showSmall() {
    random_device rr;
    int initSeed = (ll)rr() % 1000;
    rnd.seed(initSeed);
    debugTaskV5Rect = true;
    Task task = generateTask(7, 20, -1, 5, 5);
    task.debug();
    auto board = solveV5(task, 1);
    Score score = computeScore(task, board, nullptr, true);
}


void submit() {
    random_device rd;
    rnd.seed(rd());
    Task task;
    task.read();
    auto board = solveV5(task);
    checkBoard(task, board);
    for (int i = 0; i < (int)board.size(); i++, cout << endl) {
        for (int j = 0; j < (int)board[i].size(); j++) {
            cout << board[i][j] + 1 << " ";
        }
    }
}

void stress(int curThreadId = -1, int cntIterOver = -1) {
    vector<Score> scores;
    double s1 = 0, s2 = 0;
    vector<double> cov;
    int cntExp = 30;
    if (cntIterOver != -1) {
        cntExp = cntIterOver;
    }
    double longestRun = 0;
    int longestSeed = -1;
    for (int i = 0; i < cntExp; i++) {
        int seedShift = (curThreadId == -1) ? 0 : curThreadId * 1000;
        rnd.seed(i + 40000000 + seedShift);
        cerr << "i: " << i << endl;
        Task task = generateTask();
        double st_time = getTime();
        auto board = solveV5(task);
        auto score = computeScore(task, board);
        double testTime = getTime() - st_time;
        if (testTime > longestRun) {
            longestRun = testTime;
            longestSeed = i;
        }
        scores.push_back(score);
        s1 += score.s1;
        s2 += score.s2;
        cov.push_back(score.cover);
    }
    double normCof = cntExp * 1e6;
    cerr << s1 / normCof << " " <<  s2 / normCof << "  total score: " << (s1 + s2) / normCof << endl;
    if (curThreadId != -1) {
        ofstream fout("outputs/t" + to_string(curThreadId) + ".txt");
        fout << (s1 + s2) / normCof << endl;
    }
    cerr << "time: " << clock() * 1.0 / CLOCKS_PER_SEC << endl;
}


int main(int argc, char** argv) {
#ifdef HOME
    assert(argc == 1 || argc == 3);
    int cntIter = -1;
    int curThreadId = -1;
    if (argc == 3) {
        curThreadId = stoi(string(argv[1]));
        cntIter = stoi(string(argv[2]));
    }
    if (curThreadId != -1) {
        stress(curThreadId, cntIter);
        return 0;
    }
    //    testMetrics();
    //    showSmall();
    stress();
#else
    submit();
#endif
    return 0;
}
