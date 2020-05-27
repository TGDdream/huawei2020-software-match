//#define TEST
#define _UNIX

#ifdef _UNIX
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <sys/mman.h>
#include <string.h>
#endif

#include <iostream>
#include <vector>
#include <fstream>
#include <map>
#include <set>
#include <string>
#include <algorithm>
#include <queue>
#include <mutex>
#include <thread>
#include <sstream>
#include <list>
#include <forward_list>
#include <unordered_map>
#include <unordered_set>
#include <chrono>
#include <stack>
#include <atomic>
#include <string.h>
using namespace std;
#define MAX_NUM 2000000
#define MAX_NODE 400000
#define THREAD_NUM 4

/* 自动义pair结构 */
/* 为了排序和==操作兼容之前的代码，重载<和==操作符 */
template<class T, class K> struct tmyPair {
	T first;
	K second;//若p2inv使用,1-2-3，保存2-3 金额
	int third;//p2inv使用,1-2-3，保存1-2 金额

	tmyPair(T a, K b)
	{
		first = a;
		second = b;
		third = 0;
	}
	tmyPair(T a, K b, int& rec)
	{
		first = a;
		second = b;
		third = rec;
	}
	bool operator<(const tmyPair<T, K>& rhs)const
	{
		if (this->first < rhs.first) return true;
		else return false;
	}
	bool operator<(const T& rhs)const
	{
		if (this->first < rhs) return true;
		else return false;
	}
	bool operator==(const tmyPair<T, K>& rhs)const
	{
		if (this->first == rhs.first) return true;
		else return false;
	}
	bool operator==(const T& rhs)const
	{
		if (this->first == rhs) return true;
		else return false;
	}
};

bool operator<(const int& a, const tmyPair<int, int>& b)
{
	if (a < b.first) return true;
	else return false;
}


typedef vector<vector<tmyPair<int, int>>> DirectedGraph;
DirectedGraph dg;
DirectedGraph rdg;  // 反向图，dg中所有边反转
					//ans_t answer;
vector<int> inputs; //u-v pairs
vector<int> amount;
int nodeCnt;
vector<string> idsComma; //0...n to sorted id
vector<string> idsLF; //0...n to sorted id
unordered_map<int, int> idHash; //sorted id to 0...n
vector<int> inDegrees;
vector<int> outDegrees;
vector<int> validNode;
int validCnt;

/* 线程数据编码记录数组 */
unsigned int threadFind[MAX_NODE];//3环到7环，记录线程号
unsigned int threadFindSz[5][MAX_NODE];//记录长度
									   //atomic_int dfsCnt = 0;

#define nId (dg[v][it].first)
struct HWCodeCraft {
	int path[9];
	int pathIte;
	int* ans3_7[5];
	int ansIte[5];
	int tid;

	//int dgvsize;
	size_t bag2size;
	int tmp;

	/* bag2 assist container */
	bool* assistBag2 = new bool[nodeCnt]();
	vector<int> keyBuf;

	/*lb_table*/
	int lb_table[MAX_NODE][2] = {};		//默认为0，不需要fill填充，0列表示上次查询的根节点，1列表示上次查询到的下标

	/*bag3_table*/
	int bag3_table[MAX_NODE] = {};		//代替bag3的结构，默认为0，当此处为根节点时，表明可以通过路径三回到根节点

	double coe;
	unsigned char blocked[MAX_NODE];
	//unordered_map<int, int> L1;//第一层的边
	int L1[MAX_NODE] = {};

	HWCodeCraft(int id) {
		keyBuf.reserve(200);
		tid = id;
		ans3_7[0] = new int[3 * 5000000];
		ans3_7[1] = new int[4 * 5000000];
		ans3_7[2] = new int[5 * 10000000];
		ans3_7[3] = new int[6 * 20000000];
		ans3_7[4] = new int[7 * 30000000];

		ansIte[0] = 0;
		ansIte[1] = 0;
		ansIte[2] = 0;
		ansIte[3] = 0;
		ansIte[4] = 0;
		pathIte = 0;
	}
	~HWCodeCraft() {
		for (int i = 0; i < 5; ++i)
		{
			delete[]ans3_7[i];
		}
		delete[]assistBag2;
	}

	// start_id和end_id是搜索节点范围，后面开多线程可以不同线程搜不同节点的圈
	void findCircuits()
	{
		auto t = clock();
		unordered_map<int, vector<tmyPair<int, int>>> bag2;

		//unsigned char* bag3 = new unsigned char[nodeCnt]();
		//unsigned char* zero = new unsigned char[nodeCnt]();
		int shift = 2 * tid + 1;//按01233210编码方式分配线程任务，0线程初始shift=1，1线程初始shift=3，2线程初始shift=5，3线程初始shift=7
								//for (int i = tid; i < nodeCnt; i+=shift)
		for (int i = tid; i < validCnt; i += shift)
		{
			shift = 2 * THREAD_NUM - shift;//按01233210编码方式分配线程任务
			threadFind[validNode[i]] = tid;
			preSearch(validNode[i], bag2);
			//search(0, i, i, bag2, bag3,-1);
			search(validNode[i], validNode[i], bag2, -1);
			bag2.clear();   // 清空了下一轮再用
			for (auto& a : keyBuf)
			{
				assistBag2[a] = false;
			}
			keyBuf.clear();
			//memcpy(bag3, zero, nodeCnt);
		}
		//delete[]bag3;
		//delete[]zero;
		//cout << "thread " << tid << " exit " << clock() - t << endl;
	}

	// 反向预搜索函数
	void preSearch(int s,   // 起始节点
		unordered_map<int, vector<tmyPair<int, int>>>& bag2)
	{
		// 找到s节点的所有子节点中id大于s的最小下标
		auto it = lower_bound(rdg[s].begin(), rdg[s].end(), s) - rdg[s].begin();

		for (; it < rdg[s].size(); ++it)
		{
			int v1 = rdg[s][it].first; // 反向第一层子节点id
									   // 找到v1节点的所有子节点中id大于s的最小下标
			auto ij = lower_bound(rdg[v1].begin(), rdg[v1].end(), s) - rdg[v1].begin();

			for (; ij < rdg[v1].size(); ++ij)
			{
				auto v2 = rdg[v1][ij].first;    // 反向第二层子节点id
				coe = (double)rdg[s][it].second / (double)rdg[v1][ij].second;
				if (coe >= 0.2 && coe <= 3.0)//满足权值条件
				{
					bag2[v2].emplace_back(tmyPair<int, int>(v1, rdg[v1][ij].second, rdg[s][it].second));//保存第二层结果以及权值边 V2-V1  V1-s
					assistBag2[v2] = true;
					keyBuf.push_back(v2);
					auto ik = lower_bound(rdg[v2].begin(), rdg[v2].end(), s);

					if (ik != rdg[v2].end())
					{
						auto rdgend = rdg[v2].end();
						for (; ik < rdgend; ik++)
						{
							// 把能到达s的第三层节点都塞bag3里
							//bag3.insert((*ik).first);
							//首先n3要不等于n1,n3不等于n0
							//if ((*ik).first == v1 || (*ik).first == s)
							//	continue;
							// 改为要先计算金额，才能存入bag3 计算 n2->n1 /n3->n2
							//coe = (double)rdg[v1][ij].second / (double)(*ik).second;
							//if (coe >= 0.2 && coe <= 3.0)
							//	bag3[(*ik).first] = 1;
							bag3_table[(*ik).first] = s;
						}
						//bag3.insert(ik, rdg[v2].end());
					}
				}
			}
		}
	}

	void search(int v, int& s,    // 深度、当前节点、起点
		unordered_map<int, vector<tmyPair<int, int>>>& bag2,
		int recv)//接收边值
	{
		//++dfsCnt;
		//_stack.push(v);
		path[pathIte++] = v;
		blocked[v] = true;

		//auto it = lower_bound(dg[v].begin(), dg[v].end(), s) - dg[v].begin();//当前节点的比起点大的子节点
		auto it = lower_bound(dg[v].begin() + lb_table[v][1], dg[v].end(), s) - dg[v].begin();
		//更新lb_table
		lb_table[v][1] = it;

		auto dgsize = dg[v].size();
		for (; it < dgsize; ++it)
		{
			//int nId = dg[v][it].first; // 子节点id
			if (blocked[nId] != 0)
			{
				continue;
			}
			if (v == s)//第1层 v==s
			{
				L1[nId] = dg[v][it].second;//保存第一层的边，用于最后连接条件判断
			}
			coe = (double)dg[v][it].second / (double)recv;//连向子节点的边除接收边，根节点接收边默认-1
			if ((coe < 0.2 || coe>3.0) && coe > 0) continue;

			//if (bag2.find(nId) != bag2.end())   // 再走两步就能回到s的话
			//if (bag2.count(nId) != 0)   // 再走两步就能回到s的话
			//if (bag2[nId].size()!=0)   // 再走两步就能回到s的话
			if (assistBag2[nId] == true)
			{
				//_stack.push(nId);
				path[pathIte++] = nId;
				bag2size = bag2[nId].size();
				for (int j = 0; j < bag2size; ++j)
				{
					tmp = bag2[nId][j].first;
					if (blocked[tmp]) { continue; }
					/* 判断V2-V1 / cur-V2 */
					coe = (double)bag2[nId][j].second / (double)dg[v][it].second;
					if (coe < 0.2 || coe>3.0) continue;
					/* 判断s-L1 / v1-s */
					coe = (double)L1[path[1]] / (double)bag2[nId][j].third;
					if (coe < 0.2 || coe>3.0) continue;
					//_stack.push(tmp);
					path[pathIte++] = tmp;
					//answer.push_back(_stack);    // 把路径塞进答案
					/* 复制结果路径到数组内存 */
					memcpy(ans3_7[pathIte - 3] + ansIte[pathIte - 3], path, pathIte * sizeof(int));
					++(threadFindSz[pathIte - 3][s]);
					ansIte[pathIte - 3] += pathIte;
					//_stack.pop();
					pathIte--;
				}
				//_stack.pop();
				pathIte--;
			}

			if (pathIte - 1 < 3 || (pathIte - 1 == 3 && bag3_table[nId] == s))
			{
				search(nId, s, bag2, dg[v][it].second);
			}
		}
		//_stack.pop();
		pathIte--;
		blocked[v] = false;
	}
};
shared_ptr<HWCodeCraft> solver[THREAD_NUM];

#ifdef  _UNIX
/* mmap read file */
void parseInput(char* testFile)
{
	int fd = open(testFile, 0);

	struct stat statbuf;

	char* start;

	char line[100] = { 0 };
	int ret = 0;

	fstat(fd, &statbuf);

	start = (char*)mmap(NULL, statbuf.st_size, PROT_READ, MAP_PRIVATE, fd, 0);

	int temp;

	int u, v, c;

	int it = 0;
	inputs.reserve(MAX_NUM * 2);
	amount.reserve(MAX_NUM);
	do {
		line[it++] = start[ret++];
		if (line[it - 1] == '\n')
		{
			it = 0;
			sscanf(line, "%d,%d,%d", &u, &v, &c);
			inputs.push_back(u);
			inputs.push_back(v);
			amount.push_back(c);
		}
	} while (ret < statbuf.st_size);
}

void parseInputPlus(char* infile)
{
	//int fd = open(infile, 0);
	//struct stat statbuf;
	//char *start;
	//fstat(fd, &statbuf);
	//start = (char*)mmap(NULL, statbuf.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
	int fd = open(infile, O_RDONLY);
	//	cout<<fd<<endl;
	int buf_len = 10 * 1024 * 1024 * 10;  // 28w lines 数据 10mb肯定够用了
	char* start = (char*)mmap(NULL, buf_len, PROT_READ, MAP_PRIVATE, fd, 0);
	//close(fd);
	//	for(int i=0;i<50;i++)
	//	{
	//		printf("%d\n",(unsigned int)start[i]);
	//	}
	//	printf("\n\n");
	char* curChar = start;
	/* 提取数据 */
	inputs.reserve(MAX_NUM * 2);
	amount.reserve(MAX_NUM);
	int tempNum = 0;
	while (*curChar != '\0')
	{
		while (*curChar != ',')//u
		{
			tempNum = 10 * tempNum + (*curChar - '0');
			++curChar;
		}
		++curChar;
		//inputs[inputs_ite++] = tempNum;
		inputs.push_back(tempNum);
		tempNum = 0;
		while (*curChar != ',')//v
		{
			tempNum = 10 * tempNum + (*curChar - '0');
			++curChar;
		}
		++curChar;
		//inputs[inputs_ite++] = tempNum;
		inputs.push_back(tempNum);
		tempNum = 0;
		while (*curChar != '\n' && *curChar != '\r')//amount
		{
			tempNum = 10 * tempNum + (*curChar - '0');
			++curChar;
		}
		/* 跳过\r\n */
		if (*curChar == '\r' || *curChar == '\n')
			++curChar;
		if (*curChar == '\r' || *curChar == '\n')
			++curChar;

		//amount[amount_ite++] = tempNum;
		amount.push_back(tempNum);
		tempNum = 0;
	}
}

#else
/* 后面需要使用mmap的方式 */
void parseInput(string& testFile) {
	FILE* file = fopen(testFile.c_str(), "r");
	int u, v, c;
	inputs.reserve(MAX_NUM * 2);
	amount.reserve(MAX_NUM);
	while (fscanf(file, "%d,%d,%d", &u, &v, &c) != EOF) {
		//while (fscanf(file, "%d%d%d", &u, &v, &c) != EOF) {
		inputs.push_back(u);
		inputs.push_back(v);
		amount.push_back(c);
	}
}

void parseInputPlus(string& testFile) {
	FILE* file = fopen(testFile.c_str(), "r");
	fseek(file, 0L, SEEK_END);
	int fileSz = ftell(file);
	char* start = new char[fileSz + 1];
	fseek(file, 0L, SEEK_SET);

	//fread 读的时候会把\n\r只读出一个\n，因此fileSz>=startSz ，对于以\n\r换行的文件，fileSz-startSz == 边个数，
	int startSz = fread(start, sizeof(char), fileSz, file);
	fclose(file);
	start[startSz] = '\0';

	/* 提取数据 */
	inputs.reserve(MAX_NUM * 2);
	amount.reserve(MAX_NUM);
	char* curChar = start;
	int tempNum = 0;
	while (*curChar != '\0')
	{
		while (*curChar != ',')//u
		{
			tempNum = 10 * tempNum + (*curChar - '0');
			++curChar;
		}
		++curChar;
		//inputs[inputs_ite++] = tempNum;
		inputs.push_back(tempNum);
		tempNum = 0;
		while (*curChar != ',')//v
		{
			tempNum = 10 * tempNum + (*curChar - '0');
			++curChar;
		}
		++curChar;
		//inputs[inputs_ite++] = tempNum;
		inputs.push_back(tempNum);
		tempNum = 0;
		while (*curChar != '\n')//amount
		{
			tempNum = 10 * tempNum + (*curChar - '0');
			++curChar;
		}
		++curChar;
		//amount[amount_ite++] = tempNum;
		amount.push_back(tempNum);
		tempNum = 0;
	}

}


#endif //  WIN

void constructGraph() {
	auto tmp = inputs;
	sort(tmp.begin(), tmp.end());
	tmp.erase(unique(tmp.begin(), tmp.end()), tmp.end());
	nodeCnt = tmp.size();
	//idsComma.reserve(nodeCnt);
	//idsLF.reserve(nodeCnt);
	//nodeCnt = 0;			
	idsComma.reserve(nodeCnt);		//改为从1开始映射
	idsLF.reserve(nodeCnt);
	idsComma.push_back("");			//填充1个无用值
	idsLF.push_back("");			//填充1个无用值
	nodeCnt = 1;
	for (int& x : tmp) {
		idsComma.push_back(to_string(x) + ',');
		idsLF.push_back(to_string(x) + '\n');
		idHash[x] = nodeCnt++;
	}
#ifdef TEST
	printf("%d Nodes in Total\n", nodeCnt - 1);
#endif
	int sz = inputs.size();
	//dg = DirectedGraph(nodeCnt);
	//rdg = DirectedGraph(nodeCnt);
	dg.resize(nodeCnt);
	rdg.resize(nodeCnt);
	inDegrees = vector<int>(nodeCnt, 0);		//第0位无用
	outDegrees = vector<int>(nodeCnt, 0);		//第0位无用
	for (int i = 0; i < sz; i += 2) {
		int u = idHash[inputs[i]], v = idHash[inputs[i + 1]];			//从1开始映射 u和v属于 [1,nodeCnt-1]
		dg[u].push_back(tmyPair<int, int>(v, amount[i / 2]));
		rdg[v].push_back(tmyPair<int, int>(u, amount[i / 2]));
		++inDegrees[v];
		++outDegrees[u];
	}
	//int i = 0;
	//// 对邻接链根据节点id排序
	//for (i = 0; i < dg.size(); ++i)
	//{
	//	sort(dg[i].begin(), dg[i].end());
	//}
	//for (i = 0; i < rdg.size(); ++i)
	//{
	//	sort(rdg[i].begin(), rdg[i].end());
	//}
}

//////////////////////////////////////////////////////////////////////////////////////////////
int eraseCnt = 0;
/* 拓扑排序 */
/* 判断出度为0时，有问题，出度时应使用逆图来 */
void topoSort(vector<int>& degs, bool doSoring) {
	queue<int> que;
	for (int i = 1; i < nodeCnt; i++) {			//1是dg第一个有效位置，开始映射 ，[1,nodeCnt-1]
		if (0 == degs[i])
		{
			que.push(i);
		}
	}
	while (!que.empty()) {
		int u = que.front();
		que.pop();
		for (auto& v : dg[u]) {
			if (0 == --degs[v.first])
			{
				que.push(v.first);
			}
		}
	}

	for (int i = 1; i < nodeCnt; i++) {			//1是dg第一个有效位置，开始映射
		if (degs[i] == 0) {
			dg[i].clear();
			rdg[i].clear();
			++eraseCnt;
		}
		else if (doSoring) {
			sort(dg[i].begin(), dg[i].end());
			sort(rdg[i].begin(), rdg[i].end());
		}
	}
	//	if (!doSoring)
	//		cout << "indegree erase: " << eraseCnt << endl;
	//	else
	//		cout << "outdegree earse : " << eraseCnt << endl;
}


/* 拓扑排序 */
/* 判断出度为0时，有问题，出度时应使用逆图来 */
void topoSort_inv(vector<int>& degs, bool doSoring) {
	queue<int> que;
	for (int i = 1; i < nodeCnt; i++) {
		if (0 == degs[i])
		{
			que.push(i);
		}
	}
	while (!que.empty()) {
		int u = que.front();
		que.pop();
		for (auto& v : rdg[u]) {
			if (0 == --degs[v.first])
			{
				que.push(v.first);
			}
		}
	}

	for (int i = 1; i < nodeCnt; i++) {
		if (dg[i].empty() && rdg[i].empty()) continue;
		if (degs[i] == 0) {
			++eraseCnt;
			dg[i].clear();
			rdg[i].clear();
		}
		else if (doSoring) {
			sort(dg[i].begin(), dg[i].end());
			sort(rdg[i].begin(), rdg[i].end());
		}
	}
	//cout << "outdegree earse : " << eraseCnt << endl;
}

/* 去除0点 */
void reMap()
{
	validCnt = nodeCnt - 1 - eraseCnt;
	validNode.reserve(validCnt);
	auto dgsz = dg.size();			//dg.size() = nodeCnt,0为无用 [1，nodeCnt-1]为有效
	for (int i = 1; i < dgsz; i++)
	{
		if (!dg[i].empty())
		{
			validNode.push_back(i);
		}
	}
}


/* 组合线程数据并写入文件 */
void save_fwrite(const string outputFile) {
	//auto t = clock();
	FILE *fp = fopen(outputFile.c_str(), "wb");
	char* ansBuf = new char[1024 * 1024 * 1500];//1500M

	/* 计算总的结果环数 */
	int ansCnt = 0;
	for (int Tid = 0; Tid < THREAD_NUM; Tid++)
	{
		ansCnt += solver[Tid]->ansIte[0] / 3;
		ansCnt += solver[Tid]->ansIte[1] / 4;
		ansCnt += solver[Tid]->ansIte[2] / 5;
		ansCnt += solver[Tid]->ansIte[3] / 6;
		ansCnt += solver[Tid]->ansIte[4] / 7;
	}
	/* charLen 输出字符结果内存大小 */
	int charLen = sprintf(ansBuf, "%d\n", ansCnt);
	int pos[THREAD_NUM] = { 0 };//缓存区当前位置
	const char* temp;
	int Tid;
	for (int i = 3; i <= 7; i++)
	{
		for (int init_i = 0; init_i < THREAD_NUM; init_i++)
		{
			pos[init_i] = 0;
		}
		for (int cnt = 0; cnt < nodeCnt; cnt++)
		{
			if (threadFindSz[i - 3][cnt] == 0) continue;//没有从该节点开始的环
			Tid = threadFind[cnt];//当前根节点的线程
			for (int j = 0; j < threadFindSz[i - 3][cnt]; j++)
			{
				//输出该根节点路径
				for (int q = pos[Tid]; q < pos[Tid] + i - 1; q++)
				{
					temp = idsComma[solver[Tid]->ans3_7[i - 3][q]].c_str();
					int len = strlen(temp);
					memcpy(ansBuf + charLen, temp, len);
					charLen += len;
				}
				temp = idsLF[solver[Tid]->ans3_7[i - 3][pos[Tid] + i - 1]].c_str();
				int len = strlen(temp);
				memcpy(ansBuf + charLen, temp, len);
				charLen += len;
				pos[Tid] += i;//更新pos位置
			}
		}
	}

	fwrite(ansBuf, charLen, sizeof(char), fp);
	fclose(fp);
	delete[]ansBuf;
	//cout << clock() - t << endl;
}

/////////////////////////////////////////////////////////////////////////////////////////////////////

int main()
{
	//auto t = clock();
#ifdef _UNIX
	char* input = "/data/test_data.txt";
	//char* output = "/projects/student/result.txt";
	parseInputPlus(input);
#else
	string input = "n10000_e50000.txt";//test_data_dalao  test_data_28W test_data_pre
							  //string input = "test_data_dalao.txt";
	string output = "result.txt";
	//parseInput(input);
	parseInputPlus(input);
#endif // _UNIX


	constructGraph();
	topoSort(inDegrees, false);
	topoSort_inv(outDegrees, true);
	reMap();

	thread th[THREAD_NUM];
	for (int i = 0; i < THREAD_NUM; i++)
	{
		solver[i] = make_shared<HWCodeCraft>(i);
	}
	for (int i = 0; i < THREAD_NUM; i++)
	{
		//th[i] = thread(&HWCodeCraft::findCircuits, solver[i], argv[i][0]*nodeCnt, argv[i][1]*nodeCnt);
		th[i] = thread(&HWCodeCraft::findCircuits, solver[i]);
	}
	// 将四个线程和主线程同步一下
	for (int i = 0; i < THREAD_NUM; i++)
	{
		if (th[i].joinable()) { th[i].join(); }
	}
#ifdef _UNIX
	//save_mmap(output);
	string output = "/projects/student/result.txt";
	save_fwrite(output);
#else
	save_fwrite(output);
#endif // _UNIX
	//cout << "dfs count:"<<dfsCnt << endl;
	//cout << clock() - t << endl;
	return 0;
}
