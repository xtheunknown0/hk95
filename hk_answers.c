#include <iostream>
#include <map>
#include <vector>
#include <stack>
#include <list>
#include <algorithm>		// swap, algorithm
#include <cassert>
#include <chrono>			// chrono::system_clock
#include <cstdio>			// sscanf
#include <string>
#include <cassert>
#include <dc_hdt.h>
#include <LEDA/graph.h>
#include <LEDA/graph_alg.h>	// BICONNECTED_COMPONENTS2
#include <dyn_con.h>
#include "link_cut_node.h"	// Node
#include "link_cut.h"
#include "bijection.h"
#include "memory.h"

const int FOO = 0;
const int NUMJUNCS = 3000;
const int ADD = 0;
const int REM = 1;
const int QRY = 2;

using namespace std::chrono;

std::vector<Node*> VG;	// link-cut tree
std::set<int> tree_edges, cyclic_edges;

// G - {u} for u in V(G)
std::vector< std::vector<Node*> > VGmu;
std::vector< std::set<int> > EGmu, EGmEGmu;

/* add_edge: add (u, v) to E(G) and all E(G - {w}), w != u, v */
void
add_edge(int u, int v)
{	int key = pairing_function(u, v);
	if (LinkCut::root(VG[u]) != LinkCut::root(VG[v]))
	{	LinkCut::link(VG[u], VG[v]);	// link u to v
		tree_edges.insert(pairing_function(u, v));
	} else cyclic_edges.insert(key);

	for (int w = 0; w < VG.size(); w++)
	{	if ((w == u) || (w == v)) continue;
		LinkCut::access(VGmu[w][u]);
		LinkCut::access(VGmu[w][v]);
		if (VGmu[w][u]->p == VGmu[w][v]) continue;	// already have tree edge
		if (LinkCut::root(VGmu[w][u]) != LinkCut::root(VGmu[w][v]))
		{	LinkCut::link(VGmu[w][u], VGmu[w][v]);	// link u to v
			EGmu[w].insert(pairing_function(u, v));
		} else if (EGmEGmu[w].find(key) == EGmEGmu[w].end())
			EGmEGmu[w].insert(key);
	}
}

void
remove_edge(int u, int v)
{	int key = pairing_function(u, v);
	auto it = tree_edges.find(key);
	if (it == tree_edges.end()) cyclic_edges.erase(key);
	else
	{	LinkCut::cut(VG[u], VG[v], VG);
		tree_edges.erase(it);

		auto it2 = cyclic_edges.begin();
		while (it2 != cyclic_edges.end())
		{	int x, y;
			inv(*it2, x, y);
			if (LinkCut::root(VG[x]) != LinkCut::root(VG[y]))
			{	LinkCut::link(VG[x], VG[y]);	// link x to y
				tree_edges.insert(*it2);
				cyclic_edges.erase(it2);
				break;
			}
			it2++;
		}
	}

	for (int w = 0; w < VG.size(); w++)
	{	if ((w == u) || (w == v)) continue;
		if (EGmu[w].find(key) == EGmu[w].end()) EGmEGmu[w].erase(key);
		else
		{	LinkCut::cut(VGmu[w][u], VGmu[w][v], VGmu[w]);
			EGmu[w].erase(key);
			auto it2 = EGmEGmu[w].begin();
			while (it2 != EGmEGmu[w].end() )
			{	int x, y;
				inv(*it2, x, y);
				if (LinkCut::root(VGmu[w][x]) != LinkCut::root(VGmu[w][y]))
				{	LinkCut::link(VGmu[w][x], VGmu[w][y]);	// link x to y
					EGmu[w].insert(*it2);
					EGmEGmu[w].erase(it2);
					break;
				}
				it2++;
			}
		}
	}
}

void
undirected_from_root(Node* p, std::vector<Node*>& path) {
	path.clear();
	std::stack<Node*> my_stack;
	Node *curr = p;

	while (true)
	{	while (curr) { my_stack.push(curr); curr = curr->l; }
		if (my_stack.empty()) break;
		Node* top = my_stack.top();
		path.push_back(top);
		my_stack.pop();
		curr = top->r;
	}
}

void
undirected_path(std::vector<Node*>& path1, std::vector<Node*>& path2, Node* lca, std::vector<Node*>& path)
{	path.clear();
	if (path1.back() != path2.back()) return;	// path1 & path2 don't intersect
	for (auto nd : path1)	// left to right
	{ path.push_back(nd); if (nd == lca) break; }

	auto it = path2.rbegin();
	while (*it != lca) it++;
	for (it++; it != path2.rend(); it++) path.push_back(*it);
}

bool
are_biconnected(int u, int v, int& chain_len)
{	LinkCut::access(VG[u]);
	std::vector<Node*> path_to_u;
	undirected_from_root(VG[u], path_to_u);
	Node* lca = LinkCut::access(VG[v]);
	std::vector<Node*> path_to_v;
	undirected_from_root(VG[v], path_to_v);
	std::vector<Node*> uv_path;
	undirected_path(path_to_u, path_to_v, lca, uv_path);

	chain_len = 0;
	if (uv_path.empty()) return false;
	auto it = uv_path.begin() + 1;
	bool biconnected = true;
	while (it != (uv_path.end() - 1))
	{	int w = (*it)->id, u = (*(it - 1))->id, v = (*(it + 1))->id;
		chain_len++;
		if (LinkCut::root(VGmu[w][u]) != LinkCut::root(VGmu[w][v]))
		{	biconnected = false;
			std::cout << "(" << u << ", " << v << ") disconnected in G - {" << w
					  << "}." << std::endl;
			break;
		}
		std::cout << "(" << u << ", " << v << ") connected in G - {" << w
                  << "}." << std::endl;
		it++;
	}
	return biconnected;
}

int
main(int argc, char** argv)
{	std::string s;
	std::getline(std::cin, s);
	int n = std::stoi(s);

	for (int u = 0; u < n; u++) VG.push_back(new Node(FOO, u));
	for (int u = 0; u < n; u++)
	{	std::vector<Node*> vec;
		for (int v = 0; v < n; v++) vec.push_back(new Node(FOO, v));
		VGmu.push_back(vec);
		std::set<int> S;
		EGmu.push_back(S);
		EGmEGmu.push_back(S);
	}

	std::set<int> EG;
	steady_clock::time_point start = steady_clock::now();
	while (std::getline(std::cin, s))
	{	int op, u, v;
		sscanf(s.c_str(), "%d %d %d", &op, &u, &v);
		if (op == ADD)
		{	int key = pairing_function(u, v);
			if (EG.find(key) == EG.end())
			{	EG.insert(key);
				add_edge(u, v);
				for (int u = 0; u < n; u++)
					for (int v = u + 1; v < n; v++)
					{	int chain_len = 0;
						auto rv = are_biconnected(u, v, chain_len);
						std::cout << u << " " << v << " " << (rv ?
								"biconnected" : "not biconnected") << std::endl;
					}
			}
		} else if (op == REM)
		{	int key = pairing_function(u, v);
			if (EG.find(key) != EG.end())
			{	EG.erase(key);
				remove_edge(u, v);
			}
		} else
		{	int chain_len = 0;
			auto rv = are_biconnected(u, v, chain_len);
			std::cout << u << " " << v << " " << (rv ?  "biconnected" :
					"not biconnected") << std::endl;
		}
	}
	steady_clock::time_point end = steady_clock::now();
	std::cout << duration<double>(end - start).count() << " s" << std::endl;
	std::cout << "getValue(): " << getValue() << std::endl;
	return 0;
}
