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

std::vector<Node*> dir_nodes;	// link-cut tree
std::vector<node> G_und_nodes;

typedef std::map<int, edge> list_of_edges;
list_of_edges G_edges;

// G - {u} for u in V(G)
std::vector< std::vector<node> > Gs_und_nodes;
std::vector<list_of_edges> lists_of_edges;
std::array<hdt_base*, NUMJUNCS + NUMJUNCS> Gmus;

std::set<int> lc_edges, cyclic_edges;

bool
added_to_link_cut(int u, int v)
{	if (LinkCut::root(dir_nodes[u]) != LinkCut::root(dir_nodes[v]))
	{	LinkCut::link(dir_nodes[u], dir_nodes[v]);	// link u to v
		lc_edges.insert(pairing_function(u, v));
		return true;
	}
	cyclic_edges.insert(pairing_function(u, v));
	return false;
}

bool
added_edge(int u, int v, bool recovery, microseconds& time)
{	if (recovery) return added_to_link_cut(u, v);

	int key = pairing_function(u, v);
	for (int i = 0; i < dir_nodes.size(); i++)
		if ((i != u) && (i != v))
		{	lists_of_edges[i][key] = Gmus[i]->ins(Gs_und_nodes[i][u], Gs_und_nodes[i][v]);
		}

	return added_to_link_cut(u, v);
}

void
removed_edge(int u, int v, hdt_base& hb)
{	int key = pairing_function(u, v);
	for (int i = 0; i < dir_nodes.size(); i++)
		if ((i != u) && (i != v))
		{	Gmus[i]->del(lists_of_edges[i][key]);
			auto it = lists_of_edges[i].find(key);
			lists_of_edges[i].erase(it);
		}

	auto it = std::find(lc_edges.begin(), lc_edges.end(), key);
	if (it == lc_edges.end())
	{	it = std::find(cyclic_edges.begin(), cyclic_edges.end(), key);
		cyclic_edges.erase(it);
		return;
	}

	LinkCut::cut(dir_nodes[u], dir_nodes[v] , dir_nodes);
	lc_edges.erase(it);

	if (!hb.connected(G_und_nodes[u], G_und_nodes[v])) return;
	
	for (auto it = cyclic_edges.begin(); it != cyclic_edges.end(); it++)
	{	int u, v;
		inv(*it, u, v);
		if (LinkCut::root(dir_nodes[u]) != LinkCut::root(dir_nodes[v]))
		{	microseconds add_time;
			added_edge(u, v, true, add_time);
			cyclic_edges.erase(it);
			break;
		}
	}
}

void
undirected_from_root(Node *p, std::vector<Node *>& path) {
	path.clear();
	std::stack<Node *> my_stack;
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
undirected_path(std::vector<Node *>& path1, std::vector<Node *>& path2, Node* lca, std::vector<Node *>& path)
{	path.clear();
	if (path1.back() != path2.back()) return;	// path1 & path2 don't intersect
	for (auto nd : path1)	// left to right
	{ path.push_back(nd); if (nd == lca) break; }

	auto it = path2.rbegin();
	while (*it != lca) it++;
	for (it++; it != path2.rend(); it++) path.push_back(*it);
}

bool
are_biconnected(int u, int v, hdt_base& hb, int& chain_len)
{	LinkCut::access(dir_nodes[u]);
	std::vector<Node *> path_to_u; undirected_from_root(dir_nodes[u],path_to_u);
	Node* lca = LinkCut::access(dir_nodes[v]);
	std::vector<Node *> path_to_v; undirected_from_root(dir_nodes[v],path_to_v);
	std::vector<Node *> uv_path;
	undirected_path(path_to_u, path_to_v, lca, uv_path);

	chain_len = 0;
	if (uv_path.empty()) return false;
	auto it = uv_path.begin() + 1;
	bool biconnected = true;
	while (it != (uv_path.end() - 1))
	{	int w = (*it)->id, u = (*(it - 1))->id, v = (*(it + 1))->id;
		chain_len++;
		if (!Gmus[w]->connected(Gs_und_nodes[w][u], Gs_und_nodes[w][v]))
		{	biconnected = false; break; }
		it++;
	}
	return biconnected;
}

int
main(int argc, char** argv)
{	dc_graph G;
	G.make_undirected();

	std::string s;
	std::getline(std::cin, s);
	int n = std::stoi(s);

	for (int i = 0; i < n; i++) G_und_nodes.push_back(G.new_node());
	for (int i = 0; i < G.number_of_nodes(); i++)
		dir_nodes.push_back(new Node(FOO, i));

	std::vector<dc_graph> Gs;
	for (int i = 0; i < G.number_of_nodes(); i++) Gs.push_back(G);

	for (int i = 0; i < Gs.size(); i++)
	{	Gmus[i] = new hdt_base(Gs[i]);
		std::vector<node> nv;
		node a_node; forall_nodes(a_node, Gs[i]) nv.push_back(a_node);
		Gs_und_nodes.push_back(nv);

		list_of_edges loe;
		for (int u = 0; u < Gs.size(); u++) lists_of_edges.push_back(loe);
	}

	hdt_base hb(G);
	steady_clock::time_point start = steady_clock::now();
	while (std::getline(std::cin, s))
	{	int op, u, v;
		sscanf(s.c_str(), "%d %d %d", &op, &u, &v);
		if (op == ADD)
		{	int key = pairing_function(u, v);
			if (G_edges.find(key) != G_edges.end()) continue;
			G_edges[key] = hb.ins(G_und_nodes[u], G_und_nodes[v]);
		} else if (op == REM)
		{	int key = pairing_function(u, v);
			if (G_edges.find(key) == G_edges.end()) continue;
			hb.del(G_edges[key]);
			G_edges.erase(key);
			removed_edge(u, v, hb);
		} else
		{	int chain_len = 0;
			auto rv = are_biconnected(u, v, hb, chain_len);
			steady_clock::time_point end_qry = steady_clock::now();
			std::cout << u << " " << v << " " << (rv ?  "biconnected" :
					"not biconnected") << std::endl;
		}
	}
	steady_clock::time_point end = steady_clock::now();
	std::cout << duration<double>(end - start).count() << " s" << std::endl;
	return 0;
}
