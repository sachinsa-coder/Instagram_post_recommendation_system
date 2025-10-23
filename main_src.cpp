#include <bits/stdc++.h>
using namespace std;

struct Edge{
    int to;
    double weight;
};

unordered_map<int,vector<Edge>> adj;
unordered_map<int,vector<int>> user_to_posts;
unordered_map<int,vector<int>> post_to_users;
unordered_map<int,unordered_set<string>> post_hashtags;
unordered_set<int> posts;
unordered_set<int> visited_users,visited_posts;

string normTag(string s){
    transform(s.begin(),s.end(),s.begin(),::tolower);
    while(!s.empty() && (s.front()=='#'|| isspace(s.front()))) s.erase(s.begin());
    while(!s.empty() && (s.back() ==','|| s.back()==';' || isspace(s.back()))) s.pop_back();
    return s;
}

const int POST_OFFSET=1000000;
void buildGraph(const string &filename){
    ifstream fin(filename);
    string line;
    getline(fin, line);
    while (getline(fin,line)){
        if(line.empty()) continue;
        stringstream ss(line);
        string post_s,user_s,hashtags,likes_s,comments_s;
        getline(ss,post_s,',');
        getline(ss,user_s,',');
        getline(ss,hashtags,',');
        getline(ss,likes_s,',');
        getline(ss,comments_s,',');

        if (post_s.empty() || user_s.empty()) continue;
        int post=stoi(post_s);
        int user=stoi(user_s);
        int likes=likes_s.empty() ? 0 : stoi(likes_s);
        int comments=comments_s.empty() ? 0 : stoi(comments_s);

        int post_node=POST_OFFSET + post;
        posts.insert(post_node);

        double weight=likes+2.0*comments;
        adj[user].push_back({post_node,weight});
        adj[post_node].push_back({user,weight});
        user_to_posts[user].push_back(post_node);
        post_to_users[post_node].push_back(user);

        string tmp;
        stringstream hs(hashtags);
        while(hs>>tmp){
            string tag = normTag(tmp);
            if(!tag.empty()) post_hashtags[post_node].insert(tag);
        }
    }
}

vector<int> BFS(int start_user, int max_posts){
    queue<int> q;
    unordered_set<int> visited_posts_local;
    vector<int> result;

    q.push(start_user);
    visited_users.insert(start_user);

    while (!q.empty() && result.size() < max_posts){
        int user=q.front(); q.pop();
        for(int post : user_to_posts[user]){
            if(visited_posts_local.count(post)) continue;
            visited_posts_local.insert(post);
            if(user!=start_user) result.push_back(post - POST_OFFSET);

            for(int u : post_to_users[post]){
                if(!visited_users.count(u)){
                    visited_users.insert(u);
                    q.push(u);
                }
            }
            if(result.size()>= max_posts) break;
        }
    }
    return result;
}

void DFS_util(int user, vector<int> &result, int max_posts){
    if(result.size() >= max_posts) return;
    for(int post : user_to_posts[user]){
        if (visited_posts.count(post)) continue;
        visited_posts.insert(post);
        result.push_back(post-POST_OFFSET);
        for(int u : post_to_users[post]){
            if (!visited_users.count(u)){
                visited_users.insert(u);
                DFS_util(u,result,max_posts);
            }
        }
        if (result.size()>= max_posts) return;
    }
}

vector<int> DFS(int start_user, int max_posts){
    vector<int> result;
    visited_users.clear();visited_posts.clear();
    for(int post : user_to_posts[start_user]) visited_posts.insert(post);
    for(int post : user_to_posts[start_user]){
        for(int u : post_to_users[post]){
            if (!visited_users.count(u)){
                visited_users.insert(u);
                DFS_util(u,result,max_posts);
            }
        }
        if (result.size()>=max_posts) return result;
    }
    return result;
}

unordered_map<int, double> Dijkstra(int start_user){
    unordered_map<int,double> dist;
    for (auto &kv : adj) dist[kv.first] = 1e18;

    using P=pair<double,int>;
    priority_queue<P,vector<P>,greater<P>> pq;

    dist[start_user]=0;
    pq.push({0,start_user});
    while(!pq.empty()){
        auto [d,u]=pq.top(); pq.pop();
        if (d>dist[u]) continue;
        for (auto &edge : adj[u]){
            int v=edge.to;
            double nd=d + (1.0 / (edge.weight + 1e-9));
            if (nd<dist[v]) {
                dist[v]=nd;
                pq.push({nd,v});
            }
        }
    }
    return dist;
}

double cosineSim(const unordered_set<string> &A, const unordered_set<string> &B){
    if (A.empty() || B.empty()) return 0.0;
    int inter=0;
    for (auto &x : A) if (B.count(x)) inter++;
    return (double)inter / (sqrt((double)A.size()) * sqrt((double)B.size()));
}

vector<pair<double,int>> topKCosine(int start_user,int max_posts){
    vector<pair<double,int>> scores;
    unordered_set<string> user_tags;
    for (int lp : user_to_posts[start_user])
        for (auto &tag : post_hashtags[lp])
            user_tags.insert(tag);

    for (auto &kv : post_hashtags){
        int post=kv.first;
        if (find(user_to_posts[start_user].begin(),user_to_posts[start_user].end(),post)!=user_to_posts[start_user].end())
            continue;
        double sc=cosineSim(user_tags,kv.second);
        if (sc>0.0) scores.push_back({sc,post});
    }

    sort(scores.begin(),scores.end(),[](auto &a,auto &b){
        if (a.first==b.first) return a.second<b.second;
        return a.first>b.first;
    });

    if ((int)scores.size()>max_posts) scores.resize(max_posts);
    return scores;
}

double jaccardSim(const unordered_set<string> &A,const unordered_set<string> &B){
    if (A.empty() || B.empty()) return 0.0;
    int inter=0;
    for (auto &x : A) if (B.count(x)) inter++;
    int uni = A.size() + B.size() - inter;
    return (double)inter / (double)uni;
}

vector<pair<double,int>> topKJaccard(int start_user,int max_posts){
    vector<pair<double,int>> scores;
    unordered_set<string> user_tags;
    for (int lp : user_to_posts[start_user])
        for (auto &tag : post_hashtags[lp])
            user_tags.insert(tag);

    for (auto &kv : post_hashtags) {
        int post=kv.first;
        if (find(user_to_posts[start_user].begin(),user_to_posts[start_user].end(), post) != user_to_posts[start_user].end())
            continue;

        double sc=jaccardSim(user_tags,kv.second);
        if (sc>0.0) scores.push_back({sc,post});
    }

    sort(scores.begin(), scores.end(), [](auto &a, auto &b){
        if (a.first==b.first) return a.second<b.second;
        return a.first>b.first;
    });

    if ((int)scores.size()>max_posts) scores.resize(max_posts);
    return scores;
}

int main(){
    string filename="instagram_demo_graph.csv";
    cout<<"Loading dataset...\n";
    buildGraph(filename);
    cout<<"Graph loaded: "<<adj.size()<<" nodes.\n";
    int start_user;
    cout<<"Enter user_id (e.g., 101–108): ";
    cin>>start_user;
    int max_posts=5;

    visited_users.clear();visited_posts.clear();
    vector<int> bfs_posts=BFS(start_user,max_posts);
    cout <<"\n=== BFS Candidate Posts ===\n";
    for(int p : bfs_posts) cout<<"Post "<<p<<" ";
    cout <<"\n";

    visited_users.clear();visited_posts.clear();
    vector<int> dfs_posts=DFS(start_user,max_posts);
    cout <<"\n=== DFS Posts (Depth-First) ===\n";
    for(int p : dfs_posts) cout<<"Post "<<p<<" ";
    cout<<"\n";

    cout<<"\n=== Dijkstra Ranked Posts (Engagement Weighted) ===\n";
    auto dist=Dijkstra(start_user);
    vector<pair<double,int>> ranking;
    for (auto &kv : dist) if(posts.count(kv.first)) ranking.push_back({kv.second,kv.first});
    sort(ranking.begin(),ranking.end());
    for (int i=0;i<min(max_posts,(int)ranking.size()); i++)
        cout <<"Post "<<ranking[i].second-POST_OFFSET<<" -> distance="<<ranking[i].first<<"\n";

    cout<<"\n=== Cosine Similarity Recommendations ===\n";
    auto cosRes=topKCosine(start_user,max_posts);
    if(cosRes.empty()) cout<<"No cosine recommendations.\n";
    else{
        for(auto &pr : cosRes)
            cout <<"Post "<< pr.second-POST_OFFSET<<" (score="<<pr.first<<")\n";
    }

    cout<<"\n=== Jaccard Similarity Recommendations ===\n";
    auto jaccRes=topKJaccard(start_user,max_posts);
    if(jaccRes.empty()) cout<<"No Jaccard recommendations.\n";
    else{
        for(auto &pr : jaccRes)
            cout<<"Post "<<pr.second-POST_OFFSET<<" (score="<<pr.first<<")\n";
    }
    return 0;
}