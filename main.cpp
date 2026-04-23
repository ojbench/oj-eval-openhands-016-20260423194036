#include <iostream>
#include <cstring>
#include <fstream>
#include <vector>
#include <algorithm>

const int MAX_KEY_SIZE = 65;
const int M = 100; // B+ Tree order

struct KeyValue {
    char key[MAX_KEY_SIZE];
    int value;
    
    KeyValue() {
        memset(key, 0, sizeof(key));
        value = 0;
    }
    
    KeyValue(const char* k, int v) {
        strncpy(key, k, MAX_KEY_SIZE - 1);
        key[MAX_KEY_SIZE - 1] = '\0';
        value = v;
    }
    
    bool operator<(const KeyValue& other) const {
        int cmp = strcmp(key, other.key);
        if (cmp != 0) return cmp < 0;
        return value < other.value;
    }
    
    bool operator==(const KeyValue& other) const {
        return strcmp(key, other.key) == 0 && value == other.value;
    }
};

class BPlusTree {
private:
    struct Node {
        bool isLeaf;
        int count;
        KeyValue keys[M];
        Node* children[M + 1];
        Node* next; // For leaf nodes
        
        Node(bool leaf = true) : isLeaf(leaf), count(0), next(nullptr) {
            for (int i = 0; i <= M; i++) {
                children[i] = nullptr;
            }
        }
        
        ~Node() {
            if (!isLeaf) {
                for (int i = 0; i <= count; i++) {
                    delete children[i];
                }
            }
        }
    };
    
    Node* root;
    std::string filename;
    
    void splitChild(Node* parent, int index, Node* child) {
        int mid = M / 2;
        Node* newNode = new Node(child->isLeaf);
        
        newNode->count = M - mid - (child->isLeaf ? 0 : 1);
        
        for (int i = 0; i < newNode->count; i++) {
            newNode->keys[i] = child->keys[mid + 1 + i];
        }
        
        if (!child->isLeaf) {
            for (int i = 0; i <= newNode->count; i++) {
                newNode->children[i] = child->children[mid + 1 + i];
            }
        } else {
            newNode->next = child->next;
            child->next = newNode;
        }
        
        child->count = mid;
        
        for (int i = parent->count; i > index; i--) {
            parent->children[i + 1] = parent->children[i];
        }
        parent->children[index + 1] = newNode;
        
        for (int i = parent->count - 1; i >= index; i--) {
            parent->keys[i + 1] = parent->keys[i];
        }
        parent->keys[index] = child->keys[mid];
        parent->count++;
    }
    
    void insertNonFull(Node* node, const KeyValue& kv) {
        int i = node->count - 1;
        
        if (node->isLeaf) {
            while (i >= 0 && kv < node->keys[i]) {
                node->keys[i + 1] = node->keys[i];
                i--;
            }
            node->keys[i + 1] = kv;
            node->count++;
        } else {
            while (i >= 0 && kv < node->keys[i]) {
                i--;
            }
            i++;
            
            if (node->children[i]->count == M) {
                splitChild(node, i, node->children[i]);
                if (node->keys[i] < kv) {
                    i++;
                }
            }
            insertNonFull(node->children[i], kv);
        }
    }
    
    void removeFromLeaf(Node* node, int idx) {
        for (int i = idx; i < node->count - 1; i++) {
            node->keys[i] = node->keys[i + 1];
        }
        node->count--;
    }
    
    void removeFromNonLeaf(Node* node, int idx) {
        KeyValue k = node->keys[idx];
        
        if (node->children[idx]->count >= (M + 1) / 2) {
            KeyValue pred = getPredecessor(node, idx);
            node->keys[idx] = pred;
            removeHelper(node->children[idx], pred);
        } else if (node->children[idx + 1]->count >= (M + 1) / 2) {
            KeyValue succ = getSuccessor(node, idx);
            node->keys[idx] = succ;
            removeHelper(node->children[idx + 1], succ);
        } else {
            merge(node, idx);
            removeHelper(node->children[idx], k);
        }
    }
    
    KeyValue getPredecessor(Node* node, int idx) {
        Node* cur = node->children[idx];
        while (!cur->isLeaf) {
            cur = cur->children[cur->count];
        }
        return cur->keys[cur->count - 1];
    }
    
    KeyValue getSuccessor(Node* node, int idx) {
        Node* cur = node->children[idx + 1];
        while (!cur->isLeaf) {
            cur = cur->children[0];
        }
        return cur->keys[0];
    }
    
    void fill(Node* node, int idx) {
        if (idx != 0 && node->children[idx - 1]->count >= (M + 1) / 2) {
            borrowFromPrev(node, idx);
        } else if (idx != node->count && node->children[idx + 1]->count >= (M + 1) / 2) {
            borrowFromNext(node, idx);
        } else {
            if (idx != node->count) {
                merge(node, idx);
            } else {
                merge(node, idx - 1);
            }
        }
    }
    
    void borrowFromPrev(Node* node, int idx) {
        Node* child = node->children[idx];
        Node* sibling = node->children[idx - 1];
        
        for (int i = child->count - 1; i >= 0; i--) {
            child->keys[i + 1] = child->keys[i];
        }
        
        if (!child->isLeaf) {
            for (int i = child->count; i >= 0; i--) {
                child->children[i + 1] = child->children[i];
            }
            child->children[0] = sibling->children[sibling->count];
            child->keys[0] = node->keys[idx - 1];
            node->keys[idx - 1] = sibling->keys[sibling->count - 1];
        } else {
            child->keys[0] = sibling->keys[sibling->count - 1];
            node->keys[idx - 1] = child->keys[0];
        }
        
        child->count++;
        sibling->count--;
    }
    
    void borrowFromNext(Node* node, int idx) {
        Node* child = node->children[idx];
        Node* sibling = node->children[idx + 1];
        
        child->keys[child->count] = node->keys[idx];
        
        if (!child->isLeaf) {
            child->children[child->count + 1] = sibling->children[0];
            node->keys[idx] = sibling->keys[0];
            
            for (int i = 1; i < sibling->count; i++) {
                sibling->keys[i - 1] = sibling->keys[i];
            }
            for (int i = 1; i <= sibling->count; i++) {
                sibling->children[i - 1] = sibling->children[i];
            }
        } else {
            child->keys[child->count] = sibling->keys[0];
            node->keys[idx] = sibling->keys[1];
            
            for (int i = 1; i < sibling->count; i++) {
                sibling->keys[i - 1] = sibling->keys[i];
            }
        }
        
        child->count++;
        sibling->count--;
    }
    
    void merge(Node* node, int idx) {
        Node* child = node->children[idx];
        Node* sibling = node->children[idx + 1];
        
        if (!child->isLeaf) {
            child->keys[child->count] = node->keys[idx];
            
            for (int i = 0; i < sibling->count; i++) {
                child->keys[child->count + 1 + i] = sibling->keys[i];
            }
            
            for (int i = 0; i <= sibling->count; i++) {
                child->children[child->count + 1 + i] = sibling->children[i];
            }
            
            child->count += sibling->count + 1;
        } else {
            for (int i = 0; i < sibling->count; i++) {
                child->keys[child->count + i] = sibling->keys[i];
            }
            child->count += sibling->count;
            child->next = sibling->next;
        }
        
        for (int i = idx; i < node->count - 1; i++) {
            node->keys[i] = node->keys[i + 1];
        }
        
        for (int i = idx + 1; i < node->count; i++) {
            node->children[i] = node->children[i + 1];
        }
        
        node->count--;
        
        sibling->isLeaf = true;
        sibling->count = 0;
        delete sibling;
    }
    
    void removeHelper(Node* node, const KeyValue& kv) {
        int idx = 0;
        while (idx < node->count && node->keys[idx] < kv) {
            idx++;
        }
        
        if (node->isLeaf) {
            if (idx < node->count && node->keys[idx] == kv) {
                removeFromLeaf(node, idx);
            }
            return;
        }
        
        bool flag = (idx < node->count && node->keys[idx] == kv);
        
        if (flag) {
            removeFromNonLeaf(node, idx);
        } else {
            if (node->children[idx]->count < (M + 1) / 2) {
                fill(node, idx);
            }
            
            if (idx > node->count) {
                removeHelper(node->children[idx - 1], kv);
            } else {
                removeHelper(node->children[idx], kv);
            }
        }
    }
    
    Node* getFirstLeaf(Node* node) {
        if (!node) return nullptr;
        while (!node->isLeaf) {
            node = node->children[0];
        }
        return node;
    }
    
public:
    BPlusTree(const std::string& fname) : root(nullptr), filename(fname) {
        root = new Node(true);
    }
    
    ~BPlusTree() {
        delete root;
    }
    
    void insert(const char* key, int value) {
        KeyValue kv(key, value);
        
        if (root->count == M) {
            Node* newRoot = new Node(false);
            newRoot->children[0] = root;
            splitChild(newRoot, 0, root);
            root = newRoot;
        }
        
        insertNonFull(root, kv);
    }
    
    void remove(const char* key, int value) {
        KeyValue kv(key, value);
        removeHelper(root, kv);
        
        if (root->count == 0) {
            Node* tmp = root;
            if (root->isLeaf) {
                root = new Node(true);
            } else {
                root = root->children[0];
            }
            tmp->isLeaf = true;
            tmp->count = 0;
            delete tmp;
        }
    }
    
    std::vector<int> find(const char* key) {
        std::vector<int> result;
        Node* leaf = getFirstLeaf(root);
        
        while (leaf) {
            for (int i = 0; i < leaf->count; i++) {
                if (strcmp(leaf->keys[i].key, key) == 0) {
                    result.push_back(leaf->keys[i].value);
                }
            }
            leaf = leaf->next;
        }
        
        std::sort(result.begin(), result.end());
        return result;
    }
};

int main() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);
    
    BPlusTree tree("data.db");
    
    int n;
    std::cin >> n;
    
    for (int i = 0; i < n; i++) {
        std::string cmd;
        std::cin >> cmd;
        
        if (cmd == "insert") {
            std::string key;
            int value;
            std::cin >> key >> value;
            tree.insert(key.c_str(), value);
        } else if (cmd == "delete") {
            std::string key;
            int value;
            std::cin >> key >> value;
            tree.remove(key.c_str(), value);
        } else if (cmd == "find") {
            std::string key;
            std::cin >> key;
            std::vector<int> result = tree.find(key.c_str());
            
            if (result.empty()) {
                std::cout << "null\n";
            } else {
                for (size_t j = 0; j < result.size(); j++) {
                    if (j > 0) std::cout << " ";
                    std::cout << result[j];
                }
                std::cout << "\n";
            }
        }
    }
    
    return 0;
}
