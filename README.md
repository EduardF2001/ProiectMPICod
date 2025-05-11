# ProiectMPICod
Aici se gasesc cod sursa pentru codul DPLL si DL C++ 


DPLL ----------------------------------------------------------------------

#include <iostream>
#include <vector>
#include <fstream>
#include <sstream>
#include <chrono>

using namespace std;
using namespace std::chrono;


struct Clause {
    vector<int> literals;
};


vector<Clause> clauses;
vector<int> assignment;


int decisionCount = 0;
int conflictCount = 0;


void readCNF(const string& filename, int& numVars) {
    ifstream file(filename);
    string line;
    bool headerFound = false;

    if (!file.is_open()) {
        cout << "Could not open the file. Please check the file path!" << endl;
        return;
    }

    cout << "File opened successfully!" << endl;


    while (getline(file, line)) {

        if (line.empty() || line[0] == 'c') continue;


        if (line[0] == 'p' && !headerFound) {
            istringstream iss(line);
            string tmp;
            int numClauses;
            if (iss >> tmp >> tmp >> numVars >> numClauses) {
                assignment.resize(numVars + 1, -1);
                headerFound = true;
                cout << "Found header: " << numVars << " variables, " << numClauses << " clauses" << endl;
            } else {
                cout << "Error: Couldn't parse the CNF header." << endl;
                return;
            }
        } else {

            Clause clause;
            istringstream iss(line);
            int literal;
            while (iss >> literal) {
                if (literal == 0) break;
                clause.literals.push_back(literal);
            }
            clauses.push_back(clause);
        }
    }

    if (!headerFound) {
        cout << "Error: CNF header not found!" << endl;
    } else {
        cout << "Finished reading CNF with " << clauses.size() << " clauses." << endl;
    }
}


bool checkSatisfaction() {
    for (const auto& clause : clauses) {
        bool clauseSatisfied = false;
        for (int literal : clause.literals) {
            int var = abs(literal);
            int value = assignment[var];
            if (value == -1) continue;
            if ((literal > 0 && value == 1) || (literal < 0 && value == 0)) {
                clauseSatisfied = true;
                break;
            }
        }
        if (!clauseSatisfied) return false;
    }
    return true;
}


bool unitPropagation() {
    bool changesMade = true;
    while (changesMade) {
        changesMade = false;

        for (auto& clause : clauses) {
            int unassignedCount = 0;
            int lastUnassignedLiteral = 0;
            bool clauseAlreadySatisfied = false;
            for (int literal : clause.literals) {
                int var = abs(literal);
                int value = assignment[var];
                if (value == -1) {
                    unassignedCount++;
                    lastUnassignedLiteral = literal;
                } else if ((literal > 0 && value == 1) || (literal < 0 && value == 0)) {
                    clauseAlreadySatisfied = true;
                    break;
                }
            }


            if (!clauseAlreadySatisfied && unassignedCount == 0) {
                conflictCount++;
                return false; // Conflict occurred
            }


            if (!clauseAlreadySatisfied && unassignedCount == 1) {
                int var = abs(lastUnassignedLiteral);
                assignment[var] = (lastUnassignedLiteral > 0) ? 1 : 0;
                changesMade = true;
            }
        }
    }
    return true;
}


bool DPLL() {
    if (!unitPropagation()) return false;
    if (checkSatisfaction()) return true;

    int varToAssign = -1;
    for (int i = 1; i < assignment.size(); ++i) {
        if (assignment[i] == -1) {
            varToAssign = i;
            break;
        }
    }

    if (varToAssign == -1) return false;

    decisionCount++;


    cout << "Current variable assignments: ";
    for (int i = 1; i < assignment.size(); ++i) {
        cout << assignment[i] << " ";
    }
    cout << endl;


    assignment[varToAssign] = 1;
    if (DPLL()) return true;

    assignment[varToAssign] = 0;
    if (DPLL()) return true;


    assignment[varToAssign] = -1;
    return false;
}

int main(int argc, char** argv) {
    if (argc != 2) {
        cout << "Usage: ./sat_solver filename.cnf" << endl;
        return 1;
    }

    int numVars;
    readCNF(argv[1], numVars);
    auto start = high_resolution_clock::now();
    bool solutionFound = DPLL();
    auto stop = high_resolution_clock::now();
    auto elapsedTime = duration_cast<milliseconds>(stop - start);

    cout << "\n==== Results ====" << endl;
    if (solutionFound) {
        cout << "SATISFIABLE" << endl;
        cout << "Solution: ";
        for (int i = 1; i <= numVars; ++i) {
            if (assignment[i] == -1) {
                cout << "?" << i << " ";
            } else if (assignment[i] == 1) {
                cout << i << " ";
            } else {
                cout << "-" << i << " ";
            }
        }
        cout << "0" << endl;
    } else {
        cout << "UNSATISFIABLE" << endl;
    }


    cout << "Time taken: " << elapsedTime.count() / 1000.0 << " seconds" << endl;
    cout << "Decisions made: " << decisionCount << endl;
    cout << "Conflicts :" << conflictCount << endl;

    return 0;
}









------------------------------------------------------------------------------------




DP




#include <iostream>
#include <fstream>
#include <vector>
#include <set>
#include <map>
#include <sstream>
#include <algorithm>
#include <chrono>
#include <iomanip>

using namespace std;

using Clause = set<int>;
using CNF = vector<Clause>;


int variables_eliminated = 0;


bool parseDIMACS(const string& filename, CNF& formula, int& num_vars) {
    ifstream infile(filename);
    if (!infile) {
        cerr << "Cannot open file: " << filename << endl;
        return false;
    }

    string line;
    while (getline(infile, line)) {
        if (line.empty() || line[0] == 'c') continue;
        if (line[0] == 'p') {
            string tmp;
            int num_clauses;
            istringstream iss(line);
            iss >> tmp >> tmp >> num_vars >> num_clauses;
        } else {
            istringstream iss(line);
            Clause clause;
            int literal;
            while (iss >> literal && literal != 0) {
                clause.insert(literal);
            }
            formula.push_back(clause);
        }
    }

    return true;
}


set<int> getVariables(const CNF& formula) {
    set<int> vars;
    for (const auto& clause : formula) {
        for (int lit : clause)
            vars.insert(abs(lit));
    }
    return vars;
}


CNF resolveOnVar(const CNF& formula, int var) {
    CNF result;
    vector<Clause> pos, neg;


    for (const auto& clause : formula) {
        if (clause.count(var))
            pos.push_back(clause);
        else if (clause.count(-var))
            neg.push_back(clause);
        else
            result.push_back(clause);
    }


    for (const auto& c1 : pos) {
        for (const auto& c2 : neg) {
            Clause res;
            for (int lit : c1)
                if (lit != var) res.insert(lit);
            for (int lit : c2)
                if (lit != -var) res.insert(lit);


            bool tautology = false;
            for (int lit : res) {
                if (res.count(-lit)) {
                    tautology = true;
                    break;
                }
            }
            if (!tautology)
                result.push_back(res);
        }
    }

    variables_eliminated++;
    return result;
}


bool dpSolve(CNF formula) {
    while (true) {
        if (formula.empty()) return true;
        for (const auto& clause : formula)
            if (clause.empty()) return false;

        set<int> vars = getVariables(formula);
        if (vars.empty()) return true;

        int var = *vars.begin();
        formula = resolveOnVar(formula, var);
    }
}

int main() {
    CNF formula;
    int num_vars;

    string filename = "C:\\Users\\pc 10\\Desktop\\DPLL-MPI\\Example.cnf.txt";

    if (!parseDIMACS(filename, formula, num_vars)) {
        return 1;
    }

    auto start = chrono::high_resolution_clock::now();
    bool result = dpSolve(formula);
    auto end = chrono::high_resolution_clock::now();

    chrono::duration<double> elapsed = end - start;

    cout << (result ? "SATISFIABLE" : "UNSATISFIABLE") << endl;


    cout << fixed << setprecision(6);
    cout << "Time taken: " << elapsed.count() << " seconds" << endl;

    cout << "Variables eliminated: " << variables_eliminated << endl;

    return 0;
}









