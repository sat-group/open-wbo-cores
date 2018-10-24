#include "Alg_Basic.h"

using namespace openwbo;

StatusCode Basic::search() {
    // Here you can control which algorithm is being used!
    // It if useful if you implement both linearsu and the MSU3 versions.
    return linearsu();
}

StatusCode Basic::linearsu(){

    /* Fill this method with the linear search unsat-sat that we discussed during 
     * our last meeting (Alg.2 page 12 of the survey paper); Then try to improve 
     * it by exploiting the unsat core that the SAT solver returns (Alg. 10 page 
     * 26 of the survey paper). For both versions, you should destroy and 
     * rebuild the SAT solver at each iteration since we did not go over how to 
     * perform an incremental construction of x_1 + ... + x_n <= k by either 
     * introducing variables to the left-hand side or by increasing k.
     */

    lbool res = l_False; // this will represent the output of the SAT solver

    // This will store the variables in the cardinality constraint
    vec<Lit> new_cardinality_variables;
    vec<Lit> cardinality_variables;

    /* TODO: relax the soft clauses. Note you can use/change the relaxFormula method */
    relaxFormula();

    uint64_t cost = 0; // this will store the current bound we are exploring 

    /* TODO: initialize the SAT solver with the hard and soft clauses. Note you can 
                     use/change the buildSATsolver method */
    Solver* sat_solver = buildSATSolver(); // replace NULL with the properly initialization

    std::map<Lit, int> core_mapping; // Mapping between the assumption literal and
                                                                    // the respective soft clause.

    // Soft clauses that are currently in the MaxSAT formula.
    vec<bool> active_soft;

    vec<Lit> encodingAssumptions;
    vec<Lit> assumptions;
    Encoder encoder;
    encoder.setCardEncoding(_CARD_TOTALIZER_);
    encoder.setIncremental(_INCREMENTAL_ITERATIVE_);

    // Initialization of the data structures
    active_soft.growTo(maxsat_formula->nSoft(), false);
    for (int i = 0; i < maxsat_formula->nSoft(); i++)
        core_mapping[~getAssumptionLit(i)] = i;

    for(;;){

        vec<Lit> assumptions; // You only need assumptions for the MSU3 algorithm!
        /* TODO: push all the assumptions variables from soft clauses into the 
         * assumption vector. Each soft clause has one assumption variable in the member
         * 'assumption_var' */

        // the SAT solver will return either l_False (unsatisfiable) or l_True (satisfiable)
        assumptions.clear();
        for (int i = 0; i < maxsat_formula->nSoft(); i++) {
            if (!active_soft[i]) assumptions.push(getSoftClause(i).assumption_var);
        }
        for (int i = 0; i < encodingAssumptions.size(); i++) {
            assumptions.push(encodingAssumptions[i]);
        }
        res = searchSATSolver(sat_solver, assumptions);

        if (res == l_True){
            // SAT solver returned satisfiable; What does this mean?
            // (*TODO*) fill the rest...
            printf("o %lld \n", cost);
            return _OPTIMUM_;
        } else {
            // SAT solver returned unsatisfiable; What does this mean?
            // (*TODO*) fill the rest...

            /* How to extract a core from the SAT solver?
             * This is only useful for the MSU3 algorithm */
            new_cardinality_variables.clear();
            for (int i = 0; i < sat_solver->conflict.size(); i++) {
                // printf("%d\n", core_mapping[sat_solver->conflict[i]]);
                if (core_mapping.find(sat_solver->conflict[i]) != core_mapping.end()) {
                    /* coreMapping[solver->conflict[i]]: 
                     * - will contain the index of the soft clause that appears in the core
                     * Use this information if you want to explore the unsat core!*/
                    int currIndex = core_mapping[sat_solver->conflict[i]];
                    // printf("%d \n", currIndex);
                    if (!active_soft[currIndex]) {
                        Soft &curr = getSoftClause(currIndex);
                        Lit card_var = curr.relaxation_vars[0];
                        cardinality_variables.push(card_var);
                        new_cardinality_variables.push(card_var);
                        active_soft[currIndex] = true;
                    }
                }
            }
            printf("c size of cardinality %d\n", cardinality_variables.size());
            // printf(", %lld \n", cost);
            /* The assumption vector should only contain assumptions variables from 
             * soft clauses that appeared in a core; this is only useful for the MSU3 
             * algorithm! */

            // Don't forget to rebuild the SAT solver and update the assumption vector!
            // cost++;
            delete sat_solver;
            sat_solver = buildSATSolver(); // replace this with the correct initialization

            /* How to encode x_1 + ... + x_n <= k?
             * You can use the following code: */
            cost++;
            if (!encoder.hasCardEncoding()) {
                if (cardinality_variables.size() > cost) {
                    encoder.buildCardinality(sat_solver, cardinality_variables, cost);
                    encoder.incUpdateCardinality(sat_solver, cardinality_variables, cost, encodingAssumptions);
                }
            } else {
                if (new_cardinality_variables.size() > 0) {
                    printf("%d %d\n", new_cardinality_variables.size(), sat_solver->nVars());                    
                    encoder.joinEncoding(sat_solver, new_cardinality_variables, cost);
                }
                encoder.incUpdateCardinality(sat_solver, cardinality_variables, cost, encodingAssumptions);
           }

            /* 'sat_solver': SAT solver should be build before 
             * 'cardinality_variables': should have the variables of the cardinality constraint
             * 'cost': should have the cost we are looking for */
        }
    }

    /* return states are:
     * _SATISFIABLE_
     * _UNSATISFIABLE_
     * _OPTIMUM_
     * _UNKNOWN_
     * _ERROR_ */
    return _UNKNOWN_;
     
}

Solver* Basic::buildSATSolver() {

    // SAT solver is created with no variables or clauses
    Solver *S = newSATSolver();

    /* The maxsat_formula contains all the information about the MaxSAT formula:
     * - hard clauses
     * - soft clauses and respective relaxation variables
     */

    // We first need to create all the variables in the SAT solver
    for (int i = 0; i < maxsat_formula->nVars(); i++)
        newSATVariable(S);

    // We then traverse the maxsat_formula and add all hard clauses to the SAT solver
    for (int i = 0; i < maxsat_formula->nHard(); i++)
        S->addClause(getHardClause(i).clause);

    /* Next, we need to traverse the maxsat_formula and add all soft clauses to 
     * the SAT solver (we must also include the relaxation variables)
     */
    vec<Lit> clause;
    for (int i = 0; i < maxsat_formula->nSoft(); i++) {
        clause.clear();
        Soft &s = getSoftClause(i);
        s.clause.copyTo(clause);
        for (int j = 0; j < s.relaxation_vars.size(); j++)
            clause.push(s.relaxation_vars[j]);

        S->addClause(clause);
    }

    return S;
}

void Basic::relaxFormula() {
    /* We relax the formula by creating a literal r_i and adding it as a relaxation 
     * variable; we also add him as an assumption variable with \not r_i. This 
     * allows the solver to assume that all relaxation variables are initially set 
     * to False.
     */
    for (int i = 0; i < maxsat_formula->nSoft(); i++) {
        Lit l = maxsat_formula->newLiteral();
        Soft &s = getSoftClause(i);
        s.relaxation_vars.push(l);
        s.assumption_var = ~l;
    }
}

