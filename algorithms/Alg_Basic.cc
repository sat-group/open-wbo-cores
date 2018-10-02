#include "Alg_Basic.h"

using namespace openwbo;

StatusCode Basic::search() {
  // Here you can control which algorithm is being used!
  // It if useful if you implement both linearsu and the MSU3 versions.
  return linearsu();
}

uint64_t dec(uint64_t cost) {
  if (cost > 0) return cost-1;
  return 0;
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

  /* TODO: relax the soft clauses. Note you can use/change the relaxFormula method */

  /* TODO: initialize the SAT solver with the hard and soft clauses. Note you can 
           use/change the buildSATsolver method */
  

  uint64_t cost = maxsat_formula->nSoft(); // this will store the current bound we are exploring

  // This will store the variables in the cardinality constraint
  vec<Lit> cardinality_variables; 
  relaxFormula(cardinality_variables);
  vec<Lit> assumptions;

  Solver* sat_solver = buildSATSolver();

  for(;;){

    // the SAT solver will return either l_False (unsatisfiable) or l_True (satisfiable)
    res = searchSATSolver(sat_solver, assumptions);

    if (res == l_True){
      // SAT solver returned satisfiable; What does this mean?
      //cost = dec(cost);
      cost = computeCostModel(sat_solver->model);
      cost = dec(cost);
      // for (int i = 0; i < active_soft.size(); i++) {
      //   if (solver.value(getSoftClause(i)) == l_True) cost = dec(cost);
      // }

      delete sat_solver;
      sat_solver = buildSATSolver();

      /* How to encode x_1 + ... + x_n <= k?
       * You can use the following code: */
      Encoder *encoder = new Encoder();
      encoder->encodeCardinality(sat_solver, cardinality_variables, cost);

       printf("c ub %llu\n",cost+1);

    } else {
      // SAT solver returned unsatisfiable; What does this mean?
      // (*TODO*) fill the rest...

      // Don't forget to rebuild the SAT solver and update the assumption vector!
      // delete sat_solver;
      // sat_solver = buildSATSolver();

      //  How to encode x_1 + ... + x_n <= k?
      //  * You can use the following code: 
      // Encoder *encoder = new Encoder();
      // encoder->encodeCardinality(sat_solver, cardinality_variables, cost+1);

      printf("o %llu\n",cost+1);

      /* 'sat_solver': SAT solver should be build before 
       * 'cardinality_variables': should have the variables of the cardinality constraint
       * 'cost': should have the cost we are looking for */
      return _OPTIMUM_;
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

void Basic::relaxFormula(vec<Lit> &cardinality_variables) {
  /* We relax the formula by creating a literal r_i and adding it as a relaxation 
   * variable; we also add him as an assumption variable with \not r_i. This 
   * allows the solver to assume that all relaxation variables are initially set 
   * to False.
   */
  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    Lit l = maxsat_formula->newLiteral();
    Soft &s = getSoftClause(i);
    s.relaxation_vars.push(l);
    s.assumption_var = l;
    cardinality_variables.push(l);
  }
}
