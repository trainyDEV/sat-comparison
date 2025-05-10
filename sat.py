import time
from typing import List, Tuple, Dict, Set

CNF = List[List[int]]

class DPLLSolver:
    def __init__(self, cnf: CNF):
        self.cnf = cnf
        self.assignment = {}

    def simplify(self, cnf: CNF, literal: int) -> CNF:
        return [clause for clause in [
            [l for l in clause if l != -literal]
            for clause in cnf if literal not in clause
        ] if clause]

    def unit_propagate(self, cnf: CNF) -> Tuple[CNF, Dict[int, bool]]:
        assignment = {}
        while True:
            unit_clauses = [c for c in cnf if len(c) == 1]
            if not unit_clauses:
                return cnf, assignment
            for clause in unit_clauses:
                unit = clause[0]
                cnf = self.simplify(cnf, unit)
                assignment[abs(unit)] = unit > 0
                if [] in cnf:
                    return None, None

    def dpll(self, cnf: CNF, assignment: Dict[int, bool]) -> bool:
        cnf, new_assignment = self.unit_propagate(cnf)
        if cnf is None:
            return False
        assignment.update(new_assignment)
        if not cnf:
            return True

        literal = abs(cnf[0][0])
        for value in [literal, -literal]:
            new_cnf = self.simplify(cnf, value)
            if self.dpll(new_cnf, {**assignment, abs(value): value > 0}):
                return True
        return False

    def solve(self, cnf: CNF) -> bool:
        return self.dpll(cnf.copy(), {})

class DPSolver:
    def solve(self, cnf: CNF) -> bool:
        cnf = [clause.copy() for clause in cnf]
        while True:
            for clause in cnf:
                if not clause:
                    return False
                if len(clause) == 1:
                    lit = clause[0]
                    cnf = [[l for l in c if l != -lit] for c in cnf if lit not in c]
                    break
            else:
                break
        if not cnf:
            return True

        var = abs(cnf[0][0])
        return (self.solve(cnf + [[var]]) or
                self.solve(cnf + [[-var]]))

class ResolutionSolver:
    def solve(self, cnf: CNF) -> bool:
        clauses = [frozenset(c) for c in cnf]
        seen = set(clauses)

        while True:
            new_clauses = set()
            for ci in clauses:
                for cj in clauses:
                    if ci == cj:
                        continue
                    resolvents = self.resolve(ci, cj)
                    if any(len(r) == 0 for r in resolvents):
                        return False
                    new_clauses.update(resolvents)

            if new_clauses.issubset(seen):
                return True
            clauses = list(seen | new_clauses)
            seen.update(new_clauses)

    def resolve(self, ci: Set[int], cj: Set[int]) -> List[Set[int]]:
        return [frozenset((ci | cj) - {l, -l})
                for l in ci if -l in cj]

def benchmark(solvers: Dict[str, type], cnf: CNF, runs: int = 5) -> Dict[str, Dict]:
    results = {}
    for name, SolverClass in solvers.items():
        times = []
        for _ in range(runs):
            solver = SolverClass(cnf) if name == 'DPLL' else SolverClass()
            start = time.perf_counter()
            result = solver.solve(cnf)
            times.append(time.perf_counter() - start)
        avg_time = sum(times) / runs
        avg_time_ms = (sum(times) / runs) * 1000
        results[name] = {
            'time': avg_time,
            'time_ms': avg_time_ms,
            'result': result,
            'clauses': len(cnf),
            'variables': len({abs(l) for clause in cnf for l in clause})
        }
    return results

# Test cases
sat_cnf = [[1, 2], [-1, 2], [1, -2]]
unsat_cnf = [[1], [-1]]
medium_cnf = [[1, 2, 3], [-1, 4], [-2, -3], [-4, 5], [-5, 6], [-6, 7], [-7]]
# UNUSED TEST CASES (debug purposes)
conflict_cnf = [[1], [-1, 2], [-2, 3], [-3, 1]]
forced_false = [[1], [2], [-1, -2], [-1], [-2]]
circular_sat = [[-1, 2], [-2, 3], [-3, 1], [4]]

solvers = {
    'DPLL': DPLLSolver,
    'DP': DPSolver,
    'Resolution': ResolutionSolver
}

print("Testing SAT case:", benchmark(solvers, sat_cnf))
print("Testing UNSAT case:", benchmark(solvers, unsat_cnf))
print("Testing Medium case:", benchmark(solvers, medium_cnf))
