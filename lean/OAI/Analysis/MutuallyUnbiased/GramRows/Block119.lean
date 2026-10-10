import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow12160 : Integer.Sparse Key := [(key2392, 1), (key2390, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2440, 1), (key2437, 1), (key2440, 1), (key2406, 1), (key2437, 1), (key2406, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2563, 1), (key2554, 1), (key2563, 1), (key2543, 1), (key2554, 1), (key2543, 1), (key2392, -2), (key2392, -2), (key2381, -2), (key2440, -2), (key2440, -2), (key2409, -2), (key2522, -2), (key2506, -2), (key2522, -2), (key2482, -2), (key2506, -2), (key2482, -2)]

theorem rawRowCheck12160 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form21 = rawRow12160 := by decide +kernel

def row12160 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

theorem rowCheck12160 : row12160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12160 := by decide +kernel

theorem rowEval12160 (x : Key → ℝ) : Integer.Sparse.eval row12160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12160, Integer.Sparse.eval_collectBalanced, rawRowCheck12160]

def rawRow12161 : Integer.Sparse Key := [(key2406, 1), (key2406, 1), (key2480, 1), (key2480, 1), (key2543, 1), (key2543, 1), (key2378, 1), (key2378, 1), (key2503, 1), (key2503, 1), (key2554, 1), (key2554, 1), (key2390, 1), (key2390, 1), (key2437, 1), (key2437, 1), (key2563, 1), (key2563, 1), (key2392, 1), (key2392, 1), (key2440, 1), (key2440, 1), (key2522, 1), (key2522, 1), (key2409, -2), (key2482, -2), (key2482, -2), (key2381, -2), (key2506, -2), (key2506, -2), (key2392, -2), (key2392, -2), (key2440, -2), (key2440, -2), (key2522, -2), (key2522, -2)]

theorem rawRowCheck12161 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form21 = rawRow12161 := by decide +kernel

def row12161 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

theorem rowCheck12161 : row12161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12161 := by decide +kernel

theorem rowEval12161 (x : Key → ℝ) : Integer.Sparse.eval row12161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12161, Integer.Sparse.eval_collectBalanced, rawRowCheck12161]

def rawRow12162 : Integer.Sparse Key := [(key2480, 1), (key2543, 1), (key2406, 1), (key2543, 1), (key2406, 1), (key2480, 1), (key2503, 1), (key2554, 1), (key2378, 1), (key2554, 1), (key2378, 1), (key2503, 1), (key2437, 1), (key2563, 1), (key2390, 1), (key2563, 1), (key2390, 1), (key2437, 1), (key2440, 1), (key2522, 1), (key2392, 1), (key2522, 1), (key2392, 1), (key2440, 1), (key2482, -2), (key2409, -2), (key2482, -2), (key2506, -2), (key2381, -2), (key2506, -2), (key2440, -2), (key2522, -2), (key2392, -2), (key2522, -2), (key2392, -2), (key2440, -2)]

theorem rawRowCheck12162 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form21 = rawRow12162 := by decide +kernel

def row12162 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

theorem rowCheck12162 : row12162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12162 := by decide +kernel

theorem rowEval12162 (x : Key → ℝ) : Integer.Sparse.eval row12162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12162, Integer.Sparse.eval_collectBalanced, rawRowCheck12162]

def rawRow12163 : Integer.Sparse Key := [(key2543, 1), (key2480, 1), (key2543, 1), (key2406, 1), (key2480, 1), (key2406, 1), (key2554, 1), (key2503, 1), (key2554, 1), (key2378, 1), (key2503, 1), (key2378, 1), (key2563, 1), (key2437, 1), (key2563, 1), (key2390, 1), (key2437, 1), (key2390, 1), (key2522, 1), (key2440, 1), (key2522, 1), (key2392, 1), (key2440, 1), (key2392, 1), (key2482, -2), (key2482, -2), (key2409, -2), (key2506, -2), (key2506, -2), (key2381, -2), (key2522, -2), (key2440, -2), (key2522, -2), (key2392, -2), (key2440, -2), (key2392, -2)]

theorem rawRowCheck12163 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form21 = rawRow12163 := by decide +kernel

def row12163 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

theorem rowCheck12163 : row12163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12163 := by decide +kernel

theorem rowEval12163 (x : Key → ℝ) : Integer.Sparse.eval row12163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form21) x := by
  rw [rowCheck12163, Integer.Sparse.eval_collectBalanced, rawRowCheck12163]

def rawRow12164 : Integer.Sparse Key := [(key2437, 1), (key2440, 1), (key2503, 1), (key2522, 1), (key2554, 1), (key2563, 1), (key2390, 1), (key2392, 1), (key2480, 1), (key2522, 1), (key2543, 1), (key2563, 1), (key2378, 1), (key2392, 1), (key2406, 1), (key2440, 1), (key2543, 1), (key2554, 1), (key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2440, -2), (key2506, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2522, -2), (key2381, -2), (key2392, -2), (key2409, -2), (key2440, -2), (key2482, -2), (key2506, -2)]

theorem rawRowCheck12164 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form21 = rawRow12164 := by decide +kernel

def row12164 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

theorem rowCheck12164 : row12164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12164 := by decide +kernel

theorem rowEval12164 (x : Key → ℝ) : Integer.Sparse.eval row12164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12164, Integer.Sparse.eval_collectBalanced, rawRowCheck12164]

def rawRow12165 : Integer.Sparse Key := [(key2440, 1), (key2437, 1), (key2522, 1), (key2503, 1), (key2563, 1), (key2554, 1), (key2392, 1), (key2390, 1), (key2522, 1), (key2480, 1), (key2563, 1), (key2543, 1), (key2392, 1), (key2378, 1), (key2440, 1), (key2406, 1), (key2554, 1), (key2543, 1), (key2390, 1), (key2378, 1), (key2437, 1), (key2406, 1), (key2503, 1), (key2480, 1), (key2440, -2), (key2522, -2), (key2506, -2), (key2392, -2), (key2522, -2), (key2482, -2), (key2392, -2), (key2381, -2), (key2440, -2), (key2409, -2), (key2506, -2), (key2482, -2)]

theorem rawRowCheck12165 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form21 = rawRow12165 := by decide +kernel

def row12165 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

theorem rowCheck12165 : row12165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12165 := by decide +kernel

theorem rowEval12165 (x : Key → ℝ) : Integer.Sparse.eval row12165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12165, Integer.Sparse.eval_collectBalanced, rawRowCheck12165]

def rawRow12166 : Integer.Sparse Key := [(key2503, 1), (key2554, 1), (key2437, 1), (key2563, 1), (key2440, 1), (key2522, 1), (key2480, 1), (key2543, 1), (key2390, 1), (key2563, 1), (key2392, 1), (key2522, 1), (key2406, 1), (key2543, 1), (key2378, 1), (key2554, 1), (key2392, 1), (key2440, 1), (key2406, 1), (key2480, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2437, 1), (key2506, -2), (key2440, -2), (key2522, -2), (key2482, -2), (key2392, -2), (key2522, -2), (key2409, -2), (key2482, -2), (key2381, -2), (key2506, -2), (key2392, -2), (key2440, -2)]

theorem rawRowCheck12166 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form21 = rawRow12166 := by decide +kernel

def row12166 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

theorem rowCheck12166 : row12166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12166 := by decide +kernel

theorem rowEval12166 (x : Key → ℝ) : Integer.Sparse.eval row12166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12166, Integer.Sparse.eval_collectBalanced, rawRowCheck12166]

def rawRow12167 : Integer.Sparse Key := [(key2554, 1), (key2503, 1), (key2563, 1), (key2437, 1), (key2522, 1), (key2440, 1), (key2543, 1), (key2480, 1), (key2563, 1), (key2390, 1), (key2522, 1), (key2392, 1), (key2543, 1), (key2406, 1), (key2554, 1), (key2378, 1), (key2440, 1), (key2392, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2437, 1), (key2390, 1), (key2506, -2), (key2522, -2), (key2440, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2409, -2), (key2506, -2), (key2381, -2), (key2440, -2), (key2392, -2)]

theorem rawRowCheck12167 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form21 = rawRow12167 := by decide +kernel

def row12167 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

theorem rowCheck12167 : row12167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12167 := by decide +kernel

theorem rowEval12167 (x : Key → ℝ) : Integer.Sparse.eval row12167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form21) x := by
  rw [rowCheck12167, Integer.Sparse.eval_collectBalanced, rawRowCheck12167]

def rawRow12168 : Integer.Sparse Key := [(key2522, 1), (key2563, 1), (key2440, 1), (key2554, 1), (key2437, 1), (key2503, 1), (key2522, 1), (key2563, 1), (key2392, 1), (key2543, 1), (key2390, 1), (key2480, 1), (key2440, 1), (key2554, 1), (key2392, 1), (key2543, 1), (key2378, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2390, 1), (key2480, 1), (key2378, 1), (key2406, 1), (key2522, -2), (key2440, -2), (key2506, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2440, -2), (key2506, -2), (key2392, -2), (key2482, -2), (key2381, -2), (key2409, -2)]

theorem rawRowCheck12168 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form21 = rawRow12168 := by decide +kernel

def row12168 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

theorem rowCheck12168 : row12168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12168 := by decide +kernel

theorem rowEval12168 (x : Key → ℝ) : Integer.Sparse.eval row12168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12168, Integer.Sparse.eval_collectBalanced, rawRowCheck12168]

def rawRow12169 : Integer.Sparse Key := [(key2563, 1), (key2522, 1), (key2554, 1), (key2440, 1), (key2503, 1), (key2437, 1), (key2563, 1), (key2522, 1), (key2543, 1), (key2392, 1), (key2480, 1), (key2390, 1), (key2554, 1), (key2440, 1), (key2543, 1), (key2392, 1), (key2406, 1), (key2378, 1), (key2503, 1), (key2437, 1), (key2480, 1), (key2390, 1), (key2406, 1), (key2378, 1), (key2522, -2), (key2506, -2), (key2440, -2), (key2522, -2), (key2482, -2), (key2392, -2), (key2506, -2), (key2440, -2), (key2482, -2), (key2392, -2), (key2409, -2), (key2381, -2)]

theorem rawRowCheck12169 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form21 = rawRow12169 := by decide +kernel

def row12169 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

theorem rowCheck12169 : row12169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12169 := by decide +kernel

theorem rowEval12169 (x : Key → ℝ) : Integer.Sparse.eval row12169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form21) x := by
  rw [rowCheck12169, Integer.Sparse.eval_collectBalanced, rawRowCheck12169]

def rawRow12170 : Integer.Sparse Key := [(key2406, -2), (key2406, -2), (key2409, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2437, -2), (key2440, -2), (key2440, -2), (key2409, -2), (key2440, -2), (key2440, -2), (key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2506, 1), (key2506, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2506, 1), (key2506, 1), (key2522, 1), (key2522, 1)]

theorem rawRowCheck12170 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form22 = rawRow12170 := by decide +kernel

def row12170 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

theorem rowCheck12170 : row12170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12170 := by decide +kernel

theorem rowEval12170 (x : Key → ℝ) : Integer.Sparse.eval row12170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12170, Integer.Sparse.eval_collectBalanced, rawRowCheck12170]

def rawRow12171 : Integer.Sparse Key := [(key2406, -2), (key2409, -2), (key2406, -2), (key2437, -2), (key2440, -2), (key2406, -2), (key2440, -2), (key2406, -2), (key2437, -2), (key2440, -2), (key2409, -2), (key2440, -2), (key2480, 1), (key2482, 1), (key2472, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2503, 1), (key2506, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2506, 1), (key2522, 1), (key2482, 1), (key2522, 1), (key2482, 1), (key2506, 1)]

theorem rawRowCheck12171 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form22 = rawRow12171 := by decide +kernel

def row12171 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

theorem rowCheck12171 : row12171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12171 := by decide +kernel

theorem rowEval12171 (x : Key → ℝ) : Integer.Sparse.eval row12171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12171, Integer.Sparse.eval_collectBalanced, rawRowCheck12171]

def rawRow12172 : Integer.Sparse Key := [(key2409, -2), (key2406, -2), (key2406, -2), (key2440, -2), (key2437, -2), (key2440, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2440, -2), (key2440, -2), (key2409, -2), (key2482, 1), (key2480, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2506, 1), (key2503, 1), (key2506, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2482, 1), (key2506, 1), (key2482, 1)]

theorem rawRowCheck12172 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form22 = rawRow12172 := by decide +kernel

def row12172 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

theorem rowCheck12172 : row12172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12172 := by decide +kernel

theorem rowEval12172 (x : Key → ℝ) : Integer.Sparse.eval row12172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12172, Integer.Sparse.eval_collectBalanced, rawRowCheck12172]

def rawRow12173 : Integer.Sparse Key := [(key2437, -2), (key2440, -2), (key2440, -2), (key2406, -2), (key2409, -2), (key2406, -2), (key2440, -2), (key2409, -2), (key2440, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2503, 1), (key2506, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2480, 1), (key2482, 1), (key2480, 1), (key2522, 1), (key2482, 1), (key2522, 1), (key2472, 1), (key2482, 1), (key2472, 1), (key2506, 1), (key2482, 1), (key2506, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2503, 1)]

theorem rawRowCheck12173 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form22 = rawRow12173 := by decide +kernel

def row12173 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

theorem rowCheck12173 : row12173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12173 := by decide +kernel

theorem rowEval12173 (x : Key → ℝ) : Integer.Sparse.eval row12173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12173, Integer.Sparse.eval_collectBalanced, rawRowCheck12173]

def rawRow12174 : Integer.Sparse Key := [(key2440, -2), (key2437, -2), (key2440, -2), (key2409, -2), (key2406, -2), (key2440, -2), (key2406, -2), (key2440, -2), (key2409, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2506, 1), (key2503, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2482, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2506, 1), (key2482, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2503, 1), (key2480, 1)]

theorem rawRowCheck12174 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form22 = rawRow12174 := by decide +kernel

def row12174 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

theorem rowCheck12174 : row12174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12174 := by decide +kernel

theorem rowEval12174 (x : Key → ℝ) : Integer.Sparse.eval row12174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12174, Integer.Sparse.eval_collectBalanced, rawRowCheck12174]

def rawRow12175 : Integer.Sparse Key := [(key2440, -2), (key2440, -2), (key2437, -2), (key2440, -2), (key2440, -2), (key2409, -2), (key2409, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2406, -2), (key2522, 1), (key2522, 1), (key2506, 1), (key2506, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2480, 1), (key2480, 1), (key2506, 1), (key2506, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2480, 1), (key2480, 1), (key2472, 1), (key2472, 1)]

theorem rawRowCheck12175 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form22 = rawRow12175 := by decide +kernel

def row12175 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

theorem rowCheck12175 : row12175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12175 := by decide +kernel

theorem rowEval12175 (x : Key → ℝ) : Integer.Sparse.eval row12175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12175, Integer.Sparse.eval_collectBalanced, rawRowCheck12175]

def rawRow12176 : Integer.Sparse Key := [(key2378, -2), (key2378, -2), (key2381, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2506, -2), (key2506, -2), (key2538, -2), (key2554, -2), (key2554, -2), (key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2392, 1), (key2392, 1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2440, 1), (key2440, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2543, 1), (key2543, 1), (key2554, 1), (key2554, 1), (key2563, 1), (key2563, 1)]

theorem rawRowCheck12176 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form22 = rawRow12176 := by decide +kernel

def row12176 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck12176 : row12176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12176 := by decide +kernel

theorem rowEval12176 (x : Key → ℝ) : Integer.Sparse.eval row12176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12176, Integer.Sparse.eval_collectBalanced, rawRowCheck12176]

def rawRow12177 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2378, -2), (key2503, -2), (key2506, -2), (key2472, -2), (key2506, -2), (key2472, -2), (key2503, -2), (key2554, -2), (key2538, -2), (key2554, -2), (key2390, 1), (key2392, 1), (key2378, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2437, 1), (key2440, 1), (key2406, 1), (key2440, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2554, 1), (key2563, 1), (key2543, 1), (key2563, 1), (key2543, 1), (key2554, 1)]

theorem rawRowCheck12177 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form22 = rawRow12177 := by decide +kernel

def row12177 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck12177 : row12177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12177 := by decide +kernel

theorem rowEval12177 (x : Key → ℝ) : Integer.Sparse.eval row12177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12177, Integer.Sparse.eval_collectBalanced, rawRowCheck12177]

def rawRow12178 : Integer.Sparse Key := [(key2381, -2), (key2378, -2), (key2378, -2), (key2506, -2), (key2503, -2), (key2506, -2), (key2472, -2), (key2503, -2), (key2472, -2), (key2554, -2), (key2554, -2), (key2538, -2), (key2392, 1), (key2390, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2440, 1), (key2437, 1), (key2440, 1), (key2406, 1), (key2437, 1), (key2406, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2563, 1), (key2554, 1), (key2563, 1), (key2543, 1), (key2554, 1), (key2543, 1)]

theorem rawRowCheck12178 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form22 = rawRow12178 := by decide +kernel

def row12178 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck12178 : row12178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12178 := by decide +kernel

theorem rowEval12178 (x : Key → ℝ) : Integer.Sparse.eval row12178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12178, Integer.Sparse.eval_collectBalanced, rawRowCheck12178]

def rawRow12179 : Integer.Sparse Key := [(key2472, -2), (key2472, -2), (key2538, -2), (key2378, -2), (key2378, -2), (key2503, -2), (key2503, -2), (key2554, -2), (key2554, -2), (key2381, -2), (key2506, -2), (key2506, -2), (key2406, 1), (key2406, 1), (key2480, 1), (key2480, 1), (key2543, 1), (key2543, 1), (key2378, 1), (key2378, 1), (key2503, 1), (key2503, 1), (key2554, 1), (key2554, 1), (key2390, 1), (key2390, 1), (key2437, 1), (key2437, 1), (key2563, 1), (key2563, 1), (key2392, 1), (key2392, 1), (key2440, 1), (key2440, 1), (key2522, 1), (key2522, 1)]

theorem rawRowCheck12179 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form22 = rawRow12179 := by decide +kernel

def row12179 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck12179 : row12179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12179 := by decide +kernel

theorem rowEval12179 (x : Key → ℝ) : Integer.Sparse.eval row12179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12179, Integer.Sparse.eval_collectBalanced, rawRowCheck12179]

def rawRow12180 : Integer.Sparse Key := [(key2472, -2), (key2538, -2), (key2472, -2), (key2503, -2), (key2554, -2), (key2378, -2), (key2554, -2), (key2378, -2), (key2503, -2), (key2506, -2), (key2381, -2), (key2506, -2), (key2480, 1), (key2543, 1), (key2406, 1), (key2543, 1), (key2406, 1), (key2480, 1), (key2503, 1), (key2554, 1), (key2378, 1), (key2554, 1), (key2378, 1), (key2503, 1), (key2437, 1), (key2563, 1), (key2390, 1), (key2563, 1), (key2390, 1), (key2437, 1), (key2440, 1), (key2522, 1), (key2392, 1), (key2522, 1), (key2392, 1), (key2440, 1)]

theorem rawRowCheck12180 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form22 = rawRow12180 := by decide +kernel

def row12180 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck12180 : row12180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12180 := by decide +kernel

theorem rowEval12180 (x : Key → ℝ) : Integer.Sparse.eval row12180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12180, Integer.Sparse.eval_collectBalanced, rawRowCheck12180]

def rawRow12181 : Integer.Sparse Key := [(key2538, -2), (key2472, -2), (key2472, -2), (key2554, -2), (key2503, -2), (key2554, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2506, -2), (key2506, -2), (key2381, -2), (key2543, 1), (key2480, 1), (key2543, 1), (key2406, 1), (key2480, 1), (key2406, 1), (key2554, 1), (key2503, 1), (key2554, 1), (key2378, 1), (key2503, 1), (key2378, 1), (key2563, 1), (key2437, 1), (key2563, 1), (key2390, 1), (key2437, 1), (key2390, 1), (key2522, 1), (key2440, 1), (key2522, 1), (key2392, 1), (key2440, 1), (key2392, 1)]

theorem rawRowCheck12181 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form22 = rawRow12181 := by decide +kernel

def row12181 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck12181 : row12181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12181 := by decide +kernel

theorem rowEval12181 (x : Key → ℝ) : Integer.Sparse.eval row12181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form22) x := by
  rw [rowCheck12181, Integer.Sparse.eval_collectBalanced, rawRowCheck12181]

def rawRow12182 : Integer.Sparse Key := [(key2503, -2), (key2506, -2), (key2554, -2), (key2378, -2), (key2381, -2), (key2472, -2), (key2506, -2), (key2538, -2), (key2554, -2), (key2378, -2), (key2472, -2), (key2503, -2), (key2437, 1), (key2440, 1), (key2503, 1), (key2522, 1), (key2554, 1), (key2563, 1), (key2390, 1), (key2392, 1), (key2480, 1), (key2522, 1), (key2543, 1), (key2563, 1), (key2378, 1), (key2392, 1), (key2406, 1), (key2440, 1), (key2543, 1), (key2554, 1), (key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1)]

theorem rawRowCheck12182 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form22 = rawRow12182 := by decide +kernel

def row12182 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck12182 : row12182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12182 := by decide +kernel

theorem rowEval12182 (x : Key → ℝ) : Integer.Sparse.eval row12182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12182, Integer.Sparse.eval_collectBalanced, rawRowCheck12182]

def rawRow12183 : Integer.Sparse Key := [(key2506, -2), (key2503, -2), (key2554, -2), (key2381, -2), (key2378, -2), (key2506, -2), (key2472, -2), (key2554, -2), (key2538, -2), (key2378, -2), (key2503, -2), (key2472, -2), (key2440, 1), (key2437, 1), (key2522, 1), (key2503, 1), (key2563, 1), (key2554, 1), (key2392, 1), (key2390, 1), (key2522, 1), (key2480, 1), (key2563, 1), (key2543, 1), (key2392, 1), (key2378, 1), (key2440, 1), (key2406, 1), (key2554, 1), (key2543, 1), (key2390, 1), (key2378, 1), (key2437, 1), (key2406, 1), (key2503, 1), (key2480, 1)]

theorem rawRowCheck12183 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form22 = rawRow12183 := by decide +kernel

def row12183 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck12183 : row12183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12183 := by decide +kernel

theorem rowEval12183 (x : Key → ℝ) : Integer.Sparse.eval row12183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12183, Integer.Sparse.eval_collectBalanced, rawRowCheck12183]

def rawRow12184 : Integer.Sparse Key := [(key2503, -2), (key2554, -2), (key2506, -2), (key2472, -2), (key2538, -2), (key2378, -2), (key2554, -2), (key2381, -2), (key2506, -2), (key2472, -2), (key2378, -2), (key2503, -2), (key2503, 1), (key2554, 1), (key2437, 1), (key2563, 1), (key2440, 1), (key2522, 1), (key2480, 1), (key2543, 1), (key2390, 1), (key2563, 1), (key2392, 1), (key2522, 1), (key2406, 1), (key2543, 1), (key2378, 1), (key2554, 1), (key2392, 1), (key2440, 1), (key2406, 1), (key2480, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2437, 1)]

theorem rawRowCheck12184 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form22 = rawRow12184 := by decide +kernel

def row12184 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck12184 : row12184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12184 := by decide +kernel

theorem rowEval12184 (x : Key → ℝ) : Integer.Sparse.eval row12184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12184, Integer.Sparse.eval_collectBalanced, rawRowCheck12184]

def rawRow12185 : Integer.Sparse Key := [(key2554, -2), (key2503, -2), (key2506, -2), (key2538, -2), (key2472, -2), (key2554, -2), (key2378, -2), (key2506, -2), (key2381, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2554, 1), (key2503, 1), (key2563, 1), (key2437, 1), (key2522, 1), (key2440, 1), (key2543, 1), (key2480, 1), (key2563, 1), (key2390, 1), (key2522, 1), (key2392, 1), (key2543, 1), (key2406, 1), (key2554, 1), (key2378, 1), (key2440, 1), (key2392, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2437, 1), (key2390, 1)]

theorem rawRowCheck12185 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form22 = rawRow12185 := by decide +kernel

def row12185 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck12185 : row12185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12185 := by decide +kernel

theorem rowEval12185 (x : Key → ℝ) : Integer.Sparse.eval row12185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form22) x := by
  rw [rowCheck12185, Integer.Sparse.eval_collectBalanced, rawRowCheck12185]

def rawRow12186 : Integer.Sparse Key := [(key2506, -2), (key2554, -2), (key2503, -2), (key2506, -2), (key2554, -2), (key2381, -2), (key2538, -2), (key2378, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2522, 1), (key2563, 1), (key2440, 1), (key2554, 1), (key2437, 1), (key2503, 1), (key2522, 1), (key2563, 1), (key2392, 1), (key2543, 1), (key2390, 1), (key2480, 1), (key2440, 1), (key2554, 1), (key2392, 1), (key2543, 1), (key2378, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2390, 1), (key2480, 1), (key2378, 1), (key2406, 1)]

theorem rawRowCheck12186 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form22 = rawRow12186 := by decide +kernel

def row12186 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck12186 : row12186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12186 := by decide +kernel

theorem rowEval12186 (x : Key → ℝ) : Integer.Sparse.eval row12186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12186, Integer.Sparse.eval_collectBalanced, rawRowCheck12186]

def rawRow12187 : Integer.Sparse Key := [(key2554, -2), (key2506, -2), (key2503, -2), (key2554, -2), (key2506, -2), (key2538, -2), (key2381, -2), (key2472, -2), (key2378, -2), (key2503, -2), (key2472, -2), (key2378, -2), (key2563, 1), (key2522, 1), (key2554, 1), (key2440, 1), (key2503, 1), (key2437, 1), (key2563, 1), (key2522, 1), (key2543, 1), (key2392, 1), (key2480, 1), (key2390, 1), (key2554, 1), (key2440, 1), (key2543, 1), (key2392, 1), (key2406, 1), (key2378, 1), (key2503, 1), (key2437, 1), (key2480, 1), (key2390, 1), (key2406, 1), (key2378, 1)]

theorem rawRowCheck12187 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form22 = rawRow12187 := by decide +kernel

def row12187 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck12187 : row12187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12187 := by decide +kernel

theorem rowEval12187 (x : Key → ℝ) : Integer.Sparse.eval row12187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form22) x := by
  rw [rowCheck12187, Integer.Sparse.eval_collectBalanced, rawRowCheck12187]

def rawRow12188 : Integer.Sparse Key := [(key2362, -4), (key2365, -4), (key2365, -4), (key2365, -4), (key2365, -4), (key2367, -4), (key2457, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2460, 2), (key2460, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2525, 2)]

theorem rawRowCheck12188 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form23 = rawRow12188 := by decide +kernel

def row12188 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

theorem rowCheck12188 : row12188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12188 := by decide +kernel

theorem rowEval12188 (x : Key → ℝ) : Integer.Sparse.eval row12188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12188, Integer.Sparse.eval_collectBalanced, rawRowCheck12188]

def rawRow12189 : Integer.Sparse Key := [(key2365, -4), (key2362, -4), (key2365, -4), (key2365, -4), (key2367, -4), (key2365, -4), (key2460, 2), (key2457, 2), (key2460, 2), (key2521, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2525, 2), (key2460, 2), (key2521, 2)]

theorem rawRowCheck12189 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form23 = rawRow12189 := by decide +kernel

def row12189 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

theorem rowCheck12189 : row12189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12189 := by decide +kernel

theorem rowEval12189 (x : Key → ℝ) : Integer.Sparse.eval row12189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12189, Integer.Sparse.eval_collectBalanced, rawRowCheck12189]

def rawRow12190 : Integer.Sparse Key := [(key2365, -4), (key2365, -4), (key2362, -4), (key2367, -4), (key2365, -4), (key2365, -4), (key2460, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2457, 2), (key2525, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2460, 2)]

theorem rawRowCheck12190 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form23 = rawRow12190 := by decide +kernel

def row12190 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

theorem rowCheck12190 : row12190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12190 := by decide +kernel

theorem rowEval12190 (x : Key → ℝ) : Integer.Sparse.eval row12190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12190, Integer.Sparse.eval_collectBalanced, rawRowCheck12190]

def rawRow12191 : Integer.Sparse Key := [(key2365, -4), (key2365, -4), (key2367, -4), (key2362, -4), (key2365, -4), (key2365, -4), (key2521, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2460, 2), (key2525, 2), (key2457, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2460, 2), (key2521, 2)]

theorem rawRowCheck12191 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form23 = rawRow12191 := by decide +kernel

def row12191 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

theorem rowCheck12191 : row12191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12191 := by decide +kernel

theorem rowEval12191 (x : Key → ℝ) : Integer.Sparse.eval row12191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12191, Integer.Sparse.eval_collectBalanced, rawRowCheck12191]

def rawRow12192 : Integer.Sparse Key := [(key2365, -4), (key2367, -4), (key2365, -4), (key2365, -4), (key2362, -4), (key2365, -4), (key2521, 2), (key2525, 2), (key2521, 2), (key2460, 2), (key2525, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2457, 2), (key2521, 2), (key2460, 2)]

theorem rawRowCheck12192 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form23 = rawRow12192 := by decide +kernel

def row12192 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

theorem rowCheck12192 : row12192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12192 := by decide +kernel

theorem rowEval12192 (x : Key → ℝ) : Integer.Sparse.eval row12192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12192, Integer.Sparse.eval_collectBalanced, rawRowCheck12192]

def rawRow12193 : Integer.Sparse Key := [(key2367, -4), (key2365, -4), (key2365, -4), (key2365, -4), (key2365, -4), (key2362, -4), (key2525, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2460, 2), (key2521, 2), (key2521, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2457, 2)]

theorem rawRowCheck12193 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form23 = rawRow12193 := by decide +kernel

def row12193 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

theorem rowCheck12193 : row12193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12193 := by decide +kernel

theorem rowEval12193 (x : Key → ℝ) : Integer.Sparse.eval row12193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12193, Integer.Sparse.eval_collectBalanced, rawRowCheck12193]

def rawRow12194 : Integer.Sparse Key := [(key2457, -4), (key2460, -4), (key2460, -4), (key2521, -4), (key2521, -4), (key2525, -4), (key2362, 2), (key2365, 2), (key2365, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2532, 2), (key2532, 2), (key2562, 2), (key2562, 2), (key2564, 2), (key2564, 2)]

theorem rawRowCheck12194 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form23 = rawRow12194 := by decide +kernel

def row12194 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

theorem rowCheck12194 : row12194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12194 := by decide +kernel

theorem rowEval12194 (x : Key → ℝ) : Integer.Sparse.eval row12194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12194, Integer.Sparse.eval_collectBalanced, rawRowCheck12194]

def rawRow12195 : Integer.Sparse Key := [(key2460, -4), (key2457, -4), (key2460, -4), (key2521, -4), (key2525, -4), (key2521, -4), (key2365, 2), (key2362, 2), (key2365, 2), (key2521, 2), (key2457, 2), (key2521, 2), (key2562, 2), (key2564, 2), (key2532, 2), (key2564, 2), (key2532, 2), (key2562, 2)]

theorem rawRowCheck12195 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form23 = rawRow12195 := by decide +kernel

def row12195 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

theorem rowCheck12195 : row12195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12195 := by decide +kernel

theorem rowEval12195 (x : Key → ℝ) : Integer.Sparse.eval row12195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12195, Integer.Sparse.eval_collectBalanced, rawRowCheck12195]

def rawRow12196 : Integer.Sparse Key := [(key2460, -4), (key2460, -4), (key2457, -4), (key2525, -4), (key2521, -4), (key2521, -4), (key2365, 2), (key2365, 2), (key2362, 2), (key2521, 2), (key2521, 2), (key2457, 2), (key2564, 2), (key2562, 2), (key2564, 2), (key2532, 2), (key2562, 2), (key2532, 2)]

theorem rawRowCheck12196 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form23 = rawRow12196 := by decide +kernel

def row12196 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

theorem rowCheck12196 : row12196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12196 := by decide +kernel

theorem rowEval12196 (x : Key → ℝ) : Integer.Sparse.eval row12196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12196, Integer.Sparse.eval_collectBalanced, rawRowCheck12196]

def rawRow12197 : Integer.Sparse Key := [(key2457, -4), (key2521, -4), (key2521, -4), (key2460, -4), (key2460, -4), (key2525, -4), (key2457, 2), (key2521, 2), (key2521, 2), (key2362, 2), (key2562, 2), (key2562, 2), (key2365, 2), (key2365, 2), (key2521, 2), (key2521, 2), (key2564, 2), (key2564, 2)]

theorem rawRowCheck12197 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form23 = rawRow12197 := by decide +kernel

def row12197 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2525, -4), (key2562, 4), (key2564, 4)]

theorem rowCheck12197 : row12197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12197 := by decide +kernel

theorem rowEval12197 (x : Key → ℝ) : Integer.Sparse.eval row12197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12197, Integer.Sparse.eval_collectBalanced, rawRowCheck12197]

def rawRow12198 : Integer.Sparse Key := [(key2521, -4), (key2457, -4), (key2521, -4), (key2460, -4), (key2525, -4), (key2460, -4), (key2521, 2), (key2457, 2), (key2521, 2), (key2562, 2), (key2362, 2), (key2562, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2564, 2), (key2365, 2), (key2521, 2)]

theorem rawRowCheck12198 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form23 = rawRow12198 := by decide +kernel

def row12198 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2525, -4), (key2562, 4), (key2564, 4)]

theorem rowCheck12198 : row12198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12198 := by decide +kernel

theorem rowEval12198 (x : Key → ℝ) : Integer.Sparse.eval row12198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12198, Integer.Sparse.eval_collectBalanced, rawRowCheck12198]

def rawRow12199 : Integer.Sparse Key := [(key2521, -4), (key2521, -4), (key2457, -4), (key2525, -4), (key2460, -4), (key2460, -4), (key2521, 2), (key2521, 2), (key2457, 2), (key2562, 2), (key2562, 2), (key2362, 2), (key2564, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2365, 2)]

theorem rawRowCheck12199 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form23 = rawRow12199 := by decide +kernel

def row12199 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2525, -4), (key2562, 4), (key2564, 4)]

theorem rowCheck12199 : row12199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12199 := by decide +kernel

theorem rowEval12199 (x : Key → ℝ) : Integer.Sparse.eval row12199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form23) x := by
  rw [rowCheck12199, Integer.Sparse.eval_collectBalanced, rawRowCheck12199]

def rawRow12200 : Integer.Sparse Key := [(key2460, -4), (key2521, -4), (key2525, -4), (key2457, -4), (key2460, -4), (key2521, -4), (key2532, 2), (key2562, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2564, 2), (key2362, 2), (key2365, 2), (key2457, 2), (key2521, 2), (key2532, 2), (key2562, 2)]

theorem rawRowCheck12200 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form23 = rawRow12200 := by decide +kernel

def row12200 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

theorem rowCheck12200 : row12200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12200 := by decide +kernel

theorem rowEval12200 (x : Key → ℝ) : Integer.Sparse.eval row12200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12200, Integer.Sparse.eval_collectBalanced, rawRowCheck12200]

def rawRow12201 : Integer.Sparse Key := [(key2460, -4), (key2525, -4), (key2521, -4), (key2460, -4), (key2457, -4), (key2521, -4), (key2532, 2), (key2564, 2), (key2562, 2), (key2365, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2362, 2), (key2521, 2), (key2457, 2), (key2562, 2), (key2532, 2)]

theorem rawRowCheck12201 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form23 = rawRow12201 := by decide +kernel

def row12201 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

theorem rowCheck12201 : row12201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12201 := by decide +kernel

theorem rowEval12201 (x : Key → ℝ) : Integer.Sparse.eval row12201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12201, Integer.Sparse.eval_collectBalanced, rawRowCheck12201]

def rawRow12202 : Integer.Sparse Key := [(key2521, -4), (key2460, -4), (key2525, -4), (key2457, -4), (key2521, -4), (key2460, -4), (key2562, 2), (key2532, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2564, 2), (key2457, 2), (key2521, 2), (key2362, 2), (key2562, 2), (key2365, 2), (key2521, 2)]

theorem rawRowCheck12202 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form23 = rawRow12202 := by decide +kernel

def row12202 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -2), (key2525, -4), (key2532, 2), (key2562, 4), (key2564, 4)]

theorem rowCheck12202 : row12202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12202 := by decide +kernel

theorem rowEval12202 (x : Key → ℝ) : Integer.Sparse.eval row12202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12202, Integer.Sparse.eval_collectBalanced, rawRowCheck12202]

def rawRow12203 : Integer.Sparse Key := [(key2521, -4), (key2525, -4), (key2460, -4), (key2521, -4), (key2457, -4), (key2460, -4), (key2562, 2), (key2564, 2), (key2532, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2457, 2), (key2562, 2), (key2362, 2), (key2521, 2), (key2365, 2)]

theorem rawRowCheck12203 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form23 = rawRow12203 := by decide +kernel

def row12203 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -2), (key2525, -4), (key2532, 2), (key2562, 4), (key2564, 4)]

theorem rowCheck12203 : row12203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12203 := by decide +kernel

theorem rowEval12203 (x : Key → ℝ) : Integer.Sparse.eval row12203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form23) x := by
  rw [rowCheck12203, Integer.Sparse.eval_collectBalanced, rawRowCheck12203]

def rawRow12204 : Integer.Sparse Key := [(key2525, -4), (key2460, -4), (key2521, -4), (key2460, -4), (key2521, -4), (key2457, -4), (key2564, 2), (key2532, 2), (key2562, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2532, 2), (key2562, 2), (key2365, 2), (key2521, 2), (key2362, 2), (key2457, 2)]

theorem rawRowCheck12204 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form23 = rawRow12204 := by decide +kernel

def row12204 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

theorem rowCheck12204 : row12204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12204 := by decide +kernel

theorem rowEval12204 (x : Key → ℝ) : Integer.Sparse.eval row12204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12204, Integer.Sparse.eval_collectBalanced, rawRowCheck12204]

def rawRow12205 : Integer.Sparse Key := [(key2525, -4), (key2521, -4), (key2460, -4), (key2521, -4), (key2460, -4), (key2457, -4), (key2564, 2), (key2562, 2), (key2532, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2562, 2), (key2532, 2), (key2521, 2), (key2365, 2), (key2457, 2), (key2362, 2)]

theorem rawRowCheck12205 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form23 = rawRow12205 := by decide +kernel

def row12205 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

theorem rowCheck12205 : row12205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12205 := by decide +kernel

theorem rowEval12205 (x : Key → ℝ) : Integer.Sparse.eval row12205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form23) x := by
  rw [rowCheck12205, Integer.Sparse.eval_collectBalanced, rawRowCheck12205]

def rawRow12206 : Integer.Sparse Key := [(key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2)]

theorem rawRowCheck12206 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form0 = rawRow12206 := by decide +kernel

def row12206 : Integer.Sparse Key := [(key1700, 24), (key1851, -24)]

theorem rowCheck12206 : row12206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12206 := by decide +kernel

theorem rowEval12206 (x : Key → ℝ) : Integer.Sparse.eval row12206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12206, Integer.Sparse.eval_collectBalanced, rawRowCheck12206]

def rawRow12207 : Integer.Sparse Key := [(key1277, 2), (key1277, 2), (key1277, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1277, -2), (key1277, -2), (key1277, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1851, -2), (key1851, -2), (key1851, -2)]

theorem rawRowCheck12207 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow12207 := by decide +kernel

def row12207 : Integer.Sparse Key := [(key1700, -6), (key1851, 6)]

theorem rowCheck12207 : row12207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12207 := by decide +kernel

theorem rowEval12207 (x : Key → ℝ) : Integer.Sparse.eval row12207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12207, Integer.Sparse.eval_collectBalanced, rawRowCheck12207]

def rawRow12208 : Integer.Sparse Key := [(key1700, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1277, 2), (key1700, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1700, -2), (key1700, -2), (key1851, -2), (key1277, -2), (key1277, -2), (key1700, -2), (key1700, -2), (key1851, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1700, -2)]

theorem rawRowCheck12208 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form0 = rawRow12208 := by decide +kernel

def row12208 : Integer.Sparse Key := [(key1700, -6), (key1851, 6)]

theorem rowCheck12208 : row12208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12208 := by decide +kernel

theorem rowEval12208 (x : Key → ℝ) : Integer.Sparse.eval row12208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12208, Integer.Sparse.eval_collectBalanced, rawRowCheck12208]

def rawRow12209 : Integer.Sparse Key := [(key1851, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1700, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1277, 2), (key1700, 2), (key1700, -2), (key1851, -2), (key1700, -2), (key1700, -2), (key1851, -2), (key1277, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1700, -2), (key1277, -2), (key1700, -2)]

theorem rawRowCheck12209 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form0 = rawRow12209 := by decide +kernel

def row12209 : Integer.Sparse Key := [(key1700, -6), (key1851, 6)]

theorem rowCheck12209 : row12209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12209 := by decide +kernel

theorem rowEval12209 (x : Key → ℝ) : Integer.Sparse.eval row12209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12209, Integer.Sparse.eval_collectBalanced, rawRowCheck12209]

def rawRow12210 : Integer.Sparse Key := [(key1851, 2), (key1851, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1700, 2), (key1851, 2), (key1277, 2), (key1700, 2), (key1277, 2), (key1851, -2), (key1700, -2), (key1700, -2), (key1851, -2), (key1700, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1277, -2), (key1700, -2), (key1700, -2), (key1277, -2)]

theorem rawRowCheck12210 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form0 = rawRow12210 := by decide +kernel

def row12210 : Integer.Sparse Key := [(key1700, -6), (key1851, 6)]

theorem rowCheck12210 : row12210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12210 := by decide +kernel

theorem rowEval12210 (x : Key → ℝ) : Integer.Sparse.eval row12210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck12210, Integer.Sparse.eval_collectBalanced, rawRowCheck12210]

def rawRow12211 : Integer.Sparse Key := [(key219, -24), (key491, 6), (key491, 6), (key491, 6), (key491, 6)]

theorem rawRowCheck12211 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form1 = rawRow12211 := by decide +kernel

def row12211 : Integer.Sparse Key := [(key219, -24), (key491, 24)]

theorem rowCheck12211 : row12211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12211 := by decide +kernel

theorem rowEval12211 (x : Key → ℝ) : Integer.Sparse.eval row12211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12211, Integer.Sparse.eval_collectBalanced, rawRowCheck12211]

def rawRow12212 : Integer.Sparse Key := [(key491, -24), (key219, 6), (key491, 6), (key491, 6), (key491, 6)]

theorem rawRowCheck12212 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow12212 := by decide +kernel

def row12212 : Integer.Sparse Key := [(key219, 6), (key491, -6)]

theorem rowCheck12212 : row12212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12212 := by decide +kernel

theorem rowEval12212 (x : Key → ℝ) : Integer.Sparse.eval row12212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12212, Integer.Sparse.eval_collectBalanced, rawRowCheck12212]

def rawRow12213 : Integer.Sparse Key := [(key491, -24), (key491, 6), (key219, 6), (key491, 6), (key491, 6)]

theorem rawRowCheck12213 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form1 = rawRow12213 := by decide +kernel

def row12213 : Integer.Sparse Key := [(key219, 6), (key491, -6)]

theorem rowCheck12213 : row12213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12213 := by decide +kernel

theorem rowEval12213 (x : Key → ℝ) : Integer.Sparse.eval row12213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12213, Integer.Sparse.eval_collectBalanced, rawRowCheck12213]

def rawRow12214 : Integer.Sparse Key := [(key491, -24), (key491, 6), (key491, 6), (key219, 6), (key491, 6)]

theorem rawRowCheck12214 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form1 = rawRow12214 := by decide +kernel

def row12214 : Integer.Sparse Key := [(key219, 6), (key491, -6)]

theorem rowCheck12214 : row12214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12214 := by decide +kernel

theorem rowEval12214 (x : Key → ℝ) : Integer.Sparse.eval row12214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12214, Integer.Sparse.eval_collectBalanced, rawRowCheck12214]

def rawRow12215 : Integer.Sparse Key := [(key491, -24), (key491, 6), (key491, 6), (key491, 6), (key219, 6)]

theorem rawRowCheck12215 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form1 = rawRow12215 := by decide +kernel

def row12215 : Integer.Sparse Key := [(key219, 6), (key491, -6)]

theorem rowCheck12215 : row12215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12215 := by decide +kernel

theorem rowEval12215 (x : Key → ℝ) : Integer.Sparse.eval row12215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12215, Integer.Sparse.eval_collectBalanced, rawRowCheck12215]

def rawRow12216 : Integer.Sparse Key := [(key30, -6), (key30, -6), (key30, -6), (key30, -6), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2)]

theorem rawRowCheck12216 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form2 = rawRow12216 := by decide +kernel

def row12216 : Integer.Sparse Key := [(key30, -24), (key110, 24)]

theorem rowCheck12216 : row12216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12216 := by decide +kernel

theorem rowEval12216 (x : Key → ℝ) : Integer.Sparse.eval row12216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12216, Integer.Sparse.eval_collectBalanced, rawRowCheck12216]

def rawRow12217 : Integer.Sparse Key := [(key110, -6), (key110, -6), (key110, -6), (key146, -6), (key30, 2), (key30, 2), (key30, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key146, 2), (key146, 2), (key146, 2)]

theorem rawRowCheck12217 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow12217 := by decide +kernel

def row12217 : Integer.Sparse Key := [(key30, 6), (key110, -6)]

theorem rowCheck12217 : row12217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12217 := by decide +kernel

theorem rowEval12217 (x : Key → ℝ) : Integer.Sparse.eval row12217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12217, Integer.Sparse.eval_collectBalanced, rawRowCheck12217]

def rawRow12218 : Integer.Sparse Key := [(key110, -6), (key110, -6), (key146, -6), (key110, -6), (key110, 2), (key110, 2), (key146, 2), (key30, 2), (key30, 2), (key110, 2), (key110, 2), (key146, 2), (key146, 2), (key30, 2), (key110, 2), (key110, 2)]

theorem rawRowCheck12218 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form2 = rawRow12218 := by decide +kernel

def row12218 : Integer.Sparse Key := [(key30, 6), (key110, -6)]

theorem rowCheck12218 : row12218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12218 := by decide +kernel

theorem rowEval12218 (x : Key → ℝ) : Integer.Sparse.eval row12218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12218, Integer.Sparse.eval_collectBalanced, rawRowCheck12218]

def rawRow12219 : Integer.Sparse Key := [(key110, -6), (key146, -6), (key110, -6), (key110, -6), (key110, 2), (key146, 2), (key110, 2), (key110, 2), (key146, 2), (key30, 2), (key146, 2), (key30, 2), (key110, 2), (key110, 2), (key30, 2), (key110, 2)]

theorem rawRowCheck12219 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form2 = rawRow12219 := by decide +kernel

def row12219 : Integer.Sparse Key := [(key30, 6), (key110, -6)]

theorem rowCheck12219 : row12219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12219 := by decide +kernel

theorem rowEval12219 (x : Key → ℝ) : Integer.Sparse.eval row12219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12219, Integer.Sparse.eval_collectBalanced, rawRowCheck12219]

def rawRow12220 : Integer.Sparse Key := [(key146, -6), (key110, -6), (key110, -6), (key110, -6), (key146, 2), (key110, 2), (key110, 2), (key146, 2), (key110, 2), (key146, 2), (key30, 2), (key110, 2), (key30, 2), (key110, 2), (key110, 2), (key30, 2)]

theorem rawRowCheck12220 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form2 = rawRow12220 := by decide +kernel

def row12220 : Integer.Sparse Key := [(key30, 6), (key110, -6)]

theorem rowCheck12220 : row12220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12220 := by decide +kernel

theorem rowEval12220 (x : Key → ℝ) : Integer.Sparse.eval row12220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12220, Integer.Sparse.eval_collectBalanced, rawRowCheck12220]

def rawRow12221 : Integer.Sparse Key := [(key1483, -6), (key1483, -6), (key1483, -6), (key1483, -6), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2)]

theorem rawRowCheck12221 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form3 = rawRow12221 := by decide +kernel

def row12221 : Integer.Sparse Key := [(key1483, -24), (key1709, 24)]

theorem rowCheck12221 : row12221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12221 := by decide +kernel

theorem rowEval12221 (x : Key → ℝ) : Integer.Sparse.eval row12221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12221, Integer.Sparse.eval_collectBalanced, rawRowCheck12221]

def rawRow12222 : Integer.Sparse Key := [(key1357, -6), (key1709, -6), (key1709, -6), (key1709, -6), (key1357, 2), (key1357, 2), (key1357, 2), (key1483, 2), (key1483, 2), (key1483, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2)]

theorem rawRowCheck12222 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow12222 := by decide +kernel

def row12222 : Integer.Sparse Key := [(key1483, 6), (key1709, -6)]

theorem rowCheck12222 : row12222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12222 := by decide +kernel

theorem rowEval12222 (x : Key → ℝ) : Integer.Sparse.eval row12222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12222, Integer.Sparse.eval_collectBalanced, rawRowCheck12222]

def rawRow12223 : Integer.Sparse Key := [(key1709, -6), (key1357, -6), (key1709, -6), (key1709, -6), (key1483, 2), (key1709, 2), (key1709, 2), (key1357, 2), (key1709, 2), (key1709, 2), (key1357, 2), (key1357, 2), (key1483, 2), (key1483, 2), (key1709, 2), (key1709, 2)]

theorem rawRowCheck12223 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form3 = rawRow12223 := by decide +kernel

def row12223 : Integer.Sparse Key := [(key1483, 6), (key1709, -6)]

theorem rowCheck12223 : row12223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12223 := by decide +kernel

theorem rowEval12223 (x : Key → ℝ) : Integer.Sparse.eval row12223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12223, Integer.Sparse.eval_collectBalanced, rawRowCheck12223]

def rawRow12224 : Integer.Sparse Key := [(key1709, -6), (key1709, -6), (key1357, -6), (key1709, -6), (key1709, 2), (key1483, 2), (key1709, 2), (key1709, 2), (key1357, 2), (key1709, 2), (key1483, 2), (key1709, 2), (key1357, 2), (key1709, 2), (key1357, 2), (key1483, 2)]

theorem rawRowCheck12224 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form3 = rawRow12224 := by decide +kernel

def row12224 : Integer.Sparse Key := [(key1483, 6), (key1709, -6)]

theorem rowCheck12224 : row12224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12224 := by decide +kernel

theorem rowEval12224 (x : Key → ℝ) : Integer.Sparse.eval row12224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12224, Integer.Sparse.eval_collectBalanced, rawRowCheck12224]

def rawRow12225 : Integer.Sparse Key := [(key1709, -6), (key1709, -6), (key1709, -6), (key1357, -6), (key1709, 2), (key1709, 2), (key1483, 2), (key1709, 2), (key1709, 2), (key1357, 2), (key1709, 2), (key1483, 2), (key1709, 2), (key1357, 2), (key1483, 2), (key1357, 2)]

theorem rawRowCheck12225 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form3 = rawRow12225 := by decide +kernel

def row12225 : Integer.Sparse Key := [(key1483, 6), (key1709, -6)]

theorem rowCheck12225 : row12225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12225 := by decide +kernel

theorem rowEval12225 (x : Key → ℝ) : Integer.Sparse.eval row12225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12225, Integer.Sparse.eval_collectBalanced, rawRowCheck12225]

def rawRow12226 : Integer.Sparse Key := [(key1274, -6), (key1274, -6), (key1274, -6), (key1274, -6), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2)]

theorem rawRowCheck12226 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form4 = rawRow12226 := by decide +kernel

def row12226 : Integer.Sparse Key := [(key1274, -24), (key1697, 24)]

theorem rowCheck12226 : row12226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12226 := by decide +kernel

theorem rowEval12226 (x : Key → ℝ) : Integer.Sparse.eval row12226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12226, Integer.Sparse.eval_collectBalanced, rawRowCheck12226]

def rawRow12227 : Integer.Sparse Key := [(key1697, -6), (key1697, -6), (key1697, -6), (key1932, -6), (key1274, 2), (key1274, 2), (key1274, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1932, 2), (key1932, 2), (key1932, 2)]

theorem rawRowCheck12227 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow12227 := by decide +kernel

def row12227 : Integer.Sparse Key := [(key1274, 6), (key1697, -6)]

theorem rowCheck12227 : row12227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12227 := by decide +kernel

theorem rowEval12227 (x : Key → ℝ) : Integer.Sparse.eval row12227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12227, Integer.Sparse.eval_collectBalanced, rawRowCheck12227]

def rawRow12228 : Integer.Sparse Key := [(key1697, -6), (key1697, -6), (key1932, -6), (key1697, -6), (key1697, 2), (key1697, 2), (key1932, 2), (key1274, 2), (key1274, 2), (key1697, 2), (key1697, 2), (key1932, 2), (key1932, 2), (key1274, 2), (key1697, 2), (key1697, 2)]

theorem rawRowCheck12228 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form4 = rawRow12228 := by decide +kernel

def row12228 : Integer.Sparse Key := [(key1274, 6), (key1697, -6)]

theorem rowCheck12228 : row12228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12228 := by decide +kernel

theorem rowEval12228 (x : Key → ℝ) : Integer.Sparse.eval row12228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12228, Integer.Sparse.eval_collectBalanced, rawRowCheck12228]

def rawRow12229 : Integer.Sparse Key := [(key1697, -6), (key1932, -6), (key1697, -6), (key1697, -6), (key1697, 2), (key1932, 2), (key1697, 2), (key1697, 2), (key1932, 2), (key1274, 2), (key1932, 2), (key1274, 2), (key1697, 2), (key1697, 2), (key1274, 2), (key1697, 2)]

theorem rawRowCheck12229 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form4 = rawRow12229 := by decide +kernel

def row12229 : Integer.Sparse Key := [(key1274, 6), (key1697, -6)]

theorem rowCheck12229 : row12229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12229 := by decide +kernel

theorem rowEval12229 (x : Key → ℝ) : Integer.Sparse.eval row12229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12229, Integer.Sparse.eval_collectBalanced, rawRowCheck12229]

def rawRow12230 : Integer.Sparse Key := [(key1932, -6), (key1697, -6), (key1697, -6), (key1697, -6), (key1932, 2), (key1697, 2), (key1697, 2), (key1932, 2), (key1697, 2), (key1932, 2), (key1274, 2), (key1697, 2), (key1274, 2), (key1697, 2), (key1697, 2), (key1274, 2)]

theorem rawRowCheck12230 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form4 = rawRow12230 := by decide +kernel

def row12230 : Integer.Sparse Key := [(key1274, 6), (key1697, -6)]

theorem rowCheck12230 : row12230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12230 := by decide +kernel

theorem rowEval12230 (x : Key → ℝ) : Integer.Sparse.eval row12230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12230, Integer.Sparse.eval_collectBalanced, rawRowCheck12230]

def rawRow12231 : Integer.Sparse Key := [(key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1)]

theorem rawRowCheck12231 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form5 = rawRow12231 := by decide +kernel

def row12231 : Integer.Sparse Key := [(key1485, -24), (key1711, 24)]

theorem rowCheck12231 : row12231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12231 := by decide +kernel

theorem rowEval12231 (x : Key → ℝ) : Integer.Sparse.eval row12231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12231, Integer.Sparse.eval_collectBalanced, rawRowCheck12231]

def rawRow12232 : Integer.Sparse Key := [(key1359, -2), (key1359, -2), (key1359, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1359, 1), (key1359, 1), (key1359, 1), (key1359, 1), (key1359, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1936, 1), (key1936, 1), (key1936, 1), (key1936, 1), (key1936, 1)]

theorem rawRowCheck12232 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form5 = rawRow12232 := by decide +kernel

def row12232 : Integer.Sparse Key := [(key1485, 6), (key1711, -6)]

theorem rowCheck12232 : row12232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12232 := by decide +kernel

theorem rowEval12232 (x : Key → ℝ) : Integer.Sparse.eval row12232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12232, Integer.Sparse.eval_collectBalanced, rawRowCheck12232]

def rawRow12233 : Integer.Sparse Key := [(key1711, -2), (key1711, -2), (key1936, -2), (key1359, -2), (key1359, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1936, -2), (key1359, -2), (key1711, -2), (key1711, -2), (key1485, 1), (key1485, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1936, 1), (key1359, 1), (key1359, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1936, 1), (key1359, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1936, 1), (key1936, 1), (key1359, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1711, 1), (key1711, 1)]

theorem rawRowCheck12233 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form5 = rawRow12233 := by decide +kernel

def row12233 : Integer.Sparse Key := [(key1485, 6), (key1711, -6)]

theorem rowCheck12233 : row12233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12233 := by decide +kernel

theorem rowEval12233 (x : Key → ℝ) : Integer.Sparse.eval row12233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12233, Integer.Sparse.eval_collectBalanced, rawRowCheck12233]

def rawRow12234 : Integer.Sparse Key := [(key1711, -2), (key1936, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1359, -2), (key1936, -2), (key1359, -2), (key1711, -2), (key1711, -2), (key1359, -2), (key1711, -2), (key1711, 1), (key1936, 1), (key1485, 1), (key1936, 1), (key1485, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1359, 1), (key1936, 1), (key1359, 1), (key1711, 1), (key1485, 1), (key1936, 1), (key1359, 1), (key1936, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1711, 1), (key1359, 1), (key1711, 1), (key1359, 1), (key1485, 1)]

theorem rawRowCheck12234 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form5 = rawRow12234 := by decide +kernel

def row12234 : Integer.Sparse Key := [(key1485, 6), (key1711, -6)]

theorem rowCheck12234 : row12234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12234 := by decide +kernel

theorem rowEval12234 (x : Key → ℝ) : Integer.Sparse.eval row12234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12234, Integer.Sparse.eval_collectBalanced, rawRowCheck12234]

def rawRow12235 : Integer.Sparse Key := [(key1936, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1711, -2), (key1936, -2), (key1359, -2), (key1711, -2), (key1359, -2), (key1711, -2), (key1711, -2), (key1359, -2), (key1936, 1), (key1711, 1), (key1936, 1), (key1485, 1), (key1711, 1), (key1485, 1), (key1936, 1), (key1711, 1), (key1936, 1), (key1359, 1), (key1711, 1), (key1359, 1), (key1936, 1), (key1485, 1), (key1936, 1), (key1359, 1), (key1485, 1), (key1359, 1), (key1711, 1), (key1485, 1), (key1711, 1), (key1359, 1), (key1485, 1), (key1359, 1)]

theorem rawRowCheck12235 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form5 = rawRow12235 := by decide +kernel

def row12235 : Integer.Sparse Key := [(key1485, 6), (key1711, -6)]

theorem rowCheck12235 : row12235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12235 := by decide +kernel

theorem rowEval12235 (x : Key → ℝ) : Integer.Sparse.eval row12235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck12235, Integer.Sparse.eval_collectBalanced, rawRowCheck12235]

def rawRow12236 : Integer.Sparse Key := [(key1272, -24), (key1695, 6), (key1695, 6), (key1695, 6), (key1695, 6)]

theorem rawRowCheck12236 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form6 = rawRow12236 := by decide +kernel

def row12236 : Integer.Sparse Key := [(key1272, -24), (key1695, 24)]

theorem rowCheck12236 : row12236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12236 := by decide +kernel

theorem rowEval12236 (x : Key → ℝ) : Integer.Sparse.eval row12236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12236, Integer.Sparse.eval_collectBalanced, rawRowCheck12236]

def rawRow12237 : Integer.Sparse Key := [(key1695, -24), (key1272, 6), (key1695, 6), (key1695, 6), (key1695, 6)]

theorem rawRowCheck12237 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow12237 := by decide +kernel

def row12237 : Integer.Sparse Key := [(key1272, 6), (key1695, -6)]

theorem rowCheck12237 : row12237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12237 := by decide +kernel

theorem rowEval12237 (x : Key → ℝ) : Integer.Sparse.eval row12237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12237, Integer.Sparse.eval_collectBalanced, rawRowCheck12237]

def rawRow12238 : Integer.Sparse Key := [(key1695, -24), (key1695, 6), (key1272, 6), (key1695, 6), (key1695, 6)]

theorem rawRowCheck12238 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form6 = rawRow12238 := by decide +kernel

def row12238 : Integer.Sparse Key := [(key1272, 6), (key1695, -6)]

theorem rowCheck12238 : row12238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12238 := by decide +kernel

theorem rowEval12238 (x : Key → ℝ) : Integer.Sparse.eval row12238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12238, Integer.Sparse.eval_collectBalanced, rawRowCheck12238]

def rawRow12239 : Integer.Sparse Key := [(key1695, -24), (key1695, 6), (key1695, 6), (key1272, 6), (key1695, 6)]

theorem rawRowCheck12239 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form6 = rawRow12239 := by decide +kernel

def row12239 : Integer.Sparse Key := [(key1272, 6), (key1695, -6)]

theorem rowCheck12239 : row12239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12239 := by decide +kernel

theorem rowEval12239 (x : Key → ℝ) : Integer.Sparse.eval row12239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12239, Integer.Sparse.eval_collectBalanced, rawRowCheck12239]

def rawRow12240 : Integer.Sparse Key := [(key1695, -24), (key1695, 6), (key1695, 6), (key1695, 6), (key1272, 6)]

theorem rawRowCheck12240 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form6 = rawRow12240 := by decide +kernel

def row12240 : Integer.Sparse Key := [(key1272, 6), (key1695, -6)]

theorem rowCheck12240 : row12240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12240 := by decide +kernel

theorem rowEval12240 (x : Key → ℝ) : Integer.Sparse.eval row12240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12240, Integer.Sparse.eval_collectBalanced, rawRowCheck12240]

def rawRow12241 : Integer.Sparse Key := [(key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2)]

theorem rawRowCheck12241 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form7 = rawRow12241 := by decide +kernel

def row12241 : Integer.Sparse Key := [(key1359, -24), (key1485, 24)]

theorem rowCheck12241 : row12241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12241 := by decide +kernel

theorem rowEval12241 (x : Key → ℝ) : Integer.Sparse.eval row12241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12241, Integer.Sparse.eval_collectBalanced, rawRowCheck12241]

def rawRow12242 : Integer.Sparse Key := [(key1485, -2), (key1485, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1359, 2), (key1359, 2), (key1359, 2), (key1711, 2), (key1711, 2), (key1711, 2), (key1711, 2), (key1711, 2), (key1711, 2), (key1936, 2), (key1936, 2), (key1936, 2)]

theorem rawRowCheck12242 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow12242 := by decide +kernel

def row12242 : Integer.Sparse Key := [(key1359, 6), (key1485, -6)]

theorem rowCheck12242 : row12242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12242 := by decide +kernel

theorem rowEval12242 (x : Key → ℝ) : Integer.Sparse.eval row12242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12242, Integer.Sparse.eval_collectBalanced, rawRowCheck12242]

def rawRow12243 : Integer.Sparse Key := [(key1711, -2), (key1711, -2), (key1936, -2), (key1485, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1936, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1711, 2), (key1711, 2), (key1936, 2), (key1359, 2), (key1359, 2), (key1711, 2), (key1711, 2), (key1936, 2), (key1936, 2), (key1359, 2), (key1711, 2), (key1711, 2)]

theorem rawRowCheck12243 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form7 = rawRow12243 := by decide +kernel

def row12243 : Integer.Sparse Key := [(key1359, 6), (key1485, -6)]

theorem rowCheck12243 : row12243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12243 := by decide +kernel

theorem rowEval12243 (x : Key → ℝ) : Integer.Sparse.eval row12243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12243, Integer.Sparse.eval_collectBalanced, rawRowCheck12243]

def rawRow12244 : Integer.Sparse Key := [(key1711, -2), (key1936, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1485, -2), (key1936, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1485, -2), (key1711, -2), (key1711, 2), (key1936, 2), (key1711, 2), (key1711, 2), (key1936, 2), (key1359, 2), (key1936, 2), (key1359, 2), (key1711, 2), (key1711, 2), (key1359, 2), (key1711, 2)]

theorem rawRowCheck12244 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form7 = rawRow12244 := by decide +kernel

def row12244 : Integer.Sparse Key := [(key1359, 6), (key1485, -6)]

theorem rowCheck12244 : row12244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12244 := by decide +kernel

theorem rowEval12244 (x : Key → ℝ) : Integer.Sparse.eval row12244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12244, Integer.Sparse.eval_collectBalanced, rawRowCheck12244]

def rawRow12245 : Integer.Sparse Key := [(key1936, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1711, -2), (key1936, -2), (key1485, -2), (key1711, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1485, -2), (key1936, 2), (key1711, 2), (key1711, 2), (key1936, 2), (key1711, 2), (key1936, 2), (key1359, 2), (key1711, 2), (key1359, 2), (key1711, 2), (key1711, 2), (key1359, 2)]

theorem rawRowCheck12245 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form7 = rawRow12245 := by decide +kernel

def row12245 : Integer.Sparse Key := [(key1359, 6), (key1485, -6)]

theorem rowCheck12245 : row12245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12245 := by decide +kernel

theorem rowEval12245 (x : Key → ℝ) : Integer.Sparse.eval row12245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck12245, Integer.Sparse.eval_collectBalanced, rawRowCheck12245]

def rawRow12246 : Integer.Sparse Key := [(key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1)]

theorem rawRowCheck12246 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form8 = rawRow12246 := by decide +kernel

def row12246 : Integer.Sparse Key := [(key395, -24), (key440, 24)]

theorem rowCheck12246 : row12246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12246 := by decide +kernel

theorem rowEval12246 (x : Key → ℝ) : Integer.Sparse.eval row12246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12246, Integer.Sparse.eval_collectBalanced, rawRowCheck12246]

def rawRow12247 : Integer.Sparse Key := [(key258, -2), (key258, -2), (key258, -2), (key440, -2), (key440, -2), (key440, -2), (key440, -2), (key440, -2), (key440, -2), (key455, -2), (key455, -2), (key455, -2), (key258, 1), (key258, 1), (key258, 1), (key258, 1), (key258, 1), (key258, 1), (key395, 1), (key395, 1), (key395, 1), (key395, 1), (key395, 1), (key395, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key455, 1), (key455, 1), (key455, 1), (key455, 1), (key455, 1), (key455, 1)]

theorem rawRowCheck12247 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form8 = rawRow12247 := by decide +kernel

def row12247 : Integer.Sparse Key := [(key395, 6), (key440, -6)]

theorem rowCheck12247 : row12247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12247 := by decide +kernel

theorem rowEval12247 (x : Key → ℝ) : Integer.Sparse.eval row12247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12247, Integer.Sparse.eval_collectBalanced, rawRowCheck12247]

def rawRow12248 : Integer.Sparse Key := [(key440, -2), (key440, -2), (key455, -2), (key258, -2), (key258, -2), (key440, -2), (key440, -2), (key455, -2), (key455, -2), (key258, -2), (key440, -2), (key440, -2), (key395, 1), (key395, 1), (key440, 1), (key440, 1), (key455, 1), (key455, 1), (key258, 1), (key258, 1), (key440, 1), (key440, 1), (key455, 1), (key455, 1), (key258, 1), (key258, 1), (key395, 1), (key395, 1), (key455, 1), (key455, 1), (key258, 1), (key258, 1), (key395, 1), (key395, 1), (key440, 1), (key440, 1)]

theorem rawRowCheck12248 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form8 = rawRow12248 := by decide +kernel

def row12248 : Integer.Sparse Key := [(key395, 6), (key440, -6)]

theorem rowCheck12248 : row12248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12248 := by decide +kernel

theorem rowEval12248 (x : Key → ℝ) : Integer.Sparse.eval row12248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12248, Integer.Sparse.eval_collectBalanced, rawRowCheck12248]

def rawRow12249 : Integer.Sparse Key := [(key440, -2), (key455, -2), (key440, -2), (key440, -2), (key455, -2), (key258, -2), (key455, -2), (key258, -2), (key440, -2), (key440, -2), (key258, -2), (key440, -2), (key440, 1), (key455, 1), (key395, 1), (key455, 1), (key395, 1), (key440, 1), (key440, 1), (key455, 1), (key258, 1), (key455, 1), (key258, 1), (key440, 1), (key395, 1), (key455, 1), (key258, 1), (key455, 1), (key258, 1), (key395, 1), (key395, 1), (key440, 1), (key258, 1), (key440, 1), (key258, 1), (key395, 1)]

theorem rawRowCheck12249 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form8 = rawRow12249 := by decide +kernel

def row12249 : Integer.Sparse Key := [(key395, 6), (key440, -6)]

theorem rowCheck12249 : row12249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12249 := by decide +kernel

theorem rowEval12249 (x : Key → ℝ) : Integer.Sparse.eval row12249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12249, Integer.Sparse.eval_collectBalanced, rawRowCheck12249]

def rawRow12250 : Integer.Sparse Key := [(key455, -2), (key440, -2), (key440, -2), (key455, -2), (key440, -2), (key455, -2), (key258, -2), (key440, -2), (key258, -2), (key440, -2), (key440, -2), (key258, -2), (key455, 1), (key440, 1), (key455, 1), (key395, 1), (key440, 1), (key395, 1), (key455, 1), (key440, 1), (key455, 1), (key258, 1), (key440, 1), (key258, 1), (key455, 1), (key395, 1), (key455, 1), (key258, 1), (key395, 1), (key258, 1), (key440, 1), (key395, 1), (key440, 1), (key258, 1), (key395, 1), (key258, 1)]

theorem rawRowCheck12250 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form8 = rawRow12250 := by decide +kernel

def row12250 : Integer.Sparse Key := [(key395, 6), (key440, -6)]

theorem rowCheck12250 : row12250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12250 := by decide +kernel

theorem rowEval12250 (x : Key → ℝ) : Integer.Sparse.eval row12250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck12250, Integer.Sparse.eval_collectBalanced, rawRowCheck12250]

def rawRow12251 : Integer.Sparse Key := [(key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2)]

theorem rawRowCheck12251 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form9 = rawRow12251 := by decide +kernel

def row12251 : Integer.Sparse Key := [(key1711, 24), (key1936, -24)]

theorem rowCheck12251 : row12251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12251 := by decide +kernel

theorem rowEval12251 (x : Key → ℝ) : Integer.Sparse.eval row12251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12251, Integer.Sparse.eval_collectBalanced, rawRowCheck12251]

def rawRow12252 : Integer.Sparse Key := [(key1359, 1), (key1359, 1), (key1359, 1), (key1359, 1), (key1359, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1936, 1), (key1936, 1), (key1936, 1), (key1936, 1), (key1936, 1), (key1359, -2), (key1359, -2), (key1359, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2)]

theorem rawRowCheck12252 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form9 = rawRow12252 := by decide +kernel

def row12252 : Integer.Sparse Key := [(key1711, -6), (key1936, 6)]

theorem rowCheck12252 : row12252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12252 := by decide +kernel

theorem rowEval12252 (x : Key → ℝ) : Integer.Sparse.eval row12252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12252, Integer.Sparse.eval_collectBalanced, rawRowCheck12252]

def rawRow12253 : Integer.Sparse Key := [(key1485, 1), (key1485, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1936, 1), (key1359, 1), (key1359, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1936, 1), (key1359, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1936, 1), (key1936, 1), (key1359, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1711, 1), (key1711, 1), (key1485, -2), (key1711, -2), (key1711, -2), (key1359, -2), (key1711, -2), (key1711, -2), (key1359, -2), (key1359, -2), (key1485, -2), (key1485, -2), (key1711, -2), (key1711, -2)]

theorem rawRowCheck12253 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form9 = rawRow12253 := by decide +kernel

def row12253 : Integer.Sparse Key := [(key1711, -6), (key1936, 6)]

theorem rowCheck12253 : row12253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12253 := by decide +kernel

theorem rowEval12253 (x : Key → ℝ) : Integer.Sparse.eval row12253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12253, Integer.Sparse.eval_collectBalanced, rawRowCheck12253]

def rawRow12254 : Integer.Sparse Key := [(key1711, 1), (key1936, 1), (key1485, 1), (key1936, 1), (key1485, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1359, 1), (key1936, 1), (key1359, 1), (key1711, 1), (key1485, 1), (key1936, 1), (key1359, 1), (key1936, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1711, 1), (key1359, 1), (key1711, 1), (key1359, 1), (key1485, 1), (key1711, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1359, -2), (key1711, -2), (key1485, -2), (key1711, -2), (key1359, -2), (key1711, -2), (key1359, -2), (key1485, -2)]

theorem rawRowCheck12254 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form9 = rawRow12254 := by decide +kernel

def row12254 : Integer.Sparse Key := [(key1711, -6), (key1936, 6)]

theorem rowCheck12254 : row12254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12254 := by decide +kernel

theorem rowEval12254 (x : Key → ℝ) : Integer.Sparse.eval row12254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12254, Integer.Sparse.eval_collectBalanced, rawRowCheck12254]

def rawRow12255 : Integer.Sparse Key := [(key1936, 1), (key1711, 1), (key1936, 1), (key1485, 1), (key1711, 1), (key1485, 1), (key1936, 1), (key1711, 1), (key1936, 1), (key1359, 1), (key1711, 1), (key1359, 1), (key1936, 1), (key1485, 1), (key1936, 1), (key1359, 1), (key1485, 1), (key1359, 1), (key1711, 1), (key1485, 1), (key1711, 1), (key1359, 1), (key1485, 1), (key1359, 1), (key1711, -2), (key1711, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1359, -2), (key1711, -2), (key1485, -2), (key1711, -2), (key1359, -2), (key1485, -2), (key1359, -2)]

theorem rawRowCheck12255 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form9 = rawRow12255 := by decide +kernel

def row12255 : Integer.Sparse Key := [(key1711, -6), (key1936, 6)]

theorem rowCheck12255 : row12255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12255 := by decide +kernel

theorem rowEval12255 (x : Key → ℝ) : Integer.Sparse.eval row12255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck12255, Integer.Sparse.eval_collectBalanced, rawRowCheck12255]

def rawRow12256 : Integer.Sparse Key := [(key348, -6), (key348, -6), (key348, -6), (key348, -6), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2)]

theorem rawRowCheck12256 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form10 = rawRow12256 := by decide +kernel

def row12256 : Integer.Sparse Key := [(key348, -24), (key505, 24)]

theorem rowCheck12256 : row12256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12256 := by decide +kernel

theorem rowEval12256 (x : Key → ℝ) : Integer.Sparse.eval row12256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12256, Integer.Sparse.eval_collectBalanced, rawRowCheck12256]

def rawRow12257 : Integer.Sparse Key := [(key279, -6), (key505, -6), (key505, -6), (key505, -6), (key279, 2), (key279, 2), (key279, 2), (key348, 2), (key348, 2), (key348, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2)]

theorem rawRowCheck12257 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow12257 := by decide +kernel

def row12257 : Integer.Sparse Key := [(key348, 6), (key505, -6)]

theorem rowCheck12257 : row12257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12257 := by decide +kernel

theorem rowEval12257 (x : Key → ℝ) : Integer.Sparse.eval row12257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12257, Integer.Sparse.eval_collectBalanced, rawRowCheck12257]

def rawRow12258 : Integer.Sparse Key := [(key505, -6), (key279, -6), (key505, -6), (key505, -6), (key348, 2), (key505, 2), (key505, 2), (key279, 2), (key505, 2), (key505, 2), (key279, 2), (key279, 2), (key348, 2), (key348, 2), (key505, 2), (key505, 2)]

theorem rawRowCheck12258 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form10 = rawRow12258 := by decide +kernel

def row12258 : Integer.Sparse Key := [(key348, 6), (key505, -6)]

theorem rowCheck12258 : row12258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12258 := by decide +kernel

theorem rowEval12258 (x : Key → ℝ) : Integer.Sparse.eval row12258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12258, Integer.Sparse.eval_collectBalanced, rawRowCheck12258]

def rawRow12259 : Integer.Sparse Key := [(key505, -6), (key505, -6), (key279, -6), (key505, -6), (key505, 2), (key348, 2), (key505, 2), (key505, 2), (key279, 2), (key505, 2), (key348, 2), (key505, 2), (key279, 2), (key505, 2), (key279, 2), (key348, 2)]

theorem rawRowCheck12259 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form10 = rawRow12259 := by decide +kernel

def row12259 : Integer.Sparse Key := [(key348, 6), (key505, -6)]

theorem rowCheck12259 : row12259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12259 := by decide +kernel

theorem rowEval12259 (x : Key → ℝ) : Integer.Sparse.eval row12259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12259, Integer.Sparse.eval_collectBalanced, rawRowCheck12259]

def rawRow12260 : Integer.Sparse Key := [(key505, -6), (key505, -6), (key505, -6), (key279, -6), (key505, 2), (key505, 2), (key348, 2), (key505, 2), (key505, 2), (key279, 2), (key505, 2), (key348, 2), (key505, 2), (key279, 2), (key348, 2), (key279, 2)]

theorem rawRowCheck12260 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form10 = rawRow12260 := by decide +kernel

def row12260 : Integer.Sparse Key := [(key348, 6), (key505, -6)]

theorem rowCheck12260 : row12260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12260 := by decide +kernel

theorem rowEval12260 (x : Key → ℝ) : Integer.Sparse.eval row12260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck12260, Integer.Sparse.eval_collectBalanced, rawRowCheck12260]

def rawRow12261 : Integer.Sparse Key := [(key1273, 6), (key1273, 6), (key1273, 6), (key1273, 6), (key1850, -6), (key1850, -6), (key1850, -6), (key1850, -6)]

theorem rawRowCheck12261 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form11 = rawRow12261 := by decide +kernel

def row12261 : Integer.Sparse Key := [(key1273, 24), (key1850, -24)]

theorem rowCheck12261 : row12261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12261 := by decide +kernel

theorem rowEval12261 (x : Key → ℝ) : Integer.Sparse.eval row12261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12261, Integer.Sparse.eval_collectBalanced, rawRowCheck12261]

def rawRow12262 : Integer.Sparse Key := [(key1696, 6), (key1696, 6), (key1696, 6), (key1850, 6), (key1273, -6), (key1696, -6), (key1696, -6), (key1696, -6)]

theorem rawRowCheck12262 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form11 = rawRow12262 := by decide +kernel

def row12262 : Integer.Sparse Key := [(key1273, -6), (key1850, 6)]

theorem rowCheck12262 : row12262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12262 := by decide +kernel

theorem rowEval12262 (x : Key → ℝ) : Integer.Sparse.eval row12262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12262, Integer.Sparse.eval_collectBalanced, rawRowCheck12262]

def rawRow12263 : Integer.Sparse Key := [(key1696, 6), (key1696, 6), (key1850, 6), (key1696, 6), (key1696, -6), (key1273, -6), (key1696, -6), (key1696, -6)]

theorem rawRowCheck12263 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form11 = rawRow12263 := by decide +kernel

def row12263 : Integer.Sparse Key := [(key1273, -6), (key1850, 6)]

theorem rowCheck12263 : row12263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12263 := by decide +kernel

theorem rowEval12263 (x : Key → ℝ) : Integer.Sparse.eval row12263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12263, Integer.Sparse.eval_collectBalanced, rawRowCheck12263]

def rawRow12264 : Integer.Sparse Key := [(key1696, 6), (key1850, 6), (key1696, 6), (key1696, 6), (key1696, -6), (key1696, -6), (key1273, -6), (key1696, -6)]

theorem rawRowCheck12264 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form11 = rawRow12264 := by decide +kernel

def row12264 : Integer.Sparse Key := [(key1273, -6), (key1850, 6)]

theorem rowCheck12264 : row12264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12264 := by decide +kernel

theorem rowEval12264 (x : Key → ℝ) : Integer.Sparse.eval row12264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12264, Integer.Sparse.eval_collectBalanced, rawRowCheck12264]

def rawRow12265 : Integer.Sparse Key := [(key1850, 6), (key1696, 6), (key1696, 6), (key1696, 6), (key1696, -6), (key1696, -6), (key1696, -6), (key1273, -6)]

theorem rawRowCheck12265 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form11 = rawRow12265 := by decide +kernel

def row12265 : Integer.Sparse Key := [(key1273, -6), (key1850, 6)]

theorem rowCheck12265 : row12265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12265 := by decide +kernel

theorem rowEval12265 (x : Key → ℝ) : Integer.Sparse.eval row12265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12265, Integer.Sparse.eval_collectBalanced, rawRowCheck12265]

def rawRow12266 : Integer.Sparse Key := [(key1274, 6), (key1274, 6), (key1274, 6), (key1274, 6), (key1932, -6), (key1932, -6), (key1932, -6), (key1932, -6)]

theorem rawRowCheck12266 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form12 = rawRow12266 := by decide +kernel

def row12266 : Integer.Sparse Key := [(key1274, 24), (key1932, -24)]

theorem rowCheck12266 : row12266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12266 := by decide +kernel

theorem rowEval12266 (x : Key → ℝ) : Integer.Sparse.eval row12266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12266, Integer.Sparse.eval_collectBalanced, rawRowCheck12266]

def rawRow12267 : Integer.Sparse Key := [(key1697, 6), (key1697, 6), (key1697, 6), (key1932, 6), (key1274, -6), (key1697, -6), (key1697, -6), (key1697, -6)]

theorem rawRowCheck12267 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form12 = rawRow12267 := by decide +kernel

def row12267 : Integer.Sparse Key := [(key1274, -6), (key1932, 6)]

theorem rowCheck12267 : row12267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12267 := by decide +kernel

theorem rowEval12267 (x : Key → ℝ) : Integer.Sparse.eval row12267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12267, Integer.Sparse.eval_collectBalanced, rawRowCheck12267]

def rawRow12268 : Integer.Sparse Key := [(key1697, 6), (key1697, 6), (key1932, 6), (key1697, 6), (key1697, -6), (key1274, -6), (key1697, -6), (key1697, -6)]

theorem rawRowCheck12268 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form12 = rawRow12268 := by decide +kernel

def row12268 : Integer.Sparse Key := [(key1274, -6), (key1932, 6)]

theorem rowCheck12268 : row12268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12268 := by decide +kernel

theorem rowEval12268 (x : Key → ℝ) : Integer.Sparse.eval row12268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12268, Integer.Sparse.eval_collectBalanced, rawRowCheck12268]

def rawRow12269 : Integer.Sparse Key := [(key1697, 6), (key1932, 6), (key1697, 6), (key1697, 6), (key1697, -6), (key1697, -6), (key1274, -6), (key1697, -6)]

theorem rawRowCheck12269 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form12 = rawRow12269 := by decide +kernel

def row12269 : Integer.Sparse Key := [(key1274, -6), (key1932, 6)]

theorem rowCheck12269 : row12269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12269 := by decide +kernel

theorem rowEval12269 (x : Key → ℝ) : Integer.Sparse.eval row12269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12269, Integer.Sparse.eval_collectBalanced, rawRowCheck12269]

def rawRow12270 : Integer.Sparse Key := [(key1932, 6), (key1697, 6), (key1697, 6), (key1697, 6), (key1697, -6), (key1697, -6), (key1697, -6), (key1274, -6)]

theorem rawRowCheck12270 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form12 = rawRow12270 := by decide +kernel

def row12270 : Integer.Sparse Key := [(key1274, -6), (key1932, 6)]

theorem rowCheck12270 : row12270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12270 := by decide +kernel

theorem rowEval12270 (x : Key → ℝ) : Integer.Sparse.eval row12270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck12270, Integer.Sparse.eval_collectBalanced, rawRowCheck12270]

def rawRow12271 : Integer.Sparse Key := [(key750, -6), (key750, -6), (key750, -6), (key750, -6), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2)]

theorem rawRowCheck12271 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form13 = rawRow12271 := by decide +kernel

def row12271 : Integer.Sparse Key := [(key750, -24), (key927, 24)]

theorem rowCheck12271 : row12271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12271 := by decide +kernel

theorem rowEval12271 (x : Key → ℝ) : Integer.Sparse.eval row12271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12271, Integer.Sparse.eval_collectBalanced, rawRowCheck12271]

def rawRow12272 : Integer.Sparse Key := [(key927, -6), (key927, -6), (key927, -6), (key938, -6), (key750, 2), (key750, 2), (key750, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key938, 2), (key938, 2), (key938, 2)]

theorem rawRowCheck12272 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form13 = rawRow12272 := by decide +kernel

def row12272 : Integer.Sparse Key := [(key750, 6), (key927, -6)]

theorem rowCheck12272 : row12272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12272 := by decide +kernel

theorem rowEval12272 (x : Key → ℝ) : Integer.Sparse.eval row12272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12272, Integer.Sparse.eval_collectBalanced, rawRowCheck12272]

def rawRow12273 : Integer.Sparse Key := [(key927, -6), (key927, -6), (key938, -6), (key927, -6), (key927, 2), (key927, 2), (key938, 2), (key750, 2), (key750, 2), (key927, 2), (key927, 2), (key938, 2), (key938, 2), (key750, 2), (key927, 2), (key927, 2)]

theorem rawRowCheck12273 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form13 = rawRow12273 := by decide +kernel

def row12273 : Integer.Sparse Key := [(key750, 6), (key927, -6)]

theorem rowCheck12273 : row12273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12273 := by decide +kernel

theorem rowEval12273 (x : Key → ℝ) : Integer.Sparse.eval row12273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12273, Integer.Sparse.eval_collectBalanced, rawRowCheck12273]

def rawRow12274 : Integer.Sparse Key := [(key927, -6), (key938, -6), (key927, -6), (key927, -6), (key927, 2), (key938, 2), (key927, 2), (key927, 2), (key938, 2), (key750, 2), (key938, 2), (key750, 2), (key927, 2), (key927, 2), (key750, 2), (key927, 2)]

theorem rawRowCheck12274 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form13 = rawRow12274 := by decide +kernel

def row12274 : Integer.Sparse Key := [(key750, 6), (key927, -6)]

theorem rowCheck12274 : row12274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12274 := by decide +kernel

theorem rowEval12274 (x : Key → ℝ) : Integer.Sparse.eval row12274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12274, Integer.Sparse.eval_collectBalanced, rawRowCheck12274]

def rawRow12275 : Integer.Sparse Key := [(key938, -6), (key927, -6), (key927, -6), (key927, -6), (key938, 2), (key927, 2), (key927, 2), (key938, 2), (key927, 2), (key938, 2), (key750, 2), (key927, 2), (key750, 2), (key927, 2), (key927, 2), (key750, 2)]

theorem rawRowCheck12275 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form13 = rawRow12275 := by decide +kernel

def row12275 : Integer.Sparse Key := [(key750, 6), (key927, -6)]

theorem rowCheck12275 : row12275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12275 := by decide +kernel

theorem rowEval12275 (x : Key → ℝ) : Integer.Sparse.eval row12275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12275, Integer.Sparse.eval_collectBalanced, rawRowCheck12275]

def rawRow12276 : Integer.Sparse Key := [(key30, 6), (key30, 6), (key30, 6), (key30, 6), (key146, -6), (key146, -6), (key146, -6), (key146, -6)]

theorem rawRowCheck12276 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form14 = rawRow12276 := by decide +kernel

def row12276 : Integer.Sparse Key := [(key30, 24), (key146, -24)]

theorem rowCheck12276 : row12276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12276 := by decide +kernel

theorem rowEval12276 (x : Key → ℝ) : Integer.Sparse.eval row12276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12276, Integer.Sparse.eval_collectBalanced, rawRowCheck12276]

def rawRow12277 : Integer.Sparse Key := [(key110, 6), (key110, 6), (key110, 6), (key146, 6), (key30, -6), (key110, -6), (key110, -6), (key110, -6)]

theorem rawRowCheck12277 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form14 = rawRow12277 := by decide +kernel

def row12277 : Integer.Sparse Key := [(key30, -6), (key146, 6)]

theorem rowCheck12277 : row12277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12277 := by decide +kernel

theorem rowEval12277 (x : Key → ℝ) : Integer.Sparse.eval row12277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12277, Integer.Sparse.eval_collectBalanced, rawRowCheck12277]

def rawRow12278 : Integer.Sparse Key := [(key110, 6), (key110, 6), (key146, 6), (key110, 6), (key110, -6), (key30, -6), (key110, -6), (key110, -6)]

theorem rawRowCheck12278 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form14 = rawRow12278 := by decide +kernel

def row12278 : Integer.Sparse Key := [(key30, -6), (key146, 6)]

theorem rowCheck12278 : row12278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12278 := by decide +kernel

theorem rowEval12278 (x : Key → ℝ) : Integer.Sparse.eval row12278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12278, Integer.Sparse.eval_collectBalanced, rawRowCheck12278]

def rawRow12279 : Integer.Sparse Key := [(key110, 6), (key146, 6), (key110, 6), (key110, 6), (key110, -6), (key110, -6), (key30, -6), (key110, -6)]

theorem rawRowCheck12279 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form14 = rawRow12279 := by decide +kernel

def row12279 : Integer.Sparse Key := [(key30, -6), (key146, 6)]

theorem rowCheck12279 : row12279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12279 := by decide +kernel

theorem rowEval12279 (x : Key → ℝ) : Integer.Sparse.eval row12279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12279, Integer.Sparse.eval_collectBalanced, rawRowCheck12279]

def rawRow12280 : Integer.Sparse Key := [(key146, 6), (key110, 6), (key110, 6), (key110, 6), (key110, -6), (key110, -6), (key110, -6), (key30, -6)]

theorem rawRowCheck12280 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form14 = rawRow12280 := by decide +kernel

def row12280 : Integer.Sparse Key := [(key30, -6), (key146, 6)]

theorem rowCheck12280 : row12280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12280 := by decide +kernel

theorem rowEval12280 (x : Key → ℝ) : Integer.Sparse.eval row12280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12280, Integer.Sparse.eval_collectBalanced, rawRowCheck12280]

def rawRow12281 : Integer.Sparse Key := [(key1273, -6), (key1273, -6), (key1273, -6), (key1273, -6), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2)]

theorem rawRowCheck12281 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form15 = rawRow12281 := by decide +kernel

def row12281 : Integer.Sparse Key := [(key1273, -24), (key1696, 24)]

theorem rowCheck12281 : row12281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12281 := by decide +kernel

theorem rowEval12281 (x : Key → ℝ) : Integer.Sparse.eval row12281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12281, Integer.Sparse.eval_collectBalanced, rawRowCheck12281]

def rawRow12282 : Integer.Sparse Key := [(key1696, -6), (key1696, -6), (key1696, -6), (key1850, -6), (key1273, 2), (key1273, 2), (key1273, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1850, 2), (key1850, 2), (key1850, 2)]

theorem rawRowCheck12282 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form15 = rawRow12282 := by decide +kernel

def row12282 : Integer.Sparse Key := [(key1273, 6), (key1696, -6)]

theorem rowCheck12282 : row12282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12282 := by decide +kernel

theorem rowEval12282 (x : Key → ℝ) : Integer.Sparse.eval row12282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12282, Integer.Sparse.eval_collectBalanced, rawRowCheck12282]

def rawRow12283 : Integer.Sparse Key := [(key1696, -6), (key1696, -6), (key1850, -6), (key1696, -6), (key1696, 2), (key1696, 2), (key1850, 2), (key1273, 2), (key1273, 2), (key1696, 2), (key1696, 2), (key1850, 2), (key1850, 2), (key1273, 2), (key1696, 2), (key1696, 2)]

theorem rawRowCheck12283 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form15 = rawRow12283 := by decide +kernel

def row12283 : Integer.Sparse Key := [(key1273, 6), (key1696, -6)]

theorem rowCheck12283 : row12283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12283 := by decide +kernel

theorem rowEval12283 (x : Key → ℝ) : Integer.Sparse.eval row12283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12283, Integer.Sparse.eval_collectBalanced, rawRowCheck12283]

def rawRow12284 : Integer.Sparse Key := [(key1696, -6), (key1850, -6), (key1696, -6), (key1696, -6), (key1696, 2), (key1850, 2), (key1696, 2), (key1696, 2), (key1850, 2), (key1273, 2), (key1850, 2), (key1273, 2), (key1696, 2), (key1696, 2), (key1273, 2), (key1696, 2)]

theorem rawRowCheck12284 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form15 = rawRow12284 := by decide +kernel

def row12284 : Integer.Sparse Key := [(key1273, 6), (key1696, -6)]

theorem rowCheck12284 : row12284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12284 := by decide +kernel

theorem rowEval12284 (x : Key → ℝ) : Integer.Sparse.eval row12284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12284, Integer.Sparse.eval_collectBalanced, rawRowCheck12284]

def rawRow12285 : Integer.Sparse Key := [(key1850, -6), (key1696, -6), (key1696, -6), (key1696, -6), (key1850, 2), (key1696, 2), (key1696, 2), (key1850, 2), (key1696, 2), (key1850, 2), (key1273, 2), (key1696, 2), (key1273, 2), (key1696, 2), (key1696, 2), (key1273, 2)]

theorem rawRowCheck12285 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form15 = rawRow12285 := by decide +kernel

def row12285 : Integer.Sparse Key := [(key1273, 6), (key1696, -6)]

theorem rowCheck12285 : row12285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12285 := by decide +kernel

theorem rowEval12285 (x : Key → ℝ) : Integer.Sparse.eval row12285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12285, Integer.Sparse.eval_collectBalanced, rawRowCheck12285]

def rawRow12286 : Integer.Sparse Key := [(key1357, -6), (key1357, -6), (key1357, -6), (key1357, -6), (key1483, 6), (key1483, 6), (key1483, 6), (key1483, 6)]

theorem rawRowCheck12286 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form16 = rawRow12286 := by decide +kernel

def row12286 : Integer.Sparse Key := [(key1357, -24), (key1483, 24)]

theorem rowCheck12286 : row12286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12286 := by decide +kernel

theorem rowEval12286 (x : Key → ℝ) : Integer.Sparse.eval row12286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12286, Integer.Sparse.eval_collectBalanced, rawRowCheck12286]

def rawRow12287 : Integer.Sparse Key := [(key1483, -6), (key1709, -6), (key1709, -6), (key1709, -6), (key1357, 6), (key1709, 6), (key1709, 6), (key1709, 6)]

theorem rawRowCheck12287 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form16 = rawRow12287 := by decide +kernel

def row12287 : Integer.Sparse Key := [(key1357, 6), (key1483, -6)]

theorem rowCheck12287 : row12287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12287 := by decide +kernel

theorem rowEval12287 (x : Key → ℝ) : Integer.Sparse.eval row12287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12287, Integer.Sparse.eval_collectBalanced, rawRowCheck12287]

end MUB6.Certificate.GramRows

end OAI
