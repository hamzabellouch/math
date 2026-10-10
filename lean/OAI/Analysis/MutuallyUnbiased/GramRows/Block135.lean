import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14208 : Integer.Sparse Key := [(key2503, 4), (key2554, 4), (key2378, 4), (key2506, -2), (key2472, -2), (key2554, -2), (key2378, -2), (key2538, -2), (key2381, -2), (key2522, -2), (key2480, -2), (key2563, -2), (key2390, -2), (key2543, -2), (key2392, -2), (key2482, 4), (key2543, 4), (key2392, 4)]

theorem rawRowCheck14208 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form0 = rawRow14208 := by decide +kernel

def row14208 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck14208 : row14208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14208 := by decide +kernel

theorem rowEval14208 (x : Key → ℝ) : Integer.Sparse.eval row14208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14208, Integer.Sparse.eval_collectBalanced, rawRowCheck14208]

def rawRow14209 : Integer.Sparse Key := [(key2554, 4), (key2378, 4), (key2503, 4), (key2538, -2), (key2554, -2), (key2381, -2), (key2506, -2), (key2378, -2), (key2472, -2), (key2543, -2), (key2563, -2), (key2392, -2), (key2522, -2), (key2390, -2), (key2480, -2), (key2543, 4), (key2392, 4), (key2482, 4)]

theorem rawRowCheck14209 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form0 = rawRow14209 := by decide +kernel

def row14209 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck14209 : row14209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14209 := by decide +kernel

theorem rowEval14209 (x : Key → ℝ) : Integer.Sparse.eval row14209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14209, Integer.Sparse.eval_collectBalanced, rawRowCheck14209]

def rawRow14210 : Integer.Sparse Key := [(key2554, 4), (key2503, 4), (key2378, 4), (key2554, -2), (key2538, -2), (key2506, -2), (key2381, -2), (key2472, -2), (key2378, -2), (key2563, -2), (key2543, -2), (key2522, -2), (key2392, -2), (key2480, -2), (key2390, -2), (key2543, 4), (key2482, 4), (key2392, 4)]

theorem rawRowCheck14210 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form0 = rawRow14210 := by decide +kernel

def row14210 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck14210 : row14210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14210 := by decide +kernel

theorem rowEval14210 (x : Key → ℝ) : Integer.Sparse.eval row14210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14210, Integer.Sparse.eval_collectBalanced, rawRowCheck14210]

def rawRow14211 : Integer.Sparse Key := [(key2381, 4), (key2506, 4), (key2506, 4), (key2378, -2), (key2378, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2392, -2), (key2392, -2), (key2482, -2), (key2482, -2), (key2522, -2), (key2522, -2), (key2390, 4), (key2480, 4), (key2480, 4)]

theorem rawRowCheck14211 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form0 = rawRow14211 := by decide +kernel

def row14211 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

theorem rowCheck14211 : row14211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14211 := by decide +kernel

theorem rowEval14211 (x : Key → ℝ) : Integer.Sparse.eval row14211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14211, Integer.Sparse.eval_collectBalanced, rawRowCheck14211]

def rawRow14212 : Integer.Sparse Key := [(key2506, 4), (key2381, 4), (key2506, 4), (key2472, -2), (key2503, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2480, 4), (key2390, 4), (key2480, 4)]

theorem rawRowCheck14212 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form0 = rawRow14212 := by decide +kernel

def row14212 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

theorem rowCheck14212 : row14212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14212 := by decide +kernel

theorem rowEval14212 (x : Key → ℝ) : Integer.Sparse.eval row14212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14212, Integer.Sparse.eval_collectBalanced, rawRowCheck14212]

def rawRow14213 : Integer.Sparse Key := [(key2506, 4), (key2506, 4), (key2381, 4), (key2503, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2378, -2), (key2522, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2392, -2), (key2480, 4), (key2480, 4), (key2390, 4)]

theorem rawRowCheck14213 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form0 = rawRow14213 := by decide +kernel

def row14213 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

theorem rowCheck14213 : row14213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14213 := by decide +kernel

theorem rowEval14213 (x : Key → ℝ) : Integer.Sparse.eval row14213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14213, Integer.Sparse.eval_collectBalanced, rawRowCheck14213]

def rawRow14214 : Integer.Sparse Key := [(key2378, 4), (key2503, 4), (key2554, 4), (key2390, -2), (key2392, -2), (key2480, -2), (key2543, -2), (key2522, -2), (key2563, -2), (key2378, -2), (key2381, -2), (key2472, -2), (key2538, -2), (key2506, -2), (key2554, -2), (key2392, 4), (key2482, 4), (key2543, 4)]

theorem rawRowCheck14214 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form0 = rawRow14214 := by decide +kernel

def row14214 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck14214 : row14214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14214 := by decide +kernel

theorem rowEval14214 (x : Key → ℝ) : Integer.Sparse.eval row14214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14214, Integer.Sparse.eval_collectBalanced, rawRowCheck14214]

def rawRow14215 : Integer.Sparse Key := [(key2378, 4), (key2554, 4), (key2503, 4), (key2392, -2), (key2390, -2), (key2543, -2), (key2480, -2), (key2563, -2), (key2522, -2), (key2381, -2), (key2378, -2), (key2538, -2), (key2472, -2), (key2554, -2), (key2506, -2), (key2392, 4), (key2543, 4), (key2482, 4)]

theorem rawRowCheck14215 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form0 = rawRow14215 := by decide +kernel

def row14215 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck14215 : row14215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14215 := by decide +kernel

theorem rowEval14215 (x : Key → ℝ) : Integer.Sparse.eval row14215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14215, Integer.Sparse.eval_collectBalanced, rawRowCheck14215]

def rawRow14216 : Integer.Sparse Key := [(key2503, 4), (key2378, 4), (key2554, 4), (key2480, -2), (key2522, -2), (key2390, -2), (key2563, -2), (key2392, -2), (key2543, -2), (key2472, -2), (key2506, -2), (key2378, -2), (key2554, -2), (key2381, -2), (key2538, -2), (key2482, 4), (key2392, 4), (key2543, 4)]

theorem rawRowCheck14216 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form0 = rawRow14216 := by decide +kernel

def row14216 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck14216 : row14216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14216 := by decide +kernel

theorem rowEval14216 (x : Key → ℝ) : Integer.Sparse.eval row14216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14216, Integer.Sparse.eval_collectBalanced, rawRowCheck14216]

def rawRow14217 : Integer.Sparse Key := [(key2503, 4), (key2554, 4), (key2378, 4), (key2522, -2), (key2480, -2), (key2563, -2), (key2390, -2), (key2543, -2), (key2392, -2), (key2506, -2), (key2472, -2), (key2554, -2), (key2378, -2), (key2538, -2), (key2381, -2), (key2482, 4), (key2543, 4), (key2392, 4)]

theorem rawRowCheck14217 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form0 = rawRow14217 := by decide +kernel

def row14217 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck14217 : row14217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14217 := by decide +kernel

theorem rowEval14217 (x : Key → ℝ) : Integer.Sparse.eval row14217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14217, Integer.Sparse.eval_collectBalanced, rawRowCheck14217]

def rawRow14218 : Integer.Sparse Key := [(key2554, 4), (key2378, 4), (key2503, 4), (key2543, -2), (key2563, -2), (key2392, -2), (key2522, -2), (key2390, -2), (key2480, -2), (key2538, -2), (key2554, -2), (key2381, -2), (key2506, -2), (key2378, -2), (key2472, -2), (key2543, 4), (key2392, 4), (key2482, 4)]

theorem rawRowCheck14218 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form0 = rawRow14218 := by decide +kernel

def row14218 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck14218 : row14218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14218 := by decide +kernel

theorem rowEval14218 (x : Key → ℝ) : Integer.Sparse.eval row14218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14218, Integer.Sparse.eval_collectBalanced, rawRowCheck14218]

def rawRow14219 : Integer.Sparse Key := [(key2554, 4), (key2503, 4), (key2378, 4), (key2563, -2), (key2543, -2), (key2522, -2), (key2392, -2), (key2480, -2), (key2390, -2), (key2554, -2), (key2538, -2), (key2506, -2), (key2381, -2), (key2472, -2), (key2378, -2), (key2543, 4), (key2482, 4), (key2392, 4)]

theorem rawRowCheck14219 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form0 = rawRow14219 := by decide +kernel

def row14219 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck14219 : row14219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14219 := by decide +kernel

theorem rowEval14219 (x : Key → ℝ) : Integer.Sparse.eval row14219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14219, Integer.Sparse.eval_collectBalanced, rawRowCheck14219]

def rawRow14220 : Integer.Sparse Key := [(key2390, 4), (key2437, 4), (key2563, 4), (key2378, -2), (key2392, -2), (key2406, -2), (key2543, -2), (key2440, -2), (key2554, -2), (key2378, -2), (key2392, -2), (key2406, -2), (key2543, -2), (key2440, -2), (key2554, -2), (key2381, 4), (key2409, 4), (key2538, 4)]

theorem rawRowCheck14220 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form0 = rawRow14220 := by decide +kernel

def row14220 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

theorem rowCheck14220 : row14220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14220 := by decide +kernel

theorem rowEval14220 (x : Key → ℝ) : Integer.Sparse.eval row14220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14220, Integer.Sparse.eval_collectBalanced, rawRowCheck14220]

def rawRow14221 : Integer.Sparse Key := [(key2390, 4), (key2563, 4), (key2437, 4), (key2392, -2), (key2378, -2), (key2543, -2), (key2406, -2), (key2554, -2), (key2440, -2), (key2392, -2), (key2378, -2), (key2543, -2), (key2406, -2), (key2554, -2), (key2440, -2), (key2381, 4), (key2538, 4), (key2409, 4)]

theorem rawRowCheck14221 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form0 = rawRow14221 := by decide +kernel

def row14221 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

theorem rowCheck14221 : row14221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14221 := by decide +kernel

theorem rowEval14221 (x : Key → ℝ) : Integer.Sparse.eval row14221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14221, Integer.Sparse.eval_collectBalanced, rawRowCheck14221]

def rawRow14222 : Integer.Sparse Key := [(key2437, 4), (key2390, 4), (key2563, 4), (key2406, -2), (key2440, -2), (key2378, -2), (key2554, -2), (key2392, -2), (key2543, -2), (key2406, -2), (key2440, -2), (key2378, -2), (key2554, -2), (key2392, -2), (key2543, -2), (key2409, 4), (key2381, 4), (key2538, 4)]

theorem rawRowCheck14222 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form0 = rawRow14222 := by decide +kernel

def row14222 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

theorem rowCheck14222 : row14222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14222 := by decide +kernel

theorem rowEval14222 (x : Key → ℝ) : Integer.Sparse.eval row14222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14222, Integer.Sparse.eval_collectBalanced, rawRowCheck14222]

def rawRow14223 : Integer.Sparse Key := [(key2437, 4), (key2563, 4), (key2390, 4), (key2440, -2), (key2406, -2), (key2554, -2), (key2378, -2), (key2543, -2), (key2392, -2), (key2440, -2), (key2406, -2), (key2554, -2), (key2378, -2), (key2543, -2), (key2392, -2), (key2409, 4), (key2538, 4), (key2381, 4)]

theorem rawRowCheck14223 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form0 = rawRow14223 := by decide +kernel

def row14223 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

theorem rowCheck14223 : row14223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14223 := by decide +kernel

theorem rowEval14223 (x : Key → ℝ) : Integer.Sparse.eval row14223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14223, Integer.Sparse.eval_collectBalanced, rawRowCheck14223]

def rawRow14224 : Integer.Sparse Key := [(key2563, 4), (key2390, 4), (key2437, 4), (key2543, -2), (key2554, -2), (key2392, -2), (key2440, -2), (key2378, -2), (key2406, -2), (key2543, -2), (key2554, -2), (key2392, -2), (key2440, -2), (key2378, -2), (key2406, -2), (key2538, 4), (key2381, 4), (key2409, 4)]

theorem rawRowCheck14224 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form0 = rawRow14224 := by decide +kernel

def row14224 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

theorem rowCheck14224 : row14224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14224 := by decide +kernel

theorem rowEval14224 (x : Key → ℝ) : Integer.Sparse.eval row14224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14224, Integer.Sparse.eval_collectBalanced, rawRowCheck14224]

def rawRow14225 : Integer.Sparse Key := [(key2563, 4), (key2437, 4), (key2390, 4), (key2554, -2), (key2543, -2), (key2440, -2), (key2392, -2), (key2406, -2), (key2378, -2), (key2554, -2), (key2543, -2), (key2440, -2), (key2392, -2), (key2406, -2), (key2378, -2), (key2538, 4), (key2409, 4), (key2381, 4)]

theorem rawRowCheck14225 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form0 = rawRow14225 := by decide +kernel

def row14225 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

theorem rowCheck14225 : row14225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14225 := by decide +kernel

theorem rowEval14225 (x : Key → ℝ) : Integer.Sparse.eval row14225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14225, Integer.Sparse.eval_collectBalanced, rawRowCheck14225]

def rawRow14226 : Integer.Sparse Key := [(key2392, 4), (key2440, 4), (key2522, 4), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2381, -2), (key2392, -2), (key2409, -2), (key2482, -2), (key2440, -2), (key2506, -2), (key2378, 4), (key2406, 4), (key2472, 4)]

theorem rawRowCheck14226 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form0 = rawRow14226 := by decide +kernel

def row14226 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

theorem rowCheck14226 : row14226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14226 := by decide +kernel

theorem rowEval14226 (x : Key → ℝ) : Integer.Sparse.eval row14226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14226, Integer.Sparse.eval_collectBalanced, rawRowCheck14226]

def rawRow14227 : Integer.Sparse Key := [(key2392, 4), (key2522, 4), (key2440, 4), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2392, -2), (key2381, -2), (key2482, -2), (key2409, -2), (key2506, -2), (key2440, -2), (key2378, 4), (key2472, 4), (key2406, 4)]

theorem rawRowCheck14227 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form0 = rawRow14227 := by decide +kernel

def row14227 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

theorem rowCheck14227 : row14227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14227 := by decide +kernel

theorem rowEval14227 (x : Key → ℝ) : Integer.Sparse.eval row14227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14227, Integer.Sparse.eval_collectBalanced, rawRowCheck14227]

def rawRow14228 : Integer.Sparse Key := [(key2440, 4), (key2392, 4), (key2522, 4), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2409, -2), (key2440, -2), (key2381, -2), (key2506, -2), (key2392, -2), (key2482, -2), (key2406, 4), (key2378, 4), (key2472, 4)]

theorem rawRowCheck14228 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form0 = rawRow14228 := by decide +kernel

def row14228 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

theorem rowCheck14228 : row14228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14228 := by decide +kernel

theorem rowEval14228 (x : Key → ℝ) : Integer.Sparse.eval row14228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14228, Integer.Sparse.eval_collectBalanced, rawRowCheck14228]

def rawRow14229 : Integer.Sparse Key := [(key2440, 4), (key2522, 4), (key2392, 4), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2440, -2), (key2409, -2), (key2506, -2), (key2381, -2), (key2482, -2), (key2392, -2), (key2406, 4), (key2472, 4), (key2378, 4)]

theorem rawRowCheck14229 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form0 = rawRow14229 := by decide +kernel

def row14229 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

theorem rowCheck14229 : row14229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14229 := by decide +kernel

theorem rowEval14229 (x : Key → ℝ) : Integer.Sparse.eval row14229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14229, Integer.Sparse.eval_collectBalanced, rawRowCheck14229]

def rawRow14230 : Integer.Sparse Key := [(key2522, 4), (key2392, 4), (key2440, 4), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2482, -2), (key2506, -2), (key2392, -2), (key2440, -2), (key2381, -2), (key2409, -2), (key2472, 4), (key2378, 4), (key2406, 4)]

theorem rawRowCheck14230 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form0 = rawRow14230 := by decide +kernel

def row14230 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

theorem rowCheck14230 : row14230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14230 := by decide +kernel

theorem rowEval14230 (x : Key → ℝ) : Integer.Sparse.eval row14230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14230, Integer.Sparse.eval_collectBalanced, rawRowCheck14230]

def rawRow14231 : Integer.Sparse Key := [(key2522, 4), (key2440, 4), (key2392, 4), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2506, -2), (key2482, -2), (key2440, -2), (key2392, -2), (key2409, -2), (key2381, -2), (key2472, 4), (key2406, 4), (key2378, 4)]

theorem rawRowCheck14231 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form0 = rawRow14231 := by decide +kernel

def row14231 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

theorem rowCheck14231 : row14231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14231 := by decide +kernel

theorem rowEval14231 (x : Key → ℝ) : Integer.Sparse.eval row14231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14231, Integer.Sparse.eval_collectBalanced, rawRowCheck14231]

def rawRow14232 : Integer.Sparse Key := [(key2381, 4), (key2506, 4), (key2506, 4), (key2392, -2), (key2392, -2), (key2482, -2), (key2482, -2), (key2522, -2), (key2522, -2), (key2378, -2), (key2378, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2390, 4), (key2480, 4), (key2480, 4)]

theorem rawRowCheck14232 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form0 = rawRow14232 := by decide +kernel

def row14232 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

theorem rowCheck14232 : row14232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14232 := by decide +kernel

theorem rowEval14232 (x : Key → ℝ) : Integer.Sparse.eval row14232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14232, Integer.Sparse.eval_collectBalanced, rawRowCheck14232]

def rawRow14233 : Integer.Sparse Key := [(key2506, 4), (key2381, 4), (key2506, 4), (key2482, -2), (key2522, -2), (key2392, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2480, 4), (key2390, 4), (key2480, 4)]

theorem rawRowCheck14233 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form0 = rawRow14233 := by decide +kernel

def row14233 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

theorem rowCheck14233 : row14233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14233 := by decide +kernel

theorem rowEval14233 (x : Key → ℝ) : Integer.Sparse.eval row14233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14233, Integer.Sparse.eval_collectBalanced, rawRowCheck14233]

def rawRow14234 : Integer.Sparse Key := [(key2506, 4), (key2506, 4), (key2381, 4), (key2522, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2392, -2), (key2503, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2378, -2), (key2480, 4), (key2480, 4), (key2390, 4)]

theorem rawRowCheck14234 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form0 = rawRow14234 := by decide +kernel

def row14234 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

theorem rowCheck14234 : row14234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14234 := by decide +kernel

theorem rowEval14234 (x : Key → ℝ) : Integer.Sparse.eval row14234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14234, Integer.Sparse.eval_collectBalanced, rawRowCheck14234]

def rawRow14235 : Integer.Sparse Key := [(key2392, 4), (key2440, 4), (key2522, 4), (key2381, -2), (key2392, -2), (key2409, -2), (key2482, -2), (key2440, -2), (key2506, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2378, 4), (key2406, 4), (key2472, 4)]

theorem rawRowCheck14235 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form0 = rawRow14235 := by decide +kernel

def row14235 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

theorem rowCheck14235 : row14235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14235 := by decide +kernel

theorem rowEval14235 (x : Key → ℝ) : Integer.Sparse.eval row14235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14235, Integer.Sparse.eval_collectBalanced, rawRowCheck14235]

def rawRow14236 : Integer.Sparse Key := [(key2392, 4), (key2522, 4), (key2440, 4), (key2392, -2), (key2381, -2), (key2482, -2), (key2409, -2), (key2506, -2), (key2440, -2), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2378, 4), (key2472, 4), (key2406, 4)]

theorem rawRowCheck14236 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form0 = rawRow14236 := by decide +kernel

def row14236 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

theorem rowCheck14236 : row14236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14236 := by decide +kernel

theorem rowEval14236 (x : Key → ℝ) : Integer.Sparse.eval row14236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14236, Integer.Sparse.eval_collectBalanced, rawRowCheck14236]

def rawRow14237 : Integer.Sparse Key := [(key2440, 4), (key2392, 4), (key2522, 4), (key2409, -2), (key2440, -2), (key2381, -2), (key2506, -2), (key2392, -2), (key2482, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2406, 4), (key2378, 4), (key2472, 4)]

theorem rawRowCheck14237 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form0 = rawRow14237 := by decide +kernel

def row14237 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

theorem rowCheck14237 : row14237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14237 := by decide +kernel

theorem rowEval14237 (x : Key → ℝ) : Integer.Sparse.eval row14237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14237, Integer.Sparse.eval_collectBalanced, rawRowCheck14237]

def rawRow14238 : Integer.Sparse Key := [(key2440, 4), (key2522, 4), (key2392, 4), (key2440, -2), (key2409, -2), (key2506, -2), (key2381, -2), (key2482, -2), (key2392, -2), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2406, 4), (key2472, 4), (key2378, 4)]

theorem rawRowCheck14238 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form0 = rawRow14238 := by decide +kernel

def row14238 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

theorem rowCheck14238 : row14238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14238 := by decide +kernel

theorem rowEval14238 (x : Key → ℝ) : Integer.Sparse.eval row14238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14238, Integer.Sparse.eval_collectBalanced, rawRowCheck14238]

def rawRow14239 : Integer.Sparse Key := [(key2522, 4), (key2392, 4), (key2440, 4), (key2482, -2), (key2506, -2), (key2392, -2), (key2440, -2), (key2381, -2), (key2409, -2), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2472, 4), (key2378, 4), (key2406, 4)]

theorem rawRowCheck14239 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form0 = rawRow14239 := by decide +kernel

def row14239 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

theorem rowCheck14239 : row14239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14239 := by decide +kernel

theorem rowEval14239 (x : Key → ℝ) : Integer.Sparse.eval row14239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14239, Integer.Sparse.eval_collectBalanced, rawRowCheck14239]

def rawRow14240 : Integer.Sparse Key := [(key2522, 4), (key2440, 4), (key2392, 4), (key2506, -2), (key2482, -2), (key2440, -2), (key2392, -2), (key2409, -2), (key2381, -2), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2472, 4), (key2406, 4), (key2378, 4)]

theorem rawRowCheck14240 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form0 = rawRow14240 := by decide +kernel

def row14240 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

theorem rowCheck14240 : row14240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14240 := by decide +kernel

theorem rowEval14240 (x : Key → ℝ) : Integer.Sparse.eval row14240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14240, Integer.Sparse.eval_collectBalanced, rawRowCheck14240]

def rawRow14241 : Integer.Sparse Key := [(key1029, -2), (key1034, -2), (key1069, -2), (key1034, 6), (key1107, -2), (key1112, -2), (key1148, -2), (key994, 2), (key999, 2), (key1107, 2), (key1191, 2), (key1148, 2), (key1210, 2), (key999, -2), (key1112, -2), (key1191, -2), (key1121, 6), (key1013, -2), (key1121, -2), (key1197, -2)]

theorem rawRowCheck14241 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form1 = rawRow14241 := by decide +kernel

def row14241 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

theorem rowCheck14241 : row14241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14241 := by decide +kernel

theorem rowEval14241 (x : Key → ℝ) : Integer.Sparse.eval row14241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14241, Integer.Sparse.eval_collectBalanced, rawRowCheck14241]

def rawRow14242 : Integer.Sparse Key := [(key1034, -2), (key1029, -2), (key1069, -2), (key1034, 6), (key1112, -2), (key1107, -2), (key1148, -2), (key999, 2), (key994, 2), (key1191, 2), (key1107, 2), (key1210, 2), (key1148, 2), (key999, -2), (key1191, -2), (key1112, -2), (key1121, 6), (key1013, -2), (key1197, -2), (key1121, -2)]

theorem rawRowCheck14242 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form1 = rawRow14242 := by decide +kernel

def row14242 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

theorem rowCheck14242 : row14242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14242 := by decide +kernel

theorem rowEval14242 (x : Key → ℝ) : Integer.Sparse.eval row14242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14242, Integer.Sparse.eval_collectBalanced, rawRowCheck14242]

def rawRow14243 : Integer.Sparse Key := [(key1029, -2), (key1069, -2), (key1034, -2), (key1034, 6), (key1107, -2), (key1148, -2), (key1112, -2), (key1107, 2), (key1148, 2), (key994, 2), (key1210, 2), (key999, 2), (key1191, 2), (key1112, -2), (key999, -2), (key1191, -2), (key1121, 6), (key1121, -2), (key1013, -2), (key1197, -2)]

theorem rawRowCheck14243 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form1 = rawRow14243 := by decide +kernel

def row14243 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

theorem rowCheck14243 : row14243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14243 := by decide +kernel

theorem rowEval14243 (x : Key → ℝ) : Integer.Sparse.eval row14243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14243, Integer.Sparse.eval_collectBalanced, rawRowCheck14243]

def rawRow14244 : Integer.Sparse Key := [(key1069, -2), (key1029, -2), (key1034, -2), (key1034, 6), (key1148, -2), (key1107, -2), (key1112, -2), (key1148, 2), (key1107, 2), (key1210, 2), (key994, 2), (key1191, 2), (key999, 2), (key1112, -2), (key1191, -2), (key999, -2), (key1121, 6), (key1121, -2), (key1197, -2), (key1013, -2)]

theorem rawRowCheck14244 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form1 = rawRow14244 := by decide +kernel

def row14244 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

theorem rowCheck14244 : row14244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14244 := by decide +kernel

theorem rowEval14244 (x : Key → ℝ) : Integer.Sparse.eval row14244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14244, Integer.Sparse.eval_collectBalanced, rawRowCheck14244]

def rawRow14245 : Integer.Sparse Key := [(key1034, -2), (key1069, -2), (key1029, -2), (key1034, 6), (key1112, -2), (key1148, -2), (key1107, -2), (key1191, 2), (key1210, 2), (key999, 2), (key1148, 2), (key994, 2), (key1107, 2), (key1191, -2), (key999, -2), (key1112, -2), (key1121, 6), (key1197, -2), (key1013, -2), (key1121, -2)]

theorem rawRowCheck14245 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form1 = rawRow14245 := by decide +kernel

def row14245 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

theorem rowCheck14245 : row14245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14245 := by decide +kernel

theorem rowEval14245 (x : Key → ℝ) : Integer.Sparse.eval row14245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14245, Integer.Sparse.eval_collectBalanced, rawRowCheck14245]

def rawRow14246 : Integer.Sparse Key := [(key1069, -2), (key1034, -2), (key1029, -2), (key1034, 6), (key1148, -2), (key1112, -2), (key1107, -2), (key1210, 2), (key1191, 2), (key1148, 2), (key999, 2), (key1107, 2), (key994, 2), (key1191, -2), (key1112, -2), (key999, -2), (key1121, 6), (key1197, -2), (key1121, -2), (key1013, -2)]

theorem rawRowCheck14246 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form1 = rawRow14246 := by decide +kernel

def row14246 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

theorem rowCheck14246 : row14246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14246 := by decide +kernel

theorem rowEval14246 (x : Key → ℝ) : Integer.Sparse.eval row14246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14246, Integer.Sparse.eval_collectBalanced, rawRowCheck14246]

def rawRow14247 : Integer.Sparse Key := [(key1034, -2), (key1034, -2), (key1069, -2), (key1029, 6), (key1191, -2), (key1191, -2), (key1210, -2), (key999, 2), (key999, 2), (key1112, 2), (key1112, 2), (key1148, 2), (key1148, 2), (key994, -2), (key1107, -2), (key1107, -2), (key1197, 6), (key1013, -2), (key1121, -2), (key1121, -2)]

theorem rawRowCheck14247 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form1 = rawRow14247 := by decide +kernel

def row14247 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

theorem rowCheck14247 : row14247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14247 := by decide +kernel

theorem rowEval14247 (x : Key → ℝ) : Integer.Sparse.eval row14247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14247, Integer.Sparse.eval_collectBalanced, rawRowCheck14247]

def rawRow14248 : Integer.Sparse Key := [(key1034, -2), (key1069, -2), (key1034, -2), (key1029, 6), (key1191, -2), (key1210, -2), (key1191, -2), (key1112, 2), (key1148, 2), (key999, 2), (key1148, 2), (key999, 2), (key1112, 2), (key1107, -2), (key994, -2), (key1107, -2), (key1197, 6), (key1121, -2), (key1013, -2), (key1121, -2)]

theorem rawRowCheck14248 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form1 = rawRow14248 := by decide +kernel

def row14248 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

theorem rowCheck14248 : row14248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14248 := by decide +kernel

theorem rowEval14248 (x : Key → ℝ) : Integer.Sparse.eval row14248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14248, Integer.Sparse.eval_collectBalanced, rawRowCheck14248]

def rawRow14249 : Integer.Sparse Key := [(key1069, -2), (key1034, -2), (key1034, -2), (key1029, 6), (key1210, -2), (key1191, -2), (key1191, -2), (key1148, 2), (key1112, 2), (key1148, 2), (key999, 2), (key1112, 2), (key999, 2), (key1107, -2), (key1107, -2), (key994, -2), (key1197, 6), (key1121, -2), (key1121, -2), (key1013, -2)]

theorem rawRowCheck14249 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form1 = rawRow14249 := by decide +kernel

def row14249 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

theorem rowCheck14249 : row14249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14249 := by decide +kernel

theorem rowEval14249 (x : Key → ℝ) : Integer.Sparse.eval row14249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14249, Integer.Sparse.eval_collectBalanced, rawRowCheck14249]

def rawRow14250 : Integer.Sparse Key := [(key1107, -2), (key1112, -2), (key1148, -2), (key1121, 6), (key1029, -2), (key1034, -2), (key1069, -2), (key994, 2), (key999, 2), (key1107, 2), (key1191, 2), (key1148, 2), (key1210, 2), (key1013, -2), (key1121, -2), (key1197, -2), (key1034, 6), (key999, -2), (key1112, -2), (key1191, -2)]

theorem rawRowCheck14250 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form1 = rawRow14250 := by decide +kernel

def row14250 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

theorem rowCheck14250 : row14250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14250 := by decide +kernel

theorem rowEval14250 (x : Key → ℝ) : Integer.Sparse.eval row14250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14250, Integer.Sparse.eval_collectBalanced, rawRowCheck14250]

def rawRow14251 : Integer.Sparse Key := [(key1112, -2), (key1107, -2), (key1148, -2), (key1121, 6), (key1034, -2), (key1029, -2), (key1069, -2), (key999, 2), (key994, 2), (key1191, 2), (key1107, 2), (key1210, 2), (key1148, 2), (key1013, -2), (key1197, -2), (key1121, -2), (key1034, 6), (key999, -2), (key1191, -2), (key1112, -2)]

theorem rawRowCheck14251 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form1 = rawRow14251 := by decide +kernel

def row14251 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

theorem rowCheck14251 : row14251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14251 := by decide +kernel

theorem rowEval14251 (x : Key → ℝ) : Integer.Sparse.eval row14251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14251, Integer.Sparse.eval_collectBalanced, rawRowCheck14251]

def rawRow14252 : Integer.Sparse Key := [(key1107, -2), (key1148, -2), (key1112, -2), (key1121, 6), (key1029, -2), (key1069, -2), (key1034, -2), (key1107, 2), (key1148, 2), (key994, 2), (key1210, 2), (key999, 2), (key1191, 2), (key1121, -2), (key1013, -2), (key1197, -2), (key1034, 6), (key1112, -2), (key999, -2), (key1191, -2)]

theorem rawRowCheck14252 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form1 = rawRow14252 := by decide +kernel

def row14252 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

theorem rowCheck14252 : row14252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14252 := by decide +kernel

theorem rowEval14252 (x : Key → ℝ) : Integer.Sparse.eval row14252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14252, Integer.Sparse.eval_collectBalanced, rawRowCheck14252]

def rawRow14253 : Integer.Sparse Key := [(key1148, -2), (key1107, -2), (key1112, -2), (key1121, 6), (key1069, -2), (key1029, -2), (key1034, -2), (key1148, 2), (key1107, 2), (key1210, 2), (key994, 2), (key1191, 2), (key999, 2), (key1121, -2), (key1197, -2), (key1013, -2), (key1034, 6), (key1112, -2), (key1191, -2), (key999, -2)]

theorem rawRowCheck14253 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form1 = rawRow14253 := by decide +kernel

def row14253 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

theorem rowCheck14253 : row14253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14253 := by decide +kernel

theorem rowEval14253 (x : Key → ℝ) : Integer.Sparse.eval row14253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14253, Integer.Sparse.eval_collectBalanced, rawRowCheck14253]

def rawRow14254 : Integer.Sparse Key := [(key1112, -2), (key1148, -2), (key1107, -2), (key1121, 6), (key1034, -2), (key1069, -2), (key1029, -2), (key1191, 2), (key1210, 2), (key999, 2), (key1148, 2), (key994, 2), (key1107, 2), (key1197, -2), (key1013, -2), (key1121, -2), (key1034, 6), (key1191, -2), (key999, -2), (key1112, -2)]

theorem rawRowCheck14254 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form1 = rawRow14254 := by decide +kernel

def row14254 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

theorem rowCheck14254 : row14254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14254 := by decide +kernel

theorem rowEval14254 (x : Key → ℝ) : Integer.Sparse.eval row14254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14254, Integer.Sparse.eval_collectBalanced, rawRowCheck14254]

def rawRow14255 : Integer.Sparse Key := [(key1148, -2), (key1112, -2), (key1107, -2), (key1121, 6), (key1069, -2), (key1034, -2), (key1029, -2), (key1210, 2), (key1191, 2), (key1148, 2), (key999, 2), (key1107, 2), (key994, 2), (key1197, -2), (key1121, -2), (key1013, -2), (key1034, 6), (key1191, -2), (key1112, -2), (key999, -2)]

theorem rawRowCheck14255 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form1 = rawRow14255 := by decide +kernel

def row14255 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

theorem rowCheck14255 : row14255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14255 := by decide +kernel

theorem rowEval14255 (x : Key → ℝ) : Integer.Sparse.eval row14255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14255, Integer.Sparse.eval_collectBalanced, rawRowCheck14255]

def rawRow14256 : Integer.Sparse Key := [(key1107, -2), (key1121, -2), (key1148, -2), (key1112, 6), (key1107, -2), (key1121, -2), (key1148, -2), (key994, 2), (key1013, 2), (key1029, 2), (key1197, 2), (key1069, 2), (key1210, 2), (key999, -2), (key1034, -2), (key1191, -2), (key1112, 6), (key999, -2), (key1034, -2), (key1191, -2)]

theorem rawRowCheck14256 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form1 = rawRow14256 := by decide +kernel

def row14256 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

theorem rowCheck14256 : row14256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14256 := by decide +kernel

theorem rowEval14256 (x : Key → ℝ) : Integer.Sparse.eval row14256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14256, Integer.Sparse.eval_collectBalanced, rawRowCheck14256]

def rawRow14257 : Integer.Sparse Key := [(key1121, -2), (key1107, -2), (key1148, -2), (key1112, 6), (key1121, -2), (key1107, -2), (key1148, -2), (key1013, 2), (key994, 2), (key1197, 2), (key1029, 2), (key1210, 2), (key1069, 2), (key999, -2), (key1191, -2), (key1034, -2), (key1112, 6), (key999, -2), (key1191, -2), (key1034, -2)]

theorem rawRowCheck14257 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form1 = rawRow14257 := by decide +kernel

def row14257 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

theorem rowCheck14257 : row14257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14257 := by decide +kernel

theorem rowEval14257 (x : Key → ℝ) : Integer.Sparse.eval row14257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14257, Integer.Sparse.eval_collectBalanced, rawRowCheck14257]

def rawRow14258 : Integer.Sparse Key := [(key1107, -2), (key1148, -2), (key1121, -2), (key1112, 6), (key1107, -2), (key1148, -2), (key1121, -2), (key1029, 2), (key1069, 2), (key994, 2), (key1210, 2), (key1013, 2), (key1197, 2), (key1034, -2), (key999, -2), (key1191, -2), (key1112, 6), (key1034, -2), (key999, -2), (key1191, -2)]

theorem rawRowCheck14258 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form1 = rawRow14258 := by decide +kernel

def row14258 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

theorem rowCheck14258 : row14258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14258 := by decide +kernel

theorem rowEval14258 (x : Key → ℝ) : Integer.Sparse.eval row14258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14258, Integer.Sparse.eval_collectBalanced, rawRowCheck14258]

def rawRow14259 : Integer.Sparse Key := [(key1148, -2), (key1107, -2), (key1121, -2), (key1112, 6), (key1148, -2), (key1107, -2), (key1121, -2), (key1069, 2), (key1029, 2), (key1210, 2), (key994, 2), (key1197, 2), (key1013, 2), (key1034, -2), (key1191, -2), (key999, -2), (key1112, 6), (key1034, -2), (key1191, -2), (key999, -2)]

theorem rawRowCheck14259 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form1 = rawRow14259 := by decide +kernel

def row14259 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

theorem rowCheck14259 : row14259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14259 := by decide +kernel

theorem rowEval14259 (x : Key → ℝ) : Integer.Sparse.eval row14259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14259, Integer.Sparse.eval_collectBalanced, rawRowCheck14259]

def rawRow14260 : Integer.Sparse Key := [(key1121, -2), (key1148, -2), (key1107, -2), (key1112, 6), (key1121, -2), (key1148, -2), (key1107, -2), (key1197, 2), (key1210, 2), (key1013, 2), (key1069, 2), (key994, 2), (key1029, 2), (key1191, -2), (key999, -2), (key1034, -2), (key1112, 6), (key1191, -2), (key999, -2), (key1034, -2)]

theorem rawRowCheck14260 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form1 = rawRow14260 := by decide +kernel

def row14260 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

theorem rowCheck14260 : row14260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14260 := by decide +kernel

theorem rowEval14260 (x : Key → ℝ) : Integer.Sparse.eval row14260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14260, Integer.Sparse.eval_collectBalanced, rawRowCheck14260]

def rawRow14261 : Integer.Sparse Key := [(key1148, -2), (key1121, -2), (key1107, -2), (key1112, 6), (key1148, -2), (key1121, -2), (key1107, -2), (key1210, 2), (key1197, 2), (key1069, 2), (key1013, 2), (key1029, 2), (key994, 2), (key1191, -2), (key1034, -2), (key999, -2), (key1112, 6), (key1191, -2), (key1034, -2), (key999, -2)]

theorem rawRowCheck14261 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form1 = rawRow14261 := by decide +kernel

def row14261 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

theorem rowCheck14261 : row14261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14261 := by decide +kernel

theorem rowEval14261 (x : Key → ℝ) : Integer.Sparse.eval row14261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14261, Integer.Sparse.eval_collectBalanced, rawRowCheck14261]

def rawRow14262 : Integer.Sparse Key := [(key1112, -2), (key1121, -2), (key1148, -2), (key1107, 6), (key1191, -2), (key1197, -2), (key1210, -2), (key999, 2), (key1013, 2), (key1034, 2), (key1121, 2), (key1069, 2), (key1148, 2), (key994, -2), (key1029, -2), (key1107, -2), (key1191, 6), (key999, -2), (key1034, -2), (key1112, -2)]

theorem rawRowCheck14262 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form1 = rawRow14262 := by decide +kernel

def row14262 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck14262 : row14262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14262 := by decide +kernel

theorem rowEval14262 (x : Key → ℝ) : Integer.Sparse.eval row14262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14262, Integer.Sparse.eval_collectBalanced, rawRowCheck14262]

def rawRow14263 : Integer.Sparse Key := [(key1121, -2), (key1112, -2), (key1148, -2), (key1107, 6), (key1197, -2), (key1191, -2), (key1210, -2), (key1013, 2), (key999, 2), (key1121, 2), (key1034, 2), (key1148, 2), (key1069, 2), (key994, -2), (key1107, -2), (key1029, -2), (key1191, 6), (key999, -2), (key1112, -2), (key1034, -2)]

theorem rawRowCheck14263 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form1 = rawRow14263 := by decide +kernel

def row14263 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck14263 : row14263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14263 := by decide +kernel

theorem rowEval14263 (x : Key → ℝ) : Integer.Sparse.eval row14263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14263, Integer.Sparse.eval_collectBalanced, rawRowCheck14263]

def rawRow14264 : Integer.Sparse Key := [(key1112, -2), (key1148, -2), (key1121, -2), (key1107, 6), (key1191, -2), (key1210, -2), (key1197, -2), (key1034, 2), (key1069, 2), (key999, 2), (key1148, 2), (key1013, 2), (key1121, 2), (key1029, -2), (key994, -2), (key1107, -2), (key1191, 6), (key1034, -2), (key999, -2), (key1112, -2)]

theorem rawRowCheck14264 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form1 = rawRow14264 := by decide +kernel

def row14264 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck14264 : row14264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14264 := by decide +kernel

theorem rowEval14264 (x : Key → ℝ) : Integer.Sparse.eval row14264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14264, Integer.Sparse.eval_collectBalanced, rawRowCheck14264]

def rawRow14265 : Integer.Sparse Key := [(key1148, -2), (key1112, -2), (key1121, -2), (key1107, 6), (key1210, -2), (key1191, -2), (key1197, -2), (key1069, 2), (key1034, 2), (key1148, 2), (key999, 2), (key1121, 2), (key1013, 2), (key1029, -2), (key1107, -2), (key994, -2), (key1191, 6), (key1034, -2), (key1112, -2), (key999, -2)]

theorem rawRowCheck14265 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form1 = rawRow14265 := by decide +kernel

def row14265 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck14265 : row14265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14265 := by decide +kernel

theorem rowEval14265 (x : Key → ℝ) : Integer.Sparse.eval row14265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14265, Integer.Sparse.eval_collectBalanced, rawRowCheck14265]

def rawRow14266 : Integer.Sparse Key := [(key1121, -2), (key1148, -2), (key1112, -2), (key1107, 6), (key1197, -2), (key1210, -2), (key1191, -2), (key1121, 2), (key1148, 2), (key1013, 2), (key1069, 2), (key999, 2), (key1034, 2), (key1107, -2), (key994, -2), (key1029, -2), (key1191, 6), (key1112, -2), (key999, -2), (key1034, -2)]

theorem rawRowCheck14266 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form1 = rawRow14266 := by decide +kernel

def row14266 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck14266 : row14266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14266 := by decide +kernel

theorem rowEval14266 (x : Key → ℝ) : Integer.Sparse.eval row14266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14266, Integer.Sparse.eval_collectBalanced, rawRowCheck14266]

def rawRow14267 : Integer.Sparse Key := [(key1148, -2), (key1121, -2), (key1112, -2), (key1107, 6), (key1210, -2), (key1197, -2), (key1191, -2), (key1148, 2), (key1121, 2), (key1069, 2), (key1013, 2), (key1034, 2), (key999, 2), (key1107, -2), (key1029, -2), (key994, -2), (key1191, 6), (key1112, -2), (key1034, -2), (key999, -2)]

theorem rawRowCheck14267 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form1 = rawRow14267 := by decide +kernel

def row14267 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck14267 : row14267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14267 := by decide +kernel

theorem rowEval14267 (x : Key → ℝ) : Integer.Sparse.eval row14267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14267, Integer.Sparse.eval_collectBalanced, rawRowCheck14267]

def rawRow14268 : Integer.Sparse Key := [(key1191, -2), (key1191, -2), (key1210, -2), (key1197, 6), (key1034, -2), (key1034, -2), (key1069, -2), (key999, 2), (key999, 2), (key1112, 2), (key1112, 2), (key1148, 2), (key1148, 2), (key1013, -2), (key1121, -2), (key1121, -2), (key1029, 6), (key994, -2), (key1107, -2), (key1107, -2)]

theorem rawRowCheck14268 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form1 = rawRow14268 := by decide +kernel

def row14268 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

theorem rowCheck14268 : row14268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14268 := by decide +kernel

theorem rowEval14268 (x : Key → ℝ) : Integer.Sparse.eval row14268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14268, Integer.Sparse.eval_collectBalanced, rawRowCheck14268]

def rawRow14269 : Integer.Sparse Key := [(key1191, -2), (key1210, -2), (key1191, -2), (key1197, 6), (key1034, -2), (key1069, -2), (key1034, -2), (key1112, 2), (key1148, 2), (key999, 2), (key1148, 2), (key999, 2), (key1112, 2), (key1121, -2), (key1013, -2), (key1121, -2), (key1029, 6), (key1107, -2), (key994, -2), (key1107, -2)]

theorem rawRowCheck14269 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form1 = rawRow14269 := by decide +kernel

def row14269 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

theorem rowCheck14269 : row14269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14269 := by decide +kernel

theorem rowEval14269 (x : Key → ℝ) : Integer.Sparse.eval row14269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14269, Integer.Sparse.eval_collectBalanced, rawRowCheck14269]

def rawRow14270 : Integer.Sparse Key := [(key1210, -2), (key1191, -2), (key1191, -2), (key1197, 6), (key1069, -2), (key1034, -2), (key1034, -2), (key1148, 2), (key1112, 2), (key1148, 2), (key999, 2), (key1112, 2), (key999, 2), (key1121, -2), (key1121, -2), (key1013, -2), (key1029, 6), (key1107, -2), (key1107, -2), (key994, -2)]

theorem rawRowCheck14270 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form1 = rawRow14270 := by decide +kernel

def row14270 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

theorem rowCheck14270 : row14270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14270 := by decide +kernel

theorem rowEval14270 (x : Key → ℝ) : Integer.Sparse.eval row14270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14270, Integer.Sparse.eval_collectBalanced, rawRowCheck14270]

def rawRow14271 : Integer.Sparse Key := [(key1191, -2), (key1197, -2), (key1210, -2), (key1191, 6), (key1112, -2), (key1121, -2), (key1148, -2), (key999, 2), (key1013, 2), (key1034, 2), (key1121, 2), (key1069, 2), (key1148, 2), (key999, -2), (key1034, -2), (key1112, -2), (key1107, 6), (key994, -2), (key1029, -2), (key1107, -2)]

theorem rawRowCheck14271 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form1 = rawRow14271 := by decide +kernel

def row14271 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck14271 : row14271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14271 := by decide +kernel

theorem rowEval14271 (x : Key → ℝ) : Integer.Sparse.eval row14271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14271, Integer.Sparse.eval_collectBalanced, rawRowCheck14271]

def rawRow14272 : Integer.Sparse Key := [(key1197, -2), (key1191, -2), (key1210, -2), (key1191, 6), (key1121, -2), (key1112, -2), (key1148, -2), (key1013, 2), (key999, 2), (key1121, 2), (key1034, 2), (key1148, 2), (key1069, 2), (key999, -2), (key1112, -2), (key1034, -2), (key1107, 6), (key994, -2), (key1107, -2), (key1029, -2)]

theorem rawRowCheck14272 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form1 = rawRow14272 := by decide +kernel

def row14272 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck14272 : row14272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14272 := by decide +kernel

theorem rowEval14272 (x : Key → ℝ) : Integer.Sparse.eval row14272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14272, Integer.Sparse.eval_collectBalanced, rawRowCheck14272]

def rawRow14273 : Integer.Sparse Key := [(key1191, -2), (key1210, -2), (key1197, -2), (key1191, 6), (key1112, -2), (key1148, -2), (key1121, -2), (key1034, 2), (key1069, 2), (key999, 2), (key1148, 2), (key1013, 2), (key1121, 2), (key1034, -2), (key999, -2), (key1112, -2), (key1107, 6), (key1029, -2), (key994, -2), (key1107, -2)]

theorem rawRowCheck14273 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form1 = rawRow14273 := by decide +kernel

def row14273 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck14273 : row14273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14273 := by decide +kernel

theorem rowEval14273 (x : Key → ℝ) : Integer.Sparse.eval row14273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14273, Integer.Sparse.eval_collectBalanced, rawRowCheck14273]

def rawRow14274 : Integer.Sparse Key := [(key1210, -2), (key1191, -2), (key1197, -2), (key1191, 6), (key1148, -2), (key1112, -2), (key1121, -2), (key1069, 2), (key1034, 2), (key1148, 2), (key999, 2), (key1121, 2), (key1013, 2), (key1034, -2), (key1112, -2), (key999, -2), (key1107, 6), (key1029, -2), (key1107, -2), (key994, -2)]

theorem rawRowCheck14274 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form1 = rawRow14274 := by decide +kernel

def row14274 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck14274 : row14274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14274 := by decide +kernel

theorem rowEval14274 (x : Key → ℝ) : Integer.Sparse.eval row14274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14274, Integer.Sparse.eval_collectBalanced, rawRowCheck14274]

def rawRow14275 : Integer.Sparse Key := [(key1197, -2), (key1210, -2), (key1191, -2), (key1191, 6), (key1121, -2), (key1148, -2), (key1112, -2), (key1121, 2), (key1148, 2), (key1013, 2), (key1069, 2), (key999, 2), (key1034, 2), (key1112, -2), (key999, -2), (key1034, -2), (key1107, 6), (key1107, -2), (key994, -2), (key1029, -2)]

theorem rawRowCheck14275 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form1 = rawRow14275 := by decide +kernel

def row14275 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck14275 : row14275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14275 := by decide +kernel

theorem rowEval14275 (x : Key → ℝ) : Integer.Sparse.eval row14275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14275, Integer.Sparse.eval_collectBalanced, rawRowCheck14275]

def rawRow14276 : Integer.Sparse Key := [(key1210, -2), (key1197, -2), (key1191, -2), (key1191, 6), (key1148, -2), (key1121, -2), (key1112, -2), (key1148, 2), (key1121, 2), (key1069, 2), (key1013, 2), (key1034, 2), (key999, 2), (key1112, -2), (key1034, -2), (key999, -2), (key1107, 6), (key1107, -2), (key1029, -2), (key994, -2)]

theorem rawRowCheck14276 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form1 = rawRow14276 := by decide +kernel

def row14276 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck14276 : row14276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14276 := by decide +kernel

theorem rowEval14276 (x : Key → ℝ) : Integer.Sparse.eval row14276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14276, Integer.Sparse.eval_collectBalanced, rawRowCheck14276]

def rawRow14277 : Integer.Sparse Key := [(key2399, -2), (key2403, -2), (key2434, -2), (key2403, 6), (key2465, -2), (key2469, -2), (key2500, -2), (key2371, 2), (key2375, 2), (key2465, 2), (key2536, 2), (key2500, 2), (key2552, 2), (key2375, -2), (key2469, -2), (key2536, -2), (key2477, 6), (key2387, -2), (key2477, -2), (key2541, -2)]

theorem rawRowCheck14277 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form2 = rawRow14277 := by decide +kernel

def row14277 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

theorem rowCheck14277 : row14277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14277 := by decide +kernel

theorem rowEval14277 (x : Key → ℝ) : Integer.Sparse.eval row14277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14277, Integer.Sparse.eval_collectBalanced, rawRowCheck14277]

def rawRow14278 : Integer.Sparse Key := [(key2403, -2), (key2399, -2), (key2434, -2), (key2403, 6), (key2469, -2), (key2465, -2), (key2500, -2), (key2375, 2), (key2371, 2), (key2536, 2), (key2465, 2), (key2552, 2), (key2500, 2), (key2375, -2), (key2536, -2), (key2469, -2), (key2477, 6), (key2387, -2), (key2541, -2), (key2477, -2)]

theorem rawRowCheck14278 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form2 = rawRow14278 := by decide +kernel

def row14278 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

theorem rowCheck14278 : row14278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14278 := by decide +kernel

theorem rowEval14278 (x : Key → ℝ) : Integer.Sparse.eval row14278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14278, Integer.Sparse.eval_collectBalanced, rawRowCheck14278]

def rawRow14279 : Integer.Sparse Key := [(key2399, -2), (key2434, -2), (key2403, -2), (key2403, 6), (key2465, -2), (key2500, -2), (key2469, -2), (key2465, 2), (key2500, 2), (key2371, 2), (key2552, 2), (key2375, 2), (key2536, 2), (key2469, -2), (key2375, -2), (key2536, -2), (key2477, 6), (key2477, -2), (key2387, -2), (key2541, -2)]

theorem rawRowCheck14279 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form2 = rawRow14279 := by decide +kernel

def row14279 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

theorem rowCheck14279 : row14279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14279 := by decide +kernel

theorem rowEval14279 (x : Key → ℝ) : Integer.Sparse.eval row14279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14279, Integer.Sparse.eval_collectBalanced, rawRowCheck14279]

def rawRow14280 : Integer.Sparse Key := [(key2434, -2), (key2399, -2), (key2403, -2), (key2403, 6), (key2500, -2), (key2465, -2), (key2469, -2), (key2500, 2), (key2465, 2), (key2552, 2), (key2371, 2), (key2536, 2), (key2375, 2), (key2469, -2), (key2536, -2), (key2375, -2), (key2477, 6), (key2477, -2), (key2541, -2), (key2387, -2)]

theorem rawRowCheck14280 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form2 = rawRow14280 := by decide +kernel

def row14280 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

theorem rowCheck14280 : row14280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14280 := by decide +kernel

theorem rowEval14280 (x : Key → ℝ) : Integer.Sparse.eval row14280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14280, Integer.Sparse.eval_collectBalanced, rawRowCheck14280]

def rawRow14281 : Integer.Sparse Key := [(key2403, -2), (key2434, -2), (key2399, -2), (key2403, 6), (key2469, -2), (key2500, -2), (key2465, -2), (key2536, 2), (key2552, 2), (key2375, 2), (key2500, 2), (key2371, 2), (key2465, 2), (key2536, -2), (key2375, -2), (key2469, -2), (key2477, 6), (key2541, -2), (key2387, -2), (key2477, -2)]

theorem rawRowCheck14281 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form2 = rawRow14281 := by decide +kernel

def row14281 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

theorem rowCheck14281 : row14281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14281 := by decide +kernel

theorem rowEval14281 (x : Key → ℝ) : Integer.Sparse.eval row14281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14281, Integer.Sparse.eval_collectBalanced, rawRowCheck14281]

def rawRow14282 : Integer.Sparse Key := [(key2434, -2), (key2403, -2), (key2399, -2), (key2403, 6), (key2500, -2), (key2469, -2), (key2465, -2), (key2552, 2), (key2536, 2), (key2500, 2), (key2375, 2), (key2465, 2), (key2371, 2), (key2536, -2), (key2469, -2), (key2375, -2), (key2477, 6), (key2541, -2), (key2477, -2), (key2387, -2)]

theorem rawRowCheck14282 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form2 = rawRow14282 := by decide +kernel

def row14282 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

theorem rowCheck14282 : row14282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14282 := by decide +kernel

theorem rowEval14282 (x : Key → ℝ) : Integer.Sparse.eval row14282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14282, Integer.Sparse.eval_collectBalanced, rawRowCheck14282]

def rawRow14283 : Integer.Sparse Key := [(key2403, -2), (key2403, -2), (key2434, -2), (key2399, 6), (key2536, -2), (key2536, -2), (key2552, -2), (key2375, 2), (key2375, 2), (key2469, 2), (key2469, 2), (key2500, 2), (key2500, 2), (key2371, -2), (key2465, -2), (key2465, -2), (key2541, 6), (key2387, -2), (key2477, -2), (key2477, -2)]

theorem rawRowCheck14283 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form2 = rawRow14283 := by decide +kernel

def row14283 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

theorem rowCheck14283 : row14283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14283 := by decide +kernel

theorem rowEval14283 (x : Key → ℝ) : Integer.Sparse.eval row14283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14283, Integer.Sparse.eval_collectBalanced, rawRowCheck14283]

def rawRow14284 : Integer.Sparse Key := [(key2403, -2), (key2434, -2), (key2403, -2), (key2399, 6), (key2536, -2), (key2552, -2), (key2536, -2), (key2469, 2), (key2500, 2), (key2375, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2465, -2), (key2371, -2), (key2465, -2), (key2541, 6), (key2477, -2), (key2387, -2), (key2477, -2)]

theorem rawRowCheck14284 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form2 = rawRow14284 := by decide +kernel

def row14284 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

theorem rowCheck14284 : row14284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14284 := by decide +kernel

theorem rowEval14284 (x : Key → ℝ) : Integer.Sparse.eval row14284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14284, Integer.Sparse.eval_collectBalanced, rawRowCheck14284]

def rawRow14285 : Integer.Sparse Key := [(key2434, -2), (key2403, -2), (key2403, -2), (key2399, 6), (key2552, -2), (key2536, -2), (key2536, -2), (key2500, 2), (key2469, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2375, 2), (key2465, -2), (key2465, -2), (key2371, -2), (key2541, 6), (key2477, -2), (key2477, -2), (key2387, -2)]

theorem rawRowCheck14285 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form2 = rawRow14285 := by decide +kernel

def row14285 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

theorem rowCheck14285 : row14285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14285 := by decide +kernel

theorem rowEval14285 (x : Key → ℝ) : Integer.Sparse.eval row14285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14285, Integer.Sparse.eval_collectBalanced, rawRowCheck14285]

def rawRow14286 : Integer.Sparse Key := [(key2465, -2), (key2469, -2), (key2500, -2), (key2477, 6), (key2399, -2), (key2403, -2), (key2434, -2), (key2371, 2), (key2375, 2), (key2465, 2), (key2536, 2), (key2500, 2), (key2552, 2), (key2387, -2), (key2477, -2), (key2541, -2), (key2403, 6), (key2375, -2), (key2469, -2), (key2536, -2)]

theorem rawRowCheck14286 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form2 = rawRow14286 := by decide +kernel

def row14286 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

theorem rowCheck14286 : row14286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14286 := by decide +kernel

theorem rowEval14286 (x : Key → ℝ) : Integer.Sparse.eval row14286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14286, Integer.Sparse.eval_collectBalanced, rawRowCheck14286]

def rawRow14287 : Integer.Sparse Key := [(key2469, -2), (key2465, -2), (key2500, -2), (key2477, 6), (key2403, -2), (key2399, -2), (key2434, -2), (key2375, 2), (key2371, 2), (key2536, 2), (key2465, 2), (key2552, 2), (key2500, 2), (key2387, -2), (key2541, -2), (key2477, -2), (key2403, 6), (key2375, -2), (key2536, -2), (key2469, -2)]

theorem rawRowCheck14287 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form2 = rawRow14287 := by decide +kernel

def row14287 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

theorem rowCheck14287 : row14287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14287 := by decide +kernel

theorem rowEval14287 (x : Key → ℝ) : Integer.Sparse.eval row14287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14287, Integer.Sparse.eval_collectBalanced, rawRowCheck14287]

def rawRow14288 : Integer.Sparse Key := [(key2465, -2), (key2500, -2), (key2469, -2), (key2477, 6), (key2399, -2), (key2434, -2), (key2403, -2), (key2465, 2), (key2500, 2), (key2371, 2), (key2552, 2), (key2375, 2), (key2536, 2), (key2477, -2), (key2387, -2), (key2541, -2), (key2403, 6), (key2469, -2), (key2375, -2), (key2536, -2)]

theorem rawRowCheck14288 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form2 = rawRow14288 := by decide +kernel

def row14288 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

theorem rowCheck14288 : row14288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14288 := by decide +kernel

theorem rowEval14288 (x : Key → ℝ) : Integer.Sparse.eval row14288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14288, Integer.Sparse.eval_collectBalanced, rawRowCheck14288]

def rawRow14289 : Integer.Sparse Key := [(key2500, -2), (key2465, -2), (key2469, -2), (key2477, 6), (key2434, -2), (key2399, -2), (key2403, -2), (key2500, 2), (key2465, 2), (key2552, 2), (key2371, 2), (key2536, 2), (key2375, 2), (key2477, -2), (key2541, -2), (key2387, -2), (key2403, 6), (key2469, -2), (key2536, -2), (key2375, -2)]

theorem rawRowCheck14289 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form2 = rawRow14289 := by decide +kernel

def row14289 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

theorem rowCheck14289 : row14289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14289 := by decide +kernel

theorem rowEval14289 (x : Key → ℝ) : Integer.Sparse.eval row14289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14289, Integer.Sparse.eval_collectBalanced, rawRowCheck14289]

def rawRow14290 : Integer.Sparse Key := [(key2469, -2), (key2500, -2), (key2465, -2), (key2477, 6), (key2403, -2), (key2434, -2), (key2399, -2), (key2536, 2), (key2552, 2), (key2375, 2), (key2500, 2), (key2371, 2), (key2465, 2), (key2541, -2), (key2387, -2), (key2477, -2), (key2403, 6), (key2536, -2), (key2375, -2), (key2469, -2)]

theorem rawRowCheck14290 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form2 = rawRow14290 := by decide +kernel

def row14290 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

theorem rowCheck14290 : row14290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14290 := by decide +kernel

theorem rowEval14290 (x : Key → ℝ) : Integer.Sparse.eval row14290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14290, Integer.Sparse.eval_collectBalanced, rawRowCheck14290]

def rawRow14291 : Integer.Sparse Key := [(key2500, -2), (key2469, -2), (key2465, -2), (key2477, 6), (key2434, -2), (key2403, -2), (key2399, -2), (key2552, 2), (key2536, 2), (key2500, 2), (key2375, 2), (key2465, 2), (key2371, 2), (key2541, -2), (key2477, -2), (key2387, -2), (key2403, 6), (key2536, -2), (key2469, -2), (key2375, -2)]

theorem rawRowCheck14291 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form2 = rawRow14291 := by decide +kernel

def row14291 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

theorem rowCheck14291 : row14291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14291 := by decide +kernel

theorem rowEval14291 (x : Key → ℝ) : Integer.Sparse.eval row14291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14291, Integer.Sparse.eval_collectBalanced, rawRowCheck14291]

def rawRow14292 : Integer.Sparse Key := [(key2465, -2), (key2477, -2), (key2500, -2), (key2469, 6), (key2465, -2), (key2477, -2), (key2500, -2), (key2371, 2), (key2387, 2), (key2399, 2), (key2541, 2), (key2434, 2), (key2552, 2), (key2375, -2), (key2403, -2), (key2536, -2), (key2469, 6), (key2375, -2), (key2403, -2), (key2536, -2)]

theorem rawRowCheck14292 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form2 = rawRow14292 := by decide +kernel

def row14292 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

theorem rowCheck14292 : row14292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14292 := by decide +kernel

theorem rowEval14292 (x : Key → ℝ) : Integer.Sparse.eval row14292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14292, Integer.Sparse.eval_collectBalanced, rawRowCheck14292]

def rawRow14293 : Integer.Sparse Key := [(key2477, -2), (key2465, -2), (key2500, -2), (key2469, 6), (key2477, -2), (key2465, -2), (key2500, -2), (key2387, 2), (key2371, 2), (key2541, 2), (key2399, 2), (key2552, 2), (key2434, 2), (key2375, -2), (key2536, -2), (key2403, -2), (key2469, 6), (key2375, -2), (key2536, -2), (key2403, -2)]

theorem rawRowCheck14293 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form2 = rawRow14293 := by decide +kernel

def row14293 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

theorem rowCheck14293 : row14293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14293 := by decide +kernel

theorem rowEval14293 (x : Key → ℝ) : Integer.Sparse.eval row14293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14293, Integer.Sparse.eval_collectBalanced, rawRowCheck14293]

def rawRow14294 : Integer.Sparse Key := [(key2465, -2), (key2500, -2), (key2477, -2), (key2469, 6), (key2465, -2), (key2500, -2), (key2477, -2), (key2399, 2), (key2434, 2), (key2371, 2), (key2552, 2), (key2387, 2), (key2541, 2), (key2403, -2), (key2375, -2), (key2536, -2), (key2469, 6), (key2403, -2), (key2375, -2), (key2536, -2)]

theorem rawRowCheck14294 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form2 = rawRow14294 := by decide +kernel

def row14294 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

theorem rowCheck14294 : row14294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14294 := by decide +kernel

theorem rowEval14294 (x : Key → ℝ) : Integer.Sparse.eval row14294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14294, Integer.Sparse.eval_collectBalanced, rawRowCheck14294]

def rawRow14295 : Integer.Sparse Key := [(key2500, -2), (key2465, -2), (key2477, -2), (key2469, 6), (key2500, -2), (key2465, -2), (key2477, -2), (key2434, 2), (key2399, 2), (key2552, 2), (key2371, 2), (key2541, 2), (key2387, 2), (key2403, -2), (key2536, -2), (key2375, -2), (key2469, 6), (key2403, -2), (key2536, -2), (key2375, -2)]

theorem rawRowCheck14295 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form2 = rawRow14295 := by decide +kernel

def row14295 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

theorem rowCheck14295 : row14295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14295 := by decide +kernel

theorem rowEval14295 (x : Key → ℝ) : Integer.Sparse.eval row14295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14295, Integer.Sparse.eval_collectBalanced, rawRowCheck14295]

def rawRow14296 : Integer.Sparse Key := [(key2477, -2), (key2500, -2), (key2465, -2), (key2469, 6), (key2477, -2), (key2500, -2), (key2465, -2), (key2541, 2), (key2552, 2), (key2387, 2), (key2434, 2), (key2371, 2), (key2399, 2), (key2536, -2), (key2375, -2), (key2403, -2), (key2469, 6), (key2536, -2), (key2375, -2), (key2403, -2)]

theorem rawRowCheck14296 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form2 = rawRow14296 := by decide +kernel

def row14296 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

theorem rowCheck14296 : row14296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14296 := by decide +kernel

theorem rowEval14296 (x : Key → ℝ) : Integer.Sparse.eval row14296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14296, Integer.Sparse.eval_collectBalanced, rawRowCheck14296]

def rawRow14297 : Integer.Sparse Key := [(key2500, -2), (key2477, -2), (key2465, -2), (key2469, 6), (key2500, -2), (key2477, -2), (key2465, -2), (key2552, 2), (key2541, 2), (key2434, 2), (key2387, 2), (key2399, 2), (key2371, 2), (key2536, -2), (key2403, -2), (key2375, -2), (key2469, 6), (key2536, -2), (key2403, -2), (key2375, -2)]

theorem rawRowCheck14297 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form2 = rawRow14297 := by decide +kernel

def row14297 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

theorem rowCheck14297 : row14297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14297 := by decide +kernel

theorem rowEval14297 (x : Key → ℝ) : Integer.Sparse.eval row14297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14297, Integer.Sparse.eval_collectBalanced, rawRowCheck14297]

def rawRow14298 : Integer.Sparse Key := [(key2469, -2), (key2477, -2), (key2500, -2), (key2465, 6), (key2536, -2), (key2541, -2), (key2552, -2), (key2375, 2), (key2387, 2), (key2403, 2), (key2477, 2), (key2434, 2), (key2500, 2), (key2371, -2), (key2399, -2), (key2465, -2), (key2536, 6), (key2375, -2), (key2403, -2), (key2469, -2)]

theorem rawRowCheck14298 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form2 = rawRow14298 := by decide +kernel

def row14298 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck14298 : row14298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14298 := by decide +kernel

theorem rowEval14298 (x : Key → ℝ) : Integer.Sparse.eval row14298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14298, Integer.Sparse.eval_collectBalanced, rawRowCheck14298]

def rawRow14299 : Integer.Sparse Key := [(key2477, -2), (key2469, -2), (key2500, -2), (key2465, 6), (key2541, -2), (key2536, -2), (key2552, -2), (key2387, 2), (key2375, 2), (key2477, 2), (key2403, 2), (key2500, 2), (key2434, 2), (key2371, -2), (key2465, -2), (key2399, -2), (key2536, 6), (key2375, -2), (key2469, -2), (key2403, -2)]

theorem rawRowCheck14299 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form2 = rawRow14299 := by decide +kernel

def row14299 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck14299 : row14299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14299 := by decide +kernel

theorem rowEval14299 (x : Key → ℝ) : Integer.Sparse.eval row14299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14299, Integer.Sparse.eval_collectBalanced, rawRowCheck14299]

def rawRow14300 : Integer.Sparse Key := [(key2469, -2), (key2500, -2), (key2477, -2), (key2465, 6), (key2536, -2), (key2552, -2), (key2541, -2), (key2403, 2), (key2434, 2), (key2375, 2), (key2500, 2), (key2387, 2), (key2477, 2), (key2399, -2), (key2371, -2), (key2465, -2), (key2536, 6), (key2403, -2), (key2375, -2), (key2469, -2)]

theorem rawRowCheck14300 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form2 = rawRow14300 := by decide +kernel

def row14300 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck14300 : row14300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14300 := by decide +kernel

theorem rowEval14300 (x : Key → ℝ) : Integer.Sparse.eval row14300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14300, Integer.Sparse.eval_collectBalanced, rawRowCheck14300]

def rawRow14301 : Integer.Sparse Key := [(key2500, -2), (key2469, -2), (key2477, -2), (key2465, 6), (key2552, -2), (key2536, -2), (key2541, -2), (key2434, 2), (key2403, 2), (key2500, 2), (key2375, 2), (key2477, 2), (key2387, 2), (key2399, -2), (key2465, -2), (key2371, -2), (key2536, 6), (key2403, -2), (key2469, -2), (key2375, -2)]

theorem rawRowCheck14301 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form2 = rawRow14301 := by decide +kernel

def row14301 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck14301 : row14301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14301 := by decide +kernel

theorem rowEval14301 (x : Key → ℝ) : Integer.Sparse.eval row14301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14301, Integer.Sparse.eval_collectBalanced, rawRowCheck14301]

def rawRow14302 : Integer.Sparse Key := [(key2477, -2), (key2500, -2), (key2469, -2), (key2465, 6), (key2541, -2), (key2552, -2), (key2536, -2), (key2477, 2), (key2500, 2), (key2387, 2), (key2434, 2), (key2375, 2), (key2403, 2), (key2465, -2), (key2371, -2), (key2399, -2), (key2536, 6), (key2469, -2), (key2375, -2), (key2403, -2)]

theorem rawRowCheck14302 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form2 = rawRow14302 := by decide +kernel

def row14302 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck14302 : row14302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14302 := by decide +kernel

theorem rowEval14302 (x : Key → ℝ) : Integer.Sparse.eval row14302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14302, Integer.Sparse.eval_collectBalanced, rawRowCheck14302]

def rawRow14303 : Integer.Sparse Key := [(key2500, -2), (key2477, -2), (key2469, -2), (key2465, 6), (key2552, -2), (key2541, -2), (key2536, -2), (key2500, 2), (key2477, 2), (key2434, 2), (key2387, 2), (key2403, 2), (key2375, 2), (key2465, -2), (key2399, -2), (key2371, -2), (key2536, 6), (key2469, -2), (key2403, -2), (key2375, -2)]

theorem rawRowCheck14303 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form2 = rawRow14303 := by decide +kernel

def row14303 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck14303 : row14303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14303 := by decide +kernel

theorem rowEval14303 (x : Key → ℝ) : Integer.Sparse.eval row14303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14303, Integer.Sparse.eval_collectBalanced, rawRowCheck14303]

def rawRow14304 : Integer.Sparse Key := [(key2536, -2), (key2536, -2), (key2552, -2), (key2541, 6), (key2403, -2), (key2403, -2), (key2434, -2), (key2375, 2), (key2375, 2), (key2469, 2), (key2469, 2), (key2500, 2), (key2500, 2), (key2387, -2), (key2477, -2), (key2477, -2), (key2399, 6), (key2371, -2), (key2465, -2), (key2465, -2)]

theorem rawRowCheck14304 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form2 = rawRow14304 := by decide +kernel

def row14304 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

theorem rowCheck14304 : row14304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14304 := by decide +kernel

theorem rowEval14304 (x : Key → ℝ) : Integer.Sparse.eval row14304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14304, Integer.Sparse.eval_collectBalanced, rawRowCheck14304]

def rawRow14305 : Integer.Sparse Key := [(key2536, -2), (key2552, -2), (key2536, -2), (key2541, 6), (key2403, -2), (key2434, -2), (key2403, -2), (key2469, 2), (key2500, 2), (key2375, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2477, -2), (key2387, -2), (key2477, -2), (key2399, 6), (key2465, -2), (key2371, -2), (key2465, -2)]

theorem rawRowCheck14305 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form2 = rawRow14305 := by decide +kernel

def row14305 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

theorem rowCheck14305 : row14305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14305 := by decide +kernel

theorem rowEval14305 (x : Key → ℝ) : Integer.Sparse.eval row14305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14305, Integer.Sparse.eval_collectBalanced, rawRowCheck14305]

def rawRow14306 : Integer.Sparse Key := [(key2552, -2), (key2536, -2), (key2536, -2), (key2541, 6), (key2434, -2), (key2403, -2), (key2403, -2), (key2500, 2), (key2469, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2375, 2), (key2477, -2), (key2477, -2), (key2387, -2), (key2399, 6), (key2465, -2), (key2465, -2), (key2371, -2)]

theorem rawRowCheck14306 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form2 = rawRow14306 := by decide +kernel

def row14306 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

theorem rowCheck14306 : row14306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14306 := by decide +kernel

theorem rowEval14306 (x : Key → ℝ) : Integer.Sparse.eval row14306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14306, Integer.Sparse.eval_collectBalanced, rawRowCheck14306]

def rawRow14307 : Integer.Sparse Key := [(key2536, -2), (key2541, -2), (key2552, -2), (key2536, 6), (key2469, -2), (key2477, -2), (key2500, -2), (key2375, 2), (key2387, 2), (key2403, 2), (key2477, 2), (key2434, 2), (key2500, 2), (key2375, -2), (key2403, -2), (key2469, -2), (key2465, 6), (key2371, -2), (key2399, -2), (key2465, -2)]

theorem rawRowCheck14307 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form2 = rawRow14307 := by decide +kernel

def row14307 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck14307 : row14307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14307 := by decide +kernel

theorem rowEval14307 (x : Key → ℝ) : Integer.Sparse.eval row14307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14307, Integer.Sparse.eval_collectBalanced, rawRowCheck14307]

def rawRow14308 : Integer.Sparse Key := [(key2541, -2), (key2536, -2), (key2552, -2), (key2536, 6), (key2477, -2), (key2469, -2), (key2500, -2), (key2387, 2), (key2375, 2), (key2477, 2), (key2403, 2), (key2500, 2), (key2434, 2), (key2375, -2), (key2469, -2), (key2403, -2), (key2465, 6), (key2371, -2), (key2465, -2), (key2399, -2)]

theorem rawRowCheck14308 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form2 = rawRow14308 := by decide +kernel

def row14308 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck14308 : row14308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14308 := by decide +kernel

theorem rowEval14308 (x : Key → ℝ) : Integer.Sparse.eval row14308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14308, Integer.Sparse.eval_collectBalanced, rawRowCheck14308]

def rawRow14309 : Integer.Sparse Key := [(key2536, -2), (key2552, -2), (key2541, -2), (key2536, 6), (key2469, -2), (key2500, -2), (key2477, -2), (key2403, 2), (key2434, 2), (key2375, 2), (key2500, 2), (key2387, 2), (key2477, 2), (key2403, -2), (key2375, -2), (key2469, -2), (key2465, 6), (key2399, -2), (key2371, -2), (key2465, -2)]

theorem rawRowCheck14309 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form2 = rawRow14309 := by decide +kernel

def row14309 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck14309 : row14309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14309 := by decide +kernel

theorem rowEval14309 (x : Key → ℝ) : Integer.Sparse.eval row14309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14309, Integer.Sparse.eval_collectBalanced, rawRowCheck14309]

def rawRow14310 : Integer.Sparse Key := [(key2552, -2), (key2536, -2), (key2541, -2), (key2536, 6), (key2500, -2), (key2469, -2), (key2477, -2), (key2434, 2), (key2403, 2), (key2500, 2), (key2375, 2), (key2477, 2), (key2387, 2), (key2403, -2), (key2469, -2), (key2375, -2), (key2465, 6), (key2399, -2), (key2465, -2), (key2371, -2)]

theorem rawRowCheck14310 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form2 = rawRow14310 := by decide +kernel

def row14310 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck14310 : row14310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14310 := by decide +kernel

theorem rowEval14310 (x : Key → ℝ) : Integer.Sparse.eval row14310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14310, Integer.Sparse.eval_collectBalanced, rawRowCheck14310]

def rawRow14311 : Integer.Sparse Key := [(key2541, -2), (key2552, -2), (key2536, -2), (key2536, 6), (key2477, -2), (key2500, -2), (key2469, -2), (key2477, 2), (key2500, 2), (key2387, 2), (key2434, 2), (key2375, 2), (key2403, 2), (key2469, -2), (key2375, -2), (key2403, -2), (key2465, 6), (key2465, -2), (key2371, -2), (key2399, -2)]

theorem rawRowCheck14311 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form2 = rawRow14311 := by decide +kernel

def row14311 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck14311 : row14311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14311 := by decide +kernel

theorem rowEval14311 (x : Key → ℝ) : Integer.Sparse.eval row14311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14311, Integer.Sparse.eval_collectBalanced, rawRowCheck14311]

def rawRow14312 : Integer.Sparse Key := [(key2552, -2), (key2541, -2), (key2536, -2), (key2536, 6), (key2500, -2), (key2477, -2), (key2469, -2), (key2500, 2), (key2477, 2), (key2434, 2), (key2387, 2), (key2403, 2), (key2375, 2), (key2469, -2), (key2403, -2), (key2375, -2), (key2465, 6), (key2465, -2), (key2399, -2), (key2371, -2)]

theorem rawRowCheck14312 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form2 = rawRow14312 := by decide +kernel

def row14312 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck14312 : row14312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14312 := by decide +kernel

theorem rowEval14312 (x : Key → ℝ) : Integer.Sparse.eval row14312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14312, Integer.Sparse.eval_collectBalanced, rawRowCheck14312]

def rawRow14313 : Integer.Sparse Key := [(key2777, 6), (key2662, -2), (key2777, -2), (key2788, -2), (key2800, 6), (key2607, -2), (key2800, -2), (key2823, -2), (key2697, -2), (key2850, -2), (key2854, -2), (key2623, -2), (key2850, -2), (key2864, -2), (key2623, 2), (key2634, 2), (key2697, 2), (key2720, 2), (key2854, 2), (key2864, 2)]

theorem rawRowCheck14313 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form3 = rawRow14313 := by decide +kernel

def row14313 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

theorem rowCheck14313 : row14313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14313 := by decide +kernel

theorem rowEval14313 (x : Key → ℝ) : Integer.Sparse.eval row14313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14313, Integer.Sparse.eval_collectBalanced, rawRowCheck14313]

def rawRow14314 : Integer.Sparse Key := [(key2777, 6), (key2662, -2), (key2788, -2), (key2777, -2), (key2800, 6), (key2607, -2), (key2823, -2), (key2800, -2), (key2697, -2), (key2854, -2), (key2850, -2), (key2623, -2), (key2864, -2), (key2850, -2), (key2634, 2), (key2623, 2), (key2720, 2), (key2697, 2), (key2864, 2), (key2854, 2)]

theorem rawRowCheck14314 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form3 = rawRow14314 := by decide +kernel

def row14314 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

theorem rowCheck14314 : row14314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14314 := by decide +kernel

theorem rowEval14314 (x : Key → ℝ) : Integer.Sparse.eval row14314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14314, Integer.Sparse.eval_collectBalanced, rawRowCheck14314]

def rawRow14315 : Integer.Sparse Key := [(key2777, 6), (key2777, -2), (key2662, -2), (key2788, -2), (key2800, 6), (key2800, -2), (key2607, -2), (key2823, -2), (key2850, -2), (key2697, -2), (key2854, -2), (key2850, -2), (key2623, -2), (key2864, -2), (key2697, 2), (key2854, 2), (key2623, 2), (key2864, 2), (key2634, 2), (key2720, 2)]

theorem rawRowCheck14315 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form3 = rawRow14315 := by decide +kernel

def row14315 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

theorem rowCheck14315 : row14315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14315 := by decide +kernel

theorem rowEval14315 (x : Key → ℝ) : Integer.Sparse.eval row14315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14315, Integer.Sparse.eval_collectBalanced, rawRowCheck14315]

def rawRow14316 : Integer.Sparse Key := [(key2777, 6), (key2777, -2), (key2788, -2), (key2662, -2), (key2800, 6), (key2800, -2), (key2823, -2), (key2607, -2), (key2850, -2), (key2854, -2), (key2697, -2), (key2850, -2), (key2864, -2), (key2623, -2), (key2854, 2), (key2697, 2), (key2864, 2), (key2623, 2), (key2720, 2), (key2634, 2)]

theorem rawRowCheck14316 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form3 = rawRow14316 := by decide +kernel

def row14316 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

theorem rowCheck14316 : row14316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14316 := by decide +kernel

theorem rowEval14316 (x : Key → ℝ) : Integer.Sparse.eval row14316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14316, Integer.Sparse.eval_collectBalanced, rawRowCheck14316]

def rawRow14317 : Integer.Sparse Key := [(key2777, 6), (key2788, -2), (key2662, -2), (key2777, -2), (key2800, 6), (key2823, -2), (key2607, -2), (key2800, -2), (key2854, -2), (key2697, -2), (key2850, -2), (key2864, -2), (key2623, -2), (key2850, -2), (key2720, 2), (key2864, 2), (key2634, 2), (key2854, 2), (key2623, 2), (key2697, 2)]

theorem rawRowCheck14317 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form3 = rawRow14317 := by decide +kernel

def row14317 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

theorem rowCheck14317 : row14317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14317 := by decide +kernel

theorem rowEval14317 (x : Key → ℝ) : Integer.Sparse.eval row14317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14317, Integer.Sparse.eval_collectBalanced, rawRowCheck14317]

def rawRow14318 : Integer.Sparse Key := [(key2777, 6), (key2788, -2), (key2777, -2), (key2662, -2), (key2800, 6), (key2823, -2), (key2800, -2), (key2607, -2), (key2854, -2), (key2850, -2), (key2697, -2), (key2864, -2), (key2850, -2), (key2623, -2), (key2864, 2), (key2720, 2), (key2854, 2), (key2634, 2), (key2697, 2), (key2623, 2)]

theorem rawRowCheck14318 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form3 = rawRow14318 := by decide +kernel

def row14318 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

theorem rowCheck14318 : row14318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14318 := by decide +kernel

theorem rowEval14318 (x : Key → ℝ) : Integer.Sparse.eval row14318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14318, Integer.Sparse.eval_collectBalanced, rawRowCheck14318]

def rawRow14319 : Integer.Sparse Key := [(key2788, 6), (key2662, -2), (key2777, -2), (key2777, -2), (key2823, 6), (key2607, -2), (key2800, -2), (key2800, -2), (key2720, -2), (key2864, -2), (key2864, -2), (key2634, -2), (key2854, -2), (key2854, -2), (key2623, 2), (key2623, 2), (key2697, 2), (key2697, 2), (key2850, 2), (key2850, 2)]

theorem rawRowCheck14319 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form3 = rawRow14319 := by decide +kernel

def row14319 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

theorem rowCheck14319 : row14319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14319 := by decide +kernel

theorem rowEval14319 (x : Key → ℝ) : Integer.Sparse.eval row14319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14319, Integer.Sparse.eval_collectBalanced, rawRowCheck14319]

def rawRow14320 : Integer.Sparse Key := [(key2788, 6), (key2777, -2), (key2662, -2), (key2777, -2), (key2823, 6), (key2800, -2), (key2607, -2), (key2800, -2), (key2864, -2), (key2720, -2), (key2864, -2), (key2854, -2), (key2634, -2), (key2854, -2), (key2697, 2), (key2850, 2), (key2623, 2), (key2850, 2), (key2623, 2), (key2697, 2)]

theorem rawRowCheck14320 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form3 = rawRow14320 := by decide +kernel

def row14320 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

theorem rowCheck14320 : row14320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14320 := by decide +kernel

theorem rowEval14320 (x : Key → ℝ) : Integer.Sparse.eval row14320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14320, Integer.Sparse.eval_collectBalanced, rawRowCheck14320]

def rawRow14321 : Integer.Sparse Key := [(key2788, 6), (key2777, -2), (key2777, -2), (key2662, -2), (key2823, 6), (key2800, -2), (key2800, -2), (key2607, -2), (key2864, -2), (key2864, -2), (key2720, -2), (key2854, -2), (key2854, -2), (key2634, -2), (key2850, 2), (key2697, 2), (key2850, 2), (key2623, 2), (key2697, 2), (key2623, 2)]

theorem rawRowCheck14321 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form3 = rawRow14321 := by decide +kernel

def row14321 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

theorem rowCheck14321 : row14321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14321 := by decide +kernel

theorem rowEval14321 (x : Key → ℝ) : Integer.Sparse.eval row14321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14321, Integer.Sparse.eval_collectBalanced, rawRowCheck14321]

def rawRow14322 : Integer.Sparse Key := [(key2800, 6), (key2697, -2), (key2850, -2), (key2854, -2), (key2777, 6), (key2623, -2), (key2850, -2), (key2864, -2), (key2662, -2), (key2777, -2), (key2788, -2), (key2607, -2), (key2800, -2), (key2823, -2), (key2623, 2), (key2634, 2), (key2697, 2), (key2720, 2), (key2854, 2), (key2864, 2)]

theorem rawRowCheck14322 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form3 = rawRow14322 := by decide +kernel

def row14322 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

theorem rowCheck14322 : row14322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14322 := by decide +kernel

theorem rowEval14322 (x : Key → ℝ) : Integer.Sparse.eval row14322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14322, Integer.Sparse.eval_collectBalanced, rawRowCheck14322]

def rawRow14323 : Integer.Sparse Key := [(key2800, 6), (key2697, -2), (key2854, -2), (key2850, -2), (key2777, 6), (key2623, -2), (key2864, -2), (key2850, -2), (key2662, -2), (key2788, -2), (key2777, -2), (key2607, -2), (key2823, -2), (key2800, -2), (key2634, 2), (key2623, 2), (key2720, 2), (key2697, 2), (key2864, 2), (key2854, 2)]

theorem rawRowCheck14323 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form3 = rawRow14323 := by decide +kernel

def row14323 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

theorem rowCheck14323 : row14323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14323 := by decide +kernel

theorem rowEval14323 (x : Key → ℝ) : Integer.Sparse.eval row14323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14323, Integer.Sparse.eval_collectBalanced, rawRowCheck14323]

def rawRow14324 : Integer.Sparse Key := [(key2800, 6), (key2850, -2), (key2697, -2), (key2854, -2), (key2777, 6), (key2850, -2), (key2623, -2), (key2864, -2), (key2777, -2), (key2662, -2), (key2788, -2), (key2800, -2), (key2607, -2), (key2823, -2), (key2697, 2), (key2854, 2), (key2623, 2), (key2864, 2), (key2634, 2), (key2720, 2)]

theorem rawRowCheck14324 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form3 = rawRow14324 := by decide +kernel

def row14324 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

theorem rowCheck14324 : row14324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14324 := by decide +kernel

theorem rowEval14324 (x : Key → ℝ) : Integer.Sparse.eval row14324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14324, Integer.Sparse.eval_collectBalanced, rawRowCheck14324]

def rawRow14325 : Integer.Sparse Key := [(key2800, 6), (key2850, -2), (key2854, -2), (key2697, -2), (key2777, 6), (key2850, -2), (key2864, -2), (key2623, -2), (key2777, -2), (key2788, -2), (key2662, -2), (key2800, -2), (key2823, -2), (key2607, -2), (key2854, 2), (key2697, 2), (key2864, 2), (key2623, 2), (key2720, 2), (key2634, 2)]

theorem rawRowCheck14325 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form3 = rawRow14325 := by decide +kernel

def row14325 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

theorem rowCheck14325 : row14325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14325 := by decide +kernel

theorem rowEval14325 (x : Key → ℝ) : Integer.Sparse.eval row14325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14325, Integer.Sparse.eval_collectBalanced, rawRowCheck14325]

def rawRow14326 : Integer.Sparse Key := [(key2800, 6), (key2854, -2), (key2697, -2), (key2850, -2), (key2777, 6), (key2864, -2), (key2623, -2), (key2850, -2), (key2788, -2), (key2662, -2), (key2777, -2), (key2823, -2), (key2607, -2), (key2800, -2), (key2720, 2), (key2864, 2), (key2634, 2), (key2854, 2), (key2623, 2), (key2697, 2)]

theorem rawRowCheck14326 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form3 = rawRow14326 := by decide +kernel

def row14326 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

theorem rowCheck14326 : row14326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14326 := by decide +kernel

theorem rowEval14326 (x : Key → ℝ) : Integer.Sparse.eval row14326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14326, Integer.Sparse.eval_collectBalanced, rawRowCheck14326]

def rawRow14327 : Integer.Sparse Key := [(key2800, 6), (key2854, -2), (key2850, -2), (key2697, -2), (key2777, 6), (key2864, -2), (key2850, -2), (key2623, -2), (key2788, -2), (key2777, -2), (key2662, -2), (key2823, -2), (key2800, -2), (key2607, -2), (key2864, 2), (key2720, 2), (key2854, 2), (key2634, 2), (key2697, 2), (key2623, 2)]

theorem rawRowCheck14327 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form3 = rawRow14327 := by decide +kernel

def row14327 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

theorem rowCheck14327 : row14327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14327 := by decide +kernel

theorem rowEval14327 (x : Key → ℝ) : Integer.Sparse.eval row14327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14327, Integer.Sparse.eval_collectBalanced, rawRowCheck14327]

def rawRow14328 : Integer.Sparse Key := [(key2850, 6), (key2697, -2), (key2800, -2), (key2854, -2), (key2850, 6), (key2623, -2), (key2777, -2), (key2864, -2), (key2697, -2), (key2800, -2), (key2854, -2), (key2623, -2), (key2777, -2), (key2864, -2), (key2607, 2), (key2634, 2), (key2662, 2), (key2720, 2), (key2788, 2), (key2823, 2)]

theorem rawRowCheck14328 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form3 = rawRow14328 := by decide +kernel

def row14328 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

theorem rowCheck14328 : row14328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14328 := by decide +kernel

theorem rowEval14328 (x : Key → ℝ) : Integer.Sparse.eval row14328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14328, Integer.Sparse.eval_collectBalanced, rawRowCheck14328]

def rawRow14329 : Integer.Sparse Key := [(key2850, 6), (key2697, -2), (key2854, -2), (key2800, -2), (key2850, 6), (key2623, -2), (key2864, -2), (key2777, -2), (key2697, -2), (key2854, -2), (key2800, -2), (key2623, -2), (key2864, -2), (key2777, -2), (key2634, 2), (key2607, 2), (key2720, 2), (key2662, 2), (key2823, 2), (key2788, 2)]

theorem rawRowCheck14329 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form3 = rawRow14329 := by decide +kernel

def row14329 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

theorem rowCheck14329 : row14329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14329 := by decide +kernel

theorem rowEval14329 (x : Key → ℝ) : Integer.Sparse.eval row14329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14329, Integer.Sparse.eval_collectBalanced, rawRowCheck14329]

def rawRow14330 : Integer.Sparse Key := [(key2850, 6), (key2800, -2), (key2697, -2), (key2854, -2), (key2850, 6), (key2777, -2), (key2623, -2), (key2864, -2), (key2800, -2), (key2697, -2), (key2854, -2), (key2777, -2), (key2623, -2), (key2864, -2), (key2662, 2), (key2788, 2), (key2607, 2), (key2823, 2), (key2634, 2), (key2720, 2)]

theorem rawRowCheck14330 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form3 = rawRow14330 := by decide +kernel

def row14330 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

theorem rowCheck14330 : row14330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14330 := by decide +kernel

theorem rowEval14330 (x : Key → ℝ) : Integer.Sparse.eval row14330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14330, Integer.Sparse.eval_collectBalanced, rawRowCheck14330]

def rawRow14331 : Integer.Sparse Key := [(key2850, 6), (key2800, -2), (key2854, -2), (key2697, -2), (key2850, 6), (key2777, -2), (key2864, -2), (key2623, -2), (key2800, -2), (key2854, -2), (key2697, -2), (key2777, -2), (key2864, -2), (key2623, -2), (key2788, 2), (key2662, 2), (key2823, 2), (key2607, 2), (key2720, 2), (key2634, 2)]

theorem rawRowCheck14331 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form3 = rawRow14331 := by decide +kernel

def row14331 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

theorem rowCheck14331 : row14331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14331 := by decide +kernel

theorem rowEval14331 (x : Key → ℝ) : Integer.Sparse.eval row14331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14331, Integer.Sparse.eval_collectBalanced, rawRowCheck14331]

def rawRow14332 : Integer.Sparse Key := [(key2850, 6), (key2854, -2), (key2697, -2), (key2800, -2), (key2850, 6), (key2864, -2), (key2623, -2), (key2777, -2), (key2854, -2), (key2697, -2), (key2800, -2), (key2864, -2), (key2623, -2), (key2777, -2), (key2720, 2), (key2823, 2), (key2634, 2), (key2788, 2), (key2607, 2), (key2662, 2)]

theorem rawRowCheck14332 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form3 = rawRow14332 := by decide +kernel

def row14332 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

theorem rowCheck14332 : row14332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14332 := by decide +kernel

theorem rowEval14332 (x : Key → ℝ) : Integer.Sparse.eval row14332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14332, Integer.Sparse.eval_collectBalanced, rawRowCheck14332]

def rawRow14333 : Integer.Sparse Key := [(key2850, 6), (key2854, -2), (key2800, -2), (key2697, -2), (key2850, 6), (key2864, -2), (key2777, -2), (key2623, -2), (key2854, -2), (key2800, -2), (key2697, -2), (key2864, -2), (key2777, -2), (key2623, -2), (key2823, 2), (key2720, 2), (key2788, 2), (key2634, 2), (key2662, 2), (key2607, 2)]

theorem rawRowCheck14333 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form3 = rawRow14333 := by decide +kernel

def row14333 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

theorem rowCheck14333 : row14333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14333 := by decide +kernel

theorem rowEval14333 (x : Key → ℝ) : Integer.Sparse.eval row14333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14333, Integer.Sparse.eval_collectBalanced, rawRowCheck14333]

def rawRow14334 : Integer.Sparse Key := [(key2854, 6), (key2697, -2), (key2800, -2), (key2850, -2), (key2864, 6), (key2623, -2), (key2777, -2), (key2850, -2), (key2720, -2), (key2823, -2), (key2864, -2), (key2634, -2), (key2788, -2), (key2854, -2), (key2607, 2), (key2623, 2), (key2662, 2), (key2697, 2), (key2777, 2), (key2800, 2)]

theorem rawRowCheck14334 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form3 = rawRow14334 := by decide +kernel

def row14334 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

theorem rowCheck14334 : row14334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14334 := by decide +kernel

theorem rowEval14334 (x : Key → ℝ) : Integer.Sparse.eval row14334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14334, Integer.Sparse.eval_collectBalanced, rawRowCheck14334]

def rawRow14335 : Integer.Sparse Key := [(key2854, 6), (key2697, -2), (key2850, -2), (key2800, -2), (key2864, 6), (key2623, -2), (key2850, -2), (key2777, -2), (key2720, -2), (key2864, -2), (key2823, -2), (key2634, -2), (key2854, -2), (key2788, -2), (key2623, 2), (key2607, 2), (key2697, 2), (key2662, 2), (key2800, 2), (key2777, 2)]

theorem rawRowCheck14335 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form3 = rawRow14335 := by decide +kernel

def row14335 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

theorem rowCheck14335 : row14335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14335 := by decide +kernel

theorem rowEval14335 (x : Key → ℝ) : Integer.Sparse.eval row14335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14335, Integer.Sparse.eval_collectBalanced, rawRowCheck14335]

end MUB6.Certificate.GramRows

end OAI
