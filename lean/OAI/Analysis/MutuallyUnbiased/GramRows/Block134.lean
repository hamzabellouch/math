import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14080 : Integer.Sparse Key := [(key2490, 4), (key2490, 4), (key2422, 4), (key2486, -4), (key2413, -4), (key2413, -4), (key2490, -4), (key2422, -4), (key2422, -4), (key2413, 12)]

theorem rawRowCheck14080 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form7 = rawRow14080 := by decide +kernel

def row14080 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

theorem rowCheck14080 : row14080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14080 := by decide +kernel

theorem rowEval14080 (x : Key → ℝ) : Integer.Sparse.eval row14080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck14080, Integer.Sparse.eval_collectBalanced, rawRowCheck14080]

def rawRow14081 : Integer.Sparse Key := [(key2422, 4), (key2422, 4), (key2422, 4), (key2490, -4), (key2490, -4), (key2490, -4), (key2413, -4), (key2413, -4), (key2413, -4), (key2486, 12)]

theorem rawRowCheck14081 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form7 = rawRow14081 := by decide +kernel

def row14081 : Integer.Sparse Key := [(key2413, -12), (key2422, 12), (key2486, 12), (key2490, -12)]

theorem rowCheck14081 : row14081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14081 := by decide +kernel

theorem rowEval14081 (x : Key → ℝ) : Integer.Sparse.eval row14081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14081, Integer.Sparse.eval_collectBalanced, rawRowCheck14081]

def rawRow14082 : Integer.Sparse Key := [(key2422, 4), (key2490, 4), (key2490, 4), (key2422, -4), (key2422, -4), (key2490, -4), (key2413, -4), (key2413, -4), (key2486, -4), (key2413, 12)]

theorem rawRowCheck14082 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form7 = rawRow14082 := by decide +kernel

def row14082 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

theorem rowCheck14082 : row14082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14082 := by decide +kernel

theorem rowEval14082 (x : Key → ℝ) : Integer.Sparse.eval row14082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14082, Integer.Sparse.eval_collectBalanced, rawRowCheck14082]

def rawRow14083 : Integer.Sparse Key := [(key2490, 4), (key2422, 4), (key2490, 4), (key2422, -4), (key2490, -4), (key2422, -4), (key2413, -4), (key2486, -4), (key2413, -4), (key2413, 12)]

theorem rawRowCheck14083 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form7 = rawRow14083 := by decide +kernel

def row14083 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

theorem rowCheck14083 : row14083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14083 := by decide +kernel

theorem rowEval14083 (x : Key → ℝ) : Integer.Sparse.eval row14083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14083, Integer.Sparse.eval_collectBalanced, rawRowCheck14083]

def rawRow14084 : Integer.Sparse Key := [(key2490, 4), (key2490, 4), (key2422, 4), (key2490, -4), (key2422, -4), (key2422, -4), (key2486, -4), (key2413, -4), (key2413, -4), (key2413, 12)]

theorem rawRowCheck14084 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form7 = rawRow14084 := by decide +kernel

def row14084 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

theorem rowCheck14084 : row14084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14084 := by decide +kernel

theorem rowEval14084 (x : Key → ℝ) : Integer.Sparse.eval row14084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck14084, Integer.Sparse.eval_collectBalanced, rawRowCheck14084]

def rawRow14085 : Integer.Sparse Key := [(key2353, -2), (key2356, -2), (key2356, -2), (key2356, 6), (key2448, -2), (key2451, -2), (key2451, -2), (key2448, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2513, 2), (key2451, -2), (key2451, -2), (key2513, -2), (key2527, 6), (key2527, -2), (key2527, -2), (key2558, -2)]

theorem rawRowCheck14085 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form8 = rawRow14085 := by decide +kernel

def row14085 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 2), (key2527, 2), (key2558, -2)]

theorem rowCheck14085 : row14085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14085 := by decide +kernel

theorem rowEval14085 (x : Key → ℝ) : Integer.Sparse.eval row14085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14085, Integer.Sparse.eval_collectBalanced, rawRowCheck14085]

def rawRow14086 : Integer.Sparse Key := [(key2356, -2), (key2353, -2), (key2356, -2), (key2356, 6), (key2451, -2), (key2448, -2), (key2451, -2), (key2451, 2), (key2448, 2), (key2513, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2451, -2), (key2513, -2), (key2451, -2), (key2527, 6), (key2527, -2), (key2558, -2), (key2527, -2)]

theorem rawRowCheck14086 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form8 = rawRow14086 := by decide +kernel

def row14086 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 2), (key2527, 2), (key2558, -2)]

theorem rowCheck14086 : row14086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14086 := by decide +kernel

theorem rowEval14086 (x : Key → ℝ) : Integer.Sparse.eval row14086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14086, Integer.Sparse.eval_collectBalanced, rawRowCheck14086]

def rawRow14087 : Integer.Sparse Key := [(key2356, -2), (key2356, -2), (key2353, -2), (key2356, 6), (key2451, -2), (key2451, -2), (key2448, -2), (key2513, 2), (key2513, 2), (key2451, 2), (key2451, 2), (key2448, 2), (key2448, 2), (key2513, -2), (key2451, -2), (key2451, -2), (key2527, 6), (key2558, -2), (key2527, -2), (key2527, -2)]

theorem rawRowCheck14087 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form8 = rawRow14087 := by decide +kernel

def row14087 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 2), (key2527, 2), (key2558, -2)]

theorem rowCheck14087 : row14087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14087 := by decide +kernel

theorem rowEval14087 (x : Key → ℝ) : Integer.Sparse.eval row14087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14087, Integer.Sparse.eval_collectBalanced, rawRowCheck14087]

def rawRow14088 : Integer.Sparse Key := [(key2356, -2), (key2356, -2), (key2356, -2), (key2353, 6), (key2513, -2), (key2513, -2), (key2513, -2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2448, -2), (key2448, -2), (key2448, -2), (key2558, 6), (key2527, -2), (key2527, -2), (key2527, -2)]

theorem rawRowCheck14088 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form8 = rawRow14088 := by decide +kernel

def row14088 : Integer.Sparse Key := [(key2353, 6), (key2356, -6), (key2448, -6), (key2451, 12), (key2513, -6), (key2527, -6), (key2558, 6)]

theorem rowCheck14088 : row14088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14088 := by decide +kernel

theorem rowEval14088 (x : Key → ℝ) : Integer.Sparse.eval row14088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14088, Integer.Sparse.eval_collectBalanced, rawRowCheck14088]

def rawRow14089 : Integer.Sparse Key := [(key2448, -2), (key2451, -2), (key2451, -2), (key2513, 6), (key2353, -2), (key2356, -2), (key2356, -2), (key2448, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2513, 2), (key2527, -2), (key2527, -2), (key2558, -2), (key2356, 6), (key2451, -2), (key2451, -2), (key2513, -2)]

theorem rawRowCheck14089 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form8 = rawRow14089 := by decide +kernel

def row14089 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 8), (key2527, -4), (key2558, -2)]

theorem rowCheck14089 : row14089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14089 := by decide +kernel

theorem rowEval14089 (x : Key → ℝ) : Integer.Sparse.eval row14089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14089, Integer.Sparse.eval_collectBalanced, rawRowCheck14089]

def rawRow14090 : Integer.Sparse Key := [(key2451, -2), (key2448, -2), (key2451, -2), (key2513, 6), (key2356, -2), (key2353, -2), (key2356, -2), (key2451, 2), (key2448, 2), (key2513, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2527, -2), (key2558, -2), (key2527, -2), (key2356, 6), (key2451, -2), (key2513, -2), (key2451, -2)]

theorem rawRowCheck14090 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form8 = rawRow14090 := by decide +kernel

def row14090 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 8), (key2527, -4), (key2558, -2)]

theorem rowCheck14090 : row14090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14090 := by decide +kernel

theorem rowEval14090 (x : Key → ℝ) : Integer.Sparse.eval row14090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14090, Integer.Sparse.eval_collectBalanced, rawRowCheck14090]

def rawRow14091 : Integer.Sparse Key := [(key2451, -2), (key2451, -2), (key2448, -2), (key2513, 6), (key2356, -2), (key2356, -2), (key2353, -2), (key2513, 2), (key2513, 2), (key2451, 2), (key2451, 2), (key2448, 2), (key2448, 2), (key2558, -2), (key2527, -2), (key2527, -2), (key2356, 6), (key2513, -2), (key2451, -2), (key2451, -2)]

theorem rawRowCheck14091 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form8 = rawRow14091 := by decide +kernel

def row14091 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 8), (key2527, -4), (key2558, -2)]

theorem rowCheck14091 : row14091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14091 := by decide +kernel

theorem rowEval14091 (x : Key → ℝ) : Integer.Sparse.eval row14091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14091, Integer.Sparse.eval_collectBalanced, rawRowCheck14091]

def rawRow14092 : Integer.Sparse Key := [(key2448, -2), (key2451, -2), (key2513, -2), (key2451, 6), (key2448, -2), (key2451, -2), (key2513, -2), (key2353, 2), (key2356, 2), (key2448, 2), (key2513, 2), (key2527, 2), (key2558, 2), (key2356, -2), (key2451, -2), (key2513, -2), (key2451, 6), (key2356, -2), (key2451, -2), (key2513, -2)]

theorem rawRowCheck14092 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form8 = rawRow14092 := by decide +kernel

def row14092 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2451, 4), (key2513, -6), (key2527, 2), (key2558, 2)]

theorem rowCheck14092 : row14092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14092 := by decide +kernel

theorem rowEval14092 (x : Key → ℝ) : Integer.Sparse.eval row14092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14092, Integer.Sparse.eval_collectBalanced, rawRowCheck14092]

def rawRow14093 : Integer.Sparse Key := [(key2451, -2), (key2448, -2), (key2513, -2), (key2451, 6), (key2451, -2), (key2448, -2), (key2513, -2), (key2356, 2), (key2353, 2), (key2513, 2), (key2448, 2), (key2558, 2), (key2527, 2), (key2356, -2), (key2513, -2), (key2451, -2), (key2451, 6), (key2356, -2), (key2513, -2), (key2451, -2)]

theorem rawRowCheck14093 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form8 = rawRow14093 := by decide +kernel

def row14093 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2451, 4), (key2513, -6), (key2527, 2), (key2558, 2)]

theorem rowCheck14093 : row14093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14093 := by decide +kernel

theorem rowEval14093 (x : Key → ℝ) : Integer.Sparse.eval row14093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14093, Integer.Sparse.eval_collectBalanced, rawRowCheck14093]

def rawRow14094 : Integer.Sparse Key := [(key2448, -2), (key2513, -2), (key2451, -2), (key2451, 6), (key2448, -2), (key2513, -2), (key2451, -2), (key2448, 2), (key2513, 2), (key2353, 2), (key2558, 2), (key2356, 2), (key2513, 2), (key2451, -2), (key2356, -2), (key2513, -2), (key2451, 6), (key2451, -2), (key2356, -2), (key2513, -2)]

theorem rawRowCheck14094 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form8 = rawRow14094 := by decide +kernel

def row14094 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2451, 4), (key2513, -4), (key2558, 2)]

theorem rowCheck14094 : row14094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14094 := by decide +kernel

theorem rowEval14094 (x : Key → ℝ) : Integer.Sparse.eval row14094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14094, Integer.Sparse.eval_collectBalanced, rawRowCheck14094]

def rawRow14095 : Integer.Sparse Key := [(key2513, -2), (key2448, -2), (key2451, -2), (key2451, 6), (key2513, -2), (key2448, -2), (key2451, -2), (key2513, 2), (key2448, 2), (key2558, 2), (key2353, 2), (key2513, 2), (key2356, 2), (key2451, -2), (key2513, -2), (key2356, -2), (key2451, 6), (key2451, -2), (key2513, -2), (key2356, -2)]

theorem rawRowCheck14095 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form8 = rawRow14095 := by decide +kernel

def row14095 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2451, 4), (key2513, -4), (key2558, 2)]

theorem rowCheck14095 : row14095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14095 := by decide +kernel

theorem rowEval14095 (x : Key → ℝ) : Integer.Sparse.eval row14095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form8) x := by
  rw [rowCheck14095, Integer.Sparse.eval_collectBalanced, rawRowCheck14095]

def rawRow14096 : Integer.Sparse Key := [(key2451, -2), (key2513, -2), (key2448, -2), (key2451, 6), (key2451, -2), (key2513, -2), (key2448, -2), (key2527, 2), (key2558, 2), (key2356, 2), (key2513, 2), (key2353, 2), (key2448, 2), (key2513, -2), (key2356, -2), (key2451, -2), (key2451, 6), (key2513, -2), (key2356, -2), (key2451, -2)]

theorem rawRowCheck14096 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form8 = rawRow14096 := by decide +kernel

def row14096 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2451, 4), (key2513, -6), (key2527, 2), (key2558, 2)]

theorem rowCheck14096 : row14096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14096 := by decide +kernel

theorem rowEval14096 (x : Key → ℝ) : Integer.Sparse.eval row14096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14096, Integer.Sparse.eval_collectBalanced, rawRowCheck14096]

def rawRow14097 : Integer.Sparse Key := [(key2513, -2), (key2451, -2), (key2448, -2), (key2451, 6), (key2513, -2), (key2451, -2), (key2448, -2), (key2558, 2), (key2527, 2), (key2513, 2), (key2356, 2), (key2448, 2), (key2353, 2), (key2513, -2), (key2451, -2), (key2356, -2), (key2451, 6), (key2513, -2), (key2451, -2), (key2356, -2)]

theorem rawRowCheck14097 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form8 = rawRow14097 := by decide +kernel

def row14097 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2451, 4), (key2513, -6), (key2527, 2), (key2558, 2)]

theorem rowCheck14097 : row14097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14097 := by decide +kernel

theorem rowEval14097 (x : Key → ℝ) : Integer.Sparse.eval row14097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form8) x := by
  rw [rowCheck14097, Integer.Sparse.eval_collectBalanced, rawRowCheck14097]

def rawRow14098 : Integer.Sparse Key := [(key2451, -2), (key2451, -2), (key2513, -2), (key2448, 6), (key2527, -2), (key2527, -2), (key2558, -2), (key2356, 2), (key2356, 2), (key2451, 2), (key2451, 2), (key2513, 2), (key2513, 2), (key2353, -2), (key2448, -2), (key2448, -2), (key2513, 6), (key2356, -2), (key2451, -2), (key2451, -2)]

theorem rawRowCheck14098 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form8 = rawRow14098 := by decide +kernel

def row14098 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 8), (key2527, -4), (key2558, -2)]

theorem rowCheck14098 : row14098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14098 := by decide +kernel

theorem rowEval14098 (x : Key → ℝ) : Integer.Sparse.eval row14098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14098, Integer.Sparse.eval_collectBalanced, rawRowCheck14098]

def rawRow14099 : Integer.Sparse Key := [(key2451, -2), (key2513, -2), (key2451, -2), (key2448, 6), (key2527, -2), (key2558, -2), (key2527, -2), (key2451, 2), (key2513, 2), (key2356, 2), (key2513, 2), (key2356, 2), (key2451, 2), (key2448, -2), (key2353, -2), (key2448, -2), (key2513, 6), (key2451, -2), (key2356, -2), (key2451, -2)]

theorem rawRowCheck14099 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form8 = rawRow14099 := by decide +kernel

def row14099 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 8), (key2527, -4), (key2558, -2)]

theorem rowCheck14099 : row14099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14099 := by decide +kernel

theorem rowEval14099 (x : Key → ℝ) : Integer.Sparse.eval row14099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14099, Integer.Sparse.eval_collectBalanced, rawRowCheck14099]

def rawRow14100 : Integer.Sparse Key := [(key2513, -2), (key2451, -2), (key2451, -2), (key2448, 6), (key2558, -2), (key2527, -2), (key2527, -2), (key2513, 2), (key2451, 2), (key2513, 2), (key2356, 2), (key2451, 2), (key2356, 2), (key2448, -2), (key2448, -2), (key2353, -2), (key2513, 6), (key2451, -2), (key2451, -2), (key2356, -2)]

theorem rawRowCheck14100 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form8 = rawRow14100 := by decide +kernel

def row14100 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 8), (key2527, -4), (key2558, -2)]

theorem rowCheck14100 : row14100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14100 := by decide +kernel

theorem rowEval14100 (x : Key → ℝ) : Integer.Sparse.eval row14100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form8) x := by
  rw [rowCheck14100, Integer.Sparse.eval_collectBalanced, rawRowCheck14100]

def rawRow14101 : Integer.Sparse Key := [(key2527, -2), (key2527, -2), (key2527, -2), (key2558, 6), (key2356, -2), (key2356, -2), (key2356, -2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2513, -2), (key2513, -2), (key2513, -2), (key2353, 6), (key2448, -2), (key2448, -2), (key2448, -2)]

theorem rawRowCheck14101 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form8 = rawRow14101 := by decide +kernel

def row14101 : Integer.Sparse Key := [(key2353, 6), (key2356, -6), (key2448, -6), (key2451, 12), (key2513, -6), (key2527, -6), (key2558, 6)]

theorem rowCheck14101 : row14101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14101 := by decide +kernel

theorem rowEval14101 (x : Key → ℝ) : Integer.Sparse.eval row14101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14101, Integer.Sparse.eval_collectBalanced, rawRowCheck14101]

def rawRow14102 : Integer.Sparse Key := [(key2527, -2), (key2527, -2), (key2558, -2), (key2527, 6), (key2451, -2), (key2451, -2), (key2513, -2), (key2356, 2), (key2356, 2), (key2451, 2), (key2451, 2), (key2513, 2), (key2513, 2), (key2356, -2), (key2451, -2), (key2451, -2), (key2448, 6), (key2353, -2), (key2448, -2), (key2448, -2)]

theorem rawRowCheck14102 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form8 = rawRow14102 := by decide +kernel

def row14102 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 2), (key2527, 2), (key2558, -2)]

theorem rowCheck14102 : row14102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14102 := by decide +kernel

theorem rowEval14102 (x : Key → ℝ) : Integer.Sparse.eval row14102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14102, Integer.Sparse.eval_collectBalanced, rawRowCheck14102]

def rawRow14103 : Integer.Sparse Key := [(key2527, -2), (key2558, -2), (key2527, -2), (key2527, 6), (key2451, -2), (key2513, -2), (key2451, -2), (key2451, 2), (key2513, 2), (key2356, 2), (key2513, 2), (key2356, 2), (key2451, 2), (key2451, -2), (key2356, -2), (key2451, -2), (key2448, 6), (key2448, -2), (key2353, -2), (key2448, -2)]

theorem rawRowCheck14103 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form8 = rawRow14103 := by decide +kernel

def row14103 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 2), (key2527, 2), (key2558, -2)]

theorem rowCheck14103 : row14103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14103 := by decide +kernel

theorem rowEval14103 (x : Key → ℝ) : Integer.Sparse.eval row14103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14103, Integer.Sparse.eval_collectBalanced, rawRowCheck14103]

def rawRow14104 : Integer.Sparse Key := [(key2558, -2), (key2527, -2), (key2527, -2), (key2527, 6), (key2513, -2), (key2451, -2), (key2451, -2), (key2513, 2), (key2451, 2), (key2513, 2), (key2356, 2), (key2451, 2), (key2356, 2), (key2451, -2), (key2451, -2), (key2356, -2), (key2448, 6), (key2448, -2), (key2448, -2), (key2353, -2)]

theorem rawRowCheck14104 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form8 = rawRow14104 := by decide +kernel

def row14104 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 2), (key2527, 2), (key2558, -2)]

theorem rowCheck14104 : row14104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14104 := by decide +kernel

theorem rowEval14104 (x : Key → ℝ) : Integer.Sparse.eval row14104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form8) x := by
  rw [rowCheck14104, Integer.Sparse.eval_collectBalanced, rawRowCheck14104]

def rawRow14105 : Integer.Sparse Key := [(key1975, 4), (key2217, 4), (key2217, 4), (key1980, -2), (key1980, -2), (key2217, -2), (key2217, -2), (key2261, -2), (key2261, -2), (key1980, -2), (key1980, -2), (key2217, -2), (key2217, -2), (key2261, -2), (key2261, -2), (key1996, 4), (key2261, 4), (key2261, 4)]

theorem rawRowCheck14105 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form0 = rawRow14105 := by decide +kernel

def row14105 : Integer.Sparse Key := [(key1975, 4), (key1980, -8), (key1996, 4)]

theorem rowCheck14105 : row14105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14105 := by decide +kernel

theorem rowEval14105 (x : Key → ℝ) : Integer.Sparse.eval row14105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14105, Integer.Sparse.eval_collectBalanced, rawRowCheck14105]

def rawRow14106 : Integer.Sparse Key := [(key2217, 4), (key1975, 4), (key2217, 4), (key2217, -2), (key2261, -2), (key1980, -2), (key2261, -2), (key1980, -2), (key2217, -2), (key2217, -2), (key2261, -2), (key1980, -2), (key2261, -2), (key1980, -2), (key2217, -2), (key2261, 4), (key1996, 4), (key2261, 4)]

theorem rawRowCheck14106 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form0 = rawRow14106 := by decide +kernel

def row14106 : Integer.Sparse Key := [(key1975, 4), (key1980, -8), (key1996, 4)]

theorem rowCheck14106 : row14106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14106 := by decide +kernel

theorem rowEval14106 (x : Key → ℝ) : Integer.Sparse.eval row14106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14106, Integer.Sparse.eval_collectBalanced, rawRowCheck14106]

def rawRow14107 : Integer.Sparse Key := [(key2217, 4), (key2217, 4), (key1975, 4), (key2261, -2), (key2217, -2), (key2261, -2), (key1980, -2), (key2217, -2), (key1980, -2), (key2261, -2), (key2217, -2), (key2261, -2), (key1980, -2), (key2217, -2), (key1980, -2), (key2261, 4), (key2261, 4), (key1996, 4)]

theorem rawRowCheck14107 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form0 = rawRow14107 := by decide +kernel

def row14107 : Integer.Sparse Key := [(key1975, 4), (key1980, -8), (key1996, 4)]

theorem rowCheck14107 : row14107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14107 := by decide +kernel

theorem rowEval14107 (x : Key → ℝ) : Integer.Sparse.eval row14107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14107, Integer.Sparse.eval_collectBalanced, rawRowCheck14107]

def rawRow14108 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key2261, 4), (key1975, -2), (key1980, -2), (key1975, -2), (key2217, -2), (key1980, -2), (key2217, -2), (key1980, -2), (key1996, -2), (key1980, -2), (key2261, -2), (key1996, -2), (key2261, -2), (key1980, 4), (key1980, 4), (key2217, 4)]

theorem rawRowCheck14108 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form0 = rawRow14108 := by decide +kernel

def row14108 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck14108 : row14108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14108 := by decide +kernel

theorem rowEval14108 (x : Key → ℝ) : Integer.Sparse.eval row14108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14108, Integer.Sparse.eval_collectBalanced, rawRowCheck14108]

def rawRow14109 : Integer.Sparse Key := [(key1980, 4), (key2261, 4), (key1980, 4), (key1980, -2), (key1975, -2), (key2217, -2), (key1975, -2), (key2217, -2), (key1980, -2), (key1996, -2), (key1980, -2), (key2261, -2), (key1980, -2), (key2261, -2), (key1996, -2), (key1980, 4), (key2217, 4), (key1980, 4)]

theorem rawRowCheck14109 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form0 = rawRow14109 := by decide +kernel

def row14109 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck14109 : row14109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14109 := by decide +kernel

theorem rowEval14109 (x : Key → ℝ) : Integer.Sparse.eval row14109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14109, Integer.Sparse.eval_collectBalanced, rawRowCheck14109]

def rawRow14110 : Integer.Sparse Key := [(key2261, 4), (key1980, 4), (key1980, 4), (key2217, -2), (key2217, -2), (key1980, -2), (key1980, -2), (key1975, -2), (key1975, -2), (key2261, -2), (key2261, -2), (key1996, -2), (key1996, -2), (key1980, -2), (key1980, -2), (key2217, 4), (key1980, 4), (key1980, 4)]

theorem rawRowCheck14110 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form0 = rawRow14110 := by decide +kernel

def row14110 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck14110 : row14110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14110 := by decide +kernel

theorem rowEval14110 (x : Key → ℝ) : Integer.Sparse.eval row14110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14110, Integer.Sparse.eval_collectBalanced, rawRowCheck14110]

def rawRow14111 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key2261, 4), (key1980, -2), (key1996, -2), (key1980, -2), (key2261, -2), (key1996, -2), (key2261, -2), (key1975, -2), (key1980, -2), (key1975, -2), (key2217, -2), (key1980, -2), (key2217, -2), (key1980, 4), (key1980, 4), (key2217, 4)]

theorem rawRowCheck14111 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form0 = rawRow14111 := by decide +kernel

def row14111 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck14111 : row14111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14111 := by decide +kernel

theorem rowEval14111 (x : Key → ℝ) : Integer.Sparse.eval row14111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14111, Integer.Sparse.eval_collectBalanced, rawRowCheck14111]

def rawRow14112 : Integer.Sparse Key := [(key1980, 4), (key2261, 4), (key1980, 4), (key1996, -2), (key1980, -2), (key2261, -2), (key1980, -2), (key2261, -2), (key1996, -2), (key1980, -2), (key1975, -2), (key2217, -2), (key1975, -2), (key2217, -2), (key1980, -2), (key1980, 4), (key2217, 4), (key1980, 4)]

theorem rawRowCheck14112 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form0 = rawRow14112 := by decide +kernel

def row14112 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck14112 : row14112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14112 := by decide +kernel

theorem rowEval14112 (x : Key → ℝ) : Integer.Sparse.eval row14112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14112, Integer.Sparse.eval_collectBalanced, rawRowCheck14112]

def rawRow14113 : Integer.Sparse Key := [(key2261, 4), (key1980, 4), (key1980, 4), (key2261, -2), (key2261, -2), (key1996, -2), (key1996, -2), (key1980, -2), (key1980, -2), (key2217, -2), (key2217, -2), (key1980, -2), (key1980, -2), (key1975, -2), (key1975, -2), (key2217, 4), (key1980, 4), (key1980, 4)]

theorem rawRowCheck14113 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form0 = rawRow14113 := by decide +kernel

def row14113 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck14113 : row14113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14113 := by decide +kernel

theorem rowEval14113 (x : Key → ℝ) : Integer.Sparse.eval row14113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14113, Integer.Sparse.eval_collectBalanced, rawRowCheck14113]

def rawRow14114 : Integer.Sparse Key := [(key1996, 4), (key1996, 4), (key1996, 4), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1975, 4), (key1975, 4), (key1975, 4)]

theorem rawRowCheck14114 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form0 = rawRow14114 := by decide +kernel

def row14114 : Integer.Sparse Key := [(key1975, 12), (key1980, -24), (key1996, 12)]

theorem rowCheck14114 : row14114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14114 := by decide +kernel

theorem rowEval14114 (x : Key → ℝ) : Integer.Sparse.eval row14114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14114, Integer.Sparse.eval_collectBalanced, rawRowCheck14114]

def rawRow14115 : Integer.Sparse Key := [(key55, -2), (key55, -2), (key61, -2), (key61, 6), (key55, -2), (key55, -2), (key61, -2), (key55, 2), (key55, 2), (key123, 2), (key123, 2), (key126, 2), (key126, 2), (key61, -2), (key126, -2), (key126, -2), (key61, 6), (key61, -2), (key126, -2), (key126, -2)]

theorem rawRowCheck14115 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form1 = rawRow14115 := by decide +kernel

def row14115 : Integer.Sparse Key := [(key55, -4), (key61, 4), (key123, 4), (key126, -4)]

theorem rowCheck14115 : row14115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14115 := by decide +kernel

theorem rowEval14115 (x : Key → ℝ) : Integer.Sparse.eval row14115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14115, Integer.Sparse.eval_collectBalanced, rawRowCheck14115]

def rawRow14116 : Integer.Sparse Key := [(key55, -2), (key61, -2), (key55, -2), (key61, 6), (key55, -2), (key61, -2), (key55, -2), (key123, 2), (key126, 2), (key55, 2), (key126, 2), (key55, 2), (key123, 2), (key126, -2), (key61, -2), (key126, -2), (key61, 6), (key126, -2), (key61, -2), (key126, -2)]

theorem rawRowCheck14116 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form1 = rawRow14116 := by decide +kernel

def row14116 : Integer.Sparse Key := [(key55, -4), (key61, 4), (key123, 4), (key126, -4)]

theorem rowCheck14116 : row14116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14116 := by decide +kernel

theorem rowEval14116 (x : Key → ℝ) : Integer.Sparse.eval row14116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14116, Integer.Sparse.eval_collectBalanced, rawRowCheck14116]

def rawRow14117 : Integer.Sparse Key := [(key61, -2), (key55, -2), (key55, -2), (key61, 6), (key61, -2), (key55, -2), (key55, -2), (key126, 2), (key123, 2), (key126, 2), (key55, 2), (key123, 2), (key55, 2), (key126, -2), (key126, -2), (key61, -2), (key61, 6), (key126, -2), (key126, -2), (key61, -2)]

theorem rawRowCheck14117 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form1 = rawRow14117 := by decide +kernel

def row14117 : Integer.Sparse Key := [(key55, -4), (key61, 4), (key123, 4), (key126, -4)]

theorem rowCheck14117 : row14117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14117 := by decide +kernel

theorem rowEval14117 (x : Key → ℝ) : Integer.Sparse.eval row14117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14117, Integer.Sparse.eval_collectBalanced, rawRowCheck14117]

def rawRow14118 : Integer.Sparse Key := [(key55, -2), (key61, -2), (key61, -2), (key55, 6), (key123, -2), (key126, -2), (key126, -2), (key55, 2), (key61, 2), (key55, 2), (key126, 2), (key61, 2), (key126, 2), (key55, -2), (key55, -2), (key123, -2), (key126, 6), (key61, -2), (key61, -2), (key126, -2)]

theorem rawRowCheck14118 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form1 = rawRow14118 := by decide +kernel

def row14118 : Integer.Sparse Key := [(key55, 4), (key61, -4), (key123, -4), (key126, 4)]

theorem rowCheck14118 : row14118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14118 := by decide +kernel

theorem rowEval14118 (x : Key → ℝ) : Integer.Sparse.eval row14118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14118, Integer.Sparse.eval_collectBalanced, rawRowCheck14118]

def rawRow14119 : Integer.Sparse Key := [(key61, -2), (key55, -2), (key61, -2), (key55, 6), (key126, -2), (key123, -2), (key126, -2), (key61, 2), (key55, 2), (key126, 2), (key55, 2), (key126, 2), (key61, 2), (key55, -2), (key123, -2), (key55, -2), (key126, 6), (key61, -2), (key126, -2), (key61, -2)]

theorem rawRowCheck14119 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form1 = rawRow14119 := by decide +kernel

def row14119 : Integer.Sparse Key := [(key55, 4), (key61, -4), (key123, -4), (key126, 4)]

theorem rowCheck14119 : row14119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14119 := by decide +kernel

theorem rowEval14119 (x : Key → ℝ) : Integer.Sparse.eval row14119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14119, Integer.Sparse.eval_collectBalanced, rawRowCheck14119]

def rawRow14120 : Integer.Sparse Key := [(key61, -2), (key61, -2), (key55, -2), (key55, 6), (key126, -2), (key126, -2), (key123, -2), (key126, 2), (key126, 2), (key61, 2), (key61, 2), (key55, 2), (key55, 2), (key123, -2), (key55, -2), (key55, -2), (key126, 6), (key126, -2), (key61, -2), (key61, -2)]

theorem rawRowCheck14120 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form1 = rawRow14120 := by decide +kernel

def row14120 : Integer.Sparse Key := [(key55, 4), (key61, -4), (key123, -4), (key126, 4)]

theorem rowCheck14120 : row14120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14120 := by decide +kernel

theorem rowEval14120 (x : Key → ℝ) : Integer.Sparse.eval row14120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14120, Integer.Sparse.eval_collectBalanced, rawRowCheck14120]

def rawRow14121 : Integer.Sparse Key := [(key123, -2), (key126, -2), (key126, -2), (key126, 6), (key55, -2), (key61, -2), (key61, -2), (key55, 2), (key61, 2), (key55, 2), (key126, 2), (key61, 2), (key126, 2), (key61, -2), (key61, -2), (key126, -2), (key55, 6), (key55, -2), (key55, -2), (key123, -2)]

theorem rawRowCheck14121 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form1 = rawRow14121 := by decide +kernel

def row14121 : Integer.Sparse Key := [(key55, 4), (key61, -4), (key123, -4), (key126, 4)]

theorem rowCheck14121 : row14121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14121 := by decide +kernel

theorem rowEval14121 (x : Key → ℝ) : Integer.Sparse.eval row14121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14121, Integer.Sparse.eval_collectBalanced, rawRowCheck14121]

def rawRow14122 : Integer.Sparse Key := [(key126, -2), (key123, -2), (key126, -2), (key126, 6), (key61, -2), (key55, -2), (key61, -2), (key61, 2), (key55, 2), (key126, 2), (key55, 2), (key126, 2), (key61, 2), (key61, -2), (key126, -2), (key61, -2), (key55, 6), (key55, -2), (key123, -2), (key55, -2)]

theorem rawRowCheck14122 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form1 = rawRow14122 := by decide +kernel

def row14122 : Integer.Sparse Key := [(key55, 4), (key61, -4), (key123, -4), (key126, 4)]

theorem rowCheck14122 : row14122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14122 := by decide +kernel

theorem rowEval14122 (x : Key → ℝ) : Integer.Sparse.eval row14122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14122, Integer.Sparse.eval_collectBalanced, rawRowCheck14122]

def rawRow14123 : Integer.Sparse Key := [(key126, -2), (key126, -2), (key123, -2), (key126, 6), (key61, -2), (key61, -2), (key55, -2), (key126, 2), (key126, 2), (key61, 2), (key61, 2), (key55, 2), (key55, 2), (key126, -2), (key61, -2), (key61, -2), (key55, 6), (key123, -2), (key55, -2), (key55, -2)]

theorem rawRowCheck14123 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form1 = rawRow14123 := by decide +kernel

def row14123 : Integer.Sparse Key := [(key55, 4), (key61, -4), (key123, -4), (key126, 4)]

theorem rowCheck14123 : row14123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14123 := by decide +kernel

theorem rowEval14123 (x : Key → ℝ) : Integer.Sparse.eval row14123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14123, Integer.Sparse.eval_collectBalanced, rawRowCheck14123]

def rawRow14124 : Integer.Sparse Key := [(key126, -2), (key126, -2), (key126, -2), (key123, 6), (key126, -2), (key126, -2), (key126, -2), (key61, 2), (key61, 2), (key61, 2), (key61, 2), (key61, 2), (key61, 2), (key55, -2), (key55, -2), (key55, -2), (key123, 6), (key55, -2), (key55, -2), (key55, -2)]

theorem rawRowCheck14124 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form1 = rawRow14124 := by decide +kernel

def row14124 : Integer.Sparse Key := [(key55, -12), (key61, 12), (key123, 12), (key126, -12)]

theorem rowCheck14124 : row14124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14124 := by decide +kernel

theorem rowEval14124 (x : Key → ℝ) : Integer.Sparse.eval row14124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14124, Integer.Sparse.eval_collectBalanced, rawRowCheck14124]

def rawRow14125 : Integer.Sparse Key := [(key1972, -2), (key1972, -2), (key1984, -2), (key1984, 6), (key1972, -2), (key1972, -2), (key1984, -2), (key1972, 2), (key1972, 2), (key2208, 2), (key2208, 2), (key2225, 2), (key2225, 2), (key1984, -2), (key2225, -2), (key2225, -2), (key1984, 6), (key1984, -2), (key2225, -2), (key2225, -2)]

theorem rawRowCheck14125 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form2 = rawRow14125 := by decide +kernel

def row14125 : Integer.Sparse Key := [(key1972, -4), (key1984, 4), (key2208, 4), (key2225, -4)]

theorem rowCheck14125 : row14125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14125 := by decide +kernel

theorem rowEval14125 (x : Key → ℝ) : Integer.Sparse.eval row14125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14125, Integer.Sparse.eval_collectBalanced, rawRowCheck14125]

def rawRow14126 : Integer.Sparse Key := [(key1972, -2), (key1984, -2), (key1972, -2), (key1984, 6), (key1972, -2), (key1984, -2), (key1972, -2), (key2208, 2), (key2225, 2), (key1972, 2), (key2225, 2), (key1972, 2), (key2208, 2), (key2225, -2), (key1984, -2), (key2225, -2), (key1984, 6), (key2225, -2), (key1984, -2), (key2225, -2)]

theorem rawRowCheck14126 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form2 = rawRow14126 := by decide +kernel

def row14126 : Integer.Sparse Key := [(key1972, -4), (key1984, 4), (key2208, 4), (key2225, -4)]

theorem rowCheck14126 : row14126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14126 := by decide +kernel

theorem rowEval14126 (x : Key → ℝ) : Integer.Sparse.eval row14126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14126, Integer.Sparse.eval_collectBalanced, rawRowCheck14126]

def rawRow14127 : Integer.Sparse Key := [(key1984, -2), (key1972, -2), (key1972, -2), (key1984, 6), (key1984, -2), (key1972, -2), (key1972, -2), (key2225, 2), (key2208, 2), (key2225, 2), (key1972, 2), (key2208, 2), (key1972, 2), (key2225, -2), (key2225, -2), (key1984, -2), (key1984, 6), (key2225, -2), (key2225, -2), (key1984, -2)]

theorem rawRowCheck14127 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form2 = rawRow14127 := by decide +kernel

def row14127 : Integer.Sparse Key := [(key1972, -4), (key1984, 4), (key2208, 4), (key2225, -4)]

theorem rowCheck14127 : row14127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14127 := by decide +kernel

theorem rowEval14127 (x : Key → ℝ) : Integer.Sparse.eval row14127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14127, Integer.Sparse.eval_collectBalanced, rawRowCheck14127]

def rawRow14128 : Integer.Sparse Key := [(key1972, -2), (key1984, -2), (key1984, -2), (key1972, 6), (key2208, -2), (key2225, -2), (key2225, -2), (key1972, 2), (key1984, 2), (key1972, 2), (key2225, 2), (key1984, 2), (key2225, 2), (key1972, -2), (key1972, -2), (key2208, -2), (key2225, 6), (key1984, -2), (key1984, -2), (key2225, -2)]

theorem rawRowCheck14128 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form2 = rawRow14128 := by decide +kernel

def row14128 : Integer.Sparse Key := [(key1972, 4), (key1984, -4), (key2208, -4), (key2225, 4)]

theorem rowCheck14128 : row14128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14128 := by decide +kernel

theorem rowEval14128 (x : Key → ℝ) : Integer.Sparse.eval row14128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14128, Integer.Sparse.eval_collectBalanced, rawRowCheck14128]

def rawRow14129 : Integer.Sparse Key := [(key1984, -2), (key1972, -2), (key1984, -2), (key1972, 6), (key2225, -2), (key2208, -2), (key2225, -2), (key1984, 2), (key1972, 2), (key2225, 2), (key1972, 2), (key2225, 2), (key1984, 2), (key1972, -2), (key2208, -2), (key1972, -2), (key2225, 6), (key1984, -2), (key2225, -2), (key1984, -2)]

theorem rawRowCheck14129 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form2 = rawRow14129 := by decide +kernel

def row14129 : Integer.Sparse Key := [(key1972, 4), (key1984, -4), (key2208, -4), (key2225, 4)]

theorem rowCheck14129 : row14129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14129 := by decide +kernel

theorem rowEval14129 (x : Key → ℝ) : Integer.Sparse.eval row14129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14129, Integer.Sparse.eval_collectBalanced, rawRowCheck14129]

def rawRow14130 : Integer.Sparse Key := [(key1984, -2), (key1984, -2), (key1972, -2), (key1972, 6), (key2225, -2), (key2225, -2), (key2208, -2), (key2225, 2), (key2225, 2), (key1984, 2), (key1984, 2), (key1972, 2), (key1972, 2), (key2208, -2), (key1972, -2), (key1972, -2), (key2225, 6), (key2225, -2), (key1984, -2), (key1984, -2)]

theorem rawRowCheck14130 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form2 = rawRow14130 := by decide +kernel

def row14130 : Integer.Sparse Key := [(key1972, 4), (key1984, -4), (key2208, -4), (key2225, 4)]

theorem rowCheck14130 : row14130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14130 := by decide +kernel

theorem rowEval14130 (x : Key → ℝ) : Integer.Sparse.eval row14130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14130, Integer.Sparse.eval_collectBalanced, rawRowCheck14130]

def rawRow14131 : Integer.Sparse Key := [(key2208, -2), (key2225, -2), (key2225, -2), (key2225, 6), (key1972, -2), (key1984, -2), (key1984, -2), (key1972, 2), (key1984, 2), (key1972, 2), (key2225, 2), (key1984, 2), (key2225, 2), (key1984, -2), (key1984, -2), (key2225, -2), (key1972, 6), (key1972, -2), (key1972, -2), (key2208, -2)]

theorem rawRowCheck14131 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form2 = rawRow14131 := by decide +kernel

def row14131 : Integer.Sparse Key := [(key1972, 4), (key1984, -4), (key2208, -4), (key2225, 4)]

theorem rowCheck14131 : row14131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14131 := by decide +kernel

theorem rowEval14131 (x : Key → ℝ) : Integer.Sparse.eval row14131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14131, Integer.Sparse.eval_collectBalanced, rawRowCheck14131]

def rawRow14132 : Integer.Sparse Key := [(key2225, -2), (key2208, -2), (key2225, -2), (key2225, 6), (key1984, -2), (key1972, -2), (key1984, -2), (key1984, 2), (key1972, 2), (key2225, 2), (key1972, 2), (key2225, 2), (key1984, 2), (key1984, -2), (key2225, -2), (key1984, -2), (key1972, 6), (key1972, -2), (key2208, -2), (key1972, -2)]

theorem rawRowCheck14132 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form2 = rawRow14132 := by decide +kernel

def row14132 : Integer.Sparse Key := [(key1972, 4), (key1984, -4), (key2208, -4), (key2225, 4)]

theorem rowCheck14132 : row14132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14132 := by decide +kernel

theorem rowEval14132 (x : Key → ℝ) : Integer.Sparse.eval row14132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14132, Integer.Sparse.eval_collectBalanced, rawRowCheck14132]

def rawRow14133 : Integer.Sparse Key := [(key2225, -2), (key2225, -2), (key2208, -2), (key2225, 6), (key1984, -2), (key1984, -2), (key1972, -2), (key2225, 2), (key2225, 2), (key1984, 2), (key1984, 2), (key1972, 2), (key1972, 2), (key2225, -2), (key1984, -2), (key1984, -2), (key1972, 6), (key2208, -2), (key1972, -2), (key1972, -2)]

theorem rawRowCheck14133 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form2 = rawRow14133 := by decide +kernel

def row14133 : Integer.Sparse Key := [(key1972, 4), (key1984, -4), (key2208, -4), (key2225, 4)]

theorem rowCheck14133 : row14133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14133 := by decide +kernel

theorem rowEval14133 (x : Key → ℝ) : Integer.Sparse.eval row14133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14133, Integer.Sparse.eval_collectBalanced, rawRowCheck14133]

def rawRow14134 : Integer.Sparse Key := [(key2225, -2), (key2225, -2), (key2225, -2), (key2208, 6), (key2225, -2), (key2225, -2), (key2225, -2), (key1984, 2), (key1984, 2), (key1984, 2), (key1984, 2), (key1984, 2), (key1984, 2), (key1972, -2), (key1972, -2), (key1972, -2), (key2208, 6), (key1972, -2), (key1972, -2), (key1972, -2)]

theorem rawRowCheck14134 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form2 = rawRow14134 := by decide +kernel

def row14134 : Integer.Sparse Key := [(key1972, -12), (key1984, 12), (key2208, 12), (key2225, -12)]

theorem rowCheck14134 : row14134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14134 := by decide +kernel

theorem rowEval14134 (x : Key → ℝ) : Integer.Sparse.eval row14134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14134, Integer.Sparse.eval_collectBalanced, rawRowCheck14134]

def rawRow14135 : Integer.Sparse Key := [(key2010, 6), (key2010, -2), (key2039, -2), (key2039, -2), (key2010, 6), (key2010, -2), (key2124, -2), (key2124, -2), (key2010, -2), (key2039, -2), (key2039, -2), (key2010, -2), (key2124, -2), (key2124, -2), (key2039, 2), (key2039, 2), (key2124, 2), (key2124, 2), (key2211, 2), (key2211, 2)]

theorem rawRowCheck14135 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form3 = rawRow14135 := by decide +kernel

def row14135 : Integer.Sparse Key := [(key2010, 4), (key2039, -4), (key2124, -4), (key2211, 4)]

theorem rowCheck14135 : row14135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14135 := by decide +kernel

theorem rowEval14135 (x : Key → ℝ) : Integer.Sparse.eval row14135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14135, Integer.Sparse.eval_collectBalanced, rawRowCheck14135]

def rawRow14136 : Integer.Sparse Key := [(key2010, 6), (key2039, -2), (key2010, -2), (key2039, -2), (key2010, 6), (key2124, -2), (key2010, -2), (key2124, -2), (key2039, -2), (key2010, -2), (key2039, -2), (key2124, -2), (key2010, -2), (key2124, -2), (key2124, 2), (key2211, 2), (key2039, 2), (key2211, 2), (key2039, 2), (key2124, 2)]

theorem rawRowCheck14136 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form3 = rawRow14136 := by decide +kernel

def row14136 : Integer.Sparse Key := [(key2010, 4), (key2039, -4), (key2124, -4), (key2211, 4)]

theorem rowCheck14136 : row14136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14136 := by decide +kernel

theorem rowEval14136 (x : Key → ℝ) : Integer.Sparse.eval row14136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14136, Integer.Sparse.eval_collectBalanced, rawRowCheck14136]

def rawRow14137 : Integer.Sparse Key := [(key2010, 6), (key2039, -2), (key2039, -2), (key2010, -2), (key2010, 6), (key2124, -2), (key2124, -2), (key2010, -2), (key2039, -2), (key2039, -2), (key2010, -2), (key2124, -2), (key2124, -2), (key2010, -2), (key2211, 2), (key2124, 2), (key2211, 2), (key2039, 2), (key2124, 2), (key2039, 2)]

theorem rawRowCheck14137 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form3 = rawRow14137 := by decide +kernel

def row14137 : Integer.Sparse Key := [(key2010, 4), (key2039, -4), (key2124, -4), (key2211, 4)]

theorem rowCheck14137 : row14137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14137 := by decide +kernel

theorem rowEval14137 (x : Key → ℝ) : Integer.Sparse.eval row14137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14137, Integer.Sparse.eval_collectBalanced, rawRowCheck14137]

def rawRow14138 : Integer.Sparse Key := [(key2039, 6), (key2010, -2), (key2010, -2), (key2039, -2), (key2124, 6), (key2010, -2), (key2010, -2), (key2124, -2), (key2124, -2), (key2124, -2), (key2211, -2), (key2039, -2), (key2039, -2), (key2211, -2), (key2010, 2), (key2039, 2), (key2010, 2), (key2124, 2), (key2039, 2), (key2124, 2)]

theorem rawRowCheck14138 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form3 = rawRow14138 := by decide +kernel

def row14138 : Integer.Sparse Key := [(key2010, -4), (key2039, 4), (key2124, 4), (key2211, -4)]

theorem rowCheck14138 : row14138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14138 := by decide +kernel

theorem rowEval14138 (x : Key → ℝ) : Integer.Sparse.eval row14138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14138, Integer.Sparse.eval_collectBalanced, rawRowCheck14138]

def rawRow14139 : Integer.Sparse Key := [(key2039, 6), (key2010, -2), (key2039, -2), (key2010, -2), (key2124, 6), (key2010, -2), (key2124, -2), (key2010, -2), (key2124, -2), (key2211, -2), (key2124, -2), (key2039, -2), (key2211, -2), (key2039, -2), (key2039, 2), (key2010, 2), (key2124, 2), (key2010, 2), (key2124, 2), (key2039, 2)]

theorem rawRowCheck14139 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form3 = rawRow14139 := by decide +kernel

def row14139 : Integer.Sparse Key := [(key2010, -4), (key2039, 4), (key2124, 4), (key2211, -4)]

theorem rowCheck14139 : row14139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14139 := by decide +kernel

theorem rowEval14139 (x : Key → ℝ) : Integer.Sparse.eval row14139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14139, Integer.Sparse.eval_collectBalanced, rawRowCheck14139]

def rawRow14140 : Integer.Sparse Key := [(key2039, 6), (key2039, -2), (key2010, -2), (key2010, -2), (key2124, 6), (key2124, -2), (key2010, -2), (key2010, -2), (key2211, -2), (key2124, -2), (key2124, -2), (key2211, -2), (key2039, -2), (key2039, -2), (key2124, 2), (key2124, 2), (key2039, 2), (key2039, 2), (key2010, 2), (key2010, 2)]

theorem rawRowCheck14140 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form3 = rawRow14140 := by decide +kernel

def row14140 : Integer.Sparse Key := [(key2010, -4), (key2039, 4), (key2124, 4), (key2211, -4)]

theorem rowCheck14140 : row14140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14140 := by decide +kernel

theorem rowEval14140 (x : Key → ℝ) : Integer.Sparse.eval row14140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14140, Integer.Sparse.eval_collectBalanced, rawRowCheck14140]

def rawRow14141 : Integer.Sparse Key := [(key2124, 6), (key2124, -2), (key2124, -2), (key2211, -2), (key2039, 6), (key2039, -2), (key2039, -2), (key2211, -2), (key2010, -2), (key2010, -2), (key2039, -2), (key2010, -2), (key2010, -2), (key2124, -2), (key2010, 2), (key2039, 2), (key2010, 2), (key2124, 2), (key2039, 2), (key2124, 2)]

theorem rawRowCheck14141 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form3 = rawRow14141 := by decide +kernel

def row14141 : Integer.Sparse Key := [(key2010, -4), (key2039, 4), (key2124, 4), (key2211, -4)]

theorem rowCheck14141 : row14141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14141 := by decide +kernel

theorem rowEval14141 (x : Key → ℝ) : Integer.Sparse.eval row14141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14141, Integer.Sparse.eval_collectBalanced, rawRowCheck14141]

def rawRow14142 : Integer.Sparse Key := [(key2124, 6), (key2124, -2), (key2211, -2), (key2124, -2), (key2039, 6), (key2039, -2), (key2211, -2), (key2039, -2), (key2010, -2), (key2039, -2), (key2010, -2), (key2010, -2), (key2124, -2), (key2010, -2), (key2039, 2), (key2010, 2), (key2124, 2), (key2010, 2), (key2124, 2), (key2039, 2)]

theorem rawRowCheck14142 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form3 = rawRow14142 := by decide +kernel

def row14142 : Integer.Sparse Key := [(key2010, -4), (key2039, 4), (key2124, 4), (key2211, -4)]

theorem rowCheck14142 : row14142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14142 := by decide +kernel

theorem rowEval14142 (x : Key → ℝ) : Integer.Sparse.eval row14142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14142, Integer.Sparse.eval_collectBalanced, rawRowCheck14142]

def rawRow14143 : Integer.Sparse Key := [(key2124, 6), (key2211, -2), (key2124, -2), (key2124, -2), (key2039, 6), (key2211, -2), (key2039, -2), (key2039, -2), (key2039, -2), (key2010, -2), (key2010, -2), (key2124, -2), (key2010, -2), (key2010, -2), (key2124, 2), (key2124, 2), (key2039, 2), (key2039, 2), (key2010, 2), (key2010, 2)]

theorem rawRowCheck14143 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form3 = rawRow14143 := by decide +kernel

def row14143 : Integer.Sparse Key := [(key2010, -4), (key2039, 4), (key2124, 4), (key2211, -4)]

theorem rowCheck14143 : row14143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14143 := by decide +kernel

theorem rowEval14143 (x : Key → ℝ) : Integer.Sparse.eval row14143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14143, Integer.Sparse.eval_collectBalanced, rawRowCheck14143]

def rawRow14144 : Integer.Sparse Key := [(key2211, 6), (key2124, -2), (key2124, -2), (key2124, -2), (key2211, 6), (key2039, -2), (key2039, -2), (key2039, -2), (key2124, -2), (key2124, -2), (key2124, -2), (key2039, -2), (key2039, -2), (key2039, -2), (key2010, 2), (key2010, 2), (key2010, 2), (key2010, 2), (key2010, 2), (key2010, 2)]

theorem rawRowCheck14144 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form3 = rawRow14144 := by decide +kernel

def row14144 : Integer.Sparse Key := [(key2010, 12), (key2039, -12), (key2124, -12), (key2211, 12)]

theorem rowCheck14144 : row14144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14144 := by decide +kernel

theorem rowEval14144 (x : Key → ℝ) : Integer.Sparse.eval row14144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14144, Integer.Sparse.eval_collectBalanced, rawRowCheck14144]

def rawRow14145 : Integer.Sparse Key := [(key53, -2), (key53, -2), (key59, -2), (key59, 6), (key53, -2), (key53, -2), (key59, -2), (key53, 2), (key53, 2), (key121, 2), (key121, 2), (key124, 2), (key124, 2), (key59, -2), (key124, -2), (key124, -2), (key59, 6), (key59, -2), (key124, -2), (key124, -2)]

theorem rawRowCheck14145 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form4 = rawRow14145 := by decide +kernel

def row14145 : Integer.Sparse Key := [(key53, -4), (key59, 4), (key121, 4), (key124, -4)]

theorem rowCheck14145 : row14145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14145 := by decide +kernel

theorem rowEval14145 (x : Key → ℝ) : Integer.Sparse.eval row14145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14145, Integer.Sparse.eval_collectBalanced, rawRowCheck14145]

def rawRow14146 : Integer.Sparse Key := [(key53, -2), (key59, -2), (key53, -2), (key59, 6), (key53, -2), (key59, -2), (key53, -2), (key121, 2), (key124, 2), (key53, 2), (key124, 2), (key53, 2), (key121, 2), (key124, -2), (key59, -2), (key124, -2), (key59, 6), (key124, -2), (key59, -2), (key124, -2)]

theorem rawRowCheck14146 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form4 = rawRow14146 := by decide +kernel

def row14146 : Integer.Sparse Key := [(key53, -4), (key59, 4), (key121, 4), (key124, -4)]

theorem rowCheck14146 : row14146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14146 := by decide +kernel

theorem rowEval14146 (x : Key → ℝ) : Integer.Sparse.eval row14146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14146, Integer.Sparse.eval_collectBalanced, rawRowCheck14146]

def rawRow14147 : Integer.Sparse Key := [(key59, -2), (key53, -2), (key53, -2), (key59, 6), (key59, -2), (key53, -2), (key53, -2), (key124, 2), (key121, 2), (key124, 2), (key53, 2), (key121, 2), (key53, 2), (key124, -2), (key124, -2), (key59, -2), (key59, 6), (key124, -2), (key124, -2), (key59, -2)]

theorem rawRowCheck14147 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form4 = rawRow14147 := by decide +kernel

def row14147 : Integer.Sparse Key := [(key53, -4), (key59, 4), (key121, 4), (key124, -4)]

theorem rowCheck14147 : row14147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14147 := by decide +kernel

theorem rowEval14147 (x : Key → ℝ) : Integer.Sparse.eval row14147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14147, Integer.Sparse.eval_collectBalanced, rawRowCheck14147]

def rawRow14148 : Integer.Sparse Key := [(key53, -2), (key59, -2), (key59, -2), (key53, 6), (key121, -2), (key124, -2), (key124, -2), (key53, 2), (key59, 2), (key53, 2), (key124, 2), (key59, 2), (key124, 2), (key53, -2), (key53, -2), (key121, -2), (key124, 6), (key59, -2), (key59, -2), (key124, -2)]

theorem rawRowCheck14148 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form4 = rawRow14148 := by decide +kernel

def row14148 : Integer.Sparse Key := [(key53, 4), (key59, -4), (key121, -4), (key124, 4)]

theorem rowCheck14148 : row14148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14148 := by decide +kernel

theorem rowEval14148 (x : Key → ℝ) : Integer.Sparse.eval row14148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14148, Integer.Sparse.eval_collectBalanced, rawRowCheck14148]

def rawRow14149 : Integer.Sparse Key := [(key59, -2), (key53, -2), (key59, -2), (key53, 6), (key124, -2), (key121, -2), (key124, -2), (key59, 2), (key53, 2), (key124, 2), (key53, 2), (key124, 2), (key59, 2), (key53, -2), (key121, -2), (key53, -2), (key124, 6), (key59, -2), (key124, -2), (key59, -2)]

theorem rawRowCheck14149 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form4 = rawRow14149 := by decide +kernel

def row14149 : Integer.Sparse Key := [(key53, 4), (key59, -4), (key121, -4), (key124, 4)]

theorem rowCheck14149 : row14149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14149 := by decide +kernel

theorem rowEval14149 (x : Key → ℝ) : Integer.Sparse.eval row14149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14149, Integer.Sparse.eval_collectBalanced, rawRowCheck14149]

def rawRow14150 : Integer.Sparse Key := [(key59, -2), (key59, -2), (key53, -2), (key53, 6), (key124, -2), (key124, -2), (key121, -2), (key124, 2), (key124, 2), (key59, 2), (key59, 2), (key53, 2), (key53, 2), (key121, -2), (key53, -2), (key53, -2), (key124, 6), (key124, -2), (key59, -2), (key59, -2)]

theorem rawRowCheck14150 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form4 = rawRow14150 := by decide +kernel

def row14150 : Integer.Sparse Key := [(key53, 4), (key59, -4), (key121, -4), (key124, 4)]

theorem rowCheck14150 : row14150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14150 := by decide +kernel

theorem rowEval14150 (x : Key → ℝ) : Integer.Sparse.eval row14150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14150, Integer.Sparse.eval_collectBalanced, rawRowCheck14150]

def rawRow14151 : Integer.Sparse Key := [(key121, -2), (key124, -2), (key124, -2), (key124, 6), (key53, -2), (key59, -2), (key59, -2), (key53, 2), (key59, 2), (key53, 2), (key124, 2), (key59, 2), (key124, 2), (key59, -2), (key59, -2), (key124, -2), (key53, 6), (key53, -2), (key53, -2), (key121, -2)]

theorem rawRowCheck14151 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form4 = rawRow14151 := by decide +kernel

def row14151 : Integer.Sparse Key := [(key53, 4), (key59, -4), (key121, -4), (key124, 4)]

theorem rowCheck14151 : row14151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14151 := by decide +kernel

theorem rowEval14151 (x : Key → ℝ) : Integer.Sparse.eval row14151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14151, Integer.Sparse.eval_collectBalanced, rawRowCheck14151]

def rawRow14152 : Integer.Sparse Key := [(key124, -2), (key121, -2), (key124, -2), (key124, 6), (key59, -2), (key53, -2), (key59, -2), (key59, 2), (key53, 2), (key124, 2), (key53, 2), (key124, 2), (key59, 2), (key59, -2), (key124, -2), (key59, -2), (key53, 6), (key53, -2), (key121, -2), (key53, -2)]

theorem rawRowCheck14152 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form4 = rawRow14152 := by decide +kernel

def row14152 : Integer.Sparse Key := [(key53, 4), (key59, -4), (key121, -4), (key124, 4)]

theorem rowCheck14152 : row14152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14152 := by decide +kernel

theorem rowEval14152 (x : Key → ℝ) : Integer.Sparse.eval row14152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14152, Integer.Sparse.eval_collectBalanced, rawRowCheck14152]

def rawRow14153 : Integer.Sparse Key := [(key124, -2), (key124, -2), (key121, -2), (key124, 6), (key59, -2), (key59, -2), (key53, -2), (key124, 2), (key124, 2), (key59, 2), (key59, 2), (key53, 2), (key53, 2), (key124, -2), (key59, -2), (key59, -2), (key53, 6), (key121, -2), (key53, -2), (key53, -2)]

theorem rawRowCheck14153 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form4 = rawRow14153 := by decide +kernel

def row14153 : Integer.Sparse Key := [(key53, 4), (key59, -4), (key121, -4), (key124, 4)]

theorem rowCheck14153 : row14153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14153 := by decide +kernel

theorem rowEval14153 (x : Key → ℝ) : Integer.Sparse.eval row14153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14153, Integer.Sparse.eval_collectBalanced, rawRowCheck14153]

def rawRow14154 : Integer.Sparse Key := [(key124, -2), (key124, -2), (key124, -2), (key121, 6), (key124, -2), (key124, -2), (key124, -2), (key59, 2), (key59, 2), (key59, 2), (key59, 2), (key59, 2), (key59, 2), (key53, -2), (key53, -2), (key53, -2), (key121, 6), (key53, -2), (key53, -2), (key53, -2)]

theorem rawRowCheck14154 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form4 = rawRow14154 := by decide +kernel

def row14154 : Integer.Sparse Key := [(key53, -12), (key59, 12), (key121, 12), (key124, -12)]

theorem rowCheck14154 : row14154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14154 := by decide +kernel

theorem rowEval14154 (x : Key → ℝ) : Integer.Sparse.eval row14154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14154, Integer.Sparse.eval_collectBalanced, rawRowCheck14154]

def rawRow14155 : Integer.Sparse Key := [(key57, 4), (key129, 4), (key129, 4), (key64, -2), (key64, -2), (key129, -2), (key129, -2), (key140, -2), (key140, -2), (key64, -2), (key64, -2), (key129, -2), (key129, -2), (key140, -2), (key140, -2), (key77, 4), (key140, 4), (key140, 4)]

theorem rawRowCheck14155 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form5 = rawRow14155 := by decide +kernel

def row14155 : Integer.Sparse Key := [(key57, 4), (key64, -8), (key77, 4)]

theorem rowCheck14155 : row14155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14155 := by decide +kernel

theorem rowEval14155 (x : Key → ℝ) : Integer.Sparse.eval row14155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14155, Integer.Sparse.eval_collectBalanced, rawRowCheck14155]

def rawRow14156 : Integer.Sparse Key := [(key129, 4), (key57, 4), (key129, 4), (key129, -2), (key140, -2), (key64, -2), (key140, -2), (key64, -2), (key129, -2), (key129, -2), (key140, -2), (key64, -2), (key140, -2), (key64, -2), (key129, -2), (key140, 4), (key77, 4), (key140, 4)]

theorem rawRowCheck14156 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form5 = rawRow14156 := by decide +kernel

def row14156 : Integer.Sparse Key := [(key57, 4), (key64, -8), (key77, 4)]

theorem rowCheck14156 : row14156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14156 := by decide +kernel

theorem rowEval14156 (x : Key → ℝ) : Integer.Sparse.eval row14156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14156, Integer.Sparse.eval_collectBalanced, rawRowCheck14156]

def rawRow14157 : Integer.Sparse Key := [(key129, 4), (key129, 4), (key57, 4), (key140, -2), (key129, -2), (key140, -2), (key64, -2), (key129, -2), (key64, -2), (key140, -2), (key129, -2), (key140, -2), (key64, -2), (key129, -2), (key64, -2), (key140, 4), (key140, 4), (key77, 4)]

theorem rawRowCheck14157 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form5 = rawRow14157 := by decide +kernel

def row14157 : Integer.Sparse Key := [(key57, 4), (key64, -8), (key77, 4)]

theorem rowCheck14157 : row14157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14157 := by decide +kernel

theorem rowEval14157 (x : Key → ℝ) : Integer.Sparse.eval row14157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14157, Integer.Sparse.eval_collectBalanced, rawRowCheck14157]

def rawRow14158 : Integer.Sparse Key := [(key64, 4), (key64, 4), (key140, 4), (key57, -2), (key64, -2), (key57, -2), (key129, -2), (key64, -2), (key129, -2), (key64, -2), (key77, -2), (key64, -2), (key140, -2), (key77, -2), (key140, -2), (key64, 4), (key64, 4), (key129, 4)]

theorem rawRowCheck14158 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form5 = rawRow14158 := by decide +kernel

def row14158 : Integer.Sparse Key := [(key57, -4), (key64, 8), (key77, -4)]

theorem rowCheck14158 : row14158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14158 := by decide +kernel

theorem rowEval14158 (x : Key → ℝ) : Integer.Sparse.eval row14158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14158, Integer.Sparse.eval_collectBalanced, rawRowCheck14158]

def rawRow14159 : Integer.Sparse Key := [(key64, 4), (key140, 4), (key64, 4), (key64, -2), (key57, -2), (key129, -2), (key57, -2), (key129, -2), (key64, -2), (key77, -2), (key64, -2), (key140, -2), (key64, -2), (key140, -2), (key77, -2), (key64, 4), (key129, 4), (key64, 4)]

theorem rawRowCheck14159 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form5 = rawRow14159 := by decide +kernel

def row14159 : Integer.Sparse Key := [(key57, -4), (key64, 8), (key77, -4)]

theorem rowCheck14159 : row14159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14159 := by decide +kernel

theorem rowEval14159 (x : Key → ℝ) : Integer.Sparse.eval row14159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14159, Integer.Sparse.eval_collectBalanced, rawRowCheck14159]

def rawRow14160 : Integer.Sparse Key := [(key140, 4), (key64, 4), (key64, 4), (key129, -2), (key129, -2), (key64, -2), (key64, -2), (key57, -2), (key57, -2), (key140, -2), (key140, -2), (key77, -2), (key77, -2), (key64, -2), (key64, -2), (key129, 4), (key64, 4), (key64, 4)]

theorem rawRowCheck14160 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form5 = rawRow14160 := by decide +kernel

def row14160 : Integer.Sparse Key := [(key57, -4), (key64, 8), (key77, -4)]

theorem rowCheck14160 : row14160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14160 := by decide +kernel

theorem rowEval14160 (x : Key → ℝ) : Integer.Sparse.eval row14160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14160, Integer.Sparse.eval_collectBalanced, rawRowCheck14160]

def rawRow14161 : Integer.Sparse Key := [(key64, 4), (key64, 4), (key140, 4), (key64, -2), (key77, -2), (key64, -2), (key140, -2), (key77, -2), (key140, -2), (key57, -2), (key64, -2), (key57, -2), (key129, -2), (key64, -2), (key129, -2), (key64, 4), (key64, 4), (key129, 4)]

theorem rawRowCheck14161 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form5 = rawRow14161 := by decide +kernel

def row14161 : Integer.Sparse Key := [(key57, -4), (key64, 8), (key77, -4)]

theorem rowCheck14161 : row14161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14161 := by decide +kernel

theorem rowEval14161 (x : Key → ℝ) : Integer.Sparse.eval row14161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14161, Integer.Sparse.eval_collectBalanced, rawRowCheck14161]

def rawRow14162 : Integer.Sparse Key := [(key64, 4), (key140, 4), (key64, 4), (key77, -2), (key64, -2), (key140, -2), (key64, -2), (key140, -2), (key77, -2), (key64, -2), (key57, -2), (key129, -2), (key57, -2), (key129, -2), (key64, -2), (key64, 4), (key129, 4), (key64, 4)]

theorem rawRowCheck14162 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form5 = rawRow14162 := by decide +kernel

def row14162 : Integer.Sparse Key := [(key57, -4), (key64, 8), (key77, -4)]

theorem rowCheck14162 : row14162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14162 := by decide +kernel

theorem rowEval14162 (x : Key → ℝ) : Integer.Sparse.eval row14162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14162, Integer.Sparse.eval_collectBalanced, rawRowCheck14162]

def rawRow14163 : Integer.Sparse Key := [(key140, 4), (key64, 4), (key64, 4), (key140, -2), (key140, -2), (key77, -2), (key77, -2), (key64, -2), (key64, -2), (key129, -2), (key129, -2), (key64, -2), (key64, -2), (key57, -2), (key57, -2), (key129, 4), (key64, 4), (key64, 4)]

theorem rawRowCheck14163 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form5 = rawRow14163 := by decide +kernel

def row14163 : Integer.Sparse Key := [(key57, -4), (key64, 8), (key77, -4)]

theorem rowCheck14163 : row14163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14163 := by decide +kernel

theorem rowEval14163 (x : Key → ℝ) : Integer.Sparse.eval row14163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14163, Integer.Sparse.eval_collectBalanced, rawRowCheck14163]

def rawRow14164 : Integer.Sparse Key := [(key77, 4), (key77, 4), (key77, 4), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key57, 4), (key57, 4), (key57, 4)]

theorem rawRowCheck14164 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form5 = rawRow14164 := by decide +kernel

def row14164 : Integer.Sparse Key := [(key57, 12), (key64, -24), (key77, 12)]

theorem rowCheck14164 : row14164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14164 := by decide +kernel

theorem rowEval14164 (x : Key → ℝ) : Integer.Sparse.eval row14164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14164, Integer.Sparse.eval_collectBalanced, rawRowCheck14164]

def rawRow14165 : Integer.Sparse Key := [(key2012, -1), (key2012, -1), (key2126, -1), (key2126, -1), (key2143, -1), (key2143, -1), (key2025, 2), (key2143, 2), (key2143, 2), (key2012, -1), (key2012, -1), (key2126, -1), (key2126, -1), (key2143, -1), (key2143, -1), (key2041, 2), (key2041, 2), (key2126, 2), (key2126, 2), (key2227, 2), (key2227, 2), (key2054, -1), (key2054, -1), (key2143, -1), (key2143, -1), (key2227, -1), (key2227, -1), (key2025, 2), (key2143, 2), (key2143, 2), (key2054, -1), (key2054, -1), (key2143, -1), (key2143, -1), (key2227, -1), (key2227, -1)]

theorem rawRowCheck14165 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form6 = rawRow14165 := by decide +kernel

def row14165 : Integer.Sparse Key := [(key2012, -4), (key2025, 4), (key2041, 4), (key2054, -4)]

theorem rowCheck14165 : row14165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14165 := by decide +kernel

theorem rowEval14165 (x : Key → ℝ) : Integer.Sparse.eval row14165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14165, Integer.Sparse.eval_collectBalanced, rawRowCheck14165]

def rawRow14166 : Integer.Sparse Key := [(key2126, -1), (key2143, -1), (key2012, -1), (key2143, -1), (key2012, -1), (key2126, -1), (key2143, 2), (key2025, 2), (key2143, 2), (key2126, -1), (key2143, -1), (key2012, -1), (key2143, -1), (key2012, -1), (key2126, -1), (key2126, 2), (key2227, 2), (key2041, 2), (key2227, 2), (key2041, 2), (key2126, 2), (key2143, -1), (key2227, -1), (key2054, -1), (key2227, -1), (key2054, -1), (key2143, -1), (key2143, 2), (key2025, 2), (key2143, 2), (key2143, -1), (key2227, -1), (key2054, -1), (key2227, -1), (key2054, -1), (key2143, -1)]

theorem rawRowCheck14166 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form6 = rawRow14166 := by decide +kernel

def row14166 : Integer.Sparse Key := [(key2012, -4), (key2025, 4), (key2041, 4), (key2054, -4)]

theorem rowCheck14166 : row14166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14166 := by decide +kernel

theorem rowEval14166 (x : Key → ℝ) : Integer.Sparse.eval row14166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14166, Integer.Sparse.eval_collectBalanced, rawRowCheck14166]

def rawRow14167 : Integer.Sparse Key := [(key2143, -1), (key2126, -1), (key2143, -1), (key2012, -1), (key2126, -1), (key2012, -1), (key2143, 2), (key2143, 2), (key2025, 2), (key2143, -1), (key2126, -1), (key2143, -1), (key2012, -1), (key2126, -1), (key2012, -1), (key2227, 2), (key2126, 2), (key2227, 2), (key2041, 2), (key2126, 2), (key2041, 2), (key2227, -1), (key2143, -1), (key2227, -1), (key2054, -1), (key2143, -1), (key2054, -1), (key2143, 2), (key2143, 2), (key2025, 2), (key2227, -1), (key2143, -1), (key2227, -1), (key2054, -1), (key2143, -1), (key2054, -1)]

theorem rawRowCheck14167 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form6 = rawRow14167 := by decide +kernel

def row14167 : Integer.Sparse Key := [(key2012, -4), (key2025, 4), (key2041, 4), (key2054, -4)]

theorem rowCheck14167 : row14167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14167 := by decide +kernel

theorem rowEval14167 (x : Key → ℝ) : Integer.Sparse.eval row14167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14167, Integer.Sparse.eval_collectBalanced, rawRowCheck14167]

def rawRow14168 : Integer.Sparse Key := [(key2012, -1), (key2025, -1), (key2012, -1), (key2143, -1), (key2025, -1), (key2143, -1), (key2012, 2), (key2012, 2), (key2126, 2), (key2041, -1), (key2054, -1), (key2041, -1), (key2227, -1), (key2054, -1), (key2227, -1), (key2012, 2), (key2054, 2), (key2012, 2), (key2143, 2), (key2054, 2), (key2143, 2), (key2012, -1), (key2041, -1), (key2012, -1), (key2126, -1), (key2041, -1), (key2126, -1), (key2054, 2), (key2054, 2), (key2227, 2), (key2025, -1), (key2054, -1), (key2025, -1), (key2143, -1), (key2054, -1), (key2143, -1)]

theorem rawRowCheck14168 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form6 = rawRow14168 := by decide +kernel

def row14168 : Integer.Sparse Key := [(key2012, 4), (key2025, -4), (key2041, -4), (key2054, 4)]

theorem rowCheck14168 : row14168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14168 := by decide +kernel

theorem rowEval14168 (x : Key → ℝ) : Integer.Sparse.eval row14168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14168, Integer.Sparse.eval_collectBalanced, rawRowCheck14168]

def rawRow14169 : Integer.Sparse Key := [(key2025, -1), (key2012, -1), (key2143, -1), (key2012, -1), (key2143, -1), (key2025, -1), (key2012, 2), (key2126, 2), (key2012, 2), (key2054, -1), (key2041, -1), (key2227, -1), (key2041, -1), (key2227, -1), (key2054, -1), (key2054, 2), (key2012, 2), (key2143, 2), (key2012, 2), (key2143, 2), (key2054, 2), (key2041, -1), (key2012, -1), (key2126, -1), (key2012, -1), (key2126, -1), (key2041, -1), (key2054, 2), (key2227, 2), (key2054, 2), (key2054, -1), (key2025, -1), (key2143, -1), (key2025, -1), (key2143, -1), (key2054, -1)]

theorem rawRowCheck14169 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form6 = rawRow14169 := by decide +kernel

def row14169 : Integer.Sparse Key := [(key2012, 4), (key2025, -4), (key2041, -4), (key2054, 4)]

theorem rowCheck14169 : row14169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14169 := by decide +kernel

theorem rowEval14169 (x : Key → ℝ) : Integer.Sparse.eval row14169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14169, Integer.Sparse.eval_collectBalanced, rawRowCheck14169]

def rawRow14170 : Integer.Sparse Key := [(key2143, -1), (key2143, -1), (key2025, -1), (key2025, -1), (key2012, -1), (key2012, -1), (key2126, 2), (key2012, 2), (key2012, 2), (key2227, -1), (key2227, -1), (key2054, -1), (key2054, -1), (key2041, -1), (key2041, -1), (key2143, 2), (key2143, 2), (key2054, 2), (key2054, 2), (key2012, 2), (key2012, 2), (key2126, -1), (key2126, -1), (key2041, -1), (key2041, -1), (key2012, -1), (key2012, -1), (key2227, 2), (key2054, 2), (key2054, 2), (key2143, -1), (key2143, -1), (key2054, -1), (key2054, -1), (key2025, -1), (key2025, -1)]

theorem rawRowCheck14170 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form6 = rawRow14170 := by decide +kernel

def row14170 : Integer.Sparse Key := [(key2012, 4), (key2025, -4), (key2041, -4), (key2054, 4)]

theorem rowCheck14170 : row14170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14170 := by decide +kernel

theorem rowEval14170 (x : Key → ℝ) : Integer.Sparse.eval row14170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14170, Integer.Sparse.eval_collectBalanced, rawRowCheck14170]

def rawRow14171 : Integer.Sparse Key := [(key2041, -1), (key2054, -1), (key2041, -1), (key2227, -1), (key2054, -1), (key2227, -1), (key2054, 2), (key2054, 2), (key2227, 2), (key2012, -1), (key2025, -1), (key2012, -1), (key2143, -1), (key2025, -1), (key2143, -1), (key2012, 2), (key2054, 2), (key2012, 2), (key2143, 2), (key2054, 2), (key2143, 2), (key2025, -1), (key2054, -1), (key2025, -1), (key2143, -1), (key2054, -1), (key2143, -1), (key2012, 2), (key2012, 2), (key2126, 2), (key2012, -1), (key2041, -1), (key2012, -1), (key2126, -1), (key2041, -1), (key2126, -1)]

theorem rawRowCheck14171 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form6 = rawRow14171 := by decide +kernel

def row14171 : Integer.Sparse Key := [(key2012, 4), (key2025, -4), (key2041, -4), (key2054, 4)]

theorem rowCheck14171 : row14171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14171 := by decide +kernel

theorem rowEval14171 (x : Key → ℝ) : Integer.Sparse.eval row14171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14171, Integer.Sparse.eval_collectBalanced, rawRowCheck14171]

def rawRow14172 : Integer.Sparse Key := [(key2054, -1), (key2041, -1), (key2227, -1), (key2041, -1), (key2227, -1), (key2054, -1), (key2054, 2), (key2227, 2), (key2054, 2), (key2025, -1), (key2012, -1), (key2143, -1), (key2012, -1), (key2143, -1), (key2025, -1), (key2054, 2), (key2012, 2), (key2143, 2), (key2012, 2), (key2143, 2), (key2054, 2), (key2054, -1), (key2025, -1), (key2143, -1), (key2025, -1), (key2143, -1), (key2054, -1), (key2012, 2), (key2126, 2), (key2012, 2), (key2041, -1), (key2012, -1), (key2126, -1), (key2012, -1), (key2126, -1), (key2041, -1)]

theorem rawRowCheck14172 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form6 = rawRow14172 := by decide +kernel

def row14172 : Integer.Sparse Key := [(key2012, 4), (key2025, -4), (key2041, -4), (key2054, 4)]

theorem rowCheck14172 : row14172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14172 := by decide +kernel

theorem rowEval14172 (x : Key → ℝ) : Integer.Sparse.eval row14172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14172, Integer.Sparse.eval_collectBalanced, rawRowCheck14172]

def rawRow14173 : Integer.Sparse Key := [(key2227, -1), (key2227, -1), (key2054, -1), (key2054, -1), (key2041, -1), (key2041, -1), (key2227, 2), (key2054, 2), (key2054, 2), (key2143, -1), (key2143, -1), (key2025, -1), (key2025, -1), (key2012, -1), (key2012, -1), (key2143, 2), (key2143, 2), (key2054, 2), (key2054, 2), (key2012, 2), (key2012, 2), (key2143, -1), (key2143, -1), (key2054, -1), (key2054, -1), (key2025, -1), (key2025, -1), (key2126, 2), (key2012, 2), (key2012, 2), (key2126, -1), (key2126, -1), (key2041, -1), (key2041, -1), (key2012, -1), (key2012, -1)]

theorem rawRowCheck14173 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form6 = rawRow14173 := by decide +kernel

def row14173 : Integer.Sparse Key := [(key2012, 4), (key2025, -4), (key2041, -4), (key2054, 4)]

theorem rowCheck14173 : row14173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14173 := by decide +kernel

theorem rowEval14173 (x : Key → ℝ) : Integer.Sparse.eval row14173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14173, Integer.Sparse.eval_collectBalanced, rawRowCheck14173]

def rawRow14174 : Integer.Sparse Key := [(key2054, -1), (key2054, -1), (key2054, -1), (key2054, -1), (key2054, -1), (key2054, -1), (key2041, 2), (key2041, 2), (key2041, 2), (key2054, -1), (key2054, -1), (key2054, -1), (key2054, -1), (key2054, -1), (key2054, -1), (key2025, 2), (key2025, 2), (key2025, 2), (key2025, 2), (key2025, 2), (key2025, 2), (key2012, -1), (key2012, -1), (key2012, -1), (key2012, -1), (key2012, -1), (key2012, -1), (key2041, 2), (key2041, 2), (key2041, 2), (key2012, -1), (key2012, -1), (key2012, -1), (key2012, -1), (key2012, -1), (key2012, -1)]

theorem rawRowCheck14174 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form6 = rawRow14174 := by decide +kernel

def row14174 : Integer.Sparse Key := [(key2012, -12), (key2025, 12), (key2041, 12), (key2054, -12)]

theorem rowCheck14174 : row14174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14174 := by decide +kernel

theorem rowEval14174 (x : Key → ℝ) : Integer.Sparse.eval row14174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14174, Integer.Sparse.eval_collectBalanced, rawRowCheck14174]

def rawRow14175 : Integer.Sparse Key := [(key2100, 4), (key2105, 4), (key2105, 4), (key2105, -4), (key2105, -4), (key2130, -4), (key2105, -4), (key2105, -4), (key2130, -4), (key2130, 12)]

theorem rawRowCheck14175 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form7 = rawRow14175 := by decide +kernel

def row14175 : Integer.Sparse Key := [(key2100, 4), (key2105, -8), (key2130, 4)]

theorem rowCheck14175 : row14175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14175 := by decide +kernel

theorem rowEval14175 (x : Key → ℝ) : Integer.Sparse.eval row14175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14175, Integer.Sparse.eval_collectBalanced, rawRowCheck14175]

def rawRow14176 : Integer.Sparse Key := [(key2105, 4), (key2100, 4), (key2105, 4), (key2105, -4), (key2130, -4), (key2105, -4), (key2105, -4), (key2130, -4), (key2105, -4), (key2130, 12)]

theorem rawRowCheck14176 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form7 = rawRow14176 := by decide +kernel

def row14176 : Integer.Sparse Key := [(key2100, 4), (key2105, -8), (key2130, 4)]

theorem rowCheck14176 : row14176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14176 := by decide +kernel

theorem rowEval14176 (x : Key → ℝ) : Integer.Sparse.eval row14176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14176, Integer.Sparse.eval_collectBalanced, rawRowCheck14176]

def rawRow14177 : Integer.Sparse Key := [(key2105, 4), (key2105, 4), (key2100, 4), (key2130, -4), (key2105, -4), (key2105, -4), (key2130, -4), (key2105, -4), (key2105, -4), (key2130, 12)]

theorem rawRowCheck14177 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form7 = rawRow14177 := by decide +kernel

def row14177 : Integer.Sparse Key := [(key2100, 4), (key2105, -8), (key2130, 4)]

theorem rowCheck14177 : row14177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14177 := by decide +kernel

theorem rowEval14177 (x : Key → ℝ) : Integer.Sparse.eval row14177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14177, Integer.Sparse.eval_collectBalanced, rawRowCheck14177]

def rawRow14178 : Integer.Sparse Key := [(key2105, 4), (key2105, 4), (key2130, 4), (key2100, -4), (key2105, -4), (key2105, -4), (key2105, -4), (key2130, -4), (key2130, -4), (key2105, 12)]

theorem rawRowCheck14178 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form7 = rawRow14178 := by decide +kernel

def row14178 : Integer.Sparse Key := [(key2100, -4), (key2105, 8), (key2130, -4)]

theorem rowCheck14178 : row14178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14178 := by decide +kernel

theorem rowEval14178 (x : Key → ℝ) : Integer.Sparse.eval row14178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14178, Integer.Sparse.eval_collectBalanced, rawRowCheck14178]

def rawRow14179 : Integer.Sparse Key := [(key2105, 4), (key2130, 4), (key2105, 4), (key2105, -4), (key2100, -4), (key2105, -4), (key2130, -4), (key2105, -4), (key2130, -4), (key2105, 12)]

theorem rawRowCheck14179 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form7 = rawRow14179 := by decide +kernel

def row14179 : Integer.Sparse Key := [(key2100, -4), (key2105, 8), (key2130, -4)]

theorem rowCheck14179 : row14179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14179 := by decide +kernel

theorem rowEval14179 (x : Key → ℝ) : Integer.Sparse.eval row14179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14179, Integer.Sparse.eval_collectBalanced, rawRowCheck14179]

def rawRow14180 : Integer.Sparse Key := [(key2130, 4), (key2105, 4), (key2105, 4), (key2105, -4), (key2105, -4), (key2100, -4), (key2130, -4), (key2130, -4), (key2105, -4), (key2105, 12)]

theorem rawRowCheck14180 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form7 = rawRow14180 := by decide +kernel

def row14180 : Integer.Sparse Key := [(key2100, -4), (key2105, 8), (key2130, -4)]

theorem rowCheck14180 : row14180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14180 := by decide +kernel

theorem rowEval14180 (x : Key → ℝ) : Integer.Sparse.eval row14180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14180, Integer.Sparse.eval_collectBalanced, rawRowCheck14180]

def rawRow14181 : Integer.Sparse Key := [(key2105, 4), (key2105, 4), (key2130, 4), (key2105, -4), (key2130, -4), (key2130, -4), (key2100, -4), (key2105, -4), (key2105, -4), (key2105, 12)]

theorem rawRowCheck14181 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form7 = rawRow14181 := by decide +kernel

def row14181 : Integer.Sparse Key := [(key2100, -4), (key2105, 8), (key2130, -4)]

theorem rowCheck14181 : row14181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14181 := by decide +kernel

theorem rowEval14181 (x : Key → ℝ) : Integer.Sparse.eval row14181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14181, Integer.Sparse.eval_collectBalanced, rawRowCheck14181]

def rawRow14182 : Integer.Sparse Key := [(key2105, 4), (key2130, 4), (key2105, 4), (key2130, -4), (key2105, -4), (key2130, -4), (key2105, -4), (key2100, -4), (key2105, -4), (key2105, 12)]

theorem rawRowCheck14182 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form7 = rawRow14182 := by decide +kernel

def row14182 : Integer.Sparse Key := [(key2100, -4), (key2105, 8), (key2130, -4)]

theorem rowCheck14182 : row14182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14182 := by decide +kernel

theorem rowEval14182 (x : Key → ℝ) : Integer.Sparse.eval row14182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14182, Integer.Sparse.eval_collectBalanced, rawRowCheck14182]

def rawRow14183 : Integer.Sparse Key := [(key2130, 4), (key2105, 4), (key2105, 4), (key2130, -4), (key2130, -4), (key2105, -4), (key2105, -4), (key2105, -4), (key2100, -4), (key2105, 12)]

theorem rawRowCheck14183 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form7 = rawRow14183 := by decide +kernel

def row14183 : Integer.Sparse Key := [(key2100, -4), (key2105, 8), (key2130, -4)]

theorem rowCheck14183 : row14183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14183 := by decide +kernel

theorem rowEval14183 (x : Key → ℝ) : Integer.Sparse.eval row14183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14183, Integer.Sparse.eval_collectBalanced, rawRowCheck14183]

def rawRow14184 : Integer.Sparse Key := [(key2130, 4), (key2130, 4), (key2130, 4), (key2105, -4), (key2105, -4), (key2105, -4), (key2105, -4), (key2105, -4), (key2105, -4), (key2100, 12)]

theorem rawRowCheck14184 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form7 = rawRow14184 := by decide +kernel

def row14184 : Integer.Sparse Key := [(key2100, 12), (key2105, -24), (key2130, 12)]

theorem rowCheck14184 : row14184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14184 := by decide +kernel

theorem rowEval14184 (x : Key → ℝ) : Integer.Sparse.eval row14184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14184, Integer.Sparse.eval_collectBalanced, rawRowCheck14184]

def rawRow14185 : Integer.Sparse Key := [(key1971, -2), (key1971, -2), (key1979, -2), (key1979, 6), (key1971, -2), (key1971, -2), (key1979, -2), (key1971, 2), (key1971, 2), (key2207, 2), (key2207, 2), (key2216, 2), (key2216, 2), (key1979, -2), (key2216, -2), (key2216, -2), (key1979, 6), (key1979, -2), (key2216, -2), (key2216, -2)]

theorem rawRowCheck14185 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form8 = rawRow14185 := by decide +kernel

def row14185 : Integer.Sparse Key := [(key1971, -4), (key1979, 4), (key2207, 4), (key2216, -4)]

theorem rowCheck14185 : row14185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14185 := by decide +kernel

theorem rowEval14185 (x : Key → ℝ) : Integer.Sparse.eval row14185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14185, Integer.Sparse.eval_collectBalanced, rawRowCheck14185]

def rawRow14186 : Integer.Sparse Key := [(key1971, -2), (key1979, -2), (key1971, -2), (key1979, 6), (key1971, -2), (key1979, -2), (key1971, -2), (key2207, 2), (key2216, 2), (key1971, 2), (key2216, 2), (key1971, 2), (key2207, 2), (key2216, -2), (key1979, -2), (key2216, -2), (key1979, 6), (key2216, -2), (key1979, -2), (key2216, -2)]

theorem rawRowCheck14186 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form8 = rawRow14186 := by decide +kernel

def row14186 : Integer.Sparse Key := [(key1971, -4), (key1979, 4), (key2207, 4), (key2216, -4)]

theorem rowCheck14186 : row14186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14186 := by decide +kernel

theorem rowEval14186 (x : Key → ℝ) : Integer.Sparse.eval row14186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14186, Integer.Sparse.eval_collectBalanced, rawRowCheck14186]

def rawRow14187 : Integer.Sparse Key := [(key1979, -2), (key1971, -2), (key1971, -2), (key1979, 6), (key1979, -2), (key1971, -2), (key1971, -2), (key2216, 2), (key2207, 2), (key2216, 2), (key1971, 2), (key2207, 2), (key1971, 2), (key2216, -2), (key2216, -2), (key1979, -2), (key1979, 6), (key2216, -2), (key2216, -2), (key1979, -2)]

theorem rawRowCheck14187 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form8 = rawRow14187 := by decide +kernel

def row14187 : Integer.Sparse Key := [(key1971, -4), (key1979, 4), (key2207, 4), (key2216, -4)]

theorem rowCheck14187 : row14187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14187 := by decide +kernel

theorem rowEval14187 (x : Key → ℝ) : Integer.Sparse.eval row14187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14187, Integer.Sparse.eval_collectBalanced, rawRowCheck14187]

def rawRow14188 : Integer.Sparse Key := [(key1971, -2), (key1979, -2), (key1979, -2), (key1971, 6), (key2207, -2), (key2216, -2), (key2216, -2), (key1971, 2), (key1979, 2), (key1971, 2), (key2216, 2), (key1979, 2), (key2216, 2), (key1971, -2), (key1971, -2), (key2207, -2), (key2216, 6), (key1979, -2), (key1979, -2), (key2216, -2)]

theorem rawRowCheck14188 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form8 = rawRow14188 := by decide +kernel

def row14188 : Integer.Sparse Key := [(key1971, 4), (key1979, -4), (key2207, -4), (key2216, 4)]

theorem rowCheck14188 : row14188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14188 := by decide +kernel

theorem rowEval14188 (x : Key → ℝ) : Integer.Sparse.eval row14188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14188, Integer.Sparse.eval_collectBalanced, rawRowCheck14188]

def rawRow14189 : Integer.Sparse Key := [(key1979, -2), (key1971, -2), (key1979, -2), (key1971, 6), (key2216, -2), (key2207, -2), (key2216, -2), (key1979, 2), (key1971, 2), (key2216, 2), (key1971, 2), (key2216, 2), (key1979, 2), (key1971, -2), (key2207, -2), (key1971, -2), (key2216, 6), (key1979, -2), (key2216, -2), (key1979, -2)]

theorem rawRowCheck14189 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form8 = rawRow14189 := by decide +kernel

def row14189 : Integer.Sparse Key := [(key1971, 4), (key1979, -4), (key2207, -4), (key2216, 4)]

theorem rowCheck14189 : row14189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14189 := by decide +kernel

theorem rowEval14189 (x : Key → ℝ) : Integer.Sparse.eval row14189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14189, Integer.Sparse.eval_collectBalanced, rawRowCheck14189]

def rawRow14190 : Integer.Sparse Key := [(key1979, -2), (key1979, -2), (key1971, -2), (key1971, 6), (key2216, -2), (key2216, -2), (key2207, -2), (key2216, 2), (key2216, 2), (key1979, 2), (key1979, 2), (key1971, 2), (key1971, 2), (key2207, -2), (key1971, -2), (key1971, -2), (key2216, 6), (key2216, -2), (key1979, -2), (key1979, -2)]

theorem rawRowCheck14190 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form8 = rawRow14190 := by decide +kernel

def row14190 : Integer.Sparse Key := [(key1971, 4), (key1979, -4), (key2207, -4), (key2216, 4)]

theorem rowCheck14190 : row14190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14190 := by decide +kernel

theorem rowEval14190 (x : Key → ℝ) : Integer.Sparse.eval row14190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14190, Integer.Sparse.eval_collectBalanced, rawRowCheck14190]

def rawRow14191 : Integer.Sparse Key := [(key2207, -2), (key2216, -2), (key2216, -2), (key2216, 6), (key1971, -2), (key1979, -2), (key1979, -2), (key1971, 2), (key1979, 2), (key1971, 2), (key2216, 2), (key1979, 2), (key2216, 2), (key1979, -2), (key1979, -2), (key2216, -2), (key1971, 6), (key1971, -2), (key1971, -2), (key2207, -2)]

theorem rawRowCheck14191 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form8 = rawRow14191 := by decide +kernel

def row14191 : Integer.Sparse Key := [(key1971, 4), (key1979, -4), (key2207, -4), (key2216, 4)]

theorem rowCheck14191 : row14191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14191 := by decide +kernel

theorem rowEval14191 (x : Key → ℝ) : Integer.Sparse.eval row14191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14191, Integer.Sparse.eval_collectBalanced, rawRowCheck14191]

def rawRow14192 : Integer.Sparse Key := [(key2216, -2), (key2207, -2), (key2216, -2), (key2216, 6), (key1979, -2), (key1971, -2), (key1979, -2), (key1979, 2), (key1971, 2), (key2216, 2), (key1971, 2), (key2216, 2), (key1979, 2), (key1979, -2), (key2216, -2), (key1979, -2), (key1971, 6), (key1971, -2), (key2207, -2), (key1971, -2)]

theorem rawRowCheck14192 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form8 = rawRow14192 := by decide +kernel

def row14192 : Integer.Sparse Key := [(key1971, 4), (key1979, -4), (key2207, -4), (key2216, 4)]

theorem rowCheck14192 : row14192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14192 := by decide +kernel

theorem rowEval14192 (x : Key → ℝ) : Integer.Sparse.eval row14192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14192, Integer.Sparse.eval_collectBalanced, rawRowCheck14192]

def rawRow14193 : Integer.Sparse Key := [(key2216, -2), (key2216, -2), (key2207, -2), (key2216, 6), (key1979, -2), (key1979, -2), (key1971, -2), (key2216, 2), (key2216, 2), (key1979, 2), (key1979, 2), (key1971, 2), (key1971, 2), (key2216, -2), (key1979, -2), (key1979, -2), (key1971, 6), (key2207, -2), (key1971, -2), (key1971, -2)]

theorem rawRowCheck14193 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form8 = rawRow14193 := by decide +kernel

def row14193 : Integer.Sparse Key := [(key1971, 4), (key1979, -4), (key2207, -4), (key2216, 4)]

theorem rowCheck14193 : row14193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14193 := by decide +kernel

theorem rowEval14193 (x : Key → ℝ) : Integer.Sparse.eval row14193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14193, Integer.Sparse.eval_collectBalanced, rawRowCheck14193]

def rawRow14194 : Integer.Sparse Key := [(key2216, -2), (key2216, -2), (key2216, -2), (key2207, 6), (key2216, -2), (key2216, -2), (key2216, -2), (key1979, 2), (key1979, 2), (key1979, 2), (key1979, 2), (key1979, 2), (key1979, 2), (key1971, -2), (key1971, -2), (key1971, -2), (key2207, 6), (key1971, -2), (key1971, -2), (key1971, -2)]

theorem rawRowCheck14194 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form8 = rawRow14194 := by decide +kernel

def row14194 : Integer.Sparse Key := [(key1971, -12), (key1979, 12), (key2207, 12), (key2216, -12)]

theorem rowCheck14194 : row14194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14194 := by decide +kernel

theorem rowEval14194 (x : Key → ℝ) : Integer.Sparse.eval row14194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14194, Integer.Sparse.eval_collectBalanced, rawRowCheck14194]

def rawRow14195 : Integer.Sparse Key := [(key756, 4), (key760, 4), (key760, 4), (key760, -4), (key760, -4), (key787, -4), (key760, -4), (key760, -4), (key787, -4), (key787, 12)]

theorem rawRowCheck14195 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form9 = rawRow14195 := by decide +kernel

def row14195 : Integer.Sparse Key := [(key756, 4), (key760, -8), (key787, 4)]

theorem rowCheck14195 : row14195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14195 := by decide +kernel

theorem rowEval14195 (x : Key → ℝ) : Integer.Sparse.eval row14195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14195, Integer.Sparse.eval_collectBalanced, rawRowCheck14195]

def rawRow14196 : Integer.Sparse Key := [(key760, 4), (key756, 4), (key760, 4), (key760, -4), (key787, -4), (key760, -4), (key760, -4), (key787, -4), (key760, -4), (key787, 12)]

theorem rawRowCheck14196 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form9 = rawRow14196 := by decide +kernel

def row14196 : Integer.Sparse Key := [(key756, 4), (key760, -8), (key787, 4)]

theorem rowCheck14196 : row14196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14196 := by decide +kernel

theorem rowEval14196 (x : Key → ℝ) : Integer.Sparse.eval row14196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14196, Integer.Sparse.eval_collectBalanced, rawRowCheck14196]

def rawRow14197 : Integer.Sparse Key := [(key760, 4), (key760, 4), (key756, 4), (key787, -4), (key760, -4), (key760, -4), (key787, -4), (key760, -4), (key760, -4), (key787, 12)]

theorem rawRowCheck14197 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form9 = rawRow14197 := by decide +kernel

def row14197 : Integer.Sparse Key := [(key756, 4), (key760, -8), (key787, 4)]

theorem rowCheck14197 : row14197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14197 := by decide +kernel

theorem rowEval14197 (x : Key → ℝ) : Integer.Sparse.eval row14197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14197, Integer.Sparse.eval_collectBalanced, rawRowCheck14197]

def rawRow14198 : Integer.Sparse Key := [(key760, 4), (key760, 4), (key787, 4), (key756, -4), (key760, -4), (key760, -4), (key760, -4), (key787, -4), (key787, -4), (key760, 12)]

theorem rawRowCheck14198 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form9 = rawRow14198 := by decide +kernel

def row14198 : Integer.Sparse Key := [(key756, -4), (key760, 8), (key787, -4)]

theorem rowCheck14198 : row14198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14198 := by decide +kernel

theorem rowEval14198 (x : Key → ℝ) : Integer.Sparse.eval row14198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14198, Integer.Sparse.eval_collectBalanced, rawRowCheck14198]

def rawRow14199 : Integer.Sparse Key := [(key760, 4), (key787, 4), (key760, 4), (key760, -4), (key756, -4), (key760, -4), (key787, -4), (key760, -4), (key787, -4), (key760, 12)]

theorem rawRowCheck14199 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form9 = rawRow14199 := by decide +kernel

def row14199 : Integer.Sparse Key := [(key756, -4), (key760, 8), (key787, -4)]

theorem rowCheck14199 : row14199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14199 := by decide +kernel

theorem rowEval14199 (x : Key → ℝ) : Integer.Sparse.eval row14199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14199, Integer.Sparse.eval_collectBalanced, rawRowCheck14199]

def rawRow14200 : Integer.Sparse Key := [(key787, 4), (key760, 4), (key760, 4), (key760, -4), (key760, -4), (key756, -4), (key787, -4), (key787, -4), (key760, -4), (key760, 12)]

theorem rawRowCheck14200 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form9 = rawRow14200 := by decide +kernel

def row14200 : Integer.Sparse Key := [(key756, -4), (key760, 8), (key787, -4)]

theorem rowCheck14200 : row14200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14200 := by decide +kernel

theorem rowEval14200 (x : Key → ℝ) : Integer.Sparse.eval row14200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14200, Integer.Sparse.eval_collectBalanced, rawRowCheck14200]

def rawRow14201 : Integer.Sparse Key := [(key760, 4), (key760, 4), (key787, 4), (key760, -4), (key787, -4), (key787, -4), (key756, -4), (key760, -4), (key760, -4), (key760, 12)]

theorem rawRowCheck14201 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form9 = rawRow14201 := by decide +kernel

def row14201 : Integer.Sparse Key := [(key756, -4), (key760, 8), (key787, -4)]

theorem rowCheck14201 : row14201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14201 := by decide +kernel

theorem rowEval14201 (x : Key → ℝ) : Integer.Sparse.eval row14201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14201, Integer.Sparse.eval_collectBalanced, rawRowCheck14201]

def rawRow14202 : Integer.Sparse Key := [(key760, 4), (key787, 4), (key760, 4), (key787, -4), (key760, -4), (key787, -4), (key760, -4), (key756, -4), (key760, -4), (key760, 12)]

theorem rawRowCheck14202 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form9 = rawRow14202 := by decide +kernel

def row14202 : Integer.Sparse Key := [(key756, -4), (key760, 8), (key787, -4)]

theorem rowCheck14202 : row14202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14202 := by decide +kernel

theorem rowEval14202 (x : Key → ℝ) : Integer.Sparse.eval row14202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14202, Integer.Sparse.eval_collectBalanced, rawRowCheck14202]

def rawRow14203 : Integer.Sparse Key := [(key787, 4), (key760, 4), (key760, 4), (key787, -4), (key787, -4), (key760, -4), (key760, -4), (key760, -4), (key756, -4), (key760, 12)]

theorem rawRowCheck14203 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form9 = rawRow14203 := by decide +kernel

def row14203 : Integer.Sparse Key := [(key756, -4), (key760, 8), (key787, -4)]

theorem rowCheck14203 : row14203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14203 := by decide +kernel

theorem rowEval14203 (x : Key → ℝ) : Integer.Sparse.eval row14203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14203, Integer.Sparse.eval_collectBalanced, rawRowCheck14203]

def rawRow14204 : Integer.Sparse Key := [(key787, 4), (key787, 4), (key787, 4), (key760, -4), (key760, -4), (key760, -4), (key760, -4), (key760, -4), (key760, -4), (key756, 12)]

theorem rawRowCheck14204 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form9 = rawRow14204 := by decide +kernel

def row14204 : Integer.Sparse Key := [(key756, 12), (key760, -24), (key787, 12)]

theorem rowCheck14204 : row14204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14204 := by decide +kernel

theorem rowEval14204 (x : Key → ℝ) : Integer.Sparse.eval row14204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14204, Integer.Sparse.eval_collectBalanced, rawRowCheck14204]

def rawRow14205 : Integer.Sparse Key := [(key2378, 4), (key2503, 4), (key2554, 4), (key2378, -2), (key2381, -2), (key2472, -2), (key2538, -2), (key2506, -2), (key2554, -2), (key2390, -2), (key2392, -2), (key2480, -2), (key2543, -2), (key2522, -2), (key2563, -2), (key2392, 4), (key2482, 4), (key2543, 4)]

theorem rawRowCheck14205 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form0 = rawRow14205 := by decide +kernel

def row14205 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck14205 : row14205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14205 := by decide +kernel

theorem rowEval14205 (x : Key → ℝ) : Integer.Sparse.eval row14205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14205, Integer.Sparse.eval_collectBalanced, rawRowCheck14205]

def rawRow14206 : Integer.Sparse Key := [(key2378, 4), (key2554, 4), (key2503, 4), (key2381, -2), (key2378, -2), (key2538, -2), (key2472, -2), (key2554, -2), (key2506, -2), (key2392, -2), (key2390, -2), (key2543, -2), (key2480, -2), (key2563, -2), (key2522, -2), (key2392, 4), (key2543, 4), (key2482, 4)]

theorem rawRowCheck14206 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form0 = rawRow14206 := by decide +kernel

def row14206 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck14206 : row14206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14206 := by decide +kernel

theorem rowEval14206 (x : Key → ℝ) : Integer.Sparse.eval row14206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14206, Integer.Sparse.eval_collectBalanced, rawRowCheck14206]

def rawRow14207 : Integer.Sparse Key := [(key2503, 4), (key2378, 4), (key2554, 4), (key2472, -2), (key2506, -2), (key2378, -2), (key2554, -2), (key2381, -2), (key2538, -2), (key2480, -2), (key2522, -2), (key2390, -2), (key2563, -2), (key2392, -2), (key2543, -2), (key2482, 4), (key2392, 4), (key2543, 4)]

theorem rawRowCheck14207 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form0 = rawRow14207 := by decide +kernel

def row14207 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck14207 : row14207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14207 := by decide +kernel

theorem rowEval14207 (x : Key → ℝ) : Integer.Sparse.eval row14207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14207, Integer.Sparse.eval_collectBalanced, rawRowCheck14207]

end MUB6.Certificate.GramRows

end OAI
