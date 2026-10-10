import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow5120 : Integer.Sparse Key := [(key1496, -2), (key1492, -2), (key1492, -2), (key1519, 6), (key1370, 2), (key1366, 2), (key1366, 2), (key1880, -2), (key1880, -2), (key1747, -2), (key1379, -6), (key1870, 2), (key1870, 2), (key1728, 2)]

theorem rawRowCheck5120 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form19 = rawRow5120 := by decide +kernel

def row5120 : Integer.Sparse Key := [(key1366, 4), (key1370, 2), (key1379, -6), (key1492, -4), (key1496, -2), (key1519, 6), (key1728, 2), (key1747, -2), (key1870, 4), (key1880, -4)]

theorem rowCheck5120 : row5120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5120 := by decide +kernel

theorem rowEval5120 (x : Key → ℝ) : Integer.Sparse.eval row5120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck5120, Integer.Sparse.eval_collectBalanced, rawRowCheck5120]

def rawRow5121 : Integer.Sparse Key := [(key1492, -2), (key1492, -2), (key1519, -2), (key1496, 6), (key1718, 2), (key1718, 2), (key1747, 2), (key1370, -2), (key1865, -2), (key1865, -2), (key1728, -6), (key1379, 2), (key1870, 2), (key1870, 2)]

theorem rawRowCheck5121 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form19 = rawRow5121 := by decide +kernel

def row5121 : Integer.Sparse Key := [(key1370, -2), (key1379, 2), (key1492, -4), (key1496, 6), (key1519, -2), (key1718, 4), (key1728, -6), (key1747, 2), (key1865, -4), (key1870, 4)]

theorem rowCheck5121 : row5121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5121 := by decide +kernel

theorem rowEval5121 (x : Key → ℝ) : Integer.Sparse.eval row5121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck5121, Integer.Sparse.eval_collectBalanced, rawRowCheck5121]

def rawRow5122 : Integer.Sparse Key := [(key1492, -2), (key1519, -2), (key1492, -2), (key1496, 6), (key1718, 2), (key1747, 2), (key1718, 2), (key1865, -2), (key1370, -2), (key1865, -2), (key1728, -6), (key1870, 2), (key1379, 2), (key1870, 2)]

theorem rawRowCheck5122 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form19 = rawRow5122 := by decide +kernel

def row5122 : Integer.Sparse Key := [(key1370, -2), (key1379, 2), (key1492, -4), (key1496, 6), (key1519, -2), (key1718, 4), (key1728, -6), (key1747, 2), (key1865, -4), (key1870, 4)]

theorem rowCheck5122 : row5122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5122 := by decide +kernel

theorem rowEval5122 (x : Key → ℝ) : Integer.Sparse.eval row5122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck5122, Integer.Sparse.eval_collectBalanced, rawRowCheck5122]

def rawRow5123 : Integer.Sparse Key := [(key1519, -2), (key1492, -2), (key1492, -2), (key1496, 6), (key1747, 2), (key1718, 2), (key1718, 2), (key1865, -2), (key1865, -2), (key1370, -2), (key1728, -6), (key1870, 2), (key1870, 2), (key1379, 2)]

theorem rawRowCheck5123 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form19 = rawRow5123 := by decide +kernel

def row5123 : Integer.Sparse Key := [(key1370, -2), (key1379, 2), (key1492, -4), (key1496, 6), (key1519, -2), (key1718, 4), (key1728, -6), (key1747, 2), (key1865, -4), (key1870, 4)]

theorem rowCheck5123 : row5123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5123 := by decide +kernel

theorem rowEval5123 (x : Key → ℝ) : Integer.Sparse.eval row5123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form19) x := by
  rw [rowCheck5123, Integer.Sparse.eval_collectBalanced, rawRowCheck5123]

def rawRow5124 : Integer.Sparse Key := [(key1718, -2), (key1718, -2), (key1728, -2), (key1747, 6), (key1366, 2), (key1366, 2), (key1379, 2), (key1519, -2), (key1880, -2), (key1880, -2), (key1370, -6), (key1496, 2), (key1865, 2), (key1865, 2)]

theorem rawRowCheck5124 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form19 = rawRow5124 := by decide +kernel

def row5124 : Integer.Sparse Key := [(key1366, 4), (key1370, -6), (key1379, 2), (key1496, 2), (key1519, -2), (key1718, -4), (key1728, -2), (key1747, 6), (key1865, 4), (key1880, -4)]

theorem rowCheck5124 : row5124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5124 := by decide +kernel

theorem rowEval5124 (x : Key → ℝ) : Integer.Sparse.eval row5124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck5124, Integer.Sparse.eval_collectBalanced, rawRowCheck5124]

def rawRow5125 : Integer.Sparse Key := [(key1718, -2), (key1728, -2), (key1718, -2), (key1747, 6), (key1366, 2), (key1379, 2), (key1366, 2), (key1880, -2), (key1519, -2), (key1880, -2), (key1370, -6), (key1865, 2), (key1496, 2), (key1865, 2)]

theorem rawRowCheck5125 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form19 = rawRow5125 := by decide +kernel

def row5125 : Integer.Sparse Key := [(key1366, 4), (key1370, -6), (key1379, 2), (key1496, 2), (key1519, -2), (key1718, -4), (key1728, -2), (key1747, 6), (key1865, 4), (key1880, -4)]

theorem rowCheck5125 : row5125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5125 := by decide +kernel

theorem rowEval5125 (x : Key → ℝ) : Integer.Sparse.eval row5125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck5125, Integer.Sparse.eval_collectBalanced, rawRowCheck5125]

def rawRow5126 : Integer.Sparse Key := [(key1728, -2), (key1718, -2), (key1718, -2), (key1747, 6), (key1379, 2), (key1366, 2), (key1366, 2), (key1880, -2), (key1880, -2), (key1519, -2), (key1370, -6), (key1865, 2), (key1865, 2), (key1496, 2)]

theorem rawRowCheck5126 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form19 = rawRow5126 := by decide +kernel

def row5126 : Integer.Sparse Key := [(key1366, 4), (key1370, -6), (key1379, 2), (key1496, 2), (key1519, -2), (key1718, -4), (key1728, -2), (key1747, 6), (key1865, 4), (key1880, -4)]

theorem rowCheck5126 : row5126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5126 := by decide +kernel

theorem rowEval5126 (x : Key → ℝ) : Integer.Sparse.eval row5126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form19) x := by
  rw [rowCheck5126, Integer.Sparse.eval_collectBalanced, rawRowCheck5126]

def rawRow5127 : Integer.Sparse Key := [(key1718, -2), (key1718, -2), (key1747, -2), (key1728, 6), (key1492, 2), (key1492, 2), (key1519, 2), (key1379, -2), (key1870, -2), (key1870, -2), (key1496, -6), (key1370, 2), (key1865, 2), (key1865, 2)]

theorem rawRowCheck5127 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form19 = rawRow5127 := by decide +kernel

def row5127 : Integer.Sparse Key := [(key1370, 2), (key1379, -2), (key1492, 4), (key1496, -6), (key1519, 2), (key1718, -4), (key1728, 6), (key1747, -2), (key1865, 4), (key1870, -4)]

theorem rowCheck5127 : row5127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5127 := by decide +kernel

theorem rowEval5127 (x : Key → ℝ) : Integer.Sparse.eval row5127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck5127, Integer.Sparse.eval_collectBalanced, rawRowCheck5127]

def rawRow5128 : Integer.Sparse Key := [(key1718, -2), (key1747, -2), (key1718, -2), (key1728, 6), (key1492, 2), (key1519, 2), (key1492, 2), (key1870, -2), (key1379, -2), (key1870, -2), (key1496, -6), (key1865, 2), (key1370, 2), (key1865, 2)]

theorem rawRowCheck5128 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form19 = rawRow5128 := by decide +kernel

def row5128 : Integer.Sparse Key := [(key1370, 2), (key1379, -2), (key1492, 4), (key1496, -6), (key1519, 2), (key1718, -4), (key1728, 6), (key1747, -2), (key1865, 4), (key1870, -4)]

theorem rowCheck5128 : row5128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5128 := by decide +kernel

theorem rowEval5128 (x : Key → ℝ) : Integer.Sparse.eval row5128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck5128, Integer.Sparse.eval_collectBalanced, rawRowCheck5128]

def rawRow5129 : Integer.Sparse Key := [(key1747, -2), (key1718, -2), (key1718, -2), (key1728, 6), (key1519, 2), (key1492, 2), (key1492, 2), (key1870, -2), (key1870, -2), (key1379, -2), (key1496, -6), (key1865, 2), (key1865, 2), (key1370, 2)]

theorem rawRowCheck5129 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form19 = rawRow5129 := by decide +kernel

def row5129 : Integer.Sparse Key := [(key1370, 2), (key1379, -2), (key1492, 4), (key1496, -6), (key1519, 2), (key1718, -4), (key1728, 6), (key1747, -2), (key1865, 4), (key1870, -4)]

theorem rowCheck5129 : row5129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5129 := by decide +kernel

theorem rowEval5129 (x : Key → ℝ) : Integer.Sparse.eval row5129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form19) x := by
  rw [rowCheck5129, Integer.Sparse.eval_collectBalanced, rawRowCheck5129]

def rawRow5130 : Integer.Sparse Key := [(key2617, -2), (key2620, -2), (key2620, -2), (key2633, 2), (key2643, 2), (key2643, 2), (key2672, 2), (key2675, 2), (key2675, 2), (key2707, -2), (key2730, -2), (key2730, -2), (key2787, -2), (key2797, -2), (key2797, -2), (key2810, 2), (key2833, 2), (key2833, 2)]

theorem rawRowCheck5130 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form20 = rawRow5130 := by decide +kernel

def row5130 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2672, 2), (key2675, 4), (key2707, -2), (key2730, -4), (key2787, -2), (key2797, -4), (key2810, 2), (key2833, 4)]

theorem rowCheck5130 : row5130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5130 := by decide +kernel

theorem rowEval5130 (x : Key → ℝ) : Integer.Sparse.eval row5130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form20) x := by
  rw [rowCheck5130, Integer.Sparse.eval_collectBalanced, rawRowCheck5130]

def rawRow5131 : Integer.Sparse Key := [(key2620, -2), (key2617, -2), (key2620, -2), (key2643, 2), (key2633, 2), (key2643, 2), (key2675, 2), (key2672, 2), (key2675, 2), (key2730, -2), (key2707, -2), (key2730, -2), (key2797, -2), (key2787, -2), (key2797, -2), (key2833, 2), (key2810, 2), (key2833, 2)]

theorem rawRowCheck5131 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form20 = rawRow5131 := by decide +kernel

def row5131 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2672, 2), (key2675, 4), (key2707, -2), (key2730, -4), (key2787, -2), (key2797, -4), (key2810, 2), (key2833, 4)]

theorem rowCheck5131 : row5131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5131 := by decide +kernel

theorem rowEval5131 (x : Key → ℝ) : Integer.Sparse.eval row5131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form20) x := by
  rw [rowCheck5131, Integer.Sparse.eval_collectBalanced, rawRowCheck5131]

def rawRow5132 : Integer.Sparse Key := [(key2620, -2), (key2620, -2), (key2617, -2), (key2643, 2), (key2643, 2), (key2633, 2), (key2675, 2), (key2675, 2), (key2672, 2), (key2730, -2), (key2730, -2), (key2707, -2), (key2797, -2), (key2797, -2), (key2787, -2), (key2833, 2), (key2833, 2), (key2810, 2)]

theorem rawRowCheck5132 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form20 = rawRow5132 := by decide +kernel

def row5132 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2672, 2), (key2675, 4), (key2707, -2), (key2730, -4), (key2787, -2), (key2797, -4), (key2810, 2), (key2833, 4)]

theorem rowCheck5132 : row5132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5132 := by decide +kernel

theorem rowEval5132 (x : Key → ℝ) : Integer.Sparse.eval row5132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form20) x := by
  rw [rowCheck5132, Integer.Sparse.eval_collectBalanced, rawRowCheck5132]

def rawRow5133 : Integer.Sparse Key := [(key2633, -2), (key2643, -2), (key2643, -2), (key2617, 2), (key2655, 2), (key2655, 2), (key2707, 2), (key2739, 2), (key2739, 2), (key2672, -2), (key2749, -2), (key2749, -2), (key2810, -2), (key2899, -2), (key2899, -2), (key2787, 2), (key2906, 2), (key2906, 2)]

theorem rawRowCheck5133 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form20 = rawRow5133 := by decide +kernel

def row5133 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, -2), (key2707, 2), (key2739, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2899, -4), (key2906, 4)]

theorem rowCheck5133 : row5133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5133 := by decide +kernel

theorem rowEval5133 (x : Key → ℝ) : Integer.Sparse.eval row5133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form20) x := by
  rw [rowCheck5133, Integer.Sparse.eval_collectBalanced, rawRowCheck5133]

def rawRow5134 : Integer.Sparse Key := [(key2643, -2), (key2633, -2), (key2643, -2), (key2655, 2), (key2617, 2), (key2655, 2), (key2739, 2), (key2707, 2), (key2739, 2), (key2749, -2), (key2672, -2), (key2749, -2), (key2899, -2), (key2810, -2), (key2899, -2), (key2906, 2), (key2787, 2), (key2906, 2)]

theorem rawRowCheck5134 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form20 = rawRow5134 := by decide +kernel

def row5134 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, -2), (key2707, 2), (key2739, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2899, -4), (key2906, 4)]

theorem rowCheck5134 : row5134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5134 := by decide +kernel

theorem rowEval5134 (x : Key → ℝ) : Integer.Sparse.eval row5134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form20) x := by
  rw [rowCheck5134, Integer.Sparse.eval_collectBalanced, rawRowCheck5134]

def rawRow5135 : Integer.Sparse Key := [(key2643, -2), (key2643, -2), (key2633, -2), (key2655, 2), (key2655, 2), (key2617, 2), (key2739, 2), (key2739, 2), (key2707, 2), (key2749, -2), (key2749, -2), (key2672, -2), (key2899, -2), (key2899, -2), (key2810, -2), (key2906, 2), (key2906, 2), (key2787, 2)]

theorem rawRowCheck5135 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form20 = rawRow5135 := by decide +kernel

def row5135 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, -2), (key2707, 2), (key2739, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2899, -4), (key2906, 4)]

theorem rowCheck5135 : row5135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5135 := by decide +kernel

theorem rowEval5135 (x : Key → ℝ) : Integer.Sparse.eval row5135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form20) x := by
  rw [rowCheck5135, Integer.Sparse.eval_collectBalanced, rawRowCheck5135]

def rawRow5136 : Integer.Sparse Key := [(key2672, -2), (key2675, -2), (key2675, -2), (key2707, 2), (key2739, 2), (key2739, 2), (key2617, 2), (key2620, 2), (key2620, 2), (key2810, -2), (key2833, -2), (key2833, -2), (key2633, -2), (key2643, -2), (key2643, -2), (key2707, 2), (key2730, 2), (key2730, 2)]

theorem rawRowCheck5136 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form20 = rawRow5136 := by decide +kernel

def row5136 : Integer.Sparse Key := [(key2617, 2), (key2620, 4), (key2633, -2), (key2643, -4), (key2672, -2), (key2675, -4), (key2707, 4), (key2730, 4), (key2739, 4), (key2810, -2), (key2833, -4)]

theorem rowCheck5136 : row5136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5136 := by decide +kernel

theorem rowEval5136 (x : Key → ℝ) : Integer.Sparse.eval row5136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form20) x := by
  rw [rowCheck5136, Integer.Sparse.eval_collectBalanced, rawRowCheck5136]

def rawRow5137 : Integer.Sparse Key := [(key2675, -2), (key2672, -2), (key2675, -2), (key2739, 2), (key2707, 2), (key2739, 2), (key2620, 2), (key2617, 2), (key2620, 2), (key2833, -2), (key2810, -2), (key2833, -2), (key2643, -2), (key2633, -2), (key2643, -2), (key2730, 2), (key2707, 2), (key2730, 2)]

theorem rawRowCheck5137 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form20 = rawRow5137 := by decide +kernel

def row5137 : Integer.Sparse Key := [(key2617, 2), (key2620, 4), (key2633, -2), (key2643, -4), (key2672, -2), (key2675, -4), (key2707, 4), (key2730, 4), (key2739, 4), (key2810, -2), (key2833, -4)]

theorem rowCheck5137 : row5137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5137 := by decide +kernel

theorem rowEval5137 (x : Key → ℝ) : Integer.Sparse.eval row5137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form20) x := by
  rw [rowCheck5137, Integer.Sparse.eval_collectBalanced, rawRowCheck5137]

def rawRow5138 : Integer.Sparse Key := [(key2675, -2), (key2675, -2), (key2672, -2), (key2739, 2), (key2739, 2), (key2707, 2), (key2620, 2), (key2620, 2), (key2617, 2), (key2833, -2), (key2833, -2), (key2810, -2), (key2643, -2), (key2643, -2), (key2633, -2), (key2730, 2), (key2730, 2), (key2707, 2)]

theorem rawRowCheck5138 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form20 = rawRow5138 := by decide +kernel

def row5138 : Integer.Sparse Key := [(key2617, 2), (key2620, 4), (key2633, -2), (key2643, -4), (key2672, -2), (key2675, -4), (key2707, 4), (key2730, 4), (key2739, 4), (key2810, -2), (key2833, -4)]

theorem rowCheck5138 : row5138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5138 := by decide +kernel

theorem rowEval5138 (x : Key → ℝ) : Integer.Sparse.eval row5138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form20) x := by
  rw [rowCheck5138, Integer.Sparse.eval_collectBalanced, rawRowCheck5138]

def rawRow5139 : Integer.Sparse Key := [(key2707, -2), (key2730, -2), (key2730, -2), (key2672, 2), (key2749, 2), (key2749, 2), (key2810, 2), (key2833, 2), (key2833, 2), (key2617, -2), (key2962, -2), (key2962, -2), (key2707, -2), (key2978, -2), (key2978, -2), (key2633, 2), (key2985, 2), (key2985, 2)]

theorem rawRowCheck5139 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form20 = rawRow5139 := by decide +kernel

def row5139 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2672, 2), (key2707, -4), (key2730, -4), (key2749, 4), (key2810, 2), (key2833, 4), (key2962, -4), (key2978, -4), (key2985, 4)]

theorem rowCheck5139 : row5139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5139 := by decide +kernel

theorem rowEval5139 (x : Key → ℝ) : Integer.Sparse.eval row5139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form20) x := by
  rw [rowCheck5139, Integer.Sparse.eval_collectBalanced, rawRowCheck5139]

def rawRow5140 : Integer.Sparse Key := [(key2730, -2), (key2707, -2), (key2730, -2), (key2749, 2), (key2672, 2), (key2749, 2), (key2833, 2), (key2810, 2), (key2833, 2), (key2962, -2), (key2617, -2), (key2962, -2), (key2978, -2), (key2707, -2), (key2978, -2), (key2985, 2), (key2633, 2), (key2985, 2)]

theorem rawRowCheck5140 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form20 = rawRow5140 := by decide +kernel

def row5140 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2672, 2), (key2707, -4), (key2730, -4), (key2749, 4), (key2810, 2), (key2833, 4), (key2962, -4), (key2978, -4), (key2985, 4)]

theorem rowCheck5140 : row5140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5140 := by decide +kernel

theorem rowEval5140 (x : Key → ℝ) : Integer.Sparse.eval row5140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form20) x := by
  rw [rowCheck5140, Integer.Sparse.eval_collectBalanced, rawRowCheck5140]

def rawRow5141 : Integer.Sparse Key := [(key2730, -2), (key2730, -2), (key2707, -2), (key2749, 2), (key2749, 2), (key2672, 2), (key2833, 2), (key2833, 2), (key2810, 2), (key2962, -2), (key2962, -2), (key2617, -2), (key2978, -2), (key2978, -2), (key2707, -2), (key2985, 2), (key2985, 2), (key2633, 2)]

theorem rawRowCheck5141 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form20 = rawRow5141 := by decide +kernel

def row5141 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2672, 2), (key2707, -4), (key2730, -4), (key2749, 4), (key2810, 2), (key2833, 4), (key2962, -4), (key2978, -4), (key2985, 4)]

theorem rowCheck5141 : row5141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5141 := by decide +kernel

theorem rowEval5141 (x : Key → ℝ) : Integer.Sparse.eval row5141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form20) x := by
  rw [rowCheck5141, Integer.Sparse.eval_collectBalanced, rawRowCheck5141]

def rawRow5142 : Integer.Sparse Key := [(key2787, -2), (key2797, -2), (key2797, -2), (key2810, 2), (key2899, 2), (key2899, 2), (key2633, 2), (key2643, 2), (key2643, 2), (key2707, -2), (key2978, -2), (key2978, -2), (key2617, -2), (key2655, -2), (key2655, -2), (key2672, 2), (key2749, 2), (key2749, 2)]

theorem rawRowCheck5142 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form20 = rawRow5142 := by decide +kernel

def row5142 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2643, 4), (key2655, -4), (key2672, 2), (key2707, -2), (key2749, 4), (key2787, -2), (key2797, -4), (key2810, 2), (key2899, 4), (key2978, -4)]

theorem rowCheck5142 : row5142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5142 := by decide +kernel

theorem rowEval5142 (x : Key → ℝ) : Integer.Sparse.eval row5142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form20) x := by
  rw [rowCheck5142, Integer.Sparse.eval_collectBalanced, rawRowCheck5142]

def rawRow5143 : Integer.Sparse Key := [(key2797, -2), (key2787, -2), (key2797, -2), (key2899, 2), (key2810, 2), (key2899, 2), (key2643, 2), (key2633, 2), (key2643, 2), (key2978, -2), (key2707, -2), (key2978, -2), (key2655, -2), (key2617, -2), (key2655, -2), (key2749, 2), (key2672, 2), (key2749, 2)]

theorem rawRowCheck5143 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form20 = rawRow5143 := by decide +kernel

def row5143 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2643, 4), (key2655, -4), (key2672, 2), (key2707, -2), (key2749, 4), (key2787, -2), (key2797, -4), (key2810, 2), (key2899, 4), (key2978, -4)]

theorem rowCheck5143 : row5143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5143 := by decide +kernel

theorem rowEval5143 (x : Key → ℝ) : Integer.Sparse.eval row5143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form20) x := by
  rw [rowCheck5143, Integer.Sparse.eval_collectBalanced, rawRowCheck5143]

def rawRow5144 : Integer.Sparse Key := [(key2797, -2), (key2797, -2), (key2787, -2), (key2899, 2), (key2899, 2), (key2810, 2), (key2643, 2), (key2643, 2), (key2633, 2), (key2978, -2), (key2978, -2), (key2707, -2), (key2655, -2), (key2655, -2), (key2617, -2), (key2749, 2), (key2749, 2), (key2672, 2)]

theorem rawRowCheck5144 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form20 = rawRow5144 := by decide +kernel

def row5144 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2643, 4), (key2655, -4), (key2672, 2), (key2707, -2), (key2749, 4), (key2787, -2), (key2797, -4), (key2810, 2), (key2899, 4), (key2978, -4)]

theorem rowCheck5144 : row5144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5144 := by decide +kernel

theorem rowEval5144 (x : Key → ℝ) : Integer.Sparse.eval row5144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form20) x := by
  rw [rowCheck5144, Integer.Sparse.eval_collectBalanced, rawRowCheck5144]

def rawRow5145 : Integer.Sparse Key := [(key2810, -2), (key2833, -2), (key2833, -2), (key2787, 2), (key2906, 2), (key2906, 2), (key2707, 2), (key2730, 2), (key2730, 2), (key2633, -2), (key2985, -2), (key2985, -2), (key2672, -2), (key2749, -2), (key2749, -2), (key2617, 2), (key2962, 2), (key2962, 2)]

theorem rawRowCheck5145 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form20 = rawRow5145 := by decide +kernel

def row5145 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2672, -2), (key2707, 2), (key2730, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2833, -4), (key2906, 4), (key2962, 4), (key2985, -4)]

theorem rowCheck5145 : row5145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5145 := by decide +kernel

theorem rowEval5145 (x : Key → ℝ) : Integer.Sparse.eval row5145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form20) x := by
  rw [rowCheck5145, Integer.Sparse.eval_collectBalanced, rawRowCheck5145]

def rawRow5146 : Integer.Sparse Key := [(key2833, -2), (key2810, -2), (key2833, -2), (key2906, 2), (key2787, 2), (key2906, 2), (key2730, 2), (key2707, 2), (key2730, 2), (key2985, -2), (key2633, -2), (key2985, -2), (key2749, -2), (key2672, -2), (key2749, -2), (key2962, 2), (key2617, 2), (key2962, 2)]

theorem rawRowCheck5146 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form20 = rawRow5146 := by decide +kernel

def row5146 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2672, -2), (key2707, 2), (key2730, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2833, -4), (key2906, 4), (key2962, 4), (key2985, -4)]

theorem rowCheck5146 : row5146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5146 := by decide +kernel

theorem rowEval5146 (x : Key → ℝ) : Integer.Sparse.eval row5146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form20) x := by
  rw [rowCheck5146, Integer.Sparse.eval_collectBalanced, rawRowCheck5146]

def rawRow5147 : Integer.Sparse Key := [(key2833, -2), (key2833, -2), (key2810, -2), (key2906, 2), (key2906, 2), (key2787, 2), (key2730, 2), (key2730, 2), (key2707, 2), (key2985, -2), (key2985, -2), (key2633, -2), (key2749, -2), (key2749, -2), (key2672, -2), (key2962, 2), (key2962, 2), (key2617, 2)]

theorem rawRowCheck5147 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form20 = rawRow5147 := by decide +kernel

def row5147 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2672, -2), (key2707, 2), (key2730, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2833, -4), (key2906, 4), (key2962, 4), (key2985, -4)]

theorem rowCheck5147 : row5147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5147 := by decide +kernel

theorem rowEval5147 (x : Key → ℝ) : Integer.Sparse.eval row5147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form20) x := by
  rw [rowCheck5147, Integer.Sparse.eval_collectBalanced, rawRowCheck5147]

def rawRow5148 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2614, 2), (key2624, -1), (key2630, -1), (key2624, 2), (key2638, 2), (key2630, -1), (key2638, -1), (key2657, 2), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2669, -2), (key2698, 1), (key2704, 1), (key2698, -2), (key2724, -2), (key2704, 1), (key2724, 1), (key2752, -2), (key2752, 1), (key2757, 1), (key2778, -1), (key2792, -1), (key2784, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2807, -1), (key2827, -1), (key2851, -1), (key2858, -1), (key2851, 1), (key2868, 1), (key2918, 1), (key2919, 1), (key2918, -1), (key2922, -1)]

theorem rawRowCheck5148 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block2.form0 = rawRow5148 := by decide +kernel

def row5148 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

theorem rowCheck5148 : row5148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5148 := by decide +kernel

theorem rowEval5148 (x : Key → ℝ) : Integer.Sparse.eval row5148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5148, Integer.Sparse.eval_collectBalanced, rawRowCheck5148]

def rawRow5149 : Integer.Sparse Key := [(key2614, -1), (key2608, -1), (key2614, 2), (key2630, -1), (key2624, -1), (key2638, 2), (key2624, 2), (key2638, -1), (key2630, -1), (key2657, 2), (key2659, -1), (key2657, -1), (key2669, 1), (key2663, 1), (key2669, -2), (key2704, 1), (key2698, 1), (key2724, -2), (key2698, -2), (key2724, 1), (key2704, 1), (key2752, -2), (key2757, 1), (key2752, 1), (key2792, -1), (key2778, -1), (key2792, 1), (key2784, 1), (key2827, 1), (key2801, 1), (key2827, -1), (key2807, -1), (key2858, -1), (key2851, -1), (key2868, 1), (key2851, 1), (key2919, 1), (key2918, 1), (key2922, -1), (key2918, -1)]

theorem rawRowCheck5149 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block2.form0 = rawRow5149 := by decide +kernel

def row5149 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

theorem rowCheck5149 : row5149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5149 := by decide +kernel

theorem rowEval5149 (x : Key → ℝ) : Integer.Sparse.eval row5149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5149, Integer.Sparse.eval_collectBalanced, rawRowCheck5149]

def rawRow5150 : Integer.Sparse Key := [(key2614, -1), (key2614, -1), (key2608, 2), (key2638, -1), (key2638, -1), (key2630, 2), (key2630, 2), (key2624, -1), (key2624, -1), (key2659, 2), (key2657, -1), (key2657, -1), (key2669, 1), (key2669, 1), (key2663, -2), (key2724, 1), (key2724, 1), (key2704, -2), (key2704, -2), (key2698, 1), (key2698, 1), (key2757, -2), (key2752, 1), (key2752, 1), (key2784, -1), (key2784, -1), (key2778, 1), (key2778, 1), (key2807, 1), (key2807, 1), (key2801, -1), (key2801, -1), (key2868, -1), (key2868, -1), (key2858, 1), (key2858, 1), (key2922, 1), (key2922, 1), (key2919, -1), (key2919, -1)]

theorem rawRowCheck5150 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block2.form0 = rawRow5150 := by decide +kernel

def row5150 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2663, -2), (key2669, 2), (key2698, 2), (key2704, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, 2), (key2784, -2), (key2801, -2), (key2807, 2), (key2858, 2), (key2868, -2), (key2919, -2), (key2922, 2)]

theorem rowCheck5150 : row5150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5150 := by decide +kernel

theorem rowEval5150 (x : Key → ℝ) : Integer.Sparse.eval row5150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5150, Integer.Sparse.eval_collectBalanced, rawRowCheck5150]

def rawRow5151 : Integer.Sparse Key := [(key2624, -1), (key2630, -1), (key2638, 2), (key2608, -1), (key2614, -1), (key2624, 2), (key2638, 2), (key2657, -1), (key2659, -1), (key2614, 2), (key2630, -1), (key2638, -1), (key2698, 1), (key2704, 1), (key2752, -2), (key2663, 1), (key2669, 1), (key2698, -2), (key2724, -2), (key2752, 1), (key2757, 1), (key2669, -2), (key2704, 1), (key2724, 1), (key2851, -1), (key2858, -1), (key2918, 1), (key2919, 1), (key2851, 1), (key2868, 1), (key2918, -1), (key2922, -1), (key2778, -1), (key2792, -1), (key2801, 1), (key2827, 1), (key2784, 1), (key2792, 1), (key2807, -1), (key2827, -1)]

theorem rawRowCheck5151 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block2.form0 = rawRow5151 := by decide +kernel

def row5151 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

theorem rowCheck5151 : row5151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5151 := by decide +kernel

theorem rowEval5151 (x : Key → ℝ) : Integer.Sparse.eval row5151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5151, Integer.Sparse.eval_collectBalanced, rawRowCheck5151]

def rawRow5152 : Integer.Sparse Key := [(key2630, -1), (key2624, -1), (key2638, 2), (key2614, -1), (key2608, -1), (key2638, 2), (key2624, 2), (key2659, -1), (key2657, -1), (key2614, 2), (key2638, -1), (key2630, -1), (key2704, 1), (key2698, 1), (key2752, -2), (key2669, 1), (key2663, 1), (key2724, -2), (key2698, -2), (key2757, 1), (key2752, 1), (key2669, -2), (key2724, 1), (key2704, 1), (key2858, -1), (key2851, -1), (key2919, 1), (key2918, 1), (key2868, 1), (key2851, 1), (key2922, -1), (key2918, -1), (key2792, -1), (key2778, -1), (key2827, 1), (key2801, 1), (key2792, 1), (key2784, 1), (key2827, -1), (key2807, -1)]

theorem rawRowCheck5152 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block2.form0 = rawRow5152 := by decide +kernel

def row5152 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

theorem rowCheck5152 : row5152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5152 := by decide +kernel

theorem rowEval5152 (x : Key → ℝ) : Integer.Sparse.eval row5152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5152, Integer.Sparse.eval_collectBalanced, rawRowCheck5152]

def rawRow5153 : Integer.Sparse Key := [(key2624, -1), (key2638, -1), (key2630, 2), (key2624, -1), (key2638, -1), (key2608, 2), (key2659, 2), (key2614, -1), (key2638, -1), (key2630, 2), (key2614, -1), (key2638, -1), (key2698, 1), (key2752, 1), (key2704, -2), (key2698, 1), (key2752, 1), (key2663, -2), (key2757, -2), (key2669, 1), (key2724, 1), (key2704, -2), (key2669, 1), (key2724, 1), (key2801, -1), (key2919, -1), (key2807, 1), (key2858, 1), (key2778, 1), (key2922, 1), (key2784, -1), (key2868, -1), (key2801, -1), (key2919, -1), (key2778, 1), (key2922, 1), (key2807, 1), (key2858, 1), (key2784, -1), (key2868, -1)]

theorem rawRowCheck5153 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block2.form0 = rawRow5153 := by decide +kernel

def row5153 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, -2), (key2669, 2), (key2698, 2), (key2704, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, 2), (key2784, -2), (key2801, -2), (key2807, 2), (key2858, 2), (key2868, -2), (key2919, -2), (key2922, 2)]

theorem rowCheck5153 : row5153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5153 := by decide +kernel

theorem rowEval5153 (x : Key → ℝ) : Integer.Sparse.eval row5153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5153, Integer.Sparse.eval_collectBalanced, rawRowCheck5153]

def rawRow5154 : Integer.Sparse Key := [(key2638, -1), (key2624, -1), (key2630, 2), (key2638, -1), (key2624, -1), (key2659, 2), (key2608, 2), (key2638, -1), (key2614, -1), (key2630, 2), (key2638, -1), (key2614, -1), (key2752, 1), (key2698, 1), (key2704, -2), (key2752, 1), (key2698, 1), (key2757, -2), (key2663, -2), (key2724, 1), (key2669, 1), (key2704, -2), (key2724, 1), (key2669, 1), (key2919, -1), (key2801, -1), (key2858, 1), (key2807, 1), (key2922, 1), (key2778, 1), (key2868, -1), (key2784, -1), (key2919, -1), (key2801, -1), (key2922, 1), (key2778, 1), (key2858, 1), (key2807, 1), (key2868, -1), (key2784, -1)]

theorem rawRowCheck5154 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block2.form0 = rawRow5154 := by decide +kernel

def row5154 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, -2), (key2669, 2), (key2698, 2), (key2704, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, 2), (key2784, -2), (key2801, -2), (key2807, 2), (key2858, 2), (key2868, -2), (key2919, -2), (key2922, 2)]

theorem rowCheck5154 : row5154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5154 := by decide +kernel

theorem rowEval5154 (x : Key → ℝ) : Integer.Sparse.eval row5154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5154, Integer.Sparse.eval_collectBalanced, rawRowCheck5154]

def rawRow5155 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2624, 2), (key2657, -1), (key2659, -1), (key2614, 2), (key2638, 2), (key2608, -1), (key2624, -1), (key2638, 2), (key2614, -1), (key2630, -1), (key2704, 1), (key2752, 1), (key2698, -2), (key2724, 1), (key2757, 1), (key2669, -2), (key2752, -2), (key2663, 1), (key2698, 1), (key2724, -2), (key2669, 1), (key2704, 1), (key2807, -1), (key2918, -1), (key2801, 1), (key2851, 1), (key2784, 1), (key2918, 1), (key2778, -1), (key2851, -1), (key2827, -1), (key2922, -1), (key2792, 1), (key2919, 1), (key2827, 1), (key2868, 1), (key2792, -1), (key2858, -1)]

theorem rawRowCheck5155 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block2.form0 = rawRow5155 := by decide +kernel

def row5155 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

theorem rowCheck5155 : row5155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5155 := by decide +kernel

theorem rowEval5155 (x : Key → ℝ) : Integer.Sparse.eval row5155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5155, Integer.Sparse.eval_collectBalanced, rawRowCheck5155]

def rawRow5156 : Integer.Sparse Key := [(key2638, -1), (key2630, -1), (key2624, 2), (key2659, -1), (key2657, -1), (key2638, 2), (key2614, 2), (key2624, -1), (key2608, -1), (key2638, 2), (key2630, -1), (key2614, -1), (key2752, 1), (key2704, 1), (key2698, -2), (key2757, 1), (key2724, 1), (key2752, -2), (key2669, -2), (key2698, 1), (key2663, 1), (key2724, -2), (key2704, 1), (key2669, 1), (key2918, -1), (key2807, -1), (key2851, 1), (key2801, 1), (key2918, 1), (key2784, 1), (key2851, -1), (key2778, -1), (key2922, -1), (key2827, -1), (key2919, 1), (key2792, 1), (key2868, 1), (key2827, 1), (key2858, -1), (key2792, -1)]

theorem rawRowCheck5156 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block2.form0 = rawRow5156 := by decide +kernel

def row5156 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

theorem rowCheck5156 : row5156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5156 := by decide +kernel

theorem rowEval5156 (x : Key → ℝ) : Integer.Sparse.eval row5156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5156, Integer.Sparse.eval_collectBalanced, rawRowCheck5156]

def rawRow5157 : Integer.Sparse Key := [(key2657, -1), (key2657, -1), (key2659, 2), (key2614, -1), (key2614, -1), (key2630, 2), (key2630, 2), (key2638, -1), (key2638, -1), (key2608, 2), (key2624, -1), (key2624, -1), (key2724, 1), (key2724, 1), (key2757, -2), (key2669, 1), (key2669, 1), (key2704, -2), (key2704, -2), (key2752, 1), (key2752, 1), (key2663, -2), (key2698, 1), (key2698, 1), (key2868, -1), (key2868, -1), (key2922, 1), (key2922, 1), (key2858, 1), (key2858, 1), (key2919, -1), (key2919, -1), (key2784, -1), (key2784, -1), (key2807, 1), (key2807, 1), (key2778, 1), (key2778, 1), (key2801, -1), (key2801, -1)]

theorem rawRowCheck5157 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block2.form0 = rawRow5157 := by decide +kernel

def row5157 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2663, -2), (key2669, 2), (key2698, 2), (key2704, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, 2), (key2784, -2), (key2801, -2), (key2807, 2), (key2858, 2), (key2868, -2), (key2919, -2), (key2922, 2)]

theorem rowCheck5157 : row5157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5157 := by decide +kernel

theorem rowEval5157 (x : Key → ℝ) : Integer.Sparse.eval row5157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5157, Integer.Sparse.eval_collectBalanced, rawRowCheck5157]

def rawRow5158 : Integer.Sparse Key := [(key2657, -1), (key2659, -1), (key2657, 2), (key2630, -1), (key2638, -1), (key2614, 2), (key2638, 2), (key2614, -1), (key2630, -1), (key2624, 2), (key2608, -1), (key2624, -1), (key2724, 1), (key2757, 1), (key2724, -2), (key2704, 1), (key2752, 1), (key2669, -2), (key2752, -2), (key2669, 1), (key2704, 1), (key2698, -2), (key2663, 1), (key2698, 1), (key2827, -1), (key2922, -1), (key2827, 1), (key2868, 1), (key2792, 1), (key2919, 1), (key2792, -1), (key2858, -1), (key2807, -1), (key2918, -1), (key2784, 1), (key2918, 1), (key2801, 1), (key2851, 1), (key2778, -1), (key2851, -1)]

theorem rawRowCheck5158 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block2.form0 = rawRow5158 := by decide +kernel

def row5158 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

theorem rowCheck5158 : row5158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5158 := by decide +kernel

theorem rowEval5158 (x : Key → ℝ) : Integer.Sparse.eval row5158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5158, Integer.Sparse.eval_collectBalanced, rawRowCheck5158]

def rawRow5159 : Integer.Sparse Key := [(key2659, -1), (key2657, -1), (key2657, 2), (key2638, -1), (key2630, -1), (key2638, 2), (key2614, 2), (key2630, -1), (key2614, -1), (key2624, 2), (key2624, -1), (key2608, -1), (key2757, 1), (key2724, 1), (key2724, -2), (key2752, 1), (key2704, 1), (key2752, -2), (key2669, -2), (key2704, 1), (key2669, 1), (key2698, -2), (key2698, 1), (key2663, 1), (key2922, -1), (key2827, -1), (key2868, 1), (key2827, 1), (key2919, 1), (key2792, 1), (key2858, -1), (key2792, -1), (key2918, -1), (key2807, -1), (key2918, 1), (key2784, 1), (key2851, 1), (key2801, 1), (key2851, -1), (key2778, -1)]

theorem rawRowCheck5159 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block2.form0 = rawRow5159 := by decide +kernel

def row5159 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

theorem rowCheck5159 : row5159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5159 := by decide +kernel

theorem rowEval5159 (x : Key → ℝ) : Integer.Sparse.eval row5159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5159, Integer.Sparse.eval_collectBalanced, rawRowCheck5159]

def rawRow5160 : Integer.Sparse Key := [(key2663, -1), (key2669, -1), (key2669, 2), (key2698, -1), (key2704, -1), (key2698, 2), (key2752, 2), (key2704, -1), (key2752, -1), (key2724, 2), (key2724, -1), (key2757, -1), (key2608, 1), (key2614, 1), (key2614, -2), (key2801, 1), (key2807, 1), (key2801, -2), (key2827, -2), (key2807, 1), (key2827, 1), (key3011, -2), (key3011, 1), (key3016, 1), (key2624, -1), (key2638, -1), (key2630, 1), (key2638, 1), (key2698, 1), (key2724, 1), (key2704, -1), (key2724, -1), (key2851, -1), (key2858, -1), (key2851, 1), (key2868, 1), (key3021, 1), (key3022, 1), (key3021, -1), (key3025, -1)]

theorem rawRowCheck5160 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form0 = rawRow5160 := by decide +kernel

def row5160 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck5160 : row5160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5160 := by decide +kernel

theorem rowEval5160 (x : Key → ℝ) : Integer.Sparse.eval row5160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5160, Integer.Sparse.eval_collectBalanced, rawRowCheck5160]

def rawRow5161 : Integer.Sparse Key := [(key2669, -1), (key2663, -1), (key2669, 2), (key2704, -1), (key2698, -1), (key2752, 2), (key2698, 2), (key2752, -1), (key2704, -1), (key2724, 2), (key2757, -1), (key2724, -1), (key2614, 1), (key2608, 1), (key2614, -2), (key2807, 1), (key2801, 1), (key2827, -2), (key2801, -2), (key2827, 1), (key2807, 1), (key3011, -2), (key3016, 1), (key3011, 1), (key2638, -1), (key2624, -1), (key2638, 1), (key2630, 1), (key2724, 1), (key2698, 1), (key2724, -1), (key2704, -1), (key2858, -1), (key2851, -1), (key2868, 1), (key2851, 1), (key3022, 1), (key3021, 1), (key3025, -1), (key3021, -1)]

theorem rawRowCheck5161 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form0 = rawRow5161 := by decide +kernel

def row5161 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck5161 : row5161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5161 := by decide +kernel

theorem rowEval5161 (x : Key → ℝ) : Integer.Sparse.eval row5161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5161, Integer.Sparse.eval_collectBalanced, rawRowCheck5161]

def rawRow5162 : Integer.Sparse Key := [(key2669, -1), (key2669, -1), (key2663, 2), (key2752, -1), (key2752, -1), (key2704, 2), (key2704, 2), (key2698, -1), (key2698, -1), (key2757, 2), (key2724, -1), (key2724, -1), (key2614, 1), (key2614, 1), (key2608, -2), (key2827, 1), (key2827, 1), (key2807, -2), (key2807, -2), (key2801, 1), (key2801, 1), (key3016, -2), (key3011, 1), (key3011, 1), (key2630, -1), (key2630, -1), (key2624, 1), (key2624, 1), (key2704, 1), (key2704, 1), (key2698, -1), (key2698, -1), (key2868, -1), (key2868, -1), (key2858, 1), (key2858, 1), (key3025, 1), (key3025, 1), (key3022, -1), (key3022, -1)]

theorem rawRowCheck5162 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form0 = rawRow5162 := by decide +kernel

def row5162 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2630, -2), (key2663, 2), (key2669, -2), (key2698, -4), (key2704, 6), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 2), (key2858, 2), (key2868, -2), (key3011, 2), (key3016, -2), (key3022, -2), (key3025, 2)]

theorem rowCheck5162 : row5162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5162 := by decide +kernel

theorem rowEval5162 (x : Key → ℝ) : Integer.Sparse.eval row5162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5162, Integer.Sparse.eval_collectBalanced, rawRowCheck5162]

def rawRow5163 : Integer.Sparse Key := [(key2698, -1), (key2704, -1), (key2724, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2752, 2), (key2724, -1), (key2757, -1), (key2669, 2), (key2704, -1), (key2752, -1), (key2801, 1), (key2807, 1), (key2827, -2), (key2608, 1), (key2614, 1), (key2801, -2), (key2827, -2), (key3011, 1), (key3016, 1), (key2614, -2), (key2807, 1), (key2827, 1), (key2851, -1), (key2858, -1), (key3021, 1), (key3022, 1), (key2851, 1), (key2868, 1), (key3021, -1), (key3025, -1), (key2624, -1), (key2638, -1), (key2698, 1), (key2724, 1), (key2630, 1), (key2638, 1), (key2704, -1), (key2724, -1)]

theorem rawRowCheck5163 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form0 = rawRow5163 := by decide +kernel

def row5163 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2858, -1), (key2868, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck5163 : row5163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5163 := by decide +kernel

theorem rowEval5163 (x : Key → ℝ) : Integer.Sparse.eval row5163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5163, Integer.Sparse.eval_collectBalanced, rawRowCheck5163]

def rawRow5164 : Integer.Sparse Key := [(key2704, -1), (key2698, -1), (key2724, 2), (key2669, -1), (key2663, -1), (key2752, 2), (key2698, 2), (key2757, -1), (key2724, -1), (key2669, 2), (key2752, -1), (key2704, -1), (key2807, 1), (key2801, 1), (key2827, -2), (key2614, 1), (key2608, 1), (key2827, -2), (key2801, -2), (key3016, 1), (key3011, 1), (key2614, -2), (key2827, 1), (key2807, 1), (key2858, -1), (key2851, -1), (key3022, 1), (key3021, 1), (key2868, 1), (key2851, 1), (key3025, -1), (key3021, -1), (key2638, -1), (key2624, -1), (key2724, 1), (key2698, 1), (key2638, 1), (key2630, 1), (key2724, -1), (key2704, -1)]

theorem rawRowCheck5164 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form0 = rawRow5164 := by decide +kernel

def row5164 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2858, -1), (key2868, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck5164 : row5164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5164 := by decide +kernel

theorem rowEval5164 (x : Key → ℝ) : Integer.Sparse.eval row5164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5164, Integer.Sparse.eval_collectBalanced, rawRowCheck5164]

def rawRow5165 : Integer.Sparse Key := [(key2698, -1), (key2724, -1), (key2704, 2), (key2698, -1), (key2724, -1), (key2663, 2), (key2757, 2), (key2669, -1), (key2752, -1), (key2704, 2), (key2669, -1), (key2752, -1), (key2801, 1), (key2827, 1), (key2807, -2), (key2801, 1), (key2827, 1), (key2608, -2), (key3016, -2), (key2614, 1), (key2827, 1), (key2807, -2), (key2614, 1), (key2827, 1), (key2698, -1), (key3022, -1), (key2704, 1), (key2858, 1), (key2624, 1), (key3025, 1), (key2630, -1), (key2868, -1), (key2698, -1), (key3022, -1), (key2624, 1), (key3025, 1), (key2704, 1), (key2858, 1), (key2630, -1), (key2868, -1)]

theorem rawRowCheck5165 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form0 = rawRow5165 := by decide +kernel

def row5165 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2630, -2), (key2663, 2), (key2669, -2), (key2698, -4), (key2704, 6), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 4), (key2858, 2), (key2868, -2), (key3016, -2), (key3022, -2), (key3025, 2)]

theorem rowCheck5165 : row5165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5165 := by decide +kernel

theorem rowEval5165 (x : Key → ℝ) : Integer.Sparse.eval row5165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5165, Integer.Sparse.eval_collectBalanced, rawRowCheck5165]

def rawRow5166 : Integer.Sparse Key := [(key2724, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2698, -1), (key2757, 2), (key2663, 2), (key2752, -1), (key2669, -1), (key2704, 2), (key2752, -1), (key2669, -1), (key2827, 1), (key2801, 1), (key2807, -2), (key2827, 1), (key2801, 1), (key3016, -2), (key2608, -2), (key2827, 1), (key2614, 1), (key2807, -2), (key2827, 1), (key2614, 1), (key3022, -1), (key2698, -1), (key2858, 1), (key2704, 1), (key3025, 1), (key2624, 1), (key2868, -1), (key2630, -1), (key3022, -1), (key2698, -1), (key3025, 1), (key2624, 1), (key2858, 1), (key2704, 1), (key2868, -1), (key2630, -1)]

theorem rawRowCheck5166 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form0 = rawRow5166 := by decide +kernel

def row5166 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2630, -2), (key2663, 2), (key2669, -2), (key2698, -4), (key2704, 6), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 4), (key2858, 2), (key2868, -2), (key3016, -2), (key3022, -2), (key3025, 2)]

theorem rowCheck5166 : row5166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5166 := by decide +kernel

theorem rowEval5166 (x : Key → ℝ) : Integer.Sparse.eval row5166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5166, Integer.Sparse.eval_collectBalanced, rawRowCheck5166]

def rawRow5167 : Integer.Sparse Key := [(key2704, -1), (key2724, -1), (key2698, 2), (key2752, -1), (key2757, -1), (key2669, 2), (key2724, 2), (key2663, -1), (key2698, -1), (key2752, 2), (key2669, -1), (key2704, -1), (key2807, 1), (key2827, 1), (key2801, -2), (key3011, 1), (key3016, 1), (key2614, -2), (key2827, -2), (key2608, 1), (key2801, 1), (key2827, -2), (key2614, 1), (key2807, 1), (key2704, -1), (key3021, -1), (key2698, 1), (key2851, 1), (key2630, 1), (key3021, 1), (key2624, -1), (key2851, -1), (key2724, -1), (key3025, -1), (key2638, 1), (key3022, 1), (key2724, 1), (key2868, 1), (key2638, -1), (key2858, -1)]

theorem rawRowCheck5167 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form0 = rawRow5167 := by decide +kernel

def row5167 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2858, -1), (key2868, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck5167 : row5167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5167 := by decide +kernel

theorem rowEval5167 (x : Key → ℝ) : Integer.Sparse.eval row5167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5167, Integer.Sparse.eval_collectBalanced, rawRowCheck5167]

def rawRow5168 : Integer.Sparse Key := [(key2724, -1), (key2704, -1), (key2698, 2), (key2757, -1), (key2752, -1), (key2724, 2), (key2669, 2), (key2698, -1), (key2663, -1), (key2752, 2), (key2704, -1), (key2669, -1), (key2827, 1), (key2807, 1), (key2801, -2), (key3016, 1), (key3011, 1), (key2827, -2), (key2614, -2), (key2801, 1), (key2608, 1), (key2827, -2), (key2807, 1), (key2614, 1), (key3021, -1), (key2704, -1), (key2851, 1), (key2698, 1), (key3021, 1), (key2630, 1), (key2851, -1), (key2624, -1), (key3025, -1), (key2724, -1), (key3022, 1), (key2638, 1), (key2868, 1), (key2724, 1), (key2858, -1), (key2638, -1)]

theorem rawRowCheck5168 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form0 = rawRow5168 := by decide +kernel

def row5168 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2858, -1), (key2868, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck5168 : row5168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5168 := by decide +kernel

theorem rowEval5168 (x : Key → ℝ) : Integer.Sparse.eval row5168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5168, Integer.Sparse.eval_collectBalanced, rawRowCheck5168]

def rawRow5169 : Integer.Sparse Key := [(key2752, -1), (key2752, -1), (key2757, 2), (key2669, -1), (key2669, -1), (key2704, 2), (key2704, 2), (key2724, -1), (key2724, -1), (key2663, 2), (key2698, -1), (key2698, -1), (key3011, 1), (key3011, 1), (key3016, -2), (key2614, 1), (key2614, 1), (key2807, -2), (key2807, -2), (key2827, 1), (key2827, 1), (key2608, -2), (key2801, 1), (key2801, 1), (key2868, -1), (key2868, -1), (key3025, 1), (key3025, 1), (key2858, 1), (key2858, 1), (key3022, -1), (key3022, -1), (key2630, -1), (key2630, -1), (key2704, 1), (key2704, 1), (key2624, 1), (key2624, 1), (key2698, -1), (key2698, -1)]

theorem rawRowCheck5169 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form0 = rawRow5169 := by decide +kernel

def row5169 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2630, -2), (key2663, 2), (key2669, -2), (key2698, -4), (key2704, 6), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 2), (key2858, 2), (key2868, -2), (key3011, 2), (key3016, -2), (key3022, -2), (key3025, 2)]

theorem rowCheck5169 : row5169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5169 := by decide +kernel

theorem rowEval5169 (x : Key → ℝ) : Integer.Sparse.eval row5169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5169, Integer.Sparse.eval_collectBalanced, rawRowCheck5169]

def rawRow5170 : Integer.Sparse Key := [(key2752, -1), (key2757, -1), (key2752, 2), (key2704, -1), (key2724, -1), (key2669, 2), (key2724, 2), (key2669, -1), (key2704, -1), (key2698, 2), (key2663, -1), (key2698, -1), (key3011, 1), (key3016, 1), (key3011, -2), (key2807, 1), (key2827, 1), (key2614, -2), (key2827, -2), (key2614, 1), (key2807, 1), (key2801, -2), (key2608, 1), (key2801, 1), (key2724, -1), (key3025, -1), (key2724, 1), (key2868, 1), (key2638, 1), (key3022, 1), (key2638, -1), (key2858, -1), (key2704, -1), (key3021, -1), (key2630, 1), (key3021, 1), (key2698, 1), (key2851, 1), (key2624, -1), (key2851, -1)]

theorem rawRowCheck5170 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form0 = rawRow5170 := by decide +kernel

def row5170 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck5170 : row5170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5170 := by decide +kernel

theorem rowEval5170 (x : Key → ℝ) : Integer.Sparse.eval row5170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5170, Integer.Sparse.eval_collectBalanced, rawRowCheck5170]

def rawRow5171 : Integer.Sparse Key := [(key2757, -1), (key2752, -1), (key2752, 2), (key2724, -1), (key2704, -1), (key2724, 2), (key2669, 2), (key2704, -1), (key2669, -1), (key2698, 2), (key2698, -1), (key2663, -1), (key3016, 1), (key3011, 1), (key3011, -2), (key2827, 1), (key2807, 1), (key2827, -2), (key2614, -2), (key2807, 1), (key2614, 1), (key2801, -2), (key2801, 1), (key2608, 1), (key3025, -1), (key2724, -1), (key2868, 1), (key2724, 1), (key3022, 1), (key2638, 1), (key2858, -1), (key2638, -1), (key3021, -1), (key2704, -1), (key3021, 1), (key2630, 1), (key2851, 1), (key2698, 1), (key2851, -1), (key2624, -1)]

theorem rawRowCheck5171 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form0 = rawRow5171 := by decide +kernel

def row5171 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck5171 : row5171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5171 := by decide +kernel

theorem rowEval5171 (x : Key → ℝ) : Integer.Sparse.eval row5171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5171, Integer.Sparse.eval_collectBalanced, rawRowCheck5171]

def rawRow5172 : Integer.Sparse Key := [(key2778, -1), (key2792, -1), (key2784, 2), (key2851, -1), (key2858, -1), (key2801, 2), (key2919, 2), (key2807, -1), (key2918, -1), (key2868, 2), (key2827, -1), (key2922, -1), (key2624, 1), (key2638, 1), (key2630, -2), (key2851, 1), (key2858, 1), (key2698, -2), (key3022, -2), (key2704, 1), (key3021, 1), (key2868, -2), (key2724, 1), (key3025, 1), (key2608, -1), (key2659, -1), (key2614, 1), (key2638, 1), (key2663, 1), (key2757, 1), (key2669, -1), (key2724, -1), (key2801, -1), (key2919, -1), (key2778, 1), (key2922, 1), (key3011, 1), (key3022, 1), (key3007, -1), (key3025, -1)]

theorem rawRowCheck5172 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block2.form0 = rawRow5172 := by decide +kernel

def row5172 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -2), (key2704, 1), (key2757, 1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2827, -1), (key2918, -1), (key2919, 1), (key3007, -1), (key3011, 1), (key3021, 1), (key3022, -1)]

theorem rowCheck5172 : row5172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5172 := by decide +kernel

theorem rowEval5172 (x : Key → ℝ) : Integer.Sparse.eval row5172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5172, Integer.Sparse.eval_collectBalanced, rawRowCheck5172]

def rawRow5173 : Integer.Sparse Key := [(key2792, -1), (key2778, -1), (key2784, 2), (key2858, -1), (key2851, -1), (key2919, 2), (key2801, 2), (key2918, -1), (key2807, -1), (key2868, 2), (key2922, -1), (key2827, -1), (key2638, 1), (key2624, 1), (key2630, -2), (key2858, 1), (key2851, 1), (key3022, -2), (key2698, -2), (key3021, 1), (key2704, 1), (key2868, -2), (key3025, 1), (key2724, 1), (key2659, -1), (key2608, -1), (key2638, 1), (key2614, 1), (key2757, 1), (key2663, 1), (key2724, -1), (key2669, -1), (key2919, -1), (key2801, -1), (key2922, 1), (key2778, 1), (key3022, 1), (key3011, 1), (key3025, -1), (key3007, -1)]

theorem rawRowCheck5173 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block2.form0 = rawRow5173 := by decide +kernel

def row5173 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -2), (key2704, 1), (key2757, 1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2827, -1), (key2918, -1), (key2919, 1), (key3007, -1), (key3011, 1), (key3021, 1), (key3022, -1)]

theorem rowCheck5173 : row5173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5173 := by decide +kernel

theorem rowEval5173 (x : Key → ℝ) : Integer.Sparse.eval row5173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5173, Integer.Sparse.eval_collectBalanced, rawRowCheck5173]

def rawRow5174 : Integer.Sparse Key := [(key2784, -1), (key2792, -1), (key2778, 2), (key2918, -1), (key2919, -1), (key2807, 2), (key2858, 2), (key2801, -1), (key2851, -1), (key2922, 2), (key2827, -1), (key2868, -1), (key2630, 1), (key2638, 1), (key2624, -2), (key3021, 1), (key3022, 1), (key2704, -2), (key2858, -2), (key2698, 1), (key2851, 1), (key3025, -2), (key2724, 1), (key2868, 1), (key2614, -1), (key2638, -1), (key2608, 1), (key2624, 1), (key2669, 1), (key2752, 1), (key2663, -1), (key2698, -1), (key2827, -1), (key2922, -1), (key2792, 1), (key2919, 1), (key3016, 1), (key3025, 1), (key3009, -1), (key3022, -1)]

theorem rawRowCheck5174 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form0 = rawRow5174 := by decide +kernel

def row5174 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2778, 2), (key2784, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3009, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck5174 : row5174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5174 := by decide +kernel

theorem rowEval5174 (x : Key → ℝ) : Integer.Sparse.eval row5174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5174, Integer.Sparse.eval_collectBalanced, rawRowCheck5174]

def rawRow5175 : Integer.Sparse Key := [(key2792, -1), (key2784, -1), (key2778, 2), (key2919, -1), (key2918, -1), (key2858, 2), (key2807, 2), (key2851, -1), (key2801, -1), (key2922, 2), (key2868, -1), (key2827, -1), (key2638, 1), (key2630, 1), (key2624, -2), (key3022, 1), (key3021, 1), (key2858, -2), (key2704, -2), (key2851, 1), (key2698, 1), (key3025, -2), (key2868, 1), (key2724, 1), (key2638, -1), (key2614, -1), (key2624, 1), (key2608, 1), (key2752, 1), (key2669, 1), (key2698, -1), (key2663, -1), (key2922, -1), (key2827, -1), (key2919, 1), (key2792, 1), (key3025, 1), (key3016, 1), (key3022, -1), (key3009, -1)]

theorem rawRowCheck5175 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form0 = rawRow5175 := by decide +kernel

def row5175 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2778, 2), (key2784, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3009, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck5175 : row5175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5175 := by decide +kernel

theorem rowEval5175 (x : Key → ℝ) : Integer.Sparse.eval row5175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5175, Integer.Sparse.eval_collectBalanced, rawRowCheck5175]

def rawRow5176 : Integer.Sparse Key := [(key2801, -1), (key2827, -1), (key2807, 2), (key2851, -1), (key2868, -1), (key2778, 2), (key2922, 2), (key2784, -1), (key2918, -1), (key2858, 2), (key2792, -1), (key2919, -1), (key2698, 1), (key2724, 1), (key2704, -2), (key2851, 1), (key2868, 1), (key2624, -2), (key3025, -2), (key2630, 1), (key3021, 1), (key2858, -2), (key2638, 1), (key3022, 1), (key2663, -1), (key2757, -1), (key2669, 1), (key2752, 1), (key2608, 1), (key3016, 1), (key2614, -1), (key2827, -1), (key2698, -1), (key3022, -1), (key2624, 1), (key3025, 1), (key2752, 1), (key2919, 1), (key2657, -1), (key2922, -1)]

theorem rawRowCheck5176 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form0 = rawRow5176 := by decide +kernel

def row5176 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2638, 1), (key2657, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 2), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck5176 : row5176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5176 := by decide +kernel

theorem rowEval5176 (x : Key → ℝ) : Integer.Sparse.eval row5176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5176, Integer.Sparse.eval_collectBalanced, rawRowCheck5176]

def rawRow5177 : Integer.Sparse Key := [(key2827, -1), (key2801, -1), (key2807, 2), (key2868, -1), (key2851, -1), (key2922, 2), (key2778, 2), (key2918, -1), (key2784, -1), (key2858, 2), (key2919, -1), (key2792, -1), (key2724, 1), (key2698, 1), (key2704, -2), (key2868, 1), (key2851, 1), (key3025, -2), (key2624, -2), (key3021, 1), (key2630, 1), (key2858, -2), (key3022, 1), (key2638, 1), (key2757, -1), (key2663, -1), (key2752, 1), (key2669, 1), (key3016, 1), (key2608, 1), (key2827, -1), (key2614, -1), (key3022, -1), (key2698, -1), (key3025, 1), (key2624, 1), (key2919, 1), (key2752, 1), (key2922, -1), (key2657, -1)]

theorem rawRowCheck5177 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form0 = rawRow5177 := by decide +kernel

def row5177 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2638, 1), (key2657, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 2), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck5177 : row5177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5177 := by decide +kernel

theorem rowEval5177 (x : Key → ℝ) : Integer.Sparse.eval row5177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5177, Integer.Sparse.eval_collectBalanced, rawRowCheck5177]

def rawRow5178 : Integer.Sparse Key := [(key2807, -1), (key2827, -1), (key2801, 2), (key2918, -1), (key2922, -1), (key2784, 2), (key2868, 2), (key2778, -1), (key2851, -1), (key2919, 2), (key2792, -1), (key2858, -1), (key2704, 1), (key2724, 1), (key2698, -2), (key3021, 1), (key3025, 1), (key2630, -2), (key2868, -2), (key2624, 1), (key2851, 1), (key3022, -2), (key2638, 1), (key2858, 1), (key2669, -1), (key2724, -1), (key2663, 1), (key2698, 1), (key2614, 1), (key2827, 1), (key2608, -1), (key2801, -1), (key2724, -1), (key3025, -1), (key2638, 1), (key3022, 1), (key2757, 1), (key2922, 1), (key2659, -1), (key2919, -1)]

theorem rawRowCheck5178 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block2.form0 = rawRow5178 := by decide +kernel

def row5178 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, -1), (key2757, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3021, 1), (key3022, -1)]

theorem rowCheck5178 : row5178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5178 := by decide +kernel

theorem rowEval5178 (x : Key → ℝ) : Integer.Sparse.eval row5178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5178, Integer.Sparse.eval_collectBalanced, rawRowCheck5178]

def rawRow5179 : Integer.Sparse Key := [(key2827, -1), (key2807, -1), (key2801, 2), (key2922, -1), (key2918, -1), (key2868, 2), (key2784, 2), (key2851, -1), (key2778, -1), (key2919, 2), (key2858, -1), (key2792, -1), (key2724, 1), (key2704, 1), (key2698, -2), (key3025, 1), (key3021, 1), (key2868, -2), (key2630, -2), (key2851, 1), (key2624, 1), (key3022, -2), (key2858, 1), (key2638, 1), (key2724, -1), (key2669, -1), (key2698, 1), (key2663, 1), (key2827, 1), (key2614, 1), (key2801, -1), (key2608, -1), (key3025, -1), (key2724, -1), (key3022, 1), (key2638, 1), (key2922, 1), (key2757, 1), (key2919, -1), (key2659, -1)]

theorem rawRowCheck5179 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block2.form0 = rawRow5179 := by decide +kernel

def row5179 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, -1), (key2757, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3021, 1), (key3022, -1)]

theorem rowCheck5179 : row5179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5179 := by decide +kernel

theorem rowEval5179 (x : Key → ℝ) : Integer.Sparse.eval row5179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5179, Integer.Sparse.eval_collectBalanced, rawRowCheck5179]

def rawRow5180 : Integer.Sparse Key := [(key2851, -1), (key2858, -1), (key2868, 2), (key2778, -1), (key2792, -1), (key2801, 2), (key2919, 2), (key2827, -1), (key2922, -1), (key2784, 2), (key2807, -1), (key2918, -1), (key2851, 1), (key2858, 1), (key2868, -2), (key2624, 1), (key2638, 1), (key2698, -2), (key3022, -2), (key2724, 1), (key3025, 1), (key2630, -2), (key2704, 1), (key3021, 1), (key2801, -1), (key2919, -1), (key2827, 1), (key2922, 1), (key2698, 1), (key3022, 1), (key2724, -1), (key3025, -1), (key2608, -1), (key2659, -1), (key2663, 1), (key2757, 1), (key2614, 1), (key2638, 1), (key2669, -1), (key2724, -1)]

theorem rawRowCheck5180 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block2.form0 = rawRow5180 := by decide +kernel

def row5180 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, -1), (key2757, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3021, 1), (key3022, -1)]

theorem rowCheck5180 : row5180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5180 := by decide +kernel

theorem rowEval5180 (x : Key → ℝ) : Integer.Sparse.eval row5180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5180, Integer.Sparse.eval_collectBalanced, rawRowCheck5180]

def rawRow5181 : Integer.Sparse Key := [(key2858, -1), (key2851, -1), (key2868, 2), (key2792, -1), (key2778, -1), (key2919, 2), (key2801, 2), (key2922, -1), (key2827, -1), (key2784, 2), (key2918, -1), (key2807, -1), (key2858, 1), (key2851, 1), (key2868, -2), (key2638, 1), (key2624, 1), (key3022, -2), (key2698, -2), (key3025, 1), (key2724, 1), (key2630, -2), (key3021, 1), (key2704, 1), (key2919, -1), (key2801, -1), (key2922, 1), (key2827, 1), (key3022, 1), (key2698, 1), (key3025, -1), (key2724, -1), (key2659, -1), (key2608, -1), (key2757, 1), (key2663, 1), (key2638, 1), (key2614, 1), (key2724, -1), (key2669, -1)]

theorem rawRowCheck5181 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block2.form0 = rawRow5181 := by decide +kernel

def row5181 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, -1), (key2757, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3021, 1), (key3022, -1)]

theorem rowCheck5181 : row5181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5181 := by decide +kernel

theorem rowEval5181 (x : Key → ℝ) : Integer.Sparse.eval row5181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5181, Integer.Sparse.eval_collectBalanced, rawRowCheck5181]

def rawRow5182 : Integer.Sparse Key := [(key2851, -1), (key2868, -1), (key2858, 2), (key2801, -1), (key2827, -1), (key2778, 2), (key2922, 2), (key2792, -1), (key2919, -1), (key2807, 2), (key2784, -1), (key2918, -1), (key2851, 1), (key2868, 1), (key2858, -2), (key2698, 1), (key2724, 1), (key2624, -2), (key3025, -2), (key2638, 1), (key3022, 1), (key2704, -2), (key2630, 1), (key3021, 1), (key2778, -1), (key2922, -1), (key2792, 1), (key2919, 1), (key2624, 1), (key3025, 1), (key2638, -1), (key3022, -1), (key2663, -1), (key2757, -1), (key2608, 1), (key3016, 1), (key2669, 1), (key2792, 1), (key2614, -1), (key2827, -1)]

theorem rawRowCheck5182 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form0 = rawRow5182 := by decide +kernel

def row5182 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck5182 : row5182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5182 := by decide +kernel

theorem rowEval5182 (x : Key → ℝ) : Integer.Sparse.eval row5182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5182, Integer.Sparse.eval_collectBalanced, rawRowCheck5182]

def rawRow5183 : Integer.Sparse Key := [(key2868, -1), (key2851, -1), (key2858, 2), (key2827, -1), (key2801, -1), (key2922, 2), (key2778, 2), (key2919, -1), (key2792, -1), (key2807, 2), (key2918, -1), (key2784, -1), (key2868, 1), (key2851, 1), (key2858, -2), (key2724, 1), (key2698, 1), (key3025, -2), (key2624, -2), (key3022, 1), (key2638, 1), (key2704, -2), (key3021, 1), (key2630, 1), (key2922, -1), (key2778, -1), (key2919, 1), (key2792, 1), (key3025, 1), (key2624, 1), (key3022, -1), (key2638, -1), (key2757, -1), (key2663, -1), (key3016, 1), (key2608, 1), (key2792, 1), (key2669, 1), (key2827, -1), (key2614, -1)]

theorem rawRowCheck5183 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form0 = rawRow5183 := by decide +kernel

def row5183 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck5183 : row5183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5183 := by decide +kernel

theorem rowEval5183 (x : Key → ℝ) : Integer.Sparse.eval row5183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5183, Integer.Sparse.eval_collectBalanced, rawRowCheck5183]

def rawRow5184 : Integer.Sparse Key := [(key2918, -1), (key2919, -1), (key2922, 2), (key2784, -1), (key2792, -1), (key2807, 2), (key2858, 2), (key2827, -1), (key2868, -1), (key2778, 2), (key2801, -1), (key2851, -1), (key3021, 1), (key3022, 1), (key3025, -2), (key2630, 1), (key2638, 1), (key2704, -2), (key2858, -2), (key2724, 1), (key2868, 1), (key2624, -2), (key2698, 1), (key2851, 1), (key3011, -1), (key3022, -1), (key3016, 1), (key3025, 1), (key2752, 1), (key2919, 1), (key2757, -1), (key2922, -1), (key2614, -1), (key2638, -1), (key2669, 1), (key2792, 1), (key2608, 1), (key2624, 1), (key2663, -1), (key2698, -1)]

theorem rawRowCheck5184 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form0 = rawRow5184 := by decide +kernel

def row5184 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 2), (key2784, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2918, -1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck5184 : row5184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5184 := by decide +kernel

theorem rowEval5184 (x : Key → ℝ) : Integer.Sparse.eval row5184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5184, Integer.Sparse.eval_collectBalanced, rawRowCheck5184]

def rawRow5185 : Integer.Sparse Key := [(key2919, -1), (key2918, -1), (key2922, 2), (key2792, -1), (key2784, -1), (key2858, 2), (key2807, 2), (key2868, -1), (key2827, -1), (key2778, 2), (key2851, -1), (key2801, -1), (key3022, 1), (key3021, 1), (key3025, -2), (key2638, 1), (key2630, 1), (key2858, -2), (key2704, -2), (key2868, 1), (key2724, 1), (key2624, -2), (key2851, 1), (key2698, 1), (key3022, -1), (key3011, -1), (key3025, 1), (key3016, 1), (key2919, 1), (key2752, 1), (key2922, -1), (key2757, -1), (key2638, -1), (key2614, -1), (key2792, 1), (key2669, 1), (key2624, 1), (key2608, 1), (key2698, -1), (key2663, -1)]

theorem rawRowCheck5185 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form0 = rawRow5185 := by decide +kernel

def row5185 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 2), (key2784, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2918, -1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck5185 : row5185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5185 := by decide +kernel

theorem rowEval5185 (x : Key → ℝ) : Integer.Sparse.eval row5185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5185, Integer.Sparse.eval_collectBalanced, rawRowCheck5185]

def rawRow5186 : Integer.Sparse Key := [(key2918, -1), (key2922, -1), (key2919, 2), (key2807, -1), (key2827, -1), (key2784, 2), (key2868, 2), (key2792, -1), (key2858, -1), (key2801, 2), (key2778, -1), (key2851, -1), (key3021, 1), (key3025, 1), (key3022, -2), (key2704, 1), (key2724, 1), (key2630, -2), (key2868, -2), (key2638, 1), (key2858, 1), (key2698, -2), (key2624, 1), (key2851, 1), (key3007, -1), (key3025, -1), (key3009, 1), (key3022, 1), (key2657, 1), (key2922, 1), (key2659, -1), (key2919, -1), (key2669, -1), (key2724, -1), (key2614, 1), (key2827, 1), (key2663, 1), (key2698, 1), (key2608, -1), (key2801, -1)]

theorem rawRowCheck5186 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block2.form0 = rawRow5186 := by decide +kernel

def row5186 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3007, -1), (key3009, 1), (key3021, 1), (key3022, -1)]

theorem rowCheck5186 : row5186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5186 := by decide +kernel

theorem rowEval5186 (x : Key → ℝ) : Integer.Sparse.eval row5186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5186, Integer.Sparse.eval_collectBalanced, rawRowCheck5186]

def rawRow5187 : Integer.Sparse Key := [(key2922, -1), (key2918, -1), (key2919, 2), (key2827, -1), (key2807, -1), (key2868, 2), (key2784, 2), (key2858, -1), (key2792, -1), (key2801, 2), (key2851, -1), (key2778, -1), (key3025, 1), (key3021, 1), (key3022, -2), (key2724, 1), (key2704, 1), (key2868, -2), (key2630, -2), (key2858, 1), (key2638, 1), (key2698, -2), (key2851, 1), (key2624, 1), (key3025, -1), (key3007, -1), (key3022, 1), (key3009, 1), (key2922, 1), (key2657, 1), (key2919, -1), (key2659, -1), (key2724, -1), (key2669, -1), (key2827, 1), (key2614, 1), (key2698, 1), (key2663, 1), (key2801, -1), (key2608, -1)]

theorem rawRowCheck5187 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block2.form0 = rawRow5187 := by decide +kernel

def row5187 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3007, -1), (key3009, 1), (key3021, 1), (key3022, -1)]

theorem rowCheck5187 : row5187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5187 := by decide +kernel

theorem rowEval5187 (x : Key → ℝ) : Integer.Sparse.eval row5187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5187, Integer.Sparse.eval_collectBalanced, rawRowCheck5187]

def rawRow5188 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1299, 2), (key1311, -1), (key1319, -1), (key1311, 2), (key1327, 2), (key1319, -1), (key1327, -1), (key1352, 2), (key1352, -1), (key1355, -1), (key1386, 1), (key1394, 1), (key1394, -2), (key1419, 1), (key1427, 1), (key1419, -2), (key1445, -2), (key1427, 1), (key1445, 1), (key1473, -2), (key1473, 1), (key1481, 1), (key1541, -1), (key1557, -1), (key1549, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1576, -1), (key1594, -1), (key1617, -1), (key1625, -1), (key1617, 1), (key1634, 1), (key1682, 1), (key1684, 1), (key1682, -1), (key1690, -1)]

theorem rawRowCheck5188 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block2.form0 = rawRow5188 := by decide +kernel

def row5188 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5188 : row5188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5188 := by decide +kernel

theorem rowEval5188 (x : Key → ℝ) : Integer.Sparse.eval row5188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5188, Integer.Sparse.eval_collectBalanced, rawRowCheck5188]

def rawRow5189 : Integer.Sparse Key := [(key1299, -1), (key1291, -1), (key1299, 2), (key1319, -1), (key1311, -1), (key1327, 2), (key1311, 2), (key1327, -1), (key1319, -1), (key1352, 2), (key1355, -1), (key1352, -1), (key1394, 1), (key1386, 1), (key1394, -2), (key1427, 1), (key1419, 1), (key1445, -2), (key1419, -2), (key1445, 1), (key1427, 1), (key1473, -2), (key1481, 1), (key1473, 1), (key1557, -1), (key1541, -1), (key1557, 1), (key1549, 1), (key1594, 1), (key1568, 1), (key1594, -1), (key1576, -1), (key1625, -1), (key1617, -1), (key1634, 1), (key1617, 1), (key1684, 1), (key1682, 1), (key1690, -1), (key1682, -1)]

theorem rawRowCheck5189 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block2.form0 = rawRow5189 := by decide +kernel

def row5189 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5189 : row5189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5189 := by decide +kernel

theorem rowEval5189 (x : Key → ℝ) : Integer.Sparse.eval row5189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5189, Integer.Sparse.eval_collectBalanced, rawRowCheck5189]

def rawRow5190 : Integer.Sparse Key := [(key1299, -1), (key1299, -1), (key1291, 2), (key1327, -1), (key1327, -1), (key1319, 2), (key1319, 2), (key1311, -1), (key1311, -1), (key1355, 2), (key1352, -1), (key1352, -1), (key1394, 1), (key1394, 1), (key1386, -2), (key1445, 1), (key1445, 1), (key1427, -2), (key1427, -2), (key1419, 1), (key1419, 1), (key1481, -2), (key1473, 1), (key1473, 1), (key1549, -1), (key1549, -1), (key1541, 1), (key1541, 1), (key1576, 1), (key1576, 1), (key1568, -1), (key1568, -1), (key1634, -1), (key1634, -1), (key1625, 1), (key1625, 1), (key1690, 1), (key1690, 1), (key1684, -1), (key1684, -1)]

theorem rawRowCheck5190 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block2.form0 = rawRow5190 := by decide +kernel

def row5190 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1319, 4), (key1327, -2), (key1352, -2), (key1355, 2), (key1386, -2), (key1394, 2), (key1419, 2), (key1427, -4), (key1445, 2), (key1473, 2), (key1481, -2), (key1541, 2), (key1549, -2), (key1568, -2), (key1576, 2), (key1625, 2), (key1634, -2), (key1684, -2), (key1690, 2)]

theorem rowCheck5190 : row5190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5190 := by decide +kernel

theorem rowEval5190 (x : Key → ℝ) : Integer.Sparse.eval row5190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5190, Integer.Sparse.eval_collectBalanced, rawRowCheck5190]

def rawRow5191 : Integer.Sparse Key := [(key1311, -1), (key1319, -1), (key1352, 2), (key1291, -1), (key1299, -1), (key1311, 2), (key1327, 2), (key1352, -1), (key1355, -1), (key1299, 2), (key1319, -1), (key1327, -1), (key1419, 1), (key1427, 1), (key1473, -2), (key1386, 1), (key1394, 1), (key1419, -2), (key1445, -2), (key1473, 1), (key1481, 1), (key1394, -2), (key1427, 1), (key1445, 1), (key1617, -1), (key1625, -1), (key1682, 1), (key1684, 1), (key1617, 1), (key1634, 1), (key1682, -1), (key1690, -1), (key1541, -1), (key1557, -1), (key1568, 1), (key1594, 1), (key1549, 1), (key1557, 1), (key1576, -1), (key1594, -1)]

theorem rawRowCheck5191 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block2.form0 = rawRow5191 := by decide +kernel

def row5191 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5191 : row5191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5191 := by decide +kernel

theorem rowEval5191 (x : Key → ℝ) : Integer.Sparse.eval row5191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5191, Integer.Sparse.eval_collectBalanced, rawRowCheck5191]

def rawRow5192 : Integer.Sparse Key := [(key1319, -1), (key1311, -1), (key1352, 2), (key1299, -1), (key1291, -1), (key1327, 2), (key1311, 2), (key1355, -1), (key1352, -1), (key1299, 2), (key1327, -1), (key1319, -1), (key1427, 1), (key1419, 1), (key1473, -2), (key1394, 1), (key1386, 1), (key1445, -2), (key1419, -2), (key1481, 1), (key1473, 1), (key1394, -2), (key1445, 1), (key1427, 1), (key1625, -1), (key1617, -1), (key1684, 1), (key1682, 1), (key1634, 1), (key1617, 1), (key1690, -1), (key1682, -1), (key1557, -1), (key1541, -1), (key1594, 1), (key1568, 1), (key1557, 1), (key1549, 1), (key1594, -1), (key1576, -1)]

theorem rawRowCheck5192 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block2.form0 = rawRow5192 := by decide +kernel

def row5192 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5192 : row5192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5192 := by decide +kernel

theorem rowEval5192 (x : Key → ℝ) : Integer.Sparse.eval row5192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5192, Integer.Sparse.eval_collectBalanced, rawRowCheck5192]

def rawRow5193 : Integer.Sparse Key := [(key1311, -1), (key1352, -1), (key1319, 2), (key1311, -1), (key1352, -1), (key1291, 2), (key1355, 2), (key1299, -1), (key1327, -1), (key1319, 2), (key1299, -1), (key1327, -1), (key1419, 1), (key1473, 1), (key1427, -2), (key1419, 1), (key1473, 1), (key1386, -2), (key1481, -2), (key1394, 1), (key1445, 1), (key1427, -2), (key1394, 1), (key1445, 1), (key1568, -1), (key1684, -1), (key1576, 1), (key1625, 1), (key1541, 1), (key1690, 1), (key1549, -1), (key1634, -1), (key1568, -1), (key1684, -1), (key1541, 1), (key1690, 1), (key1576, 1), (key1625, 1), (key1549, -1), (key1634, -1)]

theorem rawRowCheck5193 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block2.form0 = rawRow5193 := by decide +kernel

def row5193 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1319, 4), (key1327, -2), (key1352, -2), (key1355, 2), (key1386, -2), (key1394, 2), (key1419, 2), (key1427, -4), (key1445, 2), (key1473, 2), (key1481, -2), (key1541, 2), (key1549, -2), (key1568, -2), (key1576, 2), (key1625, 2), (key1634, -2), (key1684, -2), (key1690, 2)]

theorem rowCheck5193 : row5193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5193 := by decide +kernel

theorem rowEval5193 (x : Key → ℝ) : Integer.Sparse.eval row5193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5193, Integer.Sparse.eval_collectBalanced, rawRowCheck5193]

def rawRow5194 : Integer.Sparse Key := [(key1352, -1), (key1311, -1), (key1319, 2), (key1352, -1), (key1311, -1), (key1355, 2), (key1291, 2), (key1327, -1), (key1299, -1), (key1319, 2), (key1327, -1), (key1299, -1), (key1473, 1), (key1419, 1), (key1427, -2), (key1473, 1), (key1419, 1), (key1481, -2), (key1386, -2), (key1445, 1), (key1394, 1), (key1427, -2), (key1445, 1), (key1394, 1), (key1684, -1), (key1568, -1), (key1625, 1), (key1576, 1), (key1690, 1), (key1541, 1), (key1634, -1), (key1549, -1), (key1684, -1), (key1568, -1), (key1690, 1), (key1541, 1), (key1625, 1), (key1576, 1), (key1634, -1), (key1549, -1)]

theorem rawRowCheck5194 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block2.form0 = rawRow5194 := by decide +kernel

def row5194 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1319, 4), (key1327, -2), (key1352, -2), (key1355, 2), (key1386, -2), (key1394, 2), (key1419, 2), (key1427, -4), (key1445, 2), (key1473, 2), (key1481, -2), (key1541, 2), (key1549, -2), (key1568, -2), (key1576, 2), (key1625, 2), (key1634, -2), (key1684, -2), (key1690, 2)]

theorem rowCheck5194 : row5194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5194 := by decide +kernel

theorem rowEval5194 (x : Key → ℝ) : Integer.Sparse.eval row5194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5194, Integer.Sparse.eval_collectBalanced, rawRowCheck5194]

def rawRow5195 : Integer.Sparse Key := [(key1319, -1), (key1352, -1), (key1311, 2), (key1327, -1), (key1355, -1), (key1299, 2), (key1352, 2), (key1291, -1), (key1311, -1), (key1327, 2), (key1299, -1), (key1319, -1), (key1427, 1), (key1473, 1), (key1419, -2), (key1445, 1), (key1481, 1), (key1394, -2), (key1473, -2), (key1386, 1), (key1419, 1), (key1445, -2), (key1394, 1), (key1427, 1), (key1576, -1), (key1682, -1), (key1568, 1), (key1617, 1), (key1549, 1), (key1682, 1), (key1541, -1), (key1617, -1), (key1594, -1), (key1690, -1), (key1557, 1), (key1684, 1), (key1594, 1), (key1634, 1), (key1557, -1), (key1625, -1)]

theorem rawRowCheck5195 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block2.form0 = rawRow5195 := by decide +kernel

def row5195 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5195 : row5195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5195 := by decide +kernel

theorem rowEval5195 (x : Key → ℝ) : Integer.Sparse.eval row5195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5195, Integer.Sparse.eval_collectBalanced, rawRowCheck5195]

def rawRow5196 : Integer.Sparse Key := [(key1352, -1), (key1319, -1), (key1311, 2), (key1355, -1), (key1327, -1), (key1352, 2), (key1299, 2), (key1311, -1), (key1291, -1), (key1327, 2), (key1319, -1), (key1299, -1), (key1473, 1), (key1427, 1), (key1419, -2), (key1481, 1), (key1445, 1), (key1473, -2), (key1394, -2), (key1419, 1), (key1386, 1), (key1445, -2), (key1427, 1), (key1394, 1), (key1682, -1), (key1576, -1), (key1617, 1), (key1568, 1), (key1682, 1), (key1549, 1), (key1617, -1), (key1541, -1), (key1690, -1), (key1594, -1), (key1684, 1), (key1557, 1), (key1634, 1), (key1594, 1), (key1625, -1), (key1557, -1)]

theorem rawRowCheck5196 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block2.form0 = rawRow5196 := by decide +kernel

def row5196 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5196 : row5196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5196 := by decide +kernel

theorem rowEval5196 (x : Key → ℝ) : Integer.Sparse.eval row5196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5196, Integer.Sparse.eval_collectBalanced, rawRowCheck5196]

def rawRow5197 : Integer.Sparse Key := [(key1327, -1), (key1327, -1), (key1355, 2), (key1299, -1), (key1299, -1), (key1319, 2), (key1319, 2), (key1352, -1), (key1352, -1), (key1291, 2), (key1311, -1), (key1311, -1), (key1445, 1), (key1445, 1), (key1481, -2), (key1394, 1), (key1394, 1), (key1427, -2), (key1427, -2), (key1473, 1), (key1473, 1), (key1386, -2), (key1419, 1), (key1419, 1), (key1634, -1), (key1634, -1), (key1690, 1), (key1690, 1), (key1625, 1), (key1625, 1), (key1684, -1), (key1684, -1), (key1549, -1), (key1549, -1), (key1576, 1), (key1576, 1), (key1541, 1), (key1541, 1), (key1568, -1), (key1568, -1)]

theorem rawRowCheck5197 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block2.form0 = rawRow5197 := by decide +kernel

def row5197 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1319, 4), (key1327, -2), (key1352, -2), (key1355, 2), (key1386, -2), (key1394, 2), (key1419, 2), (key1427, -4), (key1445, 2), (key1473, 2), (key1481, -2), (key1541, 2), (key1549, -2), (key1568, -2), (key1576, 2), (key1625, 2), (key1634, -2), (key1684, -2), (key1690, 2)]

theorem rowCheck5197 : row5197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5197 := by decide +kernel

theorem rowEval5197 (x : Key → ℝ) : Integer.Sparse.eval row5197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5197, Integer.Sparse.eval_collectBalanced, rawRowCheck5197]

def rawRow5198 : Integer.Sparse Key := [(key1327, -1), (key1355, -1), (key1327, 2), (key1319, -1), (key1352, -1), (key1299, 2), (key1352, 2), (key1299, -1), (key1319, -1), (key1311, 2), (key1291, -1), (key1311, -1), (key1445, 1), (key1481, 1), (key1445, -2), (key1427, 1), (key1473, 1), (key1394, -2), (key1473, -2), (key1394, 1), (key1427, 1), (key1419, -2), (key1386, 1), (key1419, 1), (key1594, -1), (key1690, -1), (key1594, 1), (key1634, 1), (key1557, 1), (key1684, 1), (key1557, -1), (key1625, -1), (key1576, -1), (key1682, -1), (key1549, 1), (key1682, 1), (key1568, 1), (key1617, 1), (key1541, -1), (key1617, -1)]

theorem rawRowCheck5198 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block2.form0 = rawRow5198 := by decide +kernel

def row5198 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5198 : row5198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5198 := by decide +kernel

theorem rowEval5198 (x : Key → ℝ) : Integer.Sparse.eval row5198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5198, Integer.Sparse.eval_collectBalanced, rawRowCheck5198]

def rawRow5199 : Integer.Sparse Key := [(key1355, -1), (key1327, -1), (key1327, 2), (key1352, -1), (key1319, -1), (key1352, 2), (key1299, 2), (key1319, -1), (key1299, -1), (key1311, 2), (key1311, -1), (key1291, -1), (key1481, 1), (key1445, 1), (key1445, -2), (key1473, 1), (key1427, 1), (key1473, -2), (key1394, -2), (key1427, 1), (key1394, 1), (key1419, -2), (key1419, 1), (key1386, 1), (key1690, -1), (key1594, -1), (key1634, 1), (key1594, 1), (key1684, 1), (key1557, 1), (key1625, -1), (key1557, -1), (key1682, -1), (key1576, -1), (key1682, 1), (key1549, 1), (key1617, 1), (key1568, 1), (key1617, -1), (key1541, -1)]

theorem rawRowCheck5199 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block2.form0 = rawRow5199 := by decide +kernel

def row5199 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5199 : row5199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5199 := by decide +kernel

theorem rowEval5199 (x : Key → ℝ) : Integer.Sparse.eval row5199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5199, Integer.Sparse.eval_collectBalanced, rawRowCheck5199]

def rawRow5200 : Integer.Sparse Key := [(key1386, -1), (key1394, -1), (key1394, 2), (key1541, -1), (key1549, -1), (key1541, 2), (key1557, 2), (key1549, -1), (key1557, -1), (key1897, 2), (key1897, -1), (key1900, -1), (key1291, 1), (key1299, 1), (key1299, -2), (key1568, 1), (key1576, 1), (key1568, -2), (key1594, -2), (key1576, 1), (key1594, 1), (key1904, -2), (key1904, 1), (key1912, 1), (key1311, -1), (key1327, -1), (key1319, 1), (key1327, 1), (key1419, 1), (key1445, 1), (key1427, -1), (key1445, -1), (key1617, -1), (key1625, -1), (key1617, 1), (key1634, 1), (key1919, 1), (key1921, 1), (key1919, -1), (key1927, -1)]

theorem rawRowCheck5200 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form0 = rawRow5200 := by decide +kernel

def row5200 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5200 : row5200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5200 := by decide +kernel

theorem rowEval5200 (x : Key → ℝ) : Integer.Sparse.eval row5200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5200, Integer.Sparse.eval_collectBalanced, rawRowCheck5200]

def rawRow5201 : Integer.Sparse Key := [(key1394, -1), (key1386, -1), (key1394, 2), (key1549, -1), (key1541, -1), (key1557, 2), (key1541, 2), (key1557, -1), (key1549, -1), (key1897, 2), (key1900, -1), (key1897, -1), (key1299, 1), (key1291, 1), (key1299, -2), (key1576, 1), (key1568, 1), (key1594, -2), (key1568, -2), (key1594, 1), (key1576, 1), (key1904, -2), (key1912, 1), (key1904, 1), (key1327, -1), (key1311, -1), (key1327, 1), (key1319, 1), (key1445, 1), (key1419, 1), (key1445, -1), (key1427, -1), (key1625, -1), (key1617, -1), (key1634, 1), (key1617, 1), (key1921, 1), (key1919, 1), (key1927, -1), (key1919, -1)]

theorem rawRowCheck5201 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form0 = rawRow5201 := by decide +kernel

def row5201 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5201 : row5201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5201 := by decide +kernel

theorem rowEval5201 (x : Key → ℝ) : Integer.Sparse.eval row5201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5201, Integer.Sparse.eval_collectBalanced, rawRowCheck5201]

def rawRow5202 : Integer.Sparse Key := [(key1394, -1), (key1394, -1), (key1386, 2), (key1557, -1), (key1557, -1), (key1549, 2), (key1549, 2), (key1541, -1), (key1541, -1), (key1900, 2), (key1897, -1), (key1897, -1), (key1299, 1), (key1299, 1), (key1291, -2), (key1594, 1), (key1594, 1), (key1576, -2), (key1576, -2), (key1568, 1), (key1568, 1), (key1912, -2), (key1904, 1), (key1904, 1), (key1319, -1), (key1319, -1), (key1311, 1), (key1311, 1), (key1427, 1), (key1427, 1), (key1419, -1), (key1419, -1), (key1634, -1), (key1634, -1), (key1625, 1), (key1625, 1), (key1927, 1), (key1927, 1), (key1921, -1), (key1921, -1)]

theorem rawRowCheck5202 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form0 = rawRow5202 := by decide +kernel

def row5202 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 2), (key1541, -2), (key1549, 4), (key1557, -2), (key1568, 2), (key1576, -4), (key1594, 2), (key1625, 2), (key1634, -2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck5202 : row5202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5202 := by decide +kernel

theorem rowEval5202 (x : Key → ℝ) : Integer.Sparse.eval row5202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5202, Integer.Sparse.eval_collectBalanced, rawRowCheck5202]

def rawRow5203 : Integer.Sparse Key := [(key1541, -1), (key1549, -1), (key1897, 2), (key1386, -1), (key1394, -1), (key1541, 2), (key1557, 2), (key1897, -1), (key1900, -1), (key1394, 2), (key1549, -1), (key1557, -1), (key1568, 1), (key1576, 1), (key1904, -2), (key1291, 1), (key1299, 1), (key1568, -2), (key1594, -2), (key1904, 1), (key1912, 1), (key1299, -2), (key1576, 1), (key1594, 1), (key1617, -1), (key1625, -1), (key1919, 1), (key1921, 1), (key1617, 1), (key1634, 1), (key1919, -1), (key1927, -1), (key1311, -1), (key1327, -1), (key1419, 1), (key1445, 1), (key1319, 1), (key1327, 1), (key1427, -1), (key1445, -1)]

theorem rawRowCheck5203 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form0 = rawRow5203 := by decide +kernel

def row5203 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5203 : row5203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5203 := by decide +kernel

theorem rowEval5203 (x : Key → ℝ) : Integer.Sparse.eval row5203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5203, Integer.Sparse.eval_collectBalanced, rawRowCheck5203]

def rawRow5204 : Integer.Sparse Key := [(key1549, -1), (key1541, -1), (key1897, 2), (key1394, -1), (key1386, -1), (key1557, 2), (key1541, 2), (key1900, -1), (key1897, -1), (key1394, 2), (key1557, -1), (key1549, -1), (key1576, 1), (key1568, 1), (key1904, -2), (key1299, 1), (key1291, 1), (key1594, -2), (key1568, -2), (key1912, 1), (key1904, 1), (key1299, -2), (key1594, 1), (key1576, 1), (key1625, -1), (key1617, -1), (key1921, 1), (key1919, 1), (key1634, 1), (key1617, 1), (key1927, -1), (key1919, -1), (key1327, -1), (key1311, -1), (key1445, 1), (key1419, 1), (key1327, 1), (key1319, 1), (key1445, -1), (key1427, -1)]

theorem rawRowCheck5204 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form0 = rawRow5204 := by decide +kernel

def row5204 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5204 : row5204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5204 := by decide +kernel

theorem rowEval5204 (x : Key → ℝ) : Integer.Sparse.eval row5204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5204, Integer.Sparse.eval_collectBalanced, rawRowCheck5204]

def rawRow5205 : Integer.Sparse Key := [(key1541, -1), (key1897, -1), (key1549, 2), (key1541, -1), (key1897, -1), (key1386, 2), (key1900, 2), (key1394, -1), (key1557, -1), (key1549, 2), (key1394, -1), (key1557, -1), (key1568, 1), (key1904, 1), (key1576, -2), (key1568, 1), (key1904, 1), (key1291, -2), (key1912, -2), (key1299, 1), (key1594, 1), (key1576, -2), (key1299, 1), (key1594, 1), (key1419, -1), (key1921, -1), (key1427, 1), (key1625, 1), (key1311, 1), (key1927, 1), (key1319, -1), (key1634, -1), (key1419, -1), (key1921, -1), (key1311, 1), (key1927, 1), (key1427, 1), (key1625, 1), (key1319, -1), (key1634, -1)]

theorem rawRowCheck5205 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form0 = rawRow5205 := by decide +kernel

def row5205 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 2), (key1541, -2), (key1549, 4), (key1557, -2), (key1568, 2), (key1576, -4), (key1594, 2), (key1625, 2), (key1634, -2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck5205 : row5205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5205 := by decide +kernel

theorem rowEval5205 (x : Key → ℝ) : Integer.Sparse.eval row5205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5205, Integer.Sparse.eval_collectBalanced, rawRowCheck5205]

def rawRow5206 : Integer.Sparse Key := [(key1897, -1), (key1541, -1), (key1549, 2), (key1897, -1), (key1541, -1), (key1900, 2), (key1386, 2), (key1557, -1), (key1394, -1), (key1549, 2), (key1557, -1), (key1394, -1), (key1904, 1), (key1568, 1), (key1576, -2), (key1904, 1), (key1568, 1), (key1912, -2), (key1291, -2), (key1594, 1), (key1299, 1), (key1576, -2), (key1594, 1), (key1299, 1), (key1921, -1), (key1419, -1), (key1625, 1), (key1427, 1), (key1927, 1), (key1311, 1), (key1634, -1), (key1319, -1), (key1921, -1), (key1419, -1), (key1927, 1), (key1311, 1), (key1625, 1), (key1427, 1), (key1634, -1), (key1319, -1)]

theorem rawRowCheck5206 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form0 = rawRow5206 := by decide +kernel

def row5206 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 2), (key1541, -2), (key1549, 4), (key1557, -2), (key1568, 2), (key1576, -4), (key1594, 2), (key1625, 2), (key1634, -2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck5206 : row5206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5206 := by decide +kernel

theorem rowEval5206 (x : Key → ℝ) : Integer.Sparse.eval row5206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5206, Integer.Sparse.eval_collectBalanced, rawRowCheck5206]

def rawRow5207 : Integer.Sparse Key := [(key1549, -1), (key1897, -1), (key1541, 2), (key1557, -1), (key1900, -1), (key1394, 2), (key1897, 2), (key1386, -1), (key1541, -1), (key1557, 2), (key1394, -1), (key1549, -1), (key1576, 1), (key1904, 1), (key1568, -2), (key1594, 1), (key1912, 1), (key1299, -2), (key1904, -2), (key1291, 1), (key1568, 1), (key1594, -2), (key1299, 1), (key1576, 1), (key1427, -1), (key1919, -1), (key1419, 1), (key1617, 1), (key1319, 1), (key1919, 1), (key1311, -1), (key1617, -1), (key1445, -1), (key1927, -1), (key1327, 1), (key1921, 1), (key1445, 1), (key1634, 1), (key1327, -1), (key1625, -1)]

theorem rawRowCheck5207 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form0 = rawRow5207 := by decide +kernel

def row5207 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5207 : row5207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5207 := by decide +kernel

theorem rowEval5207 (x : Key → ℝ) : Integer.Sparse.eval row5207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5207, Integer.Sparse.eval_collectBalanced, rawRowCheck5207]

def rawRow5208 : Integer.Sparse Key := [(key1897, -1), (key1549, -1), (key1541, 2), (key1900, -1), (key1557, -1), (key1897, 2), (key1394, 2), (key1541, -1), (key1386, -1), (key1557, 2), (key1549, -1), (key1394, -1), (key1904, 1), (key1576, 1), (key1568, -2), (key1912, 1), (key1594, 1), (key1904, -2), (key1299, -2), (key1568, 1), (key1291, 1), (key1594, -2), (key1576, 1), (key1299, 1), (key1919, -1), (key1427, -1), (key1617, 1), (key1419, 1), (key1919, 1), (key1319, 1), (key1617, -1), (key1311, -1), (key1927, -1), (key1445, -1), (key1921, 1), (key1327, 1), (key1634, 1), (key1445, 1), (key1625, -1), (key1327, -1)]

theorem rawRowCheck5208 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form0 = rawRow5208 := by decide +kernel

def row5208 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5208 : row5208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5208 := by decide +kernel

theorem rowEval5208 (x : Key → ℝ) : Integer.Sparse.eval row5208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5208, Integer.Sparse.eval_collectBalanced, rawRowCheck5208]

def rawRow5209 : Integer.Sparse Key := [(key1557, -1), (key1557, -1), (key1900, 2), (key1394, -1), (key1394, -1), (key1549, 2), (key1549, 2), (key1897, -1), (key1897, -1), (key1386, 2), (key1541, -1), (key1541, -1), (key1594, 1), (key1594, 1), (key1912, -2), (key1299, 1), (key1299, 1), (key1576, -2), (key1576, -2), (key1904, 1), (key1904, 1), (key1291, -2), (key1568, 1), (key1568, 1), (key1634, -1), (key1634, -1), (key1927, 1), (key1927, 1), (key1625, 1), (key1625, 1), (key1921, -1), (key1921, -1), (key1319, -1), (key1319, -1), (key1427, 1), (key1427, 1), (key1311, 1), (key1311, 1), (key1419, -1), (key1419, -1)]

theorem rawRowCheck5209 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form0 = rawRow5209 := by decide +kernel

def row5209 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 2), (key1541, -2), (key1549, 4), (key1557, -2), (key1568, 2), (key1576, -4), (key1594, 2), (key1625, 2), (key1634, -2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck5209 : row5209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5209 := by decide +kernel

theorem rowEval5209 (x : Key → ℝ) : Integer.Sparse.eval row5209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5209, Integer.Sparse.eval_collectBalanced, rawRowCheck5209]

def rawRow5210 : Integer.Sparse Key := [(key1557, -1), (key1900, -1), (key1557, 2), (key1549, -1), (key1897, -1), (key1394, 2), (key1897, 2), (key1394, -1), (key1549, -1), (key1541, 2), (key1386, -1), (key1541, -1), (key1594, 1), (key1912, 1), (key1594, -2), (key1576, 1), (key1904, 1), (key1299, -2), (key1904, -2), (key1299, 1), (key1576, 1), (key1568, -2), (key1291, 1), (key1568, 1), (key1445, -1), (key1927, -1), (key1445, 1), (key1634, 1), (key1327, 1), (key1921, 1), (key1327, -1), (key1625, -1), (key1427, -1), (key1919, -1), (key1319, 1), (key1919, 1), (key1419, 1), (key1617, 1), (key1311, -1), (key1617, -1)]

theorem rawRowCheck5210 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form0 = rawRow5210 := by decide +kernel

def row5210 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5210 : row5210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5210 := by decide +kernel

theorem rowEval5210 (x : Key → ℝ) : Integer.Sparse.eval row5210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5210, Integer.Sparse.eval_collectBalanced, rawRowCheck5210]

def rawRow5211 : Integer.Sparse Key := [(key1900, -1), (key1557, -1), (key1557, 2), (key1897, -1), (key1549, -1), (key1897, 2), (key1394, 2), (key1549, -1), (key1394, -1), (key1541, 2), (key1541, -1), (key1386, -1), (key1912, 1), (key1594, 1), (key1594, -2), (key1904, 1), (key1576, 1), (key1904, -2), (key1299, -2), (key1576, 1), (key1299, 1), (key1568, -2), (key1568, 1), (key1291, 1), (key1927, -1), (key1445, -1), (key1634, 1), (key1445, 1), (key1921, 1), (key1327, 1), (key1625, -1), (key1327, -1), (key1919, -1), (key1427, -1), (key1919, 1), (key1319, 1), (key1617, 1), (key1419, 1), (key1617, -1), (key1311, -1)]

theorem rawRowCheck5211 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form0 = rawRow5211 := by decide +kernel

def row5211 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5211 : row5211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5211 := by decide +kernel

theorem rowEval5211 (x : Key → ℝ) : Integer.Sparse.eval row5211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5211, Integer.Sparse.eval_collectBalanced, rawRowCheck5211]

def rawRow5212 : Integer.Sparse Key := [(key1419, -1), (key1473, -1), (key1427, 2), (key1617, -1), (key1682, -1), (key1568, 2), (key1684, 2), (key1576, -1), (key1625, -1), (key1919, 2), (key1904, -1), (key1921, -1), (key1311, 1), (key1352, 1), (key1319, -2), (key1617, 1), (key1682, 1), (key1541, -2), (key1690, -2), (key1549, 1), (key1634, 1), (key1919, -2), (key1897, 1), (key1927, 1), (key1291, -1), (key1355, -1), (key1299, 1), (key1327, 1), (key1386, 1), (key1481, 1), (key1394, -1), (key1445, -1), (key1568, -1), (key1684, -1), (key1541, 1), (key1690, 1), (key1904, 1), (key1921, 1), (key1897, -1), (key1927, -1)]

theorem rawRowCheck5212 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block2.form0 = rawRow5212 := by decide +kernel

def row5212 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5212 : row5212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5212 := by decide +kernel

theorem rowEval5212 (x : Key → ℝ) : Integer.Sparse.eval row5212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5212, Integer.Sparse.eval_collectBalanced, rawRowCheck5212]

def rawRow5213 : Integer.Sparse Key := [(key1473, -1), (key1419, -1), (key1427, 2), (key1682, -1), (key1617, -1), (key1684, 2), (key1568, 2), (key1625, -1), (key1576, -1), (key1919, 2), (key1921, -1), (key1904, -1), (key1352, 1), (key1311, 1), (key1319, -2), (key1682, 1), (key1617, 1), (key1690, -2), (key1541, -2), (key1634, 1), (key1549, 1), (key1919, -2), (key1927, 1), (key1897, 1), (key1355, -1), (key1291, -1), (key1327, 1), (key1299, 1), (key1481, 1), (key1386, 1), (key1445, -1), (key1394, -1), (key1684, -1), (key1568, -1), (key1690, 1), (key1541, 1), (key1921, 1), (key1904, 1), (key1927, -1), (key1897, -1)]

theorem rawRowCheck5213 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block2.form0 = rawRow5213 := by decide +kernel

def row5213 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5213 : row5213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5213 := by decide +kernel

theorem rowEval5213 (x : Key → ℝ) : Integer.Sparse.eval row5213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5213, Integer.Sparse.eval_collectBalanced, rawRowCheck5213]

def rawRow5214 : Integer.Sparse Key := [(key1427, -1), (key1473, -1), (key1419, 2), (key1625, -1), (key1684, -1), (key1576, 2), (key1682, 2), (key1568, -1), (key1617, -1), (key1921, 2), (key1904, -1), (key1919, -1), (key1319, 1), (key1352, 1), (key1311, -2), (key1634, 1), (key1690, 1), (key1549, -2), (key1682, -2), (key1541, 1), (key1617, 1), (key1927, -2), (key1897, 1), (key1919, 1), (key1299, -1), (key1352, -1), (key1291, 1), (key1311, 1), (key1394, 1), (key1473, 1), (key1386, -1), (key1419, -1), (key1594, -1), (key1690, -1), (key1557, 1), (key1684, 1), (key1912, 1), (key1927, 1), (key1900, -1), (key1921, -1)]

theorem rawRowCheck5214 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form0 = rawRow5214 := by decide +kernel

def row5214 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5214 : row5214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5214 := by decide +kernel

theorem rowEval5214 (x : Key → ℝ) : Integer.Sparse.eval row5214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5214, Integer.Sparse.eval_collectBalanced, rawRowCheck5214]

def rawRow5215 : Integer.Sparse Key := [(key1473, -1), (key1427, -1), (key1419, 2), (key1684, -1), (key1625, -1), (key1682, 2), (key1576, 2), (key1617, -1), (key1568, -1), (key1921, 2), (key1919, -1), (key1904, -1), (key1352, 1), (key1319, 1), (key1311, -2), (key1690, 1), (key1634, 1), (key1682, -2), (key1549, -2), (key1617, 1), (key1541, 1), (key1927, -2), (key1919, 1), (key1897, 1), (key1352, -1), (key1299, -1), (key1311, 1), (key1291, 1), (key1473, 1), (key1394, 1), (key1419, -1), (key1386, -1), (key1690, -1), (key1594, -1), (key1684, 1), (key1557, 1), (key1927, 1), (key1912, 1), (key1921, -1), (key1900, -1)]

theorem rawRowCheck5215 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form0 = rawRow5215 := by decide +kernel

def row5215 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5215 : row5215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5215 := by decide +kernel

theorem rowEval5215 (x : Key → ℝ) : Integer.Sparse.eval row5215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5215, Integer.Sparse.eval_collectBalanced, rawRowCheck5215]

def rawRow5216 : Integer.Sparse Key := [(key1568, -1), (key1904, -1), (key1576, 2), (key1617, -1), (key1919, -1), (key1419, 2), (key1921, 2), (key1427, -1), (key1625, -1), (key1682, 2), (key1473, -1), (key1684, -1), (key1541, 1), (key1897, 1), (key1549, -2), (key1617, 1), (key1919, 1), (key1311, -2), (key1927, -2), (key1319, 1), (key1634, 1), (key1682, -2), (key1352, 1), (key1690, 1), (key1386, -1), (key1900, -1), (key1394, 1), (key1557, 1), (key1291, 1), (key1912, 1), (key1299, -1), (key1594, -1), (key1419, -1), (key1921, -1), (key1311, 1), (key1927, 1), (key1473, 1), (key1684, 1), (key1352, -1), (key1690, -1)]

theorem rawRowCheck5216 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form0 = rawRow5216 := by decide +kernel

def row5216 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5216 : row5216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5216 := by decide +kernel

theorem rowEval5216 (x : Key → ℝ) : Integer.Sparse.eval row5216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5216, Integer.Sparse.eval_collectBalanced, rawRowCheck5216]

def rawRow5217 : Integer.Sparse Key := [(key1904, -1), (key1568, -1), (key1576, 2), (key1919, -1), (key1617, -1), (key1921, 2), (key1419, 2), (key1625, -1), (key1427, -1), (key1682, 2), (key1684, -1), (key1473, -1), (key1897, 1), (key1541, 1), (key1549, -2), (key1919, 1), (key1617, 1), (key1927, -2), (key1311, -2), (key1634, 1), (key1319, 1), (key1682, -2), (key1690, 1), (key1352, 1), (key1900, -1), (key1386, -1), (key1557, 1), (key1394, 1), (key1912, 1), (key1291, 1), (key1594, -1), (key1299, -1), (key1921, -1), (key1419, -1), (key1927, 1), (key1311, 1), (key1684, 1), (key1473, 1), (key1690, -1), (key1352, -1)]

theorem rawRowCheck5217 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form0 = rawRow5217 := by decide +kernel

def row5217 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5217 : row5217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5217 := by decide +kernel

theorem rowEval5217 (x : Key → ℝ) : Integer.Sparse.eval row5217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5217, Integer.Sparse.eval_collectBalanced, rawRowCheck5217]

def rawRow5218 : Integer.Sparse Key := [(key1576, -1), (key1904, -1), (key1568, 2), (key1625, -1), (key1921, -1), (key1427, 2), (key1919, 2), (key1419, -1), (key1617, -1), (key1684, 2), (key1473, -1), (key1682, -1), (key1549, 1), (key1897, 1), (key1541, -2), (key1634, 1), (key1927, 1), (key1319, -2), (key1919, -2), (key1311, 1), (key1617, 1), (key1690, -2), (key1352, 1), (key1682, 1), (key1394, -1), (key1897, -1), (key1386, 1), (key1541, 1), (key1299, 1), (key1904, 1), (key1291, -1), (key1568, -1), (key1445, -1), (key1927, -1), (key1327, 1), (key1921, 1), (key1481, 1), (key1690, 1), (key1355, -1), (key1684, -1)]

theorem rawRowCheck5218 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block2.form0 = rawRow5218 := by decide +kernel

def row5218 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5218 : row5218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5218 := by decide +kernel

theorem rowEval5218 (x : Key → ℝ) : Integer.Sparse.eval row5218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5218, Integer.Sparse.eval_collectBalanced, rawRowCheck5218]

def rawRow5219 : Integer.Sparse Key := [(key1904, -1), (key1576, -1), (key1568, 2), (key1921, -1), (key1625, -1), (key1919, 2), (key1427, 2), (key1617, -1), (key1419, -1), (key1684, 2), (key1682, -1), (key1473, -1), (key1897, 1), (key1549, 1), (key1541, -2), (key1927, 1), (key1634, 1), (key1919, -2), (key1319, -2), (key1617, 1), (key1311, 1), (key1690, -2), (key1682, 1), (key1352, 1), (key1897, -1), (key1394, -1), (key1541, 1), (key1386, 1), (key1904, 1), (key1299, 1), (key1568, -1), (key1291, -1), (key1927, -1), (key1445, -1), (key1921, 1), (key1327, 1), (key1690, 1), (key1481, 1), (key1684, -1), (key1355, -1)]

theorem rawRowCheck5219 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block2.form0 = rawRow5219 := by decide +kernel

def row5219 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5219 : row5219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5219 := by decide +kernel

theorem rowEval5219 (x : Key → ℝ) : Integer.Sparse.eval row5219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5219, Integer.Sparse.eval_collectBalanced, rawRowCheck5219]

def rawRow5220 : Integer.Sparse Key := [(key1617, -1), (key1682, -1), (key1919, 2), (key1419, -1), (key1473, -1), (key1568, 2), (key1684, 2), (key1904, -1), (key1921, -1), (key1427, 2), (key1576, -1), (key1625, -1), (key1617, 1), (key1682, 1), (key1919, -2), (key1311, 1), (key1352, 1), (key1541, -2), (key1690, -2), (key1897, 1), (key1927, 1), (key1319, -2), (key1549, 1), (key1634, 1), (key1568, -1), (key1684, -1), (key1904, 1), (key1921, 1), (key1541, 1), (key1690, 1), (key1897, -1), (key1927, -1), (key1291, -1), (key1355, -1), (key1386, 1), (key1481, 1), (key1299, 1), (key1327, 1), (key1394, -1), (key1445, -1)]

theorem rawRowCheck5220 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block2.form0 = rawRow5220 := by decide +kernel

def row5220 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5220 : row5220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5220 := by decide +kernel

theorem rowEval5220 (x : Key → ℝ) : Integer.Sparse.eval row5220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5220, Integer.Sparse.eval_collectBalanced, rawRowCheck5220]

def rawRow5221 : Integer.Sparse Key := [(key1682, -1), (key1617, -1), (key1919, 2), (key1473, -1), (key1419, -1), (key1684, 2), (key1568, 2), (key1921, -1), (key1904, -1), (key1427, 2), (key1625, -1), (key1576, -1), (key1682, 1), (key1617, 1), (key1919, -2), (key1352, 1), (key1311, 1), (key1690, -2), (key1541, -2), (key1927, 1), (key1897, 1), (key1319, -2), (key1634, 1), (key1549, 1), (key1684, -1), (key1568, -1), (key1921, 1), (key1904, 1), (key1690, 1), (key1541, 1), (key1927, -1), (key1897, -1), (key1355, -1), (key1291, -1), (key1481, 1), (key1386, 1), (key1327, 1), (key1299, 1), (key1445, -1), (key1394, -1)]

theorem rawRowCheck5221 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block2.form0 = rawRow5221 := by decide +kernel

def row5221 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5221 : row5221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5221 := by decide +kernel

theorem rowEval5221 (x : Key → ℝ) : Integer.Sparse.eval row5221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5221, Integer.Sparse.eval_collectBalanced, rawRowCheck5221]

def rawRow5222 : Integer.Sparse Key := [(key1617, -1), (key1919, -1), (key1682, 2), (key1568, -1), (key1904, -1), (key1419, 2), (key1921, 2), (key1473, -1), (key1684, -1), (key1576, 2), (key1427, -1), (key1625, -1), (key1617, 1), (key1919, 1), (key1682, -2), (key1541, 1), (key1897, 1), (key1311, -2), (key1927, -2), (key1352, 1), (key1690, 1), (key1549, -2), (key1319, 1), (key1634, 1), (key1419, -1), (key1921, -1), (key1473, 1), (key1684, 1), (key1311, 1), (key1927, 1), (key1352, -1), (key1690, -1), (key1386, -1), (key1900, -1), (key1291, 1), (key1912, 1), (key1394, 1), (key1557, 1), (key1299, -1), (key1594, -1)]

theorem rawRowCheck5222 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form0 = rawRow5222 := by decide +kernel

def row5222 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5222 : row5222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5222 := by decide +kernel

theorem rowEval5222 (x : Key → ℝ) : Integer.Sparse.eval row5222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5222, Integer.Sparse.eval_collectBalanced, rawRowCheck5222]

def rawRow5223 : Integer.Sparse Key := [(key1919, -1), (key1617, -1), (key1682, 2), (key1904, -1), (key1568, -1), (key1921, 2), (key1419, 2), (key1684, -1), (key1473, -1), (key1576, 2), (key1625, -1), (key1427, -1), (key1919, 1), (key1617, 1), (key1682, -2), (key1897, 1), (key1541, 1), (key1927, -2), (key1311, -2), (key1690, 1), (key1352, 1), (key1549, -2), (key1634, 1), (key1319, 1), (key1921, -1), (key1419, -1), (key1684, 1), (key1473, 1), (key1927, 1), (key1311, 1), (key1690, -1), (key1352, -1), (key1900, -1), (key1386, -1), (key1912, 1), (key1291, 1), (key1557, 1), (key1394, 1), (key1594, -1), (key1299, -1)]

theorem rawRowCheck5223 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form0 = rawRow5223 := by decide +kernel

def row5223 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5223 : row5223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5223 := by decide +kernel

theorem rowEval5223 (x : Key → ℝ) : Integer.Sparse.eval row5223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5223, Integer.Sparse.eval_collectBalanced, rawRowCheck5223]

def rawRow5224 : Integer.Sparse Key := [(key1625, -1), (key1684, -1), (key1921, 2), (key1427, -1), (key1473, -1), (key1576, 2), (key1682, 2), (key1904, -1), (key1919, -1), (key1419, 2), (key1568, -1), (key1617, -1), (key1634, 1), (key1690, 1), (key1927, -2), (key1319, 1), (key1352, 1), (key1549, -2), (key1682, -2), (key1897, 1), (key1919, 1), (key1311, -2), (key1541, 1), (key1617, 1), (key1594, -1), (key1690, -1), (key1912, 1), (key1927, 1), (key1557, 1), (key1684, 1), (key1900, -1), (key1921, -1), (key1299, -1), (key1352, -1), (key1394, 1), (key1473, 1), (key1291, 1), (key1311, 1), (key1386, -1), (key1419, -1)]

theorem rawRowCheck5224 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form0 = rawRow5224 := by decide +kernel

def row5224 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5224 : row5224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5224 := by decide +kernel

theorem rowEval5224 (x : Key → ℝ) : Integer.Sparse.eval row5224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5224, Integer.Sparse.eval_collectBalanced, rawRowCheck5224]

def rawRow5225 : Integer.Sparse Key := [(key1684, -1), (key1625, -1), (key1921, 2), (key1473, -1), (key1427, -1), (key1682, 2), (key1576, 2), (key1919, -1), (key1904, -1), (key1419, 2), (key1617, -1), (key1568, -1), (key1690, 1), (key1634, 1), (key1927, -2), (key1352, 1), (key1319, 1), (key1682, -2), (key1549, -2), (key1919, 1), (key1897, 1), (key1311, -2), (key1617, 1), (key1541, 1), (key1690, -1), (key1594, -1), (key1927, 1), (key1912, 1), (key1684, 1), (key1557, 1), (key1921, -1), (key1900, -1), (key1352, -1), (key1299, -1), (key1473, 1), (key1394, 1), (key1311, 1), (key1291, 1), (key1419, -1), (key1386, -1)]

theorem rawRowCheck5225 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form0 = rawRow5225 := by decide +kernel

def row5225 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck5225 : row5225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5225 := by decide +kernel

theorem rowEval5225 (x : Key → ℝ) : Integer.Sparse.eval row5225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5225, Integer.Sparse.eval_collectBalanced, rawRowCheck5225]

def rawRow5226 : Integer.Sparse Key := [(key1625, -1), (key1921, -1), (key1684, 2), (key1576, -1), (key1904, -1), (key1427, 2), (key1919, 2), (key1473, -1), (key1682, -1), (key1568, 2), (key1419, -1), (key1617, -1), (key1634, 1), (key1927, 1), (key1690, -2), (key1549, 1), (key1897, 1), (key1319, -2), (key1919, -2), (key1352, 1), (key1682, 1), (key1541, -2), (key1311, 1), (key1617, 1), (key1445, -1), (key1927, -1), (key1481, 1), (key1690, 1), (key1327, 1), (key1921, 1), (key1355, -1), (key1684, -1), (key1394, -1), (key1897, -1), (key1299, 1), (key1904, 1), (key1386, 1), (key1541, 1), (key1291, -1), (key1568, -1)]

theorem rawRowCheck5226 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block2.form0 = rawRow5226 := by decide +kernel

def row5226 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5226 : row5226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5226 := by decide +kernel

theorem rowEval5226 (x : Key → ℝ) : Integer.Sparse.eval row5226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5226, Integer.Sparse.eval_collectBalanced, rawRowCheck5226]

def rawRow5227 : Integer.Sparse Key := [(key1921, -1), (key1625, -1), (key1684, 2), (key1904, -1), (key1576, -1), (key1919, 2), (key1427, 2), (key1682, -1), (key1473, -1), (key1568, 2), (key1617, -1), (key1419, -1), (key1927, 1), (key1634, 1), (key1690, -2), (key1897, 1), (key1549, 1), (key1919, -2), (key1319, -2), (key1682, 1), (key1352, 1), (key1541, -2), (key1617, 1), (key1311, 1), (key1927, -1), (key1445, -1), (key1690, 1), (key1481, 1), (key1921, 1), (key1327, 1), (key1684, -1), (key1355, -1), (key1897, -1), (key1394, -1), (key1904, 1), (key1299, 1), (key1541, 1), (key1386, 1), (key1568, -1), (key1291, -1)]

theorem rawRowCheck5227 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block2.form0 = rawRow5227 := by decide +kernel

def row5227 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

theorem rowCheck5227 : row5227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5227 := by decide +kernel

theorem rowEval5227 (x : Key → ℝ) : Integer.Sparse.eval row5227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5227, Integer.Sparse.eval_collectBalanced, rawRowCheck5227]

def rawRow5228 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key241, 2), (key248, -1), (key253, -1), (key248, 2), (key263, 2), (key253, -1), (key263, -1), (key277, 2), (key277, -1), (key278, -1), (key302, 1), (key307, 1), (key307, -2), (key316, 1), (key321, 1), (key316, -2), (key331, -2), (key321, 1), (key331, 1), (key346, -2), (key346, 1), (key347, 1), (key385, -1), (key400, -1), (key390, 1), (key400, 1), (key406, 1), (key421, 1), (key411, -1), (key421, -1), (key435, -1), (key445, -1), (key435, 1), (key453, 1), (key487, 1), (key488, 1), (key487, -1), (key489, -1)]

theorem rawRowCheck5228 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block2.form1 = rawRow5228 := by decide +kernel

def row5228 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

theorem rowCheck5228 : row5228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5228 := by decide +kernel

theorem rowEval5228 (x : Key → ℝ) : Integer.Sparse.eval row5228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5228, Integer.Sparse.eval_collectBalanced, rawRowCheck5228]

def rawRow5229 : Integer.Sparse Key := [(key241, -1), (key236, -1), (key241, 2), (key253, -1), (key248, -1), (key263, 2), (key248, 2), (key263, -1), (key253, -1), (key277, 2), (key278, -1), (key277, -1), (key307, 1), (key302, 1), (key307, -2), (key321, 1), (key316, 1), (key331, -2), (key316, -2), (key331, 1), (key321, 1), (key346, -2), (key347, 1), (key346, 1), (key400, -1), (key385, -1), (key400, 1), (key390, 1), (key421, 1), (key406, 1), (key421, -1), (key411, -1), (key445, -1), (key435, -1), (key453, 1), (key435, 1), (key488, 1), (key487, 1), (key489, -1), (key487, -1)]

theorem rawRowCheck5229 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block2.form1 = rawRow5229 := by decide +kernel

def row5229 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

theorem rowCheck5229 : row5229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5229 := by decide +kernel

theorem rowEval5229 (x : Key → ℝ) : Integer.Sparse.eval row5229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5229, Integer.Sparse.eval_collectBalanced, rawRowCheck5229]

def rawRow5230 : Integer.Sparse Key := [(key241, -1), (key241, -1), (key236, 2), (key263, -1), (key263, -1), (key253, 2), (key253, 2), (key248, -1), (key248, -1), (key278, 2), (key277, -1), (key277, -1), (key307, 1), (key307, 1), (key302, -2), (key331, 1), (key331, 1), (key321, -2), (key321, -2), (key316, 1), (key316, 1), (key347, -2), (key346, 1), (key346, 1), (key390, -1), (key390, -1), (key385, 1), (key385, 1), (key411, 1), (key411, 1), (key406, -1), (key406, -1), (key453, -1), (key453, -1), (key445, 1), (key445, 1), (key489, 1), (key489, 1), (key488, -1), (key488, -1)]

theorem rawRowCheck5230 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block2.form1 = rawRow5230 := by decide +kernel

def row5230 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key253, 4), (key263, -2), (key277, -2), (key278, 2), (key302, -2), (key307, 2), (key316, 2), (key321, -4), (key331, 2), (key346, 2), (key347, -2), (key385, 2), (key390, -2), (key406, -2), (key411, 2), (key445, 2), (key453, -2), (key488, -2), (key489, 2)]

theorem rowCheck5230 : row5230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5230 := by decide +kernel

theorem rowEval5230 (x : Key → ℝ) : Integer.Sparse.eval row5230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5230, Integer.Sparse.eval_collectBalanced, rawRowCheck5230]

def rawRow5231 : Integer.Sparse Key := [(key248, -1), (key253, -1), (key263, 2), (key236, -1), (key241, -1), (key248, 2), (key263, 2), (key277, -1), (key278, -1), (key241, 2), (key253, -1), (key263, -1), (key316, 1), (key321, 1), (key346, -2), (key302, 1), (key307, 1), (key316, -2), (key331, -2), (key346, 1), (key347, 1), (key307, -2), (key321, 1), (key331, 1), (key435, -1), (key445, -1), (key487, 1), (key488, 1), (key435, 1), (key453, 1), (key487, -1), (key489, -1), (key385, -1), (key400, -1), (key406, 1), (key421, 1), (key390, 1), (key400, 1), (key411, -1), (key421, -1)]

theorem rawRowCheck5231 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block2.form1 = rawRow5231 := by decide +kernel

def row5231 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 3), (key277, -1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

theorem rowCheck5231 : row5231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5231 := by decide +kernel

theorem rowEval5231 (x : Key → ℝ) : Integer.Sparse.eval row5231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5231, Integer.Sparse.eval_collectBalanced, rawRowCheck5231]

def rawRow5232 : Integer.Sparse Key := [(key253, -1), (key248, -1), (key263, 2), (key241, -1), (key236, -1), (key263, 2), (key248, 2), (key278, -1), (key277, -1), (key241, 2), (key263, -1), (key253, -1), (key321, 1), (key316, 1), (key346, -2), (key307, 1), (key302, 1), (key331, -2), (key316, -2), (key347, 1), (key346, 1), (key307, -2), (key331, 1), (key321, 1), (key445, -1), (key435, -1), (key488, 1), (key487, 1), (key453, 1), (key435, 1), (key489, -1), (key487, -1), (key400, -1), (key385, -1), (key421, 1), (key406, 1), (key400, 1), (key390, 1), (key421, -1), (key411, -1)]

theorem rawRowCheck5232 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block2.form1 = rawRow5232 := by decide +kernel

def row5232 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 3), (key277, -1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

theorem rowCheck5232 : row5232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5232 := by decide +kernel

theorem rowEval5232 (x : Key → ℝ) : Integer.Sparse.eval row5232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5232, Integer.Sparse.eval_collectBalanced, rawRowCheck5232]

def rawRow5233 : Integer.Sparse Key := [(key248, -1), (key263, -1), (key253, 2), (key248, -1), (key263, -1), (key236, 2), (key278, 2), (key241, -1), (key263, -1), (key253, 2), (key241, -1), (key263, -1), (key316, 1), (key346, 1), (key321, -2), (key316, 1), (key346, 1), (key302, -2), (key347, -2), (key307, 1), (key331, 1), (key321, -2), (key307, 1), (key331, 1), (key406, -1), (key488, -1), (key411, 1), (key445, 1), (key385, 1), (key489, 1), (key390, -1), (key453, -1), (key406, -1), (key488, -1), (key385, 1), (key489, 1), (key411, 1), (key445, 1), (key390, -1), (key453, -1)]

theorem rawRowCheck5233 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block2.form1 = rawRow5233 := by decide +kernel

def row5233 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key253, 4), (key263, -4), (key278, 2), (key302, -2), (key307, 2), (key316, 2), (key321, -4), (key331, 2), (key346, 2), (key347, -2), (key385, 2), (key390, -2), (key406, -2), (key411, 2), (key445, 2), (key453, -2), (key488, -2), (key489, 2)]

theorem rowCheck5233 : row5233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5233 := by decide +kernel

theorem rowEval5233 (x : Key → ℝ) : Integer.Sparse.eval row5233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5233, Integer.Sparse.eval_collectBalanced, rawRowCheck5233]

def rawRow5234 : Integer.Sparse Key := [(key263, -1), (key248, -1), (key253, 2), (key263, -1), (key248, -1), (key278, 2), (key236, 2), (key263, -1), (key241, -1), (key253, 2), (key263, -1), (key241, -1), (key346, 1), (key316, 1), (key321, -2), (key346, 1), (key316, 1), (key347, -2), (key302, -2), (key331, 1), (key307, 1), (key321, -2), (key331, 1), (key307, 1), (key488, -1), (key406, -1), (key445, 1), (key411, 1), (key489, 1), (key385, 1), (key453, -1), (key390, -1), (key488, -1), (key406, -1), (key489, 1), (key385, 1), (key445, 1), (key411, 1), (key453, -1), (key390, -1)]

theorem rawRowCheck5234 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block2.form1 = rawRow5234 := by decide +kernel

def row5234 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key253, 4), (key263, -4), (key278, 2), (key302, -2), (key307, 2), (key316, 2), (key321, -4), (key331, 2), (key346, 2), (key347, -2), (key385, 2), (key390, -2), (key406, -2), (key411, 2), (key445, 2), (key453, -2), (key488, -2), (key489, 2)]

theorem rowCheck5234 : row5234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5234 := by decide +kernel

theorem rowEval5234 (x : Key → ℝ) : Integer.Sparse.eval row5234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5234, Integer.Sparse.eval_collectBalanced, rawRowCheck5234]

def rawRow5235 : Integer.Sparse Key := [(key253, -1), (key263, -1), (key248, 2), (key277, -1), (key278, -1), (key241, 2), (key263, 2), (key236, -1), (key248, -1), (key263, 2), (key241, -1), (key253, -1), (key321, 1), (key346, 1), (key316, -2), (key331, 1), (key347, 1), (key307, -2), (key346, -2), (key302, 1), (key316, 1), (key331, -2), (key307, 1), (key321, 1), (key411, -1), (key487, -1), (key406, 1), (key435, 1), (key390, 1), (key487, 1), (key385, -1), (key435, -1), (key421, -1), (key489, -1), (key400, 1), (key488, 1), (key421, 1), (key453, 1), (key400, -1), (key445, -1)]

theorem rawRowCheck5235 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block2.form1 = rawRow5235 := by decide +kernel

def row5235 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 3), (key277, -1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

theorem rowCheck5235 : row5235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5235 := by decide +kernel

theorem rowEval5235 (x : Key → ℝ) : Integer.Sparse.eval row5235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5235, Integer.Sparse.eval_collectBalanced, rawRowCheck5235]

def rawRow5236 : Integer.Sparse Key := [(key263, -1), (key253, -1), (key248, 2), (key278, -1), (key277, -1), (key263, 2), (key241, 2), (key248, -1), (key236, -1), (key263, 2), (key253, -1), (key241, -1), (key346, 1), (key321, 1), (key316, -2), (key347, 1), (key331, 1), (key346, -2), (key307, -2), (key316, 1), (key302, 1), (key331, -2), (key321, 1), (key307, 1), (key487, -1), (key411, -1), (key435, 1), (key406, 1), (key487, 1), (key390, 1), (key435, -1), (key385, -1), (key489, -1), (key421, -1), (key488, 1), (key400, 1), (key453, 1), (key421, 1), (key445, -1), (key400, -1)]

theorem rawRowCheck5236 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block2.form1 = rawRow5236 := by decide +kernel

def row5236 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 3), (key277, -1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

theorem rowCheck5236 : row5236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5236 := by decide +kernel

theorem rowEval5236 (x : Key → ℝ) : Integer.Sparse.eval row5236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5236, Integer.Sparse.eval_collectBalanced, rawRowCheck5236]

def rawRow5237 : Integer.Sparse Key := [(key277, -1), (key277, -1), (key278, 2), (key241, -1), (key241, -1), (key253, 2), (key253, 2), (key263, -1), (key263, -1), (key236, 2), (key248, -1), (key248, -1), (key331, 1), (key331, 1), (key347, -2), (key307, 1), (key307, 1), (key321, -2), (key321, -2), (key346, 1), (key346, 1), (key302, -2), (key316, 1), (key316, 1), (key453, -1), (key453, -1), (key489, 1), (key489, 1), (key445, 1), (key445, 1), (key488, -1), (key488, -1), (key390, -1), (key390, -1), (key411, 1), (key411, 1), (key385, 1), (key385, 1), (key406, -1), (key406, -1)]

theorem rawRowCheck5237 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block2.form1 = rawRow5237 := by decide +kernel

def row5237 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key253, 4), (key263, -2), (key277, -2), (key278, 2), (key302, -2), (key307, 2), (key316, 2), (key321, -4), (key331, 2), (key346, 2), (key347, -2), (key385, 2), (key390, -2), (key406, -2), (key411, 2), (key445, 2), (key453, -2), (key488, -2), (key489, 2)]

theorem rowCheck5237 : row5237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5237 := by decide +kernel

theorem rowEval5237 (x : Key → ℝ) : Integer.Sparse.eval row5237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5237, Integer.Sparse.eval_collectBalanced, rawRowCheck5237]

def rawRow5238 : Integer.Sparse Key := [(key277, -1), (key278, -1), (key277, 2), (key253, -1), (key263, -1), (key241, 2), (key263, 2), (key241, -1), (key253, -1), (key248, 2), (key236, -1), (key248, -1), (key331, 1), (key347, 1), (key331, -2), (key321, 1), (key346, 1), (key307, -2), (key346, -2), (key307, 1), (key321, 1), (key316, -2), (key302, 1), (key316, 1), (key421, -1), (key489, -1), (key421, 1), (key453, 1), (key400, 1), (key488, 1), (key400, -1), (key445, -1), (key411, -1), (key487, -1), (key390, 1), (key487, 1), (key406, 1), (key435, 1), (key385, -1), (key435, -1)]

theorem rawRowCheck5238 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block2.form1 = rawRow5238 := by decide +kernel

def row5238 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

theorem rowCheck5238 : row5238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5238 := by decide +kernel

theorem rowEval5238 (x : Key → ℝ) : Integer.Sparse.eval row5238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5238, Integer.Sparse.eval_collectBalanced, rawRowCheck5238]

def rawRow5239 : Integer.Sparse Key := [(key278, -1), (key277, -1), (key277, 2), (key263, -1), (key253, -1), (key263, 2), (key241, 2), (key253, -1), (key241, -1), (key248, 2), (key248, -1), (key236, -1), (key347, 1), (key331, 1), (key331, -2), (key346, 1), (key321, 1), (key346, -2), (key307, -2), (key321, 1), (key307, 1), (key316, -2), (key316, 1), (key302, 1), (key489, -1), (key421, -1), (key453, 1), (key421, 1), (key488, 1), (key400, 1), (key445, -1), (key400, -1), (key487, -1), (key411, -1), (key487, 1), (key390, 1), (key435, 1), (key406, 1), (key435, -1), (key385, -1)]

theorem rawRowCheck5239 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block2.form1 = rawRow5239 := by decide +kernel

def row5239 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

theorem rowCheck5239 : row5239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5239 := by decide +kernel

theorem rowEval5239 (x : Key → ℝ) : Integer.Sparse.eval row5239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5239, Integer.Sparse.eval_collectBalanced, rawRowCheck5239]

def rawRow5240 : Integer.Sparse Key := [(key302, -1), (key307, -1), (key307, 2), (key316, -1), (key321, -1), (key316, 2), (key346, 2), (key321, -1), (key346, -1), (key331, 2), (key331, -1), (key347, -1), (key236, 1), (key241, 1), (key241, -2), (key406, 1), (key411, 1), (key406, -2), (key421, -2), (key411, 1), (key421, 1), (key657, -2), (key657, 1), (key658, 1), (key248, -1), (key263, -1), (key253, 1), (key263, 1), (key316, 1), (key331, 1), (key321, -1), (key331, -1), (key435, -1), (key445, -1), (key435, 1), (key453, 1), (key660, 1), (key661, 1), (key660, -1), (key662, -1)]

theorem rawRowCheck5240 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form1 = rawRow5240 := by decide +kernel

def row5240 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -1), (key445, -1), (key453, 1), (key657, -1), (key658, 1), (key661, 1), (key662, -1)]

theorem rowCheck5240 : row5240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5240 := by decide +kernel

theorem rowEval5240 (x : Key → ℝ) : Integer.Sparse.eval row5240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5240, Integer.Sparse.eval_collectBalanced, rawRowCheck5240]

def rawRow5241 : Integer.Sparse Key := [(key307, -1), (key302, -1), (key307, 2), (key321, -1), (key316, -1), (key346, 2), (key316, 2), (key346, -1), (key321, -1), (key331, 2), (key347, -1), (key331, -1), (key241, 1), (key236, 1), (key241, -2), (key411, 1), (key406, 1), (key421, -2), (key406, -2), (key421, 1), (key411, 1), (key657, -2), (key658, 1), (key657, 1), (key263, -1), (key248, -1), (key263, 1), (key253, 1), (key331, 1), (key316, 1), (key331, -1), (key321, -1), (key445, -1), (key435, -1), (key453, 1), (key435, 1), (key661, 1), (key660, 1), (key662, -1), (key660, -1)]

theorem rawRowCheck5241 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form1 = rawRow5241 := by decide +kernel

def row5241 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -1), (key445, -1), (key453, 1), (key657, -1), (key658, 1), (key661, 1), (key662, -1)]

theorem rowCheck5241 : row5241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5241 := by decide +kernel

theorem rowEval5241 (x : Key → ℝ) : Integer.Sparse.eval row5241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5241, Integer.Sparse.eval_collectBalanced, rawRowCheck5241]

def rawRow5242 : Integer.Sparse Key := [(key307, -1), (key307, -1), (key302, 2), (key346, -1), (key346, -1), (key321, 2), (key321, 2), (key316, -1), (key316, -1), (key347, 2), (key331, -1), (key331, -1), (key241, 1), (key241, 1), (key236, -2), (key421, 1), (key421, 1), (key411, -2), (key411, -2), (key406, 1), (key406, 1), (key658, -2), (key657, 1), (key657, 1), (key253, -1), (key253, -1), (key248, 1), (key248, 1), (key321, 1), (key321, 1), (key316, -1), (key316, -1), (key453, -1), (key453, -1), (key445, 1), (key445, 1), (key662, 1), (key662, 1), (key661, -1), (key661, -1)]

theorem rawRowCheck5242 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form1 = rawRow5242 := by decide +kernel

def row5242 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key253, -2), (key302, 2), (key307, -2), (key316, -4), (key321, 6), (key331, -2), (key346, -2), (key347, 2), (key406, 2), (key411, -4), (key421, 2), (key445, 2), (key453, -2), (key657, 2), (key658, -2), (key661, -2), (key662, 2)]

theorem rowCheck5242 : row5242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5242 := by decide +kernel

theorem rowEval5242 (x : Key → ℝ) : Integer.Sparse.eval row5242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5242, Integer.Sparse.eval_collectBalanced, rawRowCheck5242]

def rawRow5243 : Integer.Sparse Key := [(key316, -1), (key321, -1), (key331, 2), (key302, -1), (key307, -1), (key316, 2), (key346, 2), (key331, -1), (key347, -1), (key307, 2), (key321, -1), (key346, -1), (key406, 1), (key411, 1), (key421, -2), (key236, 1), (key241, 1), (key406, -2), (key421, -2), (key657, 1), (key658, 1), (key241, -2), (key411, 1), (key421, 1), (key435, -1), (key445, -1), (key660, 1), (key661, 1), (key435, 1), (key453, 1), (key660, -1), (key662, -1), (key248, -1), (key263, -1), (key316, 1), (key331, 1), (key253, 1), (key263, 1), (key321, -1), (key331, -1)]

theorem rawRowCheck5243 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form1 = rawRow5243 := by decide +kernel

def row5243 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -3), (key445, -1), (key453, 1), (key657, 1), (key658, 1), (key661, 1), (key662, -1)]

theorem rowCheck5243 : row5243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5243 := by decide +kernel

theorem rowEval5243 (x : Key → ℝ) : Integer.Sparse.eval row5243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5243, Integer.Sparse.eval_collectBalanced, rawRowCheck5243]

def rawRow5244 : Integer.Sparse Key := [(key321, -1), (key316, -1), (key331, 2), (key307, -1), (key302, -1), (key346, 2), (key316, 2), (key347, -1), (key331, -1), (key307, 2), (key346, -1), (key321, -1), (key411, 1), (key406, 1), (key421, -2), (key241, 1), (key236, 1), (key421, -2), (key406, -2), (key658, 1), (key657, 1), (key241, -2), (key421, 1), (key411, 1), (key445, -1), (key435, -1), (key661, 1), (key660, 1), (key453, 1), (key435, 1), (key662, -1), (key660, -1), (key263, -1), (key248, -1), (key331, 1), (key316, 1), (key263, 1), (key253, 1), (key331, -1), (key321, -1)]

theorem rawRowCheck5244 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form1 = rawRow5244 := by decide +kernel

def row5244 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -3), (key445, -1), (key453, 1), (key657, 1), (key658, 1), (key661, 1), (key662, -1)]

theorem rowCheck5244 : row5244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5244 := by decide +kernel

theorem rowEval5244 (x : Key → ℝ) : Integer.Sparse.eval row5244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5244, Integer.Sparse.eval_collectBalanced, rawRowCheck5244]

def rawRow5245 : Integer.Sparse Key := [(key316, -1), (key331, -1), (key321, 2), (key316, -1), (key331, -1), (key302, 2), (key347, 2), (key307, -1), (key346, -1), (key321, 2), (key307, -1), (key346, -1), (key406, 1), (key421, 1), (key411, -2), (key406, 1), (key421, 1), (key236, -2), (key658, -2), (key241, 1), (key421, 1), (key411, -2), (key241, 1), (key421, 1), (key316, -1), (key661, -1), (key321, 1), (key445, 1), (key248, 1), (key662, 1), (key253, -1), (key453, -1), (key316, -1), (key661, -1), (key248, 1), (key662, 1), (key321, 1), (key445, 1), (key253, -1), (key453, -1)]

theorem rawRowCheck5245 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form1 = rawRow5245 := by decide +kernel

def row5245 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key253, -2), (key302, 2), (key307, -2), (key316, -4), (key321, 6), (key331, -2), (key346, -2), (key347, 2), (key406, 2), (key411, -4), (key421, 4), (key445, 2), (key453, -2), (key658, -2), (key661, -2), (key662, 2)]

theorem rowCheck5245 : row5245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5245 := by decide +kernel

theorem rowEval5245 (x : Key → ℝ) : Integer.Sparse.eval row5245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5245, Integer.Sparse.eval_collectBalanced, rawRowCheck5245]

def rawRow5246 : Integer.Sparse Key := [(key331, -1), (key316, -1), (key321, 2), (key331, -1), (key316, -1), (key347, 2), (key302, 2), (key346, -1), (key307, -1), (key321, 2), (key346, -1), (key307, -1), (key421, 1), (key406, 1), (key411, -2), (key421, 1), (key406, 1), (key658, -2), (key236, -2), (key421, 1), (key241, 1), (key411, -2), (key421, 1), (key241, 1), (key661, -1), (key316, -1), (key445, 1), (key321, 1), (key662, 1), (key248, 1), (key453, -1), (key253, -1), (key661, -1), (key316, -1), (key662, 1), (key248, 1), (key445, 1), (key321, 1), (key453, -1), (key253, -1)]

theorem rawRowCheck5246 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form1 = rawRow5246 := by decide +kernel

def row5246 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key253, -2), (key302, 2), (key307, -2), (key316, -4), (key321, 6), (key331, -2), (key346, -2), (key347, 2), (key406, 2), (key411, -4), (key421, 4), (key445, 2), (key453, -2), (key658, -2), (key661, -2), (key662, 2)]

theorem rowCheck5246 : row5246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5246 := by decide +kernel

theorem rowEval5246 (x : Key → ℝ) : Integer.Sparse.eval row5246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5246, Integer.Sparse.eval_collectBalanced, rawRowCheck5246]

def rawRow5247 : Integer.Sparse Key := [(key321, -1), (key331, -1), (key316, 2), (key346, -1), (key347, -1), (key307, 2), (key331, 2), (key302, -1), (key316, -1), (key346, 2), (key307, -1), (key321, -1), (key411, 1), (key421, 1), (key406, -2), (key657, 1), (key658, 1), (key241, -2), (key421, -2), (key236, 1), (key406, 1), (key421, -2), (key241, 1), (key411, 1), (key321, -1), (key660, -1), (key316, 1), (key435, 1), (key253, 1), (key660, 1), (key248, -1), (key435, -1), (key331, -1), (key662, -1), (key263, 1), (key661, 1), (key331, 1), (key453, 1), (key263, -1), (key445, -1)]

theorem rawRowCheck5247 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form1 = rawRow5247 := by decide +kernel

def row5247 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -3), (key445, -1), (key453, 1), (key657, 1), (key658, 1), (key661, 1), (key662, -1)]

theorem rowCheck5247 : row5247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5247 := by decide +kernel

theorem rowEval5247 (x : Key → ℝ) : Integer.Sparse.eval row5247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5247, Integer.Sparse.eval_collectBalanced, rawRowCheck5247]

end MUB6.Certificate.GramRows

end OAI
