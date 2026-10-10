import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11392 : Integer.Sparse Key := [(key2812, -4), (key2709, -4), (key2862, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2678, 6), (key2816, 6), (key2713, 6), (key2687, 6)]

theorem rawRowCheck11392 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form19 = rawRow11392 := by decide +kernel

def row11392 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11392 : row11392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11392 := by decide +kernel

theorem rowEval11392 (x : Key → ℝ) : Integer.Sparse.eval row11392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11392, Integer.Sparse.eval_collectBalanced, rawRowCheck11392]

def rawRow11393 : Integer.Sparse Key := [(key2812, -4), (key2862, -4), (key2709, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2816, 6), (key2678, 6), (key2713, 6), (key2687, 6)]

theorem rawRowCheck11393 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form19 = rawRow11393 := by decide +kernel

def row11393 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11393 : row11393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11393 := by decide +kernel

theorem rowEval11393 (x : Key → ℝ) : Integer.Sparse.eval row11393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11393, Integer.Sparse.eval_collectBalanced, rawRowCheck11393]

def rawRow11394 : Integer.Sparse Key := [(key2862, -4), (key2709, -4), (key2812, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2713, 6), (key2816, 6), (key2678, 6), (key2687, 6)]

theorem rawRowCheck11394 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form19 = rawRow11394 := by decide +kernel

def row11394 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11394 : row11394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11394 := by decide +kernel

theorem rowEval11394 (x : Key → ℝ) : Integer.Sparse.eval row11394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11394, Integer.Sparse.eval_collectBalanced, rawRowCheck11394]

def rawRow11395 : Integer.Sparse Key := [(key2862, -4), (key2812, -4), (key2709, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2816, 6), (key2713, 6), (key2678, 6), (key2687, 6)]

theorem rawRowCheck11395 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form19 = rawRow11395 := by decide +kernel

def row11395 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11395 : row11395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11395 := by decide +kernel

theorem rowEval11395 (x : Key → ℝ) : Integer.Sparse.eval row11395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11395, Integer.Sparse.eval_collectBalanced, rawRowCheck11395]

def rawRow11396 : Integer.Sparse Key := [(key2713, -4), (key2816, -4), (key2862, -4), (key2678, -4), (key2709, -4), (key2812, -4), (key2687, 6), (key2713, 6), (key2816, 6), (key2678, 6)]

theorem rawRowCheck11396 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form19 = rawRow11396 := by decide +kernel

def row11396 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11396 : row11396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11396 := by decide +kernel

theorem rowEval11396 (x : Key → ℝ) : Integer.Sparse.eval row11396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11396, Integer.Sparse.eval_collectBalanced, rawRowCheck11396]

def rawRow11397 : Integer.Sparse Key := [(key2713, -4), (key2862, -4), (key2816, -4), (key2709, -4), (key2678, -4), (key2812, -4), (key2713, 6), (key2687, 6), (key2816, 6), (key2678, 6)]

theorem rawRowCheck11397 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form19 = rawRow11397 := by decide +kernel

def row11397 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11397 : row11397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11397 := by decide +kernel

theorem rowEval11397 (x : Key → ℝ) : Integer.Sparse.eval row11397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11397, Integer.Sparse.eval_collectBalanced, rawRowCheck11397]

def rawRow11398 : Integer.Sparse Key := [(key2816, -4), (key2713, -4), (key2862, -4), (key2678, -4), (key2812, -4), (key2709, -4), (key2687, 6), (key2816, 6), (key2713, 6), (key2678, 6)]

theorem rawRowCheck11398 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form19 = rawRow11398 := by decide +kernel

def row11398 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11398 : row11398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11398 := by decide +kernel

theorem rowEval11398 (x : Key → ℝ) : Integer.Sparse.eval row11398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11398, Integer.Sparse.eval_collectBalanced, rawRowCheck11398]

def rawRow11399 : Integer.Sparse Key := [(key2816, -4), (key2862, -4), (key2713, -4), (key2812, -4), (key2678, -4), (key2709, -4), (key2816, 6), (key2687, 6), (key2713, 6), (key2678, 6)]

theorem rawRowCheck11399 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form19 = rawRow11399 := by decide +kernel

def row11399 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11399 : row11399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11399 := by decide +kernel

theorem rowEval11399 (x : Key → ℝ) : Integer.Sparse.eval row11399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11399, Integer.Sparse.eval_collectBalanced, rawRowCheck11399]

def rawRow11400 : Integer.Sparse Key := [(key2862, -4), (key2713, -4), (key2816, -4), (key2709, -4), (key2812, -4), (key2678, -4), (key2713, 6), (key2816, 6), (key2687, 6), (key2678, 6)]

theorem rawRowCheck11400 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form19 = rawRow11400 := by decide +kernel

def row11400 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11400 : row11400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11400 := by decide +kernel

theorem rowEval11400 (x : Key → ℝ) : Integer.Sparse.eval row11400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11400, Integer.Sparse.eval_collectBalanced, rawRowCheck11400]

def rawRow11401 : Integer.Sparse Key := [(key2862, -4), (key2816, -4), (key2713, -4), (key2812, -4), (key2709, -4), (key2678, -4), (key2816, 6), (key2713, 6), (key2687, 6), (key2678, 6)]

theorem rawRowCheck11401 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form19 = rawRow11401 := by decide +kernel

def row11401 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11401 : row11401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11401 := by decide +kernel

theorem rowEval11401 (x : Key → ℝ) : Integer.Sparse.eval row11401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11401, Integer.Sparse.eval_collectBalanced, rawRowCheck11401]

def rawRow11402 : Integer.Sparse Key := [(key2687, -4), (key2713, -4), (key2713, -4), (key2816, -4), (key2816, -4), (key2862, -4), (key2678, 6), (key2678, 6), (key2709, 6), (key2812, 6)]

theorem rawRowCheck11402 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form19 = rawRow11402 := by decide +kernel

def row11402 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

theorem rowCheck11402 : row11402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11402 := by decide +kernel

theorem rowEval11402 (x : Key → ℝ) : Integer.Sparse.eval row11402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11402, Integer.Sparse.eval_collectBalanced, rawRowCheck11402]

def rawRow11403 : Integer.Sparse Key := [(key2713, -4), (key2687, -4), (key2713, -4), (key2816, -4), (key2862, -4), (key2816, -4), (key2678, 6), (key2709, 6), (key2678, 6), (key2812, 6)]

theorem rawRowCheck11403 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form19 = rawRow11403 := by decide +kernel

def row11403 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

theorem rowCheck11403 : row11403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11403 := by decide +kernel

theorem rowEval11403 (x : Key → ℝ) : Integer.Sparse.eval row11403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11403, Integer.Sparse.eval_collectBalanced, rawRowCheck11403]

def rawRow11404 : Integer.Sparse Key := [(key2713, -4), (key2713, -4), (key2687, -4), (key2862, -4), (key2816, -4), (key2816, -4), (key2709, 6), (key2678, 6), (key2678, 6), (key2812, 6)]

theorem rawRowCheck11404 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form19 = rawRow11404 := by decide +kernel

def row11404 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

theorem rowCheck11404 : row11404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11404 := by decide +kernel

theorem rowEval11404 (x : Key → ℝ) : Integer.Sparse.eval row11404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11404, Integer.Sparse.eval_collectBalanced, rawRowCheck11404]

def rawRow11405 : Integer.Sparse Key := [(key2687, -4), (key2816, -4), (key2816, -4), (key2713, -4), (key2713, -4), (key2862, -4), (key2678, 6), (key2678, 6), (key2812, 6), (key2709, 6)]

theorem rawRowCheck11405 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form19 = rawRow11405 := by decide +kernel

def row11405 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

theorem rowCheck11405 : row11405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11405 := by decide +kernel

theorem rowEval11405 (x : Key → ℝ) : Integer.Sparse.eval row11405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11405, Integer.Sparse.eval_collectBalanced, rawRowCheck11405]

def rawRow11406 : Integer.Sparse Key := [(key2816, -4), (key2687, -4), (key2816, -4), (key2713, -4), (key2862, -4), (key2713, -4), (key2678, 6), (key2812, 6), (key2678, 6), (key2709, 6)]

theorem rawRowCheck11406 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form19 = rawRow11406 := by decide +kernel

def row11406 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

theorem rowCheck11406 : row11406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11406 := by decide +kernel

theorem rowEval11406 (x : Key → ℝ) : Integer.Sparse.eval row11406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11406, Integer.Sparse.eval_collectBalanced, rawRowCheck11406]

def rawRow11407 : Integer.Sparse Key := [(key2816, -4), (key2816, -4), (key2687, -4), (key2862, -4), (key2713, -4), (key2713, -4), (key2812, 6), (key2678, 6), (key2678, 6), (key2709, 6)]

theorem rawRowCheck11407 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form19 = rawRow11407 := by decide +kernel

def row11407 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

theorem rowCheck11407 : row11407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11407 := by decide +kernel

theorem rowEval11407 (x : Key → ℝ) : Integer.Sparse.eval row11407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11407, Integer.Sparse.eval_collectBalanced, rawRowCheck11407]

def rawRow11408 : Integer.Sparse Key := [(key2713, -4), (key2816, -4), (key2862, -4), (key2687, -4), (key2713, -4), (key2816, -4), (key2678, 6), (key2709, 6), (key2812, 6), (key2678, 6)]

theorem rawRowCheck11408 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form19 = rawRow11408 := by decide +kernel

def row11408 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

theorem rowCheck11408 : row11408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11408 := by decide +kernel

theorem rowEval11408 (x : Key → ℝ) : Integer.Sparse.eval row11408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11408, Integer.Sparse.eval_collectBalanced, rawRowCheck11408]

def rawRow11409 : Integer.Sparse Key := [(key2713, -4), (key2862, -4), (key2816, -4), (key2713, -4), (key2687, -4), (key2816, -4), (key2709, 6), (key2678, 6), (key2812, 6), (key2678, 6)]

theorem rawRowCheck11409 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form19 = rawRow11409 := by decide +kernel

def row11409 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

theorem rowCheck11409 : row11409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11409 := by decide +kernel

theorem rowEval11409 (x : Key → ℝ) : Integer.Sparse.eval row11409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11409, Integer.Sparse.eval_collectBalanced, rawRowCheck11409]

def rawRow11410 : Integer.Sparse Key := [(key2816, -4), (key2713, -4), (key2862, -4), (key2687, -4), (key2816, -4), (key2713, -4), (key2678, 6), (key2812, 6), (key2709, 6), (key2678, 6)]

theorem rawRowCheck11410 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form19 = rawRow11410 := by decide +kernel

def row11410 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

theorem rowCheck11410 : row11410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11410 := by decide +kernel

theorem rowEval11410 (x : Key → ℝ) : Integer.Sparse.eval row11410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11410, Integer.Sparse.eval_collectBalanced, rawRowCheck11410]

def rawRow11411 : Integer.Sparse Key := [(key2816, -4), (key2862, -4), (key2713, -4), (key2816, -4), (key2687, -4), (key2713, -4), (key2812, 6), (key2678, 6), (key2709, 6), (key2678, 6)]

theorem rawRowCheck11411 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form19 = rawRow11411 := by decide +kernel

def row11411 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

theorem rowCheck11411 : row11411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11411 := by decide +kernel

theorem rowEval11411 (x : Key → ℝ) : Integer.Sparse.eval row11411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11411, Integer.Sparse.eval_collectBalanced, rawRowCheck11411]

def rawRow11412 : Integer.Sparse Key := [(key2862, -4), (key2713, -4), (key2816, -4), (key2713, -4), (key2816, -4), (key2687, -4), (key2709, 6), (key2812, 6), (key2678, 6), (key2678, 6)]

theorem rawRowCheck11412 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form19 = rawRow11412 := by decide +kernel

def row11412 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

theorem rowCheck11412 : row11412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11412 := by decide +kernel

theorem rowEval11412 (x : Key → ℝ) : Integer.Sparse.eval row11412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11412, Integer.Sparse.eval_collectBalanced, rawRowCheck11412]

def rawRow11413 : Integer.Sparse Key := [(key2862, -4), (key2816, -4), (key2713, -4), (key2816, -4), (key2713, -4), (key2687, -4), (key2812, 6), (key2709, 6), (key2678, 6), (key2678, 6)]

theorem rawRowCheck11413 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form19 = rawRow11413 := by decide +kernel

def row11413 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

theorem rowCheck11413 : row11413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11413 := by decide +kernel

theorem rowEval11413 (x : Key → ℝ) : Integer.Sparse.eval row11413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11413, Integer.Sparse.eval_collectBalanced, rawRowCheck11413]

def rawRow11414 : Integer.Sparse Key := [(key1936, 6), (key1937, 6), (key1940, 6), (key1949, 6), (key1937, -24)]

theorem rawRowCheck11414 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form20 = rawRow11414 := by decide +kernel

def row11414 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11414 : row11414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11414 := by decide +kernel

theorem rowEval11414 (x : Key → ℝ) : Integer.Sparse.eval row11414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11414, Integer.Sparse.eval_collectBalanced, rawRowCheck11414]

def rawRow11415 : Integer.Sparse Key := [(key1937, 6), (key1936, 6), (key1940, 6), (key1949, 6), (key1937, -24)]

theorem rawRowCheck11415 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form20 = rawRow11415 := by decide +kernel

def row11415 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11415 : row11415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11415 := by decide +kernel

theorem rowEval11415 (x : Key → ℝ) : Integer.Sparse.eval row11415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11415, Integer.Sparse.eval_collectBalanced, rawRowCheck11415]

def rawRow11416 : Integer.Sparse Key := [(key1936, 6), (key1940, 6), (key1937, 6), (key1949, 6), (key1937, -24)]

theorem rawRowCheck11416 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form20 = rawRow11416 := by decide +kernel

def row11416 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11416 : row11416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11416 := by decide +kernel

theorem rowEval11416 (x : Key → ℝ) : Integer.Sparse.eval row11416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11416, Integer.Sparse.eval_collectBalanced, rawRowCheck11416]

def rawRow11417 : Integer.Sparse Key := [(key1940, 6), (key1936, 6), (key1937, 6), (key1949, 6), (key1937, -24)]

theorem rawRowCheck11417 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form20 = rawRow11417 := by decide +kernel

def row11417 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11417 : row11417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11417 := by decide +kernel

theorem rowEval11417 (x : Key → ℝ) : Integer.Sparse.eval row11417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11417, Integer.Sparse.eval_collectBalanced, rawRowCheck11417]

def rawRow11418 : Integer.Sparse Key := [(key1937, 6), (key1940, 6), (key1936, 6), (key1949, 6), (key1937, -24)]

theorem rawRowCheck11418 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form20 = rawRow11418 := by decide +kernel

def row11418 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11418 : row11418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11418 := by decide +kernel

theorem rowEval11418 (x : Key → ℝ) : Integer.Sparse.eval row11418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11418, Integer.Sparse.eval_collectBalanced, rawRowCheck11418]

def rawRow11419 : Integer.Sparse Key := [(key1940, 6), (key1937, 6), (key1936, 6), (key1949, 6), (key1937, -24)]

theorem rawRowCheck11419 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form20 = rawRow11419 := by decide +kernel

def row11419 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11419 : row11419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11419 := by decide +kernel

theorem rowEval11419 (x : Key → ℝ) : Integer.Sparse.eval row11419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11419, Integer.Sparse.eval_collectBalanced, rawRowCheck11419]

def rawRow11420 : Integer.Sparse Key := [(key1936, 6), (key1937, 6), (key1949, 6), (key1940, 6), (key1937, -24)]

theorem rawRowCheck11420 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form20 = rawRow11420 := by decide +kernel

def row11420 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11420 : row11420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11420 := by decide +kernel

theorem rowEval11420 (x : Key → ℝ) : Integer.Sparse.eval row11420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11420, Integer.Sparse.eval_collectBalanced, rawRowCheck11420]

def rawRow11421 : Integer.Sparse Key := [(key1937, 6), (key1936, 6), (key1949, 6), (key1940, 6), (key1937, -24)]

theorem rawRowCheck11421 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form20 = rawRow11421 := by decide +kernel

def row11421 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11421 : row11421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11421 := by decide +kernel

theorem rowEval11421 (x : Key → ℝ) : Integer.Sparse.eval row11421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11421, Integer.Sparse.eval_collectBalanced, rawRowCheck11421]

def rawRow11422 : Integer.Sparse Key := [(key1936, 6), (key1949, 6), (key1937, 6), (key1940, 6), (key1937, -24)]

theorem rawRowCheck11422 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form20 = rawRow11422 := by decide +kernel

def row11422 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11422 : row11422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11422 := by decide +kernel

theorem rowEval11422 (x : Key → ℝ) : Integer.Sparse.eval row11422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11422, Integer.Sparse.eval_collectBalanced, rawRowCheck11422]

def rawRow11423 : Integer.Sparse Key := [(key1949, 6), (key1936, 6), (key1937, 6), (key1940, 6), (key1937, -24)]

theorem rawRowCheck11423 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form20 = rawRow11423 := by decide +kernel

def row11423 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11423 : row11423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11423 := by decide +kernel

theorem rowEval11423 (x : Key → ℝ) : Integer.Sparse.eval row11423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11423, Integer.Sparse.eval_collectBalanced, rawRowCheck11423]

def rawRow11424 : Integer.Sparse Key := [(key1937, 6), (key1949, 6), (key1936, 6), (key1940, 6), (key1937, -24)]

theorem rawRowCheck11424 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form20 = rawRow11424 := by decide +kernel

def row11424 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11424 : row11424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11424 := by decide +kernel

theorem rowEval11424 (x : Key → ℝ) : Integer.Sparse.eval row11424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11424, Integer.Sparse.eval_collectBalanced, rawRowCheck11424]

def rawRow11425 : Integer.Sparse Key := [(key1949, 6), (key1937, 6), (key1936, 6), (key1940, 6), (key1937, -24)]

theorem rawRowCheck11425 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form20 = rawRow11425 := by decide +kernel

def row11425 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11425 : row11425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11425 := by decide +kernel

theorem rowEval11425 (x : Key → ℝ) : Integer.Sparse.eval row11425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11425, Integer.Sparse.eval_collectBalanced, rawRowCheck11425]

def rawRow11426 : Integer.Sparse Key := [(key1936, 6), (key1940, 6), (key1949, 6), (key1937, 6), (key1937, -24)]

theorem rawRowCheck11426 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form20 = rawRow11426 := by decide +kernel

def row11426 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11426 : row11426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11426 := by decide +kernel

theorem rowEval11426 (x : Key → ℝ) : Integer.Sparse.eval row11426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11426, Integer.Sparse.eval_collectBalanced, rawRowCheck11426]

def rawRow11427 : Integer.Sparse Key := [(key1940, 6), (key1936, 6), (key1949, 6), (key1937, 6), (key1937, -24)]

theorem rawRowCheck11427 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form20 = rawRow11427 := by decide +kernel

def row11427 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11427 : row11427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11427 := by decide +kernel

theorem rowEval11427 (x : Key → ℝ) : Integer.Sparse.eval row11427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11427, Integer.Sparse.eval_collectBalanced, rawRowCheck11427]

def rawRow11428 : Integer.Sparse Key := [(key1936, 6), (key1949, 6), (key1940, 6), (key1937, 6), (key1937, -24)]

theorem rawRowCheck11428 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form20 = rawRow11428 := by decide +kernel

def row11428 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11428 : row11428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11428 := by decide +kernel

theorem rowEval11428 (x : Key → ℝ) : Integer.Sparse.eval row11428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11428, Integer.Sparse.eval_collectBalanced, rawRowCheck11428]

def rawRow11429 : Integer.Sparse Key := [(key1949, 6), (key1936, 6), (key1940, 6), (key1937, 6), (key1937, -24)]

theorem rawRowCheck11429 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form20 = rawRow11429 := by decide +kernel

def row11429 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11429 : row11429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11429 := by decide +kernel

theorem rowEval11429 (x : Key → ℝ) : Integer.Sparse.eval row11429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11429, Integer.Sparse.eval_collectBalanced, rawRowCheck11429]

def rawRow11430 : Integer.Sparse Key := [(key1940, 6), (key1949, 6), (key1936, 6), (key1937, 6), (key1937, -24)]

theorem rawRowCheck11430 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form20 = rawRow11430 := by decide +kernel

def row11430 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11430 : row11430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11430 := by decide +kernel

theorem rowEval11430 (x : Key → ℝ) : Integer.Sparse.eval row11430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11430, Integer.Sparse.eval_collectBalanced, rawRowCheck11430]

def rawRow11431 : Integer.Sparse Key := [(key1949, 6), (key1940, 6), (key1936, 6), (key1937, 6), (key1937, -24)]

theorem rawRowCheck11431 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form20 = rawRow11431 := by decide +kernel

def row11431 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11431 : row11431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11431 := by decide +kernel

theorem rowEval11431 (x : Key → ℝ) : Integer.Sparse.eval row11431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11431, Integer.Sparse.eval_collectBalanced, rawRowCheck11431]

def rawRow11432 : Integer.Sparse Key := [(key1937, 6), (key1940, 6), (key1949, 6), (key1936, 6), (key1937, -24)]

theorem rawRowCheck11432 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form20 = rawRow11432 := by decide +kernel

def row11432 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11432 : row11432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11432 := by decide +kernel

theorem rowEval11432 (x : Key → ℝ) : Integer.Sparse.eval row11432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11432, Integer.Sparse.eval_collectBalanced, rawRowCheck11432]

def rawRow11433 : Integer.Sparse Key := [(key1940, 6), (key1937, 6), (key1949, 6), (key1936, 6), (key1937, -24)]

theorem rawRowCheck11433 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form20 = rawRow11433 := by decide +kernel

def row11433 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11433 : row11433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11433 := by decide +kernel

theorem rowEval11433 (x : Key → ℝ) : Integer.Sparse.eval row11433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11433, Integer.Sparse.eval_collectBalanced, rawRowCheck11433]

def rawRow11434 : Integer.Sparse Key := [(key1937, 6), (key1949, 6), (key1940, 6), (key1936, 6), (key1937, -24)]

theorem rawRowCheck11434 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form20 = rawRow11434 := by decide +kernel

def row11434 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11434 : row11434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11434 := by decide +kernel

theorem rowEval11434 (x : Key → ℝ) : Integer.Sparse.eval row11434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11434, Integer.Sparse.eval_collectBalanced, rawRowCheck11434]

def rawRow11435 : Integer.Sparse Key := [(key1949, 6), (key1937, 6), (key1940, 6), (key1936, 6), (key1937, -24)]

theorem rawRowCheck11435 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form20 = rawRow11435 := by decide +kernel

def row11435 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11435 : row11435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11435 := by decide +kernel

theorem rowEval11435 (x : Key → ℝ) : Integer.Sparse.eval row11435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11435, Integer.Sparse.eval_collectBalanced, rawRowCheck11435]

def rawRow11436 : Integer.Sparse Key := [(key1940, 6), (key1949, 6), (key1937, 6), (key1936, 6), (key1937, -24)]

theorem rawRowCheck11436 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form20 = rawRow11436 := by decide +kernel

def row11436 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11436 : row11436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11436 := by decide +kernel

theorem rowEval11436 (x : Key → ℝ) : Integer.Sparse.eval row11436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11436, Integer.Sparse.eval_collectBalanced, rawRowCheck11436]

def rawRow11437 : Integer.Sparse Key := [(key1949, 6), (key1940, 6), (key1937, 6), (key1936, 6), (key1937, -24)]

theorem rawRowCheck11437 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form20 = rawRow11437 := by decide +kernel

def row11437 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

theorem rowCheck11437 : row11437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11437 := by decide +kernel

theorem rowEval11437 (x : Key → ℝ) : Integer.Sparse.eval row11437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11437, Integer.Sparse.eval_collectBalanced, rawRowCheck11437]

def rawRow11438 : Integer.Sparse Key := [(key1937, 6), (key1937, 6), (key1940, 6), (key1949, 6), (key1936, -24)]

theorem rawRowCheck11438 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form20 = rawRow11438 := by decide +kernel

def row11438 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck11438 : row11438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11438 := by decide +kernel

theorem rowEval11438 (x : Key → ℝ) : Integer.Sparse.eval row11438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11438, Integer.Sparse.eval_collectBalanced, rawRowCheck11438]

def rawRow11439 : Integer.Sparse Key := [(key1937, 6), (key1940, 6), (key1937, 6), (key1949, 6), (key1936, -24)]

theorem rawRowCheck11439 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form20 = rawRow11439 := by decide +kernel

def row11439 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck11439 : row11439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11439 := by decide +kernel

theorem rowEval11439 (x : Key → ℝ) : Integer.Sparse.eval row11439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11439, Integer.Sparse.eval_collectBalanced, rawRowCheck11439]

def rawRow11440 : Integer.Sparse Key := [(key1940, 6), (key1937, 6), (key1937, 6), (key1949, 6), (key1936, -24)]

theorem rawRowCheck11440 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form20 = rawRow11440 := by decide +kernel

def row11440 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck11440 : row11440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11440 := by decide +kernel

theorem rowEval11440 (x : Key → ℝ) : Integer.Sparse.eval row11440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11440, Integer.Sparse.eval_collectBalanced, rawRowCheck11440]

def rawRow11441 : Integer.Sparse Key := [(key1937, 6), (key1937, 6), (key1949, 6), (key1940, 6), (key1936, -24)]

theorem rawRowCheck11441 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form20 = rawRow11441 := by decide +kernel

def row11441 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck11441 : row11441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11441 := by decide +kernel

theorem rowEval11441 (x : Key → ℝ) : Integer.Sparse.eval row11441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11441, Integer.Sparse.eval_collectBalanced, rawRowCheck11441]

def rawRow11442 : Integer.Sparse Key := [(key1937, 6), (key1949, 6), (key1937, 6), (key1940, 6), (key1936, -24)]

theorem rawRowCheck11442 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form20 = rawRow11442 := by decide +kernel

def row11442 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck11442 : row11442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11442 := by decide +kernel

theorem rowEval11442 (x : Key → ℝ) : Integer.Sparse.eval row11442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11442, Integer.Sparse.eval_collectBalanced, rawRowCheck11442]

def rawRow11443 : Integer.Sparse Key := [(key1949, 6), (key1937, 6), (key1937, 6), (key1940, 6), (key1936, -24)]

theorem rawRowCheck11443 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form20 = rawRow11443 := by decide +kernel

def row11443 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck11443 : row11443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11443 := by decide +kernel

theorem rowEval11443 (x : Key → ℝ) : Integer.Sparse.eval row11443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11443, Integer.Sparse.eval_collectBalanced, rawRowCheck11443]

def rawRow11444 : Integer.Sparse Key := [(key1937, 6), (key1940, 6), (key1949, 6), (key1937, 6), (key1936, -24)]

theorem rawRowCheck11444 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form20 = rawRow11444 := by decide +kernel

def row11444 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck11444 : row11444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11444 := by decide +kernel

theorem rowEval11444 (x : Key → ℝ) : Integer.Sparse.eval row11444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11444, Integer.Sparse.eval_collectBalanced, rawRowCheck11444]

def rawRow11445 : Integer.Sparse Key := [(key1940, 6), (key1937, 6), (key1949, 6), (key1937, 6), (key1936, -24)]

theorem rawRowCheck11445 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form20 = rawRow11445 := by decide +kernel

def row11445 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck11445 : row11445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11445 := by decide +kernel

theorem rowEval11445 (x : Key → ℝ) : Integer.Sparse.eval row11445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11445, Integer.Sparse.eval_collectBalanced, rawRowCheck11445]

def rawRow11446 : Integer.Sparse Key := [(key1937, 6), (key1949, 6), (key1940, 6), (key1937, 6), (key1936, -24)]

theorem rawRowCheck11446 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form20 = rawRow11446 := by decide +kernel

def row11446 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck11446 : row11446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11446 := by decide +kernel

theorem rowEval11446 (x : Key → ℝ) : Integer.Sparse.eval row11446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11446, Integer.Sparse.eval_collectBalanced, rawRowCheck11446]

def rawRow11447 : Integer.Sparse Key := [(key1949, 6), (key1937, 6), (key1940, 6), (key1937, 6), (key1936, -24)]

theorem rawRowCheck11447 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form20 = rawRow11447 := by decide +kernel

def row11447 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck11447 : row11447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11447 := by decide +kernel

theorem rowEval11447 (x : Key → ℝ) : Integer.Sparse.eval row11447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11447, Integer.Sparse.eval_collectBalanced, rawRowCheck11447]

def rawRow11448 : Integer.Sparse Key := [(key1940, 6), (key1949, 6), (key1937, 6), (key1937, 6), (key1936, -24)]

theorem rawRowCheck11448 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form20 = rawRow11448 := by decide +kernel

def row11448 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck11448 : row11448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11448 := by decide +kernel

theorem rowEval11448 (x : Key → ℝ) : Integer.Sparse.eval row11448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11448, Integer.Sparse.eval_collectBalanced, rawRowCheck11448]

def rawRow11449 : Integer.Sparse Key := [(key1949, 6), (key1940, 6), (key1937, 6), (key1937, 6), (key1936, -24)]

theorem rawRowCheck11449 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form20 = rawRow11449 := by decide +kernel

def row11449 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck11449 : row11449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11449 := by decide +kernel

theorem rowEval11449 (x : Key → ℝ) : Integer.Sparse.eval row11449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11449, Integer.Sparse.eval_collectBalanced, rawRowCheck11449]

def rawRow11450 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, 1), (key2636, 1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, 1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1), (key2611, -2), (key2627, -2), (key2636, -2), (key2666, -2), (key2701, -2), (key2722, -2), (key2781, -2), (key2790, -2), (key2804, -2), (key2825, -2), (key2856, -2), (key2866, -2)]

theorem rawRowCheck11450 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form21 = rawRow11450 := by decide +kernel

def row11450 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11450 : row11450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11450 := by decide +kernel

theorem rowEval11450 (x : Key → ℝ) : Integer.Sparse.eval row11450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11450, Integer.Sparse.eval_collectBalanced, rawRowCheck11450]

def rawRow11451 : Integer.Sparse Key := [(key2611, 1), (key2608, 1), (key2636, 1), (key2624, 1), (key2651, 1), (key2645, 1), (key2666, 1), (key2663, 1), (key2722, 1), (key2698, 1), (key2745, 1), (key2734, 1), (key2790, 1), (key2778, 1), (key2825, 1), (key2801, 1), (key2902, 1), (key2895, 1), (key2941, 1), (key2935, 1), (key2958, 1), (key2947, 1), (key2981, 1), (key2974, 1), (key2611, -2), (key2636, -2), (key2627, -2), (key2666, -2), (key2722, -2), (key2701, -2), (key2790, -2), (key2781, -2), (key2825, -2), (key2804, -2), (key2866, -2), (key2856, -2)]

theorem rawRowCheck11451 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form21 = rawRow11451 := by decide +kernel

def row11451 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11451 : row11451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11451 := by decide +kernel

theorem rowEval11451 (x : Key → ℝ) : Integer.Sparse.eval row11451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11451, Integer.Sparse.eval_collectBalanced, rawRowCheck11451]

def rawRow11452 : Integer.Sparse Key := [(key2624, 1), (key2636, 1), (key2608, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2698, 1), (key2734, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2801, 1), (key2895, 1), (key2778, 1), (key2902, 1), (key2790, 1), (key2825, 1), (key2947, 1), (key2974, 1), (key2935, 1), (key2981, 1), (key2941, 1), (key2958, 1), (key2627, -2), (key2611, -2), (key2636, -2), (key2701, -2), (key2666, -2), (key2722, -2), (key2804, -2), (key2856, -2), (key2781, -2), (key2866, -2), (key2790, -2), (key2825, -2)]

theorem rawRowCheck11452 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form21 = rawRow11452 := by decide +kernel

def row11452 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11452 : row11452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11452 := by decide +kernel

theorem rowEval11452 (x : Key → ℝ) : Integer.Sparse.eval row11452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11452, Integer.Sparse.eval_collectBalanced, rawRowCheck11452]

def rawRow11453 : Integer.Sparse Key := [(key2636, 1), (key2624, 1), (key2651, 1), (key2608, 1), (key2636, 1), (key2611, 1), (key2734, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2722, 1), (key2666, 1), (key2895, 1), (key2801, 1), (key2902, 1), (key2778, 1), (key2825, 1), (key2790, 1), (key2974, 1), (key2947, 1), (key2981, 1), (key2935, 1), (key2958, 1), (key2941, 1), (key2627, -2), (key2636, -2), (key2611, -2), (key2701, -2), (key2722, -2), (key2666, -2), (key2856, -2), (key2804, -2), (key2866, -2), (key2781, -2), (key2825, -2), (key2790, -2)]

theorem rawRowCheck11453 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form21 = rawRow11453 := by decide +kernel

def row11453 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11453 : row11453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11453 := by decide +kernel

theorem rowEval11453 (x : Key → ℝ) : Integer.Sparse.eval row11453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11453, Integer.Sparse.eval_collectBalanced, rawRowCheck11453]

def rawRow11454 : Integer.Sparse Key := [(key2645, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2608, 1), (key2624, 1), (key2722, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2663, 1), (key2698, 1), (key2825, 1), (key2902, 1), (key2790, 1), (key2895, 1), (key2778, 1), (key2801, 1), (key2958, 1), (key2981, 1), (key2941, 1), (key2974, 1), (key2935, 1), (key2947, 1), (key2636, -2), (key2611, -2), (key2627, -2), (key2722, -2), (key2666, -2), (key2701, -2), (key2825, -2), (key2866, -2), (key2790, -2), (key2856, -2), (key2781, -2), (key2804, -2)]

theorem rawRowCheck11454 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form21 = rawRow11454 := by decide +kernel

def row11454 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11454 : row11454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11454 := by decide +kernel

theorem rowEval11454 (x : Key → ℝ) : Integer.Sparse.eval row11454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11454, Integer.Sparse.eval_collectBalanced, rawRowCheck11454]

def rawRow11455 : Integer.Sparse Key := [(key2651, 1), (key2645, 1), (key2636, 1), (key2611, 1), (key2624, 1), (key2608, 1), (key2745, 1), (key2722, 1), (key2734, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2902, 1), (key2825, 1), (key2895, 1), (key2790, 1), (key2801, 1), (key2778, 1), (key2981, 1), (key2958, 1), (key2974, 1), (key2941, 1), (key2947, 1), (key2935, 1), (key2636, -2), (key2627, -2), (key2611, -2), (key2722, -2), (key2701, -2), (key2666, -2), (key2866, -2), (key2825, -2), (key2856, -2), (key2790, -2), (key2804, -2), (key2781, -2)]

theorem rawRowCheck11455 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form21 = rawRow11455 := by decide +kernel

def row11455 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11455 : row11455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11455 := by decide +kernel

theorem rowEval11455 (x : Key → ℝ) : Integer.Sparse.eval row11455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11455, Integer.Sparse.eval_collectBalanced, rawRowCheck11455]

def rawRow11456 : Integer.Sparse Key := [(key2663, 1), (key2666, 1), (key2698, 1), (key2734, 1), (key2722, 1), (key2745, 1), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2722, 1), (key2974, 1), (key2981, 1), (key2645, 1), (key2651, 1), (key2734, 1), (key2745, 1), (key2895, 1), (key2902, 1), (key2666, -2), (key2781, -2), (key2790, -2), (key2611, -2), (key2804, -2), (key2825, -2), (key2627, -2), (key2636, -2), (key2701, -2), (key2722, -2), (key2856, -2), (key2866, -2)]

theorem rawRowCheck11456 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form21 = rawRow11456 := by decide +kernel

def row11456 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11456 : row11456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11456 := by decide +kernel

theorem rowEval11456 (x : Key → ℝ) : Integer.Sparse.eval row11456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11456, Integer.Sparse.eval_collectBalanced, rawRowCheck11456]

def rawRow11457 : Integer.Sparse Key := [(key2666, 1), (key2663, 1), (key2734, 1), (key2698, 1), (key2745, 1), (key2722, 1), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1), (key2636, 1), (key2624, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2974, 1), (key2651, 1), (key2645, 1), (key2745, 1), (key2734, 1), (key2902, 1), (key2895, 1), (key2666, -2), (key2790, -2), (key2781, -2), (key2611, -2), (key2825, -2), (key2804, -2), (key2636, -2), (key2627, -2), (key2722, -2), (key2701, -2), (key2866, -2), (key2856, -2)]

theorem rawRowCheck11457 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form21 = rawRow11457 := by decide +kernel

def row11457 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11457 : row11457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11457 := by decide +kernel

theorem rowEval11457 (x : Key → ℝ) : Integer.Sparse.eval row11457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11457, Integer.Sparse.eval_collectBalanced, rawRowCheck11457]

def rawRow11458 : Integer.Sparse Key := [(key2698, 1), (key2722, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2698, 1), (key2974, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2734, 1), (key2895, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2745, 1), (key2781, -2), (key2666, -2), (key2790, -2), (key2804, -2), (key2611, -2), (key2825, -2), (key2701, -2), (key2856, -2), (key2627, -2), (key2866, -2), (key2636, -2), (key2722, -2)]

theorem rawRowCheck11458 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form21 = rawRow11458 := by decide +kernel

def row11458 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11458 : row11458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11458 := by decide +kernel

theorem rowEval11458 (x : Key → ℝ) : Integer.Sparse.eval row11458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11458, Integer.Sparse.eval_collectBalanced, rawRowCheck11458]

def rawRow11459 : Integer.Sparse Key := [(key2722, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2734, 1), (key2666, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2722, 1), (key2636, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2745, 1), (key2651, 1), (key2781, -2), (key2790, -2), (key2666, -2), (key2804, -2), (key2825, -2), (key2611, -2), (key2856, -2), (key2701, -2), (key2866, -2), (key2627, -2), (key2722, -2), (key2636, -2)]

theorem rawRowCheck11459 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form21 = rawRow11459 := by decide +kernel

def row11459 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11459 : row11459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11459 := by decide +kernel

theorem rowEval11459 (x : Key → ℝ) : Integer.Sparse.eval row11459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck11459, Integer.Sparse.eval_collectBalanced, rawRowCheck11459]

def rawRow11460 : Integer.Sparse Key := [(key2734, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2663, 1), (key2698, 1), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1), (key2722, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2624, 1), (key2698, 1), (key2745, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2645, 1), (key2734, 1), (key2790, -2), (key2666, -2), (key2781, -2), (key2825, -2), (key2611, -2), (key2804, -2), (key2722, -2), (key2866, -2), (key2636, -2), (key2856, -2), (key2627, -2), (key2701, -2)]

theorem rawRowCheck11460 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form21 = rawRow11460 := by decide +kernel

def row11460 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11460 : row11460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11460 := by decide +kernel

theorem rowEval11460 (x : Key → ℝ) : Integer.Sparse.eval row11460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11460, Integer.Sparse.eval_collectBalanced, rawRowCheck11460]

def rawRow11461 : Integer.Sparse Key := [(key2745, 1), (key2734, 1), (key2722, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1), (key2981, 1), (key2722, 1), (key2974, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2902, 1), (key2745, 1), (key2895, 1), (key2651, 1), (key2734, 1), (key2645, 1), (key2790, -2), (key2781, -2), (key2666, -2), (key2825, -2), (key2804, -2), (key2611, -2), (key2866, -2), (key2722, -2), (key2856, -2), (key2636, -2), (key2701, -2), (key2627, -2)]

theorem rawRowCheck11461 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form21 = rawRow11461 := by decide +kernel

def row11461 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11461 : row11461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11461 := by decide +kernel

theorem rowEval11461 (x : Key → ℝ) : Integer.Sparse.eval row11461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck11461, Integer.Sparse.eval_collectBalanced, rawRowCheck11461]

def rawRow11462 : Integer.Sparse Key := [(key2778, 1), (key2790, 1), (key2801, 1), (key2895, 1), (key2825, 1), (key2902, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2974, 1), (key2722, 1), (key2981, 1), (key2608, 1), (key2651, 1), (key2663, 1), (key2745, 1), (key2941, 1), (key2958, 1), (key2611, 1), (key2636, 1), (key2666, 1), (key2722, 1), (key2790, 1), (key2825, 1), (key2701, -2), (key2804, -2), (key2856, -2), (key2627, -2), (key2781, -2), (key2866, -2), (key2611, -2), (key2636, -2), (key2666, -2), (key2722, -2), (key2790, -2), (key2825, -2)]

theorem rawRowCheck11462 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form21 = rawRow11462 := by decide +kernel

def row11462 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 1), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11462 : row11462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11462 := by decide +kernel

theorem rowEval11462 (x : Key → ℝ) : Integer.Sparse.eval row11462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11462, Integer.Sparse.eval_collectBalanced, rawRowCheck11462]

def rawRow11463 : Integer.Sparse Key := [(key2790, 1), (key2778, 1), (key2895, 1), (key2801, 1), (key2902, 1), (key2825, 1), (key2636, 1), (key2624, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2722, 1), (key2651, 1), (key2608, 1), (key2745, 1), (key2663, 1), (key2958, 1), (key2941, 1), (key2636, 1), (key2611, 1), (key2722, 1), (key2666, 1), (key2825, 1), (key2790, 1), (key2701, -2), (key2856, -2), (key2804, -2), (key2627, -2), (key2866, -2), (key2781, -2), (key2636, -2), (key2611, -2), (key2722, -2), (key2666, -2), (key2825, -2), (key2790, -2)]

theorem rawRowCheck11463 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form21 = rawRow11463 := by decide +kernel

def row11463 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 1), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11463 : row11463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11463 := by decide +kernel

theorem rowEval11463 (x : Key → ℝ) : Integer.Sparse.eval row11463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11463, Integer.Sparse.eval_collectBalanced, rawRowCheck11463]

def rawRow11464 : Integer.Sparse Key := [(key2801, 1), (key2825, 1), (key2778, 1), (key2902, 1), (key2790, 1), (key2895, 1), (key2698, 1), (key2722, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2663, 1), (key2745, 1), (key2608, 1), (key2958, 1), (key2651, 1), (key2745, 1), (key2666, 1), (key2790, 1), (key2611, 1), (key2825, 1), (key2636, 1), (key2722, 1), (key2804, -2), (key2701, -2), (key2856, -2), (key2781, -2), (key2627, -2), (key2866, -2), (key2666, -2), (key2790, -2), (key2611, -2), (key2825, -2), (key2636, -2), (key2722, -2)]

theorem rawRowCheck11464 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form21 = rawRow11464 := by decide +kernel

def row11464 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 2), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11464 : row11464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11464 := by decide +kernel

theorem rowEval11464 (x : Key → ℝ) : Integer.Sparse.eval row11464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11464, Integer.Sparse.eval_collectBalanced, rawRowCheck11464]

def rawRow11465 : Integer.Sparse Key := [(key2825, 1), (key2801, 1), (key2902, 1), (key2778, 1), (key2895, 1), (key2790, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2974, 1), (key2636, 1), (key2745, 1), (key2663, 1), (key2958, 1), (key2608, 1), (key2745, 1), (key2651, 1), (key2790, 1), (key2666, 1), (key2825, 1), (key2611, 1), (key2722, 1), (key2636, 1), (key2804, -2), (key2856, -2), (key2701, -2), (key2781, -2), (key2866, -2), (key2627, -2), (key2790, -2), (key2666, -2), (key2825, -2), (key2611, -2), (key2722, -2), (key2636, -2)]

theorem rawRowCheck11465 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form21 = rawRow11465 := by decide +kernel

def row11465 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 2), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11465 : row11465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11465 := by decide +kernel

theorem rowEval11465 (x : Key → ℝ) : Integer.Sparse.eval row11465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck11465, Integer.Sparse.eval_collectBalanced, rawRowCheck11465]

def rawRow11466 : Integer.Sparse Key := [(key2895, 1), (key2902, 1), (key2790, 1), (key2825, 1), (key2778, 1), (key2801, 1), (key2974, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2624, 1), (key2698, 1), (key2941, 1), (key2958, 1), (key2651, 1), (key2745, 1), (key2608, 1), (key2663, 1), (key2722, 1), (key2825, 1), (key2636, 1), (key2790, 1), (key2611, 1), (key2666, 1), (key2856, -2), (key2701, -2), (key2804, -2), (key2866, -2), (key2627, -2), (key2781, -2), (key2722, -2), (key2825, -2), (key2636, -2), (key2790, -2), (key2611, -2), (key2666, -2)]

theorem rawRowCheck11466 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form21 = rawRow11466 := by decide +kernel

def row11466 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 1), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11466 : row11466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11466 := by decide +kernel

theorem rowEval11466 (x : Key → ℝ) : Integer.Sparse.eval row11466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11466, Integer.Sparse.eval_collectBalanced, rawRowCheck11466]

def rawRow11467 : Integer.Sparse Key := [(key2902, 1), (key2895, 1), (key2825, 1), (key2790, 1), (key2801, 1), (key2778, 1), (key2981, 1), (key2974, 1), (key2722, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2958, 1), (key2941, 1), (key2745, 1), (key2651, 1), (key2663, 1), (key2608, 1), (key2825, 1), (key2722, 1), (key2790, 1), (key2636, 1), (key2666, 1), (key2611, 1), (key2856, -2), (key2804, -2), (key2701, -2), (key2866, -2), (key2781, -2), (key2627, -2), (key2825, -2), (key2722, -2), (key2790, -2), (key2636, -2), (key2666, -2), (key2611, -2)]

theorem rawRowCheck11467 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form21 = rawRow11467 := by decide +kernel

def row11467 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 1), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11467 : row11467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11467 := by decide +kernel

theorem rowEval11467 (x : Key → ℝ) : Integer.Sparse.eval row11467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck11467, Integer.Sparse.eval_collectBalanced, rawRowCheck11467]

def rawRow11468 : Integer.Sparse Key := [(key2935, 1), (key2941, 1), (key2947, 1), (key2974, 1), (key2958, 1), (key2981, 1), (key2645, 1), (key2651, 1), (key2734, 1), (key2895, 1), (key2745, 1), (key2902, 1), (key2611, 1), (key2636, 1), (key2666, 1), (key2790, 1), (key2722, 1), (key2825, 1), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1), (key2722, -2), (key2825, -2), (key2866, -2), (key2636, -2), (key2790, -2), (key2856, -2), (key2611, -2), (key2627, -2), (key2666, -2), (key2701, -2), (key2781, -2), (key2804, -2)]

theorem rawRowCheck11468 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form21 = rawRow11468 := by decide +kernel

def row11468 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11468 : row11468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11468 := by decide +kernel

theorem rowEval11468 (x : Key → ℝ) : Integer.Sparse.eval row11468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11468, Integer.Sparse.eval_collectBalanced, rawRowCheck11468]

def rawRow11469 : Integer.Sparse Key := [(key2941, 1), (key2935, 1), (key2974, 1), (key2947, 1), (key2981, 1), (key2958, 1), (key2651, 1), (key2645, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2745, 1), (key2636, 1), (key2611, 1), (key2790, 1), (key2666, 1), (key2825, 1), (key2722, 1), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1), (key2722, -2), (key2866, -2), (key2825, -2), (key2636, -2), (key2856, -2), (key2790, -2), (key2627, -2), (key2611, -2), (key2701, -2), (key2666, -2), (key2804, -2), (key2781, -2)]

theorem rawRowCheck11469 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form21 = rawRow11469 := by decide +kernel

def row11469 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11469 : row11469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11469 := by decide +kernel

theorem rowEval11469 (x : Key → ℝ) : Integer.Sparse.eval row11469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11469, Integer.Sparse.eval_collectBalanced, rawRowCheck11469]

def rawRow11470 : Integer.Sparse Key := [(key2947, 1), (key2958, 1), (key2935, 1), (key2981, 1), (key2941, 1), (key2974, 1), (key2734, 1), (key2745, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2666, 1), (key2722, 1), (key2611, 1), (key2825, 1), (key2636, 1), (key2790, 1), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2825, -2), (key2722, -2), (key2866, -2), (key2790, -2), (key2636, -2), (key2856, -2), (key2666, -2), (key2781, -2), (key2611, -2), (key2804, -2), (key2627, -2), (key2701, -2)]

theorem rawRowCheck11470 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form21 = rawRow11470 := by decide +kernel

def row11470 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11470 : row11470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11470 := by decide +kernel

theorem rowEval11470 (x : Key → ℝ) : Integer.Sparse.eval row11470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11470, Integer.Sparse.eval_collectBalanced, rawRowCheck11470]

def rawRow11471 : Integer.Sparse Key := [(key2958, 1), (key2947, 1), (key2981, 1), (key2935, 1), (key2974, 1), (key2941, 1), (key2745, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2895, 1), (key2651, 1), (key2722, 1), (key2666, 1), (key2825, 1), (key2611, 1), (key2790, 1), (key2636, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1), (key2825, -2), (key2866, -2), (key2722, -2), (key2790, -2), (key2856, -2), (key2636, -2), (key2781, -2), (key2666, -2), (key2804, -2), (key2611, -2), (key2701, -2), (key2627, -2)]

theorem rawRowCheck11471 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form21 = rawRow11471 := by decide +kernel

def row11471 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11471 : row11471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11471 := by decide +kernel

theorem rowEval11471 (x : Key → ℝ) : Integer.Sparse.eval row11471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck11471, Integer.Sparse.eval_collectBalanced, rawRowCheck11471]

def rawRow11472 : Integer.Sparse Key := [(key2974, 1), (key2981, 1), (key2941, 1), (key2958, 1), (key2935, 1), (key2947, 1), (key2895, 1), (key2902, 1), (key2651, 1), (key2745, 1), (key2645, 1), (key2734, 1), (key2790, 1), (key2825, 1), (key2636, 1), (key2722, 1), (key2611, 1), (key2666, 1), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1), (key2866, -2), (key2722, -2), (key2825, -2), (key2856, -2), (key2636, -2), (key2790, -2), (key2701, -2), (key2804, -2), (key2627, -2), (key2781, -2), (key2611, -2), (key2666, -2)]

theorem rawRowCheck11472 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form21 = rawRow11472 := by decide +kernel

def row11472 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11472 : row11472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11472 := by decide +kernel

theorem rowEval11472 (x : Key → ℝ) : Integer.Sparse.eval row11472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11472, Integer.Sparse.eval_collectBalanced, rawRowCheck11472]

def rawRow11473 : Integer.Sparse Key := [(key2981, 1), (key2974, 1), (key2958, 1), (key2941, 1), (key2947, 1), (key2935, 1), (key2902, 1), (key2895, 1), (key2745, 1), (key2651, 1), (key2734, 1), (key2645, 1), (key2825, 1), (key2790, 1), (key2722, 1), (key2636, 1), (key2666, 1), (key2611, 1), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1), (key2866, -2), (key2825, -2), (key2722, -2), (key2856, -2), (key2790, -2), (key2636, -2), (key2804, -2), (key2701, -2), (key2781, -2), (key2627, -2), (key2666, -2), (key2611, -2)]

theorem rawRowCheck11473 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form21 = rawRow11473 := by decide +kernel

def row11473 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rowCheck11473 : row11473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11473 := by decide +kernel

theorem rowEval11473 (x : Key → ℝ) : Integer.Sparse.eval row11473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck11473, Integer.Sparse.eval_collectBalanced, rawRowCheck11473]

def rawRow11474 : Integer.Sparse Key := [(key2611, 1), (key2611, 1), (key2627, 1), (key2627, 1), (key2636, 1), (key2636, 1), (key2666, 1), (key2666, 1), (key2781, 1), (key2781, 1), (key2790, 1), (key2790, 1), (key2701, 1), (key2701, 1), (key2804, 1), (key2804, 1), (key2856, 1), (key2856, 1), (key2722, 1), (key2722, 1), (key2825, 1), (key2825, 1), (key2866, 1), (key2866, 1), (key2608, -2), (key2624, -2), (key2624, -2), (key2663, -2), (key2698, -2), (key2698, -2), (key2778, -2), (key2778, -2), (key2801, -2), (key2801, -2), (key2851, -2), (key2851, -2)]

theorem rawRowCheck11474 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form21 = rawRow11474 := by decide +kernel

def row11474 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

theorem rowCheck11474 : row11474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11474 := by decide +kernel

theorem rowEval11474 (x : Key → ℝ) : Integer.Sparse.eval row11474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11474, Integer.Sparse.eval_collectBalanced, rawRowCheck11474]

def rawRow11475 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2611, 1), (key2636, 1), (key2611, 1), (key2627, 1), (key2781, 1), (key2790, 1), (key2666, 1), (key2790, 1), (key2666, 1), (key2781, 1), (key2804, 1), (key2856, 1), (key2701, 1), (key2856, 1), (key2701, 1), (key2804, 1), (key2825, 1), (key2866, 1), (key2722, 1), (key2866, 1), (key2722, 1), (key2825, 1), (key2624, -2), (key2608, -2), (key2624, -2), (key2698, -2), (key2663, -2), (key2698, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key2851, -2), (key2778, -2), (key2801, -2)]

theorem rawRowCheck11475 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form21 = rawRow11475 := by decide +kernel

def row11475 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

theorem rowCheck11475 : row11475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11475 := by decide +kernel

theorem rowEval11475 (x : Key → ℝ) : Integer.Sparse.eval row11475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11475, Integer.Sparse.eval_collectBalanced, rawRowCheck11475]

def rawRow11476 : Integer.Sparse Key := [(key2636, 1), (key2627, 1), (key2636, 1), (key2611, 1), (key2627, 1), (key2611, 1), (key2790, 1), (key2781, 1), (key2790, 1), (key2666, 1), (key2781, 1), (key2666, 1), (key2856, 1), (key2804, 1), (key2856, 1), (key2701, 1), (key2804, 1), (key2701, 1), (key2866, 1), (key2825, 1), (key2866, 1), (key2722, 1), (key2825, 1), (key2722, 1), (key2624, -2), (key2624, -2), (key2608, -2), (key2698, -2), (key2698, -2), (key2663, -2), (key2851, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key2801, -2), (key2778, -2)]

theorem rawRowCheck11476 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form21 = rawRow11476 := by decide +kernel

def row11476 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

theorem rowCheck11476 : row11476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11476 := by decide +kernel

theorem rowEval11476 (x : Key → ℝ) : Integer.Sparse.eval row11476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11476, Integer.Sparse.eval_collectBalanced, rawRowCheck11476]

def rawRow11477 : Integer.Sparse Key := [(key2666, 1), (key2666, 1), (key2701, 1), (key2701, 1), (key2722, 1), (key2722, 1), (key2611, 1), (key2611, 1), (key2804, 1), (key2804, 1), (key2825, 1), (key2825, 1), (key2627, 1), (key2627, 1), (key2781, 1), (key2781, 1), (key2866, 1), (key2866, 1), (key2636, 1), (key2636, 1), (key2790, 1), (key2790, 1), (key2856, 1), (key2856, 1), (key2663, -2), (key2698, -2), (key2698, -2), (key2608, -2), (key2801, -2), (key2801, -2), (key2624, -2), (key2624, -2), (key2698, -2), (key2698, -2), (key2851, -2), (key2851, -2)]

theorem rawRowCheck11477 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form21 = rawRow11477 := by decide +kernel

def row11477 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -8), (key2701, 2), (key2722, 2), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

theorem rowCheck11477 : row11477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11477 := by decide +kernel

theorem rowEval11477 (x : Key → ℝ) : Integer.Sparse.eval row11477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11477, Integer.Sparse.eval_collectBalanced, rawRowCheck11477]

def rawRow11478 : Integer.Sparse Key := [(key2701, 1), (key2722, 1), (key2666, 1), (key2722, 1), (key2666, 1), (key2701, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2781, 1), (key2866, 1), (key2627, 1), (key2866, 1), (key2627, 1), (key2781, 1), (key2790, 1), (key2856, 1), (key2636, 1), (key2856, 1), (key2636, 1), (key2790, 1), (key2698, -2), (key2663, -2), (key2698, -2), (key2801, -2), (key2608, -2), (key2801, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2851, -2), (key2624, -2), (key2698, -2)]

theorem rawRowCheck11478 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form21 = rawRow11478 := by decide +kernel

def row11478 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -8), (key2701, 2), (key2722, 2), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

theorem rowCheck11478 : row11478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11478 := by decide +kernel

theorem rowEval11478 (x : Key → ℝ) : Integer.Sparse.eval row11478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11478, Integer.Sparse.eval_collectBalanced, rawRowCheck11478]

def rawRow11479 : Integer.Sparse Key := [(key2722, 1), (key2701, 1), (key2722, 1), (key2666, 1), (key2701, 1), (key2666, 1), (key2825, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2611, 1), (key2866, 1), (key2781, 1), (key2866, 1), (key2627, 1), (key2781, 1), (key2627, 1), (key2856, 1), (key2790, 1), (key2856, 1), (key2636, 1), (key2790, 1), (key2636, 1), (key2698, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2801, -2), (key2608, -2), (key2851, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2624, -2)]

theorem rawRowCheck11479 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form21 = rawRow11479 := by decide +kernel

def row11479 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -8), (key2701, 2), (key2722, 2), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

theorem rowCheck11479 : row11479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11479 := by decide +kernel

theorem rowEval11479 (x : Key → ℝ) : Integer.Sparse.eval row11479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck11479, Integer.Sparse.eval_collectBalanced, rawRowCheck11479]

def rawRow11480 : Integer.Sparse Key := [(key2781, 1), (key2790, 1), (key2804, 1), (key2856, 1), (key2825, 1), (key2866, 1), (key2627, 1), (key2636, 1), (key2701, 1), (key2856, 1), (key2722, 1), (key2866, 1), (key2611, 1), (key2636, 1), (key2666, 1), (key2790, 1), (key2722, 1), (key2825, 1), (key2611, 1), (key2627, 1), (key2666, 1), (key2781, 1), (key2701, 1), (key2804, 1), (key2778, -2), (key2801, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2851, -2), (key2608, -2), (key2624, -2), (key2663, -2), (key2698, -2), (key2778, -2), (key2801, -2)]

theorem rawRowCheck11480 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form21 = rawRow11480 := by decide +kernel

def row11480 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

theorem rowCheck11480 : row11480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11480 := by decide +kernel

theorem rowEval11480 (x : Key → ℝ) : Integer.Sparse.eval row11480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11480, Integer.Sparse.eval_collectBalanced, rawRowCheck11480]

def rawRow11481 : Integer.Sparse Key := [(key2790, 1), (key2781, 1), (key2856, 1), (key2804, 1), (key2866, 1), (key2825, 1), (key2636, 1), (key2627, 1), (key2856, 1), (key2701, 1), (key2866, 1), (key2722, 1), (key2636, 1), (key2611, 1), (key2790, 1), (key2666, 1), (key2825, 1), (key2722, 1), (key2627, 1), (key2611, 1), (key2781, 1), (key2666, 1), (key2804, 1), (key2701, 1), (key2778, -2), (key2851, -2), (key2801, -2), (key2624, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2608, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2778, -2)]

theorem rawRowCheck11481 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form21 = rawRow11481 := by decide +kernel

def row11481 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

theorem rowCheck11481 : row11481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11481 := by decide +kernel

theorem rowEval11481 (x : Key → ℝ) : Integer.Sparse.eval row11481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11481, Integer.Sparse.eval_collectBalanced, rawRowCheck11481]

def rawRow11482 : Integer.Sparse Key := [(key2804, 1), (key2825, 1), (key2781, 1), (key2866, 1), (key2790, 1), (key2856, 1), (key2701, 1), (key2722, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2856, 1), (key2666, 1), (key2722, 1), (key2611, 1), (key2825, 1), (key2636, 1), (key2790, 1), (key2666, 1), (key2701, 1), (key2611, 1), (key2804, 1), (key2627, 1), (key2781, 1), (key2801, -2), (key2778, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2851, -2), (key2663, -2), (key2698, -2), (key2608, -2), (key2801, -2), (key2624, -2), (key2698, -2)]

theorem rawRowCheck11482 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form21 = rawRow11482 := by decide +kernel

def row11482 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -6), (key2701, 2), (key2722, 2), (key2778, -2), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

theorem rowCheck11482 : row11482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11482 := by decide +kernel

theorem rowEval11482 (x : Key → ℝ) : Integer.Sparse.eval row11482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11482, Integer.Sparse.eval_collectBalanced, rawRowCheck11482]

def rawRow11483 : Integer.Sparse Key := [(key2825, 1), (key2804, 1), (key2866, 1), (key2781, 1), (key2856, 1), (key2790, 1), (key2722, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2856, 1), (key2636, 1), (key2722, 1), (key2666, 1), (key2825, 1), (key2611, 1), (key2790, 1), (key2636, 1), (key2701, 1), (key2666, 1), (key2804, 1), (key2611, 1), (key2781, 1), (key2627, 1), (key2801, -2), (key2851, -2), (key2778, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2608, -2), (key2698, -2), (key2624, -2)]

theorem rawRowCheck11483 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form21 = rawRow11483 := by decide +kernel

def row11483 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -6), (key2701, 2), (key2722, 2), (key2778, -2), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

theorem rowCheck11483 : row11483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11483 := by decide +kernel

theorem rowEval11483 (x : Key → ℝ) : Integer.Sparse.eval row11483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck11483, Integer.Sparse.eval_collectBalanced, rawRowCheck11483]

def rawRow11484 : Integer.Sparse Key := [(key2856, 1), (key2866, 1), (key2790, 1), (key2825, 1), (key2781, 1), (key2804, 1), (key2856, 1), (key2866, 1), (key2636, 1), (key2722, 1), (key2627, 1), (key2701, 1), (key2790, 1), (key2825, 1), (key2636, 1), (key2722, 1), (key2611, 1), (key2666, 1), (key2781, 1), (key2804, 1), (key2627, 1), (key2701, 1), (key2611, 1), (key2666, 1), (key2851, -2), (key2778, -2), (key2801, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2778, -2), (key2801, -2), (key2624, -2), (key2698, -2), (key2608, -2), (key2663, -2)]

theorem rawRowCheck11484 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form21 = rawRow11484 := by decide +kernel

def row11484 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

theorem rowCheck11484 : row11484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11484 := by decide +kernel

theorem rowEval11484 (x : Key → ℝ) : Integer.Sparse.eval row11484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11484, Integer.Sparse.eval_collectBalanced, rawRowCheck11484]

def rawRow11485 : Integer.Sparse Key := [(key2866, 1), (key2856, 1), (key2825, 1), (key2790, 1), (key2804, 1), (key2781, 1), (key2866, 1), (key2856, 1), (key2722, 1), (key2636, 1), (key2701, 1), (key2627, 1), (key2825, 1), (key2790, 1), (key2722, 1), (key2636, 1), (key2666, 1), (key2611, 1), (key2804, 1), (key2781, 1), (key2701, 1), (key2627, 1), (key2666, 1), (key2611, 1), (key2851, -2), (key2801, -2), (key2778, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2801, -2), (key2778, -2), (key2698, -2), (key2624, -2), (key2663, -2), (key2608, -2)]

theorem rawRowCheck11485 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form21 = rawRow11485 := by decide +kernel

def row11485 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

theorem rowCheck11485 : row11485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11485 := by decide +kernel

theorem rowEval11485 (x : Key → ℝ) : Integer.Sparse.eval row11485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck11485, Integer.Sparse.eval_collectBalanced, rawRowCheck11485]

def rawRow11486 : Integer.Sparse Key := [(key2378, 2), (key2378, 2), (key2381, 2), (key2472, 2), (key2472, 2), (key2538, 2), (key2503, 2), (key2506, 2), (key2503, 2), (key2554, 2), (key2506, 2), (key2554, 2), (key2390, -2), (key2392, -2), (key2392, -2), (key2480, -2), (key2482, -2), (key2480, -2), (key2543, -2), (key2482, -2), (key2543, -2), (key2522, -2), (key2522, -2), (key2563, -2)]

theorem rawRowCheck11486 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form0 = rawRow11486 := by decide +kernel

def row11486 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck11486 : row11486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11486 := by decide +kernel

theorem rowEval11486 (x : Key → ℝ) : Integer.Sparse.eval row11486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck11486, Integer.Sparse.eval_collectBalanced, rawRowCheck11486]

def rawRow11487 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2378, 2), (key2472, 2), (key2538, 2), (key2472, 2), (key2506, 2), (key2503, 2), (key2554, 2), (key2503, 2), (key2554, 2), (key2506, 2), (key2392, -2), (key2390, -2), (key2392, -2), (key2482, -2), (key2480, -2), (key2543, -2), (key2480, -2), (key2543, -2), (key2482, -2), (key2522, -2), (key2563, -2), (key2522, -2)]

theorem rawRowCheck11487 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form0 = rawRow11487 := by decide +kernel

def row11487 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck11487 : row11487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11487 := by decide +kernel

theorem rowEval11487 (x : Key → ℝ) : Integer.Sparse.eval row11487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck11487, Integer.Sparse.eval_collectBalanced, rawRowCheck11487]

def rawRow11488 : Integer.Sparse Key := [(key2381, 2), (key2378, 2), (key2378, 2), (key2538, 2), (key2472, 2), (key2472, 2), (key2554, 2), (key2554, 2), (key2506, 2), (key2506, 2), (key2503, 2), (key2503, 2), (key2392, -2), (key2392, -2), (key2390, -2), (key2543, -2), (key2543, -2), (key2482, -2), (key2482, -2), (key2480, -2), (key2480, -2), (key2563, -2), (key2522, -2), (key2522, -2)]

theorem rawRowCheck11488 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form0 = rawRow11488 := by decide +kernel

def row11488 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck11488 : row11488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11488 := by decide +kernel

theorem rowEval11488 (x : Key → ℝ) : Integer.Sparse.eval row11488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck11488, Integer.Sparse.eval_collectBalanced, rawRowCheck11488]

def rawRow11489 : Integer.Sparse Key := [(key2472, 2), (key2503, 2), (key2506, 2), (key2378, 2), (key2503, 2), (key2554, 2), (key2378, 2), (key2381, 2), (key2472, 2), (key2538, 2), (key2506, 2), (key2554, 2), (key2480, -2), (key2482, -2), (key2522, -2), (key2390, -2), (key2392, -2), (key2480, -2), (key2543, -2), (key2522, -2), (key2563, -2), (key2392, -2), (key2482, -2), (key2543, -2)]

theorem rawRowCheck11489 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form0 = rawRow11489 := by decide +kernel

def row11489 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck11489 : row11489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11489 := by decide +kernel

theorem rowEval11489 (x : Key → ℝ) : Integer.Sparse.eval row11489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck11489, Integer.Sparse.eval_collectBalanced, rawRowCheck11489]

def rawRow11490 : Integer.Sparse Key := [(key2472, 2), (key2506, 2), (key2503, 2), (key2378, 2), (key2554, 2), (key2503, 2), (key2381, 2), (key2378, 2), (key2538, 2), (key2472, 2), (key2554, 2), (key2506, 2), (key2482, -2), (key2480, -2), (key2522, -2), (key2392, -2), (key2390, -2), (key2543, -2), (key2480, -2), (key2563, -2), (key2522, -2), (key2392, -2), (key2543, -2), (key2482, -2)]

theorem rawRowCheck11490 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form0 = rawRow11490 := by decide +kernel

def row11490 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck11490 : row11490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11490 := by decide +kernel

theorem rowEval11490 (x : Key → ℝ) : Integer.Sparse.eval row11490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck11490, Integer.Sparse.eval_collectBalanced, rawRowCheck11490]

def rawRow11491 : Integer.Sparse Key := [(key2503, 2), (key2472, 2), (key2506, 2), (key2503, 2), (key2378, 2), (key2554, 2), (key2472, 2), (key2506, 2), (key2378, 2), (key2554, 2), (key2381, 2), (key2538, 2), (key2480, -2), (key2522, -2), (key2482, -2), (key2480, -2), (key2522, -2), (key2390, -2), (key2563, -2), (key2392, -2), (key2543, -2), (key2482, -2), (key2392, -2), (key2543, -2)]

theorem rawRowCheck11491 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form0 = rawRow11491 := by decide +kernel

def row11491 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck11491 : row11491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11491 := by decide +kernel

theorem rowEval11491 (x : Key → ℝ) : Integer.Sparse.eval row11491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck11491, Integer.Sparse.eval_collectBalanced, rawRowCheck11491]

def rawRow11492 : Integer.Sparse Key := [(key2503, 2), (key2506, 2), (key2472, 2), (key2503, 2), (key2554, 2), (key2378, 2), (key2506, 2), (key2472, 2), (key2554, 2), (key2378, 2), (key2538, 2), (key2381, 2), (key2522, -2), (key2480, -2), (key2482, -2), (key2522, -2), (key2480, -2), (key2563, -2), (key2390, -2), (key2543, -2), (key2392, -2), (key2482, -2), (key2543, -2), (key2392, -2)]

theorem rawRowCheck11492 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form0 = rawRow11492 := by decide +kernel

def row11492 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck11492 : row11492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11492 := by decide +kernel

theorem rowEval11492 (x : Key → ℝ) : Integer.Sparse.eval row11492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck11492, Integer.Sparse.eval_collectBalanced, rawRowCheck11492]

def rawRow11493 : Integer.Sparse Key := [(key2506, 2), (key2472, 2), (key2503, 2), (key2554, 2), (key2378, 2), (key2503, 2), (key2538, 2), (key2554, 2), (key2381, 2), (key2506, 2), (key2378, 2), (key2472, 2), (key2482, -2), (key2522, -2), (key2480, -2), (key2543, -2), (key2563, -2), (key2392, -2), (key2522, -2), (key2390, -2), (key2480, -2), (key2543, -2), (key2392, -2), (key2482, -2)]

theorem rawRowCheck11493 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form0 = rawRow11493 := by decide +kernel

def row11493 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck11493 : row11493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11493 := by decide +kernel

theorem rowEval11493 (x : Key → ℝ) : Integer.Sparse.eval row11493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck11493, Integer.Sparse.eval_collectBalanced, rawRowCheck11493]

def rawRow11494 : Integer.Sparse Key := [(key2506, 2), (key2503, 2), (key2472, 2), (key2554, 2), (key2503, 2), (key2378, 2), (key2554, 2), (key2538, 2), (key2506, 2), (key2381, 2), (key2472, 2), (key2378, 2), (key2522, -2), (key2482, -2), (key2480, -2), (key2563, -2), (key2543, -2), (key2522, -2), (key2392, -2), (key2480, -2), (key2390, -2), (key2543, -2), (key2482, -2), (key2392, -2)]

theorem rawRowCheck11494 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form0 = rawRow11494 := by decide +kernel

def row11494 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck11494 : row11494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11494 := by decide +kernel

theorem rowEval11494 (x : Key → ℝ) : Integer.Sparse.eval row11494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck11494, Integer.Sparse.eval_collectBalanced, rawRowCheck11494]

def rawRow11495 : Integer.Sparse Key := [(key2538, 2), (key2554, 2), (key2554, 2), (key2381, 2), (key2506, 2), (key2506, 2), (key2378, 2), (key2378, 2), (key2472, 2), (key2472, 2), (key2503, 2), (key2503, 2), (key2543, -2), (key2543, -2), (key2563, -2), (key2392, -2), (key2392, -2), (key2482, -2), (key2482, -2), (key2522, -2), (key2522, -2), (key2390, -2), (key2480, -2), (key2480, -2)]

theorem rawRowCheck11495 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form0 = rawRow11495 := by decide +kernel

def row11495 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck11495 : row11495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11495 := by decide +kernel

theorem rowEval11495 (x : Key → ℝ) : Integer.Sparse.eval row11495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck11495, Integer.Sparse.eval_collectBalanced, rawRowCheck11495]

def rawRow11496 : Integer.Sparse Key := [(key2554, 2), (key2538, 2), (key2554, 2), (key2506, 2), (key2381, 2), (key2506, 2), (key2472, 2), (key2503, 2), (key2378, 2), (key2503, 2), (key2378, 2), (key2472, 2), (key2543, -2), (key2563, -2), (key2543, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2480, -2), (key2390, -2), (key2480, -2)]

theorem rawRowCheck11496 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form0 = rawRow11496 := by decide +kernel

def row11496 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck11496 : row11496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11496 := by decide +kernel

theorem rowEval11496 (x : Key → ℝ) : Integer.Sparse.eval row11496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck11496, Integer.Sparse.eval_collectBalanced, rawRowCheck11496]

def rawRow11497 : Integer.Sparse Key := [(key2554, 2), (key2554, 2), (key2538, 2), (key2506, 2), (key2506, 2), (key2381, 2), (key2503, 2), (key2472, 2), (key2503, 2), (key2378, 2), (key2472, 2), (key2378, 2), (key2563, -2), (key2543, -2), (key2543, -2), (key2522, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2392, -2), (key2480, -2), (key2480, -2), (key2390, -2)]

theorem rawRowCheck11497 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form0 = rawRow11497 := by decide +kernel

def row11497 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck11497 : row11497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11497 := by decide +kernel

theorem rowEval11497 (x : Key → ℝ) : Integer.Sparse.eval row11497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck11497, Integer.Sparse.eval_collectBalanced, rawRowCheck11497]

def rawRow11498 : Integer.Sparse Key := [(key1025, -24), (key990, 6), (key1103, 6), (key1103, 6), (key1187, 6)]

theorem rawRowCheck11498 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form1 = rawRow11498 := by decide +kernel

def row11498 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

theorem rowCheck11498 : row11498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11498 := by decide +kernel

theorem rowEval11498 (x : Key → ℝ) : Integer.Sparse.eval row11498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11498, Integer.Sparse.eval_collectBalanced, rawRowCheck11498]

def rawRow11499 : Integer.Sparse Key := [(key1025, -24), (key990, 6), (key1103, 6), (key1187, 6), (key1103, 6)]

theorem rawRowCheck11499 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form1 = rawRow11499 := by decide +kernel

def row11499 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

theorem rowCheck11499 : row11499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11499 := by decide +kernel

theorem rowEval11499 (x : Key → ℝ) : Integer.Sparse.eval row11499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11499, Integer.Sparse.eval_collectBalanced, rawRowCheck11499]

def rawRow11500 : Integer.Sparse Key := [(key1025, -24), (key990, 6), (key1187, 6), (key1103, 6), (key1103, 6)]

theorem rawRowCheck11500 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form1 = rawRow11500 := by decide +kernel

def row11500 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

theorem rowCheck11500 : row11500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11500 := by decide +kernel

theorem rowEval11500 (x : Key → ℝ) : Integer.Sparse.eval row11500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11500, Integer.Sparse.eval_collectBalanced, rawRowCheck11500]

def rawRow11501 : Integer.Sparse Key := [(key1025, -24), (key1103, 6), (key990, 6), (key1103, 6), (key1187, 6)]

theorem rawRowCheck11501 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form1 = rawRow11501 := by decide +kernel

def row11501 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

theorem rowCheck11501 : row11501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11501 := by decide +kernel

theorem rowEval11501 (x : Key → ℝ) : Integer.Sparse.eval row11501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11501, Integer.Sparse.eval_collectBalanced, rawRowCheck11501]

def rawRow11502 : Integer.Sparse Key := [(key1025, -24), (key1103, 6), (key990, 6), (key1187, 6), (key1103, 6)]

theorem rawRowCheck11502 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form1 = rawRow11502 := by decide +kernel

def row11502 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

theorem rowCheck11502 : row11502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11502 := by decide +kernel

theorem rowEval11502 (x : Key → ℝ) : Integer.Sparse.eval row11502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11502, Integer.Sparse.eval_collectBalanced, rawRowCheck11502]

def rawRow11503 : Integer.Sparse Key := [(key1025, -24), (key1103, 6), (key1103, 6), (key990, 6), (key1187, 6)]

theorem rawRowCheck11503 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form1 = rawRow11503 := by decide +kernel

def row11503 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

theorem rowCheck11503 : row11503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11503 := by decide +kernel

theorem rowEval11503 (x : Key → ℝ) : Integer.Sparse.eval row11503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11503, Integer.Sparse.eval_collectBalanced, rawRowCheck11503]

def rawRow11504 : Integer.Sparse Key := [(key1025, -24), (key1103, 6), (key1103, 6), (key1187, 6), (key990, 6)]

theorem rawRowCheck11504 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form1 = rawRow11504 := by decide +kernel

def row11504 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

theorem rowCheck11504 : row11504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11504 := by decide +kernel

theorem rowEval11504 (x : Key → ℝ) : Integer.Sparse.eval row11504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck11504, Integer.Sparse.eval_collectBalanced, rawRowCheck11504]

def rawRow11505 : Integer.Sparse Key := [(key1025, -24), (key1103, 6), (key1187, 6), (key990, 6), (key1103, 6)]

theorem rawRowCheck11505 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form1 = rawRow11505 := by decide +kernel

def row11505 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

theorem rowCheck11505 : row11505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11505 := by decide +kernel

theorem rowEval11505 (x : Key → ℝ) : Integer.Sparse.eval row11505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11505, Integer.Sparse.eval_collectBalanced, rawRowCheck11505]

def rawRow11506 : Integer.Sparse Key := [(key1025, -24), (key1103, 6), (key1187, 6), (key1103, 6), (key990, 6)]

theorem rawRowCheck11506 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form1 = rawRow11506 := by decide +kernel

def row11506 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

theorem rowCheck11506 : row11506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11506 := by decide +kernel

theorem rowEval11506 (x : Key → ℝ) : Integer.Sparse.eval row11506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck11506, Integer.Sparse.eval_collectBalanced, rawRowCheck11506]

def rawRow11507 : Integer.Sparse Key := [(key1025, -24), (key1187, 6), (key990, 6), (key1103, 6), (key1103, 6)]

theorem rawRowCheck11507 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form1 = rawRow11507 := by decide +kernel

def row11507 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

theorem rowCheck11507 : row11507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11507 := by decide +kernel

theorem rowEval11507 (x : Key → ℝ) : Integer.Sparse.eval row11507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11507, Integer.Sparse.eval_collectBalanced, rawRowCheck11507]

def rawRow11508 : Integer.Sparse Key := [(key1025, -24), (key1187, 6), (key1103, 6), (key990, 6), (key1103, 6)]

theorem rawRowCheck11508 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form1 = rawRow11508 := by decide +kernel

def row11508 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

theorem rowCheck11508 : row11508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11508 := by decide +kernel

theorem rowEval11508 (x : Key → ℝ) : Integer.Sparse.eval row11508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11508, Integer.Sparse.eval_collectBalanced, rawRowCheck11508]

def rawRow11509 : Integer.Sparse Key := [(key1025, -24), (key1187, 6), (key1103, 6), (key1103, 6), (key990, 6)]

theorem rawRowCheck11509 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form1 = rawRow11509 := by decide +kernel

def row11509 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

theorem rowCheck11509 : row11509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11509 := by decide +kernel

theorem rowEval11509 (x : Key → ℝ) : Integer.Sparse.eval row11509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck11509, Integer.Sparse.eval_collectBalanced, rawRowCheck11509]

def rawRow11510 : Integer.Sparse Key := [(key1029, -6), (key1034, -6), (key1034, -6), (key1069, -6), (key994, 2), (key999, 2), (key999, 2), (key1107, 2), (key1112, 2), (key1107, 2), (key1191, 2), (key1112, 2), (key1191, 2), (key1148, 2), (key1148, 2), (key1210, 2)]

theorem rawRowCheck11510 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form2 = rawRow11510 := by decide +kernel

def row11510 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

theorem rowCheck11510 : row11510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11510 := by decide +kernel

theorem rowEval11510 (x : Key → ℝ) : Integer.Sparse.eval row11510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11510, Integer.Sparse.eval_collectBalanced, rawRowCheck11510]

def rawRow11511 : Integer.Sparse Key := [(key1034, -6), (key1029, -6), (key1034, -6), (key1069, -6), (key999, 2), (key994, 2), (key999, 2), (key1112, 2), (key1107, 2), (key1191, 2), (key1107, 2), (key1191, 2), (key1112, 2), (key1148, 2), (key1210, 2), (key1148, 2)]

theorem rawRowCheck11511 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form2 = rawRow11511 := by decide +kernel

def row11511 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

theorem rowCheck11511 : row11511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11511 := by decide +kernel

theorem rowEval11511 (x : Key → ℝ) : Integer.Sparse.eval row11511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11511, Integer.Sparse.eval_collectBalanced, rawRowCheck11511]

def rawRow11512 : Integer.Sparse Key := [(key1034, -6), (key1034, -6), (key1029, -6), (key1069, -6), (key999, 2), (key999, 2), (key994, 2), (key1191, 2), (key1191, 2), (key1112, 2), (key1112, 2), (key1107, 2), (key1107, 2), (key1210, 2), (key1148, 2), (key1148, 2)]

theorem rawRowCheck11512 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form2 = rawRow11512 := by decide +kernel

def row11512 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

theorem rowCheck11512 : row11512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11512 := by decide +kernel

theorem rowEval11512 (x : Key → ℝ) : Integer.Sparse.eval row11512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11512, Integer.Sparse.eval_collectBalanced, rawRowCheck11512]

def rawRow11513 : Integer.Sparse Key := [(key1029, -6), (key1034, -6), (key1069, -6), (key1034, -6), (key1107, 2), (key1112, 2), (key1148, 2), (key994, 2), (key999, 2), (key1107, 2), (key1191, 2), (key1148, 2), (key1210, 2), (key999, 2), (key1112, 2), (key1191, 2)]

theorem rawRowCheck11513 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form2 = rawRow11513 := by decide +kernel

def row11513 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

theorem rowCheck11513 : row11513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11513 := by decide +kernel

theorem rowEval11513 (x : Key → ℝ) : Integer.Sparse.eval row11513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11513, Integer.Sparse.eval_collectBalanced, rawRowCheck11513]

def rawRow11514 : Integer.Sparse Key := [(key1034, -6), (key1029, -6), (key1069, -6), (key1034, -6), (key1112, 2), (key1107, 2), (key1148, 2), (key999, 2), (key994, 2), (key1191, 2), (key1107, 2), (key1210, 2), (key1148, 2), (key999, 2), (key1191, 2), (key1112, 2)]

theorem rawRowCheck11514 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form2 = rawRow11514 := by decide +kernel

def row11514 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

theorem rowCheck11514 : row11514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11514 := by decide +kernel

theorem rowEval11514 (x : Key → ℝ) : Integer.Sparse.eval row11514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11514, Integer.Sparse.eval_collectBalanced, rawRowCheck11514]

def rawRow11515 : Integer.Sparse Key := [(key1029, -6), (key1069, -6), (key1034, -6), (key1034, -6), (key1107, 2), (key1148, 2), (key1112, 2), (key1107, 2), (key1148, 2), (key994, 2), (key1210, 2), (key999, 2), (key1191, 2), (key1112, 2), (key999, 2), (key1191, 2)]

theorem rawRowCheck11515 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form2 = rawRow11515 := by decide +kernel

def row11515 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

theorem rowCheck11515 : row11515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11515 := by decide +kernel

theorem rowEval11515 (x : Key → ℝ) : Integer.Sparse.eval row11515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11515, Integer.Sparse.eval_collectBalanced, rawRowCheck11515]

def rawRow11516 : Integer.Sparse Key := [(key1069, -6), (key1029, -6), (key1034, -6), (key1034, -6), (key1148, 2), (key1107, 2), (key1112, 2), (key1148, 2), (key1107, 2), (key1210, 2), (key994, 2), (key1191, 2), (key999, 2), (key1112, 2), (key1191, 2), (key999, 2)]

theorem rawRowCheck11516 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form2 = rawRow11516 := by decide +kernel

def row11516 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

theorem rowCheck11516 : row11516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11516 := by decide +kernel

theorem rowEval11516 (x : Key → ℝ) : Integer.Sparse.eval row11516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck11516, Integer.Sparse.eval_collectBalanced, rawRowCheck11516]

def rawRow11517 : Integer.Sparse Key := [(key1034, -6), (key1069, -6), (key1029, -6), (key1034, -6), (key1112, 2), (key1148, 2), (key1107, 2), (key1191, 2), (key1210, 2), (key999, 2), (key1148, 2), (key994, 2), (key1107, 2), (key1191, 2), (key999, 2), (key1112, 2)]

theorem rawRowCheck11517 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form2 = rawRow11517 := by decide +kernel

def row11517 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

theorem rowCheck11517 : row11517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11517 := by decide +kernel

theorem rowEval11517 (x : Key → ℝ) : Integer.Sparse.eval row11517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11517, Integer.Sparse.eval_collectBalanced, rawRowCheck11517]

def rawRow11518 : Integer.Sparse Key := [(key1069, -6), (key1034, -6), (key1029, -6), (key1034, -6), (key1148, 2), (key1112, 2), (key1107, 2), (key1210, 2), (key1191, 2), (key1148, 2), (key999, 2), (key1107, 2), (key994, 2), (key1191, 2), (key1112, 2), (key999, 2)]

theorem rawRowCheck11518 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form2 = rawRow11518 := by decide +kernel

def row11518 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

theorem rowCheck11518 : row11518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11518 := by decide +kernel

theorem rowEval11518 (x : Key → ℝ) : Integer.Sparse.eval row11518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck11518, Integer.Sparse.eval_collectBalanced, rawRowCheck11518]

def rawRow11519 : Integer.Sparse Key := [(key1034, -6), (key1034, -6), (key1069, -6), (key1029, -6), (key1191, 2), (key1191, 2), (key1210, 2), (key999, 2), (key999, 2), (key1112, 2), (key1112, 2), (key1148, 2), (key1148, 2), (key994, 2), (key1107, 2), (key1107, 2)]

theorem rawRowCheck11519 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form2 = rawRow11519 := by decide +kernel

def row11519 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

theorem rowCheck11519 : row11519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11519 := by decide +kernel

theorem rowEval11519 (x : Key → ℝ) : Integer.Sparse.eval row11519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11519, Integer.Sparse.eval_collectBalanced, rawRowCheck11519]

end MUB6.Certificate.GramRows

end OAI
