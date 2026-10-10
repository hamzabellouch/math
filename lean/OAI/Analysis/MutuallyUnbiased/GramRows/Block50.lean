import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3328 : Integer.Sparse Key := [(key2763, -2), (key2930, -2), (key2767, -2), (key2767, 6), (key2840, 2), (key2967, 2), (key2844, 2), (key2844, -2), (key2588, -2), (key2875, -2), (key2888, -6), (key2888, 2), (key2599, 2), (key2909, 2)]

theorem rawRowCheck3328 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form11 = rawRow3328 := by decide +kernel

def row3328 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

theorem rowCheck3328 : row3328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3328 := by decide +kernel

theorem rowEval3328 (x : Key → ℝ) : Integer.Sparse.eval row3328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3328, Integer.Sparse.eval_collectBalanced, rawRowCheck3328]

def rawRow3329 : Integer.Sparse Key := [(key2930, -2), (key2763, -2), (key2767, -2), (key2767, 6), (key2967, 2), (key2840, 2), (key2844, 2), (key2844, -2), (key2875, -2), (key2588, -2), (key2888, -6), (key2888, 2), (key2909, 2), (key2599, 2)]

theorem rawRowCheck3329 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form11 = rawRow3329 := by decide +kernel

def row3329 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

theorem rowCheck3329 : row3329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3329 := by decide +kernel

theorem rowEval3329 (x : Key → ℝ) : Integer.Sparse.eval row3329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3329, Integer.Sparse.eval_collectBalanced, rawRowCheck3329]

def rawRow3330 : Integer.Sparse Key := [(key2767, -2), (key2930, -2), (key2763, -2), (key2767, 6), (key2844, 2), (key2967, 2), (key2840, 2), (key2875, -2), (key2588, -2), (key2844, -2), (key2888, -6), (key2909, 2), (key2599, 2), (key2888, 2)]

theorem rawRowCheck3330 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form11 = rawRow3330 := by decide +kernel

def row3330 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

theorem rowCheck3330 : row3330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3330 := by decide +kernel

theorem rowEval3330 (x : Key → ℝ) : Integer.Sparse.eval row3330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3330, Integer.Sparse.eval_collectBalanced, rawRowCheck3330]

def rawRow3331 : Integer.Sparse Key := [(key2930, -2), (key2767, -2), (key2763, -2), (key2767, 6), (key2967, 2), (key2844, 2), (key2840, 2), (key2875, -2), (key2844, -2), (key2588, -2), (key2888, -6), (key2909, 2), (key2888, 2), (key2599, 2)]

theorem rawRowCheck3331 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form11 = rawRow3331 := by decide +kernel

def row3331 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

theorem rowCheck3331 : row3331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3331 := by decide +kernel

theorem rowEval3331 (x : Key → ℝ) : Integer.Sparse.eval row3331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3331, Integer.Sparse.eval_collectBalanced, rawRowCheck3331]

def rawRow3332 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2930, -2), (key2763, 6), (key2875, 2), (key2875, 2), (key2988, 2), (key2584, -2), (key2840, -2), (key2840, -2), (key2909, -6), (key2599, 2), (key2888, 2), (key2888, 2)]

theorem rawRowCheck3332 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form11 = rawRow3332 := by decide +kernel

def row3332 : Integer.Sparse Key := [(key2584, -2), (key2599, 2), (key2763, 6), (key2767, -4), (key2840, -4), (key2875, 4), (key2888, 4), (key2909, -6), (key2930, -2), (key2988, 2)]

theorem rowCheck3332 : row3332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3332 := by decide +kernel

theorem rowEval3332 (x : Key → ℝ) : Integer.Sparse.eval row3332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3332, Integer.Sparse.eval_collectBalanced, rawRowCheck3332]

def rawRow3333 : Integer.Sparse Key := [(key2767, -2), (key2930, -2), (key2767, -2), (key2763, 6), (key2875, 2), (key2988, 2), (key2875, 2), (key2840, -2), (key2584, -2), (key2840, -2), (key2909, -6), (key2888, 2), (key2599, 2), (key2888, 2)]

theorem rawRowCheck3333 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form11 = rawRow3333 := by decide +kernel

def row3333 : Integer.Sparse Key := [(key2584, -2), (key2599, 2), (key2763, 6), (key2767, -4), (key2840, -4), (key2875, 4), (key2888, 4), (key2909, -6), (key2930, -2), (key2988, 2)]

theorem rowCheck3333 : row3333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3333 := by decide +kernel

theorem rowEval3333 (x : Key → ℝ) : Integer.Sparse.eval row3333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3333, Integer.Sparse.eval_collectBalanced, rawRowCheck3333]

def rawRow3334 : Integer.Sparse Key := [(key2930, -2), (key2767, -2), (key2767, -2), (key2763, 6), (key2988, 2), (key2875, 2), (key2875, 2), (key2840, -2), (key2840, -2), (key2584, -2), (key2909, -6), (key2888, 2), (key2888, 2), (key2599, 2)]

theorem rawRowCheck3334 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form11 = rawRow3334 := by decide +kernel

def row3334 : Integer.Sparse Key := [(key2584, -2), (key2599, 2), (key2763, 6), (key2767, -4), (key2840, -4), (key2875, 4), (key2888, 4), (key2909, -6), (key2930, -2), (key2988, 2)]

theorem rowCheck3334 : row3334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3334 := by decide +kernel

theorem rowEval3334 (x : Key → ℝ) : Integer.Sparse.eval row3334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3334, Integer.Sparse.eval_collectBalanced, rawRowCheck3334]

def rawRow3335 : Integer.Sparse Key := [(key2840, -2), (key2844, -2), (key2967, -2), (key2888, 6), (key2763, 2), (key2767, 2), (key2930, 2), (key2599, -2), (key2888, -2), (key2909, -2), (key2767, -6), (key2588, 2), (key2844, 2), (key2875, 2)]

theorem rawRowCheck3335 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form11 = rawRow3335 := by decide +kernel

def row3335 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

theorem rowCheck3335 : row3335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3335 := by decide +kernel

theorem rowEval3335 (x : Key → ℝ) : Integer.Sparse.eval row3335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3335, Integer.Sparse.eval_collectBalanced, rawRowCheck3335]

def rawRow3336 : Integer.Sparse Key := [(key2844, -2), (key2840, -2), (key2967, -2), (key2888, 6), (key2767, 2), (key2763, 2), (key2930, 2), (key2599, -2), (key2909, -2), (key2888, -2), (key2767, -6), (key2588, 2), (key2875, 2), (key2844, 2)]

theorem rawRowCheck3336 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form11 = rawRow3336 := by decide +kernel

def row3336 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

theorem rowCheck3336 : row3336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3336 := by decide +kernel

theorem rowEval3336 (x : Key → ℝ) : Integer.Sparse.eval row3336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3336, Integer.Sparse.eval_collectBalanced, rawRowCheck3336]

def rawRow3337 : Integer.Sparse Key := [(key2840, -2), (key2967, -2), (key2844, -2), (key2888, 6), (key2763, 2), (key2930, 2), (key2767, 2), (key2888, -2), (key2599, -2), (key2909, -2), (key2767, -6), (key2844, 2), (key2588, 2), (key2875, 2)]

theorem rawRowCheck3337 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form11 = rawRow3337 := by decide +kernel

def row3337 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

theorem rowCheck3337 : row3337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3337 := by decide +kernel

theorem rowEval3337 (x : Key → ℝ) : Integer.Sparse.eval row3337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3337, Integer.Sparse.eval_collectBalanced, rawRowCheck3337]

def rawRow3338 : Integer.Sparse Key := [(key2967, -2), (key2840, -2), (key2844, -2), (key2888, 6), (key2930, 2), (key2763, 2), (key2767, 2), (key2888, -2), (key2909, -2), (key2599, -2), (key2767, -6), (key2844, 2), (key2875, 2), (key2588, 2)]

theorem rawRowCheck3338 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form11 = rawRow3338 := by decide +kernel

def row3338 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

theorem rowCheck3338 : row3338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3338 := by decide +kernel

theorem rowEval3338 (x : Key → ℝ) : Integer.Sparse.eval row3338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3338, Integer.Sparse.eval_collectBalanced, rawRowCheck3338]

def rawRow3339 : Integer.Sparse Key := [(key2844, -2), (key2967, -2), (key2840, -2), (key2888, 6), (key2767, 2), (key2930, 2), (key2763, 2), (key2909, -2), (key2599, -2), (key2888, -2), (key2767, -6), (key2875, 2), (key2588, 2), (key2844, 2)]

theorem rawRowCheck3339 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form11 = rawRow3339 := by decide +kernel

def row3339 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

theorem rowCheck3339 : row3339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3339 := by decide +kernel

theorem rowEval3339 (x : Key → ℝ) : Integer.Sparse.eval row3339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3339, Integer.Sparse.eval_collectBalanced, rawRowCheck3339]

def rawRow3340 : Integer.Sparse Key := [(key2967, -2), (key2844, -2), (key2840, -2), (key2888, 6), (key2930, 2), (key2767, 2), (key2763, 2), (key2909, -2), (key2888, -2), (key2599, -2), (key2767, -6), (key2875, 2), (key2844, 2), (key2588, 2)]

theorem rawRowCheck3340 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form11 = rawRow3340 := by decide +kernel

def row3340 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

theorem rowCheck3340 : row3340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3340 := by decide +kernel

theorem rowEval3340 (x : Key → ℝ) : Integer.Sparse.eval row3340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3340, Integer.Sparse.eval_collectBalanced, rawRowCheck3340]

def rawRow3341 : Integer.Sparse Key := [(key2844, -2), (key2888, -2), (key2967, -2), (key2840, 6), (key2875, 2), (key2909, 2), (key2988, 2), (key2584, -2), (key2763, -2), (key2840, -2), (key2875, -6), (key2588, 2), (key2767, 2), (key2844, 2)]

theorem rawRowCheck3341 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form11 = rawRow3341 := by decide +kernel

def row3341 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck3341 : row3341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3341 := by decide +kernel

theorem rowEval3341 (x : Key → ℝ) : Integer.Sparse.eval row3341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3341, Integer.Sparse.eval_collectBalanced, rawRowCheck3341]

def rawRow3342 : Integer.Sparse Key := [(key2888, -2), (key2844, -2), (key2967, -2), (key2840, 6), (key2909, 2), (key2875, 2), (key2988, 2), (key2584, -2), (key2840, -2), (key2763, -2), (key2875, -6), (key2588, 2), (key2844, 2), (key2767, 2)]

theorem rawRowCheck3342 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form11 = rawRow3342 := by decide +kernel

def row3342 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck3342 : row3342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3342 := by decide +kernel

theorem rowEval3342 (x : Key → ℝ) : Integer.Sparse.eval row3342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck3342, Integer.Sparse.eval_collectBalanced, rawRowCheck3342]

def rawRow3343 : Integer.Sparse Key := [(key2844, -2), (key2967, -2), (key2888, -2), (key2840, 6), (key2875, 2), (key2988, 2), (key2909, 2), (key2763, -2), (key2584, -2), (key2840, -2), (key2875, -6), (key2767, 2), (key2588, 2), (key2844, 2)]

theorem rawRowCheck3343 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form11 = rawRow3343 := by decide +kernel

def row3343 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck3343 : row3343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3343 := by decide +kernel

theorem rowEval3343 (x : Key → ℝ) : Integer.Sparse.eval row3343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3343, Integer.Sparse.eval_collectBalanced, rawRowCheck3343]

def rawRow3344 : Integer.Sparse Key := [(key2967, -2), (key2844, -2), (key2888, -2), (key2840, 6), (key2988, 2), (key2875, 2), (key2909, 2), (key2763, -2), (key2840, -2), (key2584, -2), (key2875, -6), (key2767, 2), (key2844, 2), (key2588, 2)]

theorem rawRowCheck3344 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form11 = rawRow3344 := by decide +kernel

def row3344 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck3344 : row3344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3344 := by decide +kernel

theorem rowEval3344 (x : Key → ℝ) : Integer.Sparse.eval row3344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3344, Integer.Sparse.eval_collectBalanced, rawRowCheck3344]

def rawRow3345 : Integer.Sparse Key := [(key2888, -2), (key2967, -2), (key2844, -2), (key2840, 6), (key2909, 2), (key2988, 2), (key2875, 2), (key2840, -2), (key2584, -2), (key2763, -2), (key2875, -6), (key2844, 2), (key2588, 2), (key2767, 2)]

theorem rawRowCheck3345 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form11 = rawRow3345 := by decide +kernel

def row3345 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck3345 : row3345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3345 := by decide +kernel

theorem rowEval3345 (x : Key → ℝ) : Integer.Sparse.eval row3345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck3345, Integer.Sparse.eval_collectBalanced, rawRowCheck3345]

def rawRow3346 : Integer.Sparse Key := [(key2967, -2), (key2888, -2), (key2844, -2), (key2840, 6), (key2988, 2), (key2909, 2), (key2875, 2), (key2840, -2), (key2763, -2), (key2584, -2), (key2875, -6), (key2844, 2), (key2767, 2), (key2588, 2)]

theorem rawRowCheck3346 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form11 = rawRow3346 := by decide +kernel

def row3346 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck3346 : row3346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3346 := by decide +kernel

theorem rowEval3346 (x : Key → ℝ) : Integer.Sparse.eval row3346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3346, Integer.Sparse.eval_collectBalanced, rawRowCheck3346]

def rawRow3347 : Integer.Sparse Key := [(key2875, -2), (key2875, -2), (key2988, -2), (key2909, 6), (key2767, 2), (key2767, 2), (key2930, 2), (key2599, -2), (key2888, -2), (key2888, -2), (key2763, -6), (key2584, 2), (key2840, 2), (key2840, 2)]

theorem rawRowCheck3347 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form11 = rawRow3347 := by decide +kernel

def row3347 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -6), (key2767, 4), (key2840, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, 2), (key2988, -2)]

theorem rowCheck3347 : row3347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3347 := by decide +kernel

theorem rowEval3347 (x : Key → ℝ) : Integer.Sparse.eval row3347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3347, Integer.Sparse.eval_collectBalanced, rawRowCheck3347]

def rawRow3348 : Integer.Sparse Key := [(key2875, -2), (key2988, -2), (key2875, -2), (key2909, 6), (key2767, 2), (key2930, 2), (key2767, 2), (key2888, -2), (key2599, -2), (key2888, -2), (key2763, -6), (key2840, 2), (key2584, 2), (key2840, 2)]

theorem rawRowCheck3348 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form11 = rawRow3348 := by decide +kernel

def row3348 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -6), (key2767, 4), (key2840, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, 2), (key2988, -2)]

theorem rowCheck3348 : row3348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3348 := by decide +kernel

theorem rowEval3348 (x : Key → ℝ) : Integer.Sparse.eval row3348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3348, Integer.Sparse.eval_collectBalanced, rawRowCheck3348]

def rawRow3349 : Integer.Sparse Key := [(key2988, -2), (key2875, -2), (key2875, -2), (key2909, 6), (key2930, 2), (key2767, 2), (key2767, 2), (key2888, -2), (key2888, -2), (key2599, -2), (key2763, -6), (key2840, 2), (key2840, 2), (key2584, 2)]

theorem rawRowCheck3349 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form11 = rawRow3349 := by decide +kernel

def row3349 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -6), (key2767, 4), (key2840, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, 2), (key2988, -2)]

theorem rowCheck3349 : row3349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3349 := by decide +kernel

theorem rowEval3349 (x : Key → ℝ) : Integer.Sparse.eval row3349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3349, Integer.Sparse.eval_collectBalanced, rawRowCheck3349]

def rawRow3350 : Integer.Sparse Key := [(key2875, -2), (key2909, -2), (key2988, -2), (key2875, 6), (key2844, 2), (key2888, 2), (key2967, 2), (key2588, -2), (key2767, -2), (key2844, -2), (key2840, -6), (key2584, 2), (key2763, 2), (key2840, 2)]

theorem rawRowCheck3350 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form11 = rawRow3350 := by decide +kernel

def row3350 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

theorem rowCheck3350 : row3350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3350 := by decide +kernel

theorem rowEval3350 (x : Key → ℝ) : Integer.Sparse.eval row3350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3350, Integer.Sparse.eval_collectBalanced, rawRowCheck3350]

def rawRow3351 : Integer.Sparse Key := [(key2909, -2), (key2875, -2), (key2988, -2), (key2875, 6), (key2888, 2), (key2844, 2), (key2967, 2), (key2588, -2), (key2844, -2), (key2767, -2), (key2840, -6), (key2584, 2), (key2840, 2), (key2763, 2)]

theorem rawRowCheck3351 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form11 = rawRow3351 := by decide +kernel

def row3351 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

theorem rowCheck3351 : row3351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3351 := by decide +kernel

theorem rowEval3351 (x : Key → ℝ) : Integer.Sparse.eval row3351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck3351, Integer.Sparse.eval_collectBalanced, rawRowCheck3351]

def rawRow3352 : Integer.Sparse Key := [(key2875, -2), (key2988, -2), (key2909, -2), (key2875, 6), (key2844, 2), (key2967, 2), (key2888, 2), (key2767, -2), (key2588, -2), (key2844, -2), (key2840, -6), (key2763, 2), (key2584, 2), (key2840, 2)]

theorem rawRowCheck3352 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form11 = rawRow3352 := by decide +kernel

def row3352 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

theorem rowCheck3352 : row3352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3352 := by decide +kernel

theorem rowEval3352 (x : Key → ℝ) : Integer.Sparse.eval row3352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3352, Integer.Sparse.eval_collectBalanced, rawRowCheck3352]

def rawRow3353 : Integer.Sparse Key := [(key2988, -2), (key2875, -2), (key2909, -2), (key2875, 6), (key2967, 2), (key2844, 2), (key2888, 2), (key2767, -2), (key2844, -2), (key2588, -2), (key2840, -6), (key2763, 2), (key2840, 2), (key2584, 2)]

theorem rawRowCheck3353 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form11 = rawRow3353 := by decide +kernel

def row3353 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

theorem rowCheck3353 : row3353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3353 := by decide +kernel

theorem rowEval3353 (x : Key → ℝ) : Integer.Sparse.eval row3353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3353, Integer.Sparse.eval_collectBalanced, rawRowCheck3353]

def rawRow3354 : Integer.Sparse Key := [(key2909, -2), (key2988, -2), (key2875, -2), (key2875, 6), (key2888, 2), (key2967, 2), (key2844, 2), (key2844, -2), (key2588, -2), (key2767, -2), (key2840, -6), (key2840, 2), (key2584, 2), (key2763, 2)]

theorem rawRowCheck3354 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form11 = rawRow3354 := by decide +kernel

def row3354 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

theorem rowCheck3354 : row3354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3354 := by decide +kernel

theorem rowEval3354 (x : Key → ℝ) : Integer.Sparse.eval row3354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck3354, Integer.Sparse.eval_collectBalanced, rawRowCheck3354]

def rawRow3355 : Integer.Sparse Key := [(key2988, -2), (key2909, -2), (key2875, -2), (key2875, 6), (key2967, 2), (key2888, 2), (key2844, 2), (key2844, -2), (key2767, -2), (key2588, -2), (key2840, -6), (key2840, 2), (key2763, 2), (key2584, 2)]

theorem rawRowCheck3355 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form11 = rawRow3355 := by decide +kernel

def row3355 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

theorem rowCheck3355 : row3355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3355 := by decide +kernel

theorem rowEval3355 (x : Key → ℝ) : Integer.Sparse.eval row3355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3355, Integer.Sparse.eval_collectBalanced, rawRowCheck3355]

def rawRow3356 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2937, -2), (key2664, 1), (key2668, 1), (key2779, 1), (key2791, 1), (key2937, 1), (key2942, 1), (key2802, 2), (key2806, 2), (key2949, 2), (key2609, -1), (key2613, -1), (key2802, -1), (key2826, -1), (key2949, -1), (key2959, -1), (key2699, -1), (key2703, -1), (key2852, -1), (key2857, -1), (key2973, -1), (key2975, -1), (key2625, 1), (key2629, 1), (key2852, 1), (key2867, 1), (key2973, 1), (key2982, 1)]

theorem rawRowCheck3356 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form12 = rawRow3356 := by decide +kernel

def row3356 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck3356 : row3356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3356 := by decide +kernel

theorem rowEval3356 (x : Key → ℝ) : Integer.Sparse.eval row3356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3356, Integer.Sparse.eval_collectBalanced, rawRowCheck3356]

def rawRow3357 : Integer.Sparse Key := [(key2783, -2), (key2779, -2), (key2937, -2), (key2668, 1), (key2664, 1), (key2791, 1), (key2779, 1), (key2942, 1), (key2937, 1), (key2806, 2), (key2802, 2), (key2949, 2), (key2613, -1), (key2609, -1), (key2826, -1), (key2802, -1), (key2959, -1), (key2949, -1), (key2703, -1), (key2699, -1), (key2857, -1), (key2852, -1), (key2975, -1), (key2973, -1), (key2629, 1), (key2625, 1), (key2867, 1), (key2852, 1), (key2982, 1), (key2973, 1)]

theorem rawRowCheck3357 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form12 = rawRow3357 := by decide +kernel

def row3357 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck3357 : row3357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3357 := by decide +kernel

theorem rowEval3357 (x : Key → ℝ) : Integer.Sparse.eval row3357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3357, Integer.Sparse.eval_collectBalanced, rawRowCheck3357]

def rawRow3358 : Integer.Sparse Key := [(key2779, -2), (key2937, -2), (key2783, -2), (key2779, 1), (key2937, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2802, 2), (key2949, 2), (key2806, 2), (key2802, -1), (key2949, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2852, -1), (key2973, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2852, 1), (key2973, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2867, 1)]

theorem rawRowCheck3358 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form12 = rawRow3358 := by decide +kernel

def row3358 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck3358 : row3358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3358 := by decide +kernel

theorem rowEval3358 (x : Key → ℝ) : Integer.Sparse.eval row3358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3358, Integer.Sparse.eval_collectBalanced, rawRowCheck3358]

def rawRow3359 : Integer.Sparse Key := [(key2937, -2), (key2779, -2), (key2783, -2), (key2937, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2791, 1), (key2668, 1), (key2949, 2), (key2802, 2), (key2806, 2), (key2949, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2826, -1), (key2613, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2857, -1), (key2703, -1), (key2973, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2867, 1), (key2629, 1)]

theorem rawRowCheck3359 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form12 = rawRow3359 := by decide +kernel

def row3359 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck3359 : row3359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3359 := by decide +kernel

theorem rowEval3359 (x : Key → ℝ) : Integer.Sparse.eval row3359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3359, Integer.Sparse.eval_collectBalanced, rawRowCheck3359]

def rawRow3360 : Integer.Sparse Key := [(key2783, -2), (key2937, -2), (key2779, -2), (key2791, 1), (key2942, 1), (key2668, 1), (key2937, 1), (key2664, 1), (key2779, 1), (key2806, 2), (key2949, 2), (key2802, 2), (key2826, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2609, -1), (key2802, -1), (key2857, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2699, -1), (key2852, -1), (key2867, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2625, 1), (key2852, 1)]

theorem rawRowCheck3360 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form12 = rawRow3360 := by decide +kernel

def row3360 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck3360 : row3360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3360 := by decide +kernel

theorem rowEval3360 (x : Key → ℝ) : Integer.Sparse.eval row3360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3360, Integer.Sparse.eval_collectBalanced, rawRowCheck3360]

def rawRow3361 : Integer.Sparse Key := [(key2937, -2), (key2783, -2), (key2779, -2), (key2942, 1), (key2791, 1), (key2937, 1), (key2668, 1), (key2779, 1), (key2664, 1), (key2949, 2), (key2806, 2), (key2802, 2), (key2959, -1), (key2826, -1), (key2949, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2975, -1), (key2857, -1), (key2973, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2982, 1), (key2867, 1), (key2973, 1), (key2629, 1), (key2852, 1), (key2625, 1)]

theorem rawRowCheck3361 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form12 = rawRow3361 := by decide +kernel

def row3361 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck3361 : row3361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3361 := by decide +kernel

theorem rowEval3361 (x : Key → ℝ) : Integer.Sparse.eval row3361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3361, Integer.Sparse.eval_collectBalanced, rawRowCheck3361]

def rawRow3362 : Integer.Sparse Key := [(key2791, -2), (key2791, -2), (key2942, -2), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2937, 1), (key2937, 1), (key2826, 2), (key2826, 2), (key2959, 2), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2949, -1), (key2949, -1), (key2723, -1), (key2723, -1), (key2867, -1), (key2867, -1), (key2982, -1), (key2982, -1), (key2637, 1), (key2637, 1), (key2857, 1), (key2857, 1), (key2975, 1), (key2975, 1)]

theorem rawRowCheck3362 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form12 = rawRow3362 := by decide +kernel

def row3362 : Integer.Sparse Key := [(key2613, -2), (key2637, 2), (key2668, 2), (key2723, -2), (key2783, 2), (key2791, -4), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

theorem rowCheck3362 : row3362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3362 := by decide +kernel

theorem rowEval3362 (x : Key → ℝ) : Integer.Sparse.eval row3362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3362, Integer.Sparse.eval_collectBalanced, rawRowCheck3362]

def rawRow3363 : Integer.Sparse Key := [(key2791, -2), (key2942, -2), (key2791, -2), (key2783, 1), (key2937, 1), (key2668, 1), (key2937, 1), (key2668, 1), (key2783, 1), (key2826, 2), (key2959, 2), (key2826, 2), (key2806, -1), (key2949, -1), (key2613, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2867, -1), (key2982, -1), (key2723, -1), (key2982, -1), (key2723, -1), (key2867, -1), (key2857, 1), (key2975, 1), (key2637, 1), (key2975, 1), (key2637, 1), (key2857, 1)]

theorem rawRowCheck3363 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form12 = rawRow3363 := by decide +kernel

def row3363 : Integer.Sparse Key := [(key2613, -2), (key2637, 2), (key2668, 2), (key2723, -2), (key2783, 2), (key2791, -4), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

theorem rowCheck3363 : row3363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3363 := by decide +kernel

theorem rowEval3363 (x : Key → ℝ) : Integer.Sparse.eval row3363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3363, Integer.Sparse.eval_collectBalanced, rawRowCheck3363]

def rawRow3364 : Integer.Sparse Key := [(key2942, -2), (key2791, -2), (key2791, -2), (key2937, 1), (key2783, 1), (key2937, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2959, 2), (key2826, 2), (key2826, 2), (key2949, -1), (key2806, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2982, -1), (key2867, -1), (key2982, -1), (key2723, -1), (key2867, -1), (key2723, -1), (key2975, 1), (key2857, 1), (key2975, 1), (key2637, 1), (key2857, 1), (key2637, 1)]

theorem rawRowCheck3364 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form12 = rawRow3364 := by decide +kernel

def row3364 : Integer.Sparse Key := [(key2613, -2), (key2637, 2), (key2668, 2), (key2723, -2), (key2783, 2), (key2791, -4), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

theorem rowCheck3364 : row3364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3364 := by decide +kernel

theorem rowEval3364 (x : Key → ℝ) : Integer.Sparse.eval row3364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3364, Integer.Sparse.eval_collectBalanced, rawRowCheck3364]

def rawRow3365 : Integer.Sparse Key := [(key2802, -2), (key2806, -2), (key2949, -2), (key2699, 1), (key2703, 1), (key2852, 1), (key2857, 1), (key2973, 1), (key2975, 1), (key2779, 2), (key2783, 2), (key2937, 2), (key2625, -1), (key2629, -1), (key2852, -1), (key2867, -1), (key2973, -1), (key2982, -1), (key2664, -1), (key2668, -1), (key2779, -1), (key2791, -1), (key2937, -1), (key2942, -1), (key2609, 1), (key2613, 1), (key2802, 1), (key2826, 1), (key2949, 1), (key2959, 1)]

theorem rawRowCheck3365 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form12 = rawRow3365 := by decide +kernel

def row3365 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck3365 : row3365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3365 := by decide +kernel

theorem rowEval3365 (x : Key → ℝ) : Integer.Sparse.eval row3365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3365, Integer.Sparse.eval_collectBalanced, rawRowCheck3365]

def rawRow3366 : Integer.Sparse Key := [(key2806, -2), (key2802, -2), (key2949, -2), (key2703, 1), (key2699, 1), (key2857, 1), (key2852, 1), (key2975, 1), (key2973, 1), (key2783, 2), (key2779, 2), (key2937, 2), (key2629, -1), (key2625, -1), (key2867, -1), (key2852, -1), (key2982, -1), (key2973, -1), (key2668, -1), (key2664, -1), (key2791, -1), (key2779, -1), (key2942, -1), (key2937, -1), (key2613, 1), (key2609, 1), (key2826, 1), (key2802, 1), (key2959, 1), (key2949, 1)]

theorem rawRowCheck3366 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form12 = rawRow3366 := by decide +kernel

def row3366 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck3366 : row3366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3366 := by decide +kernel

theorem rowEval3366 (x : Key → ℝ) : Integer.Sparse.eval row3366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3366, Integer.Sparse.eval_collectBalanced, rawRowCheck3366]

def rawRow3367 : Integer.Sparse Key := [(key2802, -2), (key2949, -2), (key2806, -2), (key2852, 1), (key2973, 1), (key2699, 1), (key2975, 1), (key2703, 1), (key2857, 1), (key2779, 2), (key2937, 2), (key2783, 2), (key2852, -1), (key2973, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2779, -1), (key2937, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2802, 1), (key2949, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2826, 1)]

theorem rawRowCheck3367 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form12 = rawRow3367 := by decide +kernel

def row3367 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck3367 : row3367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3367 := by decide +kernel

theorem rowEval3367 (x : Key → ℝ) : Integer.Sparse.eval row3367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3367, Integer.Sparse.eval_collectBalanced, rawRowCheck3367]

def rawRow3368 : Integer.Sparse Key := [(key2949, -2), (key2802, -2), (key2806, -2), (key2973, 1), (key2852, 1), (key2975, 1), (key2699, 1), (key2857, 1), (key2703, 1), (key2937, 2), (key2779, 2), (key2783, 2), (key2973, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2867, -1), (key2629, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2791, -1), (key2668, -1), (key2949, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2826, 1), (key2613, 1)]

theorem rawRowCheck3368 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form12 = rawRow3368 := by decide +kernel

def row3368 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck3368 : row3368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3368 := by decide +kernel

theorem rowEval3368 (x : Key → ℝ) : Integer.Sparse.eval row3368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3368, Integer.Sparse.eval_collectBalanced, rawRowCheck3368]

def rawRow3369 : Integer.Sparse Key := [(key2806, -2), (key2949, -2), (key2802, -2), (key2857, 1), (key2975, 1), (key2703, 1), (key2973, 1), (key2699, 1), (key2852, 1), (key2783, 2), (key2937, 2), (key2779, 2), (key2867, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2625, -1), (key2852, -1), (key2791, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2664, -1), (key2779, -1), (key2826, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2609, 1), (key2802, 1)]

theorem rawRowCheck3369 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form12 = rawRow3369 := by decide +kernel

def row3369 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck3369 : row3369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3369 := by decide +kernel

theorem rowEval3369 (x : Key → ℝ) : Integer.Sparse.eval row3369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3369, Integer.Sparse.eval_collectBalanced, rawRowCheck3369]

def rawRow3370 : Integer.Sparse Key := [(key2949, -2), (key2806, -2), (key2802, -2), (key2975, 1), (key2857, 1), (key2973, 1), (key2703, 1), (key2852, 1), (key2699, 1), (key2937, 2), (key2783, 2), (key2779, 2), (key2982, -1), (key2867, -1), (key2973, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2942, -1), (key2791, -1), (key2937, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2959, 1), (key2826, 1), (key2949, 1), (key2613, 1), (key2802, 1), (key2609, 1)]

theorem rawRowCheck3370 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form12 = rawRow3370 := by decide +kernel

def row3370 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck3370 : row3370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3370 := by decide +kernel

theorem rowEval3370 (x : Key → ℝ) : Integer.Sparse.eval row3370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3370, Integer.Sparse.eval_collectBalanced, rawRowCheck3370]

def rawRow3371 : Integer.Sparse Key := [(key2857, -2), (key2896, -2), (key2975, -2), (key2703, 1), (key2736, 1), (key2806, 1), (key2894, 1), (key2949, 1), (key2973, 1), (key2867, 2), (key2903, 2), (key2982, 2), (key2629, -1), (key2647, -1), (key2783, -1), (key2894, -1), (key2937, -1), (key2973, -1), (key2723, -1), (key2746, -1), (key2826, -1), (key2903, -1), (key2959, -1), (key2982, -1), (key2637, 1), (key2652, 1), (key2791, 1), (key2896, 1), (key2942, 1), (key2975, 1)]

theorem rawRowCheck3371 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form12 = rawRow3371 := by decide +kernel

def row3371 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck3371 : row3371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3371 := by decide +kernel

theorem rowEval3371 (x : Key → ℝ) : Integer.Sparse.eval row3371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3371, Integer.Sparse.eval_collectBalanced, rawRowCheck3371]

def rawRow3372 : Integer.Sparse Key := [(key2896, -2), (key2857, -2), (key2975, -2), (key2736, 1), (key2703, 1), (key2894, 1), (key2806, 1), (key2973, 1), (key2949, 1), (key2903, 2), (key2867, 2), (key2982, 2), (key2647, -1), (key2629, -1), (key2894, -1), (key2783, -1), (key2973, -1), (key2937, -1), (key2746, -1), (key2723, -1), (key2903, -1), (key2826, -1), (key2982, -1), (key2959, -1), (key2652, 1), (key2637, 1), (key2896, 1), (key2791, 1), (key2975, 1), (key2942, 1)]

theorem rawRowCheck3372 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form12 = rawRow3372 := by decide +kernel

def row3372 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck3372 : row3372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3372 := by decide +kernel

theorem rowEval3372 (x : Key → ℝ) : Integer.Sparse.eval row3372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck3372, Integer.Sparse.eval_collectBalanced, rawRowCheck3372]

def rawRow3373 : Integer.Sparse Key := [(key2857, -2), (key2975, -2), (key2896, -2), (key2806, 1), (key2949, 1), (key2703, 1), (key2973, 1), (key2736, 1), (key2894, 1), (key2867, 2), (key2982, 2), (key2903, 2), (key2783, -1), (key2937, -1), (key2629, -1), (key2973, -1), (key2647, -1), (key2894, -1), (key2826, -1), (key2959, -1), (key2723, -1), (key2982, -1), (key2746, -1), (key2903, -1), (key2791, 1), (key2942, 1), (key2637, 1), (key2975, 1), (key2652, 1), (key2896, 1)]

theorem rawRowCheck3373 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form12 = rawRow3373 := by decide +kernel

def row3373 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck3373 : row3373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3373 := by decide +kernel

theorem rowEval3373 (x : Key → ℝ) : Integer.Sparse.eval row3373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3373, Integer.Sparse.eval_collectBalanced, rawRowCheck3373]

def rawRow3374 : Integer.Sparse Key := [(key2975, -2), (key2857, -2), (key2896, -2), (key2949, 1), (key2806, 1), (key2973, 1), (key2703, 1), (key2894, 1), (key2736, 1), (key2982, 2), (key2867, 2), (key2903, 2), (key2937, -1), (key2783, -1), (key2973, -1), (key2629, -1), (key2894, -1), (key2647, -1), (key2959, -1), (key2826, -1), (key2982, -1), (key2723, -1), (key2903, -1), (key2746, -1), (key2942, 1), (key2791, 1), (key2975, 1), (key2637, 1), (key2896, 1), (key2652, 1)]

theorem rawRowCheck3374 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form12 = rawRow3374 := by decide +kernel

def row3374 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck3374 : row3374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3374 := by decide +kernel

theorem rowEval3374 (x : Key → ℝ) : Integer.Sparse.eval row3374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3374, Integer.Sparse.eval_collectBalanced, rawRowCheck3374]

def rawRow3375 : Integer.Sparse Key := [(key2896, -2), (key2975, -2), (key2857, -2), (key2894, 1), (key2973, 1), (key2736, 1), (key2949, 1), (key2703, 1), (key2806, 1), (key2903, 2), (key2982, 2), (key2867, 2), (key2894, -1), (key2973, -1), (key2647, -1), (key2937, -1), (key2629, -1), (key2783, -1), (key2903, -1), (key2982, -1), (key2746, -1), (key2959, -1), (key2723, -1), (key2826, -1), (key2896, 1), (key2975, 1), (key2652, 1), (key2942, 1), (key2637, 1), (key2791, 1)]

theorem rawRowCheck3375 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form12 = rawRow3375 := by decide +kernel

def row3375 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck3375 : row3375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3375 := by decide +kernel

theorem rowEval3375 (x : Key → ℝ) : Integer.Sparse.eval row3375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck3375, Integer.Sparse.eval_collectBalanced, rawRowCheck3375]

def rawRow3376 : Integer.Sparse Key := [(key2975, -2), (key2896, -2), (key2857, -2), (key2973, 1), (key2894, 1), (key2949, 1), (key2736, 1), (key2806, 1), (key2703, 1), (key2982, 2), (key2903, 2), (key2867, 2), (key2973, -1), (key2894, -1), (key2937, -1), (key2647, -1), (key2783, -1), (key2629, -1), (key2982, -1), (key2903, -1), (key2959, -1), (key2746, -1), (key2826, -1), (key2723, -1), (key2975, 1), (key2896, 1), (key2942, 1), (key2652, 1), (key2791, 1), (key2637, 1)]

theorem rawRowCheck3376 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form12 = rawRow3376 := by decide +kernel

def row3376 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck3376 : row3376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3376 := by decide +kernel

theorem rowEval3376 (x : Key → ℝ) : Integer.Sparse.eval row3376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3376, Integer.Sparse.eval_collectBalanced, rawRowCheck3376]

def rawRow3377 : Integer.Sparse Key := [(key2826, -2), (key2826, -2), (key2959, -2), (key2723, 1), (key2723, 1), (key2867, 1), (key2867, 1), (key2982, 1), (key2982, 1), (key2791, 2), (key2791, 2), (key2942, 2), (key2637, -1), (key2637, -1), (key2857, -1), (key2857, -1), (key2975, -1), (key2975, -1), (key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2937, -1), (key2937, -1), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2949, 1), (key2949, 1)]

theorem rawRowCheck3377 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form12 = rawRow3377 := by decide +kernel

def row3377 : Integer.Sparse Key := [(key2613, 2), (key2637, -2), (key2668, -2), (key2723, 2), (key2783, -2), (key2791, 4), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

theorem rowCheck3377 : row3377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3377 := by decide +kernel

theorem rowEval3377 (x : Key → ℝ) : Integer.Sparse.eval row3377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3377, Integer.Sparse.eval_collectBalanced, rawRowCheck3377]

def rawRow3378 : Integer.Sparse Key := [(key2826, -2), (key2959, -2), (key2826, -2), (key2867, 1), (key2982, 1), (key2723, 1), (key2982, 1), (key2723, 1), (key2867, 1), (key2791, 2), (key2942, 2), (key2791, 2), (key2857, -1), (key2975, -1), (key2637, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2783, -1), (key2937, -1), (key2668, -1), (key2937, -1), (key2668, -1), (key2783, -1), (key2806, 1), (key2949, 1), (key2613, 1), (key2949, 1), (key2613, 1), (key2806, 1)]

theorem rawRowCheck3378 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form12 = rawRow3378 := by decide +kernel

def row3378 : Integer.Sparse Key := [(key2613, 2), (key2637, -2), (key2668, -2), (key2723, 2), (key2783, -2), (key2791, 4), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

theorem rowCheck3378 : row3378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3378 := by decide +kernel

theorem rowEval3378 (x : Key → ℝ) : Integer.Sparse.eval row3378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3378, Integer.Sparse.eval_collectBalanced, rawRowCheck3378]

def rawRow3379 : Integer.Sparse Key := [(key2959, -2), (key2826, -2), (key2826, -2), (key2982, 1), (key2867, 1), (key2982, 1), (key2723, 1), (key2867, 1), (key2723, 1), (key2942, 2), (key2791, 2), (key2791, 2), (key2975, -1), (key2857, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2937, -1), (key2783, -1), (key2937, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2949, 1), (key2806, 1), (key2949, 1), (key2613, 1), (key2806, 1), (key2613, 1)]

theorem rawRowCheck3379 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form12 = rawRow3379 := by decide +kernel

def row3379 : Integer.Sparse Key := [(key2613, 2), (key2637, -2), (key2668, -2), (key2723, 2), (key2783, -2), (key2791, 4), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

theorem rowCheck3379 : row3379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3379 := by decide +kernel

theorem rowEval3379 (x : Key → ℝ) : Integer.Sparse.eval row3379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3379, Integer.Sparse.eval_collectBalanced, rawRowCheck3379]

def rawRow3380 : Integer.Sparse Key := [(key2867, -2), (key2903, -2), (key2982, -2), (key2723, 1), (key2746, 1), (key2826, 1), (key2903, 1), (key2959, 1), (key2982, 1), (key2857, 2), (key2896, 2), (key2975, 2), (key2637, -1), (key2652, -1), (key2791, -1), (key2896, -1), (key2942, -1), (key2975, -1), (key2703, -1), (key2736, -1), (key2806, -1), (key2894, -1), (key2949, -1), (key2973, -1), (key2629, 1), (key2647, 1), (key2783, 1), (key2894, 1), (key2937, 1), (key2973, 1)]

theorem rawRowCheck3380 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form12 = rawRow3380 := by decide +kernel

def row3380 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck3380 : row3380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3380 := by decide +kernel

theorem rowEval3380 (x : Key → ℝ) : Integer.Sparse.eval row3380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3380, Integer.Sparse.eval_collectBalanced, rawRowCheck3380]

def rawRow3381 : Integer.Sparse Key := [(key2903, -2), (key2867, -2), (key2982, -2), (key2746, 1), (key2723, 1), (key2903, 1), (key2826, 1), (key2982, 1), (key2959, 1), (key2896, 2), (key2857, 2), (key2975, 2), (key2652, -1), (key2637, -1), (key2896, -1), (key2791, -1), (key2975, -1), (key2942, -1), (key2736, -1), (key2703, -1), (key2894, -1), (key2806, -1), (key2973, -1), (key2949, -1), (key2647, 1), (key2629, 1), (key2894, 1), (key2783, 1), (key2973, 1), (key2937, 1)]

theorem rawRowCheck3381 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form12 = rawRow3381 := by decide +kernel

def row3381 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck3381 : row3381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3381 := by decide +kernel

theorem rowEval3381 (x : Key → ℝ) : Integer.Sparse.eval row3381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck3381, Integer.Sparse.eval_collectBalanced, rawRowCheck3381]

def rawRow3382 : Integer.Sparse Key := [(key2867, -2), (key2982, -2), (key2903, -2), (key2826, 1), (key2959, 1), (key2723, 1), (key2982, 1), (key2746, 1), (key2903, 1), (key2857, 2), (key2975, 2), (key2896, 2), (key2791, -1), (key2942, -1), (key2637, -1), (key2975, -1), (key2652, -1), (key2896, -1), (key2806, -1), (key2949, -1), (key2703, -1), (key2973, -1), (key2736, -1), (key2894, -1), (key2783, 1), (key2937, 1), (key2629, 1), (key2973, 1), (key2647, 1), (key2894, 1)]

theorem rawRowCheck3382 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form12 = rawRow3382 := by decide +kernel

def row3382 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck3382 : row3382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3382 := by decide +kernel

theorem rowEval3382 (x : Key → ℝ) : Integer.Sparse.eval row3382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3382, Integer.Sparse.eval_collectBalanced, rawRowCheck3382]

def rawRow3383 : Integer.Sparse Key := [(key2982, -2), (key2867, -2), (key2903, -2), (key2959, 1), (key2826, 1), (key2982, 1), (key2723, 1), (key2903, 1), (key2746, 1), (key2975, 2), (key2857, 2), (key2896, 2), (key2942, -1), (key2791, -1), (key2975, -1), (key2637, -1), (key2896, -1), (key2652, -1), (key2949, -1), (key2806, -1), (key2973, -1), (key2703, -1), (key2894, -1), (key2736, -1), (key2937, 1), (key2783, 1), (key2973, 1), (key2629, 1), (key2894, 1), (key2647, 1)]

theorem rawRowCheck3383 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form12 = rawRow3383 := by decide +kernel

def row3383 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck3383 : row3383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3383 := by decide +kernel

theorem rowEval3383 (x : Key → ℝ) : Integer.Sparse.eval row3383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3383, Integer.Sparse.eval_collectBalanced, rawRowCheck3383]

def rawRow3384 : Integer.Sparse Key := [(key2903, -2), (key2982, -2), (key2867, -2), (key2903, 1), (key2982, 1), (key2746, 1), (key2959, 1), (key2723, 1), (key2826, 1), (key2896, 2), (key2975, 2), (key2857, 2), (key2896, -1), (key2975, -1), (key2652, -1), (key2942, -1), (key2637, -1), (key2791, -1), (key2894, -1), (key2973, -1), (key2736, -1), (key2949, -1), (key2703, -1), (key2806, -1), (key2894, 1), (key2973, 1), (key2647, 1), (key2937, 1), (key2629, 1), (key2783, 1)]

theorem rawRowCheck3384 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form12 = rawRow3384 := by decide +kernel

def row3384 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck3384 : row3384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3384 := by decide +kernel

theorem rowEval3384 (x : Key → ℝ) : Integer.Sparse.eval row3384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck3384, Integer.Sparse.eval_collectBalanced, rawRowCheck3384]

def rawRow3385 : Integer.Sparse Key := [(key2982, -2), (key2903, -2), (key2867, -2), (key2982, 1), (key2903, 1), (key2959, 1), (key2746, 1), (key2826, 1), (key2723, 1), (key2975, 2), (key2896, 2), (key2857, 2), (key2975, -1), (key2896, -1), (key2942, -1), (key2652, -1), (key2791, -1), (key2637, -1), (key2973, -1), (key2894, -1), (key2949, -1), (key2736, -1), (key2806, -1), (key2703, -1), (key2973, 1), (key2894, 1), (key2937, 1), (key2647, 1), (key2783, 1), (key2629, 1)]

theorem rawRowCheck3385 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form12 = rawRow3385 := by decide +kernel

def row3385 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck3385 : row3385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3385 := by decide +kernel

theorem rowEval3385 (x : Key → ℝ) : Integer.Sparse.eval row3385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3385, Integer.Sparse.eval_collectBalanced, rawRowCheck3385]

def rawRow3386 : Integer.Sparse Key := [(key2174, -2), (key2176, -2), (key2187, -2), (key2176, 6), (key2274, 2), (key2276, 2), (key2287, 2), (key2079, -2), (key2276, -2), (key2341, -2), (key2279, -6), (key2085, 2), (key2279, 2), (key2343, 2)]

theorem rawRowCheck3386 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form13 = rawRow3386 := by decide +kernel

def row3386 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

theorem rowCheck3386 : row3386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3386 := by decide +kernel

theorem rowEval3386 (x : Key → ℝ) : Integer.Sparse.eval row3386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3386, Integer.Sparse.eval_collectBalanced, rawRowCheck3386]

def rawRow3387 : Integer.Sparse Key := [(key2176, -2), (key2174, -2), (key2187, -2), (key2176, 6), (key2276, 2), (key2274, 2), (key2287, 2), (key2079, -2), (key2341, -2), (key2276, -2), (key2279, -6), (key2085, 2), (key2343, 2), (key2279, 2)]

theorem rawRowCheck3387 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form13 = rawRow3387 := by decide +kernel

def row3387 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

theorem rowCheck3387 : row3387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3387 := by decide +kernel

theorem rowEval3387 (x : Key → ℝ) : Integer.Sparse.eval row3387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3387, Integer.Sparse.eval_collectBalanced, rawRowCheck3387]

def rawRow3388 : Integer.Sparse Key := [(key2174, -2), (key2187, -2), (key2176, -2), (key2176, 6), (key2274, 2), (key2287, 2), (key2276, 2), (key2276, -2), (key2079, -2), (key2341, -2), (key2279, -6), (key2279, 2), (key2085, 2), (key2343, 2)]

theorem rawRowCheck3388 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form13 = rawRow3388 := by decide +kernel

def row3388 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

theorem rowCheck3388 : row3388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3388 := by decide +kernel

theorem rowEval3388 (x : Key → ℝ) : Integer.Sparse.eval row3388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3388, Integer.Sparse.eval_collectBalanced, rawRowCheck3388]

def rawRow3389 : Integer.Sparse Key := [(key2187, -2), (key2174, -2), (key2176, -2), (key2176, 6), (key2287, 2), (key2274, 2), (key2276, 2), (key2276, -2), (key2341, -2), (key2079, -2), (key2279, -6), (key2279, 2), (key2343, 2), (key2085, 2)]

theorem rawRowCheck3389 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form13 = rawRow3389 := by decide +kernel

def row3389 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

theorem rowCheck3389 : row3389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3389 := by decide +kernel

theorem rowEval3389 (x : Key → ℝ) : Integer.Sparse.eval row3389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3389, Integer.Sparse.eval_collectBalanced, rawRowCheck3389]

def rawRow3390 : Integer.Sparse Key := [(key2176, -2), (key2187, -2), (key2174, -2), (key2176, 6), (key2276, 2), (key2287, 2), (key2274, 2), (key2341, -2), (key2079, -2), (key2276, -2), (key2279, -6), (key2343, 2), (key2085, 2), (key2279, 2)]

theorem rawRowCheck3390 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form13 = rawRow3390 := by decide +kernel

def row3390 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

theorem rowCheck3390 : row3390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3390 := by decide +kernel

theorem rowEval3390 (x : Key → ℝ) : Integer.Sparse.eval row3390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3390, Integer.Sparse.eval_collectBalanced, rawRowCheck3390]

def rawRow3391 : Integer.Sparse Key := [(key2187, -2), (key2176, -2), (key2174, -2), (key2176, 6), (key2287, 2), (key2276, 2), (key2274, 2), (key2341, -2), (key2276, -2), (key2079, -2), (key2279, -6), (key2343, 2), (key2279, 2), (key2085, 2)]

theorem rawRowCheck3391 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form13 = rawRow3391 := by decide +kernel

def row3391 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

theorem rowCheck3391 : row3391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3391 := by decide +kernel

theorem rowEval3391 (x : Key → ℝ) : Integer.Sparse.eval row3391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3391, Integer.Sparse.eval_collectBalanced, rawRowCheck3391]

def rawRow3392 : Integer.Sparse Key := [(key2176, -2), (key2176, -2), (key2187, -2), (key2174, 6), (key2341, 2), (key2341, 2), (key2347, 2), (key2077, -2), (key2274, -2), (key2274, -2), (key2343, -6), (key2085, 2), (key2279, 2), (key2279, 2)]

theorem rawRowCheck3392 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form13 = rawRow3392 := by decide +kernel

def row3392 : Integer.Sparse Key := [(key2077, -2), (key2085, 2), (key2174, 6), (key2176, -4), (key2187, -2), (key2274, -4), (key2279, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

theorem rowCheck3392 : row3392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3392 := by decide +kernel

theorem rowEval3392 (x : Key → ℝ) : Integer.Sparse.eval row3392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3392, Integer.Sparse.eval_collectBalanced, rawRowCheck3392]

def rawRow3393 : Integer.Sparse Key := [(key2176, -2), (key2187, -2), (key2176, -2), (key2174, 6), (key2341, 2), (key2347, 2), (key2341, 2), (key2274, -2), (key2077, -2), (key2274, -2), (key2343, -6), (key2279, 2), (key2085, 2), (key2279, 2)]

theorem rawRowCheck3393 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form13 = rawRow3393 := by decide +kernel

def row3393 : Integer.Sparse Key := [(key2077, -2), (key2085, 2), (key2174, 6), (key2176, -4), (key2187, -2), (key2274, -4), (key2279, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

theorem rowCheck3393 : row3393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3393 := by decide +kernel

theorem rowEval3393 (x : Key → ℝ) : Integer.Sparse.eval row3393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3393, Integer.Sparse.eval_collectBalanced, rawRowCheck3393]

def rawRow3394 : Integer.Sparse Key := [(key2187, -2), (key2176, -2), (key2176, -2), (key2174, 6), (key2347, 2), (key2341, 2), (key2341, 2), (key2274, -2), (key2274, -2), (key2077, -2), (key2343, -6), (key2279, 2), (key2279, 2), (key2085, 2)]

theorem rawRowCheck3394 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form13 = rawRow3394 := by decide +kernel

def row3394 : Integer.Sparse Key := [(key2077, -2), (key2085, 2), (key2174, 6), (key2176, -4), (key2187, -2), (key2274, -4), (key2279, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

theorem rowCheck3394 : row3394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3394 := by decide +kernel

theorem rowEval3394 (x : Key → ℝ) : Integer.Sparse.eval row3394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3394, Integer.Sparse.eval_collectBalanced, rawRowCheck3394]

def rawRow3395 : Integer.Sparse Key := [(key2274, -2), (key2276, -2), (key2287, -2), (key2279, 6), (key2174, 2), (key2176, 2), (key2187, 2), (key2085, -2), (key2279, -2), (key2343, -2), (key2176, -6), (key2079, 2), (key2276, 2), (key2341, 2)]

theorem rawRowCheck3395 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form13 = rawRow3395 := by decide +kernel

def row3395 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

theorem rowCheck3395 : row3395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3395 := by decide +kernel

theorem rowEval3395 (x : Key → ℝ) : Integer.Sparse.eval row3395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3395, Integer.Sparse.eval_collectBalanced, rawRowCheck3395]

def rawRow3396 : Integer.Sparse Key := [(key2276, -2), (key2274, -2), (key2287, -2), (key2279, 6), (key2176, 2), (key2174, 2), (key2187, 2), (key2085, -2), (key2343, -2), (key2279, -2), (key2176, -6), (key2079, 2), (key2341, 2), (key2276, 2)]

theorem rawRowCheck3396 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form13 = rawRow3396 := by decide +kernel

def row3396 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

theorem rowCheck3396 : row3396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3396 := by decide +kernel

theorem rowEval3396 (x : Key → ℝ) : Integer.Sparse.eval row3396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3396, Integer.Sparse.eval_collectBalanced, rawRowCheck3396]

def rawRow3397 : Integer.Sparse Key := [(key2274, -2), (key2287, -2), (key2276, -2), (key2279, 6), (key2174, 2), (key2187, 2), (key2176, 2), (key2279, -2), (key2085, -2), (key2343, -2), (key2176, -6), (key2276, 2), (key2079, 2), (key2341, 2)]

theorem rawRowCheck3397 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form13 = rawRow3397 := by decide +kernel

def row3397 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

theorem rowCheck3397 : row3397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3397 := by decide +kernel

theorem rowEval3397 (x : Key → ℝ) : Integer.Sparse.eval row3397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3397, Integer.Sparse.eval_collectBalanced, rawRowCheck3397]

def rawRow3398 : Integer.Sparse Key := [(key2287, -2), (key2274, -2), (key2276, -2), (key2279, 6), (key2187, 2), (key2174, 2), (key2176, 2), (key2279, -2), (key2343, -2), (key2085, -2), (key2176, -6), (key2276, 2), (key2341, 2), (key2079, 2)]

theorem rawRowCheck3398 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form13 = rawRow3398 := by decide +kernel

def row3398 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

theorem rowCheck3398 : row3398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3398 := by decide +kernel

theorem rowEval3398 (x : Key → ℝ) : Integer.Sparse.eval row3398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3398, Integer.Sparse.eval_collectBalanced, rawRowCheck3398]

def rawRow3399 : Integer.Sparse Key := [(key2276, -2), (key2287, -2), (key2274, -2), (key2279, 6), (key2176, 2), (key2187, 2), (key2174, 2), (key2343, -2), (key2085, -2), (key2279, -2), (key2176, -6), (key2341, 2), (key2079, 2), (key2276, 2)]

theorem rawRowCheck3399 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form13 = rawRow3399 := by decide +kernel

def row3399 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

theorem rowCheck3399 : row3399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3399 := by decide +kernel

theorem rowEval3399 (x : Key → ℝ) : Integer.Sparse.eval row3399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3399, Integer.Sparse.eval_collectBalanced, rawRowCheck3399]

def rawRow3400 : Integer.Sparse Key := [(key2287, -2), (key2276, -2), (key2274, -2), (key2279, 6), (key2187, 2), (key2176, 2), (key2174, 2), (key2343, -2), (key2279, -2), (key2085, -2), (key2176, -6), (key2341, 2), (key2276, 2), (key2079, 2)]

theorem rawRowCheck3400 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form13 = rawRow3400 := by decide +kernel

def row3400 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

theorem rowCheck3400 : row3400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3400 := by decide +kernel

theorem rowEval3400 (x : Key → ℝ) : Integer.Sparse.eval row3400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3400, Integer.Sparse.eval_collectBalanced, rawRowCheck3400]

def rawRow3401 : Integer.Sparse Key := [(key2276, -2), (key2279, -2), (key2287, -2), (key2274, 6), (key2341, 2), (key2343, 2), (key2347, 2), (key2077, -2), (key2174, -2), (key2274, -2), (key2341, -6), (key2079, 2), (key2176, 2), (key2276, 2)]

theorem rawRowCheck3401 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form13 = rawRow3401 := by decide +kernel

def row3401 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

theorem rowCheck3401 : row3401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3401 := by decide +kernel

theorem rowEval3401 (x : Key → ℝ) : Integer.Sparse.eval row3401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3401, Integer.Sparse.eval_collectBalanced, rawRowCheck3401]

def rawRow3402 : Integer.Sparse Key := [(key2279, -2), (key2276, -2), (key2287, -2), (key2274, 6), (key2343, 2), (key2341, 2), (key2347, 2), (key2077, -2), (key2274, -2), (key2174, -2), (key2341, -6), (key2079, 2), (key2276, 2), (key2176, 2)]

theorem rawRowCheck3402 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form13 = rawRow3402 := by decide +kernel

def row3402 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

theorem rowCheck3402 : row3402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3402 := by decide +kernel

theorem rowEval3402 (x : Key → ℝ) : Integer.Sparse.eval row3402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3402, Integer.Sparse.eval_collectBalanced, rawRowCheck3402]

def rawRow3403 : Integer.Sparse Key := [(key2276, -2), (key2287, -2), (key2279, -2), (key2274, 6), (key2341, 2), (key2347, 2), (key2343, 2), (key2174, -2), (key2077, -2), (key2274, -2), (key2341, -6), (key2176, 2), (key2079, 2), (key2276, 2)]

theorem rawRowCheck3403 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form13 = rawRow3403 := by decide +kernel

def row3403 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

theorem rowCheck3403 : row3403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3403 := by decide +kernel

theorem rowEval3403 (x : Key → ℝ) : Integer.Sparse.eval row3403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3403, Integer.Sparse.eval_collectBalanced, rawRowCheck3403]

def rawRow3404 : Integer.Sparse Key := [(key2287, -2), (key2276, -2), (key2279, -2), (key2274, 6), (key2347, 2), (key2341, 2), (key2343, 2), (key2174, -2), (key2274, -2), (key2077, -2), (key2341, -6), (key2176, 2), (key2276, 2), (key2079, 2)]

theorem rawRowCheck3404 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form13 = rawRow3404 := by decide +kernel

def row3404 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

theorem rowCheck3404 : row3404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3404 := by decide +kernel

theorem rowEval3404 (x : Key → ℝ) : Integer.Sparse.eval row3404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3404, Integer.Sparse.eval_collectBalanced, rawRowCheck3404]

def rawRow3405 : Integer.Sparse Key := [(key2279, -2), (key2287, -2), (key2276, -2), (key2274, 6), (key2343, 2), (key2347, 2), (key2341, 2), (key2274, -2), (key2077, -2), (key2174, -2), (key2341, -6), (key2276, 2), (key2079, 2), (key2176, 2)]

theorem rawRowCheck3405 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form13 = rawRow3405 := by decide +kernel

def row3405 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

theorem rowCheck3405 : row3405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3405 := by decide +kernel

theorem rowEval3405 (x : Key → ℝ) : Integer.Sparse.eval row3405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3405, Integer.Sparse.eval_collectBalanced, rawRowCheck3405]

def rawRow3406 : Integer.Sparse Key := [(key2287, -2), (key2279, -2), (key2276, -2), (key2274, 6), (key2347, 2), (key2343, 2), (key2341, 2), (key2274, -2), (key2174, -2), (key2077, -2), (key2341, -6), (key2276, 2), (key2176, 2), (key2079, 2)]

theorem rawRowCheck3406 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form13 = rawRow3406 := by decide +kernel

def row3406 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

theorem rowCheck3406 : row3406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3406 := by decide +kernel

theorem rowEval3406 (x : Key → ℝ) : Integer.Sparse.eval row3406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3406, Integer.Sparse.eval_collectBalanced, rawRowCheck3406]

def rawRow3407 : Integer.Sparse Key := [(key2341, -2), (key2341, -2), (key2347, -2), (key2343, 6), (key2176, 2), (key2176, 2), (key2187, 2), (key2085, -2), (key2279, -2), (key2279, -2), (key2174, -6), (key2077, 2), (key2274, 2), (key2274, 2)]

theorem rawRowCheck3407 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form13 = rawRow3407 := by decide +kernel

def row3407 : Integer.Sparse Key := [(key2077, 2), (key2085, -2), (key2174, -6), (key2176, 4), (key2187, 2), (key2274, 4), (key2279, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

theorem rowCheck3407 : row3407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3407 := by decide +kernel

theorem rowEval3407 (x : Key → ℝ) : Integer.Sparse.eval row3407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3407, Integer.Sparse.eval_collectBalanced, rawRowCheck3407]

def rawRow3408 : Integer.Sparse Key := [(key2341, -2), (key2347, -2), (key2341, -2), (key2343, 6), (key2176, 2), (key2187, 2), (key2176, 2), (key2279, -2), (key2085, -2), (key2279, -2), (key2174, -6), (key2274, 2), (key2077, 2), (key2274, 2)]

theorem rawRowCheck3408 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form13 = rawRow3408 := by decide +kernel

def row3408 : Integer.Sparse Key := [(key2077, 2), (key2085, -2), (key2174, -6), (key2176, 4), (key2187, 2), (key2274, 4), (key2279, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

theorem rowCheck3408 : row3408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3408 := by decide +kernel

theorem rowEval3408 (x : Key → ℝ) : Integer.Sparse.eval row3408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3408, Integer.Sparse.eval_collectBalanced, rawRowCheck3408]

def rawRow3409 : Integer.Sparse Key := [(key2347, -2), (key2341, -2), (key2341, -2), (key2343, 6), (key2187, 2), (key2176, 2), (key2176, 2), (key2279, -2), (key2279, -2), (key2085, -2), (key2174, -6), (key2274, 2), (key2274, 2), (key2077, 2)]

theorem rawRowCheck3409 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form13 = rawRow3409 := by decide +kernel

def row3409 : Integer.Sparse Key := [(key2077, 2), (key2085, -2), (key2174, -6), (key2176, 4), (key2187, 2), (key2274, 4), (key2279, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

theorem rowCheck3409 : row3409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3409 := by decide +kernel

theorem rowEval3409 (x : Key → ℝ) : Integer.Sparse.eval row3409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3409, Integer.Sparse.eval_collectBalanced, rawRowCheck3409]

def rawRow3410 : Integer.Sparse Key := [(key2341, -2), (key2343, -2), (key2347, -2), (key2341, 6), (key2276, 2), (key2279, 2), (key2287, 2), (key2079, -2), (key2176, -2), (key2276, -2), (key2274, -6), (key2077, 2), (key2174, 2), (key2274, 2)]

theorem rawRowCheck3410 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form13 = rawRow3410 := by decide +kernel

def row3410 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

theorem rowCheck3410 : row3410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3410 := by decide +kernel

theorem rowEval3410 (x : Key → ℝ) : Integer.Sparse.eval row3410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3410, Integer.Sparse.eval_collectBalanced, rawRowCheck3410]

def rawRow3411 : Integer.Sparse Key := [(key2343, -2), (key2341, -2), (key2347, -2), (key2341, 6), (key2279, 2), (key2276, 2), (key2287, 2), (key2079, -2), (key2276, -2), (key2176, -2), (key2274, -6), (key2077, 2), (key2274, 2), (key2174, 2)]

theorem rawRowCheck3411 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form13 = rawRow3411 := by decide +kernel

def row3411 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

theorem rowCheck3411 : row3411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3411 := by decide +kernel

theorem rowEval3411 (x : Key → ℝ) : Integer.Sparse.eval row3411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3411, Integer.Sparse.eval_collectBalanced, rawRowCheck3411]

def rawRow3412 : Integer.Sparse Key := [(key2341, -2), (key2347, -2), (key2343, -2), (key2341, 6), (key2276, 2), (key2287, 2), (key2279, 2), (key2176, -2), (key2079, -2), (key2276, -2), (key2274, -6), (key2174, 2), (key2077, 2), (key2274, 2)]

theorem rawRowCheck3412 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form13 = rawRow3412 := by decide +kernel

def row3412 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

theorem rowCheck3412 : row3412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3412 := by decide +kernel

theorem rowEval3412 (x : Key → ℝ) : Integer.Sparse.eval row3412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3412, Integer.Sparse.eval_collectBalanced, rawRowCheck3412]

def rawRow3413 : Integer.Sparse Key := [(key2347, -2), (key2341, -2), (key2343, -2), (key2341, 6), (key2287, 2), (key2276, 2), (key2279, 2), (key2176, -2), (key2276, -2), (key2079, -2), (key2274, -6), (key2174, 2), (key2274, 2), (key2077, 2)]

theorem rawRowCheck3413 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form13 = rawRow3413 := by decide +kernel

def row3413 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

theorem rowCheck3413 : row3413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3413 := by decide +kernel

theorem rowEval3413 (x : Key → ℝ) : Integer.Sparse.eval row3413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3413, Integer.Sparse.eval_collectBalanced, rawRowCheck3413]

def rawRow3414 : Integer.Sparse Key := [(key2343, -2), (key2347, -2), (key2341, -2), (key2341, 6), (key2279, 2), (key2287, 2), (key2276, 2), (key2276, -2), (key2079, -2), (key2176, -2), (key2274, -6), (key2274, 2), (key2077, 2), (key2174, 2)]

theorem rawRowCheck3414 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form13 = rawRow3414 := by decide +kernel

def row3414 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

theorem rowCheck3414 : row3414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3414 := by decide +kernel

theorem rowEval3414 (x : Key → ℝ) : Integer.Sparse.eval row3414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3414, Integer.Sparse.eval_collectBalanced, rawRowCheck3414]

def rawRow3415 : Integer.Sparse Key := [(key2347, -2), (key2343, -2), (key2341, -2), (key2341, 6), (key2287, 2), (key2279, 2), (key2276, 2), (key2276, -2), (key2176, -2), (key2079, -2), (key2274, -6), (key2274, 2), (key2174, 2), (key2077, 2)]

theorem rawRowCheck3415 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form13 = rawRow3415 := by decide +kernel

def row3415 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

theorem rowCheck3415 : row3415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3415 := by decide +kernel

theorem rowEval3415 (x : Key → ℝ) : Integer.Sparse.eval row3415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3415, Integer.Sparse.eval_collectBalanced, rawRowCheck3415]

def rawRow3416 : Integer.Sparse Key := [(key2406, -2), (key2437, -2), (key2443, -2), (key2406, 2), (key2411, 2), (key2443, 2), (key2843, 2), (key2966, 2), (key2968, 2), (key2587, -1), (key2593, -1), (key2843, -1), (key2880, -1), (key2968, -1), (key2989, -1), (key2887, -2), (key2889, -2), (key2995, -2), (key2598, 1), (key2600, 1), (key2887, 1), (key2910, 1), (key2995, 1), (key3002, 1)]

theorem rawRowCheck3416 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form14 = rawRow3416 := by decide +kernel

def row3416 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

theorem rowCheck3416 : row3416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3416 := by decide +kernel

theorem rowEval3416 (x : Key → ℝ) : Integer.Sparse.eval row3416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3416, Integer.Sparse.eval_collectBalanced, rawRowCheck3416]

def rawRow3417 : Integer.Sparse Key := [(key2406, -2), (key2443, -2), (key2437, -2), (key2411, 2), (key2406, 2), (key2443, 2), (key2843, 2), (key2968, 2), (key2966, 2), (key2593, -1), (key2587, -1), (key2880, -1), (key2843, -1), (key2989, -1), (key2968, -1), (key2889, -2), (key2887, -2), (key2995, -2), (key2600, 1), (key2598, 1), (key2910, 1), (key2887, 1), (key3002, 1), (key2995, 1)]

theorem rawRowCheck3417 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form14 = rawRow3417 := by decide +kernel

def row3417 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

theorem rowCheck3417 : row3417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3417 := by decide +kernel

theorem rowEval3417 (x : Key → ℝ) : Integer.Sparse.eval row3417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3417, Integer.Sparse.eval_collectBalanced, rawRowCheck3417]

def rawRow3418 : Integer.Sparse Key := [(key2437, -2), (key2406, -2), (key2443, -2), (key2406, 2), (key2443, 2), (key2411, 2), (key2966, 2), (key2843, 2), (key2968, 2), (key2843, -1), (key2968, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2887, -2), (key2995, -2), (key2889, -2), (key2887, 1), (key2995, 1), (key2598, 1), (key3002, 1), (key2600, 1), (key2910, 1)]

theorem rawRowCheck3418 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form14 = rawRow3418 := by decide +kernel

def row3418 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

theorem rowCheck3418 : row3418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3418 := by decide +kernel

theorem rowEval3418 (x : Key → ℝ) : Integer.Sparse.eval row3418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3418, Integer.Sparse.eval_collectBalanced, rawRowCheck3418]

def rawRow3419 : Integer.Sparse Key := [(key2437, -2), (key2443, -2), (key2406, -2), (key2443, 2), (key2406, 2), (key2411, 2), (key2966, 2), (key2968, 2), (key2843, 2), (key2968, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2880, -1), (key2593, -1), (key2995, -2), (key2887, -2), (key2889, -2), (key2995, 1), (key2887, 1), (key3002, 1), (key2598, 1), (key2910, 1), (key2600, 1)]

theorem rawRowCheck3419 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form14 = rawRow3419 := by decide +kernel

def row3419 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

theorem rowCheck3419 : row3419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3419 := by decide +kernel

theorem rowEval3419 (x : Key → ℝ) : Integer.Sparse.eval row3419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3419, Integer.Sparse.eval_collectBalanced, rawRowCheck3419]

def rawRow3420 : Integer.Sparse Key := [(key2443, -2), (key2406, -2), (key2437, -2), (key2411, 2), (key2443, 2), (key2406, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2880, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2587, -1), (key2843, -1), (key2889, -2), (key2995, -2), (key2887, -2), (key2910, 1), (key3002, 1), (key2600, 1), (key2995, 1), (key2598, 1), (key2887, 1)]

theorem rawRowCheck3420 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form14 = rawRow3420 := by decide +kernel

def row3420 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

theorem rowCheck3420 : row3420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3420 := by decide +kernel

theorem rowEval3420 (x : Key → ℝ) : Integer.Sparse.eval row3420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3420, Integer.Sparse.eval_collectBalanced, rawRowCheck3420]

def rawRow3421 : Integer.Sparse Key := [(key2443, -2), (key2437, -2), (key2406, -2), (key2443, 2), (key2411, 2), (key2406, 2), (key2968, 2), (key2966, 2), (key2843, 2), (key2989, -1), (key2880, -1), (key2968, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key2995, -2), (key2889, -2), (key2887, -2), (key3002, 1), (key2910, 1), (key2995, 1), (key2600, 1), (key2887, 1), (key2598, 1)]

theorem rawRowCheck3421 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form14 = rawRow3421 := by decide +kernel

def row3421 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

theorem rowCheck3421 : row3421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3421 := by decide +kernel

theorem rowEval3421 (x : Key → ℝ) : Integer.Sparse.eval row3421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3421, Integer.Sparse.eval_collectBalanced, rawRowCheck3421]

def rawRow3422 : Integer.Sparse Key := [(key2411, -2), (key2443, -2), (key2443, -2), (key2406, 2), (key2406, 2), (key2437, 2), (key2880, 2), (key2989, 2), (key2989, 2), (key2587, -1), (key2587, -1), (key2843, -1), (key2843, -1), (key2966, -1), (key2966, -1), (key2910, -2), (key2910, -2), (key3002, -2), (key2600, 1), (key2600, 1), (key2889, 1), (key2889, 1), (key2995, 1), (key2995, 1)]

theorem rawRowCheck3422 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form14 = rawRow3422 := by decide +kernel

def row3422 : Integer.Sparse Key := [(key2406, 4), (key2411, -2), (key2437, 2), (key2443, -4), (key2587, -2), (key2600, 2), (key2843, -2), (key2880, 2), (key2889, 2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, 2), (key3002, -2)]

theorem rowCheck3422 : row3422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3422 := by decide +kernel

theorem rowEval3422 (x : Key → ℝ) : Integer.Sparse.eval row3422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3422, Integer.Sparse.eval_collectBalanced, rawRowCheck3422]

def rawRow3423 : Integer.Sparse Key := [(key2443, -2), (key2411, -2), (key2443, -2), (key2406, 2), (key2437, 2), (key2406, 2), (key2989, 2), (key2880, 2), (key2989, 2), (key2843, -1), (key2966, -1), (key2587, -1), (key2966, -1), (key2587, -1), (key2843, -1), (key2910, -2), (key3002, -2), (key2910, -2), (key2889, 1), (key2995, 1), (key2600, 1), (key2995, 1), (key2600, 1), (key2889, 1)]

theorem rawRowCheck3423 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form14 = rawRow3423 := by decide +kernel

def row3423 : Integer.Sparse Key := [(key2406, 4), (key2411, -2), (key2437, 2), (key2443, -4), (key2587, -2), (key2600, 2), (key2843, -2), (key2880, 2), (key2889, 2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, 2), (key3002, -2)]

theorem rowCheck3423 : row3423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3423 := by decide +kernel

theorem rowEval3423 (x : Key → ℝ) : Integer.Sparse.eval row3423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3423, Integer.Sparse.eval_collectBalanced, rawRowCheck3423]

def rawRow3424 : Integer.Sparse Key := [(key2443, -2), (key2443, -2), (key2411, -2), (key2437, 2), (key2406, 2), (key2406, 2), (key2989, 2), (key2989, 2), (key2880, 2), (key2966, -1), (key2843, -1), (key2966, -1), (key2587, -1), (key2843, -1), (key2587, -1), (key3002, -2), (key2910, -2), (key2910, -2), (key2995, 1), (key2889, 1), (key2995, 1), (key2600, 1), (key2889, 1), (key2600, 1)]

theorem rawRowCheck3424 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form14 = rawRow3424 := by decide +kernel

def row3424 : Integer.Sparse Key := [(key2406, 4), (key2411, -2), (key2437, 2), (key2443, -4), (key2587, -2), (key2600, 2), (key2843, -2), (key2880, 2), (key2889, 2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, 2), (key3002, -2)]

theorem rowCheck3424 : row3424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3424 := by decide +kernel

theorem rowEval3424 (x : Key → ℝ) : Integer.Sparse.eval row3424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3424, Integer.Sparse.eval_collectBalanced, rawRowCheck3424]

def rawRow3425 : Integer.Sparse Key := [(key2472, -2), (key2503, -2), (key2509, -2), (key2480, 2), (key2484, 2), (key2524, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2598, -1), (key2600, -1), (key2887, -1), (key2910, -1), (key2995, -1), (key3002, -1), (key2766, -2), (key2772, -2), (key2931, -2), (key2587, 1), (key2593, 1), (key2843, 1), (key2880, 1), (key2968, 1), (key2989, 1)]

theorem rawRowCheck3425 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form14 = rawRow3425 := by decide +kernel

def row3425 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck3425 : row3425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3425 := by decide +kernel

theorem rowEval3425 (x : Key → ℝ) : Integer.Sparse.eval row3425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3425, Integer.Sparse.eval_collectBalanced, rawRowCheck3425]

def rawRow3426 : Integer.Sparse Key := [(key2472, -2), (key2509, -2), (key2503, -2), (key2484, 2), (key2480, 2), (key2524, 2), (key2406, 2), (key2443, 2), (key2437, 2), (key2600, -1), (key2598, -1), (key2910, -1), (key2887, -1), (key3002, -1), (key2995, -1), (key2772, -2), (key2766, -2), (key2931, -2), (key2593, 1), (key2587, 1), (key2880, 1), (key2843, 1), (key2989, 1), (key2968, 1)]

theorem rawRowCheck3426 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form14 = rawRow3426 := by decide +kernel

def row3426 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck3426 : row3426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3426 := by decide +kernel

theorem rowEval3426 (x : Key → ℝ) : Integer.Sparse.eval row3426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3426, Integer.Sparse.eval_collectBalanced, rawRowCheck3426]

def rawRow3427 : Integer.Sparse Key := [(key2503, -2), (key2472, -2), (key2509, -2), (key2480, 2), (key2524, 2), (key2484, 2), (key2437, 2), (key2406, 2), (key2443, 2), (key2887, -1), (key2995, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2766, -2), (key2931, -2), (key2772, -2), (key2843, 1), (key2968, 1), (key2587, 1), (key2989, 1), (key2593, 1), (key2880, 1)]

theorem rawRowCheck3427 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form14 = rawRow3427 := by decide +kernel

def row3427 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck3427 : row3427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3427 := by decide +kernel

theorem rowEval3427 (x : Key → ℝ) : Integer.Sparse.eval row3427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3427, Integer.Sparse.eval_collectBalanced, rawRowCheck3427]

def rawRow3428 : Integer.Sparse Key := [(key2503, -2), (key2509, -2), (key2472, -2), (key2524, 2), (key2480, 2), (key2484, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2995, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2910, -1), (key2600, -1), (key2931, -2), (key2766, -2), (key2772, -2), (key2968, 1), (key2843, 1), (key2989, 1), (key2587, 1), (key2880, 1), (key2593, 1)]

theorem rawRowCheck3428 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form14 = rawRow3428 := by decide +kernel

def row3428 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck3428 : row3428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3428 := by decide +kernel

theorem rowEval3428 (x : Key → ℝ) : Integer.Sparse.eval row3428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3428, Integer.Sparse.eval_collectBalanced, rawRowCheck3428]

def rawRow3429 : Integer.Sparse Key := [(key2509, -2), (key2472, -2), (key2503, -2), (key2484, 2), (key2524, 2), (key2480, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2910, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2598, -1), (key2887, -1), (key2772, -2), (key2931, -2), (key2766, -2), (key2880, 1), (key2989, 1), (key2593, 1), (key2968, 1), (key2587, 1), (key2843, 1)]

theorem rawRowCheck3429 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form14 = rawRow3429 := by decide +kernel

def row3429 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck3429 : row3429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3429 := by decide +kernel

theorem rowEval3429 (x : Key → ℝ) : Integer.Sparse.eval row3429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3429, Integer.Sparse.eval_collectBalanced, rawRowCheck3429]

def rawRow3430 : Integer.Sparse Key := [(key2509, -2), (key2503, -2), (key2472, -2), (key2524, 2), (key2484, 2), (key2480, 2), (key2443, 2), (key2437, 2), (key2406, 2), (key3002, -1), (key2910, -1), (key2995, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2931, -2), (key2772, -2), (key2766, -2), (key2989, 1), (key2880, 1), (key2968, 1), (key2593, 1), (key2843, 1), (key2587, 1)]

theorem rawRowCheck3430 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form14 = rawRow3430 := by decide +kernel

def row3430 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck3430 : row3430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3430 := by decide +kernel

theorem rowEval3430 (x : Key → ℝ) : Integer.Sparse.eval row3430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3430, Integer.Sparse.eval_collectBalanced, rawRowCheck3430]

def rawRow3431 : Integer.Sparse Key := [(key2484, -2), (key2509, -2), (key2524, -2), (key2472, 2), (key2480, 2), (key2503, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2480, -1), (key2437, -1), (key2503, -1), (key2880, -2), (key2910, -2), (key2989, -2), (key2593, 1), (key2600, 1), (key2772, 1), (key2889, 1), (key2931, 1), (key2968, 1)]

theorem rawRowCheck3431 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form14 = rawRow3431 := by decide +kernel

def row3431 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

theorem rowCheck3431 : row3431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3431 := by decide +kernel

theorem rowEval3431 (x : Key → ℝ) : Integer.Sparse.eval row3431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3431, Integer.Sparse.eval_collectBalanced, rawRowCheck3431]

def rawRow3432 : Integer.Sparse Key := [(key2484, -2), (key2524, -2), (key2509, -2), (key2480, 2), (key2472, 2), (key2503, 2), (key2571, 2), (key2580, 2), (key2576, 2), (key2390, -1), (key2378, -1), (key2480, -1), (key2406, -1), (key2503, -1), (key2437, -1), (key2910, -2), (key2880, -2), (key2989, -2), (key2600, 1), (key2593, 1), (key2889, 1), (key2772, 1), (key2968, 1), (key2931, 1)]

theorem rawRowCheck3432 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form14 = rawRow3432 := by decide +kernel

def row3432 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

theorem rowCheck3432 : row3432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3432 := by decide +kernel

theorem rowEval3432 (x : Key → ℝ) : Integer.Sparse.eval row3432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3432, Integer.Sparse.eval_collectBalanced, rawRowCheck3432]

def rawRow3433 : Integer.Sparse Key := [(key2509, -2), (key2484, -2), (key2524, -2), (key2472, 2), (key2503, 2), (key2480, 2), (key2576, 2), (key2571, 2), (key2580, 2), (key2406, -1), (key2437, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2880, -2), (key2989, -2), (key2910, -2), (key2772, 1), (key2931, 1), (key2593, 1), (key2968, 1), (key2600, 1), (key2889, 1)]

theorem rawRowCheck3433 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form14 = rawRow3433 := by decide +kernel

def row3433 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

theorem rowCheck3433 : row3433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3433 := by decide +kernel

theorem rowEval3433 (x : Key → ℝ) : Integer.Sparse.eval row3433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3433, Integer.Sparse.eval_collectBalanced, rawRowCheck3433]

def rawRow3434 : Integer.Sparse Key := [(key2509, -2), (key2524, -2), (key2484, -2), (key2503, 2), (key2472, 2), (key2480, 2), (key2576, 2), (key2580, 2), (key2571, 2), (key2437, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2480, -1), (key2390, -1), (key2989, -2), (key2880, -2), (key2910, -2), (key2931, 1), (key2772, 1), (key2968, 1), (key2593, 1), (key2889, 1), (key2600, 1)]

theorem rawRowCheck3434 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form14 = rawRow3434 := by decide +kernel

def row3434 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

theorem rowCheck3434 : row3434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3434 := by decide +kernel

theorem rowEval3434 (x : Key → ℝ) : Integer.Sparse.eval row3434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3434, Integer.Sparse.eval_collectBalanced, rawRowCheck3434]

def rawRow3435 : Integer.Sparse Key := [(key2524, -2), (key2484, -2), (key2509, -2), (key2480, 2), (key2503, 2), (key2472, 2), (key2580, 2), (key2571, 2), (key2576, 2), (key2480, -1), (key2503, -1), (key2390, -1), (key2437, -1), (key2378, -1), (key2406, -1), (key2910, -2), (key2989, -2), (key2880, -2), (key2889, 1), (key2968, 1), (key2600, 1), (key2931, 1), (key2593, 1), (key2772, 1)]

theorem rawRowCheck3435 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form14 = rawRow3435 := by decide +kernel

def row3435 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

theorem rowCheck3435 : row3435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3435 := by decide +kernel

theorem rowEval3435 (x : Key → ℝ) : Integer.Sparse.eval row3435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3435, Integer.Sparse.eval_collectBalanced, rawRowCheck3435]

def rawRow3436 : Integer.Sparse Key := [(key2524, -2), (key2509, -2), (key2484, -2), (key2503, 2), (key2480, 2), (key2472, 2), (key2580, 2), (key2576, 2), (key2571, 2), (key2503, -1), (key2480, -1), (key2437, -1), (key2390, -1), (key2406, -1), (key2378, -1), (key2989, -2), (key2910, -2), (key2880, -2), (key2968, 1), (key2889, 1), (key2931, 1), (key2600, 1), (key2772, 1), (key2593, 1)]

theorem rawRowCheck3436 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form14 = rawRow3436 := by decide +kernel

def row3436 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

theorem rowCheck3436 : row3436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3436 := by decide +kernel

theorem rowEval3436 (x : Key → ℝ) : Integer.Sparse.eval row3436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3436, Integer.Sparse.eval_collectBalanced, rawRowCheck3436]

def rawRow3437 : Integer.Sparse Key := [(key2569, -2), (key2576, -2), (key2576, -2), (key2571, 2), (key2571, 2), (key2580, 2), (key2411, 2), (key2443, 2), (key2443, 2), (key2394, -1), (key2394, -1), (key2484, -1), (key2484, -1), (key2524, -1), (key2524, -1), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, 1), (key2378, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1)]

theorem rawRowCheck3437 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form14 = rawRow3437 := by decide +kernel

def row3437 : Integer.Sparse Key := [(key2378, 2), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, 2), (key2484, -2), (key2503, 2), (key2524, -2), (key2569, -2), (key2571, 4), (key2576, -4), (key2580, 2)]

theorem rowCheck3437 : row3437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3437 := by decide +kernel

theorem rowEval3437 (x : Key → ℝ) : Integer.Sparse.eval row3437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3437, Integer.Sparse.eval_collectBalanced, rawRowCheck3437]

def rawRow3438 : Integer.Sparse Key := [(key2576, -2), (key2569, -2), (key2576, -2), (key2571, 2), (key2580, 2), (key2571, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2484, -1), (key2524, -1), (key2394, -1), (key2524, -1), (key2394, -1), (key2484, -1), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, 1), (key2503, 1), (key2378, 1), (key2503, 1), (key2378, 1), (key2472, 1)]

theorem rawRowCheck3438 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form14 = rawRow3438 := by decide +kernel

def row3438 : Integer.Sparse Key := [(key2378, 2), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, 2), (key2484, -2), (key2503, 2), (key2524, -2), (key2569, -2), (key2571, 4), (key2576, -4), (key2580, 2)]

theorem rowCheck3438 : row3438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3438 := by decide +kernel

theorem rowEval3438 (x : Key → ℝ) : Integer.Sparse.eval row3438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3438, Integer.Sparse.eval_collectBalanced, rawRowCheck3438]

def rawRow3439 : Integer.Sparse Key := [(key2576, -2), (key2576, -2), (key2569, -2), (key2580, 2), (key2571, 2), (key2571, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2524, -1), (key2484, -1), (key2524, -1), (key2394, -1), (key2484, -1), (key2394, -1), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, 1), (key2472, 1), (key2503, 1), (key2378, 1), (key2472, 1), (key2378, 1)]

theorem rawRowCheck3439 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form14 = rawRow3439 := by decide +kernel

def row3439 : Integer.Sparse Key := [(key2378, 2), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, 2), (key2484, -2), (key2503, 2), (key2524, -2), (key2569, -2), (key2571, 4), (key2576, -4), (key2580, 2)]

theorem rowCheck3439 : row3439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3439 := by decide +kernel

theorem rowEval3439 (x : Key → ℝ) : Integer.Sparse.eval row3439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3439, Integer.Sparse.eval_collectBalanced, rawRowCheck3439]

def rawRow3440 : Integer.Sparse Key := [(key2571, -2), (key2576, -2), (key2580, -2), (key2569, 2), (key2571, 2), (key2576, 2), (key2484, 2), (key2509, 2), (key2524, 2), (key2383, -1), (key2394, -1), (key2411, -1), (key2484, -1), (key2443, -1), (key2509, -1), (key2472, -2), (key2480, -2), (key2503, -2), (key2378, 1), (key2390, 1), (key2406, 1), (key2480, 1), (key2437, 1), (key2503, 1)]

theorem rawRowCheck3440 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form14 = rawRow3440 := by decide +kernel

def row3440 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

theorem rowCheck3440 : row3440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3440 := by decide +kernel

theorem rowEval3440 (x : Key → ℝ) : Integer.Sparse.eval row3440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3440, Integer.Sparse.eval_collectBalanced, rawRowCheck3440]

def rawRow3441 : Integer.Sparse Key := [(key2571, -2), (key2580, -2), (key2576, -2), (key2571, 2), (key2569, 2), (key2576, 2), (key2484, 2), (key2524, 2), (key2509, 2), (key2394, -1), (key2383, -1), (key2484, -1), (key2411, -1), (key2509, -1), (key2443, -1), (key2480, -2), (key2472, -2), (key2503, -2), (key2390, 1), (key2378, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2437, 1)]

theorem rawRowCheck3441 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form14 = rawRow3441 := by decide +kernel

def row3441 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

theorem rowCheck3441 : row3441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3441 := by decide +kernel

theorem rowEval3441 (x : Key → ℝ) : Integer.Sparse.eval row3441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3441, Integer.Sparse.eval_collectBalanced, rawRowCheck3441]

def rawRow3442 : Integer.Sparse Key := [(key2576, -2), (key2571, -2), (key2580, -2), (key2569, 2), (key2576, 2), (key2571, 2), (key2509, 2), (key2484, 2), (key2524, 2), (key2411, -1), (key2443, -1), (key2383, -1), (key2509, -1), (key2394, -1), (key2484, -1), (key2472, -2), (key2503, -2), (key2480, -2), (key2406, 1), (key2437, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2480, 1)]

theorem rawRowCheck3442 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form14 = rawRow3442 := by decide +kernel

def row3442 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

theorem rowCheck3442 : row3442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3442 := by decide +kernel

theorem rowEval3442 (x : Key → ℝ) : Integer.Sparse.eval row3442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3442, Integer.Sparse.eval_collectBalanced, rawRowCheck3442]

def rawRow3443 : Integer.Sparse Key := [(key2576, -2), (key2580, -2), (key2571, -2), (key2576, 2), (key2569, 2), (key2571, 2), (key2509, 2), (key2524, 2), (key2484, 2), (key2443, -1), (key2411, -1), (key2509, -1), (key2383, -1), (key2484, -1), (key2394, -1), (key2503, -2), (key2472, -2), (key2480, -2), (key2437, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2480, 1), (key2390, 1)]

theorem rawRowCheck3443 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form14 = rawRow3443 := by decide +kernel

def row3443 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

theorem rowCheck3443 : row3443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3443 := by decide +kernel

theorem rowEval3443 (x : Key → ℝ) : Integer.Sparse.eval row3443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3443, Integer.Sparse.eval_collectBalanced, rawRowCheck3443]

def rawRow3444 : Integer.Sparse Key := [(key2580, -2), (key2571, -2), (key2576, -2), (key2571, 2), (key2576, 2), (key2569, 2), (key2524, 2), (key2484, 2), (key2509, 2), (key2484, -1), (key2509, -1), (key2394, -1), (key2443, -1), (key2383, -1), (key2411, -1), (key2480, -2), (key2503, -2), (key2472, -2), (key2480, 1), (key2503, 1), (key2390, 1), (key2437, 1), (key2378, 1), (key2406, 1)]

theorem rawRowCheck3444 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form14 = rawRow3444 := by decide +kernel

def row3444 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

theorem rowCheck3444 : row3444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3444 := by decide +kernel

theorem rowEval3444 (x : Key → ℝ) : Integer.Sparse.eval row3444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3444, Integer.Sparse.eval_collectBalanced, rawRowCheck3444]

def rawRow3445 : Integer.Sparse Key := [(key2580, -2), (key2576, -2), (key2571, -2), (key2576, 2), (key2571, 2), (key2569, 2), (key2524, 2), (key2509, 2), (key2484, 2), (key2509, -1), (key2484, -1), (key2443, -1), (key2394, -1), (key2411, -1), (key2383, -1), (key2503, -2), (key2480, -2), (key2472, -2), (key2503, 1), (key2480, 1), (key2437, 1), (key2390, 1), (key2406, 1), (key2378, 1)]

theorem rawRowCheck3445 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form14 = rawRow3445 := by decide +kernel

def row3445 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

theorem rowCheck3445 : row3445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3445 := by decide +kernel

theorem rowEval3445 (x : Key → ℝ) : Integer.Sparse.eval row3445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3445, Integer.Sparse.eval_collectBalanced, rawRowCheck3445]

def rawRow3446 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2614, 2), (key2807, 2), (key2827, 2), (key2624, 1), (key2630, 1), (key2851, 1), (key2868, 1), (key3021, 1), (key3025, 1), (key2630, -1), (key2638, -1), (key2704, -1), (key2724, -1), (key2858, -1), (key2868, -1), (key2657, -2), (key2918, -2), (key2922, -2), (key2657, 1), (key2659, 1), (key2752, 1), (key2757, 1), (key2919, 1), (key2922, 1)]

theorem rawRowCheck3446 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form15 = rawRow3446 := by decide +kernel

def row3446 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

theorem rowCheck3446 : row3446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3446 := by decide +kernel

theorem rowEval3446 (x : Key → ℝ) : Integer.Sparse.eval row3446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3446, Integer.Sparse.eval_collectBalanced, rawRowCheck3446]

def rawRow3447 : Integer.Sparse Key := [(key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2614, 2), (key2827, 2), (key2807, 2), (key2630, 1), (key2624, 1), (key2868, 1), (key2851, 1), (key3025, 1), (key3021, 1), (key2638, -1), (key2630, -1), (key2724, -1), (key2704, -1), (key2868, -1), (key2858, -1), (key2657, -2), (key2922, -2), (key2918, -2), (key2659, 1), (key2657, 1), (key2757, 1), (key2752, 1), (key2922, 1), (key2919, 1)]

theorem rawRowCheck3447 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form15 = rawRow3447 := by decide +kernel

def row3447 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

theorem rowCheck3447 : row3447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3447 := by decide +kernel

theorem rowEval3447 (x : Key → ℝ) : Integer.Sparse.eval row3447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3447, Integer.Sparse.eval_collectBalanced, rawRowCheck3447]

def rawRow3448 : Integer.Sparse Key := [(key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2807, 2), (key2614, 2), (key2827, 2), (key2851, 1), (key3021, 1), (key2624, 1), (key3025, 1), (key2630, 1), (key2868, 1), (key2704, -1), (key2858, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2918, -2), (key2657, -2), (key2922, -2), (key2752, 1), (key2919, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2757, 1)]

theorem rawRowCheck3448 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form15 = rawRow3448 := by decide +kernel

def row3448 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

theorem rowCheck3448 : row3448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3448 := by decide +kernel

theorem rowEval3448 (x : Key → ℝ) : Integer.Sparse.eval row3448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3448, Integer.Sparse.eval_collectBalanced, rawRowCheck3448]

def rawRow3449 : Integer.Sparse Key := [(key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key2807, 2), (key2827, 2), (key2614, 2), (key3021, 1), (key2851, 1), (key3025, 1), (key2624, 1), (key2868, 1), (key2630, 1), (key2858, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2724, -1), (key2638, -1), (key2918, -2), (key2922, -2), (key2657, -2), (key2919, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2757, 1), (key2659, 1)]

theorem rawRowCheck3449 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form15 = rawRow3449 := by decide +kernel

def row3449 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

theorem rowCheck3449 : row3449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3449 := by decide +kernel

theorem rowEval3449 (x : Key → ℝ) : Integer.Sparse.eval row3449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3449, Integer.Sparse.eval_collectBalanced, rawRowCheck3449]

def rawRow3450 : Integer.Sparse Key := [(key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2827, 2), (key2614, 2), (key2807, 2), (key2868, 1), (key3025, 1), (key2630, 1), (key3021, 1), (key2624, 1), (key2851, 1), (key2724, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2630, -1), (key2704, -1), (key2922, -2), (key2657, -2), (key2918, -2), (key2757, 1), (key2922, 1), (key2659, 1), (key2919, 1), (key2657, 1), (key2752, 1)]

theorem rawRowCheck3450 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form15 = rawRow3450 := by decide +kernel

def row3450 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

theorem rowCheck3450 : row3450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3450 := by decide +kernel

theorem rowEval3450 (x : Key → ℝ) : Integer.Sparse.eval row3450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3450, Integer.Sparse.eval_collectBalanced, rawRowCheck3450]

def rawRow3451 : Integer.Sparse Key := [(key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key2827, 2), (key2807, 2), (key2614, 2), (key3025, 1), (key2868, 1), (key3021, 1), (key2630, 1), (key2851, 1), (key2624, 1), (key2868, -1), (key2724, -1), (key2858, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key2922, -2), (key2918, -2), (key2657, -2), (key2922, 1), (key2757, 1), (key2919, 1), (key2659, 1), (key2752, 1), (key2657, 1)]

theorem rawRowCheck3451 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form15 = rawRow3451 := by decide +kernel

def row3451 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

theorem rowCheck3451 : row3451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3451 := by decide +kernel

theorem rowEval3451 (x : Key → ℝ) : Integer.Sparse.eval row3451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3451, Integer.Sparse.eval_collectBalanced, rawRowCheck3451]

def rawRow3452 : Integer.Sparse Key := [(key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2638, 1), (key2638, 1), (key2858, 1), (key2858, 1), (key3022, 1), (key3022, 1), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1), (key2659, -2), (key2919, -2), (key2919, -2), (key2657, 1), (key2657, 1), (key2752, 1), (key2752, 1), (key2918, 1), (key2918, 1)]

theorem rawRowCheck3452 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form15 = rawRow3452 := by decide +kernel

def row3452 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2698, -2), (key2752, 2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, 2), (key2918, 2), (key2919, -4), (key3022, 2)]

theorem rowCheck3452 : row3452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3452 := by decide +kernel

theorem rowEval3452 (x : Key → ℝ) : Integer.Sparse.eval row3452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3452, Integer.Sparse.eval_collectBalanced, rawRowCheck3452]

def rawRow3453 : Integer.Sparse Key := [(key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2858, 1), (key3022, 1), (key2638, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2919, -2), (key2659, -2), (key2919, -2), (key2752, 1), (key2918, 1), (key2657, 1), (key2918, 1), (key2657, 1), (key2752, 1)]

theorem rawRowCheck3453 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form15 = rawRow3453 := by decide +kernel

def row3453 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2698, -2), (key2752, 2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, 2), (key2918, 2), (key2919, -4), (key3022, 2)]

theorem rowCheck3453 : row3453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3453 := by decide +kernel

theorem rowEval3453 (x : Key → ℝ) : Integer.Sparse.eval row3453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3453, Integer.Sparse.eval_collectBalanced, rawRowCheck3453]

def rawRow3454 : Integer.Sparse Key := [(key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key3022, 1), (key2858, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2638, 1), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1), (key2919, -2), (key2919, -2), (key2659, -2), (key2918, 1), (key2752, 1), (key2918, 1), (key2657, 1), (key2752, 1), (key2657, 1)]

theorem rawRowCheck3454 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form15 = rawRow3454 := by decide +kernel

def row3454 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2698, -2), (key2752, 2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, 2), (key2918, 2), (key2919, -4), (key3022, 2)]

theorem rowCheck3454 : row3454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3454 := by decide +kernel

theorem rowEval3454 (x : Key → ℝ) : Integer.Sparse.eval row3454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3454, Integer.Sparse.eval_collectBalanced, rawRowCheck3454]

def rawRow3455 : Integer.Sparse Key := [(key2624, -1), (key2630, -1), (key2851, -1), (key3021, -1), (key2868, -1), (key3025, -1), (key2638, 2), (key2858, 2), (key3022, 2), (key2608, 1), (key2614, 1), (key2801, 1), (key2827, 1), (key3011, 1), (key3016, 1), (key2657, -1), (key2659, -1), (key2752, -1), (key2757, -1), (key2919, -1), (key2922, -1), (key2614, -2), (key2807, -2), (key2827, -2), (key2630, 1), (key2638, 1), (key2704, 1), (key2724, 1), (key2858, 1), (key2868, 1)]

theorem rawRowCheck3455 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form15 = rawRow3455 := by decide +kernel

def row3455 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

theorem rowCheck3455 : row3455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3455 := by decide +kernel

theorem rowEval3455 (x : Key → ℝ) : Integer.Sparse.eval row3455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3455, Integer.Sparse.eval_collectBalanced, rawRowCheck3455]

end MUB6.Certificate.GramRows

end OAI
