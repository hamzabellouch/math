import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15360 : Integer.Sparse Key := [(key2888, -2), (key2840, -2), (key2844, -2), (key2967, 6), (key2599, -2), (key2584, -2), (key2588, -2), (key2888, 2), (key2840, 2), (key2909, 2), (key2763, 2), (key2875, 2), (key2767, 2), (key2967, -2), (key2988, -2), (key2930, -2), (key2588, 6), (key2844, -2), (key2875, -2), (key2767, -2)]

theorem rawRowCheck15360 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form8 = rawRow15360 := by decide +kernel

def row15360 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15360 : row15360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15360 := by decide +kernel

theorem rowEval15360 (x : Key → ℝ) : Integer.Sparse.eval row15360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15360, Integer.Sparse.eval_collectBalanced, rawRowCheck15360]

def rawRow15361 : Integer.Sparse Key := [(key2844, -2), (key2888, -2), (key2840, -2), (key2967, 6), (key2588, -2), (key2599, -2), (key2584, -2), (key2875, 2), (key2909, 2), (key2767, 2), (key2888, 2), (key2763, 2), (key2840, 2), (key2988, -2), (key2930, -2), (key2967, -2), (key2588, 6), (key2875, -2), (key2767, -2), (key2844, -2)]

theorem rawRowCheck15361 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form8 = rawRow15361 := by decide +kernel

def row15361 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15361 : row15361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15361 := by decide +kernel

theorem rowEval15361 (x : Key → ℝ) : Integer.Sparse.eval row15361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15361, Integer.Sparse.eval_collectBalanced, rawRowCheck15361]

def rawRow15362 : Integer.Sparse Key := [(key2888, -2), (key2844, -2), (key2840, -2), (key2967, 6), (key2599, -2), (key2588, -2), (key2584, -2), (key2909, 2), (key2875, 2), (key2888, 2), (key2767, 2), (key2840, 2), (key2763, 2), (key2988, -2), (key2967, -2), (key2930, -2), (key2588, 6), (key2875, -2), (key2844, -2), (key2767, -2)]

theorem rawRowCheck15362 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form8 = rawRow15362 := by decide +kernel

def row15362 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15362 : row15362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15362 := by decide +kernel

theorem rowEval15362 (x : Key → ℝ) : Integer.Sparse.eval row15362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15362, Integer.Sparse.eval_collectBalanced, rawRowCheck15362]

def rawRow15363 : Integer.Sparse Key := [(key2840, -2), (key2844, -2), (key2967, -2), (key2888, 6), (key2763, -2), (key2767, -2), (key2930, -2), (key2584, 2), (key2588, 2), (key2840, 2), (key2875, 2), (key2967, 2), (key2988, 2), (key2599, -2), (key2888, -2), (key2909, -2), (key2767, 6), (key2588, -2), (key2844, -2), (key2875, -2)]

theorem rawRowCheck15363 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form8 = rawRow15363 := by decide +kernel

def row15363 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

theorem rowCheck15363 : row15363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15363 := by decide +kernel

theorem rowEval15363 (x : Key → ℝ) : Integer.Sparse.eval row15363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15363, Integer.Sparse.eval_collectBalanced, rawRowCheck15363]

def rawRow15364 : Integer.Sparse Key := [(key2844, -2), (key2840, -2), (key2967, -2), (key2888, 6), (key2767, -2), (key2763, -2), (key2930, -2), (key2588, 2), (key2584, 2), (key2875, 2), (key2840, 2), (key2988, 2), (key2967, 2), (key2599, -2), (key2909, -2), (key2888, -2), (key2767, 6), (key2588, -2), (key2875, -2), (key2844, -2)]

theorem rawRowCheck15364 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form8 = rawRow15364 := by decide +kernel

def row15364 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

theorem rowCheck15364 : row15364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15364 := by decide +kernel

theorem rowEval15364 (x : Key → ℝ) : Integer.Sparse.eval row15364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15364, Integer.Sparse.eval_collectBalanced, rawRowCheck15364]

def rawRow15365 : Integer.Sparse Key := [(key2840, -2), (key2967, -2), (key2844, -2), (key2888, 6), (key2763, -2), (key2930, -2), (key2767, -2), (key2840, 2), (key2967, 2), (key2584, 2), (key2988, 2), (key2588, 2), (key2875, 2), (key2888, -2), (key2599, -2), (key2909, -2), (key2767, 6), (key2844, -2), (key2588, -2), (key2875, -2)]

theorem rawRowCheck15365 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form8 = rawRow15365 := by decide +kernel

def row15365 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

theorem rowCheck15365 : row15365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15365 := by decide +kernel

theorem rowEval15365 (x : Key → ℝ) : Integer.Sparse.eval row15365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15365, Integer.Sparse.eval_collectBalanced, rawRowCheck15365]

def rawRow15366 : Integer.Sparse Key := [(key2967, -2), (key2840, -2), (key2844, -2), (key2888, 6), (key2930, -2), (key2763, -2), (key2767, -2), (key2967, 2), (key2840, 2), (key2988, 2), (key2584, 2), (key2875, 2), (key2588, 2), (key2888, -2), (key2909, -2), (key2599, -2), (key2767, 6), (key2844, -2), (key2875, -2), (key2588, -2)]

theorem rawRowCheck15366 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form8 = rawRow15366 := by decide +kernel

def row15366 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

theorem rowCheck15366 : row15366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15366 := by decide +kernel

theorem rowEval15366 (x : Key → ℝ) : Integer.Sparse.eval row15366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15366, Integer.Sparse.eval_collectBalanced, rawRowCheck15366]

def rawRow15367 : Integer.Sparse Key := [(key2844, -2), (key2967, -2), (key2840, -2), (key2888, 6), (key2767, -2), (key2930, -2), (key2763, -2), (key2875, 2), (key2988, 2), (key2588, 2), (key2967, 2), (key2584, 2), (key2840, 2), (key2909, -2), (key2599, -2), (key2888, -2), (key2767, 6), (key2875, -2), (key2588, -2), (key2844, -2)]

theorem rawRowCheck15367 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form8 = rawRow15367 := by decide +kernel

def row15367 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

theorem rowCheck15367 : row15367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15367 := by decide +kernel

theorem rowEval15367 (x : Key → ℝ) : Integer.Sparse.eval row15367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15367, Integer.Sparse.eval_collectBalanced, rawRowCheck15367]

def rawRow15368 : Integer.Sparse Key := [(key2967, -2), (key2844, -2), (key2840, -2), (key2888, 6), (key2930, -2), (key2767, -2), (key2763, -2), (key2988, 2), (key2875, 2), (key2967, 2), (key2588, 2), (key2840, 2), (key2584, 2), (key2909, -2), (key2888, -2), (key2599, -2), (key2767, 6), (key2875, -2), (key2844, -2), (key2588, -2)]

theorem rawRowCheck15368 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form8 = rawRow15368 := by decide +kernel

def row15368 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

theorem rowCheck15368 : row15368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15368 := by decide +kernel

theorem rowEval15368 (x : Key → ℝ) : Integer.Sparse.eval row15368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15368, Integer.Sparse.eval_collectBalanced, rawRowCheck15368]

def rawRow15369 : Integer.Sparse Key := [(key2840, -2), (key2888, -2), (key2967, -2), (key2844, 6), (key2840, -2), (key2888, -2), (key2967, -2), (key2584, 2), (key2599, 2), (key2763, 2), (key2909, 2), (key2930, 2), (key2988, 2), (key2588, -2), (key2767, -2), (key2875, -2), (key2844, 6), (key2588, -2), (key2767, -2), (key2875, -2)]

theorem rawRowCheck15369 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form8 = rawRow15369 := by decide +kernel

def row15369 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

theorem rowCheck15369 : row15369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15369 := by decide +kernel

theorem rowEval15369 (x : Key → ℝ) : Integer.Sparse.eval row15369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15369, Integer.Sparse.eval_collectBalanced, rawRowCheck15369]

def rawRow15370 : Integer.Sparse Key := [(key2888, -2), (key2840, -2), (key2967, -2), (key2844, 6), (key2888, -2), (key2840, -2), (key2967, -2), (key2599, 2), (key2584, 2), (key2909, 2), (key2763, 2), (key2988, 2), (key2930, 2), (key2588, -2), (key2875, -2), (key2767, -2), (key2844, 6), (key2588, -2), (key2875, -2), (key2767, -2)]

theorem rawRowCheck15370 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form8 = rawRow15370 := by decide +kernel

def row15370 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

theorem rowCheck15370 : row15370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15370 := by decide +kernel

theorem rowEval15370 (x : Key → ℝ) : Integer.Sparse.eval row15370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15370, Integer.Sparse.eval_collectBalanced, rawRowCheck15370]

def rawRow15371 : Integer.Sparse Key := [(key2840, -2), (key2967, -2), (key2888, -2), (key2844, 6), (key2840, -2), (key2967, -2), (key2888, -2), (key2763, 2), (key2930, 2), (key2584, 2), (key2988, 2), (key2599, 2), (key2909, 2), (key2767, -2), (key2588, -2), (key2875, -2), (key2844, 6), (key2767, -2), (key2588, -2), (key2875, -2)]

theorem rawRowCheck15371 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form8 = rawRow15371 := by decide +kernel

def row15371 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

theorem rowCheck15371 : row15371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15371 := by decide +kernel

theorem rowEval15371 (x : Key → ℝ) : Integer.Sparse.eval row15371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15371, Integer.Sparse.eval_collectBalanced, rawRowCheck15371]

def rawRow15372 : Integer.Sparse Key := [(key2967, -2), (key2840, -2), (key2888, -2), (key2844, 6), (key2967, -2), (key2840, -2), (key2888, -2), (key2930, 2), (key2763, 2), (key2988, 2), (key2584, 2), (key2909, 2), (key2599, 2), (key2767, -2), (key2875, -2), (key2588, -2), (key2844, 6), (key2767, -2), (key2875, -2), (key2588, -2)]

theorem rawRowCheck15372 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form8 = rawRow15372 := by decide +kernel

def row15372 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

theorem rowCheck15372 : row15372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15372 := by decide +kernel

theorem rowEval15372 (x : Key → ℝ) : Integer.Sparse.eval row15372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15372, Integer.Sparse.eval_collectBalanced, rawRowCheck15372]

def rawRow15373 : Integer.Sparse Key := [(key2888, -2), (key2967, -2), (key2840, -2), (key2844, 6), (key2888, -2), (key2967, -2), (key2840, -2), (key2909, 2), (key2988, 2), (key2599, 2), (key2930, 2), (key2584, 2), (key2763, 2), (key2875, -2), (key2588, -2), (key2767, -2), (key2844, 6), (key2875, -2), (key2588, -2), (key2767, -2)]

theorem rawRowCheck15373 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form8 = rawRow15373 := by decide +kernel

def row15373 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

theorem rowCheck15373 : row15373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15373 := by decide +kernel

theorem rowEval15373 (x : Key → ℝ) : Integer.Sparse.eval row15373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15373, Integer.Sparse.eval_collectBalanced, rawRowCheck15373]

def rawRow15374 : Integer.Sparse Key := [(key2967, -2), (key2888, -2), (key2840, -2), (key2844, 6), (key2967, -2), (key2888, -2), (key2840, -2), (key2988, 2), (key2909, 2), (key2930, 2), (key2599, 2), (key2763, 2), (key2584, 2), (key2875, -2), (key2767, -2), (key2588, -2), (key2844, 6), (key2875, -2), (key2767, -2), (key2588, -2)]

theorem rawRowCheck15374 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form8 = rawRow15374 := by decide +kernel

def row15374 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

theorem rowCheck15374 : row15374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15374 := by decide +kernel

theorem rowEval15374 (x : Key → ℝ) : Integer.Sparse.eval row15374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15374, Integer.Sparse.eval_collectBalanced, rawRowCheck15374]

def rawRow15375 : Integer.Sparse Key := [(key2012, 4), (key2012, 4), (key2025, 4), (key2041, -4), (key2054, -4), (key2054, -4), (key2126, -4), (key2143, -4), (key2143, -4), (key2227, 12)]

theorem rawRowCheck15375 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form9 = rawRow15375 := by decide +kernel

def row15375 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

theorem rowCheck15375 : row15375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15375 := by decide +kernel

theorem rowEval15375 (x : Key → ℝ) : Integer.Sparse.eval row15375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15375, Integer.Sparse.eval_collectBalanced, rawRowCheck15375]

def rawRow15376 : Integer.Sparse Key := [(key2012, 4), (key2025, 4), (key2012, 4), (key2054, -4), (key2041, -4), (key2054, -4), (key2143, -4), (key2126, -4), (key2143, -4), (key2227, 12)]

theorem rawRowCheck15376 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form9 = rawRow15376 := by decide +kernel

def row15376 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

theorem rowCheck15376 : row15376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15376 := by decide +kernel

theorem rowEval15376 (x : Key → ℝ) : Integer.Sparse.eval row15376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15376, Integer.Sparse.eval_collectBalanced, rawRowCheck15376]

def rawRow15377 : Integer.Sparse Key := [(key2025, 4), (key2012, 4), (key2012, 4), (key2054, -4), (key2054, -4), (key2041, -4), (key2143, -4), (key2143, -4), (key2126, -4), (key2227, 12)]

theorem rawRowCheck15377 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form9 = rawRow15377 := by decide +kernel

def row15377 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

theorem rowCheck15377 : row15377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15377 := by decide +kernel

theorem rowEval15377 (x : Key → ℝ) : Integer.Sparse.eval row15377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15377, Integer.Sparse.eval_collectBalanced, rawRowCheck15377]

def rawRow15378 : Integer.Sparse Key := [(key2012, 4), (key2041, 4), (key2054, 4), (key2012, -4), (key2025, -4), (key2054, -4), (key2126, -4), (key2143, -4), (key2227, -4), (key2143, 12)]

theorem rawRowCheck15378 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form9 = rawRow15378 := by decide +kernel

def row15378 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15378 : row15378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15378 := by decide +kernel

theorem rowEval15378 (x : Key → ℝ) : Integer.Sparse.eval row15378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15378, Integer.Sparse.eval_collectBalanced, rawRowCheck15378]

def rawRow15379 : Integer.Sparse Key := [(key2012, 4), (key2054, 4), (key2041, 4), (key2025, -4), (key2012, -4), (key2054, -4), (key2143, -4), (key2126, -4), (key2227, -4), (key2143, 12)]

theorem rawRowCheck15379 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form9 = rawRow15379 := by decide +kernel

def row15379 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15379 : row15379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15379 := by decide +kernel

theorem rowEval15379 (x : Key → ℝ) : Integer.Sparse.eval row15379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15379, Integer.Sparse.eval_collectBalanced, rawRowCheck15379]

def rawRow15380 : Integer.Sparse Key := [(key2041, 4), (key2012, 4), (key2054, 4), (key2012, -4), (key2054, -4), (key2025, -4), (key2126, -4), (key2227, -4), (key2143, -4), (key2143, 12)]

theorem rawRowCheck15380 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form9 = rawRow15380 := by decide +kernel

def row15380 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15380 : row15380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15380 := by decide +kernel

theorem rowEval15380 (x : Key → ℝ) : Integer.Sparse.eval row15380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15380, Integer.Sparse.eval_collectBalanced, rawRowCheck15380]

def rawRow15381 : Integer.Sparse Key := [(key2041, 4), (key2054, 4), (key2012, 4), (key2054, -4), (key2012, -4), (key2025, -4), (key2227, -4), (key2126, -4), (key2143, -4), (key2143, 12)]

theorem rawRowCheck15381 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form9 = rawRow15381 := by decide +kernel

def row15381 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15381 : row15381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15381 := by decide +kernel

theorem rowEval15381 (x : Key → ℝ) : Integer.Sparse.eval row15381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15381, Integer.Sparse.eval_collectBalanced, rawRowCheck15381]

def rawRow15382 : Integer.Sparse Key := [(key2054, 4), (key2012, 4), (key2041, 4), (key2025, -4), (key2054, -4), (key2012, -4), (key2143, -4), (key2227, -4), (key2126, -4), (key2143, 12)]

theorem rawRowCheck15382 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form9 = rawRow15382 := by decide +kernel

def row15382 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15382 : row15382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15382 := by decide +kernel

theorem rowEval15382 (x : Key → ℝ) : Integer.Sparse.eval row15382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15382, Integer.Sparse.eval_collectBalanced, rawRowCheck15382]

def rawRow15383 : Integer.Sparse Key := [(key2054, 4), (key2041, 4), (key2012, 4), (key2054, -4), (key2025, -4), (key2012, -4), (key2227, -4), (key2143, -4), (key2126, -4), (key2143, 12)]

theorem rawRowCheck15383 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form9 = rawRow15383 := by decide +kernel

def row15383 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15383 : row15383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15383 := by decide +kernel

theorem rowEval15383 (x : Key → ℝ) : Integer.Sparse.eval row15383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15383, Integer.Sparse.eval_collectBalanced, rawRowCheck15383]

def rawRow15384 : Integer.Sparse Key := [(key2012, 4), (key2012, 4), (key2025, 4), (key2126, -4), (key2143, -4), (key2143, -4), (key2041, -4), (key2054, -4), (key2054, -4), (key2227, 12)]

theorem rawRowCheck15384 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form9 = rawRow15384 := by decide +kernel

def row15384 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

theorem rowCheck15384 : row15384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15384 := by decide +kernel

theorem rowEval15384 (x : Key → ℝ) : Integer.Sparse.eval row15384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15384, Integer.Sparse.eval_collectBalanced, rawRowCheck15384]

def rawRow15385 : Integer.Sparse Key := [(key2012, 4), (key2025, 4), (key2012, 4), (key2143, -4), (key2126, -4), (key2143, -4), (key2054, -4), (key2041, -4), (key2054, -4), (key2227, 12)]

theorem rawRowCheck15385 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form9 = rawRow15385 := by decide +kernel

def row15385 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

theorem rowCheck15385 : row15385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15385 := by decide +kernel

theorem rowEval15385 (x : Key → ℝ) : Integer.Sparse.eval row15385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15385, Integer.Sparse.eval_collectBalanced, rawRowCheck15385]

def rawRow15386 : Integer.Sparse Key := [(key2025, 4), (key2012, 4), (key2012, 4), (key2143, -4), (key2143, -4), (key2126, -4), (key2054, -4), (key2054, -4), (key2041, -4), (key2227, 12)]

theorem rawRowCheck15386 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form9 = rawRow15386 := by decide +kernel

def row15386 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

theorem rowCheck15386 : row15386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15386 := by decide +kernel

theorem rowEval15386 (x : Key → ℝ) : Integer.Sparse.eval row15386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15386, Integer.Sparse.eval_collectBalanced, rawRowCheck15386]

def rawRow15387 : Integer.Sparse Key := [(key2012, 4), (key2126, 4), (key2143, 4), (key2012, -4), (key2025, -4), (key2143, -4), (key2041, -4), (key2054, -4), (key2227, -4), (key2054, 12)]

theorem rawRowCheck15387 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form9 = rawRow15387 := by decide +kernel

def row15387 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

theorem rowCheck15387 : row15387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15387 := by decide +kernel

theorem rowEval15387 (x : Key → ℝ) : Integer.Sparse.eval row15387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15387, Integer.Sparse.eval_collectBalanced, rawRowCheck15387]

def rawRow15388 : Integer.Sparse Key := [(key2012, 4), (key2143, 4), (key2126, 4), (key2025, -4), (key2012, -4), (key2143, -4), (key2054, -4), (key2041, -4), (key2227, -4), (key2054, 12)]

theorem rawRowCheck15388 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form9 = rawRow15388 := by decide +kernel

def row15388 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

theorem rowCheck15388 : row15388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15388 := by decide +kernel

theorem rowEval15388 (x : Key → ℝ) : Integer.Sparse.eval row15388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15388, Integer.Sparse.eval_collectBalanced, rawRowCheck15388]

def rawRow15389 : Integer.Sparse Key := [(key2126, 4), (key2012, 4), (key2143, 4), (key2012, -4), (key2143, -4), (key2025, -4), (key2041, -4), (key2227, -4), (key2054, -4), (key2054, 12)]

theorem rawRowCheck15389 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form9 = rawRow15389 := by decide +kernel

def row15389 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

theorem rowCheck15389 : row15389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15389 := by decide +kernel

theorem rowEval15389 (x : Key → ℝ) : Integer.Sparse.eval row15389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15389, Integer.Sparse.eval_collectBalanced, rawRowCheck15389]

def rawRow15390 : Integer.Sparse Key := [(key2126, 4), (key2143, 4), (key2012, 4), (key2143, -4), (key2012, -4), (key2025, -4), (key2227, -4), (key2041, -4), (key2054, -4), (key2054, 12)]

theorem rawRowCheck15390 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form9 = rawRow15390 := by decide +kernel

def row15390 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

theorem rowCheck15390 : row15390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15390 := by decide +kernel

theorem rowEval15390 (x : Key → ℝ) : Integer.Sparse.eval row15390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15390, Integer.Sparse.eval_collectBalanced, rawRowCheck15390]

def rawRow15391 : Integer.Sparse Key := [(key2143, 4), (key2012, 4), (key2126, 4), (key2025, -4), (key2143, -4), (key2012, -4), (key2054, -4), (key2227, -4), (key2041, -4), (key2054, 12)]

theorem rawRowCheck15391 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form9 = rawRow15391 := by decide +kernel

def row15391 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

theorem rowCheck15391 : row15391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15391 := by decide +kernel

theorem rowEval15391 (x : Key → ℝ) : Integer.Sparse.eval row15391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15391, Integer.Sparse.eval_collectBalanced, rawRowCheck15391]

def rawRow15392 : Integer.Sparse Key := [(key2143, 4), (key2126, 4), (key2012, 4), (key2143, -4), (key2025, -4), (key2012, -4), (key2227, -4), (key2054, -4), (key2041, -4), (key2054, 12)]

theorem rawRowCheck15392 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form9 = rawRow15392 := by decide +kernel

def row15392 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

theorem rowCheck15392 : row15392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15392 := by decide +kernel

theorem rowEval15392 (x : Key → ℝ) : Integer.Sparse.eval row15392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15392, Integer.Sparse.eval_collectBalanced, rawRowCheck15392]

def rawRow15393 : Integer.Sparse Key := [(key2012, 4), (key2041, 4), (key2054, 4), (key2126, -4), (key2143, -4), (key2227, -4), (key2012, -4), (key2025, -4), (key2054, -4), (key2143, 12)]

theorem rawRowCheck15393 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form9 = rawRow15393 := by decide +kernel

def row15393 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15393 : row15393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15393 := by decide +kernel

theorem rowEval15393 (x : Key → ℝ) : Integer.Sparse.eval row15393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15393, Integer.Sparse.eval_collectBalanced, rawRowCheck15393]

def rawRow15394 : Integer.Sparse Key := [(key2012, 4), (key2054, 4), (key2041, 4), (key2143, -4), (key2126, -4), (key2227, -4), (key2025, -4), (key2012, -4), (key2054, -4), (key2143, 12)]

theorem rawRowCheck15394 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form9 = rawRow15394 := by decide +kernel

def row15394 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15394 : row15394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15394 := by decide +kernel

theorem rowEval15394 (x : Key → ℝ) : Integer.Sparse.eval row15394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15394, Integer.Sparse.eval_collectBalanced, rawRowCheck15394]

def rawRow15395 : Integer.Sparse Key := [(key2041, 4), (key2012, 4), (key2054, 4), (key2126, -4), (key2227, -4), (key2143, -4), (key2012, -4), (key2054, -4), (key2025, -4), (key2143, 12)]

theorem rawRowCheck15395 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form9 = rawRow15395 := by decide +kernel

def row15395 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15395 : row15395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15395 := by decide +kernel

theorem rowEval15395 (x : Key → ℝ) : Integer.Sparse.eval row15395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15395, Integer.Sparse.eval_collectBalanced, rawRowCheck15395]

def rawRow15396 : Integer.Sparse Key := [(key2041, 4), (key2054, 4), (key2012, 4), (key2227, -4), (key2126, -4), (key2143, -4), (key2054, -4), (key2012, -4), (key2025, -4), (key2143, 12)]

theorem rawRowCheck15396 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form9 = rawRow15396 := by decide +kernel

def row15396 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15396 : row15396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15396 := by decide +kernel

theorem rowEval15396 (x : Key → ℝ) : Integer.Sparse.eval row15396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15396, Integer.Sparse.eval_collectBalanced, rawRowCheck15396]

def rawRow15397 : Integer.Sparse Key := [(key2054, 4), (key2012, 4), (key2041, 4), (key2143, -4), (key2227, -4), (key2126, -4), (key2025, -4), (key2054, -4), (key2012, -4), (key2143, 12)]

theorem rawRowCheck15397 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form9 = rawRow15397 := by decide +kernel

def row15397 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15397 : row15397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15397 := by decide +kernel

theorem rowEval15397 (x : Key → ℝ) : Integer.Sparse.eval row15397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15397, Integer.Sparse.eval_collectBalanced, rawRowCheck15397]

def rawRow15398 : Integer.Sparse Key := [(key2054, 4), (key2041, 4), (key2012, 4), (key2227, -4), (key2143, -4), (key2126, -4), (key2054, -4), (key2025, -4), (key2012, -4), (key2143, 12)]

theorem rawRowCheck15398 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form9 = rawRow15398 := by decide +kernel

def row15398 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15398 : row15398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15398 := by decide +kernel

theorem rowEval15398 (x : Key → ℝ) : Integer.Sparse.eval row15398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15398, Integer.Sparse.eval_collectBalanced, rawRowCheck15398]

def rawRow15399 : Integer.Sparse Key := [(key2012, 4), (key2126, 4), (key2143, 4), (key2041, -4), (key2054, -4), (key2227, -4), (key2012, -4), (key2025, -4), (key2143, -4), (key2054, 12)]

theorem rawRowCheck15399 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form9 = rawRow15399 := by decide +kernel

def row15399 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

theorem rowCheck15399 : row15399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15399 := by decide +kernel

theorem rowEval15399 (x : Key → ℝ) : Integer.Sparse.eval row15399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15399, Integer.Sparse.eval_collectBalanced, rawRowCheck15399]

def rawRow15400 : Integer.Sparse Key := [(key2012, 4), (key2143, 4), (key2126, 4), (key2054, -4), (key2041, -4), (key2227, -4), (key2025, -4), (key2012, -4), (key2143, -4), (key2054, 12)]

theorem rawRowCheck15400 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form9 = rawRow15400 := by decide +kernel

def row15400 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

theorem rowCheck15400 : row15400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15400 := by decide +kernel

theorem rowEval15400 (x : Key → ℝ) : Integer.Sparse.eval row15400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15400, Integer.Sparse.eval_collectBalanced, rawRowCheck15400]

def rawRow15401 : Integer.Sparse Key := [(key2126, 4), (key2012, 4), (key2143, 4), (key2041, -4), (key2227, -4), (key2054, -4), (key2012, -4), (key2143, -4), (key2025, -4), (key2054, 12)]

theorem rawRowCheck15401 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form9 = rawRow15401 := by decide +kernel

def row15401 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

theorem rowCheck15401 : row15401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15401 := by decide +kernel

theorem rowEval15401 (x : Key → ℝ) : Integer.Sparse.eval row15401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15401, Integer.Sparse.eval_collectBalanced, rawRowCheck15401]

def rawRow15402 : Integer.Sparse Key := [(key2126, 4), (key2143, 4), (key2012, 4), (key2227, -4), (key2041, -4), (key2054, -4), (key2143, -4), (key2012, -4), (key2025, -4), (key2054, 12)]

theorem rawRowCheck15402 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form9 = rawRow15402 := by decide +kernel

def row15402 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

theorem rowCheck15402 : row15402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15402 := by decide +kernel

theorem rowEval15402 (x : Key → ℝ) : Integer.Sparse.eval row15402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15402, Integer.Sparse.eval_collectBalanced, rawRowCheck15402]

def rawRow15403 : Integer.Sparse Key := [(key2143, 4), (key2012, 4), (key2126, 4), (key2054, -4), (key2227, -4), (key2041, -4), (key2025, -4), (key2143, -4), (key2012, -4), (key2054, 12)]

theorem rawRowCheck15403 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form9 = rawRow15403 := by decide +kernel

def row15403 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

theorem rowCheck15403 : row15403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15403 := by decide +kernel

theorem rowEval15403 (x : Key → ℝ) : Integer.Sparse.eval row15403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15403, Integer.Sparse.eval_collectBalanced, rawRowCheck15403]

def rawRow15404 : Integer.Sparse Key := [(key2143, 4), (key2126, 4), (key2012, 4), (key2227, -4), (key2054, -4), (key2041, -4), (key2143, -4), (key2025, -4), (key2012, -4), (key2054, 12)]

theorem rawRowCheck15404 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form9 = rawRow15404 := by decide +kernel

def row15404 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

theorem rowCheck15404 : row15404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15404 := by decide +kernel

theorem rowEval15404 (x : Key → ℝ) : Integer.Sparse.eval row15404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15404, Integer.Sparse.eval_collectBalanced, rawRowCheck15404]

def rawRow15405 : Integer.Sparse Key := [(key2041, 4), (key2126, 4), (key2227, 4), (key2012, -4), (key2054, -4), (key2143, -4), (key2012, -4), (key2054, -4), (key2143, -4), (key2025, 12)]

theorem rawRowCheck15405 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form9 = rawRow15405 := by decide +kernel

def row15405 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

theorem rowCheck15405 : row15405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15405 := by decide +kernel

theorem rowEval15405 (x : Key → ℝ) : Integer.Sparse.eval row15405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15405, Integer.Sparse.eval_collectBalanced, rawRowCheck15405]

def rawRow15406 : Integer.Sparse Key := [(key2041, 4), (key2227, 4), (key2126, 4), (key2054, -4), (key2012, -4), (key2143, -4), (key2054, -4), (key2012, -4), (key2143, -4), (key2025, 12)]

theorem rawRowCheck15406 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form9 = rawRow15406 := by decide +kernel

def row15406 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

theorem rowCheck15406 : row15406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15406 := by decide +kernel

theorem rowEval15406 (x : Key → ℝ) : Integer.Sparse.eval row15406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15406, Integer.Sparse.eval_collectBalanced, rawRowCheck15406]

def rawRow15407 : Integer.Sparse Key := [(key2126, 4), (key2041, 4), (key2227, 4), (key2012, -4), (key2143, -4), (key2054, -4), (key2012, -4), (key2143, -4), (key2054, -4), (key2025, 12)]

theorem rawRowCheck15407 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form9 = rawRow15407 := by decide +kernel

def row15407 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

theorem rowCheck15407 : row15407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15407 := by decide +kernel

theorem rowEval15407 (x : Key → ℝ) : Integer.Sparse.eval row15407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15407, Integer.Sparse.eval_collectBalanced, rawRowCheck15407]

def rawRow15408 : Integer.Sparse Key := [(key2126, 4), (key2227, 4), (key2041, 4), (key2143, -4), (key2012, -4), (key2054, -4), (key2143, -4), (key2012, -4), (key2054, -4), (key2025, 12)]

theorem rawRowCheck15408 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form9 = rawRow15408 := by decide +kernel

def row15408 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

theorem rowCheck15408 : row15408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15408 := by decide +kernel

theorem rowEval15408 (x : Key → ℝ) : Integer.Sparse.eval row15408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15408, Integer.Sparse.eval_collectBalanced, rawRowCheck15408]

def rawRow15409 : Integer.Sparse Key := [(key2227, 4), (key2041, 4), (key2126, 4), (key2054, -4), (key2143, -4), (key2012, -4), (key2054, -4), (key2143, -4), (key2012, -4), (key2025, 12)]

theorem rawRowCheck15409 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form9 = rawRow15409 := by decide +kernel

def row15409 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

theorem rowCheck15409 : row15409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15409 := by decide +kernel

theorem rowEval15409 (x : Key → ℝ) : Integer.Sparse.eval row15409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15409, Integer.Sparse.eval_collectBalanced, rawRowCheck15409]

def rawRow15410 : Integer.Sparse Key := [(key2227, 4), (key2126, 4), (key2041, 4), (key2143, -4), (key2054, -4), (key2012, -4), (key2143, -4), (key2054, -4), (key2012, -4), (key2025, 12)]

theorem rawRowCheck15410 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form9 = rawRow15410 := by decide +kernel

def row15410 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

theorem rowCheck15410 : row15410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15410 := by decide +kernel

theorem rowEval15410 (x : Key → ℝ) : Integer.Sparse.eval row15410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15410, Integer.Sparse.eval_collectBalanced, rawRowCheck15410]

def rawRow15411 : Integer.Sparse Key := [(key2699, -1), (key2703, -1), (key2699, -1), (key2723, -1), (key2703, -1), (key2723, -1), (key2736, 2), (key2736, 2), (key2746, 2), (key2802, -1), (key2806, -1), (key2802, -1), (key2826, -1), (key2806, -1), (key2826, -1), (key2852, 2), (key2857, 2), (key2852, 2), (key2867, 2), (key2857, 2), (key2867, 2), (key2894, -1), (key2896, -1), (key2894, -1), (key2903, -1), (key2896, -1), (key2903, -1), (key2949, 2), (key2949, 2), (key2959, 2), (key2973, -1), (key2975, -1), (key2973, -1), (key2982, -1), (key2975, -1), (key2982, -1)]

theorem rawRowCheck15411 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form10 = rawRow15411 := by decide +kernel

def row15411 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

theorem rowCheck15411 : row15411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15411 := by decide +kernel

theorem rowEval15411 (x : Key → ℝ) : Integer.Sparse.eval row15411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15411, Integer.Sparse.eval_collectBalanced, rawRowCheck15411]

def rawRow15412 : Integer.Sparse Key := [(key2703, -1), (key2699, -1), (key2723, -1), (key2699, -1), (key2723, -1), (key2703, -1), (key2736, 2), (key2746, 2), (key2736, 2), (key2806, -1), (key2802, -1), (key2826, -1), (key2802, -1), (key2826, -1), (key2806, -1), (key2857, 2), (key2852, 2), (key2867, 2), (key2852, 2), (key2867, 2), (key2857, 2), (key2896, -1), (key2894, -1), (key2903, -1), (key2894, -1), (key2903, -1), (key2896, -1), (key2949, 2), (key2959, 2), (key2949, 2), (key2975, -1), (key2973, -1), (key2982, -1), (key2973, -1), (key2982, -1), (key2975, -1)]

theorem rawRowCheck15412 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form10 = rawRow15412 := by decide +kernel

def row15412 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

theorem rowCheck15412 : row15412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15412 := by decide +kernel

theorem rowEval15412 (x : Key → ℝ) : Integer.Sparse.eval row15412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15412, Integer.Sparse.eval_collectBalanced, rawRowCheck15412]

def rawRow15413 : Integer.Sparse Key := [(key2723, -1), (key2723, -1), (key2703, -1), (key2703, -1), (key2699, -1), (key2699, -1), (key2746, 2), (key2736, 2), (key2736, 2), (key2826, -1), (key2826, -1), (key2806, -1), (key2806, -1), (key2802, -1), (key2802, -1), (key2867, 2), (key2867, 2), (key2857, 2), (key2857, 2), (key2852, 2), (key2852, 2), (key2903, -1), (key2903, -1), (key2896, -1), (key2896, -1), (key2894, -1), (key2894, -1), (key2959, 2), (key2949, 2), (key2949, 2), (key2982, -1), (key2982, -1), (key2975, -1), (key2975, -1), (key2973, -1), (key2973, -1)]

theorem rawRowCheck15413 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form10 = rawRow15413 := by decide +kernel

def row15413 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

theorem rowCheck15413 : row15413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15413 := by decide +kernel

theorem rowEval15413 (x : Key → ℝ) : Integer.Sparse.eval row15413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15413, Integer.Sparse.eval_collectBalanced, rawRowCheck15413]

def rawRow15414 : Integer.Sparse Key := [(key2664, -1), (key2668, -1), (key2699, -1), (key2723, -1), (key2736, -1), (key2746, -1), (key2668, 2), (key2703, 2), (key2723, 2), (key2779, -1), (key2783, -1), (key2852, -1), (key2867, -1), (key2894, -1), (key2903, -1), (key2779, 2), (key2791, 2), (key2802, 2), (key2826, 2), (key2896, 2), (key2903, 2), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2857, -1), (key2867, -1), (key2937, 2), (key2973, 2), (key2982, 2), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2975, -1), (key2982, -1)]

theorem rawRowCheck15414 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form10 = rawRow15414 := by decide +kernel

def row15414 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

theorem rowCheck15414 : row15414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15414 := by decide +kernel

theorem rowEval15414 (x : Key → ℝ) : Integer.Sparse.eval row15414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15414, Integer.Sparse.eval_collectBalanced, rawRowCheck15414]

def rawRow15415 : Integer.Sparse Key := [(key2668, -1), (key2664, -1), (key2723, -1), (key2699, -1), (key2746, -1), (key2736, -1), (key2668, 2), (key2723, 2), (key2703, 2), (key2783, -1), (key2779, -1), (key2867, -1), (key2852, -1), (key2903, -1), (key2894, -1), (key2791, 2), (key2779, 2), (key2826, 2), (key2802, 2), (key2903, 2), (key2896, 2), (key2791, -1), (key2783, -1), (key2826, -1), (key2806, -1), (key2867, -1), (key2857, -1), (key2937, 2), (key2982, 2), (key2973, 2), (key2942, -1), (key2937, -1), (key2959, -1), (key2949, -1), (key2982, -1), (key2975, -1)]

theorem rawRowCheck15415 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form10 = rawRow15415 := by decide +kernel

def row15415 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

theorem rowCheck15415 : row15415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15415 := by decide +kernel

theorem rowEval15415 (x : Key → ℝ) : Integer.Sparse.eval row15415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15415, Integer.Sparse.eval_collectBalanced, rawRowCheck15415]

def rawRow15416 : Integer.Sparse Key := [(key2699, -1), (key2736, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2703, 2), (key2668, 2), (key2723, 2), (key2852, -1), (key2894, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2802, 2), (key2896, 2), (key2779, 2), (key2903, 2), (key2791, 2), (key2826, 2), (key2806, -1), (key2857, -1), (key2783, -1), (key2867, -1), (key2791, -1), (key2826, -1), (key2973, 2), (key2937, 2), (key2982, 2), (key2949, -1), (key2975, -1), (key2937, -1), (key2982, -1), (key2942, -1), (key2959, -1)]

theorem rawRowCheck15416 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form10 = rawRow15416 := by decide +kernel

def row15416 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

theorem rowCheck15416 : row15416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15416 := by decide +kernel

theorem rowEval15416 (x : Key → ℝ) : Integer.Sparse.eval row15416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15416, Integer.Sparse.eval_collectBalanced, rawRowCheck15416]

def rawRow15417 : Integer.Sparse Key := [(key2736, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2723, -1), (key2668, -1), (key2703, 2), (key2723, 2), (key2668, 2), (key2894, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2867, -1), (key2783, -1), (key2896, 2), (key2802, 2), (key2903, 2), (key2779, 2), (key2826, 2), (key2791, 2), (key2857, -1), (key2806, -1), (key2867, -1), (key2783, -1), (key2826, -1), (key2791, -1), (key2973, 2), (key2982, 2), (key2937, 2), (key2975, -1), (key2949, -1), (key2982, -1), (key2937, -1), (key2959, -1), (key2942, -1)]

theorem rawRowCheck15417 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form10 = rawRow15417 := by decide +kernel

def row15417 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

theorem rowCheck15417 : row15417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15417 := by decide +kernel

theorem rowEval15417 (x : Key → ℝ) : Integer.Sparse.eval row15417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15417, Integer.Sparse.eval_collectBalanced, rawRowCheck15417]

def rawRow15418 : Integer.Sparse Key := [(key2723, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2664, -1), (key2699, -1), (key2723, 2), (key2668, 2), (key2703, 2), (key2867, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2779, -1), (key2852, -1), (key2826, 2), (key2903, 2), (key2791, 2), (key2896, 2), (key2779, 2), (key2802, 2), (key2826, -1), (key2867, -1), (key2791, -1), (key2857, -1), (key2783, -1), (key2806, -1), (key2982, 2), (key2937, 2), (key2973, 2), (key2959, -1), (key2982, -1), (key2942, -1), (key2975, -1), (key2937, -1), (key2949, -1)]

theorem rawRowCheck15418 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form10 = rawRow15418 := by decide +kernel

def row15418 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

theorem rowCheck15418 : row15418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15418 := by decide +kernel

theorem rowEval15418 (x : Key → ℝ) : Integer.Sparse.eval row15418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15418, Integer.Sparse.eval_collectBalanced, rawRowCheck15418]

def rawRow15419 : Integer.Sparse Key := [(key2746, -1), (key2723, -1), (key2736, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2723, 2), (key2703, 2), (key2668, 2), (key2903, -1), (key2867, -1), (key2894, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2903, 2), (key2826, 2), (key2896, 2), (key2791, 2), (key2802, 2), (key2779, 2), (key2867, -1), (key2826, -1), (key2857, -1), (key2791, -1), (key2806, -1), (key2783, -1), (key2982, 2), (key2973, 2), (key2937, 2), (key2982, -1), (key2959, -1), (key2975, -1), (key2942, -1), (key2949, -1), (key2937, -1)]

theorem rawRowCheck15419 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form10 = rawRow15419 := by decide +kernel

def row15419 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

theorem rowCheck15419 : row15419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15419 := by decide +kernel

theorem rowEval15419 (x : Key → ℝ) : Integer.Sparse.eval row15419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15419, Integer.Sparse.eval_collectBalanced, rawRowCheck15419]

def rawRow15420 : Integer.Sparse Key := [(key2802, -1), (key2806, -1), (key2802, -1), (key2826, -1), (key2806, -1), (key2826, -1), (key2949, 2), (key2949, 2), (key2959, 2), (key2699, -1), (key2703, -1), (key2699, -1), (key2723, -1), (key2703, -1), (key2723, -1), (key2852, 2), (key2857, 2), (key2852, 2), (key2867, 2), (key2857, 2), (key2867, 2), (key2973, -1), (key2975, -1), (key2973, -1), (key2982, -1), (key2975, -1), (key2982, -1), (key2736, 2), (key2736, 2), (key2746, 2), (key2894, -1), (key2896, -1), (key2894, -1), (key2903, -1), (key2896, -1), (key2903, -1)]

theorem rawRowCheck15420 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form10 = rawRow15420 := by decide +kernel

def row15420 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

theorem rowCheck15420 : row15420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15420 := by decide +kernel

theorem rowEval15420 (x : Key → ℝ) : Integer.Sparse.eval row15420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15420, Integer.Sparse.eval_collectBalanced, rawRowCheck15420]

def rawRow15421 : Integer.Sparse Key := [(key2806, -1), (key2802, -1), (key2826, -1), (key2802, -1), (key2826, -1), (key2806, -1), (key2949, 2), (key2959, 2), (key2949, 2), (key2703, -1), (key2699, -1), (key2723, -1), (key2699, -1), (key2723, -1), (key2703, -1), (key2857, 2), (key2852, 2), (key2867, 2), (key2852, 2), (key2867, 2), (key2857, 2), (key2975, -1), (key2973, -1), (key2982, -1), (key2973, -1), (key2982, -1), (key2975, -1), (key2736, 2), (key2746, 2), (key2736, 2), (key2896, -1), (key2894, -1), (key2903, -1), (key2894, -1), (key2903, -1), (key2896, -1)]

theorem rawRowCheck15421 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form10 = rawRow15421 := by decide +kernel

def row15421 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

theorem rowCheck15421 : row15421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15421 := by decide +kernel

theorem rowEval15421 (x : Key → ℝ) : Integer.Sparse.eval row15421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15421, Integer.Sparse.eval_collectBalanced, rawRowCheck15421]

def rawRow15422 : Integer.Sparse Key := [(key2826, -1), (key2826, -1), (key2806, -1), (key2806, -1), (key2802, -1), (key2802, -1), (key2959, 2), (key2949, 2), (key2949, 2), (key2723, -1), (key2723, -1), (key2703, -1), (key2703, -1), (key2699, -1), (key2699, -1), (key2867, 2), (key2867, 2), (key2857, 2), (key2857, 2), (key2852, 2), (key2852, 2), (key2982, -1), (key2982, -1), (key2975, -1), (key2975, -1), (key2973, -1), (key2973, -1), (key2746, 2), (key2736, 2), (key2736, 2), (key2903, -1), (key2903, -1), (key2896, -1), (key2896, -1), (key2894, -1), (key2894, -1)]

theorem rawRowCheck15422 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form10 = rawRow15422 := by decide +kernel

def row15422 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

theorem rowCheck15422 : row15422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15422 := by decide +kernel

theorem rowEval15422 (x : Key → ℝ) : Integer.Sparse.eval row15422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15422, Integer.Sparse.eval_collectBalanced, rawRowCheck15422]

def rawRow15423 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2802, -1), (key2826, -1), (key2949, -1), (key2959, -1), (key2613, 2), (key2806, 2), (key2826, 2), (key2625, -1), (key2629, -1), (key2852, -1), (key2867, -1), (key2973, -1), (key2982, -1), (key2625, 2), (key2637, 2), (key2699, 2), (key2723, 2), (key2975, 2), (key2982, 2), (key2629, -1), (key2637, -1), (key2703, -1), (key2723, -1), (key2857, -1), (key2867, -1), (key2647, 2), (key2894, 2), (key2903, 2), (key2647, -1), (key2652, -1), (key2736, -1), (key2746, -1), (key2896, -1), (key2903, -1)]

theorem rawRowCheck15423 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form10 = rawRow15423 := by decide +kernel

def row15423 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

theorem rowCheck15423 : row15423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15423 := by decide +kernel

theorem rowEval15423 (x : Key → ℝ) : Integer.Sparse.eval row15423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15423, Integer.Sparse.eval_collectBalanced, rawRowCheck15423]

def rawRow15424 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2826, -1), (key2802, -1), (key2959, -1), (key2949, -1), (key2613, 2), (key2826, 2), (key2806, 2), (key2629, -1), (key2625, -1), (key2867, -1), (key2852, -1), (key2982, -1), (key2973, -1), (key2637, 2), (key2625, 2), (key2723, 2), (key2699, 2), (key2982, 2), (key2975, 2), (key2637, -1), (key2629, -1), (key2723, -1), (key2703, -1), (key2867, -1), (key2857, -1), (key2647, 2), (key2903, 2), (key2894, 2), (key2652, -1), (key2647, -1), (key2746, -1), (key2736, -1), (key2903, -1), (key2896, -1)]

theorem rawRowCheck15424 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form10 = rawRow15424 := by decide +kernel

def row15424 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

theorem rowCheck15424 : row15424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15424 := by decide +kernel

theorem rowEval15424 (x : Key → ℝ) : Integer.Sparse.eval row15424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15424, Integer.Sparse.eval_collectBalanced, rawRowCheck15424]

def rawRow15425 : Integer.Sparse Key := [(key2802, -1), (key2949, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2806, 2), (key2613, 2), (key2826, 2), (key2852, -1), (key2973, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2699, 2), (key2975, 2), (key2625, 2), (key2982, 2), (key2637, 2), (key2723, 2), (key2703, -1), (key2857, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2723, -1), (key2894, 2), (key2647, 2), (key2903, 2), (key2736, -1), (key2896, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2746, -1)]

theorem rawRowCheck15425 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form10 = rawRow15425 := by decide +kernel

def row15425 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

theorem rowCheck15425 : row15425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15425 := by decide +kernel

theorem rowEval15425 (x : Key → ℝ) : Integer.Sparse.eval row15425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15425, Integer.Sparse.eval_collectBalanced, rawRowCheck15425]

def rawRow15426 : Integer.Sparse Key := [(key2949, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2826, -1), (key2613, -1), (key2806, 2), (key2826, 2), (key2613, 2), (key2973, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2867, -1), (key2629, -1), (key2975, 2), (key2699, 2), (key2982, 2), (key2625, 2), (key2723, 2), (key2637, 2), (key2857, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2723, -1), (key2637, -1), (key2894, 2), (key2903, 2), (key2647, 2), (key2896, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2746, -1), (key2652, -1)]

theorem rawRowCheck15426 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form10 = rawRow15426 := by decide +kernel

def row15426 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

theorem rowCheck15426 : row15426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15426 := by decide +kernel

theorem rowEval15426 (x : Key → ℝ) : Integer.Sparse.eval row15426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15426, Integer.Sparse.eval_collectBalanced, rawRowCheck15426]

def rawRow15427 : Integer.Sparse Key := [(key2826, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2609, -1), (key2802, -1), (key2826, 2), (key2613, 2), (key2806, 2), (key2867, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2625, -1), (key2852, -1), (key2723, 2), (key2982, 2), (key2637, 2), (key2975, 2), (key2625, 2), (key2699, 2), (key2723, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2629, -1), (key2703, -1), (key2903, 2), (key2647, 2), (key2894, 2), (key2746, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2647, -1), (key2736, -1)]

theorem rawRowCheck15427 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form10 = rawRow15427 := by decide +kernel

def row15427 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

theorem rowCheck15427 : row15427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15427 := by decide +kernel

theorem rowEval15427 (x : Key → ℝ) : Integer.Sparse.eval row15427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15427, Integer.Sparse.eval_collectBalanced, rawRowCheck15427]

def rawRow15428 : Integer.Sparse Key := [(key2959, -1), (key2826, -1), (key2949, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2826, 2), (key2806, 2), (key2613, 2), (key2982, -1), (key2867, -1), (key2973, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2982, 2), (key2723, 2), (key2975, 2), (key2637, 2), (key2699, 2), (key2625, 2), (key2867, -1), (key2723, -1), (key2857, -1), (key2637, -1), (key2703, -1), (key2629, -1), (key2903, 2), (key2894, 2), (key2647, 2), (key2903, -1), (key2746, -1), (key2896, -1), (key2652, -1), (key2736, -1), (key2647, -1)]

theorem rawRowCheck15428 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form10 = rawRow15428 := by decide +kernel

def row15428 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

theorem rowCheck15428 : row15428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15428 := by decide +kernel

theorem rowEval15428 (x : Key → ℝ) : Integer.Sparse.eval row15428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15428, Integer.Sparse.eval_collectBalanced, rawRowCheck15428]

def rawRow15429 : Integer.Sparse Key := [(key2779, -1), (key2783, -1), (key2852, -1), (key2867, -1), (key2894, -1), (key2903, -1), (key2937, 2), (key2973, 2), (key2982, 2), (key2664, -1), (key2668, -1), (key2699, -1), (key2723, -1), (key2736, -1), (key2746, -1), (key2779, 2), (key2791, 2), (key2802, 2), (key2826, 2), (key2896, 2), (key2903, 2), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2975, -1), (key2982, -1), (key2668, 2), (key2703, 2), (key2723, 2), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2857, -1), (key2867, -1)]

theorem rawRowCheck15429 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form10 = rawRow15429 := by decide +kernel

def row15429 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

theorem rowCheck15429 : row15429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15429 := by decide +kernel

theorem rowEval15429 (x : Key → ℝ) : Integer.Sparse.eval row15429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15429, Integer.Sparse.eval_collectBalanced, rawRowCheck15429]

def rawRow15430 : Integer.Sparse Key := [(key2783, -1), (key2779, -1), (key2867, -1), (key2852, -1), (key2903, -1), (key2894, -1), (key2937, 2), (key2982, 2), (key2973, 2), (key2668, -1), (key2664, -1), (key2723, -1), (key2699, -1), (key2746, -1), (key2736, -1), (key2791, 2), (key2779, 2), (key2826, 2), (key2802, 2), (key2903, 2), (key2896, 2), (key2942, -1), (key2937, -1), (key2959, -1), (key2949, -1), (key2982, -1), (key2975, -1), (key2668, 2), (key2723, 2), (key2703, 2), (key2791, -1), (key2783, -1), (key2826, -1), (key2806, -1), (key2867, -1), (key2857, -1)]

theorem rawRowCheck15430 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form10 = rawRow15430 := by decide +kernel

def row15430 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

theorem rowCheck15430 : row15430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15430 := by decide +kernel

theorem rowEval15430 (x : Key → ℝ) : Integer.Sparse.eval row15430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15430, Integer.Sparse.eval_collectBalanced, rawRowCheck15430]

def rawRow15431 : Integer.Sparse Key := [(key2852, -1), (key2894, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2973, 2), (key2937, 2), (key2982, 2), (key2699, -1), (key2736, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2802, 2), (key2896, 2), (key2779, 2), (key2903, 2), (key2791, 2), (key2826, 2), (key2949, -1), (key2975, -1), (key2937, -1), (key2982, -1), (key2942, -1), (key2959, -1), (key2703, 2), (key2668, 2), (key2723, 2), (key2806, -1), (key2857, -1), (key2783, -1), (key2867, -1), (key2791, -1), (key2826, -1)]

theorem rawRowCheck15431 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form10 = rawRow15431 := by decide +kernel

def row15431 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

theorem rowCheck15431 : row15431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15431 := by decide +kernel

theorem rowEval15431 (x : Key → ℝ) : Integer.Sparse.eval row15431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15431, Integer.Sparse.eval_collectBalanced, rawRowCheck15431]

def rawRow15432 : Integer.Sparse Key := [(key2894, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2867, -1), (key2783, -1), (key2973, 2), (key2982, 2), (key2937, 2), (key2736, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2723, -1), (key2668, -1), (key2896, 2), (key2802, 2), (key2903, 2), (key2779, 2), (key2826, 2), (key2791, 2), (key2975, -1), (key2949, -1), (key2982, -1), (key2937, -1), (key2959, -1), (key2942, -1), (key2703, 2), (key2723, 2), (key2668, 2), (key2857, -1), (key2806, -1), (key2867, -1), (key2783, -1), (key2826, -1), (key2791, -1)]

theorem rawRowCheck15432 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form10 = rawRow15432 := by decide +kernel

def row15432 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

theorem rowCheck15432 : row15432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15432 := by decide +kernel

theorem rowEval15432 (x : Key → ℝ) : Integer.Sparse.eval row15432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15432, Integer.Sparse.eval_collectBalanced, rawRowCheck15432]

def rawRow15433 : Integer.Sparse Key := [(key2867, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2779, -1), (key2852, -1), (key2982, 2), (key2937, 2), (key2973, 2), (key2723, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2664, -1), (key2699, -1), (key2826, 2), (key2903, 2), (key2791, 2), (key2896, 2), (key2779, 2), (key2802, 2), (key2959, -1), (key2982, -1), (key2942, -1), (key2975, -1), (key2937, -1), (key2949, -1), (key2723, 2), (key2668, 2), (key2703, 2), (key2826, -1), (key2867, -1), (key2791, -1), (key2857, -1), (key2783, -1), (key2806, -1)]

theorem rawRowCheck15433 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form10 = rawRow15433 := by decide +kernel

def row15433 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

theorem rowCheck15433 : row15433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15433 := by decide +kernel

theorem rowEval15433 (x : Key → ℝ) : Integer.Sparse.eval row15433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15433, Integer.Sparse.eval_collectBalanced, rawRowCheck15433]

def rawRow15434 : Integer.Sparse Key := [(key2903, -1), (key2867, -1), (key2894, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2982, 2), (key2973, 2), (key2937, 2), (key2746, -1), (key2723, -1), (key2736, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2903, 2), (key2826, 2), (key2896, 2), (key2791, 2), (key2802, 2), (key2779, 2), (key2982, -1), (key2959, -1), (key2975, -1), (key2942, -1), (key2949, -1), (key2937, -1), (key2723, 2), (key2703, 2), (key2668, 2), (key2867, -1), (key2826, -1), (key2857, -1), (key2791, -1), (key2806, -1), (key2783, -1)]

theorem rawRowCheck15434 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form10 = rawRow15434 := by decide +kernel

def row15434 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

theorem rowCheck15434 : row15434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15434 := by decide +kernel

theorem rowEval15434 (x : Key → ℝ) : Integer.Sparse.eval row15434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15434, Integer.Sparse.eval_collectBalanced, rawRowCheck15434]

def rawRow15435 : Integer.Sparse Key := [(key2625, -1), (key2629, -1), (key2852, -1), (key2867, -1), (key2973, -1), (key2982, -1), (key2647, 2), (key2894, 2), (key2903, 2), (key2609, -1), (key2613, -1), (key2802, -1), (key2826, -1), (key2949, -1), (key2959, -1), (key2625, 2), (key2637, 2), (key2699, 2), (key2723, 2), (key2975, 2), (key2982, 2), (key2647, -1), (key2652, -1), (key2736, -1), (key2746, -1), (key2896, -1), (key2903, -1), (key2613, 2), (key2806, 2), (key2826, 2), (key2629, -1), (key2637, -1), (key2703, -1), (key2723, -1), (key2857, -1), (key2867, -1)]

theorem rawRowCheck15435 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form10 = rawRow15435 := by decide +kernel

def row15435 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

theorem rowCheck15435 : row15435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15435 := by decide +kernel

theorem rowEval15435 (x : Key → ℝ) : Integer.Sparse.eval row15435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15435, Integer.Sparse.eval_collectBalanced, rawRowCheck15435]

def rawRow15436 : Integer.Sparse Key := [(key2629, -1), (key2625, -1), (key2867, -1), (key2852, -1), (key2982, -1), (key2973, -1), (key2647, 2), (key2903, 2), (key2894, 2), (key2613, -1), (key2609, -1), (key2826, -1), (key2802, -1), (key2959, -1), (key2949, -1), (key2637, 2), (key2625, 2), (key2723, 2), (key2699, 2), (key2982, 2), (key2975, 2), (key2652, -1), (key2647, -1), (key2746, -1), (key2736, -1), (key2903, -1), (key2896, -1), (key2613, 2), (key2826, 2), (key2806, 2), (key2637, -1), (key2629, -1), (key2723, -1), (key2703, -1), (key2867, -1), (key2857, -1)]

theorem rawRowCheck15436 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form10 = rawRow15436 := by decide +kernel

def row15436 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

theorem rowCheck15436 : row15436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15436 := by decide +kernel

theorem rowEval15436 (x : Key → ℝ) : Integer.Sparse.eval row15436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15436, Integer.Sparse.eval_collectBalanced, rawRowCheck15436]

def rawRow15437 : Integer.Sparse Key := [(key2852, -1), (key2973, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2894, 2), (key2647, 2), (key2903, 2), (key2802, -1), (key2949, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2699, 2), (key2975, 2), (key2625, 2), (key2982, 2), (key2637, 2), (key2723, 2), (key2736, -1), (key2896, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2746, -1), (key2806, 2), (key2613, 2), (key2826, 2), (key2703, -1), (key2857, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2723, -1)]

theorem rawRowCheck15437 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form10 = rawRow15437 := by decide +kernel

def row15437 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

theorem rowCheck15437 : row15437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15437 := by decide +kernel

theorem rowEval15437 (x : Key → ℝ) : Integer.Sparse.eval row15437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15437, Integer.Sparse.eval_collectBalanced, rawRowCheck15437]

def rawRow15438 : Integer.Sparse Key := [(key2973, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2867, -1), (key2629, -1), (key2894, 2), (key2903, 2), (key2647, 2), (key2949, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2826, -1), (key2613, -1), (key2975, 2), (key2699, 2), (key2982, 2), (key2625, 2), (key2723, 2), (key2637, 2), (key2896, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2746, -1), (key2652, -1), (key2806, 2), (key2826, 2), (key2613, 2), (key2857, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2723, -1), (key2637, -1)]

theorem rawRowCheck15438 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form10 = rawRow15438 := by decide +kernel

def row15438 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

theorem rowCheck15438 : row15438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15438 := by decide +kernel

theorem rowEval15438 (x : Key → ℝ) : Integer.Sparse.eval row15438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15438, Integer.Sparse.eval_collectBalanced, rawRowCheck15438]

def rawRow15439 : Integer.Sparse Key := [(key2867, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2625, -1), (key2852, -1), (key2903, 2), (key2647, 2), (key2894, 2), (key2826, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2609, -1), (key2802, -1), (key2723, 2), (key2982, 2), (key2637, 2), (key2975, 2), (key2625, 2), (key2699, 2), (key2746, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2647, -1), (key2736, -1), (key2826, 2), (key2613, 2), (key2806, 2), (key2723, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2629, -1), (key2703, -1)]

theorem rawRowCheck15439 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form10 = rawRow15439 := by decide +kernel

def row15439 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

theorem rowCheck15439 : row15439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15439 := by decide +kernel

theorem rowEval15439 (x : Key → ℝ) : Integer.Sparse.eval row15439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15439, Integer.Sparse.eval_collectBalanced, rawRowCheck15439]

def rawRow15440 : Integer.Sparse Key := [(key2982, -1), (key2867, -1), (key2973, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2903, 2), (key2894, 2), (key2647, 2), (key2959, -1), (key2826, -1), (key2949, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2982, 2), (key2723, 2), (key2975, 2), (key2637, 2), (key2699, 2), (key2625, 2), (key2903, -1), (key2746, -1), (key2896, -1), (key2652, -1), (key2736, -1), (key2647, -1), (key2826, 2), (key2806, 2), (key2613, 2), (key2867, -1), (key2723, -1), (key2857, -1), (key2637, -1), (key2703, -1), (key2629, -1)]

theorem rawRowCheck15440 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form10 = rawRow15440 := by decide +kernel

def row15440 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

theorem rowCheck15440 : row15440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15440 := by decide +kernel

theorem rowEval15440 (x : Key → ℝ) : Integer.Sparse.eval row15440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15440, Integer.Sparse.eval_collectBalanced, rawRowCheck15440]

def rawRow15441 : Integer.Sparse Key := [(key2625, -1), (key2647, -1), (key2779, -1), (key2903, -1), (key2937, -1), (key2982, -1), (key2629, 2), (key2783, 2), (key2867, 2), (key2625, -1), (key2647, -1), (key2779, -1), (key2903, -1), (key2937, -1), (key2982, -1), (key2609, 2), (key2652, 2), (key2664, 2), (key2746, 2), (key2942, 2), (key2959, 2), (key2613, -1), (key2637, -1), (key2668, -1), (key2723, -1), (key2791, -1), (key2826, -1), (key2629, 2), (key2783, 2), (key2867, 2), (key2613, -1), (key2637, -1), (key2668, -1), (key2723, -1), (key2791, -1), (key2826, -1)]

theorem rawRowCheck15441 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form10 = rawRow15441 := by decide +kernel

def row15441 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

theorem rowCheck15441 : row15441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15441 := by decide +kernel

theorem rowEval15441 (x : Key → ℝ) : Integer.Sparse.eval row15441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15441, Integer.Sparse.eval_collectBalanced, rawRowCheck15441]

def rawRow15442 : Integer.Sparse Key := [(key2647, -1), (key2625, -1), (key2903, -1), (key2779, -1), (key2982, -1), (key2937, -1), (key2629, 2), (key2867, 2), (key2783, 2), (key2647, -1), (key2625, -1), (key2903, -1), (key2779, -1), (key2982, -1), (key2937, -1), (key2652, 2), (key2609, 2), (key2746, 2), (key2664, 2), (key2959, 2), (key2942, 2), (key2637, -1), (key2613, -1), (key2723, -1), (key2668, -1), (key2826, -1), (key2791, -1), (key2629, 2), (key2867, 2), (key2783, 2), (key2637, -1), (key2613, -1), (key2723, -1), (key2668, -1), (key2826, -1), (key2791, -1)]

theorem rawRowCheck15442 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form10 = rawRow15442 := by decide +kernel

def row15442 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

theorem rowCheck15442 : row15442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15442 := by decide +kernel

theorem rowEval15442 (x : Key → ℝ) : Integer.Sparse.eval row15442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15442, Integer.Sparse.eval_collectBalanced, rawRowCheck15442]

def rawRow15443 : Integer.Sparse Key := [(key2779, -1), (key2937, -1), (key2625, -1), (key2982, -1), (key2647, -1), (key2903, -1), (key2783, 2), (key2629, 2), (key2867, 2), (key2779, -1), (key2937, -1), (key2625, -1), (key2982, -1), (key2647, -1), (key2903, -1), (key2664, 2), (key2942, 2), (key2609, 2), (key2959, 2), (key2652, 2), (key2746, 2), (key2668, -1), (key2791, -1), (key2613, -1), (key2826, -1), (key2637, -1), (key2723, -1), (key2783, 2), (key2629, 2), (key2867, 2), (key2668, -1), (key2791, -1), (key2613, -1), (key2826, -1), (key2637, -1), (key2723, -1)]

theorem rawRowCheck15443 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form10 = rawRow15443 := by decide +kernel

def row15443 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

theorem rowCheck15443 : row15443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15443 := by decide +kernel

theorem rowEval15443 (x : Key → ℝ) : Integer.Sparse.eval row15443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15443, Integer.Sparse.eval_collectBalanced, rawRowCheck15443]

def rawRow15444 : Integer.Sparse Key := [(key2937, -1), (key2779, -1), (key2982, -1), (key2625, -1), (key2903, -1), (key2647, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2937, -1), (key2779, -1), (key2982, -1), (key2625, -1), (key2903, -1), (key2647, -1), (key2942, 2), (key2664, 2), (key2959, 2), (key2609, 2), (key2746, 2), (key2652, 2), (key2791, -1), (key2668, -1), (key2826, -1), (key2613, -1), (key2723, -1), (key2637, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2791, -1), (key2668, -1), (key2826, -1), (key2613, -1), (key2723, -1), (key2637, -1)]

theorem rawRowCheck15444 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form10 = rawRow15444 := by decide +kernel

def row15444 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

theorem rowCheck15444 : row15444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15444 := by decide +kernel

theorem rowEval15444 (x : Key → ℝ) : Integer.Sparse.eval row15444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15444, Integer.Sparse.eval_collectBalanced, rawRowCheck15444]

def rawRow15445 : Integer.Sparse Key := [(key2903, -1), (key2982, -1), (key2647, -1), (key2937, -1), (key2625, -1), (key2779, -1), (key2867, 2), (key2629, 2), (key2783, 2), (key2903, -1), (key2982, -1), (key2647, -1), (key2937, -1), (key2625, -1), (key2779, -1), (key2746, 2), (key2959, 2), (key2652, 2), (key2942, 2), (key2609, 2), (key2664, 2), (key2723, -1), (key2826, -1), (key2637, -1), (key2791, -1), (key2613, -1), (key2668, -1), (key2867, 2), (key2629, 2), (key2783, 2), (key2723, -1), (key2826, -1), (key2637, -1), (key2791, -1), (key2613, -1), (key2668, -1)]

theorem rawRowCheck15445 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form10 = rawRow15445 := by decide +kernel

def row15445 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

theorem rowCheck15445 : row15445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15445 := by decide +kernel

theorem rowEval15445 (x : Key → ℝ) : Integer.Sparse.eval row15445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15445, Integer.Sparse.eval_collectBalanced, rawRowCheck15445]

def rawRow15446 : Integer.Sparse Key := [(key2982, -1), (key2903, -1), (key2937, -1), (key2647, -1), (key2779, -1), (key2625, -1), (key2867, 2), (key2783, 2), (key2629, 2), (key2982, -1), (key2903, -1), (key2937, -1), (key2647, -1), (key2779, -1), (key2625, -1), (key2959, 2), (key2746, 2), (key2942, 2), (key2652, 2), (key2664, 2), (key2609, 2), (key2826, -1), (key2723, -1), (key2791, -1), (key2637, -1), (key2668, -1), (key2613, -1), (key2867, 2), (key2783, 2), (key2629, 2), (key2826, -1), (key2723, -1), (key2791, -1), (key2637, -1), (key2668, -1), (key2613, -1)]

theorem rawRowCheck15446 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form10 = rawRow15446 := by decide +kernel

def row15446 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

theorem rowCheck15446 : row15446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15446 := by decide +kernel

theorem rowEval15446 (x : Key → ℝ) : Integer.Sparse.eval row15446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15446, Integer.Sparse.eval_collectBalanced, rawRowCheck15446]

def rawRow15447 : Integer.Sparse Key := [(key1358, -2), (key1364, -2), (key1364, -2), (key1374, 6), (key1484, -2), (key1490, -2), (key1490, -2), (key1710, 2), (key1716, 2), (key1710, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1723, -2), (key1723, -2), (key1940, -2), (key1513, 6), (key1741, -2), (key1741, -2), (key1949, -2)]

theorem rawRowCheck15447 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form11 = rawRow15447 := by decide +kernel

def row15447 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

theorem rowCheck15447 : row15447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15447 := by decide +kernel

theorem rowEval15447 (x : Key → ℝ) : Integer.Sparse.eval row15447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15447, Integer.Sparse.eval_collectBalanced, rawRowCheck15447]

def rawRow15448 : Integer.Sparse Key := [(key1364, -2), (key1358, -2), (key1364, -2), (key1374, 6), (key1490, -2), (key1484, -2), (key1490, -2), (key1716, 2), (key1710, 2), (key1937, 2), (key1710, 2), (key1937, 2), (key1716, 2), (key1723, -2), (key1940, -2), (key1723, -2), (key1513, 6), (key1741, -2), (key1949, -2), (key1741, -2)]

theorem rawRowCheck15448 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form11 = rawRow15448 := by decide +kernel

def row15448 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

theorem rowCheck15448 : row15448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15448 := by decide +kernel

theorem rowEval15448 (x : Key → ℝ) : Integer.Sparse.eval row15448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15448, Integer.Sparse.eval_collectBalanced, rawRowCheck15448]

def rawRow15449 : Integer.Sparse Key := [(key1364, -2), (key1364, -2), (key1358, -2), (key1374, 6), (key1490, -2), (key1490, -2), (key1484, -2), (key1937, 2), (key1937, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1940, -2), (key1723, -2), (key1723, -2), (key1513, 6), (key1949, -2), (key1741, -2), (key1741, -2)]

theorem rawRowCheck15449 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form11 = rawRow15449 := by decide +kernel

def row15449 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

theorem rowCheck15449 : row15449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15449 := by decide +kernel

theorem rowEval15449 (x : Key → ℝ) : Integer.Sparse.eval row15449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15449, Integer.Sparse.eval_collectBalanced, rawRowCheck15449]

def rawRow15450 : Integer.Sparse Key := [(key1358, -2), (key1364, -2), (key1374, -2), (key1364, 6), (key1710, -2), (key1716, -2), (key1723, -2), (key1484, 2), (key1490, 2), (key1710, 2), (key1937, 2), (key1723, 2), (key1940, 2), (key1490, -2), (key1716, -2), (key1937, -2), (key1741, 6), (key1513, -2), (key1741, -2), (key1949, -2)]

theorem rawRowCheck15450 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form11 = rawRow15450 := by decide +kernel

def row15450 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

theorem rowCheck15450 : row15450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15450 := by decide +kernel

theorem rowEval15450 (x : Key → ℝ) : Integer.Sparse.eval row15450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15450, Integer.Sparse.eval_collectBalanced, rawRowCheck15450]

def rawRow15451 : Integer.Sparse Key := [(key1364, -2), (key1358, -2), (key1374, -2), (key1364, 6), (key1716, -2), (key1710, -2), (key1723, -2), (key1490, 2), (key1484, 2), (key1937, 2), (key1710, 2), (key1940, 2), (key1723, 2), (key1490, -2), (key1937, -2), (key1716, -2), (key1741, 6), (key1513, -2), (key1949, -2), (key1741, -2)]

theorem rawRowCheck15451 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form11 = rawRow15451 := by decide +kernel

def row15451 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

theorem rowCheck15451 : row15451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15451 := by decide +kernel

theorem rowEval15451 (x : Key → ℝ) : Integer.Sparse.eval row15451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15451, Integer.Sparse.eval_collectBalanced, rawRowCheck15451]

def rawRow15452 : Integer.Sparse Key := [(key1358, -2), (key1374, -2), (key1364, -2), (key1364, 6), (key1710, -2), (key1723, -2), (key1716, -2), (key1710, 2), (key1723, 2), (key1484, 2), (key1940, 2), (key1490, 2), (key1937, 2), (key1716, -2), (key1490, -2), (key1937, -2), (key1741, 6), (key1741, -2), (key1513, -2), (key1949, -2)]

theorem rawRowCheck15452 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form11 = rawRow15452 := by decide +kernel

def row15452 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

theorem rowCheck15452 : row15452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15452 := by decide +kernel

theorem rowEval15452 (x : Key → ℝ) : Integer.Sparse.eval row15452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15452, Integer.Sparse.eval_collectBalanced, rawRowCheck15452]

def rawRow15453 : Integer.Sparse Key := [(key1374, -2), (key1358, -2), (key1364, -2), (key1364, 6), (key1723, -2), (key1710, -2), (key1716, -2), (key1723, 2), (key1710, 2), (key1940, 2), (key1484, 2), (key1937, 2), (key1490, 2), (key1716, -2), (key1937, -2), (key1490, -2), (key1741, 6), (key1741, -2), (key1949, -2), (key1513, -2)]

theorem rawRowCheck15453 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form11 = rawRow15453 := by decide +kernel

def row15453 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

theorem rowCheck15453 : row15453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15453 := by decide +kernel

theorem rowEval15453 (x : Key → ℝ) : Integer.Sparse.eval row15453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15453, Integer.Sparse.eval_collectBalanced, rawRowCheck15453]

def rawRow15454 : Integer.Sparse Key := [(key1364, -2), (key1374, -2), (key1358, -2), (key1364, 6), (key1716, -2), (key1723, -2), (key1710, -2), (key1937, 2), (key1940, 2), (key1490, 2), (key1723, 2), (key1484, 2), (key1710, 2), (key1937, -2), (key1490, -2), (key1716, -2), (key1741, 6), (key1949, -2), (key1513, -2), (key1741, -2)]

theorem rawRowCheck15454 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form11 = rawRow15454 := by decide +kernel

def row15454 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

theorem rowCheck15454 : row15454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15454 := by decide +kernel

theorem rowEval15454 (x : Key → ℝ) : Integer.Sparse.eval row15454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15454, Integer.Sparse.eval_collectBalanced, rawRowCheck15454]

def rawRow15455 : Integer.Sparse Key := [(key1374, -2), (key1364, -2), (key1358, -2), (key1364, 6), (key1723, -2), (key1716, -2), (key1710, -2), (key1940, 2), (key1937, 2), (key1723, 2), (key1490, 2), (key1710, 2), (key1484, 2), (key1937, -2), (key1716, -2), (key1490, -2), (key1741, 6), (key1949, -2), (key1741, -2), (key1513, -2)]

theorem rawRowCheck15455 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form11 = rawRow15455 := by decide +kernel

def row15455 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

theorem rowCheck15455 : row15455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15455 := by decide +kernel

theorem rowEval15455 (x : Key → ℝ) : Integer.Sparse.eval row15455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15455, Integer.Sparse.eval_collectBalanced, rawRowCheck15455]

def rawRow15456 : Integer.Sparse Key := [(key1484, -2), (key1490, -2), (key1490, -2), (key1513, 6), (key1358, -2), (key1364, -2), (key1364, -2), (key1710, 2), (key1716, 2), (key1710, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1741, -2), (key1741, -2), (key1949, -2), (key1374, 6), (key1723, -2), (key1723, -2), (key1940, -2)]

theorem rawRowCheck15456 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form11 = rawRow15456 := by decide +kernel

def row15456 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

theorem rowCheck15456 : row15456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15456 := by decide +kernel

theorem rowEval15456 (x : Key → ℝ) : Integer.Sparse.eval row15456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15456, Integer.Sparse.eval_collectBalanced, rawRowCheck15456]

def rawRow15457 : Integer.Sparse Key := [(key1490, -2), (key1484, -2), (key1490, -2), (key1513, 6), (key1364, -2), (key1358, -2), (key1364, -2), (key1716, 2), (key1710, 2), (key1937, 2), (key1710, 2), (key1937, 2), (key1716, 2), (key1741, -2), (key1949, -2), (key1741, -2), (key1374, 6), (key1723, -2), (key1940, -2), (key1723, -2)]

theorem rawRowCheck15457 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form11 = rawRow15457 := by decide +kernel

def row15457 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

theorem rowCheck15457 : row15457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15457 := by decide +kernel

theorem rowEval15457 (x : Key → ℝ) : Integer.Sparse.eval row15457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15457, Integer.Sparse.eval_collectBalanced, rawRowCheck15457]

def rawRow15458 : Integer.Sparse Key := [(key1490, -2), (key1490, -2), (key1484, -2), (key1513, 6), (key1364, -2), (key1364, -2), (key1358, -2), (key1937, 2), (key1937, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1949, -2), (key1741, -2), (key1741, -2), (key1374, 6), (key1940, -2), (key1723, -2), (key1723, -2)]

theorem rawRowCheck15458 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form11 = rawRow15458 := by decide +kernel

def row15458 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

theorem rowCheck15458 : row15458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15458 := by decide +kernel

theorem rowEval15458 (x : Key → ℝ) : Integer.Sparse.eval row15458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15458, Integer.Sparse.eval_collectBalanced, rawRowCheck15458]

def rawRow15459 : Integer.Sparse Key := [(key1484, -2), (key1490, -2), (key1513, -2), (key1490, 6), (key1710, -2), (key1716, -2), (key1741, -2), (key1358, 2), (key1364, 2), (key1710, 2), (key1937, 2), (key1741, 2), (key1949, 2), (key1364, -2), (key1716, -2), (key1937, -2), (key1723, 6), (key1374, -2), (key1723, -2), (key1940, -2)]

theorem rawRowCheck15459 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form11 = rawRow15459 := by decide +kernel

def row15459 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

theorem rowCheck15459 : row15459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15459 := by decide +kernel

theorem rowEval15459 (x : Key → ℝ) : Integer.Sparse.eval row15459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15459, Integer.Sparse.eval_collectBalanced, rawRowCheck15459]

def rawRow15460 : Integer.Sparse Key := [(key1490, -2), (key1484, -2), (key1513, -2), (key1490, 6), (key1716, -2), (key1710, -2), (key1741, -2), (key1364, 2), (key1358, 2), (key1937, 2), (key1710, 2), (key1949, 2), (key1741, 2), (key1364, -2), (key1937, -2), (key1716, -2), (key1723, 6), (key1374, -2), (key1940, -2), (key1723, -2)]

theorem rawRowCheck15460 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form11 = rawRow15460 := by decide +kernel

def row15460 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

theorem rowCheck15460 : row15460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15460 := by decide +kernel

theorem rowEval15460 (x : Key → ℝ) : Integer.Sparse.eval row15460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15460, Integer.Sparse.eval_collectBalanced, rawRowCheck15460]

def rawRow15461 : Integer.Sparse Key := [(key1484, -2), (key1513, -2), (key1490, -2), (key1490, 6), (key1710, -2), (key1741, -2), (key1716, -2), (key1710, 2), (key1741, 2), (key1358, 2), (key1949, 2), (key1364, 2), (key1937, 2), (key1716, -2), (key1364, -2), (key1937, -2), (key1723, 6), (key1723, -2), (key1374, -2), (key1940, -2)]

theorem rawRowCheck15461 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form11 = rawRow15461 := by decide +kernel

def row15461 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

theorem rowCheck15461 : row15461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15461 := by decide +kernel

theorem rowEval15461 (x : Key → ℝ) : Integer.Sparse.eval row15461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15461, Integer.Sparse.eval_collectBalanced, rawRowCheck15461]

def rawRow15462 : Integer.Sparse Key := [(key1513, -2), (key1484, -2), (key1490, -2), (key1490, 6), (key1741, -2), (key1710, -2), (key1716, -2), (key1741, 2), (key1710, 2), (key1949, 2), (key1358, 2), (key1937, 2), (key1364, 2), (key1716, -2), (key1937, -2), (key1364, -2), (key1723, 6), (key1723, -2), (key1940, -2), (key1374, -2)]

theorem rawRowCheck15462 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form11 = rawRow15462 := by decide +kernel

def row15462 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

theorem rowCheck15462 : row15462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15462 := by decide +kernel

theorem rowEval15462 (x : Key → ℝ) : Integer.Sparse.eval row15462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15462, Integer.Sparse.eval_collectBalanced, rawRowCheck15462]

def rawRow15463 : Integer.Sparse Key := [(key1490, -2), (key1513, -2), (key1484, -2), (key1490, 6), (key1716, -2), (key1741, -2), (key1710, -2), (key1937, 2), (key1949, 2), (key1364, 2), (key1741, 2), (key1358, 2), (key1710, 2), (key1937, -2), (key1364, -2), (key1716, -2), (key1723, 6), (key1940, -2), (key1374, -2), (key1723, -2)]

theorem rawRowCheck15463 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form11 = rawRow15463 := by decide +kernel

def row15463 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

theorem rowCheck15463 : row15463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15463 := by decide +kernel

theorem rowEval15463 (x : Key → ℝ) : Integer.Sparse.eval row15463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15463, Integer.Sparse.eval_collectBalanced, rawRowCheck15463]

def rawRow15464 : Integer.Sparse Key := [(key1513, -2), (key1490, -2), (key1484, -2), (key1490, 6), (key1741, -2), (key1716, -2), (key1710, -2), (key1949, 2), (key1937, 2), (key1741, 2), (key1364, 2), (key1710, 2), (key1358, 2), (key1937, -2), (key1716, -2), (key1364, -2), (key1723, 6), (key1940, -2), (key1723, -2), (key1374, -2)]

theorem rawRowCheck15464 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form11 = rawRow15464 := by decide +kernel

def row15464 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

theorem rowCheck15464 : row15464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15464 := by decide +kernel

theorem rowEval15464 (x : Key → ℝ) : Integer.Sparse.eval row15464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15464, Integer.Sparse.eval_collectBalanced, rawRowCheck15464]

def rawRow15465 : Integer.Sparse Key := [(key1710, -2), (key1716, -2), (key1723, -2), (key1741, 6), (key1358, -2), (key1364, -2), (key1374, -2), (key1484, 2), (key1490, 2), (key1710, 2), (key1937, 2), (key1723, 2), (key1940, 2), (key1513, -2), (key1741, -2), (key1949, -2), (key1364, 6), (key1490, -2), (key1716, -2), (key1937, -2)]

theorem rawRowCheck15465 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form11 = rawRow15465 := by decide +kernel

def row15465 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

theorem rowCheck15465 : row15465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15465 := by decide +kernel

theorem rowEval15465 (x : Key → ℝ) : Integer.Sparse.eval row15465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15465, Integer.Sparse.eval_collectBalanced, rawRowCheck15465]

def rawRow15466 : Integer.Sparse Key := [(key1716, -2), (key1710, -2), (key1723, -2), (key1741, 6), (key1364, -2), (key1358, -2), (key1374, -2), (key1490, 2), (key1484, 2), (key1937, 2), (key1710, 2), (key1940, 2), (key1723, 2), (key1513, -2), (key1949, -2), (key1741, -2), (key1364, 6), (key1490, -2), (key1937, -2), (key1716, -2)]

theorem rawRowCheck15466 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form11 = rawRow15466 := by decide +kernel

def row15466 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

theorem rowCheck15466 : row15466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15466 := by decide +kernel

theorem rowEval15466 (x : Key → ℝ) : Integer.Sparse.eval row15466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15466, Integer.Sparse.eval_collectBalanced, rawRowCheck15466]

def rawRow15467 : Integer.Sparse Key := [(key1710, -2), (key1723, -2), (key1716, -2), (key1741, 6), (key1358, -2), (key1374, -2), (key1364, -2), (key1710, 2), (key1723, 2), (key1484, 2), (key1940, 2), (key1490, 2), (key1937, 2), (key1741, -2), (key1513, -2), (key1949, -2), (key1364, 6), (key1716, -2), (key1490, -2), (key1937, -2)]

theorem rawRowCheck15467 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form11 = rawRow15467 := by decide +kernel

def row15467 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

theorem rowCheck15467 : row15467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15467 := by decide +kernel

theorem rowEval15467 (x : Key → ℝ) : Integer.Sparse.eval row15467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15467, Integer.Sparse.eval_collectBalanced, rawRowCheck15467]

def rawRow15468 : Integer.Sparse Key := [(key1723, -2), (key1710, -2), (key1716, -2), (key1741, 6), (key1374, -2), (key1358, -2), (key1364, -2), (key1723, 2), (key1710, 2), (key1940, 2), (key1484, 2), (key1937, 2), (key1490, 2), (key1741, -2), (key1949, -2), (key1513, -2), (key1364, 6), (key1716, -2), (key1937, -2), (key1490, -2)]

theorem rawRowCheck15468 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form11 = rawRow15468 := by decide +kernel

def row15468 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

theorem rowCheck15468 : row15468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15468 := by decide +kernel

theorem rowEval15468 (x : Key → ℝ) : Integer.Sparse.eval row15468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15468, Integer.Sparse.eval_collectBalanced, rawRowCheck15468]

def rawRow15469 : Integer.Sparse Key := [(key1716, -2), (key1723, -2), (key1710, -2), (key1741, 6), (key1364, -2), (key1374, -2), (key1358, -2), (key1937, 2), (key1940, 2), (key1490, 2), (key1723, 2), (key1484, 2), (key1710, 2), (key1949, -2), (key1513, -2), (key1741, -2), (key1364, 6), (key1937, -2), (key1490, -2), (key1716, -2)]

theorem rawRowCheck15469 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form11 = rawRow15469 := by decide +kernel

def row15469 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

theorem rowCheck15469 : row15469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15469 := by decide +kernel

theorem rowEval15469 (x : Key → ℝ) : Integer.Sparse.eval row15469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15469, Integer.Sparse.eval_collectBalanced, rawRowCheck15469]

def rawRow15470 : Integer.Sparse Key := [(key1723, -2), (key1716, -2), (key1710, -2), (key1741, 6), (key1374, -2), (key1364, -2), (key1358, -2), (key1940, 2), (key1937, 2), (key1723, 2), (key1490, 2), (key1710, 2), (key1484, 2), (key1949, -2), (key1741, -2), (key1513, -2), (key1364, 6), (key1937, -2), (key1716, -2), (key1490, -2)]

theorem rawRowCheck15470 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form11 = rawRow15470 := by decide +kernel

def row15470 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

theorem rowCheck15470 : row15470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15470 := by decide +kernel

theorem rowEval15470 (x : Key → ℝ) : Integer.Sparse.eval row15470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15470, Integer.Sparse.eval_collectBalanced, rawRowCheck15470]

def rawRow15471 : Integer.Sparse Key := [(key1710, -2), (key1716, -2), (key1741, -2), (key1723, 6), (key1484, -2), (key1490, -2), (key1513, -2), (key1358, 2), (key1364, 2), (key1710, 2), (key1937, 2), (key1741, 2), (key1949, 2), (key1374, -2), (key1723, -2), (key1940, -2), (key1490, 6), (key1364, -2), (key1716, -2), (key1937, -2)]

theorem rawRowCheck15471 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form11 = rawRow15471 := by decide +kernel

def row15471 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

theorem rowCheck15471 : row15471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15471 := by decide +kernel

theorem rowEval15471 (x : Key → ℝ) : Integer.Sparse.eval row15471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15471, Integer.Sparse.eval_collectBalanced, rawRowCheck15471]

def rawRow15472 : Integer.Sparse Key := [(key1716, -2), (key1710, -2), (key1741, -2), (key1723, 6), (key1490, -2), (key1484, -2), (key1513, -2), (key1364, 2), (key1358, 2), (key1937, 2), (key1710, 2), (key1949, 2), (key1741, 2), (key1374, -2), (key1940, -2), (key1723, -2), (key1490, 6), (key1364, -2), (key1937, -2), (key1716, -2)]

theorem rawRowCheck15472 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form11 = rawRow15472 := by decide +kernel

def row15472 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

theorem rowCheck15472 : row15472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15472 := by decide +kernel

theorem rowEval15472 (x : Key → ℝ) : Integer.Sparse.eval row15472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15472, Integer.Sparse.eval_collectBalanced, rawRowCheck15472]

def rawRow15473 : Integer.Sparse Key := [(key1710, -2), (key1741, -2), (key1716, -2), (key1723, 6), (key1484, -2), (key1513, -2), (key1490, -2), (key1710, 2), (key1741, 2), (key1358, 2), (key1949, 2), (key1364, 2), (key1937, 2), (key1723, -2), (key1374, -2), (key1940, -2), (key1490, 6), (key1716, -2), (key1364, -2), (key1937, -2)]

theorem rawRowCheck15473 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form11 = rawRow15473 := by decide +kernel

def row15473 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

theorem rowCheck15473 : row15473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15473 := by decide +kernel

theorem rowEval15473 (x : Key → ℝ) : Integer.Sparse.eval row15473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15473, Integer.Sparse.eval_collectBalanced, rawRowCheck15473]

def rawRow15474 : Integer.Sparse Key := [(key1741, -2), (key1710, -2), (key1716, -2), (key1723, 6), (key1513, -2), (key1484, -2), (key1490, -2), (key1741, 2), (key1710, 2), (key1949, 2), (key1358, 2), (key1937, 2), (key1364, 2), (key1723, -2), (key1940, -2), (key1374, -2), (key1490, 6), (key1716, -2), (key1937, -2), (key1364, -2)]

theorem rawRowCheck15474 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form11 = rawRow15474 := by decide +kernel

def row15474 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

theorem rowCheck15474 : row15474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15474 := by decide +kernel

theorem rowEval15474 (x : Key → ℝ) : Integer.Sparse.eval row15474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15474, Integer.Sparse.eval_collectBalanced, rawRowCheck15474]

def rawRow15475 : Integer.Sparse Key := [(key1716, -2), (key1741, -2), (key1710, -2), (key1723, 6), (key1490, -2), (key1513, -2), (key1484, -2), (key1937, 2), (key1949, 2), (key1364, 2), (key1741, 2), (key1358, 2), (key1710, 2), (key1940, -2), (key1374, -2), (key1723, -2), (key1490, 6), (key1937, -2), (key1364, -2), (key1716, -2)]

theorem rawRowCheck15475 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form11 = rawRow15475 := by decide +kernel

def row15475 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

theorem rowCheck15475 : row15475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15475 := by decide +kernel

theorem rowEval15475 (x : Key → ℝ) : Integer.Sparse.eval row15475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15475, Integer.Sparse.eval_collectBalanced, rawRowCheck15475]

def rawRow15476 : Integer.Sparse Key := [(key1741, -2), (key1716, -2), (key1710, -2), (key1723, 6), (key1513, -2), (key1490, -2), (key1484, -2), (key1949, 2), (key1937, 2), (key1741, 2), (key1364, 2), (key1710, 2), (key1358, 2), (key1940, -2), (key1723, -2), (key1374, -2), (key1490, 6), (key1937, -2), (key1716, -2), (key1364, -2)]

theorem rawRowCheck15476 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form11 = rawRow15476 := by decide +kernel

def row15476 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

theorem rowCheck15476 : row15476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15476 := by decide +kernel

theorem rowEval15476 (x : Key → ℝ) : Integer.Sparse.eval row15476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15476, Integer.Sparse.eval_collectBalanced, rawRowCheck15476]

def rawRow15477 : Integer.Sparse Key := [(key1710, -2), (key1723, -2), (key1741, -2), (key1716, 6), (key1710, -2), (key1723, -2), (key1741, -2), (key1358, 2), (key1374, 2), (key1484, 2), (key1940, 2), (key1513, 2), (key1949, 2), (key1364, -2), (key1490, -2), (key1937, -2), (key1716, 6), (key1364, -2), (key1490, -2), (key1937, -2)]

theorem rawRowCheck15477 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form11 = rawRow15477 := by decide +kernel

def row15477 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

theorem rowCheck15477 : row15477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15477 := by decide +kernel

theorem rowEval15477 (x : Key → ℝ) : Integer.Sparse.eval row15477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15477, Integer.Sparse.eval_collectBalanced, rawRowCheck15477]

def rawRow15478 : Integer.Sparse Key := [(key1723, -2), (key1710, -2), (key1741, -2), (key1716, 6), (key1723, -2), (key1710, -2), (key1741, -2), (key1374, 2), (key1358, 2), (key1940, 2), (key1484, 2), (key1949, 2), (key1513, 2), (key1364, -2), (key1937, -2), (key1490, -2), (key1716, 6), (key1364, -2), (key1937, -2), (key1490, -2)]

theorem rawRowCheck15478 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form11 = rawRow15478 := by decide +kernel

def row15478 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

theorem rowCheck15478 : row15478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15478 := by decide +kernel

theorem rowEval15478 (x : Key → ℝ) : Integer.Sparse.eval row15478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15478, Integer.Sparse.eval_collectBalanced, rawRowCheck15478]

def rawRow15479 : Integer.Sparse Key := [(key1710, -2), (key1741, -2), (key1723, -2), (key1716, 6), (key1710, -2), (key1741, -2), (key1723, -2), (key1484, 2), (key1513, 2), (key1358, 2), (key1949, 2), (key1374, 2), (key1940, 2), (key1490, -2), (key1364, -2), (key1937, -2), (key1716, 6), (key1490, -2), (key1364, -2), (key1937, -2)]

theorem rawRowCheck15479 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form11 = rawRow15479 := by decide +kernel

def row15479 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

theorem rowCheck15479 : row15479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15479 := by decide +kernel

theorem rowEval15479 (x : Key → ℝ) : Integer.Sparse.eval row15479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15479, Integer.Sparse.eval_collectBalanced, rawRowCheck15479]

def rawRow15480 : Integer.Sparse Key := [(key1741, -2), (key1710, -2), (key1723, -2), (key1716, 6), (key1741, -2), (key1710, -2), (key1723, -2), (key1513, 2), (key1484, 2), (key1949, 2), (key1358, 2), (key1940, 2), (key1374, 2), (key1490, -2), (key1937, -2), (key1364, -2), (key1716, 6), (key1490, -2), (key1937, -2), (key1364, -2)]

theorem rawRowCheck15480 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form11 = rawRow15480 := by decide +kernel

def row15480 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

theorem rowCheck15480 : row15480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15480 := by decide +kernel

theorem rowEval15480 (x : Key → ℝ) : Integer.Sparse.eval row15480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15480, Integer.Sparse.eval_collectBalanced, rawRowCheck15480]

def rawRow15481 : Integer.Sparse Key := [(key1723, -2), (key1741, -2), (key1710, -2), (key1716, 6), (key1723, -2), (key1741, -2), (key1710, -2), (key1940, 2), (key1949, 2), (key1374, 2), (key1513, 2), (key1358, 2), (key1484, 2), (key1937, -2), (key1364, -2), (key1490, -2), (key1716, 6), (key1937, -2), (key1364, -2), (key1490, -2)]

theorem rawRowCheck15481 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form11 = rawRow15481 := by decide +kernel

def row15481 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

theorem rowCheck15481 : row15481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15481 := by decide +kernel

theorem rowEval15481 (x : Key → ℝ) : Integer.Sparse.eval row15481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15481, Integer.Sparse.eval_collectBalanced, rawRowCheck15481]

def rawRow15482 : Integer.Sparse Key := [(key1741, -2), (key1723, -2), (key1710, -2), (key1716, 6), (key1741, -2), (key1723, -2), (key1710, -2), (key1949, 2), (key1940, 2), (key1513, 2), (key1374, 2), (key1484, 2), (key1358, 2), (key1937, -2), (key1490, -2), (key1364, -2), (key1716, 6), (key1937, -2), (key1490, -2), (key1364, -2)]

theorem rawRowCheck15482 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form11 = rawRow15482 := by decide +kernel

def row15482 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

theorem rowCheck15482 : row15482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15482 := by decide +kernel

theorem rowEval15482 (x : Key → ℝ) : Integer.Sparse.eval row15482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15482, Integer.Sparse.eval_collectBalanced, rawRowCheck15482]

def rawRow15483 : Integer.Sparse Key := [(key2378, 2), (key2378, 2), (key2383, 2), (key2390, -2), (key2394, -2), (key2394, -2), (key2766, 2), (key2766, 2), (key2772, 2), (key2887, -1), (key2889, -1), (key2887, -1), (key2910, -1), (key2889, -1), (key2910, -1), (key2929, -2), (key2931, -2), (key2931, -2), (key2966, -1), (key2968, -1), (key2966, -1), (key2989, -1), (key2968, -1), (key2989, -1), (key2995, 4), (key2995, 4), (key3002, 4)]

theorem rawRowCheck15483 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form12 = rawRow15483 := by decide +kernel

def row15483 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, -2), (key2394, -4), (key2766, 4), (key2772, 2), (key2887, -2), (key2889, -2), (key2910, -2), (key2929, -2), (key2931, -4), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

theorem rowCheck15483 : row15483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15483 := by decide +kernel

theorem rowEval15483 (x : Key → ℝ) : Integer.Sparse.eval row15483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15483, Integer.Sparse.eval_collectBalanced, rawRowCheck15483]

def rawRow15484 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2378, 2), (key2394, -2), (key2390, -2), (key2394, -2), (key2766, 2), (key2772, 2), (key2766, 2), (key2889, -1), (key2887, -1), (key2910, -1), (key2887, -1), (key2910, -1), (key2889, -1), (key2931, -2), (key2929, -2), (key2931, -2), (key2968, -1), (key2966, -1), (key2989, -1), (key2966, -1), (key2989, -1), (key2968, -1), (key2995, 4), (key3002, 4), (key2995, 4)]

theorem rawRowCheck15484 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form12 = rawRow15484 := by decide +kernel

def row15484 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, -2), (key2394, -4), (key2766, 4), (key2772, 2), (key2887, -2), (key2889, -2), (key2910, -2), (key2929, -2), (key2931, -4), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

theorem rowCheck15484 : row15484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15484 := by decide +kernel

theorem rowEval15484 (x : Key → ℝ) : Integer.Sparse.eval row15484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15484, Integer.Sparse.eval_collectBalanced, rawRowCheck15484]

def rawRow15485 : Integer.Sparse Key := [(key2383, 2), (key2378, 2), (key2378, 2), (key2394, -2), (key2394, -2), (key2390, -2), (key2772, 2), (key2766, 2), (key2766, 2), (key2910, -1), (key2910, -1), (key2889, -1), (key2889, -1), (key2887, -1), (key2887, -1), (key2931, -2), (key2931, -2), (key2929, -2), (key2989, -1), (key2989, -1), (key2968, -1), (key2968, -1), (key2966, -1), (key2966, -1), (key3002, 4), (key2995, 4), (key2995, 4)]

theorem rawRowCheck15485 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form12 = rawRow15485 := by decide +kernel

def row15485 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, -2), (key2394, -4), (key2766, 4), (key2772, 2), (key2887, -2), (key2889, -2), (key2910, -2), (key2929, -2), (key2931, -4), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

theorem rowCheck15485 : row15485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15485 := by decide +kernel

theorem rowEval15485 (x : Key → ℝ) : Integer.Sparse.eval row15485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15485, Integer.Sparse.eval_collectBalanced, rawRowCheck15485]

def rawRow15486 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2378, -2), (key2383, -2), (key2394, -2), (key2843, 2), (key2887, 2), (key2889, 2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2966, -2), (key2968, -2), (key2995, -2), (key2929, -1), (key2931, -1), (key2966, -1), (key2989, -1), (key2995, -1), (key3002, -1), (key2931, 4), (key2968, 4), (key2989, 4)]

theorem rawRowCheck15486 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form12 = rawRow15486 := by decide +kernel

def row15486 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

theorem rowCheck15486 : row15486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15486 := by decide +kernel

theorem rowEval15486 (x : Key → ℝ) : Integer.Sparse.eval row15486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15486, Integer.Sparse.eval_collectBalanced, rawRowCheck15486]

def rawRow15487 : Integer.Sparse Key := [(key2378, 2), (key2394, 2), (key2390, 2), (key2383, -2), (key2378, -2), (key2394, -2), (key2843, 2), (key2889, 2), (key2887, 2), (key2772, -1), (key2766, -1), (key2880, -1), (key2843, -1), (key2910, -1), (key2889, -1), (key2968, -2), (key2966, -2), (key2995, -2), (key2931, -1), (key2929, -1), (key2989, -1), (key2966, -1), (key3002, -1), (key2995, -1), (key2931, 4), (key2989, 4), (key2968, 4)]

theorem rawRowCheck15487 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form12 = rawRow15487 := by decide +kernel

def row15487 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

theorem rowCheck15487 : row15487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15487 := by decide +kernel

theorem rowEval15487 (x : Key → ℝ) : Integer.Sparse.eval row15487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15487, Integer.Sparse.eval_collectBalanced, rawRowCheck15487]

end MUB6.Certificate.GramRows

end OAI
