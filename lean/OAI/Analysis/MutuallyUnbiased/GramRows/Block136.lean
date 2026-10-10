import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14336 : Integer.Sparse Key := [(key2854, 6), (key2800, -2), (key2697, -2), (key2850, -2), (key2864, 6), (key2777, -2), (key2623, -2), (key2850, -2), (key2823, -2), (key2720, -2), (key2864, -2), (key2788, -2), (key2634, -2), (key2854, -2), (key2662, 2), (key2777, 2), (key2607, 2), (key2800, 2), (key2623, 2), (key2697, 2)]

theorem rawRowCheck14336 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form3 = rawRow14336 := by decide +kernel

def row14336 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

theorem rowCheck14336 : row14336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14336 := by decide +kernel

theorem rowEval14336 (x : Key → ℝ) : Integer.Sparse.eval row14336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14336, Integer.Sparse.eval_collectBalanced, rawRowCheck14336]

def rawRow14337 : Integer.Sparse Key := [(key2854, 6), (key2800, -2), (key2850, -2), (key2697, -2), (key2864, 6), (key2777, -2), (key2850, -2), (key2623, -2), (key2823, -2), (key2864, -2), (key2720, -2), (key2788, -2), (key2854, -2), (key2634, -2), (key2777, 2), (key2662, 2), (key2800, 2), (key2607, 2), (key2697, 2), (key2623, 2)]

theorem rawRowCheck14337 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form3 = rawRow14337 := by decide +kernel

def row14337 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

theorem rowCheck14337 : row14337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14337 := by decide +kernel

theorem rowEval14337 (x : Key → ℝ) : Integer.Sparse.eval row14337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14337, Integer.Sparse.eval_collectBalanced, rawRowCheck14337]

def rawRow14338 : Integer.Sparse Key := [(key2854, 6), (key2850, -2), (key2697, -2), (key2800, -2), (key2864, 6), (key2850, -2), (key2623, -2), (key2777, -2), (key2864, -2), (key2720, -2), (key2823, -2), (key2854, -2), (key2634, -2), (key2788, -2), (key2697, 2), (key2800, 2), (key2623, 2), (key2777, 2), (key2607, 2), (key2662, 2)]

theorem rawRowCheck14338 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form3 = rawRow14338 := by decide +kernel

def row14338 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

theorem rowCheck14338 : row14338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14338 := by decide +kernel

theorem rowEval14338 (x : Key → ℝ) : Integer.Sparse.eval row14338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14338, Integer.Sparse.eval_collectBalanced, rawRowCheck14338]

def rawRow14339 : Integer.Sparse Key := [(key2854, 6), (key2850, -2), (key2800, -2), (key2697, -2), (key2864, 6), (key2850, -2), (key2777, -2), (key2623, -2), (key2864, -2), (key2823, -2), (key2720, -2), (key2854, -2), (key2788, -2), (key2634, -2), (key2800, 2), (key2697, 2), (key2777, 2), (key2623, 2), (key2662, 2), (key2607, 2)]

theorem rawRowCheck14339 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form3 = rawRow14339 := by decide +kernel

def row14339 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

theorem rowCheck14339 : row14339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14339 := by decide +kernel

theorem rowEval14339 (x : Key → ℝ) : Integer.Sparse.eval row14339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14339, Integer.Sparse.eval_collectBalanced, rawRowCheck14339]

def rawRow14340 : Integer.Sparse Key := [(key2823, 6), (key2720, -2), (key2864, -2), (key2864, -2), (key2788, 6), (key2634, -2), (key2854, -2), (key2854, -2), (key2662, -2), (key2777, -2), (key2777, -2), (key2607, -2), (key2800, -2), (key2800, -2), (key2623, 2), (key2623, 2), (key2697, 2), (key2697, 2), (key2850, 2), (key2850, 2)]

theorem rawRowCheck14340 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form3 = rawRow14340 := by decide +kernel

def row14340 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

theorem rowCheck14340 : row14340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14340 := by decide +kernel

theorem rowEval14340 (x : Key → ℝ) : Integer.Sparse.eval row14340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14340, Integer.Sparse.eval_collectBalanced, rawRowCheck14340]

def rawRow14341 : Integer.Sparse Key := [(key2823, 6), (key2864, -2), (key2720, -2), (key2864, -2), (key2788, 6), (key2854, -2), (key2634, -2), (key2854, -2), (key2777, -2), (key2662, -2), (key2777, -2), (key2800, -2), (key2607, -2), (key2800, -2), (key2697, 2), (key2850, 2), (key2623, 2), (key2850, 2), (key2623, 2), (key2697, 2)]

theorem rawRowCheck14341 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form3 = rawRow14341 := by decide +kernel

def row14341 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

theorem rowCheck14341 : row14341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14341 := by decide +kernel

theorem rowEval14341 (x : Key → ℝ) : Integer.Sparse.eval row14341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14341, Integer.Sparse.eval_collectBalanced, rawRowCheck14341]

def rawRow14342 : Integer.Sparse Key := [(key2823, 6), (key2864, -2), (key2864, -2), (key2720, -2), (key2788, 6), (key2854, -2), (key2854, -2), (key2634, -2), (key2777, -2), (key2777, -2), (key2662, -2), (key2800, -2), (key2800, -2), (key2607, -2), (key2850, 2), (key2697, 2), (key2850, 2), (key2623, 2), (key2697, 2), (key2623, 2)]

theorem rawRowCheck14342 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form3 = rawRow14342 := by decide +kernel

def row14342 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

theorem rowCheck14342 : row14342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14342 := by decide +kernel

theorem rowEval14342 (x : Key → ℝ) : Integer.Sparse.eval row14342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14342, Integer.Sparse.eval_collectBalanced, rawRowCheck14342]

def rawRow14343 : Integer.Sparse Key := [(key2864, 6), (key2720, -2), (key2823, -2), (key2864, -2), (key2854, 6), (key2634, -2), (key2788, -2), (key2854, -2), (key2697, -2), (key2800, -2), (key2850, -2), (key2623, -2), (key2777, -2), (key2850, -2), (key2607, 2), (key2623, 2), (key2662, 2), (key2697, 2), (key2777, 2), (key2800, 2)]

theorem rawRowCheck14343 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form3 = rawRow14343 := by decide +kernel

def row14343 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

theorem rowCheck14343 : row14343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14343 := by decide +kernel

theorem rowEval14343 (x : Key → ℝ) : Integer.Sparse.eval row14343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14343, Integer.Sparse.eval_collectBalanced, rawRowCheck14343]

def rawRow14344 : Integer.Sparse Key := [(key2864, 6), (key2720, -2), (key2864, -2), (key2823, -2), (key2854, 6), (key2634, -2), (key2854, -2), (key2788, -2), (key2697, -2), (key2850, -2), (key2800, -2), (key2623, -2), (key2850, -2), (key2777, -2), (key2623, 2), (key2607, 2), (key2697, 2), (key2662, 2), (key2800, 2), (key2777, 2)]

theorem rawRowCheck14344 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form3 = rawRow14344 := by decide +kernel

def row14344 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

theorem rowCheck14344 : row14344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14344 := by decide +kernel

theorem rowEval14344 (x : Key → ℝ) : Integer.Sparse.eval row14344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14344, Integer.Sparse.eval_collectBalanced, rawRowCheck14344]

def rawRow14345 : Integer.Sparse Key := [(key2864, 6), (key2823, -2), (key2720, -2), (key2864, -2), (key2854, 6), (key2788, -2), (key2634, -2), (key2854, -2), (key2800, -2), (key2697, -2), (key2850, -2), (key2777, -2), (key2623, -2), (key2850, -2), (key2662, 2), (key2777, 2), (key2607, 2), (key2800, 2), (key2623, 2), (key2697, 2)]

theorem rawRowCheck14345 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form3 = rawRow14345 := by decide +kernel

def row14345 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

theorem rowCheck14345 : row14345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14345 := by decide +kernel

theorem rowEval14345 (x : Key → ℝ) : Integer.Sparse.eval row14345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14345, Integer.Sparse.eval_collectBalanced, rawRowCheck14345]

def rawRow14346 : Integer.Sparse Key := [(key2864, 6), (key2823, -2), (key2864, -2), (key2720, -2), (key2854, 6), (key2788, -2), (key2854, -2), (key2634, -2), (key2800, -2), (key2850, -2), (key2697, -2), (key2777, -2), (key2850, -2), (key2623, -2), (key2777, 2), (key2662, 2), (key2800, 2), (key2607, 2), (key2697, 2), (key2623, 2)]

theorem rawRowCheck14346 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form3 = rawRow14346 := by decide +kernel

def row14346 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

theorem rowCheck14346 : row14346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14346 := by decide +kernel

theorem rowEval14346 (x : Key → ℝ) : Integer.Sparse.eval row14346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14346, Integer.Sparse.eval_collectBalanced, rawRowCheck14346]

def rawRow14347 : Integer.Sparse Key := [(key2864, 6), (key2864, -2), (key2720, -2), (key2823, -2), (key2854, 6), (key2854, -2), (key2634, -2), (key2788, -2), (key2850, -2), (key2697, -2), (key2800, -2), (key2850, -2), (key2623, -2), (key2777, -2), (key2697, 2), (key2800, 2), (key2623, 2), (key2777, 2), (key2607, 2), (key2662, 2)]

theorem rawRowCheck14347 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form3 = rawRow14347 := by decide +kernel

def row14347 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

theorem rowCheck14347 : row14347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14347 := by decide +kernel

theorem rowEval14347 (x : Key → ℝ) : Integer.Sparse.eval row14347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14347, Integer.Sparse.eval_collectBalanced, rawRowCheck14347]

def rawRow14348 : Integer.Sparse Key := [(key2864, 6), (key2864, -2), (key2823, -2), (key2720, -2), (key2854, 6), (key2854, -2), (key2788, -2), (key2634, -2), (key2850, -2), (key2800, -2), (key2697, -2), (key2850, -2), (key2777, -2), (key2623, -2), (key2800, 2), (key2697, 2), (key2777, 2), (key2623, 2), (key2662, 2), (key2607, 2)]

theorem rawRowCheck14348 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form3 = rawRow14348 := by decide +kernel

def row14348 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

theorem rowCheck14348 : row14348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14348 := by decide +kernel

theorem rowEval14348 (x : Key → ℝ) : Integer.Sparse.eval row14348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14348, Integer.Sparse.eval_collectBalanced, rawRowCheck14348]

def rawRow14349 : Integer.Sparse Key := [(key1028, -2), (key1032, -2), (key1068, -2), (key1032, 6), (key1106, -2), (key1110, -2), (key1147, -2), (key993, 2), (key997, 2), (key1106, 2), (key1189, 2), (key1147, 2), (key1209, 2), (key997, -2), (key1110, -2), (key1189, -2), (key1120, 6), (key1012, -2), (key1120, -2), (key1196, -2)]

theorem rawRowCheck14349 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form4 = rawRow14349 := by decide +kernel

def row14349 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

theorem rowCheck14349 : row14349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14349 := by decide +kernel

theorem rowEval14349 (x : Key → ℝ) : Integer.Sparse.eval row14349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14349, Integer.Sparse.eval_collectBalanced, rawRowCheck14349]

def rawRow14350 : Integer.Sparse Key := [(key1032, -2), (key1028, -2), (key1068, -2), (key1032, 6), (key1110, -2), (key1106, -2), (key1147, -2), (key997, 2), (key993, 2), (key1189, 2), (key1106, 2), (key1209, 2), (key1147, 2), (key997, -2), (key1189, -2), (key1110, -2), (key1120, 6), (key1012, -2), (key1196, -2), (key1120, -2)]

theorem rawRowCheck14350 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form4 = rawRow14350 := by decide +kernel

def row14350 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

theorem rowCheck14350 : row14350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14350 := by decide +kernel

theorem rowEval14350 (x : Key → ℝ) : Integer.Sparse.eval row14350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14350, Integer.Sparse.eval_collectBalanced, rawRowCheck14350]

def rawRow14351 : Integer.Sparse Key := [(key1028, -2), (key1068, -2), (key1032, -2), (key1032, 6), (key1106, -2), (key1147, -2), (key1110, -2), (key1106, 2), (key1147, 2), (key993, 2), (key1209, 2), (key997, 2), (key1189, 2), (key1110, -2), (key997, -2), (key1189, -2), (key1120, 6), (key1120, -2), (key1012, -2), (key1196, -2)]

theorem rawRowCheck14351 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form4 = rawRow14351 := by decide +kernel

def row14351 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

theorem rowCheck14351 : row14351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14351 := by decide +kernel

theorem rowEval14351 (x : Key → ℝ) : Integer.Sparse.eval row14351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14351, Integer.Sparse.eval_collectBalanced, rawRowCheck14351]

def rawRow14352 : Integer.Sparse Key := [(key1068, -2), (key1028, -2), (key1032, -2), (key1032, 6), (key1147, -2), (key1106, -2), (key1110, -2), (key1147, 2), (key1106, 2), (key1209, 2), (key993, 2), (key1189, 2), (key997, 2), (key1110, -2), (key1189, -2), (key997, -2), (key1120, 6), (key1120, -2), (key1196, -2), (key1012, -2)]

theorem rawRowCheck14352 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form4 = rawRow14352 := by decide +kernel

def row14352 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

theorem rowCheck14352 : row14352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14352 := by decide +kernel

theorem rowEval14352 (x : Key → ℝ) : Integer.Sparse.eval row14352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14352, Integer.Sparse.eval_collectBalanced, rawRowCheck14352]

def rawRow14353 : Integer.Sparse Key := [(key1032, -2), (key1068, -2), (key1028, -2), (key1032, 6), (key1110, -2), (key1147, -2), (key1106, -2), (key1189, 2), (key1209, 2), (key997, 2), (key1147, 2), (key993, 2), (key1106, 2), (key1189, -2), (key997, -2), (key1110, -2), (key1120, 6), (key1196, -2), (key1012, -2), (key1120, -2)]

theorem rawRowCheck14353 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form4 = rawRow14353 := by decide +kernel

def row14353 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

theorem rowCheck14353 : row14353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14353 := by decide +kernel

theorem rowEval14353 (x : Key → ℝ) : Integer.Sparse.eval row14353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14353, Integer.Sparse.eval_collectBalanced, rawRowCheck14353]

def rawRow14354 : Integer.Sparse Key := [(key1068, -2), (key1032, -2), (key1028, -2), (key1032, 6), (key1147, -2), (key1110, -2), (key1106, -2), (key1209, 2), (key1189, 2), (key1147, 2), (key997, 2), (key1106, 2), (key993, 2), (key1189, -2), (key1110, -2), (key997, -2), (key1120, 6), (key1196, -2), (key1120, -2), (key1012, -2)]

theorem rawRowCheck14354 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form4 = rawRow14354 := by decide +kernel

def row14354 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

theorem rowCheck14354 : row14354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14354 := by decide +kernel

theorem rowEval14354 (x : Key → ℝ) : Integer.Sparse.eval row14354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14354, Integer.Sparse.eval_collectBalanced, rawRowCheck14354]

def rawRow14355 : Integer.Sparse Key := [(key1032, -2), (key1032, -2), (key1068, -2), (key1028, 6), (key1189, -2), (key1189, -2), (key1209, -2), (key997, 2), (key997, 2), (key1110, 2), (key1110, 2), (key1147, 2), (key1147, 2), (key993, -2), (key1106, -2), (key1106, -2), (key1196, 6), (key1012, -2), (key1120, -2), (key1120, -2)]

theorem rawRowCheck14355 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form4 = rawRow14355 := by decide +kernel

def row14355 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

theorem rowCheck14355 : row14355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14355 := by decide +kernel

theorem rowEval14355 (x : Key → ℝ) : Integer.Sparse.eval row14355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14355, Integer.Sparse.eval_collectBalanced, rawRowCheck14355]

def rawRow14356 : Integer.Sparse Key := [(key1032, -2), (key1068, -2), (key1032, -2), (key1028, 6), (key1189, -2), (key1209, -2), (key1189, -2), (key1110, 2), (key1147, 2), (key997, 2), (key1147, 2), (key997, 2), (key1110, 2), (key1106, -2), (key993, -2), (key1106, -2), (key1196, 6), (key1120, -2), (key1012, -2), (key1120, -2)]

theorem rawRowCheck14356 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form4 = rawRow14356 := by decide +kernel

def row14356 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

theorem rowCheck14356 : row14356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14356 := by decide +kernel

theorem rowEval14356 (x : Key → ℝ) : Integer.Sparse.eval row14356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14356, Integer.Sparse.eval_collectBalanced, rawRowCheck14356]

def rawRow14357 : Integer.Sparse Key := [(key1068, -2), (key1032, -2), (key1032, -2), (key1028, 6), (key1209, -2), (key1189, -2), (key1189, -2), (key1147, 2), (key1110, 2), (key1147, 2), (key997, 2), (key1110, 2), (key997, 2), (key1106, -2), (key1106, -2), (key993, -2), (key1196, 6), (key1120, -2), (key1120, -2), (key1012, -2)]

theorem rawRowCheck14357 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form4 = rawRow14357 := by decide +kernel

def row14357 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

theorem rowCheck14357 : row14357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14357 := by decide +kernel

theorem rowEval14357 (x : Key → ℝ) : Integer.Sparse.eval row14357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14357, Integer.Sparse.eval_collectBalanced, rawRowCheck14357]

def rawRow14358 : Integer.Sparse Key := [(key1106, -2), (key1110, -2), (key1147, -2), (key1120, 6), (key1028, -2), (key1032, -2), (key1068, -2), (key993, 2), (key997, 2), (key1106, 2), (key1189, 2), (key1147, 2), (key1209, 2), (key1012, -2), (key1120, -2), (key1196, -2), (key1032, 6), (key997, -2), (key1110, -2), (key1189, -2)]

theorem rawRowCheck14358 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form4 = rawRow14358 := by decide +kernel

def row14358 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

theorem rowCheck14358 : row14358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14358 := by decide +kernel

theorem rowEval14358 (x : Key → ℝ) : Integer.Sparse.eval row14358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14358, Integer.Sparse.eval_collectBalanced, rawRowCheck14358]

def rawRow14359 : Integer.Sparse Key := [(key1110, -2), (key1106, -2), (key1147, -2), (key1120, 6), (key1032, -2), (key1028, -2), (key1068, -2), (key997, 2), (key993, 2), (key1189, 2), (key1106, 2), (key1209, 2), (key1147, 2), (key1012, -2), (key1196, -2), (key1120, -2), (key1032, 6), (key997, -2), (key1189, -2), (key1110, -2)]

theorem rawRowCheck14359 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form4 = rawRow14359 := by decide +kernel

def row14359 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

theorem rowCheck14359 : row14359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14359 := by decide +kernel

theorem rowEval14359 (x : Key → ℝ) : Integer.Sparse.eval row14359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14359, Integer.Sparse.eval_collectBalanced, rawRowCheck14359]

def rawRow14360 : Integer.Sparse Key := [(key1106, -2), (key1147, -2), (key1110, -2), (key1120, 6), (key1028, -2), (key1068, -2), (key1032, -2), (key1106, 2), (key1147, 2), (key993, 2), (key1209, 2), (key997, 2), (key1189, 2), (key1120, -2), (key1012, -2), (key1196, -2), (key1032, 6), (key1110, -2), (key997, -2), (key1189, -2)]

theorem rawRowCheck14360 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form4 = rawRow14360 := by decide +kernel

def row14360 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

theorem rowCheck14360 : row14360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14360 := by decide +kernel

theorem rowEval14360 (x : Key → ℝ) : Integer.Sparse.eval row14360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14360, Integer.Sparse.eval_collectBalanced, rawRowCheck14360]

def rawRow14361 : Integer.Sparse Key := [(key1147, -2), (key1106, -2), (key1110, -2), (key1120, 6), (key1068, -2), (key1028, -2), (key1032, -2), (key1147, 2), (key1106, 2), (key1209, 2), (key993, 2), (key1189, 2), (key997, 2), (key1120, -2), (key1196, -2), (key1012, -2), (key1032, 6), (key1110, -2), (key1189, -2), (key997, -2)]

theorem rawRowCheck14361 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form4 = rawRow14361 := by decide +kernel

def row14361 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

theorem rowCheck14361 : row14361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14361 := by decide +kernel

theorem rowEval14361 (x : Key → ℝ) : Integer.Sparse.eval row14361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14361, Integer.Sparse.eval_collectBalanced, rawRowCheck14361]

def rawRow14362 : Integer.Sparse Key := [(key1110, -2), (key1147, -2), (key1106, -2), (key1120, 6), (key1032, -2), (key1068, -2), (key1028, -2), (key1189, 2), (key1209, 2), (key997, 2), (key1147, 2), (key993, 2), (key1106, 2), (key1196, -2), (key1012, -2), (key1120, -2), (key1032, 6), (key1189, -2), (key997, -2), (key1110, -2)]

theorem rawRowCheck14362 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form4 = rawRow14362 := by decide +kernel

def row14362 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

theorem rowCheck14362 : row14362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14362 := by decide +kernel

theorem rowEval14362 (x : Key → ℝ) : Integer.Sparse.eval row14362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14362, Integer.Sparse.eval_collectBalanced, rawRowCheck14362]

def rawRow14363 : Integer.Sparse Key := [(key1147, -2), (key1110, -2), (key1106, -2), (key1120, 6), (key1068, -2), (key1032, -2), (key1028, -2), (key1209, 2), (key1189, 2), (key1147, 2), (key997, 2), (key1106, 2), (key993, 2), (key1196, -2), (key1120, -2), (key1012, -2), (key1032, 6), (key1189, -2), (key1110, -2), (key997, -2)]

theorem rawRowCheck14363 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form4 = rawRow14363 := by decide +kernel

def row14363 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

theorem rowCheck14363 : row14363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14363 := by decide +kernel

theorem rowEval14363 (x : Key → ℝ) : Integer.Sparse.eval row14363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14363, Integer.Sparse.eval_collectBalanced, rawRowCheck14363]

def rawRow14364 : Integer.Sparse Key := [(key1106, -2), (key1120, -2), (key1147, -2), (key1110, 6), (key1106, -2), (key1120, -2), (key1147, -2), (key993, 2), (key1012, 2), (key1028, 2), (key1196, 2), (key1068, 2), (key1209, 2), (key997, -2), (key1032, -2), (key1189, -2), (key1110, 6), (key997, -2), (key1032, -2), (key1189, -2)]

theorem rawRowCheck14364 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form4 = rawRow14364 := by decide +kernel

def row14364 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

theorem rowCheck14364 : row14364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14364 := by decide +kernel

theorem rowEval14364 (x : Key → ℝ) : Integer.Sparse.eval row14364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14364, Integer.Sparse.eval_collectBalanced, rawRowCheck14364]

def rawRow14365 : Integer.Sparse Key := [(key1120, -2), (key1106, -2), (key1147, -2), (key1110, 6), (key1120, -2), (key1106, -2), (key1147, -2), (key1012, 2), (key993, 2), (key1196, 2), (key1028, 2), (key1209, 2), (key1068, 2), (key997, -2), (key1189, -2), (key1032, -2), (key1110, 6), (key997, -2), (key1189, -2), (key1032, -2)]

theorem rawRowCheck14365 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form4 = rawRow14365 := by decide +kernel

def row14365 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

theorem rowCheck14365 : row14365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14365 := by decide +kernel

theorem rowEval14365 (x : Key → ℝ) : Integer.Sparse.eval row14365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14365, Integer.Sparse.eval_collectBalanced, rawRowCheck14365]

def rawRow14366 : Integer.Sparse Key := [(key1106, -2), (key1147, -2), (key1120, -2), (key1110, 6), (key1106, -2), (key1147, -2), (key1120, -2), (key1028, 2), (key1068, 2), (key993, 2), (key1209, 2), (key1012, 2), (key1196, 2), (key1032, -2), (key997, -2), (key1189, -2), (key1110, 6), (key1032, -2), (key997, -2), (key1189, -2)]

theorem rawRowCheck14366 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form4 = rawRow14366 := by decide +kernel

def row14366 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

theorem rowCheck14366 : row14366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14366 := by decide +kernel

theorem rowEval14366 (x : Key → ℝ) : Integer.Sparse.eval row14366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14366, Integer.Sparse.eval_collectBalanced, rawRowCheck14366]

def rawRow14367 : Integer.Sparse Key := [(key1147, -2), (key1106, -2), (key1120, -2), (key1110, 6), (key1147, -2), (key1106, -2), (key1120, -2), (key1068, 2), (key1028, 2), (key1209, 2), (key993, 2), (key1196, 2), (key1012, 2), (key1032, -2), (key1189, -2), (key997, -2), (key1110, 6), (key1032, -2), (key1189, -2), (key997, -2)]

theorem rawRowCheck14367 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form4 = rawRow14367 := by decide +kernel

def row14367 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

theorem rowCheck14367 : row14367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14367 := by decide +kernel

theorem rowEval14367 (x : Key → ℝ) : Integer.Sparse.eval row14367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14367, Integer.Sparse.eval_collectBalanced, rawRowCheck14367]

def rawRow14368 : Integer.Sparse Key := [(key1120, -2), (key1147, -2), (key1106, -2), (key1110, 6), (key1120, -2), (key1147, -2), (key1106, -2), (key1196, 2), (key1209, 2), (key1012, 2), (key1068, 2), (key993, 2), (key1028, 2), (key1189, -2), (key997, -2), (key1032, -2), (key1110, 6), (key1189, -2), (key997, -2), (key1032, -2)]

theorem rawRowCheck14368 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form4 = rawRow14368 := by decide +kernel

def row14368 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

theorem rowCheck14368 : row14368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14368 := by decide +kernel

theorem rowEval14368 (x : Key → ℝ) : Integer.Sparse.eval row14368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14368, Integer.Sparse.eval_collectBalanced, rawRowCheck14368]

def rawRow14369 : Integer.Sparse Key := [(key1147, -2), (key1120, -2), (key1106, -2), (key1110, 6), (key1147, -2), (key1120, -2), (key1106, -2), (key1209, 2), (key1196, 2), (key1068, 2), (key1012, 2), (key1028, 2), (key993, 2), (key1189, -2), (key1032, -2), (key997, -2), (key1110, 6), (key1189, -2), (key1032, -2), (key997, -2)]

theorem rawRowCheck14369 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form4 = rawRow14369 := by decide +kernel

def row14369 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

theorem rowCheck14369 : row14369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14369 := by decide +kernel

theorem rowEval14369 (x : Key → ℝ) : Integer.Sparse.eval row14369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14369, Integer.Sparse.eval_collectBalanced, rawRowCheck14369]

def rawRow14370 : Integer.Sparse Key := [(key1110, -2), (key1120, -2), (key1147, -2), (key1106, 6), (key1189, -2), (key1196, -2), (key1209, -2), (key997, 2), (key1012, 2), (key1032, 2), (key1120, 2), (key1068, 2), (key1147, 2), (key993, -2), (key1028, -2), (key1106, -2), (key1189, 6), (key997, -2), (key1032, -2), (key1110, -2)]

theorem rawRowCheck14370 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form4 = rawRow14370 := by decide +kernel

def row14370 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck14370 : row14370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14370 := by decide +kernel

theorem rowEval14370 (x : Key → ℝ) : Integer.Sparse.eval row14370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14370, Integer.Sparse.eval_collectBalanced, rawRowCheck14370]

def rawRow14371 : Integer.Sparse Key := [(key1120, -2), (key1110, -2), (key1147, -2), (key1106, 6), (key1196, -2), (key1189, -2), (key1209, -2), (key1012, 2), (key997, 2), (key1120, 2), (key1032, 2), (key1147, 2), (key1068, 2), (key993, -2), (key1106, -2), (key1028, -2), (key1189, 6), (key997, -2), (key1110, -2), (key1032, -2)]

theorem rawRowCheck14371 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form4 = rawRow14371 := by decide +kernel

def row14371 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck14371 : row14371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14371 := by decide +kernel

theorem rowEval14371 (x : Key → ℝ) : Integer.Sparse.eval row14371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14371, Integer.Sparse.eval_collectBalanced, rawRowCheck14371]

def rawRow14372 : Integer.Sparse Key := [(key1110, -2), (key1147, -2), (key1120, -2), (key1106, 6), (key1189, -2), (key1209, -2), (key1196, -2), (key1032, 2), (key1068, 2), (key997, 2), (key1147, 2), (key1012, 2), (key1120, 2), (key1028, -2), (key993, -2), (key1106, -2), (key1189, 6), (key1032, -2), (key997, -2), (key1110, -2)]

theorem rawRowCheck14372 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form4 = rawRow14372 := by decide +kernel

def row14372 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck14372 : row14372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14372 := by decide +kernel

theorem rowEval14372 (x : Key → ℝ) : Integer.Sparse.eval row14372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14372, Integer.Sparse.eval_collectBalanced, rawRowCheck14372]

def rawRow14373 : Integer.Sparse Key := [(key1147, -2), (key1110, -2), (key1120, -2), (key1106, 6), (key1209, -2), (key1189, -2), (key1196, -2), (key1068, 2), (key1032, 2), (key1147, 2), (key997, 2), (key1120, 2), (key1012, 2), (key1028, -2), (key1106, -2), (key993, -2), (key1189, 6), (key1032, -2), (key1110, -2), (key997, -2)]

theorem rawRowCheck14373 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form4 = rawRow14373 := by decide +kernel

def row14373 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck14373 : row14373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14373 := by decide +kernel

theorem rowEval14373 (x : Key → ℝ) : Integer.Sparse.eval row14373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14373, Integer.Sparse.eval_collectBalanced, rawRowCheck14373]

def rawRow14374 : Integer.Sparse Key := [(key1120, -2), (key1147, -2), (key1110, -2), (key1106, 6), (key1196, -2), (key1209, -2), (key1189, -2), (key1120, 2), (key1147, 2), (key1012, 2), (key1068, 2), (key997, 2), (key1032, 2), (key1106, -2), (key993, -2), (key1028, -2), (key1189, 6), (key1110, -2), (key997, -2), (key1032, -2)]

theorem rawRowCheck14374 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form4 = rawRow14374 := by decide +kernel

def row14374 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck14374 : row14374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14374 := by decide +kernel

theorem rowEval14374 (x : Key → ℝ) : Integer.Sparse.eval row14374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14374, Integer.Sparse.eval_collectBalanced, rawRowCheck14374]

def rawRow14375 : Integer.Sparse Key := [(key1147, -2), (key1120, -2), (key1110, -2), (key1106, 6), (key1209, -2), (key1196, -2), (key1189, -2), (key1147, 2), (key1120, 2), (key1068, 2), (key1012, 2), (key1032, 2), (key997, 2), (key1106, -2), (key1028, -2), (key993, -2), (key1189, 6), (key1110, -2), (key1032, -2), (key997, -2)]

theorem rawRowCheck14375 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form4 = rawRow14375 := by decide +kernel

def row14375 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck14375 : row14375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14375 := by decide +kernel

theorem rowEval14375 (x : Key → ℝ) : Integer.Sparse.eval row14375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14375, Integer.Sparse.eval_collectBalanced, rawRowCheck14375]

def rawRow14376 : Integer.Sparse Key := [(key1189, -2), (key1189, -2), (key1209, -2), (key1196, 6), (key1032, -2), (key1032, -2), (key1068, -2), (key997, 2), (key997, 2), (key1110, 2), (key1110, 2), (key1147, 2), (key1147, 2), (key1012, -2), (key1120, -2), (key1120, -2), (key1028, 6), (key993, -2), (key1106, -2), (key1106, -2)]

theorem rawRowCheck14376 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form4 = rawRow14376 := by decide +kernel

def row14376 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

theorem rowCheck14376 : row14376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14376 := by decide +kernel

theorem rowEval14376 (x : Key → ℝ) : Integer.Sparse.eval row14376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14376, Integer.Sparse.eval_collectBalanced, rawRowCheck14376]

def rawRow14377 : Integer.Sparse Key := [(key1189, -2), (key1209, -2), (key1189, -2), (key1196, 6), (key1032, -2), (key1068, -2), (key1032, -2), (key1110, 2), (key1147, 2), (key997, 2), (key1147, 2), (key997, 2), (key1110, 2), (key1120, -2), (key1012, -2), (key1120, -2), (key1028, 6), (key1106, -2), (key993, -2), (key1106, -2)]

theorem rawRowCheck14377 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form4 = rawRow14377 := by decide +kernel

def row14377 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

theorem rowCheck14377 : row14377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14377 := by decide +kernel

theorem rowEval14377 (x : Key → ℝ) : Integer.Sparse.eval row14377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14377, Integer.Sparse.eval_collectBalanced, rawRowCheck14377]

def rawRow14378 : Integer.Sparse Key := [(key1209, -2), (key1189, -2), (key1189, -2), (key1196, 6), (key1068, -2), (key1032, -2), (key1032, -2), (key1147, 2), (key1110, 2), (key1147, 2), (key997, 2), (key1110, 2), (key997, 2), (key1120, -2), (key1120, -2), (key1012, -2), (key1028, 6), (key1106, -2), (key1106, -2), (key993, -2)]

theorem rawRowCheck14378 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form4 = rawRow14378 := by decide +kernel

def row14378 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

theorem rowCheck14378 : row14378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14378 := by decide +kernel

theorem rowEval14378 (x : Key → ℝ) : Integer.Sparse.eval row14378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14378, Integer.Sparse.eval_collectBalanced, rawRowCheck14378]

def rawRow14379 : Integer.Sparse Key := [(key1189, -2), (key1196, -2), (key1209, -2), (key1189, 6), (key1110, -2), (key1120, -2), (key1147, -2), (key997, 2), (key1012, 2), (key1032, 2), (key1120, 2), (key1068, 2), (key1147, 2), (key997, -2), (key1032, -2), (key1110, -2), (key1106, 6), (key993, -2), (key1028, -2), (key1106, -2)]

theorem rawRowCheck14379 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form4 = rawRow14379 := by decide +kernel

def row14379 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck14379 : row14379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14379 := by decide +kernel

theorem rowEval14379 (x : Key → ℝ) : Integer.Sparse.eval row14379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14379, Integer.Sparse.eval_collectBalanced, rawRowCheck14379]

def rawRow14380 : Integer.Sparse Key := [(key1196, -2), (key1189, -2), (key1209, -2), (key1189, 6), (key1120, -2), (key1110, -2), (key1147, -2), (key1012, 2), (key997, 2), (key1120, 2), (key1032, 2), (key1147, 2), (key1068, 2), (key997, -2), (key1110, -2), (key1032, -2), (key1106, 6), (key993, -2), (key1106, -2), (key1028, -2)]

theorem rawRowCheck14380 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form4 = rawRow14380 := by decide +kernel

def row14380 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck14380 : row14380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14380 := by decide +kernel

theorem rowEval14380 (x : Key → ℝ) : Integer.Sparse.eval row14380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14380, Integer.Sparse.eval_collectBalanced, rawRowCheck14380]

def rawRow14381 : Integer.Sparse Key := [(key1189, -2), (key1209, -2), (key1196, -2), (key1189, 6), (key1110, -2), (key1147, -2), (key1120, -2), (key1032, 2), (key1068, 2), (key997, 2), (key1147, 2), (key1012, 2), (key1120, 2), (key1032, -2), (key997, -2), (key1110, -2), (key1106, 6), (key1028, -2), (key993, -2), (key1106, -2)]

theorem rawRowCheck14381 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form4 = rawRow14381 := by decide +kernel

def row14381 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck14381 : row14381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14381 := by decide +kernel

theorem rowEval14381 (x : Key → ℝ) : Integer.Sparse.eval row14381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14381, Integer.Sparse.eval_collectBalanced, rawRowCheck14381]

def rawRow14382 : Integer.Sparse Key := [(key1209, -2), (key1189, -2), (key1196, -2), (key1189, 6), (key1147, -2), (key1110, -2), (key1120, -2), (key1068, 2), (key1032, 2), (key1147, 2), (key997, 2), (key1120, 2), (key1012, 2), (key1032, -2), (key1110, -2), (key997, -2), (key1106, 6), (key1028, -2), (key1106, -2), (key993, -2)]

theorem rawRowCheck14382 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form4 = rawRow14382 := by decide +kernel

def row14382 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck14382 : row14382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14382 := by decide +kernel

theorem rowEval14382 (x : Key → ℝ) : Integer.Sparse.eval row14382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14382, Integer.Sparse.eval_collectBalanced, rawRowCheck14382]

def rawRow14383 : Integer.Sparse Key := [(key1196, -2), (key1209, -2), (key1189, -2), (key1189, 6), (key1120, -2), (key1147, -2), (key1110, -2), (key1120, 2), (key1147, 2), (key1012, 2), (key1068, 2), (key997, 2), (key1032, 2), (key1110, -2), (key997, -2), (key1032, -2), (key1106, 6), (key1106, -2), (key993, -2), (key1028, -2)]

theorem rawRowCheck14383 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form4 = rawRow14383 := by decide +kernel

def row14383 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck14383 : row14383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14383 := by decide +kernel

theorem rowEval14383 (x : Key → ℝ) : Integer.Sparse.eval row14383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14383, Integer.Sparse.eval_collectBalanced, rawRowCheck14383]

def rawRow14384 : Integer.Sparse Key := [(key1209, -2), (key1196, -2), (key1189, -2), (key1189, 6), (key1147, -2), (key1120, -2), (key1110, -2), (key1147, 2), (key1120, 2), (key1068, 2), (key1012, 2), (key1032, 2), (key997, 2), (key1110, -2), (key1032, -2), (key997, -2), (key1106, 6), (key1106, -2), (key1028, -2), (key993, -2)]

theorem rawRowCheck14384 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form4 = rawRow14384 := by decide +kernel

def row14384 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck14384 : row14384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14384 := by decide +kernel

theorem rowEval14384 (x : Key → ℝ) : Integer.Sparse.eval row14384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14384, Integer.Sparse.eval_collectBalanced, rawRowCheck14384]

def rawRow14385 : Integer.Sparse Key := [(key1003, 4), (key1152, 4), (key1213, 4), (key1003, -2), (key1007, -2), (key1116, -2), (key1194, -2), (key1156, -2), (key1213, -2), (key1017, -2), (key1020, -2), (key1125, -2), (key1200, -2), (key1172, -2), (key1223, -2), (key1020, 4), (key1128, 4), (key1200, 4)]

theorem rawRowCheck14385 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form5 = rawRow14385 := by decide +kernel

def row14385 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck14385 : row14385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14385 := by decide +kernel

theorem rowEval14385 (x : Key → ℝ) : Integer.Sparse.eval row14385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14385, Integer.Sparse.eval_collectBalanced, rawRowCheck14385]

def rawRow14386 : Integer.Sparse Key := [(key1003, 4), (key1213, 4), (key1152, 4), (key1007, -2), (key1003, -2), (key1194, -2), (key1116, -2), (key1213, -2), (key1156, -2), (key1020, -2), (key1017, -2), (key1200, -2), (key1125, -2), (key1223, -2), (key1172, -2), (key1020, 4), (key1200, 4), (key1128, 4)]

theorem rawRowCheck14386 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form5 = rawRow14386 := by decide +kernel

def row14386 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck14386 : row14386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14386 := by decide +kernel

theorem rowEval14386 (x : Key → ℝ) : Integer.Sparse.eval row14386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14386, Integer.Sparse.eval_collectBalanced, rawRowCheck14386]

def rawRow14387 : Integer.Sparse Key := [(key1152, 4), (key1003, 4), (key1213, 4), (key1116, -2), (key1156, -2), (key1003, -2), (key1213, -2), (key1007, -2), (key1194, -2), (key1125, -2), (key1172, -2), (key1017, -2), (key1223, -2), (key1020, -2), (key1200, -2), (key1128, 4), (key1020, 4), (key1200, 4)]

theorem rawRowCheck14387 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form5 = rawRow14387 := by decide +kernel

def row14387 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck14387 : row14387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14387 := by decide +kernel

theorem rowEval14387 (x : Key → ℝ) : Integer.Sparse.eval row14387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14387, Integer.Sparse.eval_collectBalanced, rawRowCheck14387]

def rawRow14388 : Integer.Sparse Key := [(key1152, 4), (key1213, 4), (key1003, 4), (key1156, -2), (key1116, -2), (key1213, -2), (key1003, -2), (key1194, -2), (key1007, -2), (key1172, -2), (key1125, -2), (key1223, -2), (key1017, -2), (key1200, -2), (key1020, -2), (key1128, 4), (key1200, 4), (key1020, 4)]

theorem rawRowCheck14388 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form5 = rawRow14388 := by decide +kernel

def row14388 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck14388 : row14388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14388 := by decide +kernel

theorem rowEval14388 (x : Key → ℝ) : Integer.Sparse.eval row14388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14388, Integer.Sparse.eval_collectBalanced, rawRowCheck14388]

def rawRow14389 : Integer.Sparse Key := [(key1213, 4), (key1003, 4), (key1152, 4), (key1194, -2), (key1213, -2), (key1007, -2), (key1156, -2), (key1003, -2), (key1116, -2), (key1200, -2), (key1223, -2), (key1020, -2), (key1172, -2), (key1017, -2), (key1125, -2), (key1200, 4), (key1020, 4), (key1128, 4)]

theorem rawRowCheck14389 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form5 = rawRow14389 := by decide +kernel

def row14389 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck14389 : row14389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14389 := by decide +kernel

theorem rowEval14389 (x : Key → ℝ) : Integer.Sparse.eval row14389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14389, Integer.Sparse.eval_collectBalanced, rawRowCheck14389]

def rawRow14390 : Integer.Sparse Key := [(key1213, 4), (key1152, 4), (key1003, 4), (key1213, -2), (key1194, -2), (key1156, -2), (key1007, -2), (key1116, -2), (key1003, -2), (key1223, -2), (key1200, -2), (key1172, -2), (key1020, -2), (key1125, -2), (key1017, -2), (key1200, 4), (key1128, 4), (key1020, 4)]

theorem rawRowCheck14390 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form5 = rawRow14390 := by decide +kernel

def row14390 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck14390 : row14390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14390 := by decide +kernel

theorem rowEval14390 (x : Key → ℝ) : Integer.Sparse.eval row14390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14390, Integer.Sparse.eval_collectBalanced, rawRowCheck14390]

def rawRow14391 : Integer.Sparse Key := [(key1007, 4), (key1156, 4), (key1156, 4), (key1003, -2), (key1003, -2), (key1116, -2), (key1116, -2), (key1152, -2), (key1152, -2), (key1020, -2), (key1020, -2), (key1128, -2), (key1128, -2), (key1172, -2), (key1172, -2), (key1017, 4), (key1125, 4), (key1125, 4)]

theorem rawRowCheck14391 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form5 = rawRow14391 := by decide +kernel

def row14391 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

theorem rowCheck14391 : row14391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14391 := by decide +kernel

theorem rowEval14391 (x : Key → ℝ) : Integer.Sparse.eval row14391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14391, Integer.Sparse.eval_collectBalanced, rawRowCheck14391]

def rawRow14392 : Integer.Sparse Key := [(key1156, 4), (key1007, 4), (key1156, 4), (key1116, -2), (key1152, -2), (key1003, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1128, -2), (key1172, -2), (key1020, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1125, 4), (key1017, 4), (key1125, 4)]

theorem rawRowCheck14392 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form5 = rawRow14392 := by decide +kernel

def row14392 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

theorem rowCheck14392 : row14392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14392 := by decide +kernel

theorem rowEval14392 (x : Key → ℝ) : Integer.Sparse.eval row14392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14392, Integer.Sparse.eval_collectBalanced, rawRowCheck14392]

def rawRow14393 : Integer.Sparse Key := [(key1156, 4), (key1156, 4), (key1007, 4), (key1152, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1003, -2), (key1172, -2), (key1128, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1020, -2), (key1125, 4), (key1125, 4), (key1017, 4)]

theorem rawRowCheck14393 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form5 = rawRow14393 := by decide +kernel

def row14393 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

theorem rowCheck14393 : row14393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14393 := by decide +kernel

theorem rowEval14393 (x : Key → ℝ) : Integer.Sparse.eval row14393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14393, Integer.Sparse.eval_collectBalanced, rawRowCheck14393]

def rawRow14394 : Integer.Sparse Key := [(key1003, 4), (key1152, 4), (key1213, 4), (key1017, -2), (key1020, -2), (key1125, -2), (key1200, -2), (key1172, -2), (key1223, -2), (key1003, -2), (key1007, -2), (key1116, -2), (key1194, -2), (key1156, -2), (key1213, -2), (key1020, 4), (key1128, 4), (key1200, 4)]

theorem rawRowCheck14394 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form5 = rawRow14394 := by decide +kernel

def row14394 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck14394 : row14394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14394 := by decide +kernel

theorem rowEval14394 (x : Key → ℝ) : Integer.Sparse.eval row14394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14394, Integer.Sparse.eval_collectBalanced, rawRowCheck14394]

def rawRow14395 : Integer.Sparse Key := [(key1003, 4), (key1213, 4), (key1152, 4), (key1020, -2), (key1017, -2), (key1200, -2), (key1125, -2), (key1223, -2), (key1172, -2), (key1007, -2), (key1003, -2), (key1194, -2), (key1116, -2), (key1213, -2), (key1156, -2), (key1020, 4), (key1200, 4), (key1128, 4)]

theorem rawRowCheck14395 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form5 = rawRow14395 := by decide +kernel

def row14395 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck14395 : row14395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14395 := by decide +kernel

theorem rowEval14395 (x : Key → ℝ) : Integer.Sparse.eval row14395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14395, Integer.Sparse.eval_collectBalanced, rawRowCheck14395]

def rawRow14396 : Integer.Sparse Key := [(key1152, 4), (key1003, 4), (key1213, 4), (key1125, -2), (key1172, -2), (key1017, -2), (key1223, -2), (key1020, -2), (key1200, -2), (key1116, -2), (key1156, -2), (key1003, -2), (key1213, -2), (key1007, -2), (key1194, -2), (key1128, 4), (key1020, 4), (key1200, 4)]

theorem rawRowCheck14396 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form5 = rawRow14396 := by decide +kernel

def row14396 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck14396 : row14396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14396 := by decide +kernel

theorem rowEval14396 (x : Key → ℝ) : Integer.Sparse.eval row14396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14396, Integer.Sparse.eval_collectBalanced, rawRowCheck14396]

def rawRow14397 : Integer.Sparse Key := [(key1152, 4), (key1213, 4), (key1003, 4), (key1172, -2), (key1125, -2), (key1223, -2), (key1017, -2), (key1200, -2), (key1020, -2), (key1156, -2), (key1116, -2), (key1213, -2), (key1003, -2), (key1194, -2), (key1007, -2), (key1128, 4), (key1200, 4), (key1020, 4)]

theorem rawRowCheck14397 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form5 = rawRow14397 := by decide +kernel

def row14397 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck14397 : row14397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14397 := by decide +kernel

theorem rowEval14397 (x : Key → ℝ) : Integer.Sparse.eval row14397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14397, Integer.Sparse.eval_collectBalanced, rawRowCheck14397]

def rawRow14398 : Integer.Sparse Key := [(key1213, 4), (key1003, 4), (key1152, 4), (key1200, -2), (key1223, -2), (key1020, -2), (key1172, -2), (key1017, -2), (key1125, -2), (key1194, -2), (key1213, -2), (key1007, -2), (key1156, -2), (key1003, -2), (key1116, -2), (key1200, 4), (key1020, 4), (key1128, 4)]

theorem rawRowCheck14398 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form5 = rawRow14398 := by decide +kernel

def row14398 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck14398 : row14398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14398 := by decide +kernel

theorem rowEval14398 (x : Key → ℝ) : Integer.Sparse.eval row14398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14398, Integer.Sparse.eval_collectBalanced, rawRowCheck14398]

def rawRow14399 : Integer.Sparse Key := [(key1213, 4), (key1152, 4), (key1003, 4), (key1223, -2), (key1200, -2), (key1172, -2), (key1020, -2), (key1125, -2), (key1017, -2), (key1213, -2), (key1194, -2), (key1156, -2), (key1007, -2), (key1116, -2), (key1003, -2), (key1200, 4), (key1128, 4), (key1020, 4)]

theorem rawRowCheck14399 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form5 = rawRow14399 := by decide +kernel

def row14399 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck14399 : row14399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14399 := by decide +kernel

theorem rowEval14399 (x : Key → ℝ) : Integer.Sparse.eval row14399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14399, Integer.Sparse.eval_collectBalanced, rawRowCheck14399]

def rawRow14400 : Integer.Sparse Key := [(key1017, 4), (key1073, 4), (key1223, 4), (key1003, -2), (key1020, -2), (key1038, -2), (key1200, -2), (key1077, -2), (key1213, -2), (key1003, -2), (key1020, -2), (key1038, -2), (key1200, -2), (key1077, -2), (key1213, -2), (key1007, 4), (key1042, 4), (key1194, 4)]

theorem rawRowCheck14400 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form5 = rawRow14400 := by decide +kernel

def row14400 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

theorem rowCheck14400 : row14400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14400 := by decide +kernel

theorem rowEval14400 (x : Key → ℝ) : Integer.Sparse.eval row14400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14400, Integer.Sparse.eval_collectBalanced, rawRowCheck14400]

def rawRow14401 : Integer.Sparse Key := [(key1017, 4), (key1223, 4), (key1073, 4), (key1020, -2), (key1003, -2), (key1200, -2), (key1038, -2), (key1213, -2), (key1077, -2), (key1020, -2), (key1003, -2), (key1200, -2), (key1038, -2), (key1213, -2), (key1077, -2), (key1007, 4), (key1194, 4), (key1042, 4)]

theorem rawRowCheck14401 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form5 = rawRow14401 := by decide +kernel

def row14401 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

theorem rowCheck14401 : row14401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14401 := by decide +kernel

theorem rowEval14401 (x : Key → ℝ) : Integer.Sparse.eval row14401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14401, Integer.Sparse.eval_collectBalanced, rawRowCheck14401]

def rawRow14402 : Integer.Sparse Key := [(key1073, 4), (key1017, 4), (key1223, 4), (key1038, -2), (key1077, -2), (key1003, -2), (key1213, -2), (key1020, -2), (key1200, -2), (key1038, -2), (key1077, -2), (key1003, -2), (key1213, -2), (key1020, -2), (key1200, -2), (key1042, 4), (key1007, 4), (key1194, 4)]

theorem rawRowCheck14402 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form5 = rawRow14402 := by decide +kernel

def row14402 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

theorem rowCheck14402 : row14402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14402 := by decide +kernel

theorem rowEval14402 (x : Key → ℝ) : Integer.Sparse.eval row14402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14402, Integer.Sparse.eval_collectBalanced, rawRowCheck14402]

def rawRow14403 : Integer.Sparse Key := [(key1073, 4), (key1223, 4), (key1017, 4), (key1077, -2), (key1038, -2), (key1213, -2), (key1003, -2), (key1200, -2), (key1020, -2), (key1077, -2), (key1038, -2), (key1213, -2), (key1003, -2), (key1200, -2), (key1020, -2), (key1042, 4), (key1194, 4), (key1007, 4)]

theorem rawRowCheck14403 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form5 = rawRow14403 := by decide +kernel

def row14403 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

theorem rowCheck14403 : row14403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14403 := by decide +kernel

theorem rowEval14403 (x : Key → ℝ) : Integer.Sparse.eval row14403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14403, Integer.Sparse.eval_collectBalanced, rawRowCheck14403]

def rawRow14404 : Integer.Sparse Key := [(key1223, 4), (key1017, 4), (key1073, 4), (key1200, -2), (key1213, -2), (key1020, -2), (key1077, -2), (key1003, -2), (key1038, -2), (key1200, -2), (key1213, -2), (key1020, -2), (key1077, -2), (key1003, -2), (key1038, -2), (key1194, 4), (key1007, 4), (key1042, 4)]

theorem rawRowCheck14404 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form5 = rawRow14404 := by decide +kernel

def row14404 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

theorem rowCheck14404 : row14404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14404 := by decide +kernel

theorem rowEval14404 (x : Key → ℝ) : Integer.Sparse.eval row14404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14404, Integer.Sparse.eval_collectBalanced, rawRowCheck14404]

def rawRow14405 : Integer.Sparse Key := [(key1223, 4), (key1073, 4), (key1017, 4), (key1213, -2), (key1200, -2), (key1077, -2), (key1020, -2), (key1038, -2), (key1003, -2), (key1213, -2), (key1200, -2), (key1077, -2), (key1020, -2), (key1038, -2), (key1003, -2), (key1194, 4), (key1042, 4), (key1007, 4)]

theorem rawRowCheck14405 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form5 = rawRow14405 := by decide +kernel

def row14405 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

theorem rowCheck14405 : row14405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14405 := by decide +kernel

theorem rowEval14405 (x : Key → ℝ) : Integer.Sparse.eval row14405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14405, Integer.Sparse.eval_collectBalanced, rawRowCheck14405]

def rawRow14406 : Integer.Sparse Key := [(key1020, 4), (key1077, 4), (key1172, 4), (key1003, -2), (key1017, -2), (key1038, -2), (key1125, -2), (key1073, -2), (key1152, -2), (key1007, -2), (key1020, -2), (key1042, -2), (key1128, -2), (key1077, -2), (key1156, -2), (key1003, 4), (key1038, 4), (key1116, 4)]

theorem rawRowCheck14406 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form5 = rawRow14406 := by decide +kernel

def row14406 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

theorem rowCheck14406 : row14406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14406 := by decide +kernel

theorem rowEval14406 (x : Key → ℝ) : Integer.Sparse.eval row14406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14406, Integer.Sparse.eval_collectBalanced, rawRowCheck14406]

def rawRow14407 : Integer.Sparse Key := [(key1020, 4), (key1172, 4), (key1077, 4), (key1017, -2), (key1003, -2), (key1125, -2), (key1038, -2), (key1152, -2), (key1073, -2), (key1020, -2), (key1007, -2), (key1128, -2), (key1042, -2), (key1156, -2), (key1077, -2), (key1003, 4), (key1116, 4), (key1038, 4)]

theorem rawRowCheck14407 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form5 = rawRow14407 := by decide +kernel

def row14407 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

theorem rowCheck14407 : row14407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14407 := by decide +kernel

theorem rowEval14407 (x : Key → ℝ) : Integer.Sparse.eval row14407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14407, Integer.Sparse.eval_collectBalanced, rawRowCheck14407]

def rawRow14408 : Integer.Sparse Key := [(key1077, 4), (key1020, 4), (key1172, 4), (key1038, -2), (key1073, -2), (key1003, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1042, -2), (key1077, -2), (key1007, -2), (key1156, -2), (key1020, -2), (key1128, -2), (key1038, 4), (key1003, 4), (key1116, 4)]

theorem rawRowCheck14408 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form5 = rawRow14408 := by decide +kernel

def row14408 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

theorem rowCheck14408 : row14408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14408 := by decide +kernel

theorem rowEval14408 (x : Key → ℝ) : Integer.Sparse.eval row14408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14408, Integer.Sparse.eval_collectBalanced, rawRowCheck14408]

def rawRow14409 : Integer.Sparse Key := [(key1077, 4), (key1172, 4), (key1020, 4), (key1073, -2), (key1038, -2), (key1152, -2), (key1003, -2), (key1125, -2), (key1017, -2), (key1077, -2), (key1042, -2), (key1156, -2), (key1007, -2), (key1128, -2), (key1020, -2), (key1038, 4), (key1116, 4), (key1003, 4)]

theorem rawRowCheck14409 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form5 = rawRow14409 := by decide +kernel

def row14409 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

theorem rowCheck14409 : row14409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14409 := by decide +kernel

theorem rowEval14409 (x : Key → ℝ) : Integer.Sparse.eval row14409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14409, Integer.Sparse.eval_collectBalanced, rawRowCheck14409]

def rawRow14410 : Integer.Sparse Key := [(key1172, 4), (key1020, 4), (key1077, 4), (key1125, -2), (key1152, -2), (key1017, -2), (key1073, -2), (key1003, -2), (key1038, -2), (key1128, -2), (key1156, -2), (key1020, -2), (key1077, -2), (key1007, -2), (key1042, -2), (key1116, 4), (key1003, 4), (key1038, 4)]

theorem rawRowCheck14410 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form5 = rawRow14410 := by decide +kernel

def row14410 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

theorem rowCheck14410 : row14410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14410 := by decide +kernel

theorem rowEval14410 (x : Key → ℝ) : Integer.Sparse.eval row14410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14410, Integer.Sparse.eval_collectBalanced, rawRowCheck14410]

def rawRow14411 : Integer.Sparse Key := [(key1172, 4), (key1077, 4), (key1020, 4), (key1152, -2), (key1125, -2), (key1073, -2), (key1017, -2), (key1038, -2), (key1003, -2), (key1156, -2), (key1128, -2), (key1077, -2), (key1020, -2), (key1042, -2), (key1007, -2), (key1116, 4), (key1038, 4), (key1003, 4)]

theorem rawRowCheck14411 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form5 = rawRow14411 := by decide +kernel

def row14411 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

theorem rowCheck14411 : row14411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14411 := by decide +kernel

theorem rowEval14411 (x : Key → ℝ) : Integer.Sparse.eval row14411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14411, Integer.Sparse.eval_collectBalanced, rawRowCheck14411]

def rawRow14412 : Integer.Sparse Key := [(key1007, 4), (key1156, 4), (key1156, 4), (key1020, -2), (key1020, -2), (key1128, -2), (key1128, -2), (key1172, -2), (key1172, -2), (key1003, -2), (key1003, -2), (key1116, -2), (key1116, -2), (key1152, -2), (key1152, -2), (key1017, 4), (key1125, 4), (key1125, 4)]

theorem rawRowCheck14412 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form5 = rawRow14412 := by decide +kernel

def row14412 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

theorem rowCheck14412 : row14412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14412 := by decide +kernel

theorem rowEval14412 (x : Key → ℝ) : Integer.Sparse.eval row14412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14412, Integer.Sparse.eval_collectBalanced, rawRowCheck14412]

def rawRow14413 : Integer.Sparse Key := [(key1156, 4), (key1007, 4), (key1156, 4), (key1128, -2), (key1172, -2), (key1020, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1125, 4), (key1017, 4), (key1125, 4)]

theorem rawRowCheck14413 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form5 = rawRow14413 := by decide +kernel

def row14413 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

theorem rowCheck14413 : row14413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14413 := by decide +kernel

theorem rowEval14413 (x : Key → ℝ) : Integer.Sparse.eval row14413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14413, Integer.Sparse.eval_collectBalanced, rawRowCheck14413]

def rawRow14414 : Integer.Sparse Key := [(key1156, 4), (key1156, 4), (key1007, 4), (key1172, -2), (key1128, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1020, -2), (key1152, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1003, -2), (key1125, 4), (key1125, 4), (key1017, 4)]

theorem rawRowCheck14414 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form5 = rawRow14414 := by decide +kernel

def row14414 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

theorem rowCheck14414 : row14414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14414 := by decide +kernel

theorem rowEval14414 (x : Key → ℝ) : Integer.Sparse.eval row14414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14414, Integer.Sparse.eval_collectBalanced, rawRowCheck14414]

def rawRow14415 : Integer.Sparse Key := [(key1020, 4), (key1077, 4), (key1172, 4), (key1007, -2), (key1020, -2), (key1042, -2), (key1128, -2), (key1077, -2), (key1156, -2), (key1003, -2), (key1017, -2), (key1038, -2), (key1125, -2), (key1073, -2), (key1152, -2), (key1003, 4), (key1038, 4), (key1116, 4)]

theorem rawRowCheck14415 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form5 = rawRow14415 := by decide +kernel

def row14415 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

theorem rowCheck14415 : row14415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14415 := by decide +kernel

theorem rowEval14415 (x : Key → ℝ) : Integer.Sparse.eval row14415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14415, Integer.Sparse.eval_collectBalanced, rawRowCheck14415]

def rawRow14416 : Integer.Sparse Key := [(key1020, 4), (key1172, 4), (key1077, 4), (key1020, -2), (key1007, -2), (key1128, -2), (key1042, -2), (key1156, -2), (key1077, -2), (key1017, -2), (key1003, -2), (key1125, -2), (key1038, -2), (key1152, -2), (key1073, -2), (key1003, 4), (key1116, 4), (key1038, 4)]

theorem rawRowCheck14416 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form5 = rawRow14416 := by decide +kernel

def row14416 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

theorem rowCheck14416 : row14416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14416 := by decide +kernel

theorem rowEval14416 (x : Key → ℝ) : Integer.Sparse.eval row14416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14416, Integer.Sparse.eval_collectBalanced, rawRowCheck14416]

def rawRow14417 : Integer.Sparse Key := [(key1077, 4), (key1020, 4), (key1172, 4), (key1042, -2), (key1077, -2), (key1007, -2), (key1156, -2), (key1020, -2), (key1128, -2), (key1038, -2), (key1073, -2), (key1003, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1038, 4), (key1003, 4), (key1116, 4)]

theorem rawRowCheck14417 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form5 = rawRow14417 := by decide +kernel

def row14417 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

theorem rowCheck14417 : row14417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14417 := by decide +kernel

theorem rowEval14417 (x : Key → ℝ) : Integer.Sparse.eval row14417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14417, Integer.Sparse.eval_collectBalanced, rawRowCheck14417]

def rawRow14418 : Integer.Sparse Key := [(key1077, 4), (key1172, 4), (key1020, 4), (key1077, -2), (key1042, -2), (key1156, -2), (key1007, -2), (key1128, -2), (key1020, -2), (key1073, -2), (key1038, -2), (key1152, -2), (key1003, -2), (key1125, -2), (key1017, -2), (key1038, 4), (key1116, 4), (key1003, 4)]

theorem rawRowCheck14418 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form5 = rawRow14418 := by decide +kernel

def row14418 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

theorem rowCheck14418 : row14418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14418 := by decide +kernel

theorem rowEval14418 (x : Key → ℝ) : Integer.Sparse.eval row14418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14418, Integer.Sparse.eval_collectBalanced, rawRowCheck14418]

def rawRow14419 : Integer.Sparse Key := [(key1172, 4), (key1020, 4), (key1077, 4), (key1128, -2), (key1156, -2), (key1020, -2), (key1077, -2), (key1007, -2), (key1042, -2), (key1125, -2), (key1152, -2), (key1017, -2), (key1073, -2), (key1003, -2), (key1038, -2), (key1116, 4), (key1003, 4), (key1038, 4)]

theorem rawRowCheck14419 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form5 = rawRow14419 := by decide +kernel

def row14419 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

theorem rowCheck14419 : row14419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14419 := by decide +kernel

theorem rowEval14419 (x : Key → ℝ) : Integer.Sparse.eval row14419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14419, Integer.Sparse.eval_collectBalanced, rawRowCheck14419]

def rawRow14420 : Integer.Sparse Key := [(key1172, 4), (key1077, 4), (key1020, 4), (key1156, -2), (key1128, -2), (key1077, -2), (key1020, -2), (key1042, -2), (key1007, -2), (key1152, -2), (key1125, -2), (key1073, -2), (key1017, -2), (key1038, -2), (key1003, -2), (key1116, 4), (key1038, 4), (key1003, 4)]

theorem rawRowCheck14420 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form5 = rawRow14420 := by decide +kernel

def row14420 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

theorem rowCheck14420 : row14420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14420 := by decide +kernel

theorem rowEval14420 (x : Key → ℝ) : Integer.Sparse.eval row14420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14420, Integer.Sparse.eval_collectBalanced, rawRowCheck14420]

def rawRow14421 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2613, 2), (key2806, 2), (key2949, 2), (key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2625, 2), (key2647, 2), (key2779, 2), (key2937, 2), (key2903, 2), (key2982, 2), (key2629, -1), (key2647, -1), (key2783, -1), (key2937, -1), (key2894, -1), (key2973, -1), (key2637, 2), (key2857, 2), (key2975, 2), (key2637, -1), (key2652, -1), (key2791, -1), (key2942, -1), (key2896, -1), (key2975, -1)]

theorem rawRowCheck14421 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form6 = rawRow14421 := by decide +kernel

def row14421 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck14421 : row14421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14421 := by decide +kernel

theorem rowEval14421 (x : Key → ℝ) : Integer.Sparse.eval row14421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14421, Integer.Sparse.eval_collectBalanced, rawRowCheck14421]

def rawRow14422 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2613, 2), (key2949, 2), (key2806, 2), (key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2647, 2), (key2625, 2), (key2937, 2), (key2779, 2), (key2982, 2), (key2903, 2), (key2647, -1), (key2629, -1), (key2937, -1), (key2783, -1), (key2973, -1), (key2894, -1), (key2637, 2), (key2975, 2), (key2857, 2), (key2652, -1), (key2637, -1), (key2942, -1), (key2791, -1), (key2975, -1), (key2896, -1)]

theorem rawRowCheck14422 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form6 = rawRow14422 := by decide +kernel

def row14422 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck14422 : row14422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14422 := by decide +kernel

theorem rowEval14422 (x : Key → ℝ) : Integer.Sparse.eval row14422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14422, Integer.Sparse.eval_collectBalanced, rawRowCheck14422]

def rawRow14423 : Integer.Sparse Key := [(key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2806, 2), (key2613, 2), (key2949, 2), (key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2779, 2), (key2903, 2), (key2625, 2), (key2982, 2), (key2647, 2), (key2937, 2), (key2783, -1), (key2894, -1), (key2629, -1), (key2973, -1), (key2647, -1), (key2937, -1), (key2857, 2), (key2637, 2), (key2975, 2), (key2791, -1), (key2896, -1), (key2637, -1), (key2975, -1), (key2652, -1), (key2942, -1)]

theorem rawRowCheck14423 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form6 = rawRow14423 := by decide +kernel

def row14423 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck14423 : row14423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14423 := by decide +kernel

theorem rowEval14423 (x : Key → ℝ) : Integer.Sparse.eval row14423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14423, Integer.Sparse.eval_collectBalanced, rawRowCheck14423]

def rawRow14424 : Integer.Sparse Key := [(key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2806, 2), (key2949, 2), (key2613, 2), (key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2903, 2), (key2779, 2), (key2982, 2), (key2625, 2), (key2937, 2), (key2647, 2), (key2894, -1), (key2783, -1), (key2973, -1), (key2629, -1), (key2937, -1), (key2647, -1), (key2857, 2), (key2975, 2), (key2637, 2), (key2896, -1), (key2791, -1), (key2975, -1), (key2637, -1), (key2942, -1), (key2652, -1)]

theorem rawRowCheck14424 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form6 = rawRow14424 := by decide +kernel

def row14424 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck14424 : row14424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14424 := by decide +kernel

theorem rowEval14424 (x : Key → ℝ) : Integer.Sparse.eval row14424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14424, Integer.Sparse.eval_collectBalanced, rawRowCheck14424]

def rawRow14425 : Integer.Sparse Key := [(key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2949, 2), (key2613, 2), (key2806, 2), (key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2937, 2), (key2982, 2), (key2647, 2), (key2903, 2), (key2625, 2), (key2779, 2), (key2937, -1), (key2973, -1), (key2647, -1), (key2894, -1), (key2629, -1), (key2783, -1), (key2975, 2), (key2637, 2), (key2857, 2), (key2942, -1), (key2975, -1), (key2652, -1), (key2896, -1), (key2637, -1), (key2791, -1)]

theorem rawRowCheck14425 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form6 = rawRow14425 := by decide +kernel

def row14425 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck14425 : row14425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14425 := by decide +kernel

theorem rowEval14425 (x : Key → ℝ) : Integer.Sparse.eval row14425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14425, Integer.Sparse.eval_collectBalanced, rawRowCheck14425]

def rawRow14426 : Integer.Sparse Key := [(key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2949, 2), (key2806, 2), (key2613, 2), (key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2982, 2), (key2937, 2), (key2903, 2), (key2647, 2), (key2779, 2), (key2625, 2), (key2973, -1), (key2937, -1), (key2894, -1), (key2647, -1), (key2783, -1), (key2629, -1), (key2975, 2), (key2857, 2), (key2637, 2), (key2975, -1), (key2942, -1), (key2896, -1), (key2652, -1), (key2791, -1), (key2637, -1)]

theorem rawRowCheck14426 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form6 = rawRow14426 := by decide +kernel

def row14426 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck14426 : row14426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14426 := by decide +kernel

theorem rowEval14426 (x : Key → ℝ) : Integer.Sparse.eval row14426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14426, Integer.Sparse.eval_collectBalanced, rawRowCheck14426]

def rawRow14427 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2609, 2), (key2802, 2), (key2802, 2), (key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2629, 2), (key2629, 2), (key2783, 2), (key2783, 2), (key2867, 2), (key2867, 2), (key2625, -1), (key2625, -1), (key2779, -1), (key2779, -1), (key2852, -1), (key2852, -1), (key2652, 2), (key2896, 2), (key2896, 2), (key2637, -1), (key2637, -1), (key2791, -1), (key2791, -1), (key2857, -1), (key2857, -1)]

theorem rawRowCheck14427 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form6 = rawRow14427 := by decide +kernel

def row14427 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

theorem rowCheck14427 : row14427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14427 := by decide +kernel

theorem rowEval14427 (x : Key → ℝ) : Integer.Sparse.eval row14427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14427, Integer.Sparse.eval_collectBalanced, rawRowCheck14427]

def rawRow14428 : Integer.Sparse Key := [(key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2802, 2), (key2609, 2), (key2802, 2), (key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2779, -1), (key2852, -1), (key2625, -1), (key2852, -1), (key2625, -1), (key2779, -1), (key2896, 2), (key2652, 2), (key2896, 2), (key2791, -1), (key2857, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2791, -1)]

theorem rawRowCheck14428 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form6 = rawRow14428 := by decide +kernel

def row14428 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

theorem rowCheck14428 : row14428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14428 := by decide +kernel

theorem rowEval14428 (x : Key → ℝ) : Integer.Sparse.eval row14428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14428, Integer.Sparse.eval_collectBalanced, rawRowCheck14428]

def rawRow14429 : Integer.Sparse Key := [(key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2802, 2), (key2802, 2), (key2609, 2), (key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2867, 2), (key2783, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2629, 2), (key2852, -1), (key2779, -1), (key2852, -1), (key2625, -1), (key2779, -1), (key2625, -1), (key2896, 2), (key2896, 2), (key2652, 2), (key2857, -1), (key2791, -1), (key2857, -1), (key2637, -1), (key2791, -1), (key2637, -1)]

theorem rawRowCheck14429 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form6 = rawRow14429 := by decide +kernel

def row14429 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

theorem rowCheck14429 : row14429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14429 := by decide +kernel

theorem rowEval14429 (x : Key → ℝ) : Integer.Sparse.eval row14429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14429, Integer.Sparse.eval_collectBalanced, rawRowCheck14429]

def rawRow14430 : Integer.Sparse Key := [(key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2637, 2), (key2857, 2), (key2975, 2), (key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2625, 2), (key2647, 2), (key2779, 2), (key2937, 2), (key2903, 2), (key2982, 2), (key2637, -1), (key2652, -1), (key2791, -1), (key2942, -1), (key2896, -1), (key2975, -1), (key2613, 2), (key2806, 2), (key2949, 2), (key2629, -1), (key2647, -1), (key2783, -1), (key2937, -1), (key2894, -1), (key2973, -1)]

theorem rawRowCheck14430 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form6 = rawRow14430 := by decide +kernel

def row14430 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck14430 : row14430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14430 := by decide +kernel

theorem rowEval14430 (x : Key → ℝ) : Integer.Sparse.eval row14430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14430, Integer.Sparse.eval_collectBalanced, rawRowCheck14430]

def rawRow14431 : Integer.Sparse Key := [(key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2637, 2), (key2975, 2), (key2857, 2), (key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2647, 2), (key2625, 2), (key2937, 2), (key2779, 2), (key2982, 2), (key2903, 2), (key2652, -1), (key2637, -1), (key2942, -1), (key2791, -1), (key2975, -1), (key2896, -1), (key2613, 2), (key2949, 2), (key2806, 2), (key2647, -1), (key2629, -1), (key2937, -1), (key2783, -1), (key2973, -1), (key2894, -1)]

theorem rawRowCheck14431 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form6 = rawRow14431 := by decide +kernel

def row14431 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck14431 : row14431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14431 := by decide +kernel

theorem rowEval14431 (x : Key → ℝ) : Integer.Sparse.eval row14431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14431, Integer.Sparse.eval_collectBalanced, rawRowCheck14431]

def rawRow14432 : Integer.Sparse Key := [(key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2857, 2), (key2637, 2), (key2975, 2), (key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2779, 2), (key2903, 2), (key2625, 2), (key2982, 2), (key2647, 2), (key2937, 2), (key2791, -1), (key2896, -1), (key2637, -1), (key2975, -1), (key2652, -1), (key2942, -1), (key2806, 2), (key2613, 2), (key2949, 2), (key2783, -1), (key2894, -1), (key2629, -1), (key2973, -1), (key2647, -1), (key2937, -1)]

theorem rawRowCheck14432 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form6 = rawRow14432 := by decide +kernel

def row14432 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck14432 : row14432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14432 := by decide +kernel

theorem rowEval14432 (x : Key → ℝ) : Integer.Sparse.eval row14432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14432, Integer.Sparse.eval_collectBalanced, rawRowCheck14432]

def rawRow14433 : Integer.Sparse Key := [(key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2857, 2), (key2975, 2), (key2637, 2), (key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2903, 2), (key2779, 2), (key2982, 2), (key2625, 2), (key2937, 2), (key2647, 2), (key2896, -1), (key2791, -1), (key2975, -1), (key2637, -1), (key2942, -1), (key2652, -1), (key2806, 2), (key2949, 2), (key2613, 2), (key2894, -1), (key2783, -1), (key2973, -1), (key2629, -1), (key2937, -1), (key2647, -1)]

theorem rawRowCheck14433 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form6 = rawRow14433 := by decide +kernel

def row14433 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck14433 : row14433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14433 := by decide +kernel

theorem rowEval14433 (x : Key → ℝ) : Integer.Sparse.eval row14433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14433, Integer.Sparse.eval_collectBalanced, rawRowCheck14433]

def rawRow14434 : Integer.Sparse Key := [(key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2975, 2), (key2637, 2), (key2857, 2), (key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2937, 2), (key2982, 2), (key2647, 2), (key2903, 2), (key2625, 2), (key2779, 2), (key2942, -1), (key2975, -1), (key2652, -1), (key2896, -1), (key2637, -1), (key2791, -1), (key2949, 2), (key2613, 2), (key2806, 2), (key2937, -1), (key2973, -1), (key2647, -1), (key2894, -1), (key2629, -1), (key2783, -1)]

theorem rawRowCheck14434 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form6 = rawRow14434 := by decide +kernel

def row14434 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck14434 : row14434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14434 := by decide +kernel

theorem rowEval14434 (x : Key → ℝ) : Integer.Sparse.eval row14434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14434, Integer.Sparse.eval_collectBalanced, rawRowCheck14434]

def rawRow14435 : Integer.Sparse Key := [(key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2975, 2), (key2857, 2), (key2637, 2), (key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2982, 2), (key2937, 2), (key2903, 2), (key2647, 2), (key2779, 2), (key2625, 2), (key2975, -1), (key2942, -1), (key2896, -1), (key2652, -1), (key2791, -1), (key2637, -1), (key2949, 2), (key2806, 2), (key2613, 2), (key2973, -1), (key2937, -1), (key2894, -1), (key2647, -1), (key2783, -1), (key2629, -1)]

theorem rawRowCheck14435 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form6 = rawRow14435 := by decide +kernel

def row14435 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck14435 : row14435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14435 := by decide +kernel

theorem rowEval14435 (x : Key → ℝ) : Integer.Sparse.eval row14435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14435, Integer.Sparse.eval_collectBalanced, rawRowCheck14435]

def rawRow14436 : Integer.Sparse Key := [(key2625, -1), (key2637, -1), (key2699, -1), (key2975, -1), (key2723, -1), (key2982, -1), (key2629, 2), (key2703, 2), (key2973, 2), (key2625, -1), (key2637, -1), (key2699, -1), (key2975, -1), (key2723, -1), (key2982, -1), (key2609, 2), (key2652, 2), (key2664, 2), (key2942, 2), (key2746, 2), (key2959, 2), (key2613, -1), (key2647, -1), (key2668, -1), (key2937, -1), (key2736, -1), (key2949, -1), (key2629, 2), (key2703, 2), (key2973, 2), (key2613, -1), (key2647, -1), (key2668, -1), (key2937, -1), (key2736, -1), (key2949, -1)]

theorem rawRowCheck14436 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form6 = rawRow14436 := by decide +kernel

def row14436 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

theorem rowCheck14436 : row14436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14436 := by decide +kernel

theorem rowEval14436 (x : Key → ℝ) : Integer.Sparse.eval row14436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14436, Integer.Sparse.eval_collectBalanced, rawRowCheck14436]

def rawRow14437 : Integer.Sparse Key := [(key2637, -1), (key2625, -1), (key2975, -1), (key2699, -1), (key2982, -1), (key2723, -1), (key2629, 2), (key2973, 2), (key2703, 2), (key2637, -1), (key2625, -1), (key2975, -1), (key2699, -1), (key2982, -1), (key2723, -1), (key2652, 2), (key2609, 2), (key2942, 2), (key2664, 2), (key2959, 2), (key2746, 2), (key2647, -1), (key2613, -1), (key2937, -1), (key2668, -1), (key2949, -1), (key2736, -1), (key2629, 2), (key2973, 2), (key2703, 2), (key2647, -1), (key2613, -1), (key2937, -1), (key2668, -1), (key2949, -1), (key2736, -1)]

theorem rawRowCheck14437 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form6 = rawRow14437 := by decide +kernel

def row14437 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

theorem rowCheck14437 : row14437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14437 := by decide +kernel

theorem rowEval14437 (x : Key → ℝ) : Integer.Sparse.eval row14437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14437, Integer.Sparse.eval_collectBalanced, rawRowCheck14437]

def rawRow14438 : Integer.Sparse Key := [(key2699, -1), (key2723, -1), (key2625, -1), (key2982, -1), (key2637, -1), (key2975, -1), (key2703, 2), (key2629, 2), (key2973, 2), (key2699, -1), (key2723, -1), (key2625, -1), (key2982, -1), (key2637, -1), (key2975, -1), (key2664, 2), (key2746, 2), (key2609, 2), (key2959, 2), (key2652, 2), (key2942, 2), (key2668, -1), (key2736, -1), (key2613, -1), (key2949, -1), (key2647, -1), (key2937, -1), (key2703, 2), (key2629, 2), (key2973, 2), (key2668, -1), (key2736, -1), (key2613, -1), (key2949, -1), (key2647, -1), (key2937, -1)]

theorem rawRowCheck14438 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form6 = rawRow14438 := by decide +kernel

def row14438 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

theorem rowCheck14438 : row14438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14438 := by decide +kernel

theorem rowEval14438 (x : Key → ℝ) : Integer.Sparse.eval row14438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14438, Integer.Sparse.eval_collectBalanced, rawRowCheck14438]

def rawRow14439 : Integer.Sparse Key := [(key2723, -1), (key2699, -1), (key2982, -1), (key2625, -1), (key2975, -1), (key2637, -1), (key2703, 2), (key2973, 2), (key2629, 2), (key2723, -1), (key2699, -1), (key2982, -1), (key2625, -1), (key2975, -1), (key2637, -1), (key2746, 2), (key2664, 2), (key2959, 2), (key2609, 2), (key2942, 2), (key2652, 2), (key2736, -1), (key2668, -1), (key2949, -1), (key2613, -1), (key2937, -1), (key2647, -1), (key2703, 2), (key2973, 2), (key2629, 2), (key2736, -1), (key2668, -1), (key2949, -1), (key2613, -1), (key2937, -1), (key2647, -1)]

theorem rawRowCheck14439 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form6 = rawRow14439 := by decide +kernel

def row14439 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

theorem rowCheck14439 : row14439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14439 := by decide +kernel

theorem rowEval14439 (x : Key → ℝ) : Integer.Sparse.eval row14439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14439, Integer.Sparse.eval_collectBalanced, rawRowCheck14439]

def rawRow14440 : Integer.Sparse Key := [(key2975, -1), (key2982, -1), (key2637, -1), (key2723, -1), (key2625, -1), (key2699, -1), (key2973, 2), (key2629, 2), (key2703, 2), (key2975, -1), (key2982, -1), (key2637, -1), (key2723, -1), (key2625, -1), (key2699, -1), (key2942, 2), (key2959, 2), (key2652, 2), (key2746, 2), (key2609, 2), (key2664, 2), (key2937, -1), (key2949, -1), (key2647, -1), (key2736, -1), (key2613, -1), (key2668, -1), (key2973, 2), (key2629, 2), (key2703, 2), (key2937, -1), (key2949, -1), (key2647, -1), (key2736, -1), (key2613, -1), (key2668, -1)]

theorem rawRowCheck14440 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form6 = rawRow14440 := by decide +kernel

def row14440 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

theorem rowCheck14440 : row14440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14440 := by decide +kernel

theorem rowEval14440 (x : Key → ℝ) : Integer.Sparse.eval row14440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14440, Integer.Sparse.eval_collectBalanced, rawRowCheck14440]

def rawRow14441 : Integer.Sparse Key := [(key2982, -1), (key2975, -1), (key2723, -1), (key2637, -1), (key2699, -1), (key2625, -1), (key2973, 2), (key2703, 2), (key2629, 2), (key2982, -1), (key2975, -1), (key2723, -1), (key2637, -1), (key2699, -1), (key2625, -1), (key2959, 2), (key2942, 2), (key2746, 2), (key2652, 2), (key2664, 2), (key2609, 2), (key2949, -1), (key2937, -1), (key2736, -1), (key2647, -1), (key2668, -1), (key2613, -1), (key2973, 2), (key2703, 2), (key2629, 2), (key2949, -1), (key2937, -1), (key2736, -1), (key2647, -1), (key2668, -1), (key2613, -1)]

theorem rawRowCheck14441 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form6 = rawRow14441 := by decide +kernel

def row14441 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

theorem rowCheck14441 : row14441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14441 := by decide +kernel

theorem rowEval14441 (x : Key → ℝ) : Integer.Sparse.eval row14441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14441, Integer.Sparse.eval_collectBalanced, rawRowCheck14441]

def rawRow14442 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2703, -1), (key2857, -1), (key2723, -1), (key2867, -1), (key2625, 2), (key2699, 2), (key2852, 2), (key2647, -1), (key2652, -1), (key2736, -1), (key2896, -1), (key2746, -1), (key2903, -1), (key2613, 2), (key2637, 2), (key2668, 2), (key2791, 2), (key2723, 2), (key2826, 2), (key2609, -1), (key2625, -1), (key2664, -1), (key2779, -1), (key2699, -1), (key2802, -1), (key2647, 2), (key2736, 2), (key2894, 2), (key2613, -1), (key2629, -1), (key2668, -1), (key2783, -1), (key2703, -1), (key2806, -1)]

theorem rawRowCheck14442 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form6 = rawRow14442 := by decide +kernel

def row14442 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck14442 : row14442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14442 := by decide +kernel

theorem rowEval14442 (x : Key → ℝ) : Integer.Sparse.eval row14442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14442, Integer.Sparse.eval_collectBalanced, rawRowCheck14442]

def rawRow14443 : Integer.Sparse Key := [(key2637, -1), (key2629, -1), (key2857, -1), (key2703, -1), (key2867, -1), (key2723, -1), (key2625, 2), (key2852, 2), (key2699, 2), (key2652, -1), (key2647, -1), (key2896, -1), (key2736, -1), (key2903, -1), (key2746, -1), (key2637, 2), (key2613, 2), (key2791, 2), (key2668, 2), (key2826, 2), (key2723, 2), (key2625, -1), (key2609, -1), (key2779, -1), (key2664, -1), (key2802, -1), (key2699, -1), (key2647, 2), (key2894, 2), (key2736, 2), (key2629, -1), (key2613, -1), (key2783, -1), (key2668, -1), (key2806, -1), (key2703, -1)]

theorem rawRowCheck14443 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form6 = rawRow14443 := by decide +kernel

def row14443 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck14443 : row14443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14443 := by decide +kernel

theorem rowEval14443 (x : Key → ℝ) : Integer.Sparse.eval row14443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14443, Integer.Sparse.eval_collectBalanced, rawRowCheck14443]

def rawRow14444 : Integer.Sparse Key := [(key2703, -1), (key2723, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2699, 2), (key2625, 2), (key2852, 2), (key2736, -1), (key2746, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2668, 2), (key2723, 2), (key2613, 2), (key2826, 2), (key2637, 2), (key2791, 2), (key2664, -1), (key2699, -1), (key2609, -1), (key2802, -1), (key2625, -1), (key2779, -1), (key2736, 2), (key2647, 2), (key2894, 2), (key2668, -1), (key2703, -1), (key2613, -1), (key2806, -1), (key2629, -1), (key2783, -1)]

theorem rawRowCheck14444 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form6 = rawRow14444 := by decide +kernel

def row14444 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck14444 : row14444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14444 := by decide +kernel

theorem rowEval14444 (x : Key → ℝ) : Integer.Sparse.eval row14444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14444, Integer.Sparse.eval_collectBalanced, rawRowCheck14444]

def rawRow14445 : Integer.Sparse Key := [(key2723, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2857, -1), (key2637, -1), (key2699, 2), (key2852, 2), (key2625, 2), (key2746, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2896, -1), (key2652, -1), (key2723, 2), (key2668, 2), (key2826, 2), (key2613, 2), (key2791, 2), (key2637, 2), (key2699, -1), (key2664, -1), (key2802, -1), (key2609, -1), (key2779, -1), (key2625, -1), (key2736, 2), (key2894, 2), (key2647, 2), (key2703, -1), (key2668, -1), (key2806, -1), (key2613, -1), (key2783, -1), (key2629, -1)]

theorem rawRowCheck14445 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form6 = rawRow14445 := by decide +kernel

def row14445 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck14445 : row14445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14445 := by decide +kernel

theorem rowEval14445 (x : Key → ℝ) : Integer.Sparse.eval row14445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14445, Integer.Sparse.eval_collectBalanced, rawRowCheck14445]

def rawRow14446 : Integer.Sparse Key := [(key2857, -1), (key2867, -1), (key2637, -1), (key2723, -1), (key2629, -1), (key2703, -1), (key2852, 2), (key2625, 2), (key2699, 2), (key2896, -1), (key2903, -1), (key2652, -1), (key2746, -1), (key2647, -1), (key2736, -1), (key2791, 2), (key2826, 2), (key2637, 2), (key2723, 2), (key2613, 2), (key2668, 2), (key2779, -1), (key2802, -1), (key2625, -1), (key2699, -1), (key2609, -1), (key2664, -1), (key2894, 2), (key2647, 2), (key2736, 2), (key2783, -1), (key2806, -1), (key2629, -1), (key2703, -1), (key2613, -1), (key2668, -1)]

theorem rawRowCheck14446 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form6 = rawRow14446 := by decide +kernel

def row14446 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck14446 : row14446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14446 := by decide +kernel

theorem rowEval14446 (x : Key → ℝ) : Integer.Sparse.eval row14446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14446, Integer.Sparse.eval_collectBalanced, rawRowCheck14446]

def rawRow14447 : Integer.Sparse Key := [(key2867, -1), (key2857, -1), (key2723, -1), (key2637, -1), (key2703, -1), (key2629, -1), (key2852, 2), (key2699, 2), (key2625, 2), (key2903, -1), (key2896, -1), (key2746, -1), (key2652, -1), (key2736, -1), (key2647, -1), (key2826, 2), (key2791, 2), (key2723, 2), (key2637, 2), (key2668, 2), (key2613, 2), (key2802, -1), (key2779, -1), (key2699, -1), (key2625, -1), (key2664, -1), (key2609, -1), (key2894, 2), (key2736, 2), (key2647, 2), (key2806, -1), (key2783, -1), (key2703, -1), (key2629, -1), (key2668, -1), (key2613, -1)]

theorem rawRowCheck14447 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form6 = rawRow14447 := by decide +kernel

def row14447 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck14447 : row14447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14447 := by decide +kernel

theorem rowEval14447 (x : Key → ℝ) : Integer.Sparse.eval row14447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14447, Integer.Sparse.eval_collectBalanced, rawRowCheck14447]

def rawRow14448 : Integer.Sparse Key := [(key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2652, 2), (key2896, 2), (key2896, 2), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2629, 2), (key2629, 2), (key2783, 2), (key2783, 2), (key2867, 2), (key2867, 2), (key2637, -1), (key2637, -1), (key2791, -1), (key2791, -1), (key2857, -1), (key2857, -1), (key2609, 2), (key2802, 2), (key2802, 2), (key2625, -1), (key2625, -1), (key2779, -1), (key2779, -1), (key2852, -1), (key2852, -1)]

theorem rawRowCheck14448 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form6 = rawRow14448 := by decide +kernel

def row14448 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

theorem rowCheck14448 : row14448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14448 := by decide +kernel

theorem rowEval14448 (x : Key → ℝ) : Integer.Sparse.eval row14448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14448, Integer.Sparse.eval_collectBalanced, rawRowCheck14448]

def rawRow14449 : Integer.Sparse Key := [(key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2896, 2), (key2652, 2), (key2896, 2), (key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2791, -1), (key2857, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2791, -1), (key2802, 2), (key2609, 2), (key2802, 2), (key2779, -1), (key2852, -1), (key2625, -1), (key2852, -1), (key2625, -1), (key2779, -1)]

theorem rawRowCheck14449 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form6 = rawRow14449 := by decide +kernel

def row14449 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

theorem rowCheck14449 : row14449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14449 := by decide +kernel

theorem rowEval14449 (x : Key → ℝ) : Integer.Sparse.eval row14449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14449, Integer.Sparse.eval_collectBalanced, rawRowCheck14449]

def rawRow14450 : Integer.Sparse Key := [(key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2896, 2), (key2896, 2), (key2652, 2), (key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2867, 2), (key2783, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2629, 2), (key2857, -1), (key2791, -1), (key2857, -1), (key2637, -1), (key2791, -1), (key2637, -1), (key2802, 2), (key2802, 2), (key2609, 2), (key2852, -1), (key2779, -1), (key2852, -1), (key2625, -1), (key2779, -1), (key2625, -1)]

theorem rawRowCheck14450 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form6 = rawRow14450 := by decide +kernel

def row14450 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

theorem rowCheck14450 : row14450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14450 := by decide +kernel

theorem rowEval14450 (x : Key → ℝ) : Integer.Sparse.eval row14450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14450, Integer.Sparse.eval_collectBalanced, rawRowCheck14450]

def rawRow14451 : Integer.Sparse Key := [(key2647, -1), (key2652, -1), (key2736, -1), (key2896, -1), (key2746, -1), (key2903, -1), (key2647, 2), (key2736, 2), (key2894, 2), (key2629, -1), (key2637, -1), (key2703, -1), (key2857, -1), (key2723, -1), (key2867, -1), (key2613, 2), (key2637, 2), (key2668, 2), (key2791, 2), (key2723, 2), (key2826, 2), (key2613, -1), (key2629, -1), (key2668, -1), (key2783, -1), (key2703, -1), (key2806, -1), (key2625, 2), (key2699, 2), (key2852, 2), (key2609, -1), (key2625, -1), (key2664, -1), (key2779, -1), (key2699, -1), (key2802, -1)]

theorem rawRowCheck14451 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form6 = rawRow14451 := by decide +kernel

def row14451 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck14451 : row14451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14451 := by decide +kernel

theorem rowEval14451 (x : Key → ℝ) : Integer.Sparse.eval row14451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14451, Integer.Sparse.eval_collectBalanced, rawRowCheck14451]

def rawRow14452 : Integer.Sparse Key := [(key2652, -1), (key2647, -1), (key2896, -1), (key2736, -1), (key2903, -1), (key2746, -1), (key2647, 2), (key2894, 2), (key2736, 2), (key2637, -1), (key2629, -1), (key2857, -1), (key2703, -1), (key2867, -1), (key2723, -1), (key2637, 2), (key2613, 2), (key2791, 2), (key2668, 2), (key2826, 2), (key2723, 2), (key2629, -1), (key2613, -1), (key2783, -1), (key2668, -1), (key2806, -1), (key2703, -1), (key2625, 2), (key2852, 2), (key2699, 2), (key2625, -1), (key2609, -1), (key2779, -1), (key2664, -1), (key2802, -1), (key2699, -1)]

theorem rawRowCheck14452 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form6 = rawRow14452 := by decide +kernel

def row14452 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck14452 : row14452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14452 := by decide +kernel

theorem rowEval14452 (x : Key → ℝ) : Integer.Sparse.eval row14452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14452, Integer.Sparse.eval_collectBalanced, rawRowCheck14452]

def rawRow14453 : Integer.Sparse Key := [(key2736, -1), (key2746, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2736, 2), (key2647, 2), (key2894, 2), (key2703, -1), (key2723, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2668, 2), (key2723, 2), (key2613, 2), (key2826, 2), (key2637, 2), (key2791, 2), (key2668, -1), (key2703, -1), (key2613, -1), (key2806, -1), (key2629, -1), (key2783, -1), (key2699, 2), (key2625, 2), (key2852, 2), (key2664, -1), (key2699, -1), (key2609, -1), (key2802, -1), (key2625, -1), (key2779, -1)]

theorem rawRowCheck14453 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form6 = rawRow14453 := by decide +kernel

def row14453 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck14453 : row14453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14453 := by decide +kernel

theorem rowEval14453 (x : Key → ℝ) : Integer.Sparse.eval row14453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14453, Integer.Sparse.eval_collectBalanced, rawRowCheck14453]

def rawRow14454 : Integer.Sparse Key := [(key2746, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2896, -1), (key2652, -1), (key2736, 2), (key2894, 2), (key2647, 2), (key2723, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2857, -1), (key2637, -1), (key2723, 2), (key2668, 2), (key2826, 2), (key2613, 2), (key2791, 2), (key2637, 2), (key2703, -1), (key2668, -1), (key2806, -1), (key2613, -1), (key2783, -1), (key2629, -1), (key2699, 2), (key2852, 2), (key2625, 2), (key2699, -1), (key2664, -1), (key2802, -1), (key2609, -1), (key2779, -1), (key2625, -1)]

theorem rawRowCheck14454 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form6 = rawRow14454 := by decide +kernel

def row14454 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck14454 : row14454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14454 := by decide +kernel

theorem rowEval14454 (x : Key → ℝ) : Integer.Sparse.eval row14454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14454, Integer.Sparse.eval_collectBalanced, rawRowCheck14454]

def rawRow14455 : Integer.Sparse Key := [(key2896, -1), (key2903, -1), (key2652, -1), (key2746, -1), (key2647, -1), (key2736, -1), (key2894, 2), (key2647, 2), (key2736, 2), (key2857, -1), (key2867, -1), (key2637, -1), (key2723, -1), (key2629, -1), (key2703, -1), (key2791, 2), (key2826, 2), (key2637, 2), (key2723, 2), (key2613, 2), (key2668, 2), (key2783, -1), (key2806, -1), (key2629, -1), (key2703, -1), (key2613, -1), (key2668, -1), (key2852, 2), (key2625, 2), (key2699, 2), (key2779, -1), (key2802, -1), (key2625, -1), (key2699, -1), (key2609, -1), (key2664, -1)]

theorem rawRowCheck14455 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form6 = rawRow14455 := by decide +kernel

def row14455 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck14455 : row14455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14455 := by decide +kernel

theorem rowEval14455 (x : Key → ℝ) : Integer.Sparse.eval row14455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14455, Integer.Sparse.eval_collectBalanced, rawRowCheck14455]

def rawRow14456 : Integer.Sparse Key := [(key2903, -1), (key2896, -1), (key2746, -1), (key2652, -1), (key2736, -1), (key2647, -1), (key2894, 2), (key2736, 2), (key2647, 2), (key2867, -1), (key2857, -1), (key2723, -1), (key2637, -1), (key2703, -1), (key2629, -1), (key2826, 2), (key2791, 2), (key2723, 2), (key2637, 2), (key2668, 2), (key2613, 2), (key2806, -1), (key2783, -1), (key2703, -1), (key2629, -1), (key2668, -1), (key2613, -1), (key2852, 2), (key2699, 2), (key2625, 2), (key2802, -1), (key2779, -1), (key2699, -1), (key2625, -1), (key2664, -1), (key2609, -1)]

theorem rawRowCheck14456 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form6 = rawRow14456 := by decide +kernel

def row14456 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck14456 : row14456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14456 := by decide +kernel

theorem rowEval14456 (x : Key → ℝ) : Integer.Sparse.eval row14456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14456, Integer.Sparse.eval_collectBalanced, rawRowCheck14456]

def rawRow14457 : Integer.Sparse Key := [(key2678, 4), (key2812, 4), (key2816, 4), (key2678, -4), (key2687, -4), (key2816, -4), (key2709, -4), (key2713, -4), (key2862, -4), (key2713, 12)]

theorem rawRowCheck14457 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form7 = rawRow14457 := by decide +kernel

def row14457 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

theorem rowCheck14457 : row14457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14457 := by decide +kernel

theorem rowEval14457 (x : Key → ℝ) : Integer.Sparse.eval row14457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14457, Integer.Sparse.eval_collectBalanced, rawRowCheck14457]

def rawRow14458 : Integer.Sparse Key := [(key2678, 4), (key2816, 4), (key2812, 4), (key2687, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2709, -4), (key2862, -4), (key2713, 12)]

theorem rawRowCheck14458 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form7 = rawRow14458 := by decide +kernel

def row14458 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

theorem rowCheck14458 : row14458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14458 := by decide +kernel

theorem rowEval14458 (x : Key → ℝ) : Integer.Sparse.eval row14458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14458, Integer.Sparse.eval_collectBalanced, rawRowCheck14458]

def rawRow14459 : Integer.Sparse Key := [(key2812, 4), (key2678, 4), (key2816, 4), (key2678, -4), (key2816, -4), (key2687, -4), (key2709, -4), (key2862, -4), (key2713, -4), (key2713, 12)]

theorem rawRowCheck14459 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form7 = rawRow14459 := by decide +kernel

def row14459 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

theorem rowCheck14459 : row14459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14459 := by decide +kernel

theorem rowEval14459 (x : Key → ℝ) : Integer.Sparse.eval row14459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14459, Integer.Sparse.eval_collectBalanced, rawRowCheck14459]

def rawRow14460 : Integer.Sparse Key := [(key2812, 4), (key2816, 4), (key2678, 4), (key2816, -4), (key2678, -4), (key2687, -4), (key2862, -4), (key2709, -4), (key2713, -4), (key2713, 12)]

theorem rawRowCheck14460 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form7 = rawRow14460 := by decide +kernel

def row14460 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

theorem rowCheck14460 : row14460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14460 := by decide +kernel

theorem rowEval14460 (x : Key → ℝ) : Integer.Sparse.eval row14460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14460, Integer.Sparse.eval_collectBalanced, rawRowCheck14460]

def rawRow14461 : Integer.Sparse Key := [(key2816, 4), (key2678, 4), (key2812, 4), (key2687, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2862, -4), (key2709, -4), (key2713, 12)]

theorem rawRowCheck14461 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form7 = rawRow14461 := by decide +kernel

def row14461 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

theorem rowCheck14461 : row14461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14461 := by decide +kernel

theorem rowEval14461 (x : Key → ℝ) : Integer.Sparse.eval row14461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14461, Integer.Sparse.eval_collectBalanced, rawRowCheck14461]

def rawRow14462 : Integer.Sparse Key := [(key2816, 4), (key2812, 4), (key2678, 4), (key2816, -4), (key2687, -4), (key2678, -4), (key2862, -4), (key2713, -4), (key2709, -4), (key2713, 12)]

theorem rawRowCheck14462 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form7 = rawRow14462 := by decide +kernel

def row14462 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

theorem rowCheck14462 : row14462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14462 := by decide +kernel

theorem rowEval14462 (x : Key → ℝ) : Integer.Sparse.eval row14462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14462, Integer.Sparse.eval_collectBalanced, rawRowCheck14462]

def rawRow14463 : Integer.Sparse Key := [(key2687, 4), (key2816, 4), (key2816, 4), (key2678, -4), (key2678, -4), (key2812, -4), (key2713, -4), (key2713, -4), (key2862, -4), (key2709, 12)]

theorem rawRowCheck14463 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form7 = rawRow14463 := by decide +kernel

def row14463 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck14463 : row14463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14463 := by decide +kernel

theorem rowEval14463 (x : Key → ℝ) : Integer.Sparse.eval row14463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14463, Integer.Sparse.eval_collectBalanced, rawRowCheck14463]

end MUB6.Certificate.GramRows

end OAI
