import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9344 : Integer.Sparse Key := [(key2300, -6), (key2313, -6), (key2299, -6), (key2300, -6), (key2300, 2), (key2313, 2), (key2299, 2), (key2340, 2), (key2349, 2), (key2007, 2), (key2313, 2), (key2006, 2), (key2299, 2), (key2340, 2), (key2007, 2), (key2300, 2)]

theorem rawRowCheck9344 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form13 = rawRow9344 := by decide +kernel

def row9344 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

theorem rowCheck9344 : row9344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9344 := by decide +kernel

theorem rowEval9344 (x : Key → ℝ) : Integer.Sparse.eval row9344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9344, Integer.Sparse.eval_collectBalanced, rawRowCheck9344]

def rawRow9345 : Integer.Sparse Key := [(key2313, -6), (key2300, -6), (key2299, -6), (key2300, -6), (key2313, 2), (key2300, 2), (key2299, 2), (key2349, 2), (key2340, 2), (key2313, 2), (key2007, 2), (key2299, 2), (key2006, 2), (key2340, 2), (key2300, 2), (key2007, 2)]

theorem rawRowCheck9345 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form13 = rawRow9345 := by decide +kernel

def row9345 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

theorem rowCheck9345 : row9345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9345 := by decide +kernel

theorem rowEval9345 (x : Key → ℝ) : Integer.Sparse.eval row9345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck9345, Integer.Sparse.eval_collectBalanced, rawRowCheck9345]

def rawRow9346 : Integer.Sparse Key := [(key2300, -6), (key2300, -6), (key2313, -6), (key2299, -6), (key2340, 2), (key2340, 2), (key2349, 2), (key2007, 2), (key2007, 2), (key2300, 2), (key2300, 2), (key2313, 2), (key2313, 2), (key2006, 2), (key2299, 2), (key2299, 2)]

theorem rawRowCheck9346 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form13 = rawRow9346 := by decide +kernel

def row9346 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

theorem rowCheck9346 : row9346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9346 := by decide +kernel

theorem rowEval9346 (x : Key → ℝ) : Integer.Sparse.eval row9346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9346, Integer.Sparse.eval_collectBalanced, rawRowCheck9346]

def rawRow9347 : Integer.Sparse Key := [(key2300, -6), (key2313, -6), (key2300, -6), (key2299, -6), (key2340, 2), (key2349, 2), (key2340, 2), (key2300, 2), (key2313, 2), (key2007, 2), (key2313, 2), (key2007, 2), (key2300, 2), (key2299, 2), (key2006, 2), (key2299, 2)]

theorem rawRowCheck9347 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form13 = rawRow9347 := by decide +kernel

def row9347 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

theorem rowCheck9347 : row9347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9347 := by decide +kernel

theorem rowEval9347 (x : Key → ℝ) : Integer.Sparse.eval row9347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9347, Integer.Sparse.eval_collectBalanced, rawRowCheck9347]

def rawRow9348 : Integer.Sparse Key := [(key2313, -6), (key2300, -6), (key2300, -6), (key2299, -6), (key2349, 2), (key2340, 2), (key2340, 2), (key2313, 2), (key2300, 2), (key2313, 2), (key2007, 2), (key2300, 2), (key2007, 2), (key2299, 2), (key2299, 2), (key2006, 2)]

theorem rawRowCheck9348 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form13 = rawRow9348 := by decide +kernel

def row9348 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

theorem rowCheck9348 : row9348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9348 := by decide +kernel

theorem rowEval9348 (x : Key → ℝ) : Integer.Sparse.eval row9348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck9348, Integer.Sparse.eval_collectBalanced, rawRowCheck9348]

def rawRow9349 : Integer.Sparse Key := [(key972, 6), (key977, 6), (key977, 6), (key977, 6), (key1162, -6), (key1162, -6), (key1162, -6), (key1218, -6)]

theorem rawRowCheck9349 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form14 = rawRow9349 := by decide +kernel

def row9349 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1162, -18), (key1218, -6)]

theorem rowCheck9349 : row9349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9349 := by decide +kernel

theorem rowEval9349 (x : Key → ℝ) : Integer.Sparse.eval row9349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9349, Integer.Sparse.eval_collectBalanced, rawRowCheck9349]

def rawRow9350 : Integer.Sparse Key := [(key977, 6), (key972, 6), (key977, 6), (key977, 6), (key1162, -6), (key1162, -6), (key1218, -6), (key1162, -6)]

theorem rawRowCheck9350 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form14 = rawRow9350 := by decide +kernel

def row9350 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1162, -18), (key1218, -6)]

theorem rowCheck9350 : row9350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9350 := by decide +kernel

theorem rowEval9350 (x : Key → ℝ) : Integer.Sparse.eval row9350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9350, Integer.Sparse.eval_collectBalanced, rawRowCheck9350]

def rawRow9351 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key972, 6), (key977, 6), (key1162, -6), (key1218, -6), (key1162, -6), (key1162, -6)]

theorem rawRowCheck9351 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form14 = rawRow9351 := by decide +kernel

def row9351 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1162, -18), (key1218, -6)]

theorem rowCheck9351 : row9351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9351 := by decide +kernel

theorem rowEval9351 (x : Key → ℝ) : Integer.Sparse.eval row9351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9351, Integer.Sparse.eval_collectBalanced, rawRowCheck9351]

def rawRow9352 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key977, 6), (key972, 6), (key1218, -6), (key1162, -6), (key1162, -6), (key1162, -6)]

theorem rawRowCheck9352 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form14 = rawRow9352 := by decide +kernel

def row9352 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1162, -18), (key1218, -6)]

theorem rowCheck9352 : row9352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9352 := by decide +kernel

theorem rowEval9352 (x : Key → ℝ) : Integer.Sparse.eval row9352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9352, Integer.Sparse.eval_collectBalanced, rawRowCheck9352]

def rawRow9353 : Integer.Sparse Key := [(key1086, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key977, -6), (key1091, -6), (key1091, -6), (key1181, -6)]

theorem rawRowCheck9353 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form14 = rawRow9353 := by decide +kernel

def row9353 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

theorem rowCheck9353 : row9353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9353 := by decide +kernel

theorem rowEval9353 (x : Key → ℝ) : Integer.Sparse.eval row9353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9353, Integer.Sparse.eval_collectBalanced, rawRowCheck9353]

def rawRow9354 : Integer.Sparse Key := [(key1091, 6), (key1086, 6), (key1091, 6), (key1162, 6), (key977, -6), (key1091, -6), (key1181, -6), (key1091, -6)]

theorem rawRowCheck9354 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form14 = rawRow9354 := by decide +kernel

def row9354 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

theorem rowCheck9354 : row9354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9354 := by decide +kernel

theorem rowEval9354 (x : Key → ℝ) : Integer.Sparse.eval row9354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9354, Integer.Sparse.eval_collectBalanced, rawRowCheck9354]

def rawRow9355 : Integer.Sparse Key := [(key1091, 6), (key1091, 6), (key1086, 6), (key1162, 6), (key977, -6), (key1181, -6), (key1091, -6), (key1091, -6)]

theorem rawRowCheck9355 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form14 = rawRow9355 := by decide +kernel

def row9355 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

theorem rowCheck9355 : row9355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9355 := by decide +kernel

theorem rowEval9355 (x : Key → ℝ) : Integer.Sparse.eval row9355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9355, Integer.Sparse.eval_collectBalanced, rawRowCheck9355]

def rawRow9356 : Integer.Sparse Key := [(key1086, 6), (key1091, 6), (key1162, 6), (key1091, 6), (key1091, -6), (key977, -6), (key1091, -6), (key1181, -6)]

theorem rawRowCheck9356 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form14 = rawRow9356 := by decide +kernel

def row9356 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

theorem rowCheck9356 : row9356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9356 := by decide +kernel

theorem rowEval9356 (x : Key → ℝ) : Integer.Sparse.eval row9356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9356, Integer.Sparse.eval_collectBalanced, rawRowCheck9356]

def rawRow9357 : Integer.Sparse Key := [(key1091, 6), (key1086, 6), (key1162, 6), (key1091, 6), (key1091, -6), (key977, -6), (key1181, -6), (key1091, -6)]

theorem rawRowCheck9357 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form14 = rawRow9357 := by decide +kernel

def row9357 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

theorem rowCheck9357 : row9357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9357 := by decide +kernel

theorem rowEval9357 (x : Key → ℝ) : Integer.Sparse.eval row9357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9357, Integer.Sparse.eval_collectBalanced, rawRowCheck9357]

def rawRow9358 : Integer.Sparse Key := [(key1086, 6), (key1162, 6), (key1091, 6), (key1091, 6), (key1091, -6), (key1091, -6), (key977, -6), (key1181, -6)]

theorem rawRowCheck9358 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form14 = rawRow9358 := by decide +kernel

def row9358 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

theorem rowCheck9358 : row9358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9358 := by decide +kernel

theorem rowEval9358 (x : Key → ℝ) : Integer.Sparse.eval row9358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9358, Integer.Sparse.eval_collectBalanced, rawRowCheck9358]

def rawRow9359 : Integer.Sparse Key := [(key1162, 6), (key1086, 6), (key1091, 6), (key1091, 6), (key1091, -6), (key1091, -6), (key1181, -6), (key977, -6)]

theorem rawRowCheck9359 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form14 = rawRow9359 := by decide +kernel

def row9359 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

theorem rowCheck9359 : row9359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9359 := by decide +kernel

theorem rowEval9359 (x : Key → ℝ) : Integer.Sparse.eval row9359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck9359, Integer.Sparse.eval_collectBalanced, rawRowCheck9359]

def rawRow9360 : Integer.Sparse Key := [(key1091, 6), (key1162, 6), (key1086, 6), (key1091, 6), (key1091, -6), (key1181, -6), (key977, -6), (key1091, -6)]

theorem rawRowCheck9360 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form14 = rawRow9360 := by decide +kernel

def row9360 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

theorem rowCheck9360 : row9360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9360 := by decide +kernel

theorem rowEval9360 (x : Key → ℝ) : Integer.Sparse.eval row9360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9360, Integer.Sparse.eval_collectBalanced, rawRowCheck9360]

def rawRow9361 : Integer.Sparse Key := [(key1162, 6), (key1091, 6), (key1086, 6), (key1091, 6), (key1091, -6), (key1181, -6), (key1091, -6), (key977, -6)]

theorem rawRowCheck9361 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form14 = rawRow9361 := by decide +kernel

def row9361 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

theorem rowCheck9361 : row9361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9361 := by decide +kernel

theorem rowEval9361 (x : Key → ℝ) : Integer.Sparse.eval row9361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck9361, Integer.Sparse.eval_collectBalanced, rawRowCheck9361]

def rawRow9362 : Integer.Sparse Key := [(key1091, 6), (key1091, 6), (key1162, 6), (key1086, 6), (key1181, -6), (key977, -6), (key1091, -6), (key1091, -6)]

theorem rawRowCheck9362 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form14 = rawRow9362 := by decide +kernel

def row9362 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

theorem rowCheck9362 : row9362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9362 := by decide +kernel

theorem rowEval9362 (x : Key → ℝ) : Integer.Sparse.eval row9362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9362, Integer.Sparse.eval_collectBalanced, rawRowCheck9362]

def rawRow9363 : Integer.Sparse Key := [(key1091, 6), (key1162, 6), (key1091, 6), (key1086, 6), (key1181, -6), (key1091, -6), (key977, -6), (key1091, -6)]

theorem rawRowCheck9363 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form14 = rawRow9363 := by decide +kernel

def row9363 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

theorem rowCheck9363 : row9363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9363 := by decide +kernel

theorem rowEval9363 (x : Key → ℝ) : Integer.Sparse.eval row9363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9363, Integer.Sparse.eval_collectBalanced, rawRowCheck9363]

def rawRow9364 : Integer.Sparse Key := [(key1162, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1181, -6), (key1091, -6), (key1091, -6), (key977, -6)]

theorem rawRowCheck9364 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form14 = rawRow9364 := by decide +kernel

def row9364 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

theorem rowCheck9364 : row9364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9364 := by decide +kernel

theorem rowEval9364 (x : Key → ℝ) : Integer.Sparse.eval row9364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck9364, Integer.Sparse.eval_collectBalanced, rawRowCheck9364]

def rawRow9365 : Integer.Sparse Key := [(key2353, -6), (key2356, -6), (key2356, -6), (key2356, -6), (key2448, 2), (key2451, 2), (key2451, 2), (key2448, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2513, 2), (key2451, 2), (key2451, 2), (key2513, 2)]

theorem rawRowCheck9365 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form15 = rawRow9365 := by decide +kernel

def row9365 : Integer.Sparse Key := [(key2353, -6), (key2356, -18), (key2448, 6), (key2451, 12), (key2513, 6)]

theorem rowCheck9365 : row9365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9365 := by decide +kernel

theorem rowEval9365 (x : Key → ℝ) : Integer.Sparse.eval row9365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9365, Integer.Sparse.eval_collectBalanced, rawRowCheck9365]

def rawRow9366 : Integer.Sparse Key := [(key2356, -6), (key2353, -6), (key2356, -6), (key2356, -6), (key2451, 2), (key2448, 2), (key2451, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2451, 2), (key2513, 2), (key2451, 2)]

theorem rawRowCheck9366 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form15 = rawRow9366 := by decide +kernel

def row9366 : Integer.Sparse Key := [(key2353, -6), (key2356, -18), (key2448, 6), (key2451, 12), (key2513, 6)]

theorem rowCheck9366 : row9366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9366 := by decide +kernel

theorem rowEval9366 (x : Key → ℝ) : Integer.Sparse.eval row9366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9366, Integer.Sparse.eval_collectBalanced, rawRowCheck9366]

def rawRow9367 : Integer.Sparse Key := [(key2356, -6), (key2356, -6), (key2353, -6), (key2356, -6), (key2451, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2513, 2), (key2451, 2), (key2451, 2), (key2448, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2451, 2)]

theorem rawRowCheck9367 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form15 = rawRow9367 := by decide +kernel

def row9367 : Integer.Sparse Key := [(key2353, -6), (key2356, -18), (key2448, 6), (key2451, 12), (key2513, 6)]

theorem rowCheck9367 : row9367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9367 := by decide +kernel

theorem rowEval9367 (x : Key → ℝ) : Integer.Sparse.eval row9367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9367, Integer.Sparse.eval_collectBalanced, rawRowCheck9367]

def rawRow9368 : Integer.Sparse Key := [(key2356, -6), (key2356, -6), (key2356, -6), (key2353, -6), (key2513, 2), (key2513, 2), (key2513, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2448, 2), (key2448, 2), (key2448, 2)]

theorem rawRowCheck9368 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form15 = rawRow9368 := by decide +kernel

def row9368 : Integer.Sparse Key := [(key2353, -6), (key2356, -18), (key2448, 6), (key2451, 12), (key2513, 6)]

theorem rowCheck9368 : row9368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9368 := by decide +kernel

theorem rowEval9368 (x : Key → ℝ) : Integer.Sparse.eval row9368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9368, Integer.Sparse.eval_collectBalanced, rawRowCheck9368]

def rawRow9369 : Integer.Sparse Key := [(key2448, -6), (key2451, -6), (key2451, -6), (key2513, -6), (key2353, 2), (key2356, 2), (key2356, 2), (key2448, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2513, 2), (key2527, 2), (key2527, 2), (key2558, 2)]

theorem rawRowCheck9369 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form15 = rawRow9369 := by decide +kernel

def row9369 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, -2), (key2527, 4), (key2558, 2)]

theorem rowCheck9369 : row9369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9369 := by decide +kernel

theorem rowEval9369 (x : Key → ℝ) : Integer.Sparse.eval row9369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9369, Integer.Sparse.eval_collectBalanced, rawRowCheck9369]

def rawRow9370 : Integer.Sparse Key := [(key2451, -6), (key2448, -6), (key2451, -6), (key2513, -6), (key2356, 2), (key2353, 2), (key2356, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2527, 2), (key2558, 2), (key2527, 2)]

theorem rawRowCheck9370 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form15 = rawRow9370 := by decide +kernel

def row9370 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, -2), (key2527, 4), (key2558, 2)]

theorem rowCheck9370 : row9370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9370 := by decide +kernel

theorem rowEval9370 (x : Key → ℝ) : Integer.Sparse.eval row9370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9370, Integer.Sparse.eval_collectBalanced, rawRowCheck9370]

def rawRow9371 : Integer.Sparse Key := [(key2451, -6), (key2451, -6), (key2448, -6), (key2513, -6), (key2356, 2), (key2356, 2), (key2353, 2), (key2513, 2), (key2513, 2), (key2451, 2), (key2451, 2), (key2448, 2), (key2448, 2), (key2558, 2), (key2527, 2), (key2527, 2)]

theorem rawRowCheck9371 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form15 = rawRow9371 := by decide +kernel

def row9371 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, -2), (key2527, 4), (key2558, 2)]

theorem rowCheck9371 : row9371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9371 := by decide +kernel

theorem rowEval9371 (x : Key → ℝ) : Integer.Sparse.eval row9371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9371, Integer.Sparse.eval_collectBalanced, rawRowCheck9371]

def rawRow9372 : Integer.Sparse Key := [(key2448, -6), (key2451, -6), (key2513, -6), (key2451, -6), (key2448, 2), (key2451, 2), (key2513, 2), (key2353, 2), (key2356, 2), (key2448, 2), (key2513, 2), (key2527, 2), (key2558, 2), (key2356, 2), (key2451, 2), (key2513, 2)]

theorem rawRowCheck9372 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form15 = rawRow9372 := by decide +kernel

def row9372 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2527, 2), (key2558, 2)]

theorem rowCheck9372 : row9372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9372 := by decide +kernel

theorem rowEval9372 (x : Key → ℝ) : Integer.Sparse.eval row9372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9372, Integer.Sparse.eval_collectBalanced, rawRowCheck9372]

def rawRow9373 : Integer.Sparse Key := [(key2451, -6), (key2448, -6), (key2513, -6), (key2451, -6), (key2451, 2), (key2448, 2), (key2513, 2), (key2356, 2), (key2353, 2), (key2513, 2), (key2448, 2), (key2558, 2), (key2527, 2), (key2356, 2), (key2513, 2), (key2451, 2)]

theorem rawRowCheck9373 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form15 = rawRow9373 := by decide +kernel

def row9373 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2527, 2), (key2558, 2)]

theorem rowCheck9373 : row9373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9373 := by decide +kernel

theorem rowEval9373 (x : Key → ℝ) : Integer.Sparse.eval row9373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9373, Integer.Sparse.eval_collectBalanced, rawRowCheck9373]

def rawRow9374 : Integer.Sparse Key := [(key2448, -6), (key2513, -6), (key2451, -6), (key2451, -6), (key2448, 2), (key2513, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2353, 2), (key2558, 2), (key2356, 2), (key2513, 2), (key2451, 2), (key2356, 2), (key2513, 2)]

theorem rawRowCheck9374 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form15 = rawRow9374 := by decide +kernel

def row9374 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, 2), (key2558, 2)]

theorem rowCheck9374 : row9374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9374 := by decide +kernel

theorem rowEval9374 (x : Key → ℝ) : Integer.Sparse.eval row9374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9374, Integer.Sparse.eval_collectBalanced, rawRowCheck9374]

def rawRow9375 : Integer.Sparse Key := [(key2513, -6), (key2448, -6), (key2451, -6), (key2451, -6), (key2513, 2), (key2448, 2), (key2451, 2), (key2513, 2), (key2448, 2), (key2558, 2), (key2353, 2), (key2513, 2), (key2356, 2), (key2451, 2), (key2513, 2), (key2356, 2)]

theorem rawRowCheck9375 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form15 = rawRow9375 := by decide +kernel

def row9375 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, 2), (key2558, 2)]

theorem rowCheck9375 : row9375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9375 := by decide +kernel

theorem rowEval9375 (x : Key → ℝ) : Integer.Sparse.eval row9375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck9375, Integer.Sparse.eval_collectBalanced, rawRowCheck9375]

def rawRow9376 : Integer.Sparse Key := [(key2451, -6), (key2513, -6), (key2448, -6), (key2451, -6), (key2451, 2), (key2513, 2), (key2448, 2), (key2527, 2), (key2558, 2), (key2356, 2), (key2513, 2), (key2353, 2), (key2448, 2), (key2513, 2), (key2356, 2), (key2451, 2)]

theorem rawRowCheck9376 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form15 = rawRow9376 := by decide +kernel

def row9376 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2527, 2), (key2558, 2)]

theorem rowCheck9376 : row9376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9376 := by decide +kernel

theorem rowEval9376 (x : Key → ℝ) : Integer.Sparse.eval row9376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9376, Integer.Sparse.eval_collectBalanced, rawRowCheck9376]

def rawRow9377 : Integer.Sparse Key := [(key2513, -6), (key2451, -6), (key2448, -6), (key2451, -6), (key2513, 2), (key2451, 2), (key2448, 2), (key2558, 2), (key2527, 2), (key2513, 2), (key2356, 2), (key2448, 2), (key2353, 2), (key2513, 2), (key2451, 2), (key2356, 2)]

theorem rawRowCheck9377 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form15 = rawRow9377 := by decide +kernel

def row9377 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2527, 2), (key2558, 2)]

theorem rowCheck9377 : row9377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9377 := by decide +kernel

theorem rowEval9377 (x : Key → ℝ) : Integer.Sparse.eval row9377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck9377, Integer.Sparse.eval_collectBalanced, rawRowCheck9377]

def rawRow9378 : Integer.Sparse Key := [(key2451, -6), (key2451, -6), (key2513, -6), (key2448, -6), (key2527, 2), (key2527, 2), (key2558, 2), (key2356, 2), (key2356, 2), (key2451, 2), (key2451, 2), (key2513, 2), (key2513, 2), (key2353, 2), (key2448, 2), (key2448, 2)]

theorem rawRowCheck9378 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form15 = rawRow9378 := by decide +kernel

def row9378 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, -2), (key2527, 4), (key2558, 2)]

theorem rowCheck9378 : row9378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9378 := by decide +kernel

theorem rowEval9378 (x : Key → ℝ) : Integer.Sparse.eval row9378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9378, Integer.Sparse.eval_collectBalanced, rawRowCheck9378]

def rawRow9379 : Integer.Sparse Key := [(key2451, -6), (key2513, -6), (key2451, -6), (key2448, -6), (key2527, 2), (key2558, 2), (key2527, 2), (key2451, 2), (key2513, 2), (key2356, 2), (key2513, 2), (key2356, 2), (key2451, 2), (key2448, 2), (key2353, 2), (key2448, 2)]

theorem rawRowCheck9379 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form15 = rawRow9379 := by decide +kernel

def row9379 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, -2), (key2527, 4), (key2558, 2)]

theorem rowCheck9379 : row9379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9379 := by decide +kernel

theorem rowEval9379 (x : Key → ℝ) : Integer.Sparse.eval row9379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9379, Integer.Sparse.eval_collectBalanced, rawRowCheck9379]

def rawRow9380 : Integer.Sparse Key := [(key2513, -6), (key2451, -6), (key2451, -6), (key2448, -6), (key2558, 2), (key2527, 2), (key2527, 2), (key2513, 2), (key2451, 2), (key2513, 2), (key2356, 2), (key2451, 2), (key2356, 2), (key2448, 2), (key2448, 2), (key2353, 2)]

theorem rawRowCheck9380 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form15 = rawRow9380 := by decide +kernel

def row9380 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, -2), (key2527, 4), (key2558, 2)]

theorem rowCheck9380 : row9380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9380 := by decide +kernel

theorem rowEval9380 (x : Key → ℝ) : Integer.Sparse.eval row9380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck9380, Integer.Sparse.eval_collectBalanced, rawRowCheck9380]

def rawRow9381 : Integer.Sparse Key := [(key2405, 2), (key2405, 2), (key2405, 2), (key2471, 2), (key2471, 2), (key2471, 2), (key2479, 2), (key2479, 2), (key2479, 2), (key2479, 2), (key2479, 2), (key2479, 2), (key2436, -2), (key2436, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2518, -2), (key2518, -2)]

theorem rawRowCheck9381 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form0 = rawRow9381 := by decide +kernel

def row9381 : Integer.Sparse Key := [(key2405, 6), (key2436, -6), (key2471, 6), (key2479, 12), (key2502, -12), (key2518, -6)]

theorem rowCheck9381 : row9381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9381 := by decide +kernel

theorem rowEval9381 (x : Key → ℝ) : Integer.Sparse.eval row9381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9381, Integer.Sparse.eval_collectBalanced, rawRowCheck9381]

def rawRow9382 : Integer.Sparse Key := [(key2471, 2), (key2479, 2), (key2479, 2), (key2405, 2), (key2479, 2), (key2479, 2), (key2405, 2), (key2405, 2), (key2471, 2), (key2471, 2), (key2479, 2), (key2479, 2), (key2502, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2502, -2)]

theorem rawRowCheck9382 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form0 = rawRow9382 := by decide +kernel

def row9382 : Integer.Sparse Key := [(key2405, 6), (key2436, -6), (key2471, 6), (key2479, 12), (key2502, -12), (key2518, -6)]

theorem rowCheck9382 : row9382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9382 := by decide +kernel

theorem rowEval9382 (x : Key → ℝ) : Integer.Sparse.eval row9382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9382, Integer.Sparse.eval_collectBalanced, rawRowCheck9382]

def rawRow9383 : Integer.Sparse Key := [(key2479, 2), (key2471, 2), (key2479, 2), (key2479, 2), (key2405, 2), (key2479, 2), (key2471, 2), (key2479, 2), (key2405, 2), (key2479, 2), (key2405, 2), (key2471, 2), (key2502, -2), (key2518, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2436, -2), (key2502, -2)]

theorem rawRowCheck9383 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form0 = rawRow9383 := by decide +kernel

def row9383 : Integer.Sparse Key := [(key2405, 6), (key2436, -6), (key2471, 6), (key2479, 12), (key2502, -12), (key2518, -6)]

theorem rowCheck9383 : row9383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9383 := by decide +kernel

theorem rowEval9383 (x : Key → ℝ) : Integer.Sparse.eval row9383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9383, Integer.Sparse.eval_collectBalanced, rawRowCheck9383]

def rawRow9384 : Integer.Sparse Key := [(key2479, 2), (key2479, 2), (key2471, 2), (key2479, 2), (key2479, 2), (key2405, 2), (key2479, 2), (key2471, 2), (key2479, 2), (key2405, 2), (key2471, 2), (key2405, 2), (key2518, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2436, -2)]

theorem rawRowCheck9384 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form0 = rawRow9384 := by decide +kernel

def row9384 : Integer.Sparse Key := [(key2405, 6), (key2436, -6), (key2471, 6), (key2479, 12), (key2502, -12), (key2518, -6)]

theorem rowCheck9384 : row9384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9384 := by decide +kernel

theorem rowEval9384 (x : Key → ℝ) : Integer.Sparse.eval row9384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9384, Integer.Sparse.eval_collectBalanced, rawRowCheck9384]

def rawRow9385 : Integer.Sparse Key := [(key989, -24), (key1024, 6), (key1102, 6), (key1102, 6), (key1102, 6)]

theorem rawRowCheck9385 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form1 = rawRow9385 := by decide +kernel

def row9385 : Integer.Sparse Key := [(key989, -24), (key1024, 6), (key1102, 18)]

theorem rowCheck9385 : row9385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9385 := by decide +kernel

theorem rowEval9385 (x : Key → ℝ) : Integer.Sparse.eval row9385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9385, Integer.Sparse.eval_collectBalanced, rawRowCheck9385]

def rawRow9386 : Integer.Sparse Key := [(key989, -24), (key1102, 6), (key1024, 6), (key1102, 6), (key1102, 6)]

theorem rawRowCheck9386 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form1 = rawRow9386 := by decide +kernel

def row9386 : Integer.Sparse Key := [(key989, -24), (key1024, 6), (key1102, 18)]

theorem rowCheck9386 : row9386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9386 := by decide +kernel

theorem rowEval9386 (x : Key → ℝ) : Integer.Sparse.eval row9386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9386, Integer.Sparse.eval_collectBalanced, rawRowCheck9386]

def rawRow9387 : Integer.Sparse Key := [(key989, -24), (key1102, 6), (key1102, 6), (key1024, 6), (key1102, 6)]

theorem rawRowCheck9387 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form1 = rawRow9387 := by decide +kernel

def row9387 : Integer.Sparse Key := [(key989, -24), (key1024, 6), (key1102, 18)]

theorem rowCheck9387 : row9387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9387 := by decide +kernel

theorem rowEval9387 (x : Key → ℝ) : Integer.Sparse.eval row9387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9387, Integer.Sparse.eval_collectBalanced, rawRowCheck9387]

def rawRow9388 : Integer.Sparse Key := [(key989, -24), (key1102, 6), (key1102, 6), (key1102, 6), (key1024, 6)]

theorem rawRowCheck9388 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form1 = rawRow9388 := by decide +kernel

def row9388 : Integer.Sparse Key := [(key989, -24), (key1024, 6), (key1102, 18)]

theorem rowCheck9388 : row9388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9388 := by decide +kernel

theorem rowEval9388 (x : Key → ℝ) : Integer.Sparse.eval row9388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9388, Integer.Sparse.eval_collectBalanced, rawRowCheck9388]

def rawRow9389 : Integer.Sparse Key := [(key995, -6), (key995, -6), (key995, -6), (key1011, -6), (key1030, 2), (key1030, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1119, 2), (key1119, 2), (key1119, 2)]

theorem rawRowCheck9389 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form2 = rawRow9389 := by decide +kernel

def row9389 : Integer.Sparse Key := [(key995, -18), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, 6)]

theorem rowCheck9389 : row9389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9389 := by decide +kernel

theorem rowEval9389 (x : Key → ℝ) : Integer.Sparse.eval row9389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9389, Integer.Sparse.eval_collectBalanced, rawRowCheck9389]

def rawRow9390 : Integer.Sparse Key := [(key995, -6), (key995, -6), (key1011, -6), (key995, -6), (key1108, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1119, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1108, 2)]

theorem rawRowCheck9390 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form2 = rawRow9390 := by decide +kernel

def row9390 : Integer.Sparse Key := [(key995, -18), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, 6)]

theorem rowCheck9390 : row9390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9390 := by decide +kernel

theorem rowEval9390 (x : Key → ℝ) : Integer.Sparse.eval row9390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9390, Integer.Sparse.eval_collectBalanced, rawRowCheck9390]

def rawRow9391 : Integer.Sparse Key := [(key995, -6), (key1011, -6), (key995, -6), (key995, -6), (key1108, 2), (key1119, 2), (key1108, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1030, 2), (key1108, 2)]

theorem rawRowCheck9391 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form2 = rawRow9391 := by decide +kernel

def row9391 : Integer.Sparse Key := [(key995, -18), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, 6)]

theorem rowCheck9391 : row9391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9391 := by decide +kernel

theorem rowEval9391 (x : Key → ℝ) : Integer.Sparse.eval row9391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9391, Integer.Sparse.eval_collectBalanced, rawRowCheck9391]

def rawRow9392 : Integer.Sparse Key := [(key1011, -6), (key995, -6), (key995, -6), (key995, -6), (key1119, 2), (key1108, 2), (key1108, 2), (key1119, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1030, 2)]

theorem rawRowCheck9392 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form2 = rawRow9392 := by decide +kernel

def row9392 : Integer.Sparse Key := [(key995, -18), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, 6)]

theorem rowCheck9392 : row9392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9392 := by decide +kernel

theorem rowEval9392 (x : Key → ℝ) : Integer.Sparse.eval row9392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9392, Integer.Sparse.eval_collectBalanced, rawRowCheck9392]

def rawRow9393 : Integer.Sparse Key := [(key2661, -6), (key2696, -6), (key2696, -6), (key2696, -6), (key2776, 2), (key2776, 2), (key2776, 2), (key2799, 2), (key2799, 2), (key2799, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2)]

theorem rawRowCheck9393 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form3 = rawRow9393 := by decide +kernel

def row9393 : Integer.Sparse Key := [(key2661, -6), (key2696, -18), (key2776, 6), (key2799, 6), (key2849, 12)]

theorem rowCheck9393 : row9393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9393 := by decide +kernel

theorem rowEval9393 (x : Key → ℝ) : Integer.Sparse.eval row9393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9393, Integer.Sparse.eval_collectBalanced, rawRowCheck9393]

def rawRow9394 : Integer.Sparse Key := [(key2696, -6), (key2661, -6), (key2696, -6), (key2696, -6), (key2799, 2), (key2849, 2), (key2849, 2), (key2776, 2), (key2849, 2), (key2849, 2), (key2776, 2), (key2776, 2), (key2799, 2), (key2799, 2), (key2849, 2), (key2849, 2)]

theorem rawRowCheck9394 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form3 = rawRow9394 := by decide +kernel

def row9394 : Integer.Sparse Key := [(key2661, -6), (key2696, -18), (key2776, 6), (key2799, 6), (key2849, 12)]

theorem rowCheck9394 : row9394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9394 := by decide +kernel

theorem rowEval9394 (x : Key → ℝ) : Integer.Sparse.eval row9394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9394, Integer.Sparse.eval_collectBalanced, rawRowCheck9394]

def rawRow9395 : Integer.Sparse Key := [(key2696, -6), (key2696, -6), (key2661, -6), (key2696, -6), (key2849, 2), (key2799, 2), (key2849, 2), (key2849, 2), (key2776, 2), (key2849, 2), (key2799, 2), (key2849, 2), (key2776, 2), (key2849, 2), (key2776, 2), (key2799, 2)]

theorem rawRowCheck9395 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form3 = rawRow9395 := by decide +kernel

def row9395 : Integer.Sparse Key := [(key2661, -6), (key2696, -18), (key2776, 6), (key2799, 6), (key2849, 12)]

theorem rowCheck9395 : row9395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9395 := by decide +kernel

theorem rowEval9395 (x : Key → ℝ) : Integer.Sparse.eval row9395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9395, Integer.Sparse.eval_collectBalanced, rawRowCheck9395]

def rawRow9396 : Integer.Sparse Key := [(key2696, -6), (key2696, -6), (key2696, -6), (key2661, -6), (key2849, 2), (key2849, 2), (key2799, 2), (key2849, 2), (key2849, 2), (key2776, 2), (key2849, 2), (key2799, 2), (key2849, 2), (key2776, 2), (key2799, 2), (key2776, 2)]

theorem rawRowCheck9396 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form3 = rawRow9396 := by decide +kernel

def row9396 : Integer.Sparse Key := [(key2661, -6), (key2696, -18), (key2776, 6), (key2799, 6), (key2849, 12)]

theorem rowCheck9396 : row9396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9396 := by decide +kernel

theorem rowEval9396 (x : Key → ℝ) : Integer.Sparse.eval row9396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9396, Integer.Sparse.eval_collectBalanced, rawRowCheck9396]

def rawRow9397 : Integer.Sparse Key := [(key2372, -6), (key2372, -6), (key2372, -6), (key2385, -6), (key2400, 2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2475, 2), (key2475, 2), (key2475, 2)]

theorem rawRowCheck9397 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form4 = rawRow9397 := by decide +kernel

def row9397 : Integer.Sparse Key := [(key2372, -18), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, 6)]

theorem rowCheck9397 : row9397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9397 := by decide +kernel

theorem rowEval9397 (x : Key → ℝ) : Integer.Sparse.eval row9397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9397, Integer.Sparse.eval_collectBalanced, rawRowCheck9397]

def rawRow9398 : Integer.Sparse Key := [(key2372, -6), (key2372, -6), (key2385, -6), (key2372, -6), (key2466, 2), (key2466, 2), (key2475, 2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2475, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2466, 2)]

theorem rawRowCheck9398 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form4 = rawRow9398 := by decide +kernel

def row9398 : Integer.Sparse Key := [(key2372, -18), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, 6)]

theorem rowCheck9398 : row9398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9398 := by decide +kernel

theorem rowEval9398 (x : Key → ℝ) : Integer.Sparse.eval row9398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9398, Integer.Sparse.eval_collectBalanced, rawRowCheck9398]

def rawRow9399 : Integer.Sparse Key := [(key2372, -6), (key2385, -6), (key2372, -6), (key2372, -6), (key2466, 2), (key2475, 2), (key2466, 2), (key2466, 2), (key2475, 2), (key2400, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2400, 2), (key2466, 2)]

theorem rawRowCheck9399 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form4 = rawRow9399 := by decide +kernel

def row9399 : Integer.Sparse Key := [(key2372, -18), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, 6)]

theorem rowCheck9399 : row9399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9399 := by decide +kernel

theorem rowEval9399 (x : Key → ℝ) : Integer.Sparse.eval row9399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9399, Integer.Sparse.eval_collectBalanced, rawRowCheck9399]

def rawRow9400 : Integer.Sparse Key := [(key2385, -6), (key2372, -6), (key2372, -6), (key2372, -6), (key2475, 2), (key2466, 2), (key2466, 2), (key2475, 2), (key2466, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2400, 2)]

theorem rawRowCheck9400 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form4 = rawRow9400 := by decide +kernel

def row9400 : Integer.Sparse Key := [(key2372, -18), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, 6)]

theorem rowCheck9400 : row9400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9400 := by decide +kernel

theorem rowEval9400 (x : Key → ℝ) : Integer.Sparse.eval row9400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9400, Integer.Sparse.eval_collectBalanced, rawRowCheck9400]

def rawRow9401 : Integer.Sparse Key := [(key2400, -6), (key2400, -6), (key2400, -6), (key2432, -6), (key2372, 2), (key2372, 2), (key2372, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2498, 2), (key2498, 2)]

theorem rawRowCheck9401 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow9401 := by decide +kernel

def row9401 : Integer.Sparse Key := [(key2372, 6), (key2400, -18), (key2432, -6), (key2466, 12), (key2498, 6)]

theorem rowCheck9401 : row9401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9401 := by decide +kernel

theorem rowEval9401 (x : Key → ℝ) : Integer.Sparse.eval row9401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9401, Integer.Sparse.eval_collectBalanced, rawRowCheck9401]

def rawRow9402 : Integer.Sparse Key := [(key2400, -6), (key2400, -6), (key2432, -6), (key2400, -6), (key2466, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2372, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2466, 2)]

theorem rawRowCheck9402 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form4 = rawRow9402 := by decide +kernel

def row9402 : Integer.Sparse Key := [(key2372, 6), (key2400, -18), (key2432, -6), (key2466, 12), (key2498, 6)]

theorem rowCheck9402 : row9402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9402 := by decide +kernel

theorem rowEval9402 (x : Key → ℝ) : Integer.Sparse.eval row9402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9402, Integer.Sparse.eval_collectBalanced, rawRowCheck9402]

def rawRow9403 : Integer.Sparse Key := [(key2400, -6), (key2432, -6), (key2400, -6), (key2400, -6), (key2466, 2), (key2498, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2466, 2), (key2372, 2), (key2466, 2)]

theorem rawRowCheck9403 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form4 = rawRow9403 := by decide +kernel

def row9403 : Integer.Sparse Key := [(key2372, 6), (key2400, -18), (key2432, -6), (key2466, 12), (key2498, 6)]

theorem rowCheck9403 : row9403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9403 := by decide +kernel

theorem rowEval9403 (x : Key → ℝ) : Integer.Sparse.eval row9403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9403, Integer.Sparse.eval_collectBalanced, rawRowCheck9403]

def rawRow9404 : Integer.Sparse Key := [(key2432, -6), (key2400, -6), (key2400, -6), (key2400, -6), (key2498, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2466, 2), (key2372, 2)]

theorem rawRowCheck9404 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form4 = rawRow9404 := by decide +kernel

def row9404 : Integer.Sparse Key := [(key2372, 6), (key2400, -18), (key2432, -6), (key2466, 12), (key2498, 6)]

theorem rowCheck9404 : row9404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9404 := by decide +kernel

theorem rowEval9404 (x : Key → ℝ) : Integer.Sparse.eval row9404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck9404, Integer.Sparse.eval_collectBalanced, rawRowCheck9404]

def rawRow9405 : Integer.Sparse Key := [(key2665, -2), (key2665, -2), (key2665, -2), (key2780, -2), (key2780, -2), (key2780, -2), (key2780, -2), (key2780, -2), (key2780, -2), (key2789, -2), (key2789, -2), (key2789, -2), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1), (key2855, 1), (key2855, 1), (key2855, 1), (key2855, 1)]

theorem rawRowCheck9405 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form5 = rawRow9405 := by decide +kernel

def row9405 : Integer.Sparse Key := [(key2665, -6), (key2700, 6), (key2780, -12), (key2789, -6), (key2803, 6), (key2853, 6), (key2855, 6)]

theorem rowCheck9405 : row9405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9405 := by decide +kernel

theorem rowEval9405 (x : Key → ℝ) : Integer.Sparse.eval row9405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9405, Integer.Sparse.eval_collectBalanced, rawRowCheck9405]

def rawRow9406 : Integer.Sparse Key := [(key2780, -2), (key2780, -2), (key2789, -2), (key2665, -2), (key2665, -2), (key2780, -2), (key2780, -2), (key2789, -2), (key2789, -2), (key2665, -2), (key2780, -2), (key2780, -2), (key2803, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1), (key2700, 1), (key2700, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1), (key2700, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2855, 1), (key2855, 1), (key2700, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2853, 1), (key2853, 1)]

theorem rawRowCheck9406 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form5 = rawRow9406 := by decide +kernel

def row9406 : Integer.Sparse Key := [(key2665, -6), (key2700, 6), (key2780, -12), (key2789, -6), (key2803, 6), (key2853, 6), (key2855, 6)]

theorem rowCheck9406 : row9406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9406 := by decide +kernel

theorem rowEval9406 (x : Key → ℝ) : Integer.Sparse.eval row9406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9406, Integer.Sparse.eval_collectBalanced, rawRowCheck9406]

def rawRow9407 : Integer.Sparse Key := [(key2780, -2), (key2789, -2), (key2780, -2), (key2780, -2), (key2789, -2), (key2665, -2), (key2789, -2), (key2665, -2), (key2780, -2), (key2780, -2), (key2665, -2), (key2780, -2), (key2853, 1), (key2855, 1), (key2803, 1), (key2855, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2700, 1), (key2855, 1), (key2700, 1), (key2853, 1), (key2803, 1), (key2855, 1), (key2700, 1), (key2855, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2853, 1), (key2700, 1), (key2853, 1), (key2700, 1), (key2803, 1)]

theorem rawRowCheck9407 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form5 = rawRow9407 := by decide +kernel

def row9407 : Integer.Sparse Key := [(key2665, -6), (key2700, 6), (key2780, -12), (key2789, -6), (key2803, 6), (key2853, 6), (key2855, 6)]

theorem rowCheck9407 : row9407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9407 := by decide +kernel

theorem rowEval9407 (x : Key → ℝ) : Integer.Sparse.eval row9407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9407, Integer.Sparse.eval_collectBalanced, rawRowCheck9407]

def rawRow9408 : Integer.Sparse Key := [(key2789, -2), (key2780, -2), (key2780, -2), (key2789, -2), (key2780, -2), (key2789, -2), (key2665, -2), (key2780, -2), (key2665, -2), (key2780, -2), (key2780, -2), (key2665, -2), (key2855, 1), (key2853, 1), (key2855, 1), (key2803, 1), (key2853, 1), (key2803, 1), (key2855, 1), (key2853, 1), (key2855, 1), (key2700, 1), (key2853, 1), (key2700, 1), (key2855, 1), (key2803, 1), (key2855, 1), (key2700, 1), (key2803, 1), (key2700, 1), (key2853, 1), (key2803, 1), (key2853, 1), (key2700, 1), (key2803, 1), (key2700, 1)]

theorem rawRowCheck9408 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form5 = rawRow9408 := by decide +kernel

def row9408 : Integer.Sparse Key := [(key2665, -6), (key2700, 6), (key2780, -12), (key2789, -6), (key2803, 6), (key2853, 6), (key2855, 6)]

theorem rowCheck9408 : row9408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9408 := by decide +kernel

theorem rowEval9408 (x : Key → ℝ) : Integer.Sparse.eval row9408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9408, Integer.Sparse.eval_collectBalanced, rawRowCheck9408]

def rawRow9409 : Integer.Sparse Key := [(key2610, -2), (key2610, -2), (key2610, -2), (key2803, -2), (key2803, -2), (key2803, -2), (key2803, -2), (key2803, -2), (key2803, -2), (key2824, -2), (key2824, -2), (key2824, -2), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1), (key2865, 1), (key2865, 1), (key2865, 1), (key2865, 1)]

theorem rawRowCheck9409 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form5 = rawRow9409 := by decide +kernel

def row9409 : Integer.Sparse Key := [(key2610, -6), (key2626, 6), (key2780, 6), (key2803, -12), (key2824, -6), (key2853, 6), (key2865, 6)]

theorem rowCheck9409 : row9409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9409 := by decide +kernel

theorem rowEval9409 (x : Key → ℝ) : Integer.Sparse.eval row9409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9409, Integer.Sparse.eval_collectBalanced, rawRowCheck9409]

def rawRow9410 : Integer.Sparse Key := [(key2803, -2), (key2803, -2), (key2824, -2), (key2610, -2), (key2610, -2), (key2803, -2), (key2803, -2), (key2824, -2), (key2824, -2), (key2610, -2), (key2803, -2), (key2803, -2), (key2780, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1), (key2626, 1), (key2626, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1), (key2626, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2865, 1), (key2865, 1), (key2626, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2853, 1), (key2853, 1)]

theorem rawRowCheck9410 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form5 = rawRow9410 := by decide +kernel

def row9410 : Integer.Sparse Key := [(key2610, -6), (key2626, 6), (key2780, 6), (key2803, -12), (key2824, -6), (key2853, 6), (key2865, 6)]

theorem rowCheck9410 : row9410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9410 := by decide +kernel

theorem rowEval9410 (x : Key → ℝ) : Integer.Sparse.eval row9410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9410, Integer.Sparse.eval_collectBalanced, rawRowCheck9410]

def rawRow9411 : Integer.Sparse Key := [(key2803, -2), (key2824, -2), (key2803, -2), (key2803, -2), (key2824, -2), (key2610, -2), (key2824, -2), (key2610, -2), (key2803, -2), (key2803, -2), (key2610, -2), (key2803, -2), (key2853, 1), (key2865, 1), (key2780, 1), (key2865, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2626, 1), (key2865, 1), (key2626, 1), (key2853, 1), (key2780, 1), (key2865, 1), (key2626, 1), (key2865, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2853, 1), (key2626, 1), (key2853, 1), (key2626, 1), (key2780, 1)]

theorem rawRowCheck9411 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form5 = rawRow9411 := by decide +kernel

def row9411 : Integer.Sparse Key := [(key2610, -6), (key2626, 6), (key2780, 6), (key2803, -12), (key2824, -6), (key2853, 6), (key2865, 6)]

theorem rowCheck9411 : row9411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9411 := by decide +kernel

theorem rowEval9411 (x : Key → ℝ) : Integer.Sparse.eval row9411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9411, Integer.Sparse.eval_collectBalanced, rawRowCheck9411]

def rawRow9412 : Integer.Sparse Key := [(key2824, -2), (key2803, -2), (key2803, -2), (key2824, -2), (key2803, -2), (key2824, -2), (key2610, -2), (key2803, -2), (key2610, -2), (key2803, -2), (key2803, -2), (key2610, -2), (key2865, 1), (key2853, 1), (key2865, 1), (key2780, 1), (key2853, 1), (key2780, 1), (key2865, 1), (key2853, 1), (key2865, 1), (key2626, 1), (key2853, 1), (key2626, 1), (key2865, 1), (key2780, 1), (key2865, 1), (key2626, 1), (key2780, 1), (key2626, 1), (key2853, 1), (key2780, 1), (key2853, 1), (key2626, 1), (key2780, 1), (key2626, 1)]

theorem rawRowCheck9412 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form5 = rawRow9412 := by decide +kernel

def row9412 : Integer.Sparse Key := [(key2610, -6), (key2626, 6), (key2780, 6), (key2803, -12), (key2824, -6), (key2853, 6), (key2865, 6)]

theorem rowCheck9412 : row9412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9412 := by decide +kernel

theorem rowEval9412 (x : Key → ℝ) : Integer.Sparse.eval row9412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck9412, Integer.Sparse.eval_collectBalanced, rawRowCheck9412]

def rawRow9413 : Integer.Sparse Key := [(key2368, -24), (key2760, 6), (key2837, 6), (key2837, 6), (key2837, 6)]

theorem rawRowCheck9413 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form6 = rawRow9413 := by decide +kernel

def row9413 : Integer.Sparse Key := [(key2368, -24), (key2760, 6), (key2837, 18)]

theorem rowCheck9413 : row9413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9413 := by decide +kernel

theorem rowEval9413 (x : Key → ℝ) : Integer.Sparse.eval row9413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9413, Integer.Sparse.eval_collectBalanced, rawRowCheck9413]

def rawRow9414 : Integer.Sparse Key := [(key2368, -24), (key2837, 6), (key2760, 6), (key2837, 6), (key2837, 6)]

theorem rawRowCheck9414 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form6 = rawRow9414 := by decide +kernel

def row9414 : Integer.Sparse Key := [(key2368, -24), (key2760, 6), (key2837, 18)]

theorem rowCheck9414 : row9414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9414 := by decide +kernel

theorem rowEval9414 (x : Key → ℝ) : Integer.Sparse.eval row9414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9414, Integer.Sparse.eval_collectBalanced, rawRowCheck9414]

def rawRow9415 : Integer.Sparse Key := [(key2368, -24), (key2837, 6), (key2837, 6), (key2760, 6), (key2837, 6)]

theorem rawRowCheck9415 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form6 = rawRow9415 := by decide +kernel

def row9415 : Integer.Sparse Key := [(key2368, -24), (key2760, 6), (key2837, 18)]

theorem rowCheck9415 : row9415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9415 := by decide +kernel

theorem rowEval9415 (x : Key → ℝ) : Integer.Sparse.eval row9415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9415, Integer.Sparse.eval_collectBalanced, rawRowCheck9415]

def rawRow9416 : Integer.Sparse Key := [(key2368, -24), (key2837, 6), (key2837, 6), (key2837, 6), (key2760, 6)]

theorem rawRowCheck9416 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form6 = rawRow9416 := by decide +kernel

def row9416 : Integer.Sparse Key := [(key2368, -24), (key2760, 6), (key2837, 18)]

theorem rowCheck9416 : row9416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9416 := by decide +kernel

theorem rowEval9416 (x : Key → ℝ) : Integer.Sparse.eval row9416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9416, Integer.Sparse.eval_collectBalanced, rawRowCheck9416]

def rawRow9417 : Integer.Sparse Key := [(key2396, -24), (key2581, 6), (key2837, 6), (key2837, 6), (key2837, 6)]

theorem rawRowCheck9417 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow9417 := by decide +kernel

def row9417 : Integer.Sparse Key := [(key2396, -24), (key2581, 6), (key2837, 18)]

theorem rowCheck9417 : row9417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9417 := by decide +kernel

theorem rowEval9417 (x : Key → ℝ) : Integer.Sparse.eval row9417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9417, Integer.Sparse.eval_collectBalanced, rawRowCheck9417]

def rawRow9418 : Integer.Sparse Key := [(key2396, -24), (key2837, 6), (key2581, 6), (key2837, 6), (key2837, 6)]

theorem rawRowCheck9418 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form6 = rawRow9418 := by decide +kernel

def row9418 : Integer.Sparse Key := [(key2396, -24), (key2581, 6), (key2837, 18)]

theorem rowCheck9418 : row9418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9418 := by decide +kernel

theorem rowEval9418 (x : Key → ℝ) : Integer.Sparse.eval row9418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9418, Integer.Sparse.eval_collectBalanced, rawRowCheck9418]

def rawRow9419 : Integer.Sparse Key := [(key2396, -24), (key2837, 6), (key2837, 6), (key2581, 6), (key2837, 6)]

theorem rawRowCheck9419 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form6 = rawRow9419 := by decide +kernel

def row9419 : Integer.Sparse Key := [(key2396, -24), (key2581, 6), (key2837, 18)]

theorem rowCheck9419 : row9419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9419 := by decide +kernel

theorem rowEval9419 (x : Key → ℝ) : Integer.Sparse.eval row9419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9419, Integer.Sparse.eval_collectBalanced, rawRowCheck9419]

def rawRow9420 : Integer.Sparse Key := [(key2396, -24), (key2837, 6), (key2837, 6), (key2837, 6), (key2581, 6)]

theorem rawRowCheck9420 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form6 = rawRow9420 := by decide +kernel

def row9420 : Integer.Sparse Key := [(key2396, -24), (key2581, 6), (key2837, 18)]

theorem rowCheck9420 : row9420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9420 := by decide +kernel

theorem rowEval9420 (x : Key → ℝ) : Integer.Sparse.eval row9420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9420, Integer.Sparse.eval_collectBalanced, rawRowCheck9420]

def rawRow9421 : Integer.Sparse Key := [(key2610, -2), (key2610, -2), (key2610, -2), (key2626, -2), (key2626, -2), (key2626, -2), (key2626, -2), (key2626, -2), (key2626, -2), (key2635, -2), (key2635, -2), (key2635, -2), (key2665, 2), (key2665, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2789, 2), (key2789, 2)]

theorem rawRowCheck9421 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form7 = rawRow9421 := by decide +kernel

def row9421 : Integer.Sparse Key := [(key2610, -6), (key2626, -12), (key2635, -6), (key2665, 6), (key2780, 12), (key2789, 6)]

theorem rowCheck9421 : row9421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9421 := by decide +kernel

theorem rowEval9421 (x : Key → ℝ) : Integer.Sparse.eval row9421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9421, Integer.Sparse.eval_collectBalanced, rawRowCheck9421]

def rawRow9422 : Integer.Sparse Key := [(key2626, -2), (key2626, -2), (key2635, -2), (key2610, -2), (key2610, -2), (key2626, -2), (key2626, -2), (key2635, -2), (key2635, -2), (key2610, -2), (key2626, -2), (key2626, -2), (key2780, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2780, 2)]

theorem rawRowCheck9422 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form7 = rawRow9422 := by decide +kernel

def row9422 : Integer.Sparse Key := [(key2610, -6), (key2626, -12), (key2635, -6), (key2665, 6), (key2780, 12), (key2789, 6)]

theorem rowCheck9422 : row9422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9422 := by decide +kernel

theorem rowEval9422 (x : Key → ℝ) : Integer.Sparse.eval row9422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9422, Integer.Sparse.eval_collectBalanced, rawRowCheck9422]

def rawRow9423 : Integer.Sparse Key := [(key2626, -2), (key2635, -2), (key2626, -2), (key2626, -2), (key2635, -2), (key2610, -2), (key2635, -2), (key2610, -2), (key2626, -2), (key2626, -2), (key2610, -2), (key2626, -2), (key2780, 2), (key2789, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2665, 2), (key2780, 2)]

theorem rawRowCheck9423 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form7 = rawRow9423 := by decide +kernel

def row9423 : Integer.Sparse Key := [(key2610, -6), (key2626, -12), (key2635, -6), (key2665, 6), (key2780, 12), (key2789, 6)]

theorem rowCheck9423 : row9423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9423 := by decide +kernel

theorem rowEval9423 (x : Key → ℝ) : Integer.Sparse.eval row9423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9423, Integer.Sparse.eval_collectBalanced, rawRowCheck9423]

def rawRow9424 : Integer.Sparse Key := [(key2635, -2), (key2626, -2), (key2626, -2), (key2635, -2), (key2626, -2), (key2635, -2), (key2610, -2), (key2626, -2), (key2610, -2), (key2626, -2), (key2626, -2), (key2610, -2), (key2789, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2665, 2)]

theorem rawRowCheck9424 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form7 = rawRow9424 := by decide +kernel

def row9424 : Integer.Sparse Key := [(key2610, -6), (key2626, -12), (key2635, -6), (key2665, 6), (key2780, 12), (key2789, 6)]

theorem rowCheck9424 : row9424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9424 := by decide +kernel

theorem rowEval9424 (x : Key → ℝ) : Integer.Sparse.eval row9424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9424, Integer.Sparse.eval_collectBalanced, rawRowCheck9424]

def rawRow9425 : Integer.Sparse Key := [(key2665, -2), (key2665, -2), (key2665, -2), (key2700, -2), (key2700, -2), (key2700, -2), (key2700, -2), (key2700, -2), (key2700, -2), (key2721, -2), (key2721, -2), (key2721, -2), (key2610, 2), (key2610, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2824, 2), (key2824, 2)]

theorem rawRowCheck9425 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow9425 := by decide +kernel

def row9425 : Integer.Sparse Key := [(key2610, 6), (key2665, -6), (key2700, -12), (key2721, -6), (key2803, 12), (key2824, 6)]

theorem rowCheck9425 : row9425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9425 := by decide +kernel

theorem rowEval9425 (x : Key → ℝ) : Integer.Sparse.eval row9425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9425, Integer.Sparse.eval_collectBalanced, rawRowCheck9425]

def rawRow9426 : Integer.Sparse Key := [(key2700, -2), (key2700, -2), (key2721, -2), (key2665, -2), (key2665, -2), (key2700, -2), (key2700, -2), (key2721, -2), (key2721, -2), (key2665, -2), (key2700, -2), (key2700, -2), (key2803, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2803, 2)]

theorem rawRowCheck9426 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form7 = rawRow9426 := by decide +kernel

def row9426 : Integer.Sparse Key := [(key2610, 6), (key2665, -6), (key2700, -12), (key2721, -6), (key2803, 12), (key2824, 6)]

theorem rowCheck9426 : row9426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9426 := by decide +kernel

theorem rowEval9426 (x : Key → ℝ) : Integer.Sparse.eval row9426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9426, Integer.Sparse.eval_collectBalanced, rawRowCheck9426]

def rawRow9427 : Integer.Sparse Key := [(key2700, -2), (key2721, -2), (key2700, -2), (key2700, -2), (key2721, -2), (key2665, -2), (key2721, -2), (key2665, -2), (key2700, -2), (key2700, -2), (key2665, -2), (key2700, -2), (key2803, 2), (key2824, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2610, 2), (key2803, 2)]

theorem rawRowCheck9427 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form7 = rawRow9427 := by decide +kernel

def row9427 : Integer.Sparse Key := [(key2610, 6), (key2665, -6), (key2700, -12), (key2721, -6), (key2803, 12), (key2824, 6)]

theorem rowCheck9427 : row9427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9427 := by decide +kernel

theorem rowEval9427 (x : Key → ℝ) : Integer.Sparse.eval row9427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9427, Integer.Sparse.eval_collectBalanced, rawRowCheck9427]

def rawRow9428 : Integer.Sparse Key := [(key2721, -2), (key2700, -2), (key2700, -2), (key2721, -2), (key2700, -2), (key2721, -2), (key2665, -2), (key2700, -2), (key2665, -2), (key2700, -2), (key2700, -2), (key2665, -2), (key2824, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2610, 2)]

theorem rawRowCheck9428 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form7 = rawRow9428 := by decide +kernel

def row9428 : Integer.Sparse Key := [(key2610, 6), (key2665, -6), (key2700, -12), (key2721, -6), (key2803, 12), (key2824, 6)]

theorem rowCheck9428 : row9428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9428 := by decide +kernel

theorem rowEval9428 (x : Key → ℝ) : Integer.Sparse.eval row9428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck9428, Integer.Sparse.eval_collectBalanced, rawRowCheck9428]

def rawRow9429 : Integer.Sparse Key := [(key1388, -2), (key1388, -2), (key1388, -2), (key1543, -2), (key1543, -2), (key1543, -2), (key1543, -2), (key1543, -2), (key1543, -2), (key1553, -2), (key1553, -2), (key1553, -2), (key1421, 1), (key1421, 1), (key1421, 1), (key1421, 1), (key1421, 1), (key1421, 1), (key1570, 1), (key1570, 1), (key1570, 1), (key1570, 1), (key1570, 1), (key1570, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1621, 1), (key1621, 1), (key1621, 1), (key1621, 1), (key1621, 1), (key1621, 1)]

theorem rawRowCheck9429 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form8 = rawRow9429 := by decide +kernel

def row9429 : Integer.Sparse Key := [(key1388, -6), (key1421, 6), (key1543, -12), (key1553, -6), (key1570, 6), (key1619, 6), (key1621, 6)]

theorem rowCheck9429 : row9429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9429 := by decide +kernel

theorem rowEval9429 (x : Key → ℝ) : Integer.Sparse.eval row9429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9429, Integer.Sparse.eval_collectBalanced, rawRowCheck9429]

def rawRow9430 : Integer.Sparse Key := [(key1543, -2), (key1543, -2), (key1553, -2), (key1388, -2), (key1388, -2), (key1543, -2), (key1543, -2), (key1553, -2), (key1553, -2), (key1388, -2), (key1543, -2), (key1543, -2), (key1570, 1), (key1570, 1), (key1619, 1), (key1619, 1), (key1621, 1), (key1621, 1), (key1421, 1), (key1421, 1), (key1619, 1), (key1619, 1), (key1621, 1), (key1621, 1), (key1421, 1), (key1421, 1), (key1570, 1), (key1570, 1), (key1621, 1), (key1621, 1), (key1421, 1), (key1421, 1), (key1570, 1), (key1570, 1), (key1619, 1), (key1619, 1)]

theorem rawRowCheck9430 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form8 = rawRow9430 := by decide +kernel

def row9430 : Integer.Sparse Key := [(key1388, -6), (key1421, 6), (key1543, -12), (key1553, -6), (key1570, 6), (key1619, 6), (key1621, 6)]

theorem rowCheck9430 : row9430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9430 := by decide +kernel

theorem rowEval9430 (x : Key → ℝ) : Integer.Sparse.eval row9430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9430, Integer.Sparse.eval_collectBalanced, rawRowCheck9430]

def rawRow9431 : Integer.Sparse Key := [(key1543, -2), (key1553, -2), (key1543, -2), (key1543, -2), (key1553, -2), (key1388, -2), (key1553, -2), (key1388, -2), (key1543, -2), (key1543, -2), (key1388, -2), (key1543, -2), (key1619, 1), (key1621, 1), (key1570, 1), (key1621, 1), (key1570, 1), (key1619, 1), (key1619, 1), (key1621, 1), (key1421, 1), (key1621, 1), (key1421, 1), (key1619, 1), (key1570, 1), (key1621, 1), (key1421, 1), (key1621, 1), (key1421, 1), (key1570, 1), (key1570, 1), (key1619, 1), (key1421, 1), (key1619, 1), (key1421, 1), (key1570, 1)]

theorem rawRowCheck9431 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form8 = rawRow9431 := by decide +kernel

def row9431 : Integer.Sparse Key := [(key1388, -6), (key1421, 6), (key1543, -12), (key1553, -6), (key1570, 6), (key1619, 6), (key1621, 6)]

theorem rowCheck9431 : row9431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9431 := by decide +kernel

theorem rowEval9431 (x : Key → ℝ) : Integer.Sparse.eval row9431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9431, Integer.Sparse.eval_collectBalanced, rawRowCheck9431]

def rawRow9432 : Integer.Sparse Key := [(key1553, -2), (key1543, -2), (key1543, -2), (key1553, -2), (key1543, -2), (key1553, -2), (key1388, -2), (key1543, -2), (key1388, -2), (key1543, -2), (key1543, -2), (key1388, -2), (key1621, 1), (key1619, 1), (key1621, 1), (key1570, 1), (key1619, 1), (key1570, 1), (key1621, 1), (key1619, 1), (key1621, 1), (key1421, 1), (key1619, 1), (key1421, 1), (key1621, 1), (key1570, 1), (key1621, 1), (key1421, 1), (key1570, 1), (key1421, 1), (key1619, 1), (key1570, 1), (key1619, 1), (key1421, 1), (key1570, 1), (key1421, 1)]

theorem rawRowCheck9432 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form8 = rawRow9432 := by decide +kernel

def row9432 : Integer.Sparse Key := [(key1388, -6), (key1421, 6), (key1543, -12), (key1553, -6), (key1570, 6), (key1619, 6), (key1621, 6)]

theorem rowCheck9432 : row9432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9432 := by decide +kernel

theorem rowEval9432 (x : Key → ℝ) : Integer.Sparse.eval row9432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9432, Integer.Sparse.eval_collectBalanced, rawRowCheck9432]

def rawRow9433 : Integer.Sparse Key := [(key1293, -2), (key1293, -2), (key1293, -2), (key1570, -2), (key1570, -2), (key1570, -2), (key1570, -2), (key1570, -2), (key1570, -2), (key1590, -2), (key1590, -2), (key1590, -2), (key1313, 1), (key1313, 1), (key1313, 1), (key1313, 1), (key1313, 1), (key1313, 1), (key1543, 1), (key1543, 1), (key1543, 1), (key1543, 1), (key1543, 1), (key1543, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1630, 1), (key1630, 1), (key1630, 1), (key1630, 1), (key1630, 1), (key1630, 1)]

theorem rawRowCheck9433 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form8 = rawRow9433 := by decide +kernel

def row9433 : Integer.Sparse Key := [(key1293, -6), (key1313, 6), (key1543, 6), (key1570, -12), (key1590, -6), (key1619, 6), (key1630, 6)]

theorem rowCheck9433 : row9433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9433 := by decide +kernel

theorem rowEval9433 (x : Key → ℝ) : Integer.Sparse.eval row9433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9433, Integer.Sparse.eval_collectBalanced, rawRowCheck9433]

def rawRow9434 : Integer.Sparse Key := [(key1570, -2), (key1570, -2), (key1590, -2), (key1293, -2), (key1293, -2), (key1570, -2), (key1570, -2), (key1590, -2), (key1590, -2), (key1293, -2), (key1570, -2), (key1570, -2), (key1543, 1), (key1543, 1), (key1619, 1), (key1619, 1), (key1630, 1), (key1630, 1), (key1313, 1), (key1313, 1), (key1619, 1), (key1619, 1), (key1630, 1), (key1630, 1), (key1313, 1), (key1313, 1), (key1543, 1), (key1543, 1), (key1630, 1), (key1630, 1), (key1313, 1), (key1313, 1), (key1543, 1), (key1543, 1), (key1619, 1), (key1619, 1)]

theorem rawRowCheck9434 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form8 = rawRow9434 := by decide +kernel

def row9434 : Integer.Sparse Key := [(key1293, -6), (key1313, 6), (key1543, 6), (key1570, -12), (key1590, -6), (key1619, 6), (key1630, 6)]

theorem rowCheck9434 : row9434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9434 := by decide +kernel

theorem rowEval9434 (x : Key → ℝ) : Integer.Sparse.eval row9434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9434, Integer.Sparse.eval_collectBalanced, rawRowCheck9434]

def rawRow9435 : Integer.Sparse Key := [(key1570, -2), (key1590, -2), (key1570, -2), (key1570, -2), (key1590, -2), (key1293, -2), (key1590, -2), (key1293, -2), (key1570, -2), (key1570, -2), (key1293, -2), (key1570, -2), (key1619, 1), (key1630, 1), (key1543, 1), (key1630, 1), (key1543, 1), (key1619, 1), (key1619, 1), (key1630, 1), (key1313, 1), (key1630, 1), (key1313, 1), (key1619, 1), (key1543, 1), (key1630, 1), (key1313, 1), (key1630, 1), (key1313, 1), (key1543, 1), (key1543, 1), (key1619, 1), (key1313, 1), (key1619, 1), (key1313, 1), (key1543, 1)]

theorem rawRowCheck9435 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form8 = rawRow9435 := by decide +kernel

def row9435 : Integer.Sparse Key := [(key1293, -6), (key1313, 6), (key1543, 6), (key1570, -12), (key1590, -6), (key1619, 6), (key1630, 6)]

theorem rowCheck9435 : row9435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9435 := by decide +kernel

theorem rowEval9435 (x : Key → ℝ) : Integer.Sparse.eval row9435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9435, Integer.Sparse.eval_collectBalanced, rawRowCheck9435]

def rawRow9436 : Integer.Sparse Key := [(key1590, -2), (key1570, -2), (key1570, -2), (key1590, -2), (key1570, -2), (key1590, -2), (key1293, -2), (key1570, -2), (key1293, -2), (key1570, -2), (key1570, -2), (key1293, -2), (key1630, 1), (key1619, 1), (key1630, 1), (key1543, 1), (key1619, 1), (key1543, 1), (key1630, 1), (key1619, 1), (key1630, 1), (key1313, 1), (key1619, 1), (key1313, 1), (key1630, 1), (key1543, 1), (key1630, 1), (key1313, 1), (key1543, 1), (key1313, 1), (key1619, 1), (key1543, 1), (key1619, 1), (key1313, 1), (key1543, 1), (key1313, 1)]

theorem rawRowCheck9436 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form8 = rawRow9436 := by decide +kernel

def row9436 : Integer.Sparse Key := [(key1293, -6), (key1313, 6), (key1543, 6), (key1570, -12), (key1590, -6), (key1619, 6), (key1630, 6)]

theorem rowCheck9436 : row9436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9436 := by decide +kernel

theorem rowEval9436 (x : Key → ℝ) : Integer.Sparse.eval row9436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck9436, Integer.Sparse.eval_collectBalanced, rawRowCheck9436]

def rawRow9437 : Integer.Sparse Key := [(key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1), (key2855, 1), (key2855, 1), (key2855, 1), (key2855, 1), (key2721, -2), (key2721, -2), (key2721, -2), (key2824, -2), (key2824, -2), (key2824, -2), (key2865, -2), (key2865, -2), (key2865, -2), (key2865, -2), (key2865, -2), (key2865, -2)]

theorem rawRowCheck9437 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form9 = rawRow9437 := by decide +kernel

def row9437 : Integer.Sparse Key := [(key2700, 6), (key2721, -6), (key2803, 6), (key2824, -6), (key2853, 6), (key2855, 6), (key2865, -12)]

theorem rowCheck9437 : row9437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9437 := by decide +kernel

theorem rowEval9437 (x : Key → ℝ) : Integer.Sparse.eval row9437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9437, Integer.Sparse.eval_collectBalanced, rawRowCheck9437]

def rawRow9438 : Integer.Sparse Key := [(key2803, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1), (key2700, 1), (key2700, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1), (key2700, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2855, 1), (key2855, 1), (key2700, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2824, -2), (key2865, -2), (key2865, -2), (key2721, -2), (key2865, -2), (key2865, -2), (key2721, -2), (key2721, -2), (key2824, -2), (key2824, -2), (key2865, -2), (key2865, -2)]

theorem rawRowCheck9438 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form9 = rawRow9438 := by decide +kernel

def row9438 : Integer.Sparse Key := [(key2700, 6), (key2721, -6), (key2803, 6), (key2824, -6), (key2853, 6), (key2855, 6), (key2865, -12)]

theorem rowCheck9438 : row9438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9438 := by decide +kernel

theorem rowEval9438 (x : Key → ℝ) : Integer.Sparse.eval row9438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9438, Integer.Sparse.eval_collectBalanced, rawRowCheck9438]

def rawRow9439 : Integer.Sparse Key := [(key2853, 1), (key2855, 1), (key2803, 1), (key2855, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2700, 1), (key2855, 1), (key2700, 1), (key2853, 1), (key2803, 1), (key2855, 1), (key2700, 1), (key2855, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2853, 1), (key2700, 1), (key2853, 1), (key2700, 1), (key2803, 1), (key2865, -2), (key2824, -2), (key2865, -2), (key2865, -2), (key2721, -2), (key2865, -2), (key2824, -2), (key2865, -2), (key2721, -2), (key2865, -2), (key2721, -2), (key2824, -2)]

theorem rawRowCheck9439 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form9 = rawRow9439 := by decide +kernel

def row9439 : Integer.Sparse Key := [(key2700, 6), (key2721, -6), (key2803, 6), (key2824, -6), (key2853, 6), (key2855, 6), (key2865, -12)]

theorem rowCheck9439 : row9439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9439 := by decide +kernel

theorem rowEval9439 (x : Key → ℝ) : Integer.Sparse.eval row9439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9439, Integer.Sparse.eval_collectBalanced, rawRowCheck9439]

def rawRow9440 : Integer.Sparse Key := [(key2855, 1), (key2853, 1), (key2855, 1), (key2803, 1), (key2853, 1), (key2803, 1), (key2855, 1), (key2853, 1), (key2855, 1), (key2700, 1), (key2853, 1), (key2700, 1), (key2855, 1), (key2803, 1), (key2855, 1), (key2700, 1), (key2803, 1), (key2700, 1), (key2853, 1), (key2803, 1), (key2853, 1), (key2700, 1), (key2803, 1), (key2700, 1), (key2865, -2), (key2865, -2), (key2824, -2), (key2865, -2), (key2865, -2), (key2721, -2), (key2865, -2), (key2824, -2), (key2865, -2), (key2721, -2), (key2824, -2), (key2721, -2)]

theorem rawRowCheck9440 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form9 = rawRow9440 := by decide +kernel

def row9440 : Integer.Sparse Key := [(key2700, 6), (key2721, -6), (key2803, 6), (key2824, -6), (key2853, 6), (key2855, 6), (key2865, -12)]

theorem rowCheck9440 : row9440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9440 := by decide +kernel

theorem rowEval9440 (x : Key → ℝ) : Integer.Sparse.eval row9440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9440, Integer.Sparse.eval_collectBalanced, rawRowCheck9440]

def rawRow9441 : Integer.Sparse Key := [(key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1), (key2865, 1), (key2865, 1), (key2865, 1), (key2865, 1), (key2635, -2), (key2635, -2), (key2635, -2), (key2789, -2), (key2789, -2), (key2789, -2), (key2855, -2), (key2855, -2), (key2855, -2), (key2855, -2), (key2855, -2), (key2855, -2)]

theorem rawRowCheck9441 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form9 = rawRow9441 := by decide +kernel

def row9441 : Integer.Sparse Key := [(key2626, 6), (key2635, -6), (key2780, 6), (key2789, -6), (key2853, 6), (key2855, -12), (key2865, 6)]

theorem rowCheck9441 : row9441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9441 := by decide +kernel

theorem rowEval9441 (x : Key → ℝ) : Integer.Sparse.eval row9441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9441, Integer.Sparse.eval_collectBalanced, rawRowCheck9441]

def rawRow9442 : Integer.Sparse Key := [(key2780, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1), (key2626, 1), (key2626, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1), (key2626, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2865, 1), (key2865, 1), (key2626, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2789, -2), (key2855, -2), (key2855, -2), (key2635, -2), (key2855, -2), (key2855, -2), (key2635, -2), (key2635, -2), (key2789, -2), (key2789, -2), (key2855, -2), (key2855, -2)]

theorem rawRowCheck9442 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form9 = rawRow9442 := by decide +kernel

def row9442 : Integer.Sparse Key := [(key2626, 6), (key2635, -6), (key2780, 6), (key2789, -6), (key2853, 6), (key2855, -12), (key2865, 6)]

theorem rowCheck9442 : row9442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9442 := by decide +kernel

theorem rowEval9442 (x : Key → ℝ) : Integer.Sparse.eval row9442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9442, Integer.Sparse.eval_collectBalanced, rawRowCheck9442]

def rawRow9443 : Integer.Sparse Key := [(key2853, 1), (key2865, 1), (key2780, 1), (key2865, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2626, 1), (key2865, 1), (key2626, 1), (key2853, 1), (key2780, 1), (key2865, 1), (key2626, 1), (key2865, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2853, 1), (key2626, 1), (key2853, 1), (key2626, 1), (key2780, 1), (key2855, -2), (key2789, -2), (key2855, -2), (key2855, -2), (key2635, -2), (key2855, -2), (key2789, -2), (key2855, -2), (key2635, -2), (key2855, -2), (key2635, -2), (key2789, -2)]

theorem rawRowCheck9443 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form9 = rawRow9443 := by decide +kernel

def row9443 : Integer.Sparse Key := [(key2626, 6), (key2635, -6), (key2780, 6), (key2789, -6), (key2853, 6), (key2855, -12), (key2865, 6)]

theorem rowCheck9443 : row9443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9443 := by decide +kernel

theorem rowEval9443 (x : Key → ℝ) : Integer.Sparse.eval row9443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9443, Integer.Sparse.eval_collectBalanced, rawRowCheck9443]

def rawRow9444 : Integer.Sparse Key := [(key2865, 1), (key2853, 1), (key2865, 1), (key2780, 1), (key2853, 1), (key2780, 1), (key2865, 1), (key2853, 1), (key2865, 1), (key2626, 1), (key2853, 1), (key2626, 1), (key2865, 1), (key2780, 1), (key2865, 1), (key2626, 1), (key2780, 1), (key2626, 1), (key2853, 1), (key2780, 1), (key2853, 1), (key2626, 1), (key2780, 1), (key2626, 1), (key2855, -2), (key2855, -2), (key2789, -2), (key2855, -2), (key2855, -2), (key2635, -2), (key2855, -2), (key2789, -2), (key2855, -2), (key2635, -2), (key2789, -2), (key2635, -2)]

theorem rawRowCheck9444 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form9 = rawRow9444 := by decide +kernel

def row9444 : Integer.Sparse Key := [(key2626, 6), (key2635, -6), (key2780, 6), (key2789, -6), (key2853, 6), (key2855, -12), (key2865, 6)]

theorem rowCheck9444 : row9444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9444 := by decide +kernel

theorem rowEval9444 (x : Key → ℝ) : Integer.Sparse.eval row9444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck9444, Integer.Sparse.eval_collectBalanced, rawRowCheck9444]

def rawRow9445 : Integer.Sparse Key := [(key1382, -6), (key1537, -6), (key1537, -6), (key1537, -6), (key1415, 2), (key1415, 2), (key1415, 2), (key1564, 2), (key1564, 2), (key1564, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2)]

theorem rawRowCheck9445 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form10 = rawRow9445 := by decide +kernel

def row9445 : Integer.Sparse Key := [(key1382, -6), (key1415, 6), (key1537, -18), (key1564, 6), (key1613, 12)]

theorem rowCheck9445 : row9445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9445 := by decide +kernel

theorem rowEval9445 (x : Key → ℝ) : Integer.Sparse.eval row9445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9445, Integer.Sparse.eval_collectBalanced, rawRowCheck9445]

def rawRow9446 : Integer.Sparse Key := [(key1537, -6), (key1382, -6), (key1537, -6), (key1537, -6), (key1564, 2), (key1613, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1613, 2), (key1415, 2), (key1415, 2), (key1564, 2), (key1564, 2), (key1613, 2), (key1613, 2)]

theorem rawRowCheck9446 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form10 = rawRow9446 := by decide +kernel

def row9446 : Integer.Sparse Key := [(key1382, -6), (key1415, 6), (key1537, -18), (key1564, 6), (key1613, 12)]

theorem rowCheck9446 : row9446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9446 := by decide +kernel

theorem rowEval9446 (x : Key → ℝ) : Integer.Sparse.eval row9446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9446, Integer.Sparse.eval_collectBalanced, rawRowCheck9446]

def rawRow9447 : Integer.Sparse Key := [(key1537, -6), (key1537, -6), (key1382, -6), (key1537, -6), (key1613, 2), (key1564, 2), (key1613, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1564, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1415, 2), (key1564, 2)]

theorem rawRowCheck9447 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form10 = rawRow9447 := by decide +kernel

def row9447 : Integer.Sparse Key := [(key1382, -6), (key1415, 6), (key1537, -18), (key1564, 6), (key1613, 12)]

theorem rowCheck9447 : row9447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9447 := by decide +kernel

theorem rowEval9447 (x : Key → ℝ) : Integer.Sparse.eval row9447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9447, Integer.Sparse.eval_collectBalanced, rawRowCheck9447]

def rawRow9448 : Integer.Sparse Key := [(key1537, -6), (key1537, -6), (key1537, -6), (key1382, -6), (key1613, 2), (key1613, 2), (key1564, 2), (key1613, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1564, 2), (key1613, 2), (key1415, 2), (key1564, 2), (key1415, 2)]

theorem rawRowCheck9448 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form10 = rawRow9448 := by decide +kernel

def row9448 : Integer.Sparse Key := [(key1382, -6), (key1415, 6), (key1537, -18), (key1564, 6), (key1613, 12)]

theorem rowCheck9448 : row9448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9448 := by decide +kernel

theorem rowEval9448 (x : Key → ℝ) : Integer.Sparse.eval row9448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9448, Integer.Sparse.eval_collectBalanced, rawRowCheck9448]

def rawRow9449 : Integer.Sparse Key := [(key1287, -6), (key1564, -6), (key1564, -6), (key1564, -6), (key1307, 2), (key1307, 2), (key1307, 2), (key1537, 2), (key1537, 2), (key1537, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2)]

theorem rawRowCheck9449 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow9449 := by decide +kernel

def row9449 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1537, 6), (key1564, -18), (key1613, 12)]

theorem rowCheck9449 : row9449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9449 := by decide +kernel

theorem rowEval9449 (x : Key → ℝ) : Integer.Sparse.eval row9449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9449, Integer.Sparse.eval_collectBalanced, rawRowCheck9449]

def rawRow9450 : Integer.Sparse Key := [(key1564, -6), (key1287, -6), (key1564, -6), (key1564, -6), (key1537, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1307, 2), (key1537, 2), (key1537, 2), (key1613, 2), (key1613, 2)]

theorem rawRowCheck9450 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form10 = rawRow9450 := by decide +kernel

def row9450 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1537, 6), (key1564, -18), (key1613, 12)]

theorem rowCheck9450 : row9450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9450 := by decide +kernel

theorem rowEval9450 (x : Key → ℝ) : Integer.Sparse.eval row9450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9450, Integer.Sparse.eval_collectBalanced, rawRowCheck9450]

def rawRow9451 : Integer.Sparse Key := [(key1564, -6), (key1564, -6), (key1287, -6), (key1564, -6), (key1613, 2), (key1537, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1537, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1307, 2), (key1537, 2)]

theorem rawRowCheck9451 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form10 = rawRow9451 := by decide +kernel

def row9451 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1537, 6), (key1564, -18), (key1613, 12)]

theorem rowCheck9451 : row9451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9451 := by decide +kernel

theorem rowEval9451 (x : Key → ℝ) : Integer.Sparse.eval row9451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9451, Integer.Sparse.eval_collectBalanced, rawRowCheck9451]

def rawRow9452 : Integer.Sparse Key := [(key1564, -6), (key1564, -6), (key1564, -6), (key1287, -6), (key1613, 2), (key1613, 2), (key1537, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1537, 2), (key1613, 2), (key1307, 2), (key1537, 2), (key1307, 2)]

theorem rawRowCheck9452 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form10 = rawRow9452 := by decide +kernel

def row9452 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1537, 6), (key1564, -18), (key1613, 12)]

theorem rowCheck9452 : row9452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9452 := by decide +kernel

theorem rowEval9452 (x : Key → ℝ) : Integer.Sparse.eval row9452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9452, Integer.Sparse.eval_collectBalanced, rawRowCheck9452]

def rawRow9453 : Integer.Sparse Key := [(key2369, 6), (key2369, 6), (key2369, 6), (key2384, 6), (key2431, -6), (key2497, -6), (key2497, -6), (key2497, -6)]

theorem rawRowCheck9453 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form11 = rawRow9453 := by decide +kernel

def row9453 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2431, -6), (key2497, -18)]

theorem rowCheck9453 : row9453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9453 := by decide +kernel

theorem rowEval9453 (x : Key → ℝ) : Integer.Sparse.eval row9453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9453, Integer.Sparse.eval_collectBalanced, rawRowCheck9453]

def rawRow9454 : Integer.Sparse Key := [(key2369, 6), (key2369, 6), (key2384, 6), (key2369, 6), (key2497, -6), (key2431, -6), (key2497, -6), (key2497, -6)]

theorem rawRowCheck9454 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form11 = rawRow9454 := by decide +kernel

def row9454 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2431, -6), (key2497, -18)]

theorem rowCheck9454 : row9454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9454 := by decide +kernel

theorem rowEval9454 (x : Key → ℝ) : Integer.Sparse.eval row9454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9454, Integer.Sparse.eval_collectBalanced, rawRowCheck9454]

def rawRow9455 : Integer.Sparse Key := [(key2369, 6), (key2384, 6), (key2369, 6), (key2369, 6), (key2497, -6), (key2497, -6), (key2431, -6), (key2497, -6)]

theorem rawRowCheck9455 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form11 = rawRow9455 := by decide +kernel

def row9455 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2431, -6), (key2497, -18)]

theorem rowCheck9455 : row9455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9455 := by decide +kernel

theorem rowEval9455 (x : Key → ℝ) : Integer.Sparse.eval row9455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9455, Integer.Sparse.eval_collectBalanced, rawRowCheck9455]

def rawRow9456 : Integer.Sparse Key := [(key2384, 6), (key2369, 6), (key2369, 6), (key2369, 6), (key2497, -6), (key2497, -6), (key2497, -6), (key2431, -6)]

theorem rawRowCheck9456 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form11 = rawRow9456 := by decide +kernel

def row9456 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2431, -6), (key2497, -18)]

theorem rowCheck9456 : row9456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9456 := by decide +kernel

theorem rowEval9456 (x : Key → ℝ) : Integer.Sparse.eval row9456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9456, Integer.Sparse.eval_collectBalanced, rawRowCheck9456]

def rawRow9457 : Integer.Sparse Key := [(key2397, 6), (key2397, 6), (key2397, 6), (key2431, 6), (key2384, -6), (key2474, -6), (key2474, -6), (key2474, -6)]

theorem rawRowCheck9457 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form11 = rawRow9457 := by decide +kernel

def row9457 : Integer.Sparse Key := [(key2384, -6), (key2397, 18), (key2431, 6), (key2474, -18)]

theorem rowCheck9457 : row9457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9457 := by decide +kernel

theorem rowEval9457 (x : Key → ℝ) : Integer.Sparse.eval row9457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9457, Integer.Sparse.eval_collectBalanced, rawRowCheck9457]

def rawRow9458 : Integer.Sparse Key := [(key2397, 6), (key2397, 6), (key2431, 6), (key2397, 6), (key2474, -6), (key2384, -6), (key2474, -6), (key2474, -6)]

theorem rawRowCheck9458 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form11 = rawRow9458 := by decide +kernel

def row9458 : Integer.Sparse Key := [(key2384, -6), (key2397, 18), (key2431, 6), (key2474, -18)]

theorem rowCheck9458 : row9458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9458 := by decide +kernel

theorem rowEval9458 (x : Key → ℝ) : Integer.Sparse.eval row9458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9458, Integer.Sparse.eval_collectBalanced, rawRowCheck9458]

def rawRow9459 : Integer.Sparse Key := [(key2397, 6), (key2431, 6), (key2397, 6), (key2397, 6), (key2474, -6), (key2474, -6), (key2384, -6), (key2474, -6)]

theorem rawRowCheck9459 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form11 = rawRow9459 := by decide +kernel

def row9459 : Integer.Sparse Key := [(key2384, -6), (key2397, 18), (key2431, 6), (key2474, -18)]

theorem rowCheck9459 : row9459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9459 := by decide +kernel

theorem rowEval9459 (x : Key → ℝ) : Integer.Sparse.eval row9459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9459, Integer.Sparse.eval_collectBalanced, rawRowCheck9459]

def rawRow9460 : Integer.Sparse Key := [(key2431, 6), (key2397, 6), (key2397, 6), (key2397, 6), (key2474, -6), (key2474, -6), (key2474, -6), (key2384, -6)]

theorem rawRowCheck9460 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form11 = rawRow9460 := by decide +kernel

def row9460 : Integer.Sparse Key := [(key2384, -6), (key2397, 18), (key2431, 6), (key2474, -18)]

theorem rowCheck9460 : row9460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9460 := by decide +kernel

theorem rowEval9460 (x : Key → ℝ) : Integer.Sparse.eval row9460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9460, Integer.Sparse.eval_collectBalanced, rawRowCheck9460]

def rawRow9461 : Integer.Sparse Key := [(key2372, 6), (key2372, 6), (key2372, 6), (key2385, 6), (key2432, -6), (key2498, -6), (key2498, -6), (key2498, -6)]

theorem rawRowCheck9461 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form12 = rawRow9461 := by decide +kernel

def row9461 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2432, -6), (key2498, -18)]

theorem rowCheck9461 : row9461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9461 := by decide +kernel

theorem rowEval9461 (x : Key → ℝ) : Integer.Sparse.eval row9461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9461, Integer.Sparse.eval_collectBalanced, rawRowCheck9461]

def rawRow9462 : Integer.Sparse Key := [(key2372, 6), (key2372, 6), (key2385, 6), (key2372, 6), (key2498, -6), (key2432, -6), (key2498, -6), (key2498, -6)]

theorem rawRowCheck9462 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form12 = rawRow9462 := by decide +kernel

def row9462 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2432, -6), (key2498, -18)]

theorem rowCheck9462 : row9462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9462 := by decide +kernel

theorem rowEval9462 (x : Key → ℝ) : Integer.Sparse.eval row9462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9462, Integer.Sparse.eval_collectBalanced, rawRowCheck9462]

def rawRow9463 : Integer.Sparse Key := [(key2372, 6), (key2385, 6), (key2372, 6), (key2372, 6), (key2498, -6), (key2498, -6), (key2432, -6), (key2498, -6)]

theorem rawRowCheck9463 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form12 = rawRow9463 := by decide +kernel

def row9463 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2432, -6), (key2498, -18)]

theorem rowCheck9463 : row9463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9463 := by decide +kernel

theorem rowEval9463 (x : Key → ℝ) : Integer.Sparse.eval row9463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9463, Integer.Sparse.eval_collectBalanced, rawRowCheck9463]

def rawRow9464 : Integer.Sparse Key := [(key2385, 6), (key2372, 6), (key2372, 6), (key2372, 6), (key2498, -6), (key2498, -6), (key2498, -6), (key2432, -6)]

theorem rawRowCheck9464 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form12 = rawRow9464 := by decide +kernel

def row9464 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2432, -6), (key2498, -18)]

theorem rowCheck9464 : row9464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9464 := by decide +kernel

theorem rowEval9464 (x : Key → ℝ) : Integer.Sparse.eval row9464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9464, Integer.Sparse.eval_collectBalanced, rawRowCheck9464]

def rawRow9465 : Integer.Sparse Key := [(key2400, 6), (key2400, 6), (key2400, 6), (key2432, 6), (key2385, -6), (key2475, -6), (key2475, -6), (key2475, -6)]

theorem rawRowCheck9465 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form12 = rawRow9465 := by decide +kernel

def row9465 : Integer.Sparse Key := [(key2385, -6), (key2400, 18), (key2432, 6), (key2475, -18)]

theorem rowCheck9465 : row9465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9465 := by decide +kernel

theorem rowEval9465 (x : Key → ℝ) : Integer.Sparse.eval row9465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9465, Integer.Sparse.eval_collectBalanced, rawRowCheck9465]

def rawRow9466 : Integer.Sparse Key := [(key2400, 6), (key2400, 6), (key2432, 6), (key2400, 6), (key2475, -6), (key2385, -6), (key2475, -6), (key2475, -6)]

theorem rawRowCheck9466 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form12 = rawRow9466 := by decide +kernel

def row9466 : Integer.Sparse Key := [(key2385, -6), (key2400, 18), (key2432, 6), (key2475, -18)]

theorem rowCheck9466 : row9466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9466 := by decide +kernel

theorem rowEval9466 (x : Key → ℝ) : Integer.Sparse.eval row9466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9466, Integer.Sparse.eval_collectBalanced, rawRowCheck9466]

def rawRow9467 : Integer.Sparse Key := [(key2400, 6), (key2432, 6), (key2400, 6), (key2400, 6), (key2475, -6), (key2475, -6), (key2385, -6), (key2475, -6)]

theorem rawRowCheck9467 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form12 = rawRow9467 := by decide +kernel

def row9467 : Integer.Sparse Key := [(key2385, -6), (key2400, 18), (key2432, 6), (key2475, -18)]

theorem rowCheck9467 : row9467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9467 := by decide +kernel

theorem rowEval9467 (x : Key → ℝ) : Integer.Sparse.eval row9467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9467, Integer.Sparse.eval_collectBalanced, rawRowCheck9467]

def rawRow9468 : Integer.Sparse Key := [(key2432, 6), (key2400, 6), (key2400, 6), (key2400, 6), (key2475, -6), (key2475, -6), (key2475, -6), (key2385, -6)]

theorem rawRowCheck9468 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form12 = rawRow9468 := by decide +kernel

def row9468 : Integer.Sparse Key := [(key2385, -6), (key2400, 18), (key2432, 6), (key2475, -18)]

theorem rowCheck9468 : row9468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9468 := by decide +kernel

theorem rowEval9468 (x : Key → ℝ) : Integer.Sparse.eval row9468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9468, Integer.Sparse.eval_collectBalanced, rawRowCheck9468]

def rawRow9469 : Integer.Sparse Key := [(key2098, -6), (key2098, -6), (key2098, -6), (key2099, -6), (key2203, 2), (key2203, 2), (key2203, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2318, 2), (key2318, 2), (key2318, 2)]

theorem rawRowCheck9469 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9469 := by decide +kernel

def row9469 : Integer.Sparse Key := [(key2098, -18), (key2099, -6), (key2203, 6), (key2317, 12), (key2318, 6)]

theorem rowCheck9469 : row9469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9469 := by decide +kernel

theorem rowEval9469 (x : Key → ℝ) : Integer.Sparse.eval row9469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9469, Integer.Sparse.eval_collectBalanced, rawRowCheck9469]

def rawRow9470 : Integer.Sparse Key := [(key2098, -6), (key2098, -6), (key2099, -6), (key2098, -6), (key2317, 2), (key2317, 2), (key2318, 2), (key2203, 2), (key2203, 2), (key2317, 2), (key2317, 2), (key2318, 2), (key2318, 2), (key2203, 2), (key2317, 2), (key2317, 2)]

theorem rawRowCheck9470 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form13 = rawRow9470 := by decide +kernel

def row9470 : Integer.Sparse Key := [(key2098, -18), (key2099, -6), (key2203, 6), (key2317, 12), (key2318, 6)]

theorem rowCheck9470 : row9470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9470 := by decide +kernel

theorem rowEval9470 (x : Key → ℝ) : Integer.Sparse.eval row9470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9470, Integer.Sparse.eval_collectBalanced, rawRowCheck9470]

def rawRow9471 : Integer.Sparse Key := [(key2098, -6), (key2099, -6), (key2098, -6), (key2098, -6), (key2317, 2), (key2318, 2), (key2317, 2), (key2317, 2), (key2318, 2), (key2203, 2), (key2318, 2), (key2203, 2), (key2317, 2), (key2317, 2), (key2203, 2), (key2317, 2)]

theorem rawRowCheck9471 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form13 = rawRow9471 := by decide +kernel

def row9471 : Integer.Sparse Key := [(key2098, -18), (key2099, -6), (key2203, 6), (key2317, 12), (key2318, 6)]

theorem rowCheck9471 : row9471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9471 := by decide +kernel

theorem rowEval9471 (x : Key → ℝ) : Integer.Sparse.eval row9471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9471, Integer.Sparse.eval_collectBalanced, rawRowCheck9471]

end MUB6.Certificate.GramRows

end OAI
