import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1408 : Integer.Sparse Key := [(key992, -6), (key1010, 2), (key992, 2), (key992, 2), (key1027, 6), (key1066, -2), (key1027, -2), (key1027, -2), (key1118, -2), (key1105, -2), (key1105, -2), (key1145, 2), (key1105, 2), (key1105, 2)]

theorem rawRowCheck1408 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form4 = rawRow1408 := by decide +kernel

def row1408 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, 2), (key1066, -2), (key1118, -2), (key1145, 2)]

theorem rowCheck1408 : row1408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1408 := by decide +kernel

theorem rowEval1408 (x : Key → ℝ) : Integer.Sparse.eval row1408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1408, Integer.Sparse.eval_collectBalanced, rawRowCheck1408]

def rawRow1409 : Integer.Sparse Key := [(key1010, -6), (key992, 2), (key992, 2), (key992, 2), (key1066, 6), (key1027, -2), (key1027, -2), (key1027, -2), (key1145, -2), (key1145, -2), (key1145, -2), (key1118, 2), (key1118, 2), (key1118, 2)]

theorem rawRowCheck1409 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form4 = rawRow1409 := by decide +kernel

def row1409 : Integer.Sparse Key := [(key992, 6), (key1010, -6), (key1027, -6), (key1066, 6), (key1118, 6), (key1145, -6)]

theorem rowCheck1409 : row1409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1409 := by decide +kernel

theorem rowEval1409 (x : Key → ℝ) : Integer.Sparse.eval row1409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1409, Integer.Sparse.eval_collectBalanced, rawRowCheck1409]

def rawRow1410 : Integer.Sparse Key := [(key1027, -6), (key1105, 2), (key1105, 2), (key1118, 2), (key992, 6), (key1105, -2), (key1105, -2), (key1145, -2), (key992, -2), (key992, -2), (key1010, -2), (key1027, 2), (key1027, 2), (key1066, 2)]

theorem rawRowCheck1410 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form4 = rawRow1410 := by decide +kernel

def row1410 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, -2), (key1066, 2), (key1118, 2), (key1145, -2)]

theorem rowCheck1410 : row1410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1410 := by decide +kernel

theorem rowEval1410 (x : Key → ℝ) : Integer.Sparse.eval row1410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1410, Integer.Sparse.eval_collectBalanced, rawRowCheck1410]

def rawRow1411 : Integer.Sparse Key := [(key1027, -6), (key1105, 2), (key1118, 2), (key1105, 2), (key992, 6), (key1105, -2), (key1145, -2), (key1105, -2), (key992, -2), (key1010, -2), (key992, -2), (key1027, 2), (key1066, 2), (key1027, 2)]

theorem rawRowCheck1411 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form4 = rawRow1411 := by decide +kernel

def row1411 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, -2), (key1066, 2), (key1118, 2), (key1145, -2)]

theorem rowCheck1411 : row1411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1411 := by decide +kernel

theorem rowEval1411 (x : Key → ℝ) : Integer.Sparse.eval row1411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1411, Integer.Sparse.eval_collectBalanced, rawRowCheck1411]

def rawRow1412 : Integer.Sparse Key := [(key1027, -6), (key1118, 2), (key1105, 2), (key1105, 2), (key992, 6), (key1145, -2), (key1105, -2), (key1105, -2), (key1010, -2), (key992, -2), (key992, -2), (key1066, 2), (key1027, 2), (key1027, 2)]

theorem rawRowCheck1412 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form4 = rawRow1412 := by decide +kernel

def row1412 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, -2), (key1066, 2), (key1118, 2), (key1145, -2)]

theorem rowCheck1412 : row1412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1412 := by decide +kernel

theorem rowEval1412 (x : Key → ℝ) : Integer.Sparse.eval row1412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1412, Integer.Sparse.eval_collectBalanced, rawRowCheck1412]

def rawRow1413 : Integer.Sparse Key := [(key1118, -6), (key1027, 2), (key1105, 2), (key1105, 2), (key1145, 6), (key992, -2), (key1105, -2), (key1105, -2), (key1066, -2), (key1145, -2), (key1145, -2), (key1010, 2), (key1118, 2), (key1118, 2)]

theorem rawRowCheck1413 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form4 = rawRow1413 := by decide +kernel

def row1413 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, 2), (key1066, -2), (key1118, -2), (key1145, 2)]

theorem rowCheck1413 : row1413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1413 := by decide +kernel

theorem rowEval1413 (x : Key → ℝ) : Integer.Sparse.eval row1413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1413, Integer.Sparse.eval_collectBalanced, rawRowCheck1413]

def rawRow1414 : Integer.Sparse Key := [(key1118, -6), (key1105, 2), (key1027, 2), (key1105, 2), (key1145, 6), (key1105, -2), (key992, -2), (key1105, -2), (key1145, -2), (key1066, -2), (key1145, -2), (key1118, 2), (key1010, 2), (key1118, 2)]

theorem rawRowCheck1414 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form4 = rawRow1414 := by decide +kernel

def row1414 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, 2), (key1066, -2), (key1118, -2), (key1145, 2)]

theorem rowCheck1414 : row1414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1414 := by decide +kernel

theorem rowEval1414 (x : Key → ℝ) : Integer.Sparse.eval row1414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1414, Integer.Sparse.eval_collectBalanced, rawRowCheck1414]

def rawRow1415 : Integer.Sparse Key := [(key1118, -6), (key1105, 2), (key1105, 2), (key1027, 2), (key1145, 6), (key1105, -2), (key1105, -2), (key992, -2), (key1145, -2), (key1145, -2), (key1066, -2), (key1118, 2), (key1118, 2), (key1010, 2)]

theorem rawRowCheck1415 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form4 = rawRow1415 := by decide +kernel

def row1415 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, 2), (key1066, -2), (key1118, -2), (key1145, 2)]

theorem rowCheck1415 : row1415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1415 := by decide +kernel

theorem rowEval1415 (x : Key → ℝ) : Integer.Sparse.eval row1415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck1415, Integer.Sparse.eval_collectBalanced, rawRowCheck1415]

def rawRow1416 : Integer.Sparse Key := [(key1066, -6), (key1145, 2), (key1145, 2), (key1145, 2), (key1010, 6), (key1118, -2), (key1118, -2), (key1118, -2), (key992, -2), (key992, -2), (key992, -2), (key1027, 2), (key1027, 2), (key1027, 2)]

theorem rawRowCheck1416 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form4 = rawRow1416 := by decide +kernel

def row1416 : Integer.Sparse Key := [(key992, -6), (key1010, 6), (key1027, 6), (key1066, -6), (key1118, -6), (key1145, 6)]

theorem rowCheck1416 : row1416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1416 := by decide +kernel

theorem rowEval1416 (x : Key → ℝ) : Integer.Sparse.eval row1416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1416, Integer.Sparse.eval_collectBalanced, rawRowCheck1416]

def rawRow1417 : Integer.Sparse Key := [(key1145, -6), (key1066, 2), (key1145, 2), (key1145, 2), (key1118, 6), (key1010, -2), (key1118, -2), (key1118, -2), (key1027, -2), (key1105, -2), (key1105, -2), (key992, 2), (key1105, 2), (key1105, 2)]

theorem rawRowCheck1417 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form4 = rawRow1417 := by decide +kernel

def row1417 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, -2), (key1066, 2), (key1118, 2), (key1145, -2)]

theorem rowCheck1417 : row1417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1417 := by decide +kernel

theorem rowEval1417 (x : Key → ℝ) : Integer.Sparse.eval row1417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1417, Integer.Sparse.eval_collectBalanced, rawRowCheck1417]

def rawRow1418 : Integer.Sparse Key := [(key1145, -6), (key1145, 2), (key1066, 2), (key1145, 2), (key1118, 6), (key1118, -2), (key1010, -2), (key1118, -2), (key1105, -2), (key1027, -2), (key1105, -2), (key1105, 2), (key992, 2), (key1105, 2)]

theorem rawRowCheck1418 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form4 = rawRow1418 := by decide +kernel

def row1418 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, -2), (key1066, 2), (key1118, 2), (key1145, -2)]

theorem rowCheck1418 : row1418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1418 := by decide +kernel

theorem rowEval1418 (x : Key → ℝ) : Integer.Sparse.eval row1418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1418, Integer.Sparse.eval_collectBalanced, rawRowCheck1418]

def rawRow1419 : Integer.Sparse Key := [(key1145, -6), (key1145, 2), (key1145, 2), (key1066, 2), (key1118, 6), (key1118, -2), (key1118, -2), (key1010, -2), (key1105, -2), (key1105, -2), (key1027, -2), (key1105, 2), (key1105, 2), (key992, 2)]

theorem rawRowCheck1419 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form4 = rawRow1419 := by decide +kernel

def row1419 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, -2), (key1066, 2), (key1118, 2), (key1145, -2)]

theorem rowCheck1419 : row1419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1419 := by decide +kernel

theorem rowEval1419 (x : Key → ℝ) : Integer.Sparse.eval row1419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck1419, Integer.Sparse.eval_collectBalanced, rawRowCheck1419]

def rawRow1420 : Integer.Sparse Key := [(key376, -1), (key380, -1), (key376, -1), (key566, -1), (key380, -1), (key566, -1), (key380, 2), (key380, 2), (key566, 2), (key427, 1), (key431, 1), (key427, 1), (key591, 1), (key431, 1), (key591, 1), (key431, -1), (key465, -1), (key431, -1), (key591, -1), (key465, -1), (key591, -1), (key459, -2), (key459, -2), (key608, -2), (key459, 1), (key482, 1), (key459, 1), (key608, 1), (key482, 1), (key608, 1)]

theorem rawRowCheck1420 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form5 = rawRow1420 := by decide +kernel

def row1420 : Integer.Sparse Key := [(key376, -2), (key380, 2), (key427, 2), (key459, -2), (key465, -2), (key482, 2)]

theorem rowCheck1420 : row1420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1420 := by decide +kernel

theorem rowEval1420 (x : Key → ℝ) : Integer.Sparse.eval row1420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1420, Integer.Sparse.eval_collectBalanced, rawRowCheck1420]

def rawRow1421 : Integer.Sparse Key := [(key380, -1), (key376, -1), (key566, -1), (key376, -1), (key566, -1), (key380, -1), (key380, 2), (key566, 2), (key380, 2), (key431, 1), (key427, 1), (key591, 1), (key427, 1), (key591, 1), (key431, 1), (key465, -1), (key431, -1), (key591, -1), (key431, -1), (key591, -1), (key465, -1), (key459, -2), (key608, -2), (key459, -2), (key482, 1), (key459, 1), (key608, 1), (key459, 1), (key608, 1), (key482, 1)]

theorem rawRowCheck1421 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form5 = rawRow1421 := by decide +kernel

def row1421 : Integer.Sparse Key := [(key376, -2), (key380, 2), (key427, 2), (key459, -2), (key465, -2), (key482, 2)]

theorem rowCheck1421 : row1421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1421 := by decide +kernel

theorem rowEval1421 (x : Key → ℝ) : Integer.Sparse.eval row1421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1421, Integer.Sparse.eval_collectBalanced, rawRowCheck1421]

def rawRow1422 : Integer.Sparse Key := [(key566, -1), (key566, -1), (key380, -1), (key380, -1), (key376, -1), (key376, -1), (key566, 2), (key380, 2), (key380, 2), (key591, 1), (key591, 1), (key431, 1), (key431, 1), (key427, 1), (key427, 1), (key591, -1), (key591, -1), (key465, -1), (key465, -1), (key431, -1), (key431, -1), (key608, -2), (key459, -2), (key459, -2), (key608, 1), (key608, 1), (key482, 1), (key482, 1), (key459, 1), (key459, 1)]

theorem rawRowCheck1422 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form5 = rawRow1422 := by decide +kernel

def row1422 : Integer.Sparse Key := [(key376, -2), (key380, 2), (key427, 2), (key459, -2), (key465, -2), (key482, 2)]

theorem rowCheck1422 : row1422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1422 := by decide +kernel

theorem rowEval1422 (x : Key → ℝ) : Integer.Sparse.eval row1422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1422, Integer.Sparse.eval_collectBalanced, rawRowCheck1422]

def rawRow1423 : Integer.Sparse Key := [(key380, -1), (key380, -1), (key380, -1), (key380, -1), (key380, -1), (key380, -1), (key376, 2), (key376, 2), (key376, 2), (key465, 1), (key465, 1), (key465, 1), (key465, 1), (key465, 1), (key465, 1), (key427, -1), (key427, -1), (key427, -1), (key427, -1), (key427, -1), (key427, -1), (key482, -2), (key482, -2), (key482, -2), (key459, 1), (key459, 1), (key459, 1), (key459, 1), (key459, 1), (key459, 1)]

theorem rawRowCheck1423 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form5 = rawRow1423 := by decide +kernel

def row1423 : Integer.Sparse Key := [(key376, 6), (key380, -6), (key427, -6), (key459, 6), (key465, 6), (key482, -6)]

theorem rowCheck1423 : row1423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1423 := by decide +kernel

theorem rowEval1423 (x : Key → ℝ) : Integer.Sparse.eval row1423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1423, Integer.Sparse.eval_collectBalanced, rawRowCheck1423]

def rawRow1424 : Integer.Sparse Key := [(key427, -1), (key431, -1), (key427, -1), (key591, -1), (key431, -1), (key591, -1), (key459, 2), (key459, 2), (key608, 2), (key376, 1), (key380, 1), (key376, 1), (key566, 1), (key380, 1), (key566, 1), (key459, -1), (key482, -1), (key459, -1), (key608, -1), (key482, -1), (key608, -1), (key380, -2), (key380, -2), (key566, -2), (key431, 1), (key465, 1), (key431, 1), (key591, 1), (key465, 1), (key591, 1)]

theorem rawRowCheck1424 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form5 = rawRow1424 := by decide +kernel

def row1424 : Integer.Sparse Key := [(key376, 2), (key380, -2), (key427, -2), (key459, 2), (key465, 2), (key482, -2)]

theorem rowCheck1424 : row1424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1424 := by decide +kernel

theorem rowEval1424 (x : Key → ℝ) : Integer.Sparse.eval row1424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1424, Integer.Sparse.eval_collectBalanced, rawRowCheck1424]

def rawRow1425 : Integer.Sparse Key := [(key431, -1), (key427, -1), (key591, -1), (key427, -1), (key591, -1), (key431, -1), (key459, 2), (key608, 2), (key459, 2), (key380, 1), (key376, 1), (key566, 1), (key376, 1), (key566, 1), (key380, 1), (key482, -1), (key459, -1), (key608, -1), (key459, -1), (key608, -1), (key482, -1), (key380, -2), (key566, -2), (key380, -2), (key465, 1), (key431, 1), (key591, 1), (key431, 1), (key591, 1), (key465, 1)]

theorem rawRowCheck1425 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form5 = rawRow1425 := by decide +kernel

def row1425 : Integer.Sparse Key := [(key376, 2), (key380, -2), (key427, -2), (key459, 2), (key465, 2), (key482, -2)]

theorem rowCheck1425 : row1425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1425 := by decide +kernel

theorem rowEval1425 (x : Key → ℝ) : Integer.Sparse.eval row1425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1425, Integer.Sparse.eval_collectBalanced, rawRowCheck1425]

def rawRow1426 : Integer.Sparse Key := [(key591, -1), (key591, -1), (key431, -1), (key431, -1), (key427, -1), (key427, -1), (key608, 2), (key459, 2), (key459, 2), (key566, 1), (key566, 1), (key380, 1), (key380, 1), (key376, 1), (key376, 1), (key608, -1), (key608, -1), (key482, -1), (key482, -1), (key459, -1), (key459, -1), (key566, -2), (key380, -2), (key380, -2), (key591, 1), (key591, 1), (key465, 1), (key465, 1), (key431, 1), (key431, 1)]

theorem rawRowCheck1426 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form5 = rawRow1426 := by decide +kernel

def row1426 : Integer.Sparse Key := [(key376, 2), (key380, -2), (key427, -2), (key459, 2), (key465, 2), (key482, -2)]

theorem rowCheck1426 : row1426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1426 := by decide +kernel

theorem rowEval1426 (x : Key → ℝ) : Integer.Sparse.eval row1426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1426, Integer.Sparse.eval_collectBalanced, rawRowCheck1426]

def rawRow1427 : Integer.Sparse Key := [(key211, -1), (key211, -1), (key431, -1), (key431, -1), (key459, -1), (key459, -1), (key207, 2), (key427, 2), (key427, 2), (key216, 1), (key216, 1), (key465, 1), (key465, 1), (key482, 1), (key482, 1), (key207, -1), (key207, -1), (key376, -1), (key376, -1), (key427, -1), (key427, -1), (key216, -2), (key465, -2), (key465, -2), (key211, 1), (key211, 1), (key380, 1), (key380, 1), (key431, 1), (key431, 1)]

theorem rawRowCheck1427 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form5 = rawRow1427 := by decide +kernel

def row1427 : Integer.Sparse Key := [(key376, -2), (key380, 2), (key427, 2), (key459, -2), (key465, -2), (key482, 2)]

theorem rowCheck1427 : row1427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1427 := by decide +kernel

theorem rowEval1427 (x : Key → ℝ) : Integer.Sparse.eval row1427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1427, Integer.Sparse.eval_collectBalanced, rawRowCheck1427]

def rawRow1428 : Integer.Sparse Key := [(key431, -1), (key459, -1), (key211, -1), (key459, -1), (key211, -1), (key431, -1), (key427, 2), (key207, 2), (key427, 2), (key465, 1), (key482, 1), (key216, 1), (key482, 1), (key216, 1), (key465, 1), (key376, -1), (key427, -1), (key207, -1), (key427, -1), (key207, -1), (key376, -1), (key465, -2), (key216, -2), (key465, -2), (key380, 1), (key431, 1), (key211, 1), (key431, 1), (key211, 1), (key380, 1)]

theorem rawRowCheck1428 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form5 = rawRow1428 := by decide +kernel

def row1428 : Integer.Sparse Key := [(key376, -2), (key380, 2), (key427, 2), (key459, -2), (key465, -2), (key482, 2)]

theorem rowCheck1428 : row1428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1428 := by decide +kernel

theorem rowEval1428 (x : Key → ℝ) : Integer.Sparse.eval row1428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1428, Integer.Sparse.eval_collectBalanced, rawRowCheck1428]

def rawRow1429 : Integer.Sparse Key := [(key459, -1), (key431, -1), (key459, -1), (key211, -1), (key431, -1), (key211, -1), (key427, 2), (key427, 2), (key207, 2), (key482, 1), (key465, 1), (key482, 1), (key216, 1), (key465, 1), (key216, 1), (key427, -1), (key376, -1), (key427, -1), (key207, -1), (key376, -1), (key207, -1), (key465, -2), (key465, -2), (key216, -2), (key431, 1), (key380, 1), (key431, 1), (key211, 1), (key380, 1), (key211, 1)]

theorem rawRowCheck1429 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form5 = rawRow1429 := by decide +kernel

def row1429 : Integer.Sparse Key := [(key376, -2), (key380, 2), (key427, 2), (key459, -2), (key465, -2), (key482, 2)]

theorem rowCheck1429 : row1429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1429 := by decide +kernel

theorem rowEval1429 (x : Key → ℝ) : Integer.Sparse.eval row1429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck1429, Integer.Sparse.eval_collectBalanced, rawRowCheck1429]

def rawRow1430 : Integer.Sparse Key := [(key465, -1), (key465, -1), (key465, -1), (key465, -1), (key465, -1), (key465, -1), (key482, 2), (key482, 2), (key482, 2), (key380, 1), (key380, 1), (key380, 1), (key380, 1), (key380, 1), (key380, 1), (key459, -1), (key459, -1), (key459, -1), (key459, -1), (key459, -1), (key459, -1), (key376, -2), (key376, -2), (key376, -2), (key427, 1), (key427, 1), (key427, 1), (key427, 1), (key427, 1), (key427, 1)]

theorem rawRowCheck1430 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form5 = rawRow1430 := by decide +kernel

def row1430 : Integer.Sparse Key := [(key376, -6), (key380, 6), (key427, 6), (key459, -6), (key465, -6), (key482, 6)]

theorem rowCheck1430 : row1430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1430 := by decide +kernel

theorem rowEval1430 (x : Key → ℝ) : Integer.Sparse.eval row1430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1430, Integer.Sparse.eval_collectBalanced, rawRowCheck1430]

def rawRow1431 : Integer.Sparse Key := [(key216, -1), (key216, -1), (key465, -1), (key465, -1), (key482, -1), (key482, -1), (key216, 2), (key465, 2), (key465, 2), (key211, 1), (key211, 1), (key431, 1), (key431, 1), (key459, 1), (key459, 1), (key211, -1), (key211, -1), (key380, -1), (key380, -1), (key431, -1), (key431, -1), (key207, -2), (key427, -2), (key427, -2), (key207, 1), (key207, 1), (key376, 1), (key376, 1), (key427, 1), (key427, 1)]

theorem rawRowCheck1431 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form5 = rawRow1431 := by decide +kernel

def row1431 : Integer.Sparse Key := [(key376, 2), (key380, -2), (key427, -2), (key459, 2), (key465, 2), (key482, -2)]

theorem rowCheck1431 : row1431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1431 := by decide +kernel

theorem rowEval1431 (x : Key → ℝ) : Integer.Sparse.eval row1431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1431, Integer.Sparse.eval_collectBalanced, rawRowCheck1431]

def rawRow1432 : Integer.Sparse Key := [(key465, -1), (key482, -1), (key216, -1), (key482, -1), (key216, -1), (key465, -1), (key465, 2), (key216, 2), (key465, 2), (key431, 1), (key459, 1), (key211, 1), (key459, 1), (key211, 1), (key431, 1), (key380, -1), (key431, -1), (key211, -1), (key431, -1), (key211, -1), (key380, -1), (key427, -2), (key207, -2), (key427, -2), (key376, 1), (key427, 1), (key207, 1), (key427, 1), (key207, 1), (key376, 1)]

theorem rawRowCheck1432 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form5 = rawRow1432 := by decide +kernel

def row1432 : Integer.Sparse Key := [(key376, 2), (key380, -2), (key427, -2), (key459, 2), (key465, 2), (key482, -2)]

theorem rowCheck1432 : row1432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1432 := by decide +kernel

theorem rowEval1432 (x : Key → ℝ) : Integer.Sparse.eval row1432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1432, Integer.Sparse.eval_collectBalanced, rawRowCheck1432]

def rawRow1433 : Integer.Sparse Key := [(key482, -1), (key465, -1), (key482, -1), (key216, -1), (key465, -1), (key216, -1), (key465, 2), (key465, 2), (key216, 2), (key459, 1), (key431, 1), (key459, 1), (key211, 1), (key431, 1), (key211, 1), (key431, -1), (key380, -1), (key431, -1), (key211, -1), (key380, -1), (key211, -1), (key427, -2), (key427, -2), (key207, -2), (key427, 1), (key376, 1), (key427, 1), (key207, 1), (key376, 1), (key207, 1)]

theorem rawRowCheck1433 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form5 = rawRow1433 := by decide +kernel

def row1433 : Integer.Sparse Key := [(key376, 2), (key380, -2), (key427, -2), (key459, 2), (key465, 2), (key482, -2)]

theorem rowCheck1433 : row1433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1433 := by decide +kernel

theorem rowEval1433 (x : Key → ℝ) : Integer.Sparse.eval row1433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck1433, Integer.Sparse.eval_collectBalanced, rawRowCheck1433]

def rawRow1434 : Integer.Sparse Key := [(key1049, -2), (key1061, -2), (key1061, -2), (key1053, 2), (key1061, 2), (key1061, 2), (key1135, 2), (key1141, 2), (key1141, 2), (key1141, -6), (key1237, -2), (key1239, -2), (key1239, -2), (key1239, 6)]

theorem rawRowCheck1434 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form6 = rawRow1434 := by decide +kernel

def row1434 : Integer.Sparse Key := [(key1049, -2), (key1053, 2), (key1135, 2), (key1141, -2), (key1237, -2), (key1239, 2)]

theorem rowCheck1434 : row1434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1434 := by decide +kernel

theorem rowEval1434 (x : Key → ℝ) : Integer.Sparse.eval row1434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1434, Integer.Sparse.eval_collectBalanced, rawRowCheck1434]

def rawRow1435 : Integer.Sparse Key := [(key1061, -2), (key1049, -2), (key1061, -2), (key1061, 2), (key1053, 2), (key1061, 2), (key1141, 2), (key1135, 2), (key1141, 2), (key1141, -6), (key1239, -2), (key1237, -2), (key1239, -2), (key1239, 6)]

theorem rawRowCheck1435 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form6 = rawRow1435 := by decide +kernel

def row1435 : Integer.Sparse Key := [(key1049, -2), (key1053, 2), (key1135, 2), (key1141, -2), (key1237, -2), (key1239, 2)]

theorem rowCheck1435 : row1435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1435 := by decide +kernel

theorem rowEval1435 (x : Key → ℝ) : Integer.Sparse.eval row1435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1435, Integer.Sparse.eval_collectBalanced, rawRowCheck1435]

def rawRow1436 : Integer.Sparse Key := [(key1061, -2), (key1061, -2), (key1049, -2), (key1061, 2), (key1061, 2), (key1053, 2), (key1141, 2), (key1141, 2), (key1135, 2), (key1141, -6), (key1239, -2), (key1239, -2), (key1237, -2), (key1239, 6)]

theorem rawRowCheck1436 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form6 = rawRow1436 := by decide +kernel

def row1436 : Integer.Sparse Key := [(key1049, -2), (key1053, 2), (key1135, 2), (key1141, -2), (key1237, -2), (key1239, 2)]

theorem rowCheck1436 : row1436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1436 := by decide +kernel

theorem rowEval1436 (x : Key → ℝ) : Integer.Sparse.eval row1436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1436, Integer.Sparse.eval_collectBalanced, rawRowCheck1436]

def rawRow1437 : Integer.Sparse Key := [(key1053, -2), (key1053, -2), (key1053, -2), (key1049, 2), (key1049, 2), (key1049, 2), (key1141, 2), (key1141, 2), (key1141, 2), (key1135, -6), (key1239, -2), (key1239, -2), (key1239, -2), (key1237, 6)]

theorem rawRowCheck1437 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form6 = rawRow1437 := by decide +kernel

def row1437 : Integer.Sparse Key := [(key1049, 6), (key1053, -6), (key1135, -6), (key1141, 6), (key1237, 6), (key1239, -6)]

theorem rowCheck1437 : row1437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1437 := by decide +kernel

theorem rowEval1437 (x : Key → ℝ) : Integer.Sparse.eval row1437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1437, Integer.Sparse.eval_collectBalanced, rawRowCheck1437]

def rawRow1438 : Integer.Sparse Key := [(key1135, -2), (key1141, -2), (key1141, -2), (key1237, 2), (key1239, 2), (key1239, 2), (key1049, 2), (key1061, 2), (key1061, 2), (key1239, -6), (key1053, -2), (key1061, -2), (key1061, -2), (key1141, 6)]

theorem rawRowCheck1438 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form6 = rawRow1438 := by decide +kernel

def row1438 : Integer.Sparse Key := [(key1049, 2), (key1053, -2), (key1135, -2), (key1141, 2), (key1237, 2), (key1239, -2)]

theorem rowCheck1438 : row1438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1438 := by decide +kernel

theorem rowEval1438 (x : Key → ℝ) : Integer.Sparse.eval row1438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1438, Integer.Sparse.eval_collectBalanced, rawRowCheck1438]

def rawRow1439 : Integer.Sparse Key := [(key1141, -2), (key1135, -2), (key1141, -2), (key1239, 2), (key1237, 2), (key1239, 2), (key1061, 2), (key1049, 2), (key1061, 2), (key1239, -6), (key1061, -2), (key1053, -2), (key1061, -2), (key1141, 6)]

theorem rawRowCheck1439 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form6 = rawRow1439 := by decide +kernel

def row1439 : Integer.Sparse Key := [(key1049, 2), (key1053, -2), (key1135, -2), (key1141, 2), (key1237, 2), (key1239, -2)]

theorem rowCheck1439 : row1439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1439 := by decide +kernel

theorem rowEval1439 (x : Key → ℝ) : Integer.Sparse.eval row1439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1439, Integer.Sparse.eval_collectBalanced, rawRowCheck1439]

def rawRow1440 : Integer.Sparse Key := [(key1141, -2), (key1141, -2), (key1135, -2), (key1239, 2), (key1239, 2), (key1237, 2), (key1061, 2), (key1061, 2), (key1049, 2), (key1239, -6), (key1061, -2), (key1061, -2), (key1053, -2), (key1141, 6)]

theorem rawRowCheck1440 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form6 = rawRow1440 := by decide +kernel

def row1440 : Integer.Sparse Key := [(key1049, 2), (key1053, -2), (key1135, -2), (key1141, 2), (key1237, 2), (key1239, -2)]

theorem rowCheck1440 : row1440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1440 := by decide +kernel

theorem rowEval1440 (x : Key → ℝ) : Integer.Sparse.eval row1440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1440, Integer.Sparse.eval_collectBalanced, rawRowCheck1440]

def rawRow1441 : Integer.Sparse Key := [(key1053, -2), (key1053, -2), (key1237, -2), (key1049, 2), (key1049, 2), (key1135, 2), (key1061, 2), (key1061, 2), (key1239, 2), (key1049, -6), (key1061, -2), (key1061, -2), (key1141, -2), (key1053, 6)]

theorem rawRowCheck1441 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form6 = rawRow1441 := by decide +kernel

def row1441 : Integer.Sparse Key := [(key1049, -2), (key1053, 2), (key1135, 2), (key1141, -2), (key1237, -2), (key1239, 2)]

theorem rowCheck1441 : row1441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1441 := by decide +kernel

theorem rowEval1441 (x : Key → ℝ) : Integer.Sparse.eval row1441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1441, Integer.Sparse.eval_collectBalanced, rawRowCheck1441]

def rawRow1442 : Integer.Sparse Key := [(key1053, -2), (key1237, -2), (key1053, -2), (key1049, 2), (key1135, 2), (key1049, 2), (key1061, 2), (key1239, 2), (key1061, 2), (key1049, -6), (key1061, -2), (key1141, -2), (key1061, -2), (key1053, 6)]

theorem rawRowCheck1442 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form6 = rawRow1442 := by decide +kernel

def row1442 : Integer.Sparse Key := [(key1049, -2), (key1053, 2), (key1135, 2), (key1141, -2), (key1237, -2), (key1239, 2)]

theorem rowCheck1442 : row1442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1442 := by decide +kernel

theorem rowEval1442 (x : Key → ℝ) : Integer.Sparse.eval row1442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1442, Integer.Sparse.eval_collectBalanced, rawRowCheck1442]

def rawRow1443 : Integer.Sparse Key := [(key1237, -2), (key1053, -2), (key1053, -2), (key1135, 2), (key1049, 2), (key1049, 2), (key1239, 2), (key1061, 2), (key1061, 2), (key1049, -6), (key1141, -2), (key1061, -2), (key1061, -2), (key1053, 6)]

theorem rawRowCheck1443 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form6 = rawRow1443 := by decide +kernel

def row1443 : Integer.Sparse Key := [(key1049, -2), (key1053, 2), (key1135, 2), (key1141, -2), (key1237, -2), (key1239, 2)]

theorem rowCheck1443 : row1443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1443 := by decide +kernel

theorem rowEval1443 (x : Key → ℝ) : Integer.Sparse.eval row1443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck1443, Integer.Sparse.eval_collectBalanced, rawRowCheck1443]

def rawRow1444 : Integer.Sparse Key := [(key1141, -2), (key1141, -2), (key1141, -2), (key1239, 2), (key1239, 2), (key1239, 2), (key1053, 2), (key1053, 2), (key1053, 2), (key1237, -6), (key1049, -2), (key1049, -2), (key1049, -2), (key1135, 6)]

theorem rawRowCheck1444 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form6 = rawRow1444 := by decide +kernel

def row1444 : Integer.Sparse Key := [(key1049, -6), (key1053, 6), (key1135, 6), (key1141, -6), (key1237, -6), (key1239, 6)]

theorem rowCheck1444 : row1444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1444 := by decide +kernel

theorem rowEval1444 (x : Key → ℝ) : Integer.Sparse.eval row1444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1444, Integer.Sparse.eval_collectBalanced, rawRowCheck1444]

def rawRow1445 : Integer.Sparse Key := [(key1061, -2), (key1061, -2), (key1239, -2), (key1061, 2), (key1061, 2), (key1141, 2), (key1053, 2), (key1053, 2), (key1237, 2), (key1053, -6), (key1049, -2), (key1049, -2), (key1135, -2), (key1049, 6)]

theorem rawRowCheck1445 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form6 = rawRow1445 := by decide +kernel

def row1445 : Integer.Sparse Key := [(key1049, 2), (key1053, -2), (key1135, -2), (key1141, 2), (key1237, 2), (key1239, -2)]

theorem rowCheck1445 : row1445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1445 := by decide +kernel

theorem rowEval1445 (x : Key → ℝ) : Integer.Sparse.eval row1445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1445, Integer.Sparse.eval_collectBalanced, rawRowCheck1445]

def rawRow1446 : Integer.Sparse Key := [(key1061, -2), (key1239, -2), (key1061, -2), (key1061, 2), (key1141, 2), (key1061, 2), (key1053, 2), (key1237, 2), (key1053, 2), (key1053, -6), (key1049, -2), (key1135, -2), (key1049, -2), (key1049, 6)]

theorem rawRowCheck1446 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form6 = rawRow1446 := by decide +kernel

def row1446 : Integer.Sparse Key := [(key1049, 2), (key1053, -2), (key1135, -2), (key1141, 2), (key1237, 2), (key1239, -2)]

theorem rowCheck1446 : row1446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1446 := by decide +kernel

theorem rowEval1446 (x : Key → ℝ) : Integer.Sparse.eval row1446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1446, Integer.Sparse.eval_collectBalanced, rawRowCheck1446]

def rawRow1447 : Integer.Sparse Key := [(key1239, -2), (key1061, -2), (key1061, -2), (key1141, 2), (key1061, 2), (key1061, 2), (key1237, 2), (key1053, 2), (key1053, 2), (key1053, -6), (key1135, -2), (key1049, -2), (key1049, -2), (key1049, 6)]

theorem rawRowCheck1447 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form6 = rawRow1447 := by decide +kernel

def row1447 : Integer.Sparse Key := [(key1049, 2), (key1053, -2), (key1135, -2), (key1141, 2), (key1237, 2), (key1239, -2)]

theorem rowCheck1447 : row1447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1447 := by decide +kernel

theorem rowEval1447 (x : Key → ℝ) : Integer.Sparse.eval row1447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck1447, Integer.Sparse.eval_collectBalanced, rawRowCheck1447]

def rawRow1448 : Integer.Sparse Key := [(key207, -2), (key211, -2), (key211, -2), (key207, 1), (key211, 1), (key207, 1), (key216, 1), (key211, 1), (key216, 1), (key376, 2), (key380, 2), (key380, 2), (key376, -1), (key380, -1), (key376, -1), (key566, -1), (key380, -1), (key566, -1), (key427, -1), (key431, -1), (key427, -1), (key465, -1), (key431, -1), (key465, -1), (key427, 1), (key431, 1), (key427, 1), (key591, 1), (key431, 1), (key591, 1)]

theorem rawRowCheck1448 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form7 = rawRow1448 := by decide +kernel

def row1448 : Integer.Sparse Key := [(key211, -2), (key216, 2), (key380, 2), (key465, -2), (key566, -2), (key591, 2)]

theorem rowCheck1448 : row1448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1448 := by decide +kernel

theorem rowEval1448 (x : Key → ℝ) : Integer.Sparse.eval row1448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1448, Integer.Sparse.eval_collectBalanced, rawRowCheck1448]

def rawRow1449 : Integer.Sparse Key := [(key211, -2), (key207, -2), (key211, -2), (key211, 1), (key207, 1), (key216, 1), (key207, 1), (key216, 1), (key211, 1), (key380, 2), (key376, 2), (key380, 2), (key380, -1), (key376, -1), (key566, -1), (key376, -1), (key566, -1), (key380, -1), (key431, -1), (key427, -1), (key465, -1), (key427, -1), (key465, -1), (key431, -1), (key431, 1), (key427, 1), (key591, 1), (key427, 1), (key591, 1), (key431, 1)]

theorem rawRowCheck1449 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form7 = rawRow1449 := by decide +kernel

def row1449 : Integer.Sparse Key := [(key211, -2), (key216, 2), (key380, 2), (key465, -2), (key566, -2), (key591, 2)]

theorem rowCheck1449 : row1449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1449 := by decide +kernel

theorem rowEval1449 (x : Key → ℝ) : Integer.Sparse.eval row1449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1449, Integer.Sparse.eval_collectBalanced, rawRowCheck1449]

def rawRow1450 : Integer.Sparse Key := [(key211, -2), (key211, -2), (key207, -2), (key216, 1), (key216, 1), (key211, 1), (key211, 1), (key207, 1), (key207, 1), (key380, 2), (key380, 2), (key376, 2), (key566, -1), (key566, -1), (key380, -1), (key380, -1), (key376, -1), (key376, -1), (key465, -1), (key465, -1), (key431, -1), (key431, -1), (key427, -1), (key427, -1), (key591, 1), (key591, 1), (key431, 1), (key431, 1), (key427, 1), (key427, 1)]

theorem rawRowCheck1450 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form7 = rawRow1450 := by decide +kernel

def row1450 : Integer.Sparse Key := [(key211, -2), (key216, 2), (key380, 2), (key465, -2), (key566, -2), (key591, 2)]

theorem rowCheck1450 : row1450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1450 := by decide +kernel

theorem rowEval1450 (x : Key → ℝ) : Integer.Sparse.eval row1450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1450, Integer.Sparse.eval_collectBalanced, rawRowCheck1450]

def rawRow1451 : Integer.Sparse Key := [(key216, -2), (key216, -2), (key216, -2), (key211, 1), (key211, 1), (key211, 1), (key211, 1), (key211, 1), (key211, 1), (key566, 2), (key566, 2), (key566, 2), (key380, -1), (key380, -1), (key380, -1), (key380, -1), (key380, -1), (key380, -1), (key591, -1), (key591, -1), (key591, -1), (key591, -1), (key591, -1), (key591, -1), (key465, 1), (key465, 1), (key465, 1), (key465, 1), (key465, 1), (key465, 1)]

theorem rawRowCheck1451 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form7 = rawRow1451 := by decide +kernel

def row1451 : Integer.Sparse Key := [(key211, 6), (key216, -6), (key380, -6), (key465, 6), (key566, 6), (key591, -6)]

theorem rowCheck1451 : row1451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1451 := by decide +kernel

theorem rowEval1451 (x : Key → ℝ) : Integer.Sparse.eval row1451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1451, Integer.Sparse.eval_collectBalanced, rawRowCheck1451]

def rawRow1452 : Integer.Sparse Key := [(key376, -2), (key380, -2), (key380, -2), (key427, 1), (key431, 1), (key427, 1), (key465, 1), (key431, 1), (key465, 1), (key207, 2), (key211, 2), (key211, 2), (key427, -1), (key431, -1), (key427, -1), (key591, -1), (key431, -1), (key591, -1), (key207, -1), (key211, -1), (key207, -1), (key216, -1), (key211, -1), (key216, -1), (key376, 1), (key380, 1), (key376, 1), (key566, 1), (key380, 1), (key566, 1)]

theorem rawRowCheck1452 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form7 = rawRow1452 := by decide +kernel

def row1452 : Integer.Sparse Key := [(key211, 2), (key216, -2), (key380, -2), (key465, 2), (key566, 2), (key591, -2)]

theorem rowCheck1452 : row1452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1452 := by decide +kernel

theorem rowEval1452 (x : Key → ℝ) : Integer.Sparse.eval row1452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1452, Integer.Sparse.eval_collectBalanced, rawRowCheck1452]

def rawRow1453 : Integer.Sparse Key := [(key380, -2), (key376, -2), (key380, -2), (key431, 1), (key427, 1), (key465, 1), (key427, 1), (key465, 1), (key431, 1), (key211, 2), (key207, 2), (key211, 2), (key431, -1), (key427, -1), (key591, -1), (key427, -1), (key591, -1), (key431, -1), (key211, -1), (key207, -1), (key216, -1), (key207, -1), (key216, -1), (key211, -1), (key380, 1), (key376, 1), (key566, 1), (key376, 1), (key566, 1), (key380, 1)]

theorem rawRowCheck1453 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form7 = rawRow1453 := by decide +kernel

def row1453 : Integer.Sparse Key := [(key211, 2), (key216, -2), (key380, -2), (key465, 2), (key566, 2), (key591, -2)]

theorem rowCheck1453 : row1453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1453 := by decide +kernel

theorem rowEval1453 (x : Key → ℝ) : Integer.Sparse.eval row1453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1453, Integer.Sparse.eval_collectBalanced, rawRowCheck1453]

def rawRow1454 : Integer.Sparse Key := [(key380, -2), (key380, -2), (key376, -2), (key465, 1), (key465, 1), (key431, 1), (key431, 1), (key427, 1), (key427, 1), (key211, 2), (key211, 2), (key207, 2), (key591, -1), (key591, -1), (key431, -1), (key431, -1), (key427, -1), (key427, -1), (key216, -1), (key216, -1), (key211, -1), (key211, -1), (key207, -1), (key207, -1), (key566, 1), (key566, 1), (key380, 1), (key380, 1), (key376, 1), (key376, 1)]

theorem rawRowCheck1454 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form7 = rawRow1454 := by decide +kernel

def row1454 : Integer.Sparse Key := [(key211, 2), (key216, -2), (key380, -2), (key465, 2), (key566, 2), (key591, -2)]

theorem rowCheck1454 : row1454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1454 := by decide +kernel

theorem rowEval1454 (x : Key → ℝ) : Integer.Sparse.eval row1454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1454, Integer.Sparse.eval_collectBalanced, rawRowCheck1454]

def rawRow1455 : Integer.Sparse Key := [(key465, -2), (key465, -2), (key482, -2), (key380, 1), (key380, 1), (key431, 1), (key431, 1), (key459, 1), (key459, 1), (key591, 2), (key591, 2), (key608, 2), (key211, -1), (key211, -1), (key431, -1), (key431, -1), (key459, -1), (key459, -1), (key566, -1), (key566, -1), (key591, -1), (key591, -1), (key608, -1), (key608, -1), (key216, 1), (key216, 1), (key465, 1), (key465, 1), (key482, 1), (key482, 1)]

theorem rawRowCheck1455 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form7 = rawRow1455 := by decide +kernel

def row1455 : Integer.Sparse Key := [(key211, -2), (key216, 2), (key380, 2), (key465, -2), (key566, -2), (key591, 2)]

theorem rowCheck1455 : row1455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1455 := by decide +kernel

theorem rowEval1455 (x : Key → ℝ) : Integer.Sparse.eval row1455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1455, Integer.Sparse.eval_collectBalanced, rawRowCheck1455]

def rawRow1456 : Integer.Sparse Key := [(key465, -2), (key482, -2), (key465, -2), (key431, 1), (key459, 1), (key380, 1), (key459, 1), (key380, 1), (key431, 1), (key591, 2), (key608, 2), (key591, 2), (key431, -1), (key459, -1), (key211, -1), (key459, -1), (key211, -1), (key431, -1), (key591, -1), (key608, -1), (key566, -1), (key608, -1), (key566, -1), (key591, -1), (key465, 1), (key482, 1), (key216, 1), (key482, 1), (key216, 1), (key465, 1)]

theorem rawRowCheck1456 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form7 = rawRow1456 := by decide +kernel

def row1456 : Integer.Sparse Key := [(key211, -2), (key216, 2), (key380, 2), (key465, -2), (key566, -2), (key591, 2)]

theorem rowCheck1456 : row1456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1456 := by decide +kernel

theorem rowEval1456 (x : Key → ℝ) : Integer.Sparse.eval row1456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1456, Integer.Sparse.eval_collectBalanced, rawRowCheck1456]

def rawRow1457 : Integer.Sparse Key := [(key482, -2), (key465, -2), (key465, -2), (key459, 1), (key431, 1), (key459, 1), (key380, 1), (key431, 1), (key380, 1), (key608, 2), (key591, 2), (key591, 2), (key459, -1), (key431, -1), (key459, -1), (key211, -1), (key431, -1), (key211, -1), (key608, -1), (key591, -1), (key608, -1), (key566, -1), (key591, -1), (key566, -1), (key482, 1), (key465, 1), (key482, 1), (key216, 1), (key465, 1), (key216, 1)]

theorem rawRowCheck1457 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form7 = rawRow1457 := by decide +kernel

def row1457 : Integer.Sparse Key := [(key211, -2), (key216, 2), (key380, 2), (key465, -2), (key566, -2), (key591, 2)]

theorem rowCheck1457 : row1457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1457 := by decide +kernel

theorem rowEval1457 (x : Key → ℝ) : Integer.Sparse.eval row1457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck1457, Integer.Sparse.eval_collectBalanced, rawRowCheck1457]

def rawRow1458 : Integer.Sparse Key := [(key566, -2), (key566, -2), (key566, -2), (key591, 1), (key591, 1), (key591, 1), (key591, 1), (key591, 1), (key591, 1), (key216, 2), (key216, 2), (key216, 2), (key465, -1), (key465, -1), (key465, -1), (key465, -1), (key465, -1), (key465, -1), (key211, -1), (key211, -1), (key211, -1), (key211, -1), (key211, -1), (key211, -1), (key380, 1), (key380, 1), (key380, 1), (key380, 1), (key380, 1), (key380, 1)]

theorem rawRowCheck1458 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form7 = rawRow1458 := by decide +kernel

def row1458 : Integer.Sparse Key := [(key211, -6), (key216, 6), (key380, 6), (key465, -6), (key566, -6), (key591, 6)]

theorem rowCheck1458 : row1458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1458 := by decide +kernel

theorem rowEval1458 (x : Key → ℝ) : Integer.Sparse.eval row1458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1458, Integer.Sparse.eval_collectBalanced, rawRowCheck1458]

def rawRow1459 : Integer.Sparse Key := [(key591, -2), (key591, -2), (key608, -2), (key566, 1), (key566, 1), (key591, 1), (key591, 1), (key608, 1), (key608, 1), (key465, 2), (key465, 2), (key482, 2), (key216, -1), (key216, -1), (key465, -1), (key465, -1), (key482, -1), (key482, -1), (key380, -1), (key380, -1), (key431, -1), (key431, -1), (key459, -1), (key459, -1), (key211, 1), (key211, 1), (key431, 1), (key431, 1), (key459, 1), (key459, 1)]

theorem rawRowCheck1459 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form7 = rawRow1459 := by decide +kernel

def row1459 : Integer.Sparse Key := [(key211, 2), (key216, -2), (key380, -2), (key465, 2), (key566, 2), (key591, -2)]

theorem rowCheck1459 : row1459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1459 := by decide +kernel

theorem rowEval1459 (x : Key → ℝ) : Integer.Sparse.eval row1459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1459, Integer.Sparse.eval_collectBalanced, rawRowCheck1459]

def rawRow1460 : Integer.Sparse Key := [(key591, -2), (key608, -2), (key591, -2), (key591, 1), (key608, 1), (key566, 1), (key608, 1), (key566, 1), (key591, 1), (key465, 2), (key482, 2), (key465, 2), (key465, -1), (key482, -1), (key216, -1), (key482, -1), (key216, -1), (key465, -1), (key431, -1), (key459, -1), (key380, -1), (key459, -1), (key380, -1), (key431, -1), (key431, 1), (key459, 1), (key211, 1), (key459, 1), (key211, 1), (key431, 1)]

theorem rawRowCheck1460 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form7 = rawRow1460 := by decide +kernel

def row1460 : Integer.Sparse Key := [(key211, 2), (key216, -2), (key380, -2), (key465, 2), (key566, 2), (key591, -2)]

theorem rowCheck1460 : row1460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1460 := by decide +kernel

theorem rowEval1460 (x : Key → ℝ) : Integer.Sparse.eval row1460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1460, Integer.Sparse.eval_collectBalanced, rawRowCheck1460]

def rawRow1461 : Integer.Sparse Key := [(key608, -2), (key591, -2), (key591, -2), (key608, 1), (key591, 1), (key608, 1), (key566, 1), (key591, 1), (key566, 1), (key482, 2), (key465, 2), (key465, 2), (key482, -1), (key465, -1), (key482, -1), (key216, -1), (key465, -1), (key216, -1), (key459, -1), (key431, -1), (key459, -1), (key380, -1), (key431, -1), (key380, -1), (key459, 1), (key431, 1), (key459, 1), (key211, 1), (key431, 1), (key211, 1)]

theorem rawRowCheck1461 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form7 = rawRow1461 := by decide +kernel

def row1461 : Integer.Sparse Key := [(key211, 2), (key216, -2), (key380, -2), (key465, 2), (key566, 2), (key591, -2)]

theorem rowCheck1461 : row1461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1461 := by decide +kernel

theorem rowEval1461 (x : Key → ℝ) : Integer.Sparse.eval row1461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck1461, Integer.Sparse.eval_collectBalanced, rawRowCheck1461]

def rawRow1462 : Integer.Sparse Key := [(key1, -2), (key4, -2), (key4, -2), (key4, 6), (key84, 2), (key87, 2), (key87, 2), (key87, -2), (key87, -2), (key148, -2), (key164, -6), (key164, 2), (key164, 2), (key184, 2)]

theorem rawRowCheck1462 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form8 = rawRow1462 := by decide +kernel

def row1462 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key148, -2), (key164, -2), (key184, 2)]

theorem rowCheck1462 : row1462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1462 := by decide +kernel

theorem rowEval1462 (x : Key → ℝ) : Integer.Sparse.eval row1462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1462, Integer.Sparse.eval_collectBalanced, rawRowCheck1462]

def rawRow1463 : Integer.Sparse Key := [(key4, -2), (key1, -2), (key4, -2), (key4, 6), (key87, 2), (key84, 2), (key87, 2), (key87, -2), (key148, -2), (key87, -2), (key164, -6), (key164, 2), (key184, 2), (key164, 2)]

theorem rawRowCheck1463 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form8 = rawRow1463 := by decide +kernel

def row1463 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key148, -2), (key164, -2), (key184, 2)]

theorem rowCheck1463 : row1463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1463 := by decide +kernel

theorem rowEval1463 (x : Key → ℝ) : Integer.Sparse.eval row1463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1463, Integer.Sparse.eval_collectBalanced, rawRowCheck1463]

def rawRow1464 : Integer.Sparse Key := [(key4, -2), (key4, -2), (key1, -2), (key4, 6), (key87, 2), (key87, 2), (key84, 2), (key148, -2), (key87, -2), (key87, -2), (key164, -6), (key184, 2), (key164, 2), (key164, 2)]

theorem rawRowCheck1464 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form8 = rawRow1464 := by decide +kernel

def row1464 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key148, -2), (key164, -2), (key184, 2)]

theorem rowCheck1464 : row1464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1464 := by decide +kernel

theorem rowEval1464 (x : Key → ℝ) : Integer.Sparse.eval row1464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1464, Integer.Sparse.eval_collectBalanced, rawRowCheck1464]

def rawRow1465 : Integer.Sparse Key := [(key4, -2), (key4, -2), (key4, -2), (key1, 6), (key148, 2), (key148, 2), (key148, 2), (key84, -2), (key84, -2), (key84, -2), (key184, -6), (key164, 2), (key164, 2), (key164, 2)]

theorem rawRowCheck1465 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form8 = rawRow1465 := by decide +kernel

def row1465 : Integer.Sparse Key := [(key1, 6), (key4, -6), (key84, -6), (key148, 6), (key164, 6), (key184, -6)]

theorem rowCheck1465 : row1465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1465 := by decide +kernel

theorem rowEval1465 (x : Key → ℝ) : Integer.Sparse.eval row1465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1465, Integer.Sparse.eval_collectBalanced, rawRowCheck1465]

def rawRow1466 : Integer.Sparse Key := [(key84, -2), (key87, -2), (key87, -2), (key148, 6), (key1, 2), (key4, 2), (key4, 2), (key164, -2), (key164, -2), (key184, -2), (key4, -6), (key87, 2), (key87, 2), (key148, 2)]

theorem rawRowCheck1466 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form8 = rawRow1466 := by decide +kernel

def row1466 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key148, 8), (key164, -4), (key184, -2)]

theorem rowCheck1466 : row1466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1466 := by decide +kernel

theorem rowEval1466 (x : Key → ℝ) : Integer.Sparse.eval row1466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1466, Integer.Sparse.eval_collectBalanced, rawRowCheck1466]

def rawRow1467 : Integer.Sparse Key := [(key87, -2), (key84, -2), (key87, -2), (key148, 6), (key4, 2), (key1, 2), (key4, 2), (key164, -2), (key184, -2), (key164, -2), (key4, -6), (key87, 2), (key148, 2), (key87, 2)]

theorem rawRowCheck1467 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form8 = rawRow1467 := by decide +kernel

def row1467 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key148, 8), (key164, -4), (key184, -2)]

theorem rowCheck1467 : row1467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1467 := by decide +kernel

theorem rowEval1467 (x : Key → ℝ) : Integer.Sparse.eval row1467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1467, Integer.Sparse.eval_collectBalanced, rawRowCheck1467]

def rawRow1468 : Integer.Sparse Key := [(key87, -2), (key87, -2), (key84, -2), (key148, 6), (key4, 2), (key4, 2), (key1, 2), (key184, -2), (key164, -2), (key164, -2), (key4, -6), (key148, 2), (key87, 2), (key87, 2)]

theorem rawRowCheck1468 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form8 = rawRow1468 := by decide +kernel

def row1468 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key148, 8), (key164, -4), (key184, -2)]

theorem rowCheck1468 : row1468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1468 := by decide +kernel

theorem rowEval1468 (x : Key → ℝ) : Integer.Sparse.eval row1468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1468, Integer.Sparse.eval_collectBalanced, rawRowCheck1468]

def rawRow1469 : Integer.Sparse Key := [(key87, -2), (key87, -2), (key148, -2), (key84, 6), (key164, 2), (key164, 2), (key184, 2), (key1, -2), (key84, -2), (key84, -2), (key148, -6), (key4, 2), (key87, 2), (key87, 2)]

theorem rawRowCheck1469 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form8 = rawRow1469 := by decide +kernel

def row1469 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key148, -8), (key164, 4), (key184, 2)]

theorem rowCheck1469 : row1469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1469 := by decide +kernel

theorem rowEval1469 (x : Key → ℝ) : Integer.Sparse.eval row1469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1469, Integer.Sparse.eval_collectBalanced, rawRowCheck1469]

def rawRow1470 : Integer.Sparse Key := [(key87, -2), (key148, -2), (key87, -2), (key84, 6), (key164, 2), (key184, 2), (key164, 2), (key84, -2), (key1, -2), (key84, -2), (key148, -6), (key87, 2), (key4, 2), (key87, 2)]

theorem rawRowCheck1470 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form8 = rawRow1470 := by decide +kernel

def row1470 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key148, -8), (key164, 4), (key184, 2)]

theorem rowCheck1470 : row1470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1470 := by decide +kernel

theorem rowEval1470 (x : Key → ℝ) : Integer.Sparse.eval row1470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1470, Integer.Sparse.eval_collectBalanced, rawRowCheck1470]

def rawRow1471 : Integer.Sparse Key := [(key148, -2), (key87, -2), (key87, -2), (key84, 6), (key184, 2), (key164, 2), (key164, 2), (key84, -2), (key84, -2), (key1, -2), (key148, -6), (key87, 2), (key87, 2), (key4, 2)]

theorem rawRowCheck1471 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form8 = rawRow1471 := by decide +kernel

def row1471 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key148, -8), (key164, 4), (key184, 2)]

theorem rowCheck1471 : row1471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1471 := by decide +kernel

theorem rowEval1471 (x : Key → ℝ) : Integer.Sparse.eval row1471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck1471, Integer.Sparse.eval_collectBalanced, rawRowCheck1471]

def rawRow1472 : Integer.Sparse Key := [(key164, -2), (key164, -2), (key164, -2), (key184, 6), (key4, 2), (key4, 2), (key4, 2), (key148, -2), (key148, -2), (key148, -2), (key1, -6), (key84, 2), (key84, 2), (key84, 2)]

theorem rawRowCheck1472 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form8 = rawRow1472 := by decide +kernel

def row1472 : Integer.Sparse Key := [(key1, -6), (key4, 6), (key84, 6), (key148, -6), (key164, -6), (key184, 6)]

theorem rowCheck1472 : row1472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1472 := by decide +kernel

theorem rowEval1472 (x : Key → ℝ) : Integer.Sparse.eval row1472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1472, Integer.Sparse.eval_collectBalanced, rawRowCheck1472]

def rawRow1473 : Integer.Sparse Key := [(key164, -2), (key164, -2), (key184, -2), (key164, 6), (key87, 2), (key87, 2), (key148, 2), (key4, -2), (key87, -2), (key87, -2), (key84, -6), (key1, 2), (key84, 2), (key84, 2)]

theorem rawRowCheck1473 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form8 = rawRow1473 := by decide +kernel

def row1473 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key148, 2), (key164, 2), (key184, -2)]

theorem rowCheck1473 : row1473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1473 := by decide +kernel

theorem rowEval1473 (x : Key → ℝ) : Integer.Sparse.eval row1473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1473, Integer.Sparse.eval_collectBalanced, rawRowCheck1473]

def rawRow1474 : Integer.Sparse Key := [(key164, -2), (key184, -2), (key164, -2), (key164, 6), (key87, 2), (key148, 2), (key87, 2), (key87, -2), (key4, -2), (key87, -2), (key84, -6), (key84, 2), (key1, 2), (key84, 2)]

theorem rawRowCheck1474 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form8 = rawRow1474 := by decide +kernel

def row1474 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key148, 2), (key164, 2), (key184, -2)]

theorem rowCheck1474 : row1474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1474 := by decide +kernel

theorem rowEval1474 (x : Key → ℝ) : Integer.Sparse.eval row1474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1474, Integer.Sparse.eval_collectBalanced, rawRowCheck1474]

def rawRow1475 : Integer.Sparse Key := [(key184, -2), (key164, -2), (key164, -2), (key164, 6), (key148, 2), (key87, 2), (key87, 2), (key87, -2), (key87, -2), (key4, -2), (key84, -6), (key84, 2), (key84, 2), (key1, 2)]

theorem rawRowCheck1475 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form8 = rawRow1475 := by decide +kernel

def row1475 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key148, 2), (key164, 2), (key184, -2)]

theorem rowCheck1475 : row1475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1475 := by decide +kernel

theorem rowEval1475 (x : Key → ℝ) : Integer.Sparse.eval row1475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck1475, Integer.Sparse.eval_collectBalanced, rawRowCheck1475]

def rawRow1476 : Integer.Sparse Key := [(key2672, -2), (key2749, -2), (key2749, -2), (key2675, 1), (key2675, 1), (key2730, 1), (key2730, 1), (key2751, 1), (key2751, 1), (key2787, 2), (key2906, 2), (key2906, 2), (key2797, -1), (key2797, -1), (key2833, -1), (key2833, -1), (key2915, -1), (key2915, -1), (key2940, -1), (key2940, -1), (key2985, -1), (key2985, -1), (key3001, -1), (key3001, -1), (key2945, 1), (key2945, 1), (key2962, 1), (key2962, 1), (key3004, 1), (key3004, 1)]

theorem rawRowCheck1476 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form0 = rawRow1476 := by decide +kernel

def row1476 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2730, 2), (key2749, -4), (key2751, 2), (key2787, 2), (key2797, -2), (key2833, -2), (key2906, 4), (key2915, -2), (key2940, -2), (key2945, 2), (key2962, 2), (key2985, -2), (key3001, -2), (key3004, 2)]

theorem rowCheck1476 : row1476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1476 := by decide +kernel

theorem rowEval1476 (x : Key → ℝ) : Integer.Sparse.eval row1476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1476, Integer.Sparse.eval_collectBalanced, rawRowCheck1476]

def rawRow1477 : Integer.Sparse Key := [(key2749, -2), (key2672, -2), (key2749, -2), (key2730, 1), (key2751, 1), (key2675, 1), (key2751, 1), (key2675, 1), (key2730, 1), (key2906, 2), (key2787, 2), (key2906, 2), (key2833, -1), (key2915, -1), (key2797, -1), (key2915, -1), (key2797, -1), (key2833, -1), (key2985, -1), (key3001, -1), (key2940, -1), (key3001, -1), (key2940, -1), (key2985, -1), (key2962, 1), (key3004, 1), (key2945, 1), (key3004, 1), (key2945, 1), (key2962, 1)]

theorem rawRowCheck1477 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form0 = rawRow1477 := by decide +kernel

def row1477 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2730, 2), (key2749, -4), (key2751, 2), (key2787, 2), (key2797, -2), (key2833, -2), (key2906, 4), (key2915, -2), (key2940, -2), (key2945, 2), (key2962, 2), (key2985, -2), (key3001, -2), (key3004, 2)]

theorem rowCheck1477 : row1477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1477 := by decide +kernel

theorem rowEval1477 (x : Key → ℝ) : Integer.Sparse.eval row1477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1477, Integer.Sparse.eval_collectBalanced, rawRowCheck1477]

def rawRow1478 : Integer.Sparse Key := [(key2749, -2), (key2749, -2), (key2672, -2), (key2751, 1), (key2730, 1), (key2751, 1), (key2675, 1), (key2730, 1), (key2675, 1), (key2906, 2), (key2906, 2), (key2787, 2), (key2915, -1), (key2833, -1), (key2915, -1), (key2797, -1), (key2833, -1), (key2797, -1), (key3001, -1), (key2985, -1), (key3001, -1), (key2940, -1), (key2985, -1), (key2940, -1), (key3004, 1), (key2962, 1), (key3004, 1), (key2945, 1), (key2962, 1), (key2945, 1)]

theorem rawRowCheck1478 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form0 = rawRow1478 := by decide +kernel

def row1478 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2730, 2), (key2749, -4), (key2751, 2), (key2787, 2), (key2797, -2), (key2833, -2), (key2906, 4), (key2915, -2), (key2940, -2), (key2945, 2), (key2962, 2), (key2985, -2), (key3001, -2), (key3004, 2)]

theorem rowCheck1478 : row1478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1478 := by decide +kernel

theorem rowEval1478 (x : Key → ℝ) : Integer.Sparse.eval row1478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1478, Integer.Sparse.eval_collectBalanced, rawRowCheck1478]

def rawRow1479 : Integer.Sparse Key := [(key2675, -2), (key2739, -2), (key2751, -2), (key2672, 1), (key2675, 1), (key2707, 1), (key2730, 1), (key2739, 1), (key2749, 1), (key2797, 2), (key2899, 2), (key2915, 2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, -1), (key2899, -1), (key2906, -1), (key2945, -1), (key2946, -1), (key2978, -1), (key2994, -1), (key2999, -1), (key3004, -1), (key2940, 1), (key2946, 1), (key2952, 1), (key2964, 1), (key2999, 1), (key3001, 1)]

theorem rawRowCheck1479 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form0 = rawRow1479 := by decide +kernel

def row1479 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, -1), (key2749, 1), (key2751, -2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, -1), (key2899, 1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, 1), (key2978, -1), (key2994, -1), (key3001, 1), (key3004, -1)]

theorem rowCheck1479 : row1479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1479 := by decide +kernel

theorem rowEval1479 (x : Key → ℝ) : Integer.Sparse.eval row1479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1479, Integer.Sparse.eval_collectBalanced, rawRowCheck1479]

def rawRow1480 : Integer.Sparse Key := [(key2675, -2), (key2751, -2), (key2739, -2), (key2675, 1), (key2672, 1), (key2730, 1), (key2707, 1), (key2749, 1), (key2739, 1), (key2797, 2), (key2915, 2), (key2899, 2), (key2797, -1), (key2787, -1), (key2833, -1), (key2810, -1), (key2906, -1), (key2899, -1), (key2946, -1), (key2945, -1), (key2994, -1), (key2978, -1), (key3004, -1), (key2999, -1), (key2946, 1), (key2940, 1), (key2964, 1), (key2952, 1), (key3001, 1), (key2999, 1)]

theorem rawRowCheck1480 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form0 = rawRow1480 := by decide +kernel

def row1480 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, -1), (key2749, 1), (key2751, -2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, -1), (key2899, 1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, 1), (key2978, -1), (key2994, -1), (key3001, 1), (key3004, -1)]

theorem rowCheck1480 : row1480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1480 := by decide +kernel

theorem rowEval1480 (x : Key → ℝ) : Integer.Sparse.eval row1480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1480, Integer.Sparse.eval_collectBalanced, rawRowCheck1480]

def rawRow1481 : Integer.Sparse Key := [(key2739, -2), (key2675, -2), (key2751, -2), (key2707, 1), (key2739, 1), (key2672, 1), (key2749, 1), (key2675, 1), (key2730, 1), (key2899, 2), (key2797, 2), (key2915, 2), (key2810, -1), (key2899, -1), (key2787, -1), (key2906, -1), (key2797, -1), (key2833, -1), (key2978, -1), (key2999, -1), (key2945, -1), (key3004, -1), (key2946, -1), (key2994, -1), (key2952, 1), (key2999, 1), (key2940, 1), (key3001, 1), (key2946, 1), (key2964, 1)]

theorem rawRowCheck1481 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form0 = rawRow1481 := by decide +kernel

def row1481 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, -1), (key2749, 1), (key2751, -2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, -1), (key2899, 1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, 1), (key2978, -1), (key2994, -1), (key3001, 1), (key3004, -1)]

theorem rowCheck1481 : row1481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1481 := by decide +kernel

theorem rowEval1481 (x : Key → ℝ) : Integer.Sparse.eval row1481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1481, Integer.Sparse.eval_collectBalanced, rawRowCheck1481]

def rawRow1482 : Integer.Sparse Key := [(key2739, -2), (key2751, -2), (key2675, -2), (key2739, 1), (key2707, 1), (key2749, 1), (key2672, 1), (key2730, 1), (key2675, 1), (key2899, 2), (key2915, 2), (key2797, 2), (key2899, -1), (key2810, -1), (key2906, -1), (key2787, -1), (key2833, -1), (key2797, -1), (key2999, -1), (key2978, -1), (key3004, -1), (key2945, -1), (key2994, -1), (key2946, -1), (key2999, 1), (key2952, 1), (key3001, 1), (key2940, 1), (key2964, 1), (key2946, 1)]

theorem rawRowCheck1482 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form0 = rawRow1482 := by decide +kernel

def row1482 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, -1), (key2749, 1), (key2751, -2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, -1), (key2899, 1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, 1), (key2978, -1), (key2994, -1), (key3001, 1), (key3004, -1)]

theorem rowCheck1482 : row1482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1482 := by decide +kernel

theorem rowEval1482 (x : Key → ℝ) : Integer.Sparse.eval row1482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1482, Integer.Sparse.eval_collectBalanced, rawRowCheck1482]

def rawRow1483 : Integer.Sparse Key := [(key2751, -2), (key2675, -2), (key2739, -2), (key2730, 1), (key2749, 1), (key2675, 1), (key2739, 1), (key2672, 1), (key2707, 1), (key2915, 2), (key2797, 2), (key2899, 2), (key2833, -1), (key2906, -1), (key2797, -1), (key2899, -1), (key2787, -1), (key2810, -1), (key2994, -1), (key3004, -1), (key2946, -1), (key2999, -1), (key2945, -1), (key2978, -1), (key2964, 1), (key3001, 1), (key2946, 1), (key2999, 1), (key2940, 1), (key2952, 1)]

theorem rawRowCheck1483 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form0 = rawRow1483 := by decide +kernel

def row1483 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, -1), (key2749, 1), (key2751, -2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, -1), (key2899, 1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, 1), (key2978, -1), (key2994, -1), (key3001, 1), (key3004, -1)]

theorem rowCheck1483 : row1483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1483 := by decide +kernel

theorem rowEval1483 (x : Key → ℝ) : Integer.Sparse.eval row1483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1483, Integer.Sparse.eval_collectBalanced, rawRowCheck1483]

def rawRow1484 : Integer.Sparse Key := [(key2751, -2), (key2739, -2), (key2675, -2), (key2749, 1), (key2730, 1), (key2739, 1), (key2675, 1), (key2707, 1), (key2672, 1), (key2915, 2), (key2899, 2), (key2797, 2), (key2906, -1), (key2833, -1), (key2899, -1), (key2797, -1), (key2810, -1), (key2787, -1), (key3004, -1), (key2994, -1), (key2999, -1), (key2946, -1), (key2978, -1), (key2945, -1), (key3001, 1), (key2964, 1), (key2999, 1), (key2946, 1), (key2952, 1), (key2940, 1)]

theorem rawRowCheck1484 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form0 = rawRow1484 := by decide +kernel

def row1484 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, -1), (key2749, 1), (key2751, -2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, -1), (key2899, 1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, 1), (key2978, -1), (key2994, -1), (key3001, 1), (key3004, -1)]

theorem rowCheck1484 : row1484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1484 := by decide +kernel

theorem rowEval1484 (x : Key → ℝ) : Integer.Sparse.eval row1484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1484, Integer.Sparse.eval_collectBalanced, rawRowCheck1484]

def rawRow1485 : Integer.Sparse Key := [(key2707, -2), (key2978, -2), (key2978, -2), (key2730, 1), (key2730, 1), (key2985, 1), (key2985, 1), (key2994, 1), (key2994, 1), (key2672, 2), (key2749, 2), (key2749, 2), (key2945, -1), (key2945, -1), (key2962, -1), (key2962, -1), (key3004, -1), (key3004, -1), (key2675, -1), (key2675, -1), (key2730, -1), (key2730, -1), (key2751, -1), (key2751, -1), (key2797, 1), (key2797, 1), (key2833, 1), (key2833, 1), (key2915, 1), (key2915, 1)]

theorem rawRowCheck1485 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form0 = rawRow1485 := by decide +kernel

def row1485 : Integer.Sparse Key := [(key2672, 2), (key2675, -2), (key2707, -2), (key2749, 4), (key2751, -2), (key2797, 2), (key2833, 2), (key2915, 2), (key2945, -2), (key2962, -2), (key2978, -4), (key2985, 2), (key2994, 2), (key3004, -2)]

theorem rowCheck1485 : row1485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1485 := by decide +kernel

theorem rowEval1485 (x : Key → ℝ) : Integer.Sparse.eval row1485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1485, Integer.Sparse.eval_collectBalanced, rawRowCheck1485]

def rawRow1486 : Integer.Sparse Key := [(key2978, -2), (key2707, -2), (key2978, -2), (key2985, 1), (key2994, 1), (key2730, 1), (key2994, 1), (key2730, 1), (key2985, 1), (key2749, 2), (key2672, 2), (key2749, 2), (key2962, -1), (key3004, -1), (key2945, -1), (key3004, -1), (key2945, -1), (key2962, -1), (key2730, -1), (key2751, -1), (key2675, -1), (key2751, -1), (key2675, -1), (key2730, -1), (key2833, 1), (key2915, 1), (key2797, 1), (key2915, 1), (key2797, 1), (key2833, 1)]

theorem rawRowCheck1486 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form0 = rawRow1486 := by decide +kernel

def row1486 : Integer.Sparse Key := [(key2672, 2), (key2675, -2), (key2707, -2), (key2749, 4), (key2751, -2), (key2797, 2), (key2833, 2), (key2915, 2), (key2945, -2), (key2962, -2), (key2978, -4), (key2985, 2), (key2994, 2), (key3004, -2)]

theorem rowCheck1486 : row1486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1486 := by decide +kernel

theorem rowEval1486 (x : Key → ℝ) : Integer.Sparse.eval row1486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1486, Integer.Sparse.eval_collectBalanced, rawRowCheck1486]

def rawRow1487 : Integer.Sparse Key := [(key2978, -2), (key2978, -2), (key2707, -2), (key2994, 1), (key2985, 1), (key2994, 1), (key2730, 1), (key2985, 1), (key2730, 1), (key2749, 2), (key2749, 2), (key2672, 2), (key3004, -1), (key2962, -1), (key3004, -1), (key2945, -1), (key2962, -1), (key2945, -1), (key2751, -1), (key2730, -1), (key2751, -1), (key2675, -1), (key2730, -1), (key2675, -1), (key2915, 1), (key2833, 1), (key2915, 1), (key2797, 1), (key2833, 1), (key2797, 1)]

theorem rawRowCheck1487 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form0 = rawRow1487 := by decide +kernel

def row1487 : Integer.Sparse Key := [(key2672, 2), (key2675, -2), (key2707, -2), (key2749, 4), (key2751, -2), (key2797, 2), (key2833, 2), (key2915, 2), (key2945, -2), (key2962, -2), (key2978, -4), (key2985, 2), (key2994, 2), (key3004, -2)]

theorem rowCheck1487 : row1487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1487 := by decide +kernel

theorem rowEval1487 (x : Key → ℝ) : Integer.Sparse.eval row1487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1487, Integer.Sparse.eval_collectBalanced, rawRowCheck1487]

def rawRow1488 : Integer.Sparse Key := [(key2739, -2), (key2899, -2), (key2999, -2), (key2749, 1), (key2751, 1), (key2906, 1), (key3001, 1), (key2915, 1), (key3004, 1), (key2675, 2), (key2797, 2), (key2946, 2), (key2730, -1), (key2751, -1), (key2833, -1), (key2964, -1), (key2915, -1), (key2994, -1), (key2672, -1), (key2675, -1), (key2707, -1), (key2730, -1), (key2739, -1), (key2749, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2833, 1), (key2899, 1), (key2906, 1)]

theorem rawRowCheck1488 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form0 = rawRow1488 := by decide +kernel

def row1488 : Integer.Sparse Key := [(key2672, -1), (key2675, 1), (key2707, -1), (key2730, -2), (key2739, -3), (key2787, 1), (key2797, 3), (key2810, 1), (key2899, -1), (key2906, 2), (key2946, 2), (key2964, -1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck1488 : row1488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1488 := by decide +kernel

theorem rowEval1488 (x : Key → ℝ) : Integer.Sparse.eval row1488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1488, Integer.Sparse.eval_collectBalanced, rawRowCheck1488]

def rawRow1489 : Integer.Sparse Key := [(key2739, -2), (key2999, -2), (key2899, -2), (key2751, 1), (key2749, 1), (key3001, 1), (key2906, 1), (key3004, 1), (key2915, 1), (key2675, 2), (key2946, 2), (key2797, 2), (key2751, -1), (key2730, -1), (key2964, -1), (key2833, -1), (key2994, -1), (key2915, -1), (key2675, -1), (key2672, -1), (key2730, -1), (key2707, -1), (key2749, -1), (key2739, -1), (key2797, 1), (key2787, 1), (key2833, 1), (key2810, 1), (key2906, 1), (key2899, 1)]

theorem rawRowCheck1489 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form0 = rawRow1489 := by decide +kernel

def row1489 : Integer.Sparse Key := [(key2672, -1), (key2675, 1), (key2707, -1), (key2730, -2), (key2739, -3), (key2787, 1), (key2797, 3), (key2810, 1), (key2899, -1), (key2906, 2), (key2946, 2), (key2964, -1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck1489 : row1489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1489 := by decide +kernel

theorem rowEval1489 (x : Key → ℝ) : Integer.Sparse.eval row1489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1489, Integer.Sparse.eval_collectBalanced, rawRowCheck1489]

def rawRow1490 : Integer.Sparse Key := [(key2899, -2), (key2739, -2), (key2999, -2), (key2906, 1), (key2915, 1), (key2749, 1), (key3004, 1), (key2751, 1), (key3001, 1), (key2797, 2), (key2675, 2), (key2946, 2), (key2833, -1), (key2915, -1), (key2730, -1), (key2994, -1), (key2751, -1), (key2964, -1), (key2707, -1), (key2739, -1), (key2672, -1), (key2749, -1), (key2675, -1), (key2730, -1), (key2810, 1), (key2899, 1), (key2787, 1), (key2906, 1), (key2797, 1), (key2833, 1)]

theorem rawRowCheck1490 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form0 = rawRow1490 := by decide +kernel

def row1490 : Integer.Sparse Key := [(key2672, -1), (key2675, 1), (key2707, -1), (key2730, -2), (key2739, -3), (key2787, 1), (key2797, 3), (key2810, 1), (key2899, -1), (key2906, 2), (key2946, 2), (key2964, -1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck1490 : row1490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1490 := by decide +kernel

theorem rowEval1490 (x : Key → ℝ) : Integer.Sparse.eval row1490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1490, Integer.Sparse.eval_collectBalanced, rawRowCheck1490]

def rawRow1491 : Integer.Sparse Key := [(key2899, -2), (key2999, -2), (key2739, -2), (key2915, 1), (key2906, 1), (key3004, 1), (key2749, 1), (key3001, 1), (key2751, 1), (key2797, 2), (key2946, 2), (key2675, 2), (key2915, -1), (key2833, -1), (key2994, -1), (key2730, -1), (key2964, -1), (key2751, -1), (key2739, -1), (key2707, -1), (key2749, -1), (key2672, -1), (key2730, -1), (key2675, -1), (key2899, 1), (key2810, 1), (key2906, 1), (key2787, 1), (key2833, 1), (key2797, 1)]

theorem rawRowCheck1491 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form0 = rawRow1491 := by decide +kernel

def row1491 : Integer.Sparse Key := [(key2672, -1), (key2675, 1), (key2707, -1), (key2730, -2), (key2739, -3), (key2787, 1), (key2797, 3), (key2810, 1), (key2899, -1), (key2906, 2), (key2946, 2), (key2964, -1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck1491 : row1491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1491 := by decide +kernel

theorem rowEval1491 (x : Key → ℝ) : Integer.Sparse.eval row1491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1491, Integer.Sparse.eval_collectBalanced, rawRowCheck1491]

def rawRow1492 : Integer.Sparse Key := [(key2999, -2), (key2739, -2), (key2899, -2), (key3001, 1), (key3004, 1), (key2751, 1), (key2915, 1), (key2749, 1), (key2906, 1), (key2946, 2), (key2675, 2), (key2797, 2), (key2964, -1), (key2994, -1), (key2751, -1), (key2915, -1), (key2730, -1), (key2833, -1), (key2730, -1), (key2749, -1), (key2675, -1), (key2739, -1), (key2672, -1), (key2707, -1), (key2833, 1), (key2906, 1), (key2797, 1), (key2899, 1), (key2787, 1), (key2810, 1)]

theorem rawRowCheck1492 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form0 = rawRow1492 := by decide +kernel

def row1492 : Integer.Sparse Key := [(key2672, -1), (key2675, 1), (key2707, -1), (key2730, -2), (key2739, -3), (key2787, 1), (key2797, 3), (key2810, 1), (key2899, -1), (key2906, 2), (key2946, 2), (key2964, -1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck1492 : row1492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1492 := by decide +kernel

theorem rowEval1492 (x : Key → ℝ) : Integer.Sparse.eval row1492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1492, Integer.Sparse.eval_collectBalanced, rawRowCheck1492]

def rawRow1493 : Integer.Sparse Key := [(key2999, -2), (key2899, -2), (key2739, -2), (key3004, 1), (key3001, 1), (key2915, 1), (key2751, 1), (key2906, 1), (key2749, 1), (key2946, 2), (key2797, 2), (key2675, 2), (key2994, -1), (key2964, -1), (key2915, -1), (key2751, -1), (key2833, -1), (key2730, -1), (key2749, -1), (key2730, -1), (key2739, -1), (key2675, -1), (key2707, -1), (key2672, -1), (key2906, 1), (key2833, 1), (key2899, 1), (key2797, 1), (key2810, 1), (key2787, 1)]

theorem rawRowCheck1493 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form0 = rawRow1493 := by decide +kernel

def row1493 : Integer.Sparse Key := [(key2672, -1), (key2675, 1), (key2707, -1), (key2730, -2), (key2739, -3), (key2787, 1), (key2797, 3), (key2810, 1), (key2899, -1), (key2906, 2), (key2946, 2), (key2964, -1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck1493 : row1493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1493 := by decide +kernel

theorem rowEval1493 (x : Key → ℝ) : Integer.Sparse.eval row1493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1493, Integer.Sparse.eval_collectBalanced, rawRowCheck1493]

def rawRow1494 : Integer.Sparse Key := [(key1314, -6), (key1294, 2), (key1335, 2), (key1335, 2), (key1544, 6), (key1389, -2), (key1770, -2), (key1770, -2), (key1571, -2), (key1653, -2), (key1653, -2), (key1422, 2), (key1811, 2), (key1811, 2)]

theorem rawRowCheck1494 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form1 = rawRow1494 := by decide +kernel

def row1494 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, -2), (key1422, 2), (key1544, 6), (key1571, -2), (key1653, -4), (key1770, -4), (key1811, 4)]

theorem rowCheck1494 : row1494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1494 := by decide +kernel

theorem rowEval1494 (x : Key → ℝ) : Integer.Sparse.eval row1494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1494, Integer.Sparse.eval_collectBalanced, rawRowCheck1494]

def rawRow1495 : Integer.Sparse Key := [(key1314, -6), (key1335, 2), (key1294, 2), (key1335, 2), (key1544, 6), (key1770, -2), (key1389, -2), (key1770, -2), (key1653, -2), (key1571, -2), (key1653, -2), (key1811, 2), (key1422, 2), (key1811, 2)]

theorem rawRowCheck1495 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form1 = rawRow1495 := by decide +kernel

def row1495 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, -2), (key1422, 2), (key1544, 6), (key1571, -2), (key1653, -4), (key1770, -4), (key1811, 4)]

theorem rowCheck1495 : row1495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1495 := by decide +kernel

theorem rowEval1495 (x : Key → ℝ) : Integer.Sparse.eval row1495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1495, Integer.Sparse.eval_collectBalanced, rawRowCheck1495]

def rawRow1496 : Integer.Sparse Key := [(key1314, -6), (key1335, 2), (key1335, 2), (key1294, 2), (key1544, 6), (key1770, -2), (key1770, -2), (key1389, -2), (key1653, -2), (key1653, -2), (key1571, -2), (key1811, 2), (key1811, 2), (key1422, 2)]

theorem rawRowCheck1496 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form1 = rawRow1496 := by decide +kernel

def row1496 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, -2), (key1422, 2), (key1544, 6), (key1571, -2), (key1653, -4), (key1770, -4), (key1811, 4)]

theorem rowCheck1496 : row1496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1496 := by decide +kernel

theorem rowEval1496 (x : Key → ℝ) : Integer.Sparse.eval row1496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1496, Integer.Sparse.eval_collectBalanced, rawRowCheck1496]

def rawRow1497 : Integer.Sparse Key := [(key1335, -6), (key1294, 2), (key1314, 2), (key1335, 2), (key1770, 6), (key1389, -2), (key1544, -2), (key1770, -2), (key1786, -2), (key1811, -2), (key1838, -2), (key1453, 2), (key1653, 2), (key1838, 2)]

theorem rawRowCheck1497 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form1 = rawRow1497 := by decide +kernel

def row1497 : Integer.Sparse Key := [(key1294, 2), (key1314, 2), (key1335, -4), (key1389, -2), (key1453, 2), (key1544, -2), (key1653, 2), (key1770, 4), (key1786, -2), (key1811, -2)]

theorem rowCheck1497 : row1497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1497 := by decide +kernel

theorem rowEval1497 (x : Key → ℝ) : Integer.Sparse.eval row1497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1497, Integer.Sparse.eval_collectBalanced, rawRowCheck1497]

def rawRow1498 : Integer.Sparse Key := [(key1335, -6), (key1294, 2), (key1335, 2), (key1314, 2), (key1770, 6), (key1389, -2), (key1770, -2), (key1544, -2), (key1786, -2), (key1838, -2), (key1811, -2), (key1453, 2), (key1838, 2), (key1653, 2)]

theorem rawRowCheck1498 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form1 = rawRow1498 := by decide +kernel

def row1498 : Integer.Sparse Key := [(key1294, 2), (key1314, 2), (key1335, -4), (key1389, -2), (key1453, 2), (key1544, -2), (key1653, 2), (key1770, 4), (key1786, -2), (key1811, -2)]

theorem rowCheck1498 : row1498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1498 := by decide +kernel

theorem rowEval1498 (x : Key → ℝ) : Integer.Sparse.eval row1498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1498, Integer.Sparse.eval_collectBalanced, rawRowCheck1498]

def rawRow1499 : Integer.Sparse Key := [(key1335, -6), (key1314, 2), (key1294, 2), (key1335, 2), (key1770, 6), (key1544, -2), (key1389, -2), (key1770, -2), (key1811, -2), (key1786, -2), (key1838, -2), (key1653, 2), (key1453, 2), (key1838, 2)]

theorem rawRowCheck1499 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form1 = rawRow1499 := by decide +kernel

def row1499 : Integer.Sparse Key := [(key1294, 2), (key1314, 2), (key1335, -4), (key1389, -2), (key1453, 2), (key1544, -2), (key1653, 2), (key1770, 4), (key1786, -2), (key1811, -2)]

theorem rowCheck1499 : row1499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1499 := by decide +kernel

theorem rowEval1499 (x : Key → ℝ) : Integer.Sparse.eval row1499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1499, Integer.Sparse.eval_collectBalanced, rawRowCheck1499]

def rawRow1500 : Integer.Sparse Key := [(key1335, -6), (key1314, 2), (key1335, 2), (key1294, 2), (key1770, 6), (key1544, -2), (key1770, -2), (key1389, -2), (key1811, -2), (key1838, -2), (key1786, -2), (key1653, 2), (key1838, 2), (key1453, 2)]

theorem rawRowCheck1500 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form1 = rawRow1500 := by decide +kernel

def row1500 : Integer.Sparse Key := [(key1294, 2), (key1314, 2), (key1335, -4), (key1389, -2), (key1453, 2), (key1544, -2), (key1653, 2), (key1770, 4), (key1786, -2), (key1811, -2)]

theorem rowCheck1500 : row1500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1500 := by decide +kernel

theorem rowEval1500 (x : Key → ℝ) : Integer.Sparse.eval row1500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1500, Integer.Sparse.eval_collectBalanced, rawRowCheck1500]

def rawRow1501 : Integer.Sparse Key := [(key1335, -6), (key1335, 2), (key1294, 2), (key1314, 2), (key1770, 6), (key1770, -2), (key1389, -2), (key1544, -2), (key1838, -2), (key1786, -2), (key1811, -2), (key1838, 2), (key1453, 2), (key1653, 2)]

theorem rawRowCheck1501 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form1 = rawRow1501 := by decide +kernel

def row1501 : Integer.Sparse Key := [(key1294, 2), (key1314, 2), (key1335, -4), (key1389, -2), (key1453, 2), (key1544, -2), (key1653, 2), (key1770, 4), (key1786, -2), (key1811, -2)]

theorem rowCheck1501 : row1501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1501 := by decide +kernel

theorem rowEval1501 (x : Key → ℝ) : Integer.Sparse.eval row1501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1501, Integer.Sparse.eval_collectBalanced, rawRowCheck1501]

def rawRow1502 : Integer.Sparse Key := [(key1335, -6), (key1335, 2), (key1314, 2), (key1294, 2), (key1770, 6), (key1770, -2), (key1544, -2), (key1389, -2), (key1838, -2), (key1811, -2), (key1786, -2), (key1838, 2), (key1653, 2), (key1453, 2)]

theorem rawRowCheck1502 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form1 = rawRow1502 := by decide +kernel

def row1502 : Integer.Sparse Key := [(key1294, 2), (key1314, 2), (key1335, -4), (key1389, -2), (key1453, 2), (key1544, -2), (key1653, 2), (key1770, 4), (key1786, -2), (key1811, -2)]

theorem rowCheck1502 : row1502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1502 := by decide +kernel

theorem rowEval1502 (x : Key → ℝ) : Integer.Sparse.eval row1502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1502, Integer.Sparse.eval_collectBalanced, rawRowCheck1502]

def rawRow1503 : Integer.Sparse Key := [(key1544, -6), (key1571, 2), (key1653, 2), (key1653, 2), (key1314, 6), (key1422, -2), (key1811, -2), (key1811, -2), (key1294, -2), (key1335, -2), (key1335, -2), (key1389, 2), (key1770, 2), (key1770, 2)]

theorem rawRowCheck1503 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form1 = rawRow1503 := by decide +kernel

def row1503 : Integer.Sparse Key := [(key1294, -2), (key1314, 6), (key1335, -4), (key1389, 2), (key1422, -2), (key1544, -6), (key1571, 2), (key1653, 4), (key1770, 4), (key1811, -4)]

theorem rowCheck1503 : row1503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1503 := by decide +kernel

theorem rowEval1503 (x : Key → ℝ) : Integer.Sparse.eval row1503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1503, Integer.Sparse.eval_collectBalanced, rawRowCheck1503]

def rawRow1504 : Integer.Sparse Key := [(key1544, -6), (key1653, 2), (key1571, 2), (key1653, 2), (key1314, 6), (key1811, -2), (key1422, -2), (key1811, -2), (key1335, -2), (key1294, -2), (key1335, -2), (key1770, 2), (key1389, 2), (key1770, 2)]

theorem rawRowCheck1504 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form1 = rawRow1504 := by decide +kernel

def row1504 : Integer.Sparse Key := [(key1294, -2), (key1314, 6), (key1335, -4), (key1389, 2), (key1422, -2), (key1544, -6), (key1571, 2), (key1653, 4), (key1770, 4), (key1811, -4)]

theorem rowCheck1504 : row1504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1504 := by decide +kernel

theorem rowEval1504 (x : Key → ℝ) : Integer.Sparse.eval row1504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1504, Integer.Sparse.eval_collectBalanced, rawRowCheck1504]

def rawRow1505 : Integer.Sparse Key := [(key1544, -6), (key1653, 2), (key1653, 2), (key1571, 2), (key1314, 6), (key1811, -2), (key1811, -2), (key1422, -2), (key1335, -2), (key1335, -2), (key1294, -2), (key1770, 2), (key1770, 2), (key1389, 2)]

theorem rawRowCheck1505 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form1 = rawRow1505 := by decide +kernel

def row1505 : Integer.Sparse Key := [(key1294, -2), (key1314, 6), (key1335, -4), (key1389, 2), (key1422, -2), (key1544, -6), (key1571, 2), (key1653, 4), (key1770, 4), (key1811, -4)]

theorem rowCheck1505 : row1505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1505 := by decide +kernel

theorem rowEval1505 (x : Key → ℝ) : Integer.Sparse.eval row1505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1505, Integer.Sparse.eval_collectBalanced, rawRowCheck1505]

def rawRow1506 : Integer.Sparse Key := [(key1653, -6), (key1544, 2), (key1571, 2), (key1653, 2), (key1811, 6), (key1314, -2), (key1422, -2), (key1811, -2), (key1770, -2), (key1786, -2), (key1838, -2), (key1335, 2), (key1453, 2), (key1838, 2)]

theorem rawRowCheck1506 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form1 = rawRow1506 := by decide +kernel

def row1506 : Integer.Sparse Key := [(key1314, -2), (key1335, 2), (key1422, -2), (key1453, 2), (key1544, 2), (key1571, 2), (key1653, -4), (key1770, -2), (key1786, -2), (key1811, 4)]

theorem rowCheck1506 : row1506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1506 := by decide +kernel

theorem rowEval1506 (x : Key → ℝ) : Integer.Sparse.eval row1506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1506, Integer.Sparse.eval_collectBalanced, rawRowCheck1506]

def rawRow1507 : Integer.Sparse Key := [(key1653, -6), (key1544, 2), (key1653, 2), (key1571, 2), (key1811, 6), (key1314, -2), (key1811, -2), (key1422, -2), (key1770, -2), (key1838, -2), (key1786, -2), (key1335, 2), (key1838, 2), (key1453, 2)]

theorem rawRowCheck1507 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form1 = rawRow1507 := by decide +kernel

def row1507 : Integer.Sparse Key := [(key1314, -2), (key1335, 2), (key1422, -2), (key1453, 2), (key1544, 2), (key1571, 2), (key1653, -4), (key1770, -2), (key1786, -2), (key1811, 4)]

theorem rowCheck1507 : row1507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1507 := by decide +kernel

theorem rowEval1507 (x : Key → ℝ) : Integer.Sparse.eval row1507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1507, Integer.Sparse.eval_collectBalanced, rawRowCheck1507]

def rawRow1508 : Integer.Sparse Key := [(key1653, -6), (key1571, 2), (key1544, 2), (key1653, 2), (key1811, 6), (key1422, -2), (key1314, -2), (key1811, -2), (key1786, -2), (key1770, -2), (key1838, -2), (key1453, 2), (key1335, 2), (key1838, 2)]

theorem rawRowCheck1508 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form1 = rawRow1508 := by decide +kernel

def row1508 : Integer.Sparse Key := [(key1314, -2), (key1335, 2), (key1422, -2), (key1453, 2), (key1544, 2), (key1571, 2), (key1653, -4), (key1770, -2), (key1786, -2), (key1811, 4)]

theorem rowCheck1508 : row1508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1508 := by decide +kernel

theorem rowEval1508 (x : Key → ℝ) : Integer.Sparse.eval row1508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1508, Integer.Sparse.eval_collectBalanced, rawRowCheck1508]

def rawRow1509 : Integer.Sparse Key := [(key1653, -6), (key1571, 2), (key1653, 2), (key1544, 2), (key1811, 6), (key1422, -2), (key1811, -2), (key1314, -2), (key1786, -2), (key1838, -2), (key1770, -2), (key1453, 2), (key1838, 2), (key1335, 2)]

theorem rawRowCheck1509 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form1 = rawRow1509 := by decide +kernel

def row1509 : Integer.Sparse Key := [(key1314, -2), (key1335, 2), (key1422, -2), (key1453, 2), (key1544, 2), (key1571, 2), (key1653, -4), (key1770, -2), (key1786, -2), (key1811, 4)]

theorem rowCheck1509 : row1509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1509 := by decide +kernel

theorem rowEval1509 (x : Key → ℝ) : Integer.Sparse.eval row1509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1509, Integer.Sparse.eval_collectBalanced, rawRowCheck1509]

def rawRow1510 : Integer.Sparse Key := [(key1653, -6), (key1653, 2), (key1544, 2), (key1571, 2), (key1811, 6), (key1811, -2), (key1314, -2), (key1422, -2), (key1838, -2), (key1770, -2), (key1786, -2), (key1838, 2), (key1335, 2), (key1453, 2)]

theorem rawRowCheck1510 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form1 = rawRow1510 := by decide +kernel

def row1510 : Integer.Sparse Key := [(key1314, -2), (key1335, 2), (key1422, -2), (key1453, 2), (key1544, 2), (key1571, 2), (key1653, -4), (key1770, -2), (key1786, -2), (key1811, 4)]

theorem rowCheck1510 : row1510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1510 := by decide +kernel

theorem rowEval1510 (x : Key → ℝ) : Integer.Sparse.eval row1510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1510, Integer.Sparse.eval_collectBalanced, rawRowCheck1510]

def rawRow1511 : Integer.Sparse Key := [(key1653, -6), (key1653, 2), (key1571, 2), (key1544, 2), (key1811, 6), (key1811, -2), (key1422, -2), (key1314, -2), (key1838, -2), (key1786, -2), (key1770, -2), (key1838, 2), (key1453, 2), (key1335, 2)]

theorem rawRowCheck1511 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form1 = rawRow1511 := by decide +kernel

def row1511 : Integer.Sparse Key := [(key1314, -2), (key1335, 2), (key1422, -2), (key1453, 2), (key1544, 2), (key1571, 2), (key1653, -4), (key1770, -2), (key1786, -2), (key1811, 4)]

theorem rowCheck1511 : row1511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1511 := by decide +kernel

theorem rowEval1511 (x : Key → ℝ) : Integer.Sparse.eval row1511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1511, Integer.Sparse.eval_collectBalanced, rawRowCheck1511]

def rawRow1512 : Integer.Sparse Key := [(key1770, -6), (key1786, 2), (key1811, 2), (key1838, 2), (key1335, 6), (key1453, -2), (key1653, -2), (key1838, -2), (key1294, -2), (key1314, -2), (key1335, -2), (key1389, 2), (key1544, 2), (key1770, 2)]

theorem rawRowCheck1512 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form1 = rawRow1512 := by decide +kernel

def row1512 : Integer.Sparse Key := [(key1294, -2), (key1314, -2), (key1335, 4), (key1389, 2), (key1453, -2), (key1544, 2), (key1653, -2), (key1770, -4), (key1786, 2), (key1811, 2)]

theorem rowCheck1512 : row1512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1512 := by decide +kernel

theorem rowEval1512 (x : Key → ℝ) : Integer.Sparse.eval row1512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1512, Integer.Sparse.eval_collectBalanced, rawRowCheck1512]

def rawRow1513 : Integer.Sparse Key := [(key1770, -6), (key1786, 2), (key1838, 2), (key1811, 2), (key1335, 6), (key1453, -2), (key1838, -2), (key1653, -2), (key1294, -2), (key1335, -2), (key1314, -2), (key1389, 2), (key1770, 2), (key1544, 2)]

theorem rawRowCheck1513 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form1 = rawRow1513 := by decide +kernel

def row1513 : Integer.Sparse Key := [(key1294, -2), (key1314, -2), (key1335, 4), (key1389, 2), (key1453, -2), (key1544, 2), (key1653, -2), (key1770, -4), (key1786, 2), (key1811, 2)]

theorem rowCheck1513 : row1513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1513 := by decide +kernel

theorem rowEval1513 (x : Key → ℝ) : Integer.Sparse.eval row1513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1513, Integer.Sparse.eval_collectBalanced, rawRowCheck1513]

def rawRow1514 : Integer.Sparse Key := [(key1770, -6), (key1811, 2), (key1786, 2), (key1838, 2), (key1335, 6), (key1653, -2), (key1453, -2), (key1838, -2), (key1314, -2), (key1294, -2), (key1335, -2), (key1544, 2), (key1389, 2), (key1770, 2)]

theorem rawRowCheck1514 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form1 = rawRow1514 := by decide +kernel

def row1514 : Integer.Sparse Key := [(key1294, -2), (key1314, -2), (key1335, 4), (key1389, 2), (key1453, -2), (key1544, 2), (key1653, -2), (key1770, -4), (key1786, 2), (key1811, 2)]

theorem rowCheck1514 : row1514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1514 := by decide +kernel

theorem rowEval1514 (x : Key → ℝ) : Integer.Sparse.eval row1514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1514, Integer.Sparse.eval_collectBalanced, rawRowCheck1514]

def rawRow1515 : Integer.Sparse Key := [(key1770, -6), (key1811, 2), (key1838, 2), (key1786, 2), (key1335, 6), (key1653, -2), (key1838, -2), (key1453, -2), (key1314, -2), (key1335, -2), (key1294, -2), (key1544, 2), (key1770, 2), (key1389, 2)]

theorem rawRowCheck1515 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form1 = rawRow1515 := by decide +kernel

def row1515 : Integer.Sparse Key := [(key1294, -2), (key1314, -2), (key1335, 4), (key1389, 2), (key1453, -2), (key1544, 2), (key1653, -2), (key1770, -4), (key1786, 2), (key1811, 2)]

theorem rowCheck1515 : row1515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1515 := by decide +kernel

theorem rowEval1515 (x : Key → ℝ) : Integer.Sparse.eval row1515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1515, Integer.Sparse.eval_collectBalanced, rawRowCheck1515]

def rawRow1516 : Integer.Sparse Key := [(key1770, -6), (key1838, 2), (key1786, 2), (key1811, 2), (key1335, 6), (key1838, -2), (key1453, -2), (key1653, -2), (key1335, -2), (key1294, -2), (key1314, -2), (key1770, 2), (key1389, 2), (key1544, 2)]

theorem rawRowCheck1516 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form1 = rawRow1516 := by decide +kernel

def row1516 : Integer.Sparse Key := [(key1294, -2), (key1314, -2), (key1335, 4), (key1389, 2), (key1453, -2), (key1544, 2), (key1653, -2), (key1770, -4), (key1786, 2), (key1811, 2)]

theorem rowCheck1516 : row1516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1516 := by decide +kernel

theorem rowEval1516 (x : Key → ℝ) : Integer.Sparse.eval row1516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1516, Integer.Sparse.eval_collectBalanced, rawRowCheck1516]

def rawRow1517 : Integer.Sparse Key := [(key1770, -6), (key1838, 2), (key1811, 2), (key1786, 2), (key1335, 6), (key1838, -2), (key1653, -2), (key1453, -2), (key1335, -2), (key1314, -2), (key1294, -2), (key1770, 2), (key1544, 2), (key1389, 2)]

theorem rawRowCheck1517 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form1 = rawRow1517 := by decide +kernel

def row1517 : Integer.Sparse Key := [(key1294, -2), (key1314, -2), (key1335, 4), (key1389, 2), (key1453, -2), (key1544, 2), (key1653, -2), (key1770, -4), (key1786, 2), (key1811, 2)]

theorem rowCheck1517 : row1517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1517 := by decide +kernel

theorem rowEval1517 (x : Key → ℝ) : Integer.Sparse.eval row1517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1517, Integer.Sparse.eval_collectBalanced, rawRowCheck1517]

def rawRow1518 : Integer.Sparse Key := [(key1811, -6), (key1770, 2), (key1786, 2), (key1838, 2), (key1653, 6), (key1335, -2), (key1453, -2), (key1838, -2), (key1544, -2), (key1571, -2), (key1653, -2), (key1314, 2), (key1422, 2), (key1811, 2)]

theorem rawRowCheck1518 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form1 = rawRow1518 := by decide +kernel

def row1518 : Integer.Sparse Key := [(key1314, 2), (key1335, -2), (key1422, 2), (key1453, -2), (key1544, -2), (key1571, -2), (key1653, 4), (key1770, 2), (key1786, 2), (key1811, -4)]

theorem rowCheck1518 : row1518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1518 := by decide +kernel

theorem rowEval1518 (x : Key → ℝ) : Integer.Sparse.eval row1518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1518, Integer.Sparse.eval_collectBalanced, rawRowCheck1518]

def rawRow1519 : Integer.Sparse Key := [(key1811, -6), (key1770, 2), (key1838, 2), (key1786, 2), (key1653, 6), (key1335, -2), (key1838, -2), (key1453, -2), (key1544, -2), (key1653, -2), (key1571, -2), (key1314, 2), (key1811, 2), (key1422, 2)]

theorem rawRowCheck1519 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form1 = rawRow1519 := by decide +kernel

def row1519 : Integer.Sparse Key := [(key1314, 2), (key1335, -2), (key1422, 2), (key1453, -2), (key1544, -2), (key1571, -2), (key1653, 4), (key1770, 2), (key1786, 2), (key1811, -4)]

theorem rowCheck1519 : row1519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1519 := by decide +kernel

theorem rowEval1519 (x : Key → ℝ) : Integer.Sparse.eval row1519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1519, Integer.Sparse.eval_collectBalanced, rawRowCheck1519]

def rawRow1520 : Integer.Sparse Key := [(key1811, -6), (key1786, 2), (key1770, 2), (key1838, 2), (key1653, 6), (key1453, -2), (key1335, -2), (key1838, -2), (key1571, -2), (key1544, -2), (key1653, -2), (key1422, 2), (key1314, 2), (key1811, 2)]

theorem rawRowCheck1520 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form1 = rawRow1520 := by decide +kernel

def row1520 : Integer.Sparse Key := [(key1314, 2), (key1335, -2), (key1422, 2), (key1453, -2), (key1544, -2), (key1571, -2), (key1653, 4), (key1770, 2), (key1786, 2), (key1811, -4)]

theorem rowCheck1520 : row1520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1520 := by decide +kernel

theorem rowEval1520 (x : Key → ℝ) : Integer.Sparse.eval row1520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1520, Integer.Sparse.eval_collectBalanced, rawRowCheck1520]

def rawRow1521 : Integer.Sparse Key := [(key1811, -6), (key1786, 2), (key1838, 2), (key1770, 2), (key1653, 6), (key1453, -2), (key1838, -2), (key1335, -2), (key1571, -2), (key1653, -2), (key1544, -2), (key1422, 2), (key1811, 2), (key1314, 2)]

theorem rawRowCheck1521 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form1 = rawRow1521 := by decide +kernel

def row1521 : Integer.Sparse Key := [(key1314, 2), (key1335, -2), (key1422, 2), (key1453, -2), (key1544, -2), (key1571, -2), (key1653, 4), (key1770, 2), (key1786, 2), (key1811, -4)]

theorem rowCheck1521 : row1521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1521 := by decide +kernel

theorem rowEval1521 (x : Key → ℝ) : Integer.Sparse.eval row1521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1521, Integer.Sparse.eval_collectBalanced, rawRowCheck1521]

def rawRow1522 : Integer.Sparse Key := [(key1811, -6), (key1838, 2), (key1770, 2), (key1786, 2), (key1653, 6), (key1838, -2), (key1335, -2), (key1453, -2), (key1653, -2), (key1544, -2), (key1571, -2), (key1811, 2), (key1314, 2), (key1422, 2)]

theorem rawRowCheck1522 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form1 = rawRow1522 := by decide +kernel

def row1522 : Integer.Sparse Key := [(key1314, 2), (key1335, -2), (key1422, 2), (key1453, -2), (key1544, -2), (key1571, -2), (key1653, 4), (key1770, 2), (key1786, 2), (key1811, -4)]

theorem rowCheck1522 : row1522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1522 := by decide +kernel

theorem rowEval1522 (x : Key → ℝ) : Integer.Sparse.eval row1522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1522, Integer.Sparse.eval_collectBalanced, rawRowCheck1522]

def rawRow1523 : Integer.Sparse Key := [(key1811, -6), (key1838, 2), (key1786, 2), (key1770, 2), (key1653, 6), (key1838, -2), (key1453, -2), (key1335, -2), (key1653, -2), (key1571, -2), (key1544, -2), (key1811, 2), (key1422, 2), (key1314, 2)]

theorem rawRowCheck1523 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form1 = rawRow1523 := by decide +kernel

def row1523 : Integer.Sparse Key := [(key1314, 2), (key1335, -2), (key1422, 2), (key1453, -2), (key1544, -2), (key1571, -2), (key1653, 4), (key1770, 2), (key1786, 2), (key1811, -4)]

theorem rowCheck1523 : row1523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1523 := by decide +kernel

theorem rowEval1523 (x : Key → ℝ) : Integer.Sparse.eval row1523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1523, Integer.Sparse.eval_collectBalanced, rawRowCheck1523]

def rawRow1524 : Integer.Sparse Key := [(key2628, -2), (key2628, -2), (key2641, -2), (key2612, 1), (key2616, 1), (key2640, 1), (key2640, 1), (key2660, 1), (key2660, 1), (key2706, 2), (key2706, 2), (key2753, 2), (key2671, -1), (key2671, -1), (key2726, -1), (key2726, -1), (key2758, -1), (key2758, -1), (key2809, -1), (key2809, -1), (key2860, -1), (key2860, -1), (key2920, -1), (key2920, -1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1), (key2923, 1), (key2923, 1)]

theorem rawRowCheck1524 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form2 = rawRow1524 := by decide +kernel

def row1524 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 2), (key2641, -2), (key2660, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2753, 2), (key2758, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2920, -2), (key2923, 2)]

theorem rowCheck1524 : row1524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1524 := by decide +kernel

theorem rowEval1524 (x : Key → ℝ) : Integer.Sparse.eval row1524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1524, Integer.Sparse.eval_collectBalanced, rawRowCheck1524]

def rawRow1525 : Integer.Sparse Key := [(key2628, -2), (key2641, -2), (key2628, -2), (key2646, 1), (key2653, 1), (key2612, 1), (key2653, 1), (key2616, 1), (key2640, 1), (key2706, 2), (key2753, 2), (key2706, 2), (key2726, -1), (key2758, -1), (key2671, -1), (key2758, -1), (key2671, -1), (key2726, -1), (key2860, -1), (key2920, -1), (key2809, -1), (key2920, -1), (key2809, -1), (key2860, -1), (key2870, 1), (key2923, 1), (key2786, 1), (key2923, 1), (key2786, 1), (key2870, 1)]

theorem rawRowCheck1525 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form2 = rawRow1525 := by decide +kernel

def row1525 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2753, 2), (key2758, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2920, -2), (key2923, 2)]

theorem rowCheck1525 : row1525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1525 := by decide +kernel

theorem rowEval1525 (x : Key → ℝ) : Integer.Sparse.eval row1525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1525, Integer.Sparse.eval_collectBalanced, rawRowCheck1525]

def rawRow1526 : Integer.Sparse Key := [(key2641, -2), (key2628, -2), (key2628, -2), (key2653, 1), (key2646, 1), (key2653, 1), (key2612, 1), (key2640, 1), (key2616, 1), (key2753, 2), (key2706, 2), (key2706, 2), (key2758, -1), (key2726, -1), (key2758, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2920, -1), (key2860, -1), (key2920, -1), (key2809, -1), (key2860, -1), (key2809, -1), (key2923, 1), (key2870, 1), (key2923, 1), (key2786, 1), (key2870, 1), (key2786, 1)]

theorem rawRowCheck1526 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form2 = rawRow1526 := by decide +kernel

def row1526 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2753, 2), (key2758, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2920, -2), (key2923, 2)]

theorem rowCheck1526 : row1526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1526 := by decide +kernel

theorem rowEval1526 (x : Key → ℝ) : Integer.Sparse.eval row1526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1526, Integer.Sparse.eval_collectBalanced, rawRowCheck1526]

def rawRow1527 : Integer.Sparse Key := [(key2646, -2), (key2648, -2), (key2653, -2), (key2612, 1), (key2618, 1), (key2628, 1), (key2648, 1), (key2641, 1), (key2653, 1), (key2726, 2), (key2732, 2), (key2758, 2), (key2671, -1), (key2676, -1), (key2706, -1), (key2732, -1), (key2753, -1), (key2758, -1), (key2829, -1), (key2835, -1), (key2870, -1), (key2885, -1), (key2923, -1), (key2927, -1), (key2794, 1), (key2798, 1), (key2860, 1), (key2885, 1), (key2920, 1), (key2927, 1)]

theorem rawRowCheck1527 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form2 = rawRow1527 := by decide +kernel

def row1527 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

theorem rowCheck1527 : row1527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1527 := by decide +kernel

theorem rowEval1527 (x : Key → ℝ) : Integer.Sparse.eval row1527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1527, Integer.Sparse.eval_collectBalanced, rawRowCheck1527]

def rawRow1528 : Integer.Sparse Key := [(key2648, -2), (key2646, -2), (key2653, -2), (key2618, 1), (key2612, 1), (key2648, 1), (key2628, 1), (key2653, 1), (key2641, 1), (key2732, 2), (key2726, 2), (key2758, 2), (key2676, -1), (key2671, -1), (key2732, -1), (key2706, -1), (key2758, -1), (key2753, -1), (key2835, -1), (key2829, -1), (key2885, -1), (key2870, -1), (key2927, -1), (key2923, -1), (key2798, 1), (key2794, 1), (key2885, 1), (key2860, 1), (key2927, 1), (key2920, 1)]

theorem rawRowCheck1528 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form2 = rawRow1528 := by decide +kernel

def row1528 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

theorem rowCheck1528 : row1528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1528 := by decide +kernel

theorem rowEval1528 (x : Key → ℝ) : Integer.Sparse.eval row1528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1528, Integer.Sparse.eval_collectBalanced, rawRowCheck1528]

def rawRow1529 : Integer.Sparse Key := [(key2646, -2), (key2653, -2), (key2648, -2), (key2628, 1), (key2641, 1), (key2612, 1), (key2653, 1), (key2618, 1), (key2648, 1), (key2726, 2), (key2758, 2), (key2732, 2), (key2706, -1), (key2753, -1), (key2671, -1), (key2758, -1), (key2676, -1), (key2732, -1), (key2870, -1), (key2923, -1), (key2829, -1), (key2927, -1), (key2835, -1), (key2885, -1), (key2860, 1), (key2920, 1), (key2794, 1), (key2927, 1), (key2798, 1), (key2885, 1)]

theorem rawRowCheck1529 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form2 = rawRow1529 := by decide +kernel

def row1529 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

theorem rowCheck1529 : row1529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1529 := by decide +kernel

theorem rowEval1529 (x : Key → ℝ) : Integer.Sparse.eval row1529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1529, Integer.Sparse.eval_collectBalanced, rawRowCheck1529]

def rawRow1530 : Integer.Sparse Key := [(key2653, -2), (key2646, -2), (key2648, -2), (key2641, 1), (key2628, 1), (key2653, 1), (key2612, 1), (key2648, 1), (key2618, 1), (key2758, 2), (key2726, 2), (key2732, 2), (key2753, -1), (key2706, -1), (key2758, -1), (key2671, -1), (key2732, -1), (key2676, -1), (key2923, -1), (key2870, -1), (key2927, -1), (key2829, -1), (key2885, -1), (key2835, -1), (key2920, 1), (key2860, 1), (key2927, 1), (key2794, 1), (key2885, 1), (key2798, 1)]

theorem rawRowCheck1530 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form2 = rawRow1530 := by decide +kernel

def row1530 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

theorem rowCheck1530 : row1530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1530 := by decide +kernel

theorem rowEval1530 (x : Key → ℝ) : Integer.Sparse.eval row1530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1530, Integer.Sparse.eval_collectBalanced, rawRowCheck1530]

def rawRow1531 : Integer.Sparse Key := [(key2648, -2), (key2653, -2), (key2646, -2), (key2648, 1), (key2653, 1), (key2618, 1), (key2641, 1), (key2612, 1), (key2628, 1), (key2732, 2), (key2758, 2), (key2726, 2), (key2732, -1), (key2758, -1), (key2676, -1), (key2753, -1), (key2671, -1), (key2706, -1), (key2885, -1), (key2927, -1), (key2835, -1), (key2923, -1), (key2829, -1), (key2870, -1), (key2885, 1), (key2927, 1), (key2798, 1), (key2920, 1), (key2794, 1), (key2860, 1)]

theorem rawRowCheck1531 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form2 = rawRow1531 := by decide +kernel

def row1531 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

theorem rowCheck1531 : row1531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1531 := by decide +kernel

theorem rowEval1531 (x : Key → ℝ) : Integer.Sparse.eval row1531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1531, Integer.Sparse.eval_collectBalanced, rawRowCheck1531]

def rawRow1532 : Integer.Sparse Key := [(key2653, -2), (key2648, -2), (key2646, -2), (key2653, 1), (key2648, 1), (key2641, 1), (key2618, 1), (key2628, 1), (key2612, 1), (key2758, 2), (key2732, 2), (key2726, 2), (key2758, -1), (key2732, -1), (key2753, -1), (key2676, -1), (key2706, -1), (key2671, -1), (key2927, -1), (key2885, -1), (key2923, -1), (key2835, -1), (key2870, -1), (key2829, -1), (key2927, 1), (key2885, 1), (key2920, 1), (key2798, 1), (key2860, 1), (key2794, 1)]

theorem rawRowCheck1532 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form2 = rawRow1532 := by decide +kernel

def row1532 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

theorem rowCheck1532 : row1532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1532 := by decide +kernel

theorem rowEval1532 (x : Key → ℝ) : Integer.Sparse.eval row1532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1532, Integer.Sparse.eval_collectBalanced, rawRowCheck1532]

def rawRow1533 : Integer.Sparse Key := [(key2782, -2), (key2782, -2), (key2795, -2), (key2805, 1), (key2805, 1), (key2893, 1), (key2893, 1), (key2897, 1), (key2897, 1), (key2628, 2), (key2628, 2), (key2641, 2), (key2702, -1), (key2702, -1), (key2972, -1), (key2972, -1), (key2976, -1), (key2976, -1), (key2612, -1), (key2616, -1), (key2640, -1), (key2640, -1), (key2660, -1), (key2660, -1), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2758, 1), (key2758, 1)]

theorem rawRowCheck1533 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form2 = rawRow1533 := by decide +kernel

def row1533 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, 4), (key2640, -2), (key2641, 2), (key2660, -2), (key2671, 2), (key2702, -2), (key2726, 2), (key2758, 2), (key2782, -4), (key2795, -2), (key2805, 2), (key2893, 2), (key2897, 2), (key2972, -2), (key2976, -2)]

theorem rowCheck1533 : row1533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1533 := by decide +kernel

theorem rowEval1533 (x : Key → ℝ) : Integer.Sparse.eval row1533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1533, Integer.Sparse.eval_collectBalanced, rawRowCheck1533]

def rawRow1534 : Integer.Sparse Key := [(key2782, -2), (key2795, -2), (key2782, -2), (key2893, 1), (key2897, 1), (key2805, 1), (key2897, 1), (key2805, 1), (key2893, 1), (key2628, 2), (key2641, 2), (key2628, 2), (key2972, -1), (key2976, -1), (key2702, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2646, -1), (key2653, -1), (key2612, -1), (key2653, -1), (key2616, -1), (key2640, -1), (key2726, 1), (key2758, 1), (key2671, 1), (key2758, 1), (key2671, 1), (key2726, 1)]

theorem rawRowCheck1534 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form2 = rawRow1534 := by decide +kernel

def row1534 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, 4), (key2640, -1), (key2641, 2), (key2646, -1), (key2653, -2), (key2671, 2), (key2702, -2), (key2726, 2), (key2758, 2), (key2782, -4), (key2795, -2), (key2805, 2), (key2893, 2), (key2897, 2), (key2972, -2), (key2976, -2)]

theorem rowCheck1534 : row1534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1534 := by decide +kernel

theorem rowEval1534 (x : Key → ℝ) : Integer.Sparse.eval row1534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1534, Integer.Sparse.eval_collectBalanced, rawRowCheck1534]

def rawRow1535 : Integer.Sparse Key := [(key2795, -2), (key2782, -2), (key2782, -2), (key2897, 1), (key2893, 1), (key2897, 1), (key2805, 1), (key2893, 1), (key2805, 1), (key2641, 2), (key2628, 2), (key2628, 2), (key2976, -1), (key2972, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2702, -1), (key2653, -1), (key2646, -1), (key2653, -1), (key2612, -1), (key2640, -1), (key2616, -1), (key2758, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2671, 1)]

theorem rawRowCheck1535 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form2 = rawRow1535 := by decide +kernel

def row1535 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, 4), (key2640, -1), (key2641, 2), (key2646, -1), (key2653, -2), (key2671, 2), (key2702, -2), (key2726, 2), (key2758, 2), (key2782, -4), (key2795, -2), (key2805, 2), (key2893, 2), (key2897, 2), (key2972, -2), (key2976, -2)]

theorem rowCheck1535 : row1535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1535 := by decide +kernel

theorem rowEval1535 (x : Key → ℝ) : Integer.Sparse.eval row1535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1535, Integer.Sparse.eval_collectBalanced, rawRowCheck1535]

end MUB6.Certificate.GramRows

end OAI
