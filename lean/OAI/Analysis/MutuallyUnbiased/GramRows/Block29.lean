import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1024 : Integer.Sparse Key := [(key1543, -6), (key1388, 2), (key1543, 2), (key1553, 2), (key1570, 6), (key1293, -2), (key1570, -2), (key1590, -2), (key1421, -2), (key1619, -2), (key1621, -2), (key1313, 2), (key1619, 2), (key1630, 2)]

theorem rawRowCheck1024 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form4 = rawRow1024 := by decide +kernel

def row1024 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

theorem rowCheck1024 : row1024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1024 := by decide +kernel

theorem rowEval1024 (x : Key → ℝ) : Integer.Sparse.eval row1024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1024, Integer.Sparse.eval_collectBalanced, rawRowCheck1024]

def rawRow1025 : Integer.Sparse Key := [(key1543, -6), (key1388, 2), (key1553, 2), (key1543, 2), (key1570, 6), (key1293, -2), (key1590, -2), (key1570, -2), (key1421, -2), (key1621, -2), (key1619, -2), (key1313, 2), (key1630, 2), (key1619, 2)]

theorem rawRowCheck1025 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form4 = rawRow1025 := by decide +kernel

def row1025 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

theorem rowCheck1025 : row1025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1025 := by decide +kernel

theorem rowEval1025 (x : Key → ℝ) : Integer.Sparse.eval row1025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1025, Integer.Sparse.eval_collectBalanced, rawRowCheck1025]

def rawRow1026 : Integer.Sparse Key := [(key1543, -6), (key1543, 2), (key1388, 2), (key1553, 2), (key1570, 6), (key1570, -2), (key1293, -2), (key1590, -2), (key1619, -2), (key1421, -2), (key1621, -2), (key1619, 2), (key1313, 2), (key1630, 2)]

theorem rawRowCheck1026 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form4 = rawRow1026 := by decide +kernel

def row1026 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

theorem rowCheck1026 : row1026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1026 := by decide +kernel

theorem rowEval1026 (x : Key → ℝ) : Integer.Sparse.eval row1026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1026, Integer.Sparse.eval_collectBalanced, rawRowCheck1026]

def rawRow1027 : Integer.Sparse Key := [(key1543, -6), (key1543, 2), (key1553, 2), (key1388, 2), (key1570, 6), (key1570, -2), (key1590, -2), (key1293, -2), (key1619, -2), (key1621, -2), (key1421, -2), (key1619, 2), (key1630, 2), (key1313, 2)]

theorem rawRowCheck1027 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form4 = rawRow1027 := by decide +kernel

def row1027 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

theorem rowCheck1027 : row1027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1027 := by decide +kernel

theorem rowEval1027 (x : Key → ℝ) : Integer.Sparse.eval row1027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1027, Integer.Sparse.eval_collectBalanced, rawRowCheck1027]

def rawRow1028 : Integer.Sparse Key := [(key1543, -6), (key1553, 2), (key1388, 2), (key1543, 2), (key1570, 6), (key1590, -2), (key1293, -2), (key1570, -2), (key1621, -2), (key1421, -2), (key1619, -2), (key1630, 2), (key1313, 2), (key1619, 2)]

theorem rawRowCheck1028 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form4 = rawRow1028 := by decide +kernel

def row1028 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

theorem rowCheck1028 : row1028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1028 := by decide +kernel

theorem rowEval1028 (x : Key → ℝ) : Integer.Sparse.eval row1028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1028, Integer.Sparse.eval_collectBalanced, rawRowCheck1028]

def rawRow1029 : Integer.Sparse Key := [(key1543, -6), (key1553, 2), (key1543, 2), (key1388, 2), (key1570, 6), (key1590, -2), (key1570, -2), (key1293, -2), (key1621, -2), (key1619, -2), (key1421, -2), (key1630, 2), (key1619, 2), (key1313, 2)]

theorem rawRowCheck1029 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form4 = rawRow1029 := by decide +kernel

def row1029 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

theorem rowCheck1029 : row1029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1029 := by decide +kernel

theorem rowEval1029 (x : Key → ℝ) : Integer.Sparse.eval row1029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1029, Integer.Sparse.eval_collectBalanced, rawRowCheck1029]

def rawRow1030 : Integer.Sparse Key := [(key1553, -6), (key1388, 2), (key1543, 2), (key1543, 2), (key1590, 6), (key1293, -2), (key1570, -2), (key1570, -2), (key1441, -2), (key1630, -2), (key1630, -2), (key1323, 2), (key1621, 2), (key1621, 2)]

theorem rawRowCheck1030 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form4 = rawRow1030 := by decide +kernel

def row1030 : Integer.Sparse Key := [(key1293, -2), (key1323, 2), (key1388, 2), (key1441, -2), (key1543, 4), (key1553, -6), (key1570, -4), (key1590, 6), (key1621, 4), (key1630, -4)]

theorem rowCheck1030 : row1030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1030 := by decide +kernel

theorem rowEval1030 (x : Key → ℝ) : Integer.Sparse.eval row1030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1030, Integer.Sparse.eval_collectBalanced, rawRowCheck1030]

def rawRow1031 : Integer.Sparse Key := [(key1553, -6), (key1543, 2), (key1388, 2), (key1543, 2), (key1590, 6), (key1570, -2), (key1293, -2), (key1570, -2), (key1630, -2), (key1441, -2), (key1630, -2), (key1621, 2), (key1323, 2), (key1621, 2)]

theorem rawRowCheck1031 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form4 = rawRow1031 := by decide +kernel

def row1031 : Integer.Sparse Key := [(key1293, -2), (key1323, 2), (key1388, 2), (key1441, -2), (key1543, 4), (key1553, -6), (key1570, -4), (key1590, 6), (key1621, 4), (key1630, -4)]

theorem rowCheck1031 : row1031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1031 := by decide +kernel

theorem rowEval1031 (x : Key → ℝ) : Integer.Sparse.eval row1031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1031, Integer.Sparse.eval_collectBalanced, rawRowCheck1031]

def rawRow1032 : Integer.Sparse Key := [(key1553, -6), (key1543, 2), (key1543, 2), (key1388, 2), (key1590, 6), (key1570, -2), (key1570, -2), (key1293, -2), (key1630, -2), (key1630, -2), (key1441, -2), (key1621, 2), (key1621, 2), (key1323, 2)]

theorem rawRowCheck1032 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form4 = rawRow1032 := by decide +kernel

def row1032 : Integer.Sparse Key := [(key1293, -2), (key1323, 2), (key1388, 2), (key1441, -2), (key1543, 4), (key1553, -6), (key1570, -4), (key1590, 6), (key1621, 4), (key1630, -4)]

theorem rowCheck1032 : row1032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1032 := by decide +kernel

theorem rowEval1032 (x : Key → ℝ) : Integer.Sparse.eval row1032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1032, Integer.Sparse.eval_collectBalanced, rawRowCheck1032]

def rawRow1033 : Integer.Sparse Key := [(key1570, -6), (key1421, 2), (key1619, 2), (key1621, 2), (key1543, 6), (key1313, -2), (key1619, -2), (key1630, -2), (key1388, -2), (key1543, -2), (key1553, -2), (key1293, 2), (key1570, 2), (key1590, 2)]

theorem rawRowCheck1033 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form4 = rawRow1033 := by decide +kernel

def row1033 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

theorem rowCheck1033 : row1033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1033 := by decide +kernel

theorem rowEval1033 (x : Key → ℝ) : Integer.Sparse.eval row1033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1033, Integer.Sparse.eval_collectBalanced, rawRowCheck1033]

def rawRow1034 : Integer.Sparse Key := [(key1570, -6), (key1421, 2), (key1621, 2), (key1619, 2), (key1543, 6), (key1313, -2), (key1630, -2), (key1619, -2), (key1388, -2), (key1553, -2), (key1543, -2), (key1293, 2), (key1590, 2), (key1570, 2)]

theorem rawRowCheck1034 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form4 = rawRow1034 := by decide +kernel

def row1034 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

theorem rowCheck1034 : row1034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1034 := by decide +kernel

theorem rowEval1034 (x : Key → ℝ) : Integer.Sparse.eval row1034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1034, Integer.Sparse.eval_collectBalanced, rawRowCheck1034]

def rawRow1035 : Integer.Sparse Key := [(key1570, -6), (key1619, 2), (key1421, 2), (key1621, 2), (key1543, 6), (key1619, -2), (key1313, -2), (key1630, -2), (key1543, -2), (key1388, -2), (key1553, -2), (key1570, 2), (key1293, 2), (key1590, 2)]

theorem rawRowCheck1035 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form4 = rawRow1035 := by decide +kernel

def row1035 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

theorem rowCheck1035 : row1035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1035 := by decide +kernel

theorem rowEval1035 (x : Key → ℝ) : Integer.Sparse.eval row1035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1035, Integer.Sparse.eval_collectBalanced, rawRowCheck1035]

def rawRow1036 : Integer.Sparse Key := [(key1570, -6), (key1619, 2), (key1621, 2), (key1421, 2), (key1543, 6), (key1619, -2), (key1630, -2), (key1313, -2), (key1543, -2), (key1553, -2), (key1388, -2), (key1570, 2), (key1590, 2), (key1293, 2)]

theorem rawRowCheck1036 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form4 = rawRow1036 := by decide +kernel

def row1036 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

theorem rowCheck1036 : row1036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1036 := by decide +kernel

theorem rowEval1036 (x : Key → ℝ) : Integer.Sparse.eval row1036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1036, Integer.Sparse.eval_collectBalanced, rawRowCheck1036]

def rawRow1037 : Integer.Sparse Key := [(key1570, -6), (key1621, 2), (key1421, 2), (key1619, 2), (key1543, 6), (key1630, -2), (key1313, -2), (key1619, -2), (key1553, -2), (key1388, -2), (key1543, -2), (key1590, 2), (key1293, 2), (key1570, 2)]

theorem rawRowCheck1037 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form4 = rawRow1037 := by decide +kernel

def row1037 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

theorem rowCheck1037 : row1037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1037 := by decide +kernel

theorem rowEval1037 (x : Key → ℝ) : Integer.Sparse.eval row1037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1037, Integer.Sparse.eval_collectBalanced, rawRowCheck1037]

def rawRow1038 : Integer.Sparse Key := [(key1570, -6), (key1621, 2), (key1619, 2), (key1421, 2), (key1543, 6), (key1630, -2), (key1619, -2), (key1313, -2), (key1553, -2), (key1543, -2), (key1388, -2), (key1590, 2), (key1570, 2), (key1293, 2)]

theorem rawRowCheck1038 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form4 = rawRow1038 := by decide +kernel

def row1038 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

theorem rowCheck1038 : row1038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1038 := by decide +kernel

theorem rowEval1038 (x : Key → ℝ) : Integer.Sparse.eval row1038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1038, Integer.Sparse.eval_collectBalanced, rawRowCheck1038]

def rawRow1039 : Integer.Sparse Key := [(key1621, -6), (key1421, 2), (key1570, 2), (key1619, 2), (key1630, 6), (key1313, -2), (key1543, -2), (key1619, -2), (key1441, -2), (key1590, -2), (key1630, -2), (key1323, 2), (key1553, 2), (key1621, 2)]

theorem rawRowCheck1039 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form4 = rawRow1039 := by decide +kernel

def row1039 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

theorem rowCheck1039 : row1039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1039 := by decide +kernel

theorem rowEval1039 (x : Key → ℝ) : Integer.Sparse.eval row1039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1039, Integer.Sparse.eval_collectBalanced, rawRowCheck1039]

def rawRow1040 : Integer.Sparse Key := [(key1621, -6), (key1421, 2), (key1619, 2), (key1570, 2), (key1630, 6), (key1313, -2), (key1619, -2), (key1543, -2), (key1441, -2), (key1630, -2), (key1590, -2), (key1323, 2), (key1621, 2), (key1553, 2)]

theorem rawRowCheck1040 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form4 = rawRow1040 := by decide +kernel

def row1040 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

theorem rowCheck1040 : row1040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1040 := by decide +kernel

theorem rowEval1040 (x : Key → ℝ) : Integer.Sparse.eval row1040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1040, Integer.Sparse.eval_collectBalanced, rawRowCheck1040]

def rawRow1041 : Integer.Sparse Key := [(key1621, -6), (key1570, 2), (key1421, 2), (key1619, 2), (key1630, 6), (key1543, -2), (key1313, -2), (key1619, -2), (key1590, -2), (key1441, -2), (key1630, -2), (key1553, 2), (key1323, 2), (key1621, 2)]

theorem rawRowCheck1041 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form4 = rawRow1041 := by decide +kernel

def row1041 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

theorem rowCheck1041 : row1041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1041 := by decide +kernel

theorem rowEval1041 (x : Key → ℝ) : Integer.Sparse.eval row1041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1041, Integer.Sparse.eval_collectBalanced, rawRowCheck1041]

def rawRow1042 : Integer.Sparse Key := [(key1621, -6), (key1570, 2), (key1619, 2), (key1421, 2), (key1630, 6), (key1543, -2), (key1619, -2), (key1313, -2), (key1590, -2), (key1630, -2), (key1441, -2), (key1553, 2), (key1621, 2), (key1323, 2)]

theorem rawRowCheck1042 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form4 = rawRow1042 := by decide +kernel

def row1042 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

theorem rowCheck1042 : row1042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1042 := by decide +kernel

theorem rowEval1042 (x : Key → ℝ) : Integer.Sparse.eval row1042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1042, Integer.Sparse.eval_collectBalanced, rawRowCheck1042]

def rawRow1043 : Integer.Sparse Key := [(key1621, -6), (key1619, 2), (key1421, 2), (key1570, 2), (key1630, 6), (key1619, -2), (key1313, -2), (key1543, -2), (key1630, -2), (key1441, -2), (key1590, -2), (key1621, 2), (key1323, 2), (key1553, 2)]

theorem rawRowCheck1043 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form4 = rawRow1043 := by decide +kernel

def row1043 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

theorem rowCheck1043 : row1043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1043 := by decide +kernel

theorem rowEval1043 (x : Key → ℝ) : Integer.Sparse.eval row1043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1043, Integer.Sparse.eval_collectBalanced, rawRowCheck1043]

def rawRow1044 : Integer.Sparse Key := [(key1621, -6), (key1619, 2), (key1570, 2), (key1421, 2), (key1630, 6), (key1619, -2), (key1543, -2), (key1313, -2), (key1630, -2), (key1590, -2), (key1441, -2), (key1621, 2), (key1553, 2), (key1323, 2)]

theorem rawRowCheck1044 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form4 = rawRow1044 := by decide +kernel

def row1044 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

theorem rowCheck1044 : row1044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1044 := by decide +kernel

theorem rowEval1044 (x : Key → ℝ) : Integer.Sparse.eval row1044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1044, Integer.Sparse.eval_collectBalanced, rawRowCheck1044]

def rawRow1045 : Integer.Sparse Key := [(key1590, -6), (key1441, 2), (key1630, 2), (key1630, 2), (key1553, 6), (key1323, -2), (key1621, -2), (key1621, -2), (key1388, -2), (key1543, -2), (key1543, -2), (key1293, 2), (key1570, 2), (key1570, 2)]

theorem rawRowCheck1045 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form4 = rawRow1045 := by decide +kernel

def row1045 : Integer.Sparse Key := [(key1293, 2), (key1323, -2), (key1388, -2), (key1441, 2), (key1543, -4), (key1553, 6), (key1570, 4), (key1590, -6), (key1621, -4), (key1630, 4)]

theorem rowCheck1045 : row1045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1045 := by decide +kernel

theorem rowEval1045 (x : Key → ℝ) : Integer.Sparse.eval row1045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1045, Integer.Sparse.eval_collectBalanced, rawRowCheck1045]

def rawRow1046 : Integer.Sparse Key := [(key1590, -6), (key1630, 2), (key1441, 2), (key1630, 2), (key1553, 6), (key1621, -2), (key1323, -2), (key1621, -2), (key1543, -2), (key1388, -2), (key1543, -2), (key1570, 2), (key1293, 2), (key1570, 2)]

theorem rawRowCheck1046 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form4 = rawRow1046 := by decide +kernel

def row1046 : Integer.Sparse Key := [(key1293, 2), (key1323, -2), (key1388, -2), (key1441, 2), (key1543, -4), (key1553, 6), (key1570, 4), (key1590, -6), (key1621, -4), (key1630, 4)]

theorem rowCheck1046 : row1046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1046 := by decide +kernel

theorem rowEval1046 (x : Key → ℝ) : Integer.Sparse.eval row1046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1046, Integer.Sparse.eval_collectBalanced, rawRowCheck1046]

def rawRow1047 : Integer.Sparse Key := [(key1590, -6), (key1630, 2), (key1630, 2), (key1441, 2), (key1553, 6), (key1621, -2), (key1621, -2), (key1323, -2), (key1543, -2), (key1543, -2), (key1388, -2), (key1570, 2), (key1570, 2), (key1293, 2)]

theorem rawRowCheck1047 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form4 = rawRow1047 := by decide +kernel

def row1047 : Integer.Sparse Key := [(key1293, 2), (key1323, -2), (key1388, -2), (key1441, 2), (key1543, -4), (key1553, 6), (key1570, 4), (key1590, -6), (key1621, -4), (key1630, 4)]

theorem rowCheck1047 : row1047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1047 := by decide +kernel

theorem rowEval1047 (x : Key → ℝ) : Integer.Sparse.eval row1047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1047, Integer.Sparse.eval_collectBalanced, rawRowCheck1047]

def rawRow1048 : Integer.Sparse Key := [(key1630, -6), (key1441, 2), (key1590, 2), (key1630, 2), (key1621, 6), (key1323, -2), (key1553, -2), (key1621, -2), (key1421, -2), (key1570, -2), (key1619, -2), (key1313, 2), (key1543, 2), (key1619, 2)]

theorem rawRowCheck1048 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form4 = rawRow1048 := by decide +kernel

def row1048 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

theorem rowCheck1048 : row1048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1048 := by decide +kernel

theorem rowEval1048 (x : Key → ℝ) : Integer.Sparse.eval row1048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1048, Integer.Sparse.eval_collectBalanced, rawRowCheck1048]

def rawRow1049 : Integer.Sparse Key := [(key1630, -6), (key1441, 2), (key1630, 2), (key1590, 2), (key1621, 6), (key1323, -2), (key1621, -2), (key1553, -2), (key1421, -2), (key1619, -2), (key1570, -2), (key1313, 2), (key1619, 2), (key1543, 2)]

theorem rawRowCheck1049 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form4 = rawRow1049 := by decide +kernel

def row1049 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

theorem rowCheck1049 : row1049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1049 := by decide +kernel

theorem rowEval1049 (x : Key → ℝ) : Integer.Sparse.eval row1049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1049, Integer.Sparse.eval_collectBalanced, rawRowCheck1049]

def rawRow1050 : Integer.Sparse Key := [(key1630, -6), (key1590, 2), (key1441, 2), (key1630, 2), (key1621, 6), (key1553, -2), (key1323, -2), (key1621, -2), (key1570, -2), (key1421, -2), (key1619, -2), (key1543, 2), (key1313, 2), (key1619, 2)]

theorem rawRowCheck1050 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form4 = rawRow1050 := by decide +kernel

def row1050 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

theorem rowCheck1050 : row1050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1050 := by decide +kernel

theorem rowEval1050 (x : Key → ℝ) : Integer.Sparse.eval row1050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1050, Integer.Sparse.eval_collectBalanced, rawRowCheck1050]

def rawRow1051 : Integer.Sparse Key := [(key1630, -6), (key1590, 2), (key1630, 2), (key1441, 2), (key1621, 6), (key1553, -2), (key1621, -2), (key1323, -2), (key1570, -2), (key1619, -2), (key1421, -2), (key1543, 2), (key1619, 2), (key1313, 2)]

theorem rawRowCheck1051 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form4 = rawRow1051 := by decide +kernel

def row1051 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

theorem rowCheck1051 : row1051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1051 := by decide +kernel

theorem rowEval1051 (x : Key → ℝ) : Integer.Sparse.eval row1051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1051, Integer.Sparse.eval_collectBalanced, rawRowCheck1051]

def rawRow1052 : Integer.Sparse Key := [(key1630, -6), (key1630, 2), (key1441, 2), (key1590, 2), (key1621, 6), (key1621, -2), (key1323, -2), (key1553, -2), (key1619, -2), (key1421, -2), (key1570, -2), (key1619, 2), (key1313, 2), (key1543, 2)]

theorem rawRowCheck1052 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form4 = rawRow1052 := by decide +kernel

def row1052 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

theorem rowCheck1052 : row1052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1052 := by decide +kernel

theorem rowEval1052 (x : Key → ℝ) : Integer.Sparse.eval row1052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1052, Integer.Sparse.eval_collectBalanced, rawRowCheck1052]

def rawRow1053 : Integer.Sparse Key := [(key1630, -6), (key1630, 2), (key1590, 2), (key1441, 2), (key1621, 6), (key1621, -2), (key1553, -2), (key1323, -2), (key1619, -2), (key1570, -2), (key1421, -2), (key1619, 2), (key1543, 2), (key1313, 2)]

theorem rawRowCheck1053 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form4 = rawRow1053 := by decide +kernel

def row1053 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

theorem rowCheck1053 : row1053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1053 := by decide +kernel

theorem rowEval1053 (x : Key → ℝ) : Integer.Sparse.eval row1053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1053, Integer.Sparse.eval_collectBalanced, rawRowCheck1053]

def rawRow1054 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key406, -1), (key421, -1), (key657, -1), (key658, -1), (key241, 2), (key411, 2), (key421, 2), (key248, 1), (key253, 1), (key435, 1), (key453, 1), (key660, 1), (key662, 1), (key253, -1), (key263, -1), (key321, -1), (key331, -1), (key445, -1), (key453, -1), (key277, -2), (key487, -2), (key489, -2), (key277, 1), (key278, 1), (key346, 1), (key347, 1), (key488, 1), (key489, 1)]

theorem rawRowCheck1054 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form5 = rawRow1054 := by decide +kernel

def row1054 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key421, 1), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key657, -1), (key658, -1), (key660, 1), (key662, 1)]

theorem rowCheck1054 : row1054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1054 := by decide +kernel

theorem rowEval1054 (x : Key → ℝ) : Integer.Sparse.eval row1054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1054, Integer.Sparse.eval_collectBalanced, rawRowCheck1054]

def rawRow1055 : Integer.Sparse Key := [(key241, -1), (key236, -1), (key421, -1), (key406, -1), (key658, -1), (key657, -1), (key241, 2), (key421, 2), (key411, 2), (key253, 1), (key248, 1), (key453, 1), (key435, 1), (key662, 1), (key660, 1), (key263, -1), (key253, -1), (key331, -1), (key321, -1), (key453, -1), (key445, -1), (key277, -2), (key489, -2), (key487, -2), (key278, 1), (key277, 1), (key347, 1), (key346, 1), (key489, 1), (key488, 1)]

theorem rawRowCheck1055 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form5 = rawRow1055 := by decide +kernel

def row1055 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key421, 1), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key657, -1), (key658, -1), (key660, 1), (key662, 1)]

theorem rowCheck1055 : row1055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1055 := by decide +kernel

theorem rowEval1055 (x : Key → ℝ) : Integer.Sparse.eval row1055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1055, Integer.Sparse.eval_collectBalanced, rawRowCheck1055]

end MUB6.Certificate.GramRows

end OAI
