import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3968 : Integer.Sparse Key := [(key171, -2), (key174, -2), (key179, -2), (key171, 6), (key103, 2), (key112, 2), (key134, 2), (key21, -2), (key46, -2), (key103, -2), (key100, -6), (key18, 2), (key375, 2), (key426, 2)]

theorem rawRowCheck3968 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form8 = rawRow3968 := by decide +kernel

def row3968 : Integer.Sparse Key := [(key18, 2), (key21, -2), (key46, -2), (key100, -6), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key375, 2), (key426, 2)]

theorem rowCheck3968 : row3968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3968 := by decide +kernel

theorem rowEval3968 (x : Key → ℝ) : Integer.Sparse.eval row3968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3968, Integer.Sparse.eval_collectBalanced, rawRowCheck3968]

def rawRow3969 : Integer.Sparse Key := [(key174, -2), (key171, -2), (key179, -2), (key171, 6), (key112, 2), (key103, 2), (key134, 2), (key21, -2), (key103, -2), (key46, -2), (key100, -6), (key18, 2), (key426, 2), (key375, 2)]

theorem rawRowCheck3969 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form8 = rawRow3969 := by decide +kernel

def row3969 : Integer.Sparse Key := [(key18, 2), (key21, -2), (key46, -2), (key100, -6), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key375, 2), (key426, 2)]

theorem rowCheck3969 : row3969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3969 := by decide +kernel

theorem rowEval3969 (x : Key → ℝ) : Integer.Sparse.eval row3969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3969, Integer.Sparse.eval_collectBalanced, rawRowCheck3969]

def rawRow3970 : Integer.Sparse Key := [(key171, -2), (key179, -2), (key174, -2), (key171, 6), (key103, 2), (key134, 2), (key112, 2), (key46, -2), (key21, -2), (key103, -2), (key100, -6), (key43, 2), (key206, 2), (key426, 2)]

theorem rawRowCheck3970 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form8 = rawRow3970 := by decide +kernel

def row3970 : Integer.Sparse Key := [(key21, -2), (key43, 2), (key46, -2), (key100, -6), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key206, 2), (key426, 2)]

theorem rowCheck3970 : row3970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3970 := by decide +kernel

theorem rowEval3970 (x : Key → ℝ) : Integer.Sparse.eval row3970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3970, Integer.Sparse.eval_collectBalanced, rawRowCheck3970]

def rawRow3971 : Integer.Sparse Key := [(key179, -2), (key171, -2), (key174, -2), (key171, 6), (key134, 2), (key103, 2), (key112, 2), (key46, -2), (key103, -2), (key21, -2), (key100, -6), (key43, 2), (key426, 2), (key206, 2)]

theorem rawRowCheck3971 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form8 = rawRow3971 := by decide +kernel

def row3971 : Integer.Sparse Key := [(key21, -2), (key43, 2), (key46, -2), (key100, -6), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key206, 2), (key426, 2)]

theorem rowCheck3971 : row3971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3971 := by decide +kernel

theorem rowEval3971 (x : Key → ℝ) : Integer.Sparse.eval row3971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3971, Integer.Sparse.eval_collectBalanced, rawRowCheck3971]

def rawRow3972 : Integer.Sparse Key := [(key174, -2), (key179, -2), (key171, -2), (key171, 6), (key112, 2), (key134, 2), (key103, 2), (key103, -2), (key21, -2), (key46, -2), (key100, -6), (key100, 2), (key18, 2), (key375, 2)]

theorem rawRowCheck3972 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form8 = rawRow3972 := by decide +kernel

def row3972 : Integer.Sparse Key := [(key18, 2), (key21, -2), (key46, -2), (key100, -4), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key375, 2)]

theorem rowCheck3972 : row3972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3972 := by decide +kernel

theorem rowEval3972 (x : Key → ℝ) : Integer.Sparse.eval row3972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3972, Integer.Sparse.eval_collectBalanced, rawRowCheck3972]

def rawRow3973 : Integer.Sparse Key := [(key179, -2), (key174, -2), (key171, -2), (key171, 6), (key134, 2), (key112, 2), (key103, 2), (key103, -2), (key46, -2), (key21, -2), (key100, -6), (key100, 2), (key43, 2), (key206, 2)]

theorem rawRowCheck3973 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form8 = rawRow3973 := by decide +kernel

def row3973 : Integer.Sparse Key := [(key21, -2), (key43, 2), (key46, -2), (key100, -4), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key206, 2)]

theorem rowCheck3973 : row3973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3973 := by decide +kernel

theorem rowEval3973 (x : Key → ℝ) : Integer.Sparse.eval row3973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3973, Integer.Sparse.eval_collectBalanced, rawRowCheck3973]

def rawRow3974 : Integer.Sparse Key := [(key1391, -2), (key1772, -2), (key1780, -2), (key1391, 1), (key1397, 1), (key1546, 1), (key1559, 1), (key1774, 1), (key1780, 1), (key1424, 2), (key1813, 2), (key1817, 2), (key1316, -1), (key1329, -1), (key1424, -1), (key1447, -1), (key1817, -1), (key1825, -1), (key1455, -1), (key1457, -1), (key1655, -1), (key1659, -1), (key1839, -1), (key1841, -1), (key1337, 1), (key1345, 1), (key1455, 1), (key1466, 1), (key1841, 1), (key1844, 1)]

theorem rawRowCheck3974 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form9 = rawRow3974 := by decide +kernel

def row3974 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

theorem rowCheck3974 : row3974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3974 := by decide +kernel

theorem rowEval3974 (x : Key → ℝ) : Integer.Sparse.eval row3974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3974, Integer.Sparse.eval_collectBalanced, rawRowCheck3974]

def rawRow3975 : Integer.Sparse Key := [(key1391, -2), (key1780, -2), (key1772, -2), (key1397, 1), (key1391, 1), (key1559, 1), (key1546, 1), (key1780, 1), (key1774, 1), (key1424, 2), (key1817, 2), (key1813, 2), (key1329, -1), (key1316, -1), (key1447, -1), (key1424, -1), (key1825, -1), (key1817, -1), (key1457, -1), (key1455, -1), (key1659, -1), (key1655, -1), (key1841, -1), (key1839, -1), (key1345, 1), (key1337, 1), (key1466, 1), (key1455, 1), (key1844, 1), (key1841, 1)]

theorem rawRowCheck3975 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form9 = rawRow3975 := by decide +kernel

def row3975 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

theorem rowCheck3975 : row3975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3975 := by decide +kernel

theorem rowEval3975 (x : Key → ℝ) : Integer.Sparse.eval row3975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3975, Integer.Sparse.eval_collectBalanced, rawRowCheck3975]

def rawRow3976 : Integer.Sparse Key := [(key1772, -2), (key1391, -2), (key1780, -2), (key1546, 1), (key1774, 1), (key1391, 1), (key1780, 1), (key1397, 1), (key1559, 1), (key1813, 2), (key1424, 2), (key1817, 2), (key1424, -1), (key1817, -1), (key1316, -1), (key1825, -1), (key1329, -1), (key1447, -1), (key1655, -1), (key1839, -1), (key1455, -1), (key1841, -1), (key1457, -1), (key1659, -1), (key1455, 1), (key1841, 1), (key1337, 1), (key1844, 1), (key1345, 1), (key1466, 1)]

theorem rawRowCheck3976 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form9 = rawRow3976 := by decide +kernel

def row3976 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

theorem rowCheck3976 : row3976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3976 := by decide +kernel

theorem rowEval3976 (x : Key → ℝ) : Integer.Sparse.eval row3976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3976, Integer.Sparse.eval_collectBalanced, rawRowCheck3976]

def rawRow3977 : Integer.Sparse Key := [(key1772, -2), (key1780, -2), (key1391, -2), (key1774, 1), (key1546, 1), (key1780, 1), (key1391, 1), (key1559, 1), (key1397, 1), (key1813, 2), (key1817, 2), (key1424, 2), (key1817, -1), (key1424, -1), (key1825, -1), (key1316, -1), (key1447, -1), (key1329, -1), (key1839, -1), (key1655, -1), (key1841, -1), (key1455, -1), (key1659, -1), (key1457, -1), (key1841, 1), (key1455, 1), (key1844, 1), (key1337, 1), (key1466, 1), (key1345, 1)]

theorem rawRowCheck3977 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form9 = rawRow3977 := by decide +kernel

def row3977 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

theorem rowCheck3977 : row3977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3977 := by decide +kernel

theorem rowEval3977 (x : Key → ℝ) : Integer.Sparse.eval row3977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3977, Integer.Sparse.eval_collectBalanced, rawRowCheck3977]

def rawRow3978 : Integer.Sparse Key := [(key1780, -2), (key1391, -2), (key1772, -2), (key1559, 1), (key1780, 1), (key1397, 1), (key1774, 1), (key1391, 1), (key1546, 1), (key1817, 2), (key1424, 2), (key1813, 2), (key1447, -1), (key1825, -1), (key1329, -1), (key1817, -1), (key1316, -1), (key1424, -1), (key1659, -1), (key1841, -1), (key1457, -1), (key1839, -1), (key1455, -1), (key1655, -1), (key1466, 1), (key1844, 1), (key1345, 1), (key1841, 1), (key1337, 1), (key1455, 1)]

theorem rawRowCheck3978 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form9 = rawRow3978 := by decide +kernel

def row3978 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

theorem rowCheck3978 : row3978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3978 := by decide +kernel

theorem rowEval3978 (x : Key → ℝ) : Integer.Sparse.eval row3978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3978, Integer.Sparse.eval_collectBalanced, rawRowCheck3978]

def rawRow3979 : Integer.Sparse Key := [(key1780, -2), (key1772, -2), (key1391, -2), (key1780, 1), (key1559, 1), (key1774, 1), (key1397, 1), (key1546, 1), (key1391, 1), (key1817, 2), (key1813, 2), (key1424, 2), (key1825, -1), (key1447, -1), (key1817, -1), (key1329, -1), (key1424, -1), (key1316, -1), (key1841, -1), (key1659, -1), (key1839, -1), (key1457, -1), (key1655, -1), (key1455, -1), (key1844, 1), (key1466, 1), (key1841, 1), (key1345, 1), (key1455, 1), (key1337, 1)]

theorem rawRowCheck3979 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form9 = rawRow3979 := by decide +kernel

def row3979 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

theorem rowCheck3979 : row3979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3979 := by decide +kernel

theorem rowEval3979 (x : Key → ℝ) : Integer.Sparse.eval row3979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3979, Integer.Sparse.eval_collectBalanced, rawRowCheck3979]

def rawRow3980 : Integer.Sparse Key := [(key1397, -2), (key1774, -2), (key1774, -2), (key1391, 1), (key1391, 1), (key1546, 1), (key1546, 1), (key1772, 1), (key1772, 1), (key1447, 2), (key1825, 2), (key1825, 2), (key1316, -1), (key1316, -1), (key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1466, -1), (key1466, -1), (key1667, -1), (key1667, -1), (key1844, -1), (key1844, -1), (key1339, 1), (key1339, 1), (key1457, 1), (key1457, 1), (key1839, 1), (key1839, 1)]

theorem rawRowCheck3980 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form9 = rawRow3980 := by decide +kernel

def row3980 : Integer.Sparse Key := [(key1316, -2), (key1339, 2), (key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1546, 2), (key1667, -2), (key1772, 2), (key1774, -4), (key1813, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

theorem rowCheck3980 : row3980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3980 := by decide +kernel

theorem rowEval3980 (x : Key → ℝ) : Integer.Sparse.eval row3980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3980, Integer.Sparse.eval_collectBalanced, rawRowCheck3980]

def rawRow3981 : Integer.Sparse Key := [(key1774, -2), (key1397, -2), (key1774, -2), (key1546, 1), (key1772, 1), (key1391, 1), (key1772, 1), (key1391, 1), (key1546, 1), (key1825, 2), (key1447, 2), (key1825, 2), (key1424, -1), (key1813, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1667, -1), (key1844, -1), (key1466, -1), (key1844, -1), (key1466, -1), (key1667, -1), (key1457, 1), (key1839, 1), (key1339, 1), (key1839, 1), (key1339, 1), (key1457, 1)]

theorem rawRowCheck3981 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form9 = rawRow3981 := by decide +kernel

def row3981 : Integer.Sparse Key := [(key1316, -2), (key1339, 2), (key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1546, 2), (key1667, -2), (key1772, 2), (key1774, -4), (key1813, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

theorem rowCheck3981 : row3981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3981 := by decide +kernel

theorem rowEval3981 (x : Key → ℝ) : Integer.Sparse.eval row3981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3981, Integer.Sparse.eval_collectBalanced, rawRowCheck3981]

def rawRow3982 : Integer.Sparse Key := [(key1774, -2), (key1774, -2), (key1397, -2), (key1772, 1), (key1546, 1), (key1772, 1), (key1391, 1), (key1546, 1), (key1391, 1), (key1825, 2), (key1825, 2), (key1447, 2), (key1813, -1), (key1424, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1316, -1), (key1844, -1), (key1667, -1), (key1844, -1), (key1466, -1), (key1667, -1), (key1466, -1), (key1839, 1), (key1457, 1), (key1839, 1), (key1339, 1), (key1457, 1), (key1339, 1)]

theorem rawRowCheck3982 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form9 = rawRow3982 := by decide +kernel

def row3982 : Integer.Sparse Key := [(key1316, -2), (key1339, 2), (key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1546, 2), (key1667, -2), (key1772, 2), (key1774, -4), (key1813, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

theorem rowCheck3982 : row3982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3982 := by decide +kernel

theorem rowEval3982 (x : Key → ℝ) : Integer.Sparse.eval row3982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3982, Integer.Sparse.eval_collectBalanced, rawRowCheck3982]

def rawRow3983 : Integer.Sparse Key := [(key1424, -2), (key1813, -2), (key1817, -2), (key1455, 1), (key1457, 1), (key1655, 1), (key1659, 1), (key1839, 1), (key1841, 1), (key1391, 2), (key1772, 2), (key1780, 2), (key1337, -1), (key1345, -1), (key1455, -1), (key1466, -1), (key1841, -1), (key1844, -1), (key1391, -1), (key1397, -1), (key1546, -1), (key1559, -1), (key1774, -1), (key1780, -1), (key1316, 1), (key1329, 1), (key1424, 1), (key1447, 1), (key1817, 1), (key1825, 1)]

theorem rawRowCheck3983 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form9 = rawRow3983 := by decide +kernel

def row3983 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

theorem rowCheck3983 : row3983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3983 := by decide +kernel

theorem rowEval3983 (x : Key → ℝ) : Integer.Sparse.eval row3983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3983, Integer.Sparse.eval_collectBalanced, rawRowCheck3983]

def rawRow3984 : Integer.Sparse Key := [(key1424, -2), (key1817, -2), (key1813, -2), (key1457, 1), (key1455, 1), (key1659, 1), (key1655, 1), (key1841, 1), (key1839, 1), (key1391, 2), (key1780, 2), (key1772, 2), (key1345, -1), (key1337, -1), (key1466, -1), (key1455, -1), (key1844, -1), (key1841, -1), (key1397, -1), (key1391, -1), (key1559, -1), (key1546, -1), (key1780, -1), (key1774, -1), (key1329, 1), (key1316, 1), (key1447, 1), (key1424, 1), (key1825, 1), (key1817, 1)]

theorem rawRowCheck3984 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form9 = rawRow3984 := by decide +kernel

def row3984 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

theorem rowCheck3984 : row3984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3984 := by decide +kernel

theorem rowEval3984 (x : Key → ℝ) : Integer.Sparse.eval row3984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3984, Integer.Sparse.eval_collectBalanced, rawRowCheck3984]

def rawRow3985 : Integer.Sparse Key := [(key1813, -2), (key1424, -2), (key1817, -2), (key1655, 1), (key1839, 1), (key1455, 1), (key1841, 1), (key1457, 1), (key1659, 1), (key1772, 2), (key1391, 2), (key1780, 2), (key1455, -1), (key1841, -1), (key1337, -1), (key1844, -1), (key1345, -1), (key1466, -1), (key1546, -1), (key1774, -1), (key1391, -1), (key1780, -1), (key1397, -1), (key1559, -1), (key1424, 1), (key1817, 1), (key1316, 1), (key1825, 1), (key1329, 1), (key1447, 1)]

theorem rawRowCheck3985 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form9 = rawRow3985 := by decide +kernel

def row3985 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

theorem rowCheck3985 : row3985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3985 := by decide +kernel

theorem rowEval3985 (x : Key → ℝ) : Integer.Sparse.eval row3985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3985, Integer.Sparse.eval_collectBalanced, rawRowCheck3985]

def rawRow3986 : Integer.Sparse Key := [(key1813, -2), (key1817, -2), (key1424, -2), (key1839, 1), (key1655, 1), (key1841, 1), (key1455, 1), (key1659, 1), (key1457, 1), (key1772, 2), (key1780, 2), (key1391, 2), (key1841, -1), (key1455, -1), (key1844, -1), (key1337, -1), (key1466, -1), (key1345, -1), (key1774, -1), (key1546, -1), (key1780, -1), (key1391, -1), (key1559, -1), (key1397, -1), (key1817, 1), (key1424, 1), (key1825, 1), (key1316, 1), (key1447, 1), (key1329, 1)]

theorem rawRowCheck3986 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form9 = rawRow3986 := by decide +kernel

def row3986 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

theorem rowCheck3986 : row3986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3986 := by decide +kernel

theorem rowEval3986 (x : Key → ℝ) : Integer.Sparse.eval row3986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3986, Integer.Sparse.eval_collectBalanced, rawRowCheck3986]

def rawRow3987 : Integer.Sparse Key := [(key1817, -2), (key1424, -2), (key1813, -2), (key1659, 1), (key1841, 1), (key1457, 1), (key1839, 1), (key1455, 1), (key1655, 1), (key1780, 2), (key1391, 2), (key1772, 2), (key1466, -1), (key1844, -1), (key1345, -1), (key1841, -1), (key1337, -1), (key1455, -1), (key1559, -1), (key1780, -1), (key1397, -1), (key1774, -1), (key1391, -1), (key1546, -1), (key1447, 1), (key1825, 1), (key1329, 1), (key1817, 1), (key1316, 1), (key1424, 1)]

theorem rawRowCheck3987 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form9 = rawRow3987 := by decide +kernel

def row3987 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

theorem rowCheck3987 : row3987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3987 := by decide +kernel

theorem rowEval3987 (x : Key → ℝ) : Integer.Sparse.eval row3987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3987, Integer.Sparse.eval_collectBalanced, rawRowCheck3987]

def rawRow3988 : Integer.Sparse Key := [(key1817, -2), (key1813, -2), (key1424, -2), (key1841, 1), (key1659, 1), (key1839, 1), (key1457, 1), (key1655, 1), (key1455, 1), (key1780, 2), (key1772, 2), (key1391, 2), (key1844, -1), (key1466, -1), (key1841, -1), (key1345, -1), (key1455, -1), (key1337, -1), (key1780, -1), (key1559, -1), (key1774, -1), (key1397, -1), (key1546, -1), (key1391, -1), (key1825, 1), (key1447, 1), (key1817, 1), (key1329, 1), (key1424, 1), (key1316, 1)]

theorem rawRowCheck3988 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form9 = rawRow3988 := by decide +kernel

def row3988 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

theorem rowCheck3988 : row3988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3988 := by decide +kernel

theorem rowEval3988 (x : Key → ℝ) : Integer.Sparse.eval row3988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3988, Integer.Sparse.eval_collectBalanced, rawRowCheck3988]

def rawRow3989 : Integer.Sparse Key := [(key1457, -2), (key1790, -2), (key1839, -2), (key1424, 1), (key1455, 1), (key1573, 1), (key1655, 1), (key1788, 1), (key1813, 1), (key1466, 2), (key1798, 2), (key1844, 2), (key1296, -1), (key1337, -1), (key1391, -1), (key1455, -1), (key1772, -1), (key1788, -1), (key1447, -1), (key1466, -1), (key1596, -1), (key1667, -1), (key1798, -1), (key1825, -1), (key1302, 1), (key1339, 1), (key1397, 1), (key1457, 1), (key1774, 1), (key1790, 1)]

theorem rawRowCheck3989 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form9 = rawRow3989 := by decide +kernel

def row3989 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

theorem rowCheck3989 : row3989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3989 := by decide +kernel

theorem rowEval3989 (x : Key → ℝ) : Integer.Sparse.eval row3989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3989, Integer.Sparse.eval_collectBalanced, rawRowCheck3989]

def rawRow3990 : Integer.Sparse Key := [(key1457, -2), (key1839, -2), (key1790, -2), (key1455, 1), (key1424, 1), (key1655, 1), (key1573, 1), (key1813, 1), (key1788, 1), (key1466, 2), (key1844, 2), (key1798, 2), (key1337, -1), (key1296, -1), (key1455, -1), (key1391, -1), (key1788, -1), (key1772, -1), (key1466, -1), (key1447, -1), (key1667, -1), (key1596, -1), (key1825, -1), (key1798, -1), (key1339, 1), (key1302, 1), (key1457, 1), (key1397, 1), (key1790, 1), (key1774, 1)]

theorem rawRowCheck3990 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form9 = rawRow3990 := by decide +kernel

def row3990 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

theorem rowCheck3990 : row3990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3990 := by decide +kernel

theorem rowEval3990 (x : Key → ℝ) : Integer.Sparse.eval row3990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3990, Integer.Sparse.eval_collectBalanced, rawRowCheck3990]

def rawRow3991 : Integer.Sparse Key := [(key1790, -2), (key1457, -2), (key1839, -2), (key1573, 1), (key1788, 1), (key1424, 1), (key1813, 1), (key1455, 1), (key1655, 1), (key1798, 2), (key1466, 2), (key1844, 2), (key1391, -1), (key1772, -1), (key1296, -1), (key1788, -1), (key1337, -1), (key1455, -1), (key1596, -1), (key1798, -1), (key1447, -1), (key1825, -1), (key1466, -1), (key1667, -1), (key1397, 1), (key1774, 1), (key1302, 1), (key1790, 1), (key1339, 1), (key1457, 1)]

theorem rawRowCheck3991 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form9 = rawRow3991 := by decide +kernel

def row3991 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

theorem rowCheck3991 : row3991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3991 := by decide +kernel

theorem rowEval3991 (x : Key → ℝ) : Integer.Sparse.eval row3991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3991, Integer.Sparse.eval_collectBalanced, rawRowCheck3991]

def rawRow3992 : Integer.Sparse Key := [(key1790, -2), (key1839, -2), (key1457, -2), (key1788, 1), (key1573, 1), (key1813, 1), (key1424, 1), (key1655, 1), (key1455, 1), (key1798, 2), (key1844, 2), (key1466, 2), (key1772, -1), (key1391, -1), (key1788, -1), (key1296, -1), (key1455, -1), (key1337, -1), (key1798, -1), (key1596, -1), (key1825, -1), (key1447, -1), (key1667, -1), (key1466, -1), (key1774, 1), (key1397, 1), (key1790, 1), (key1302, 1), (key1457, 1), (key1339, 1)]

theorem rawRowCheck3992 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form9 = rawRow3992 := by decide +kernel

def row3992 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

theorem rowCheck3992 : row3992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3992 := by decide +kernel

theorem rowEval3992 (x : Key → ℝ) : Integer.Sparse.eval row3992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3992, Integer.Sparse.eval_collectBalanced, rawRowCheck3992]

def rawRow3993 : Integer.Sparse Key := [(key1839, -2), (key1457, -2), (key1790, -2), (key1655, 1), (key1813, 1), (key1455, 1), (key1788, 1), (key1424, 1), (key1573, 1), (key1844, 2), (key1466, 2), (key1798, 2), (key1455, -1), (key1788, -1), (key1337, -1), (key1772, -1), (key1296, -1), (key1391, -1), (key1667, -1), (key1825, -1), (key1466, -1), (key1798, -1), (key1447, -1), (key1596, -1), (key1457, 1), (key1790, 1), (key1339, 1), (key1774, 1), (key1302, 1), (key1397, 1)]

theorem rawRowCheck3993 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form9 = rawRow3993 := by decide +kernel

def row3993 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

theorem rowCheck3993 : row3993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3993 := by decide +kernel

theorem rowEval3993 (x : Key → ℝ) : Integer.Sparse.eval row3993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3993, Integer.Sparse.eval_collectBalanced, rawRowCheck3993]

def rawRow3994 : Integer.Sparse Key := [(key1839, -2), (key1790, -2), (key1457, -2), (key1813, 1), (key1655, 1), (key1788, 1), (key1455, 1), (key1573, 1), (key1424, 1), (key1844, 2), (key1798, 2), (key1466, 2), (key1788, -1), (key1455, -1), (key1772, -1), (key1337, -1), (key1391, -1), (key1296, -1), (key1825, -1), (key1667, -1), (key1798, -1), (key1466, -1), (key1596, -1), (key1447, -1), (key1790, 1), (key1457, 1), (key1774, 1), (key1339, 1), (key1397, 1), (key1302, 1)]

theorem rawRowCheck3994 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form9 = rawRow3994 := by decide +kernel

def row3994 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

theorem rowCheck3994 : row3994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3994 := by decide +kernel

theorem rowEval3994 (x : Key → ℝ) : Integer.Sparse.eval row3994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3994, Integer.Sparse.eval_collectBalanced, rawRowCheck3994]

def rawRow3995 : Integer.Sparse Key := [(key1447, -2), (key1825, -2), (key1825, -2), (key1466, 1), (key1466, 1), (key1667, 1), (key1667, 1), (key1844, 1), (key1844, 1), (key1397, 2), (key1774, 2), (key1774, 2), (key1339, -1), (key1339, -1), (key1457, -1), (key1457, -1), (key1839, -1), (key1839, -1), (key1391, -1), (key1391, -1), (key1546, -1), (key1546, -1), (key1772, -1), (key1772, -1), (key1316, 1), (key1316, 1), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1)]

theorem rawRowCheck3995 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form9 = rawRow3995 := by decide +kernel

def row3995 : Integer.Sparse Key := [(key1316, 2), (key1339, -2), (key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1546, -2), (key1667, 2), (key1772, -2), (key1774, 4), (key1813, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

theorem rowCheck3995 : row3995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3995 := by decide +kernel

theorem rowEval3995 (x : Key → ℝ) : Integer.Sparse.eval row3995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3995, Integer.Sparse.eval_collectBalanced, rawRowCheck3995]

def rawRow3996 : Integer.Sparse Key := [(key1825, -2), (key1447, -2), (key1825, -2), (key1667, 1), (key1844, 1), (key1466, 1), (key1844, 1), (key1466, 1), (key1667, 1), (key1774, 2), (key1397, 2), (key1774, 2), (key1457, -1), (key1839, -1), (key1339, -1), (key1839, -1), (key1339, -1), (key1457, -1), (key1546, -1), (key1772, -1), (key1391, -1), (key1772, -1), (key1391, -1), (key1546, -1), (key1424, 1), (key1813, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1424, 1)]

theorem rawRowCheck3996 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form9 = rawRow3996 := by decide +kernel

def row3996 : Integer.Sparse Key := [(key1316, 2), (key1339, -2), (key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1546, -2), (key1667, 2), (key1772, -2), (key1774, 4), (key1813, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

theorem rowCheck3996 : row3996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3996 := by decide +kernel

theorem rowEval3996 (x : Key → ℝ) : Integer.Sparse.eval row3996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3996, Integer.Sparse.eval_collectBalanced, rawRowCheck3996]

def rawRow3997 : Integer.Sparse Key := [(key1825, -2), (key1825, -2), (key1447, -2), (key1844, 1), (key1667, 1), (key1844, 1), (key1466, 1), (key1667, 1), (key1466, 1), (key1774, 2), (key1774, 2), (key1397, 2), (key1839, -1), (key1457, -1), (key1839, -1), (key1339, -1), (key1457, -1), (key1339, -1), (key1772, -1), (key1546, -1), (key1772, -1), (key1391, -1), (key1546, -1), (key1391, -1), (key1813, 1), (key1424, 1), (key1813, 1), (key1316, 1), (key1424, 1), (key1316, 1)]

theorem rawRowCheck3997 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form9 = rawRow3997 := by decide +kernel

def row3997 : Integer.Sparse Key := [(key1316, 2), (key1339, -2), (key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1546, -2), (key1667, 2), (key1772, -2), (key1774, 4), (key1813, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

theorem rowCheck3997 : row3997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3997 := by decide +kernel

theorem rowEval3997 (x : Key → ℝ) : Integer.Sparse.eval row3997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3997, Integer.Sparse.eval_collectBalanced, rawRowCheck3997]

def rawRow3998 : Integer.Sparse Key := [(key1466, -2), (key1798, -2), (key1844, -2), (key1447, 1), (key1466, 1), (key1596, 1), (key1667, 1), (key1798, 1), (key1825, 1), (key1457, 2), (key1790, 2), (key1839, 2), (key1302, -1), (key1339, -1), (key1397, -1), (key1457, -1), (key1774, -1), (key1790, -1), (key1424, -1), (key1455, -1), (key1573, -1), (key1655, -1), (key1788, -1), (key1813, -1), (key1296, 1), (key1337, 1), (key1391, 1), (key1455, 1), (key1772, 1), (key1788, 1)]

theorem rawRowCheck3998 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form9 = rawRow3998 := by decide +kernel

def row3998 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

theorem rowCheck3998 : row3998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3998 := by decide +kernel

theorem rowEval3998 (x : Key → ℝ) : Integer.Sparse.eval row3998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3998, Integer.Sparse.eval_collectBalanced, rawRowCheck3998]

def rawRow3999 : Integer.Sparse Key := [(key1466, -2), (key1844, -2), (key1798, -2), (key1466, 1), (key1447, 1), (key1667, 1), (key1596, 1), (key1825, 1), (key1798, 1), (key1457, 2), (key1839, 2), (key1790, 2), (key1339, -1), (key1302, -1), (key1457, -1), (key1397, -1), (key1790, -1), (key1774, -1), (key1455, -1), (key1424, -1), (key1655, -1), (key1573, -1), (key1813, -1), (key1788, -1), (key1337, 1), (key1296, 1), (key1455, 1), (key1391, 1), (key1788, 1), (key1772, 1)]

theorem rawRowCheck3999 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form9 = rawRow3999 := by decide +kernel

def row3999 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

theorem rowCheck3999 : row3999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3999 := by decide +kernel

theorem rowEval3999 (x : Key → ℝ) : Integer.Sparse.eval row3999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3999, Integer.Sparse.eval_collectBalanced, rawRowCheck3999]

def rawRow4000 : Integer.Sparse Key := [(key1798, -2), (key1466, -2), (key1844, -2), (key1596, 1), (key1798, 1), (key1447, 1), (key1825, 1), (key1466, 1), (key1667, 1), (key1790, 2), (key1457, 2), (key1839, 2), (key1397, -1), (key1774, -1), (key1302, -1), (key1790, -1), (key1339, -1), (key1457, -1), (key1573, -1), (key1788, -1), (key1424, -1), (key1813, -1), (key1455, -1), (key1655, -1), (key1391, 1), (key1772, 1), (key1296, 1), (key1788, 1), (key1337, 1), (key1455, 1)]

theorem rawRowCheck4000 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form9 = rawRow4000 := by decide +kernel

def row4000 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

theorem rowCheck4000 : row4000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4000 := by decide +kernel

theorem rowEval4000 (x : Key → ℝ) : Integer.Sparse.eval row4000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4000, Integer.Sparse.eval_collectBalanced, rawRowCheck4000]

def rawRow4001 : Integer.Sparse Key := [(key1798, -2), (key1844, -2), (key1466, -2), (key1798, 1), (key1596, 1), (key1825, 1), (key1447, 1), (key1667, 1), (key1466, 1), (key1790, 2), (key1839, 2), (key1457, 2), (key1774, -1), (key1397, -1), (key1790, -1), (key1302, -1), (key1457, -1), (key1339, -1), (key1788, -1), (key1573, -1), (key1813, -1), (key1424, -1), (key1655, -1), (key1455, -1), (key1772, 1), (key1391, 1), (key1788, 1), (key1296, 1), (key1455, 1), (key1337, 1)]

theorem rawRowCheck4001 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form9 = rawRow4001 := by decide +kernel

def row4001 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

theorem rowCheck4001 : row4001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4001 := by decide +kernel

theorem rowEval4001 (x : Key → ℝ) : Integer.Sparse.eval row4001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4001, Integer.Sparse.eval_collectBalanced, rawRowCheck4001]

def rawRow4002 : Integer.Sparse Key := [(key1844, -2), (key1466, -2), (key1798, -2), (key1667, 1), (key1825, 1), (key1466, 1), (key1798, 1), (key1447, 1), (key1596, 1), (key1839, 2), (key1457, 2), (key1790, 2), (key1457, -1), (key1790, -1), (key1339, -1), (key1774, -1), (key1302, -1), (key1397, -1), (key1655, -1), (key1813, -1), (key1455, -1), (key1788, -1), (key1424, -1), (key1573, -1), (key1455, 1), (key1788, 1), (key1337, 1), (key1772, 1), (key1296, 1), (key1391, 1)]

theorem rawRowCheck4002 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form9 = rawRow4002 := by decide +kernel

def row4002 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

theorem rowCheck4002 : row4002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4002 := by decide +kernel

theorem rowEval4002 (x : Key → ℝ) : Integer.Sparse.eval row4002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4002, Integer.Sparse.eval_collectBalanced, rawRowCheck4002]

def rawRow4003 : Integer.Sparse Key := [(key1844, -2), (key1798, -2), (key1466, -2), (key1825, 1), (key1667, 1), (key1798, 1), (key1466, 1), (key1596, 1), (key1447, 1), (key1839, 2), (key1790, 2), (key1457, 2), (key1790, -1), (key1457, -1), (key1774, -1), (key1339, -1), (key1397, -1), (key1302, -1), (key1813, -1), (key1655, -1), (key1788, -1), (key1455, -1), (key1573, -1), (key1424, -1), (key1788, 1), (key1455, 1), (key1772, 1), (key1337, 1), (key1391, 1), (key1296, 1)]

theorem rawRowCheck4003 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form9 = rawRow4003 := by decide +kernel

def row4003 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

theorem rowCheck4003 : row4003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4003 := by decide +kernel

theorem rowEval4003 (x : Key → ℝ) : Integer.Sparse.eval row4003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4003, Integer.Sparse.eval_collectBalanced, rawRowCheck4003]

def rawRow4004 : Integer.Sparse Key := [(key1527, -2), (key1533, -2), (key1893, -2), (key1533, 6), (key1605, 2), (key1611, 2), (key1915, 2), (key1258, -2), (key1611, -2), (key1639, -2), (key1678, -6), (key1270, 2), (key1678, 2), (key1692, 2)]

theorem rawRowCheck4004 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form10 = rawRow4004 := by decide +kernel

def row4004 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

theorem rowCheck4004 : row4004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4004 := by decide +kernel

theorem rowEval4004 (x : Key → ℝ) : Integer.Sparse.eval row4004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4004, Integer.Sparse.eval_collectBalanced, rawRowCheck4004]

def rawRow4005 : Integer.Sparse Key := [(key1533, -2), (key1527, -2), (key1893, -2), (key1533, 6), (key1611, 2), (key1605, 2), (key1915, 2), (key1258, -2), (key1639, -2), (key1611, -2), (key1678, -6), (key1270, 2), (key1692, 2), (key1678, 2)]

theorem rawRowCheck4005 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form10 = rawRow4005 := by decide +kernel

def row4005 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

theorem rowCheck4005 : row4005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4005 := by decide +kernel

theorem rowEval4005 (x : Key → ℝ) : Integer.Sparse.eval row4005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4005, Integer.Sparse.eval_collectBalanced, rawRowCheck4005]

def rawRow4006 : Integer.Sparse Key := [(key1527, -2), (key1893, -2), (key1533, -2), (key1533, 6), (key1605, 2), (key1915, 2), (key1611, 2), (key1611, -2), (key1258, -2), (key1639, -2), (key1678, -6), (key1678, 2), (key1270, 2), (key1692, 2)]

theorem rawRowCheck4006 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form10 = rawRow4006 := by decide +kernel

def row4006 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

theorem rowCheck4006 : row4006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4006 := by decide +kernel

theorem rowEval4006 (x : Key → ℝ) : Integer.Sparse.eval row4006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4006, Integer.Sparse.eval_collectBalanced, rawRowCheck4006]

def rawRow4007 : Integer.Sparse Key := [(key1893, -2), (key1527, -2), (key1533, -2), (key1533, 6), (key1915, 2), (key1605, 2), (key1611, 2), (key1611, -2), (key1639, -2), (key1258, -2), (key1678, -6), (key1678, 2), (key1692, 2), (key1270, 2)]

theorem rawRowCheck4007 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form10 = rawRow4007 := by decide +kernel

def row4007 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

theorem rowCheck4007 : row4007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4007 := by decide +kernel

theorem rowEval4007 (x : Key → ℝ) : Integer.Sparse.eval row4007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4007, Integer.Sparse.eval_collectBalanced, rawRowCheck4007]

def rawRow4008 : Integer.Sparse Key := [(key1533, -2), (key1893, -2), (key1527, -2), (key1533, 6), (key1611, 2), (key1915, 2), (key1605, 2), (key1639, -2), (key1258, -2), (key1611, -2), (key1678, -6), (key1692, 2), (key1270, 2), (key1678, 2)]

theorem rawRowCheck4008 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form10 = rawRow4008 := by decide +kernel

def row4008 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

theorem rowCheck4008 : row4008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4008 := by decide +kernel

theorem rowEval4008 (x : Key → ℝ) : Integer.Sparse.eval row4008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4008, Integer.Sparse.eval_collectBalanced, rawRowCheck4008]

def rawRow4009 : Integer.Sparse Key := [(key1893, -2), (key1533, -2), (key1527, -2), (key1533, 6), (key1915, 2), (key1611, 2), (key1605, 2), (key1639, -2), (key1611, -2), (key1258, -2), (key1678, -6), (key1692, 2), (key1678, 2), (key1270, 2)]

theorem rawRowCheck4009 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form10 = rawRow4009 := by decide +kernel

def row4009 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

theorem rowCheck4009 : row4009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4009 := by decide +kernel

theorem rowEval4009 (x : Key → ℝ) : Integer.Sparse.eval row4009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4009, Integer.Sparse.eval_collectBalanced, rawRowCheck4009]

def rawRow4010 : Integer.Sparse Key := [(key1533, -2), (key1533, -2), (key1893, -2), (key1527, 6), (key1639, 2), (key1639, 2), (key1929, 2), (key1252, -2), (key1605, -2), (key1605, -2), (key1692, -6), (key1270, 2), (key1678, 2), (key1678, 2)]

theorem rawRowCheck4010 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form10 = rawRow4010 := by decide +kernel

def row4010 : Integer.Sparse Key := [(key1252, -2), (key1270, 2), (key1527, 6), (key1533, -4), (key1605, -4), (key1639, 4), (key1678, 4), (key1692, -6), (key1893, -2), (key1929, 2)]

theorem rowCheck4010 : row4010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4010 := by decide +kernel

theorem rowEval4010 (x : Key → ℝ) : Integer.Sparse.eval row4010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4010, Integer.Sparse.eval_collectBalanced, rawRowCheck4010]

def rawRow4011 : Integer.Sparse Key := [(key1533, -2), (key1893, -2), (key1533, -2), (key1527, 6), (key1639, 2), (key1929, 2), (key1639, 2), (key1605, -2), (key1252, -2), (key1605, -2), (key1692, -6), (key1678, 2), (key1270, 2), (key1678, 2)]

theorem rawRowCheck4011 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form10 = rawRow4011 := by decide +kernel

def row4011 : Integer.Sparse Key := [(key1252, -2), (key1270, 2), (key1527, 6), (key1533, -4), (key1605, -4), (key1639, 4), (key1678, 4), (key1692, -6), (key1893, -2), (key1929, 2)]

theorem rowCheck4011 : row4011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4011 := by decide +kernel

theorem rowEval4011 (x : Key → ℝ) : Integer.Sparse.eval row4011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4011, Integer.Sparse.eval_collectBalanced, rawRowCheck4011]

def rawRow4012 : Integer.Sparse Key := [(key1893, -2), (key1533, -2), (key1533, -2), (key1527, 6), (key1929, 2), (key1639, 2), (key1639, 2), (key1605, -2), (key1605, -2), (key1252, -2), (key1692, -6), (key1678, 2), (key1678, 2), (key1270, 2)]

theorem rawRowCheck4012 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form10 = rawRow4012 := by decide +kernel

def row4012 : Integer.Sparse Key := [(key1252, -2), (key1270, 2), (key1527, 6), (key1533, -4), (key1605, -4), (key1639, 4), (key1678, 4), (key1692, -6), (key1893, -2), (key1929, 2)]

theorem rowCheck4012 : row4012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4012 := by decide +kernel

theorem rowEval4012 (x : Key → ℝ) : Integer.Sparse.eval row4012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4012, Integer.Sparse.eval_collectBalanced, rawRowCheck4012]

def rawRow4013 : Integer.Sparse Key := [(key1605, -2), (key1611, -2), (key1915, -2), (key1678, 6), (key1527, 2), (key1533, 2), (key1893, 2), (key1270, -2), (key1678, -2), (key1692, -2), (key1533, -6), (key1258, 2), (key1611, 2), (key1639, 2)]

theorem rawRowCheck4013 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form10 = rawRow4013 := by decide +kernel

def row4013 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

theorem rowCheck4013 : row4013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4013 := by decide +kernel

theorem rowEval4013 (x : Key → ℝ) : Integer.Sparse.eval row4013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4013, Integer.Sparse.eval_collectBalanced, rawRowCheck4013]

def rawRow4014 : Integer.Sparse Key := [(key1611, -2), (key1605, -2), (key1915, -2), (key1678, 6), (key1533, 2), (key1527, 2), (key1893, 2), (key1270, -2), (key1692, -2), (key1678, -2), (key1533, -6), (key1258, 2), (key1639, 2), (key1611, 2)]

theorem rawRowCheck4014 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form10 = rawRow4014 := by decide +kernel

def row4014 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

theorem rowCheck4014 : row4014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4014 := by decide +kernel

theorem rowEval4014 (x : Key → ℝ) : Integer.Sparse.eval row4014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4014, Integer.Sparse.eval_collectBalanced, rawRowCheck4014]

def rawRow4015 : Integer.Sparse Key := [(key1605, -2), (key1915, -2), (key1611, -2), (key1678, 6), (key1527, 2), (key1893, 2), (key1533, 2), (key1678, -2), (key1270, -2), (key1692, -2), (key1533, -6), (key1611, 2), (key1258, 2), (key1639, 2)]

theorem rawRowCheck4015 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form10 = rawRow4015 := by decide +kernel

def row4015 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

theorem rowCheck4015 : row4015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4015 := by decide +kernel

theorem rowEval4015 (x : Key → ℝ) : Integer.Sparse.eval row4015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4015, Integer.Sparse.eval_collectBalanced, rawRowCheck4015]

def rawRow4016 : Integer.Sparse Key := [(key1915, -2), (key1605, -2), (key1611, -2), (key1678, 6), (key1893, 2), (key1527, 2), (key1533, 2), (key1678, -2), (key1692, -2), (key1270, -2), (key1533, -6), (key1611, 2), (key1639, 2), (key1258, 2)]

theorem rawRowCheck4016 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form10 = rawRow4016 := by decide +kernel

def row4016 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

theorem rowCheck4016 : row4016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4016 := by decide +kernel

theorem rowEval4016 (x : Key → ℝ) : Integer.Sparse.eval row4016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4016, Integer.Sparse.eval_collectBalanced, rawRowCheck4016]

def rawRow4017 : Integer.Sparse Key := [(key1611, -2), (key1915, -2), (key1605, -2), (key1678, 6), (key1533, 2), (key1893, 2), (key1527, 2), (key1692, -2), (key1270, -2), (key1678, -2), (key1533, -6), (key1639, 2), (key1258, 2), (key1611, 2)]

theorem rawRowCheck4017 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form10 = rawRow4017 := by decide +kernel

def row4017 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

theorem rowCheck4017 : row4017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4017 := by decide +kernel

theorem rowEval4017 (x : Key → ℝ) : Integer.Sparse.eval row4017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4017, Integer.Sparse.eval_collectBalanced, rawRowCheck4017]

def rawRow4018 : Integer.Sparse Key := [(key1915, -2), (key1611, -2), (key1605, -2), (key1678, 6), (key1893, 2), (key1533, 2), (key1527, 2), (key1692, -2), (key1678, -2), (key1270, -2), (key1533, -6), (key1639, 2), (key1611, 2), (key1258, 2)]

theorem rawRowCheck4018 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form10 = rawRow4018 := by decide +kernel

def row4018 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

theorem rowCheck4018 : row4018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4018 := by decide +kernel

theorem rowEval4018 (x : Key → ℝ) : Integer.Sparse.eval row4018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4018, Integer.Sparse.eval_collectBalanced, rawRowCheck4018]

def rawRow4019 : Integer.Sparse Key := [(key1611, -2), (key1678, -2), (key1915, -2), (key1605, 6), (key1639, 2), (key1692, 2), (key1929, 2), (key1252, -2), (key1527, -2), (key1605, -2), (key1639, -6), (key1258, 2), (key1533, 2), (key1611, 2)]

theorem rawRowCheck4019 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form10 = rawRow4019 := by decide +kernel

def row4019 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

theorem rowCheck4019 : row4019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4019 := by decide +kernel

theorem rowEval4019 (x : Key → ℝ) : Integer.Sparse.eval row4019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4019, Integer.Sparse.eval_collectBalanced, rawRowCheck4019]

def rawRow4020 : Integer.Sparse Key := [(key1678, -2), (key1611, -2), (key1915, -2), (key1605, 6), (key1692, 2), (key1639, 2), (key1929, 2), (key1252, -2), (key1605, -2), (key1527, -2), (key1639, -6), (key1258, 2), (key1611, 2), (key1533, 2)]

theorem rawRowCheck4020 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form10 = rawRow4020 := by decide +kernel

def row4020 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

theorem rowCheck4020 : row4020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4020 := by decide +kernel

theorem rowEval4020 (x : Key → ℝ) : Integer.Sparse.eval row4020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4020, Integer.Sparse.eval_collectBalanced, rawRowCheck4020]

def rawRow4021 : Integer.Sparse Key := [(key1611, -2), (key1915, -2), (key1678, -2), (key1605, 6), (key1639, 2), (key1929, 2), (key1692, 2), (key1527, -2), (key1252, -2), (key1605, -2), (key1639, -6), (key1533, 2), (key1258, 2), (key1611, 2)]

theorem rawRowCheck4021 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form10 = rawRow4021 := by decide +kernel

def row4021 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

theorem rowCheck4021 : row4021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4021 := by decide +kernel

theorem rowEval4021 (x : Key → ℝ) : Integer.Sparse.eval row4021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4021, Integer.Sparse.eval_collectBalanced, rawRowCheck4021]

def rawRow4022 : Integer.Sparse Key := [(key1915, -2), (key1611, -2), (key1678, -2), (key1605, 6), (key1929, 2), (key1639, 2), (key1692, 2), (key1527, -2), (key1605, -2), (key1252, -2), (key1639, -6), (key1533, 2), (key1611, 2), (key1258, 2)]

theorem rawRowCheck4022 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form10 = rawRow4022 := by decide +kernel

def row4022 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

theorem rowCheck4022 : row4022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4022 := by decide +kernel

theorem rowEval4022 (x : Key → ℝ) : Integer.Sparse.eval row4022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4022, Integer.Sparse.eval_collectBalanced, rawRowCheck4022]

def rawRow4023 : Integer.Sparse Key := [(key1678, -2), (key1915, -2), (key1611, -2), (key1605, 6), (key1692, 2), (key1929, 2), (key1639, 2), (key1605, -2), (key1252, -2), (key1527, -2), (key1639, -6), (key1611, 2), (key1258, 2), (key1533, 2)]

theorem rawRowCheck4023 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form10 = rawRow4023 := by decide +kernel

def row4023 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

theorem rowCheck4023 : row4023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4023 := by decide +kernel

theorem rowEval4023 (x : Key → ℝ) : Integer.Sparse.eval row4023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4023, Integer.Sparse.eval_collectBalanced, rawRowCheck4023]

def rawRow4024 : Integer.Sparse Key := [(key1915, -2), (key1678, -2), (key1611, -2), (key1605, 6), (key1929, 2), (key1692, 2), (key1639, 2), (key1605, -2), (key1527, -2), (key1252, -2), (key1639, -6), (key1611, 2), (key1533, 2), (key1258, 2)]

theorem rawRowCheck4024 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form10 = rawRow4024 := by decide +kernel

def row4024 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

theorem rowCheck4024 : row4024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4024 := by decide +kernel

theorem rowEval4024 (x : Key → ℝ) : Integer.Sparse.eval row4024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4024, Integer.Sparse.eval_collectBalanced, rawRowCheck4024]

def rawRow4025 : Integer.Sparse Key := [(key1639, -2), (key1639, -2), (key1929, -2), (key1692, 6), (key1533, 2), (key1533, 2), (key1893, 2), (key1270, -2), (key1678, -2), (key1678, -2), (key1527, -6), (key1252, 2), (key1605, 2), (key1605, 2)]

theorem rawRowCheck4025 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form10 = rawRow4025 := by decide +kernel

def row4025 : Integer.Sparse Key := [(key1252, 2), (key1270, -2), (key1527, -6), (key1533, 4), (key1605, 4), (key1639, -4), (key1678, -4), (key1692, 6), (key1893, 2), (key1929, -2)]

theorem rowCheck4025 : row4025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4025 := by decide +kernel

theorem rowEval4025 (x : Key → ℝ) : Integer.Sparse.eval row4025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4025, Integer.Sparse.eval_collectBalanced, rawRowCheck4025]

def rawRow4026 : Integer.Sparse Key := [(key1639, -2), (key1929, -2), (key1639, -2), (key1692, 6), (key1533, 2), (key1893, 2), (key1533, 2), (key1678, -2), (key1270, -2), (key1678, -2), (key1527, -6), (key1605, 2), (key1252, 2), (key1605, 2)]

theorem rawRowCheck4026 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form10 = rawRow4026 := by decide +kernel

def row4026 : Integer.Sparse Key := [(key1252, 2), (key1270, -2), (key1527, -6), (key1533, 4), (key1605, 4), (key1639, -4), (key1678, -4), (key1692, 6), (key1893, 2), (key1929, -2)]

theorem rowCheck4026 : row4026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4026 := by decide +kernel

theorem rowEval4026 (x : Key → ℝ) : Integer.Sparse.eval row4026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4026, Integer.Sparse.eval_collectBalanced, rawRowCheck4026]

def rawRow4027 : Integer.Sparse Key := [(key1929, -2), (key1639, -2), (key1639, -2), (key1692, 6), (key1893, 2), (key1533, 2), (key1533, 2), (key1678, -2), (key1678, -2), (key1270, -2), (key1527, -6), (key1605, 2), (key1605, 2), (key1252, 2)]

theorem rawRowCheck4027 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form10 = rawRow4027 := by decide +kernel

def row4027 : Integer.Sparse Key := [(key1252, 2), (key1270, -2), (key1527, -6), (key1533, 4), (key1605, 4), (key1639, -4), (key1678, -4), (key1692, 6), (key1893, 2), (key1929, -2)]

theorem rowCheck4027 : row4027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4027 := by decide +kernel

theorem rowEval4027 (x : Key → ℝ) : Integer.Sparse.eval row4027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4027, Integer.Sparse.eval_collectBalanced, rawRowCheck4027]

def rawRow4028 : Integer.Sparse Key := [(key1639, -2), (key1692, -2), (key1929, -2), (key1639, 6), (key1611, 2), (key1678, 2), (key1915, 2), (key1258, -2), (key1533, -2), (key1611, -2), (key1605, -6), (key1252, 2), (key1527, 2), (key1605, 2)]

theorem rawRowCheck4028 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form10 = rawRow4028 := by decide +kernel

def row4028 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

theorem rowCheck4028 : row4028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4028 := by decide +kernel

theorem rowEval4028 (x : Key → ℝ) : Integer.Sparse.eval row4028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4028, Integer.Sparse.eval_collectBalanced, rawRowCheck4028]

def rawRow4029 : Integer.Sparse Key := [(key1692, -2), (key1639, -2), (key1929, -2), (key1639, 6), (key1678, 2), (key1611, 2), (key1915, 2), (key1258, -2), (key1611, -2), (key1533, -2), (key1605, -6), (key1252, 2), (key1605, 2), (key1527, 2)]

theorem rawRowCheck4029 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form10 = rawRow4029 := by decide +kernel

def row4029 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

theorem rowCheck4029 : row4029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4029 := by decide +kernel

theorem rowEval4029 (x : Key → ℝ) : Integer.Sparse.eval row4029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4029, Integer.Sparse.eval_collectBalanced, rawRowCheck4029]

def rawRow4030 : Integer.Sparse Key := [(key1639, -2), (key1929, -2), (key1692, -2), (key1639, 6), (key1611, 2), (key1915, 2), (key1678, 2), (key1533, -2), (key1258, -2), (key1611, -2), (key1605, -6), (key1527, 2), (key1252, 2), (key1605, 2)]

theorem rawRowCheck4030 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form10 = rawRow4030 := by decide +kernel

def row4030 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

theorem rowCheck4030 : row4030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4030 := by decide +kernel

theorem rowEval4030 (x : Key → ℝ) : Integer.Sparse.eval row4030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4030, Integer.Sparse.eval_collectBalanced, rawRowCheck4030]

def rawRow4031 : Integer.Sparse Key := [(key1929, -2), (key1639, -2), (key1692, -2), (key1639, 6), (key1915, 2), (key1611, 2), (key1678, 2), (key1533, -2), (key1611, -2), (key1258, -2), (key1605, -6), (key1527, 2), (key1605, 2), (key1252, 2)]

theorem rawRowCheck4031 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form10 = rawRow4031 := by decide +kernel

def row4031 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

theorem rowCheck4031 : row4031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4031 := by decide +kernel

theorem rowEval4031 (x : Key → ℝ) : Integer.Sparse.eval row4031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4031, Integer.Sparse.eval_collectBalanced, rawRowCheck4031]

def rawRow4032 : Integer.Sparse Key := [(key1692, -2), (key1929, -2), (key1639, -2), (key1639, 6), (key1678, 2), (key1915, 2), (key1611, 2), (key1611, -2), (key1258, -2), (key1533, -2), (key1605, -6), (key1605, 2), (key1252, 2), (key1527, 2)]

theorem rawRowCheck4032 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form10 = rawRow4032 := by decide +kernel

def row4032 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

theorem rowCheck4032 : row4032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4032 := by decide +kernel

theorem rowEval4032 (x : Key → ℝ) : Integer.Sparse.eval row4032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4032, Integer.Sparse.eval_collectBalanced, rawRowCheck4032]

def rawRow4033 : Integer.Sparse Key := [(key1929, -2), (key1692, -2), (key1639, -2), (key1639, 6), (key1915, 2), (key1678, 2), (key1611, 2), (key1611, -2), (key1533, -2), (key1258, -2), (key1605, -6), (key1605, 2), (key1527, 2), (key1252, 2)]

theorem rawRowCheck4033 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form10 = rawRow4033 := by decide +kernel

def row4033 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

theorem rowCheck4033 : row4033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4033 := by decide +kernel

theorem rowEval4033 (x : Key → ℝ) : Integer.Sparse.eval row4033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4033, Integer.Sparse.eval_collectBalanced, rawRowCheck4033]

def rawRow4034 : Integer.Sparse Key := [(key1526, -2), (key1530, -2), (key1764, -2), (key1530, 6), (key1604, 2), (key1608, 2), (key1805, 2), (key1255, -2), (key1608, -2), (key1637, -2), (key1647, -6), (key1264, 2), (key1647, 2), (key1671, 2)]

theorem rawRowCheck4034 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form11 = rawRow4034 := by decide +kernel

def row4034 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

theorem rowCheck4034 : row4034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4034 := by decide +kernel

theorem rowEval4034 (x : Key → ℝ) : Integer.Sparse.eval row4034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4034, Integer.Sparse.eval_collectBalanced, rawRowCheck4034]

def rawRow4035 : Integer.Sparse Key := [(key1530, -2), (key1526, -2), (key1764, -2), (key1530, 6), (key1608, 2), (key1604, 2), (key1805, 2), (key1255, -2), (key1637, -2), (key1608, -2), (key1647, -6), (key1264, 2), (key1671, 2), (key1647, 2)]

theorem rawRowCheck4035 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form11 = rawRow4035 := by decide +kernel

def row4035 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

theorem rowCheck4035 : row4035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4035 := by decide +kernel

theorem rowEval4035 (x : Key → ℝ) : Integer.Sparse.eval row4035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4035, Integer.Sparse.eval_collectBalanced, rawRowCheck4035]

def rawRow4036 : Integer.Sparse Key := [(key1526, -2), (key1764, -2), (key1530, -2), (key1530, 6), (key1604, 2), (key1805, 2), (key1608, 2), (key1608, -2), (key1255, -2), (key1637, -2), (key1647, -6), (key1647, 2), (key1264, 2), (key1671, 2)]

theorem rawRowCheck4036 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form11 = rawRow4036 := by decide +kernel

def row4036 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

theorem rowCheck4036 : row4036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4036 := by decide +kernel

theorem rowEval4036 (x : Key → ℝ) : Integer.Sparse.eval row4036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4036, Integer.Sparse.eval_collectBalanced, rawRowCheck4036]

def rawRow4037 : Integer.Sparse Key := [(key1764, -2), (key1526, -2), (key1530, -2), (key1530, 6), (key1805, 2), (key1604, 2), (key1608, 2), (key1608, -2), (key1637, -2), (key1255, -2), (key1647, -6), (key1647, 2), (key1671, 2), (key1264, 2)]

theorem rawRowCheck4037 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form11 = rawRow4037 := by decide +kernel

def row4037 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

theorem rowCheck4037 : row4037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4037 := by decide +kernel

theorem rowEval4037 (x : Key → ℝ) : Integer.Sparse.eval row4037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4037, Integer.Sparse.eval_collectBalanced, rawRowCheck4037]

def rawRow4038 : Integer.Sparse Key := [(key1530, -2), (key1764, -2), (key1526, -2), (key1530, 6), (key1608, 2), (key1805, 2), (key1604, 2), (key1637, -2), (key1255, -2), (key1608, -2), (key1647, -6), (key1671, 2), (key1264, 2), (key1647, 2)]

theorem rawRowCheck4038 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form11 = rawRow4038 := by decide +kernel

def row4038 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

theorem rowCheck4038 : row4038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4038 := by decide +kernel

theorem rowEval4038 (x : Key → ℝ) : Integer.Sparse.eval row4038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4038, Integer.Sparse.eval_collectBalanced, rawRowCheck4038]

def rawRow4039 : Integer.Sparse Key := [(key1764, -2), (key1530, -2), (key1526, -2), (key1530, 6), (key1805, 2), (key1608, 2), (key1604, 2), (key1637, -2), (key1608, -2), (key1255, -2), (key1647, -6), (key1671, 2), (key1647, 2), (key1264, 2)]

theorem rawRowCheck4039 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form11 = rawRow4039 := by decide +kernel

def row4039 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

theorem rowCheck4039 : row4039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4039 := by decide +kernel

theorem rowEval4039 (x : Key → ℝ) : Integer.Sparse.eval row4039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4039, Integer.Sparse.eval_collectBalanced, rawRowCheck4039]

def rawRow4040 : Integer.Sparse Key := [(key1530, -2), (key1530, -2), (key1764, -2), (key1526, 6), (key1637, 2), (key1637, 2), (key1829, 2), (key1251, -2), (key1604, -2), (key1604, -2), (key1671, -6), (key1264, 2), (key1647, 2), (key1647, 2)]

theorem rawRowCheck4040 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form11 = rawRow4040 := by decide +kernel

def row4040 : Integer.Sparse Key := [(key1251, -2), (key1264, 2), (key1526, 6), (key1530, -4), (key1604, -4), (key1637, 4), (key1647, 4), (key1671, -6), (key1764, -2), (key1829, 2)]

theorem rowCheck4040 : row4040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4040 := by decide +kernel

theorem rowEval4040 (x : Key → ℝ) : Integer.Sparse.eval row4040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4040, Integer.Sparse.eval_collectBalanced, rawRowCheck4040]

def rawRow4041 : Integer.Sparse Key := [(key1530, -2), (key1764, -2), (key1530, -2), (key1526, 6), (key1637, 2), (key1829, 2), (key1637, 2), (key1604, -2), (key1251, -2), (key1604, -2), (key1671, -6), (key1647, 2), (key1264, 2), (key1647, 2)]

theorem rawRowCheck4041 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form11 = rawRow4041 := by decide +kernel

def row4041 : Integer.Sparse Key := [(key1251, -2), (key1264, 2), (key1526, 6), (key1530, -4), (key1604, -4), (key1637, 4), (key1647, 4), (key1671, -6), (key1764, -2), (key1829, 2)]

theorem rowCheck4041 : row4041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4041 := by decide +kernel

theorem rowEval4041 (x : Key → ℝ) : Integer.Sparse.eval row4041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4041, Integer.Sparse.eval_collectBalanced, rawRowCheck4041]

def rawRow4042 : Integer.Sparse Key := [(key1764, -2), (key1530, -2), (key1530, -2), (key1526, 6), (key1829, 2), (key1637, 2), (key1637, 2), (key1604, -2), (key1604, -2), (key1251, -2), (key1671, -6), (key1647, 2), (key1647, 2), (key1264, 2)]

theorem rawRowCheck4042 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form11 = rawRow4042 := by decide +kernel

def row4042 : Integer.Sparse Key := [(key1251, -2), (key1264, 2), (key1526, 6), (key1530, -4), (key1604, -4), (key1637, 4), (key1647, 4), (key1671, -6), (key1764, -2), (key1829, 2)]

theorem rowCheck4042 : row4042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4042 := by decide +kernel

theorem rowEval4042 (x : Key → ℝ) : Integer.Sparse.eval row4042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4042, Integer.Sparse.eval_collectBalanced, rawRowCheck4042]

def rawRow4043 : Integer.Sparse Key := [(key1604, -2), (key1608, -2), (key1805, -2), (key1647, 6), (key1526, 2), (key1530, 2), (key1764, 2), (key1264, -2), (key1647, -2), (key1671, -2), (key1530, -6), (key1255, 2), (key1608, 2), (key1637, 2)]

theorem rawRowCheck4043 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form11 = rawRow4043 := by decide +kernel

def row4043 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

theorem rowCheck4043 : row4043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4043 := by decide +kernel

theorem rowEval4043 (x : Key → ℝ) : Integer.Sparse.eval row4043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4043, Integer.Sparse.eval_collectBalanced, rawRowCheck4043]

def rawRow4044 : Integer.Sparse Key := [(key1608, -2), (key1604, -2), (key1805, -2), (key1647, 6), (key1530, 2), (key1526, 2), (key1764, 2), (key1264, -2), (key1671, -2), (key1647, -2), (key1530, -6), (key1255, 2), (key1637, 2), (key1608, 2)]

theorem rawRowCheck4044 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form11 = rawRow4044 := by decide +kernel

def row4044 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

theorem rowCheck4044 : row4044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4044 := by decide +kernel

theorem rowEval4044 (x : Key → ℝ) : Integer.Sparse.eval row4044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4044, Integer.Sparse.eval_collectBalanced, rawRowCheck4044]

def rawRow4045 : Integer.Sparse Key := [(key1604, -2), (key1805, -2), (key1608, -2), (key1647, 6), (key1526, 2), (key1764, 2), (key1530, 2), (key1647, -2), (key1264, -2), (key1671, -2), (key1530, -6), (key1608, 2), (key1255, 2), (key1637, 2)]

theorem rawRowCheck4045 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form11 = rawRow4045 := by decide +kernel

def row4045 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

theorem rowCheck4045 : row4045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4045 := by decide +kernel

theorem rowEval4045 (x : Key → ℝ) : Integer.Sparse.eval row4045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4045, Integer.Sparse.eval_collectBalanced, rawRowCheck4045]

def rawRow4046 : Integer.Sparse Key := [(key1805, -2), (key1604, -2), (key1608, -2), (key1647, 6), (key1764, 2), (key1526, 2), (key1530, 2), (key1647, -2), (key1671, -2), (key1264, -2), (key1530, -6), (key1608, 2), (key1637, 2), (key1255, 2)]

theorem rawRowCheck4046 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form11 = rawRow4046 := by decide +kernel

def row4046 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

theorem rowCheck4046 : row4046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4046 := by decide +kernel

theorem rowEval4046 (x : Key → ℝ) : Integer.Sparse.eval row4046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4046, Integer.Sparse.eval_collectBalanced, rawRowCheck4046]

def rawRow4047 : Integer.Sparse Key := [(key1608, -2), (key1805, -2), (key1604, -2), (key1647, 6), (key1530, 2), (key1764, 2), (key1526, 2), (key1671, -2), (key1264, -2), (key1647, -2), (key1530, -6), (key1637, 2), (key1255, 2), (key1608, 2)]

theorem rawRowCheck4047 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form11 = rawRow4047 := by decide +kernel

def row4047 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

theorem rowCheck4047 : row4047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4047 := by decide +kernel

theorem rowEval4047 (x : Key → ℝ) : Integer.Sparse.eval row4047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4047, Integer.Sparse.eval_collectBalanced, rawRowCheck4047]

def rawRow4048 : Integer.Sparse Key := [(key1805, -2), (key1608, -2), (key1604, -2), (key1647, 6), (key1764, 2), (key1530, 2), (key1526, 2), (key1671, -2), (key1647, -2), (key1264, -2), (key1530, -6), (key1637, 2), (key1608, 2), (key1255, 2)]

theorem rawRowCheck4048 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form11 = rawRow4048 := by decide +kernel

def row4048 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

theorem rowCheck4048 : row4048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4048 := by decide +kernel

theorem rowEval4048 (x : Key → ℝ) : Integer.Sparse.eval row4048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4048, Integer.Sparse.eval_collectBalanced, rawRowCheck4048]

def rawRow4049 : Integer.Sparse Key := [(key1608, -2), (key1647, -2), (key1805, -2), (key1604, 6), (key1637, 2), (key1671, 2), (key1829, 2), (key1251, -2), (key1526, -2), (key1604, -2), (key1637, -6), (key1255, 2), (key1530, 2), (key1608, 2)]

theorem rawRowCheck4049 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form11 = rawRow4049 := by decide +kernel

def row4049 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

theorem rowCheck4049 : row4049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4049 := by decide +kernel

theorem rowEval4049 (x : Key → ℝ) : Integer.Sparse.eval row4049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4049, Integer.Sparse.eval_collectBalanced, rawRowCheck4049]

def rawRow4050 : Integer.Sparse Key := [(key1647, -2), (key1608, -2), (key1805, -2), (key1604, 6), (key1671, 2), (key1637, 2), (key1829, 2), (key1251, -2), (key1604, -2), (key1526, -2), (key1637, -6), (key1255, 2), (key1608, 2), (key1530, 2)]

theorem rawRowCheck4050 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form11 = rawRow4050 := by decide +kernel

def row4050 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

theorem rowCheck4050 : row4050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4050 := by decide +kernel

theorem rowEval4050 (x : Key → ℝ) : Integer.Sparse.eval row4050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4050, Integer.Sparse.eval_collectBalanced, rawRowCheck4050]

def rawRow4051 : Integer.Sparse Key := [(key1608, -2), (key1805, -2), (key1647, -2), (key1604, 6), (key1637, 2), (key1829, 2), (key1671, 2), (key1526, -2), (key1251, -2), (key1604, -2), (key1637, -6), (key1530, 2), (key1255, 2), (key1608, 2)]

theorem rawRowCheck4051 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form11 = rawRow4051 := by decide +kernel

def row4051 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

theorem rowCheck4051 : row4051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4051 := by decide +kernel

theorem rowEval4051 (x : Key → ℝ) : Integer.Sparse.eval row4051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4051, Integer.Sparse.eval_collectBalanced, rawRowCheck4051]

def rawRow4052 : Integer.Sparse Key := [(key1805, -2), (key1608, -2), (key1647, -2), (key1604, 6), (key1829, 2), (key1637, 2), (key1671, 2), (key1526, -2), (key1604, -2), (key1251, -2), (key1637, -6), (key1530, 2), (key1608, 2), (key1255, 2)]

theorem rawRowCheck4052 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form11 = rawRow4052 := by decide +kernel

def row4052 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

theorem rowCheck4052 : row4052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4052 := by decide +kernel

theorem rowEval4052 (x : Key → ℝ) : Integer.Sparse.eval row4052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4052, Integer.Sparse.eval_collectBalanced, rawRowCheck4052]

def rawRow4053 : Integer.Sparse Key := [(key1647, -2), (key1805, -2), (key1608, -2), (key1604, 6), (key1671, 2), (key1829, 2), (key1637, 2), (key1604, -2), (key1251, -2), (key1526, -2), (key1637, -6), (key1608, 2), (key1255, 2), (key1530, 2)]

theorem rawRowCheck4053 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form11 = rawRow4053 := by decide +kernel

def row4053 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

theorem rowCheck4053 : row4053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4053 := by decide +kernel

theorem rowEval4053 (x : Key → ℝ) : Integer.Sparse.eval row4053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4053, Integer.Sparse.eval_collectBalanced, rawRowCheck4053]

def rawRow4054 : Integer.Sparse Key := [(key1805, -2), (key1647, -2), (key1608, -2), (key1604, 6), (key1829, 2), (key1671, 2), (key1637, 2), (key1604, -2), (key1526, -2), (key1251, -2), (key1637, -6), (key1608, 2), (key1530, 2), (key1255, 2)]

theorem rawRowCheck4054 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form11 = rawRow4054 := by decide +kernel

def row4054 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

theorem rowCheck4054 : row4054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4054 := by decide +kernel

theorem rowEval4054 (x : Key → ℝ) : Integer.Sparse.eval row4054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4054, Integer.Sparse.eval_collectBalanced, rawRowCheck4054]

def rawRow4055 : Integer.Sparse Key := [(key1637, -2), (key1637, -2), (key1829, -2), (key1671, 6), (key1530, 2), (key1530, 2), (key1764, 2), (key1264, -2), (key1647, -2), (key1647, -2), (key1526, -6), (key1251, 2), (key1604, 2), (key1604, 2)]

theorem rawRowCheck4055 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form11 = rawRow4055 := by decide +kernel

def row4055 : Integer.Sparse Key := [(key1251, 2), (key1264, -2), (key1526, -6), (key1530, 4), (key1604, 4), (key1637, -4), (key1647, -4), (key1671, 6), (key1764, 2), (key1829, -2)]

theorem rowCheck4055 : row4055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4055 := by decide +kernel

theorem rowEval4055 (x : Key → ℝ) : Integer.Sparse.eval row4055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4055, Integer.Sparse.eval_collectBalanced, rawRowCheck4055]

def rawRow4056 : Integer.Sparse Key := [(key1637, -2), (key1829, -2), (key1637, -2), (key1671, 6), (key1530, 2), (key1764, 2), (key1530, 2), (key1647, -2), (key1264, -2), (key1647, -2), (key1526, -6), (key1604, 2), (key1251, 2), (key1604, 2)]

theorem rawRowCheck4056 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form11 = rawRow4056 := by decide +kernel

def row4056 : Integer.Sparse Key := [(key1251, 2), (key1264, -2), (key1526, -6), (key1530, 4), (key1604, 4), (key1637, -4), (key1647, -4), (key1671, 6), (key1764, 2), (key1829, -2)]

theorem rowCheck4056 : row4056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4056 := by decide +kernel

theorem rowEval4056 (x : Key → ℝ) : Integer.Sparse.eval row4056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4056, Integer.Sparse.eval_collectBalanced, rawRowCheck4056]

def rawRow4057 : Integer.Sparse Key := [(key1829, -2), (key1637, -2), (key1637, -2), (key1671, 6), (key1764, 2), (key1530, 2), (key1530, 2), (key1647, -2), (key1647, -2), (key1264, -2), (key1526, -6), (key1604, 2), (key1604, 2), (key1251, 2)]

theorem rawRowCheck4057 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form11 = rawRow4057 := by decide +kernel

def row4057 : Integer.Sparse Key := [(key1251, 2), (key1264, -2), (key1526, -6), (key1530, 4), (key1604, 4), (key1637, -4), (key1647, -4), (key1671, 6), (key1764, 2), (key1829, -2)]

theorem rowCheck4057 : row4057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4057 := by decide +kernel

theorem rowEval4057 (x : Key → ℝ) : Integer.Sparse.eval row4057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4057, Integer.Sparse.eval_collectBalanced, rawRowCheck4057]

def rawRow4058 : Integer.Sparse Key := [(key1637, -2), (key1671, -2), (key1829, -2), (key1637, 6), (key1608, 2), (key1647, 2), (key1805, 2), (key1255, -2), (key1530, -2), (key1608, -2), (key1604, -6), (key1251, 2), (key1526, 2), (key1604, 2)]

theorem rawRowCheck4058 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form11 = rawRow4058 := by decide +kernel

def row4058 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

theorem rowCheck4058 : row4058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4058 := by decide +kernel

theorem rowEval4058 (x : Key → ℝ) : Integer.Sparse.eval row4058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4058, Integer.Sparse.eval_collectBalanced, rawRowCheck4058]

def rawRow4059 : Integer.Sparse Key := [(key1671, -2), (key1637, -2), (key1829, -2), (key1637, 6), (key1647, 2), (key1608, 2), (key1805, 2), (key1255, -2), (key1608, -2), (key1530, -2), (key1604, -6), (key1251, 2), (key1604, 2), (key1526, 2)]

theorem rawRowCheck4059 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form11 = rawRow4059 := by decide +kernel

def row4059 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

theorem rowCheck4059 : row4059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4059 := by decide +kernel

theorem rowEval4059 (x : Key → ℝ) : Integer.Sparse.eval row4059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4059, Integer.Sparse.eval_collectBalanced, rawRowCheck4059]

def rawRow4060 : Integer.Sparse Key := [(key1637, -2), (key1829, -2), (key1671, -2), (key1637, 6), (key1608, 2), (key1805, 2), (key1647, 2), (key1530, -2), (key1255, -2), (key1608, -2), (key1604, -6), (key1526, 2), (key1251, 2), (key1604, 2)]

theorem rawRowCheck4060 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form11 = rawRow4060 := by decide +kernel

def row4060 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

theorem rowCheck4060 : row4060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4060 := by decide +kernel

theorem rowEval4060 (x : Key → ℝ) : Integer.Sparse.eval row4060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4060, Integer.Sparse.eval_collectBalanced, rawRowCheck4060]

def rawRow4061 : Integer.Sparse Key := [(key1829, -2), (key1637, -2), (key1671, -2), (key1637, 6), (key1805, 2), (key1608, 2), (key1647, 2), (key1530, -2), (key1608, -2), (key1255, -2), (key1604, -6), (key1526, 2), (key1604, 2), (key1251, 2)]

theorem rawRowCheck4061 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form11 = rawRow4061 := by decide +kernel

def row4061 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

theorem rowCheck4061 : row4061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4061 := by decide +kernel

theorem rowEval4061 (x : Key → ℝ) : Integer.Sparse.eval row4061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4061, Integer.Sparse.eval_collectBalanced, rawRowCheck4061]

def rawRow4062 : Integer.Sparse Key := [(key1671, -2), (key1829, -2), (key1637, -2), (key1637, 6), (key1647, 2), (key1805, 2), (key1608, 2), (key1608, -2), (key1255, -2), (key1530, -2), (key1604, -6), (key1604, 2), (key1251, 2), (key1526, 2)]

theorem rawRowCheck4062 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form11 = rawRow4062 := by decide +kernel

def row4062 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

theorem rowCheck4062 : row4062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4062 := by decide +kernel

theorem rowEval4062 (x : Key → ℝ) : Integer.Sparse.eval row4062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4062, Integer.Sparse.eval_collectBalanced, rawRowCheck4062]

def rawRow4063 : Integer.Sparse Key := [(key1829, -2), (key1671, -2), (key1637, -2), (key1637, 6), (key1805, 2), (key1647, 2), (key1608, 2), (key1608, -2), (key1530, -2), (key1255, -2), (key1604, -6), (key1604, 2), (key1526, 2), (key1251, 2)]

theorem rawRowCheck4063 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form11 = rawRow4063 := by decide +kernel

def row4063 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

theorem rowCheck4063 : row4063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4063 := by decide +kernel

theorem rowEval4063 (x : Key → ℝ) : Integer.Sparse.eval row4063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4063, Integer.Sparse.eval_collectBalanced, rawRowCheck4063]

def rawRow4064 : Integer.Sparse Key := [(key1541, -2), (key1545, -2), (key1771, -2), (key1386, 1), (key1390, 1), (key1541, 1), (key1554, 1), (key1771, 1), (key1778, 1), (key1568, 2), (key1572, 2), (key1787, 2), (key1291, -1), (key1295, -1), (key1568, -1), (key1591, -1), (key1787, -1), (key1796, -1), (key1419, -1), (key1423, -1), (key1617, -1), (key1622, -1), (key1812, -1), (key1815, -1), (key1311, 1), (key1315, 1), (key1617, 1), (key1631, 1), (key1812, 1), (key1823, 1)]

theorem rawRowCheck4064 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form12 = rawRow4064 := by decide +kernel

def row4064 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4064 : row4064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4064 := by decide +kernel

theorem rowEval4064 (x : Key → ℝ) : Integer.Sparse.eval row4064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4064, Integer.Sparse.eval_collectBalanced, rawRowCheck4064]

def rawRow4065 : Integer.Sparse Key := [(key1545, -2), (key1541, -2), (key1771, -2), (key1390, 1), (key1386, 1), (key1554, 1), (key1541, 1), (key1778, 1), (key1771, 1), (key1572, 2), (key1568, 2), (key1787, 2), (key1295, -1), (key1291, -1), (key1591, -1), (key1568, -1), (key1796, -1), (key1787, -1), (key1423, -1), (key1419, -1), (key1622, -1), (key1617, -1), (key1815, -1), (key1812, -1), (key1315, 1), (key1311, 1), (key1631, 1), (key1617, 1), (key1823, 1), (key1812, 1)]

theorem rawRowCheck4065 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form12 = rawRow4065 := by decide +kernel

def row4065 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4065 : row4065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4065 := by decide +kernel

theorem rowEval4065 (x : Key → ℝ) : Integer.Sparse.eval row4065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4065, Integer.Sparse.eval_collectBalanced, rawRowCheck4065]

def rawRow4066 : Integer.Sparse Key := [(key1541, -2), (key1771, -2), (key1545, -2), (key1541, 1), (key1771, 1), (key1386, 1), (key1778, 1), (key1390, 1), (key1554, 1), (key1568, 2), (key1787, 2), (key1572, 2), (key1568, -1), (key1787, -1), (key1291, -1), (key1796, -1), (key1295, -1), (key1591, -1), (key1617, -1), (key1812, -1), (key1419, -1), (key1815, -1), (key1423, -1), (key1622, -1), (key1617, 1), (key1812, 1), (key1311, 1), (key1823, 1), (key1315, 1), (key1631, 1)]

theorem rawRowCheck4066 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form12 = rawRow4066 := by decide +kernel

def row4066 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4066 : row4066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4066 := by decide +kernel

theorem rowEval4066 (x : Key → ℝ) : Integer.Sparse.eval row4066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4066, Integer.Sparse.eval_collectBalanced, rawRowCheck4066]

def rawRow4067 : Integer.Sparse Key := [(key1771, -2), (key1541, -2), (key1545, -2), (key1771, 1), (key1541, 1), (key1778, 1), (key1386, 1), (key1554, 1), (key1390, 1), (key1787, 2), (key1568, 2), (key1572, 2), (key1787, -1), (key1568, -1), (key1796, -1), (key1291, -1), (key1591, -1), (key1295, -1), (key1812, -1), (key1617, -1), (key1815, -1), (key1419, -1), (key1622, -1), (key1423, -1), (key1812, 1), (key1617, 1), (key1823, 1), (key1311, 1), (key1631, 1), (key1315, 1)]

theorem rawRowCheck4067 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form12 = rawRow4067 := by decide +kernel

def row4067 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4067 : row4067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4067 := by decide +kernel

theorem rowEval4067 (x : Key → ℝ) : Integer.Sparse.eval row4067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4067, Integer.Sparse.eval_collectBalanced, rawRowCheck4067]

def rawRow4068 : Integer.Sparse Key := [(key1545, -2), (key1771, -2), (key1541, -2), (key1554, 1), (key1778, 1), (key1390, 1), (key1771, 1), (key1386, 1), (key1541, 1), (key1572, 2), (key1787, 2), (key1568, 2), (key1591, -1), (key1796, -1), (key1295, -1), (key1787, -1), (key1291, -1), (key1568, -1), (key1622, -1), (key1815, -1), (key1423, -1), (key1812, -1), (key1419, -1), (key1617, -1), (key1631, 1), (key1823, 1), (key1315, 1), (key1812, 1), (key1311, 1), (key1617, 1)]

theorem rawRowCheck4068 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form12 = rawRow4068 := by decide +kernel

def row4068 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4068 : row4068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4068 := by decide +kernel

theorem rowEval4068 (x : Key → ℝ) : Integer.Sparse.eval row4068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4068, Integer.Sparse.eval_collectBalanced, rawRowCheck4068]

def rawRow4069 : Integer.Sparse Key := [(key1771, -2), (key1545, -2), (key1541, -2), (key1778, 1), (key1554, 1), (key1771, 1), (key1390, 1), (key1541, 1), (key1386, 1), (key1787, 2), (key1572, 2), (key1568, 2), (key1796, -1), (key1591, -1), (key1787, -1), (key1295, -1), (key1568, -1), (key1291, -1), (key1815, -1), (key1622, -1), (key1812, -1), (key1423, -1), (key1617, -1), (key1419, -1), (key1823, 1), (key1631, 1), (key1812, 1), (key1315, 1), (key1617, 1), (key1311, 1)]

theorem rawRowCheck4069 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form12 = rawRow4069 := by decide +kernel

def row4069 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4069 : row4069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4069 := by decide +kernel

theorem rowEval4069 (x : Key → ℝ) : Integer.Sparse.eval row4069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4069, Integer.Sparse.eval_collectBalanced, rawRowCheck4069]

def rawRow4070 : Integer.Sparse Key := [(key1554, -2), (key1554, -2), (key1778, -2), (key1390, 1), (key1390, 1), (key1545, 1), (key1545, 1), (key1771, 1), (key1771, 1), (key1591, 2), (key1591, 2), (key1796, 2), (key1295, -1), (key1295, -1), (key1572, -1), (key1572, -1), (key1787, -1), (key1787, -1), (key1442, -1), (key1442, -1), (key1631, -1), (key1631, -1), (key1823, -1), (key1823, -1), (key1324, 1), (key1324, 1), (key1622, 1), (key1622, 1), (key1815, 1), (key1815, 1)]

theorem rawRowCheck4070 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form12 = rawRow4070 := by decide +kernel

def row4070 : Integer.Sparse Key := [(key1295, -2), (key1324, 2), (key1390, 2), (key1442, -2), (key1545, 2), (key1554, -4), (key1572, -2), (key1591, 4), (key1622, 2), (key1631, -2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

theorem rowCheck4070 : row4070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4070 := by decide +kernel

theorem rowEval4070 (x : Key → ℝ) : Integer.Sparse.eval row4070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4070, Integer.Sparse.eval_collectBalanced, rawRowCheck4070]

def rawRow4071 : Integer.Sparse Key := [(key1554, -2), (key1778, -2), (key1554, -2), (key1545, 1), (key1771, 1), (key1390, 1), (key1771, 1), (key1390, 1), (key1545, 1), (key1591, 2), (key1796, 2), (key1591, 2), (key1572, -1), (key1787, -1), (key1295, -1), (key1787, -1), (key1295, -1), (key1572, -1), (key1631, -1), (key1823, -1), (key1442, -1), (key1823, -1), (key1442, -1), (key1631, -1), (key1622, 1), (key1815, 1), (key1324, 1), (key1815, 1), (key1324, 1), (key1622, 1)]

theorem rawRowCheck4071 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form12 = rawRow4071 := by decide +kernel

def row4071 : Integer.Sparse Key := [(key1295, -2), (key1324, 2), (key1390, 2), (key1442, -2), (key1545, 2), (key1554, -4), (key1572, -2), (key1591, 4), (key1622, 2), (key1631, -2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

theorem rowCheck4071 : row4071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4071 := by decide +kernel

theorem rowEval4071 (x : Key → ℝ) : Integer.Sparse.eval row4071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4071, Integer.Sparse.eval_collectBalanced, rawRowCheck4071]

def rawRow4072 : Integer.Sparse Key := [(key1778, -2), (key1554, -2), (key1554, -2), (key1771, 1), (key1545, 1), (key1771, 1), (key1390, 1), (key1545, 1), (key1390, 1), (key1796, 2), (key1591, 2), (key1591, 2), (key1787, -1), (key1572, -1), (key1787, -1), (key1295, -1), (key1572, -1), (key1295, -1), (key1823, -1), (key1631, -1), (key1823, -1), (key1442, -1), (key1631, -1), (key1442, -1), (key1815, 1), (key1622, 1), (key1815, 1), (key1324, 1), (key1622, 1), (key1324, 1)]

theorem rawRowCheck4072 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form12 = rawRow4072 := by decide +kernel

def row4072 : Integer.Sparse Key := [(key1295, -2), (key1324, 2), (key1390, 2), (key1442, -2), (key1545, 2), (key1554, -4), (key1572, -2), (key1591, 4), (key1622, 2), (key1631, -2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

theorem rowCheck4072 : row4072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4072 := by decide +kernel

theorem rowEval4072 (x : Key → ℝ) : Integer.Sparse.eval row4072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4072, Integer.Sparse.eval_collectBalanced, rawRowCheck4072]

def rawRow4073 : Integer.Sparse Key := [(key1568, -2), (key1572, -2), (key1787, -2), (key1419, 1), (key1423, 1), (key1617, 1), (key1622, 1), (key1812, 1), (key1815, 1), (key1541, 2), (key1545, 2), (key1771, 2), (key1311, -1), (key1315, -1), (key1617, -1), (key1631, -1), (key1812, -1), (key1823, -1), (key1386, -1), (key1390, -1), (key1541, -1), (key1554, -1), (key1771, -1), (key1778, -1), (key1291, 1), (key1295, 1), (key1568, 1), (key1591, 1), (key1787, 1), (key1796, 1)]

theorem rawRowCheck4073 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form12 = rawRow4073 := by decide +kernel

def row4073 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4073 : row4073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4073 := by decide +kernel

theorem rowEval4073 (x : Key → ℝ) : Integer.Sparse.eval row4073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4073, Integer.Sparse.eval_collectBalanced, rawRowCheck4073]

def rawRow4074 : Integer.Sparse Key := [(key1572, -2), (key1568, -2), (key1787, -2), (key1423, 1), (key1419, 1), (key1622, 1), (key1617, 1), (key1815, 1), (key1812, 1), (key1545, 2), (key1541, 2), (key1771, 2), (key1315, -1), (key1311, -1), (key1631, -1), (key1617, -1), (key1823, -1), (key1812, -1), (key1390, -1), (key1386, -1), (key1554, -1), (key1541, -1), (key1778, -1), (key1771, -1), (key1295, 1), (key1291, 1), (key1591, 1), (key1568, 1), (key1796, 1), (key1787, 1)]

theorem rawRowCheck4074 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form12 = rawRow4074 := by decide +kernel

def row4074 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4074 : row4074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4074 := by decide +kernel

theorem rowEval4074 (x : Key → ℝ) : Integer.Sparse.eval row4074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4074, Integer.Sparse.eval_collectBalanced, rawRowCheck4074]

def rawRow4075 : Integer.Sparse Key := [(key1568, -2), (key1787, -2), (key1572, -2), (key1617, 1), (key1812, 1), (key1419, 1), (key1815, 1), (key1423, 1), (key1622, 1), (key1541, 2), (key1771, 2), (key1545, 2), (key1617, -1), (key1812, -1), (key1311, -1), (key1823, -1), (key1315, -1), (key1631, -1), (key1541, -1), (key1771, -1), (key1386, -1), (key1778, -1), (key1390, -1), (key1554, -1), (key1568, 1), (key1787, 1), (key1291, 1), (key1796, 1), (key1295, 1), (key1591, 1)]

theorem rawRowCheck4075 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form12 = rawRow4075 := by decide +kernel

def row4075 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4075 : row4075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4075 := by decide +kernel

theorem rowEval4075 (x : Key → ℝ) : Integer.Sparse.eval row4075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4075, Integer.Sparse.eval_collectBalanced, rawRowCheck4075]

def rawRow4076 : Integer.Sparse Key := [(key1787, -2), (key1568, -2), (key1572, -2), (key1812, 1), (key1617, 1), (key1815, 1), (key1419, 1), (key1622, 1), (key1423, 1), (key1771, 2), (key1541, 2), (key1545, 2), (key1812, -1), (key1617, -1), (key1823, -1), (key1311, -1), (key1631, -1), (key1315, -1), (key1771, -1), (key1541, -1), (key1778, -1), (key1386, -1), (key1554, -1), (key1390, -1), (key1787, 1), (key1568, 1), (key1796, 1), (key1291, 1), (key1591, 1), (key1295, 1)]

theorem rawRowCheck4076 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form12 = rawRow4076 := by decide +kernel

def row4076 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4076 : row4076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4076 := by decide +kernel

theorem rowEval4076 (x : Key → ℝ) : Integer.Sparse.eval row4076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4076, Integer.Sparse.eval_collectBalanced, rawRowCheck4076]

def rawRow4077 : Integer.Sparse Key := [(key1572, -2), (key1787, -2), (key1568, -2), (key1622, 1), (key1815, 1), (key1423, 1), (key1812, 1), (key1419, 1), (key1617, 1), (key1545, 2), (key1771, 2), (key1541, 2), (key1631, -1), (key1823, -1), (key1315, -1), (key1812, -1), (key1311, -1), (key1617, -1), (key1554, -1), (key1778, -1), (key1390, -1), (key1771, -1), (key1386, -1), (key1541, -1), (key1591, 1), (key1796, 1), (key1295, 1), (key1787, 1), (key1291, 1), (key1568, 1)]

theorem rawRowCheck4077 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form12 = rawRow4077 := by decide +kernel

def row4077 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4077 : row4077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4077 := by decide +kernel

theorem rowEval4077 (x : Key → ℝ) : Integer.Sparse.eval row4077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4077, Integer.Sparse.eval_collectBalanced, rawRowCheck4077]

def rawRow4078 : Integer.Sparse Key := [(key1787, -2), (key1572, -2), (key1568, -2), (key1815, 1), (key1622, 1), (key1812, 1), (key1423, 1), (key1617, 1), (key1419, 1), (key1771, 2), (key1545, 2), (key1541, 2), (key1823, -1), (key1631, -1), (key1812, -1), (key1315, -1), (key1617, -1), (key1311, -1), (key1778, -1), (key1554, -1), (key1771, -1), (key1390, -1), (key1541, -1), (key1386, -1), (key1796, 1), (key1591, 1), (key1787, 1), (key1295, 1), (key1568, 1), (key1291, 1)]

theorem rawRowCheck4078 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form12 = rawRow4078 := by decide +kernel

def row4078 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4078 : row4078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4078 := by decide +kernel

theorem rowEval4078 (x : Key → ℝ) : Integer.Sparse.eval row4078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4078, Integer.Sparse.eval_collectBalanced, rawRowCheck4078]

def rawRow4079 : Integer.Sparse Key := [(key1622, -2), (key1657, -2), (key1815, -2), (key1423, 1), (key1454, 1), (key1572, 1), (key1654, 1), (key1787, 1), (key1812, 1), (key1631, 2), (key1665, 2), (key1823, 2), (key1315, -1), (key1336, -1), (key1545, -1), (key1654, -1), (key1771, -1), (key1812, -1), (key1442, -1), (key1464, -1), (key1591, -1), (key1665, -1), (key1796, -1), (key1823, -1), (key1324, 1), (key1343, 1), (key1554, 1), (key1657, 1), (key1778, 1), (key1815, 1)]

theorem rawRowCheck4079 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form12 = rawRow4079 := by decide +kernel

def row4079 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4079 : row4079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4079 := by decide +kernel

theorem rowEval4079 (x : Key → ℝ) : Integer.Sparse.eval row4079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4079, Integer.Sparse.eval_collectBalanced, rawRowCheck4079]

def rawRow4080 : Integer.Sparse Key := [(key1657, -2), (key1622, -2), (key1815, -2), (key1454, 1), (key1423, 1), (key1654, 1), (key1572, 1), (key1812, 1), (key1787, 1), (key1665, 2), (key1631, 2), (key1823, 2), (key1336, -1), (key1315, -1), (key1654, -1), (key1545, -1), (key1812, -1), (key1771, -1), (key1464, -1), (key1442, -1), (key1665, -1), (key1591, -1), (key1823, -1), (key1796, -1), (key1343, 1), (key1324, 1), (key1657, 1), (key1554, 1), (key1815, 1), (key1778, 1)]

theorem rawRowCheck4080 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form12 = rawRow4080 := by decide +kernel

def row4080 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4080 : row4080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4080 := by decide +kernel

theorem rowEval4080 (x : Key → ℝ) : Integer.Sparse.eval row4080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4080, Integer.Sparse.eval_collectBalanced, rawRowCheck4080]

def rawRow4081 : Integer.Sparse Key := [(key1622, -2), (key1815, -2), (key1657, -2), (key1572, 1), (key1787, 1), (key1423, 1), (key1812, 1), (key1454, 1), (key1654, 1), (key1631, 2), (key1823, 2), (key1665, 2), (key1545, -1), (key1771, -1), (key1315, -1), (key1812, -1), (key1336, -1), (key1654, -1), (key1591, -1), (key1796, -1), (key1442, -1), (key1823, -1), (key1464, -1), (key1665, -1), (key1554, 1), (key1778, 1), (key1324, 1), (key1815, 1), (key1343, 1), (key1657, 1)]

theorem rawRowCheck4081 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form12 = rawRow4081 := by decide +kernel

def row4081 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4081 : row4081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4081 := by decide +kernel

theorem rowEval4081 (x : Key → ℝ) : Integer.Sparse.eval row4081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4081, Integer.Sparse.eval_collectBalanced, rawRowCheck4081]

def rawRow4082 : Integer.Sparse Key := [(key1815, -2), (key1622, -2), (key1657, -2), (key1787, 1), (key1572, 1), (key1812, 1), (key1423, 1), (key1654, 1), (key1454, 1), (key1823, 2), (key1631, 2), (key1665, 2), (key1771, -1), (key1545, -1), (key1812, -1), (key1315, -1), (key1654, -1), (key1336, -1), (key1796, -1), (key1591, -1), (key1823, -1), (key1442, -1), (key1665, -1), (key1464, -1), (key1778, 1), (key1554, 1), (key1815, 1), (key1324, 1), (key1657, 1), (key1343, 1)]

theorem rawRowCheck4082 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form12 = rawRow4082 := by decide +kernel

def row4082 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4082 : row4082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4082 := by decide +kernel

theorem rowEval4082 (x : Key → ℝ) : Integer.Sparse.eval row4082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4082, Integer.Sparse.eval_collectBalanced, rawRowCheck4082]

def rawRow4083 : Integer.Sparse Key := [(key1657, -2), (key1815, -2), (key1622, -2), (key1654, 1), (key1812, 1), (key1454, 1), (key1787, 1), (key1423, 1), (key1572, 1), (key1665, 2), (key1823, 2), (key1631, 2), (key1654, -1), (key1812, -1), (key1336, -1), (key1771, -1), (key1315, -1), (key1545, -1), (key1665, -1), (key1823, -1), (key1464, -1), (key1796, -1), (key1442, -1), (key1591, -1), (key1657, 1), (key1815, 1), (key1343, 1), (key1778, 1), (key1324, 1), (key1554, 1)]

theorem rawRowCheck4083 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form12 = rawRow4083 := by decide +kernel

def row4083 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4083 : row4083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4083 := by decide +kernel

theorem rowEval4083 (x : Key → ℝ) : Integer.Sparse.eval row4083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4083, Integer.Sparse.eval_collectBalanced, rawRowCheck4083]

def rawRow4084 : Integer.Sparse Key := [(key1815, -2), (key1657, -2), (key1622, -2), (key1812, 1), (key1654, 1), (key1787, 1), (key1454, 1), (key1572, 1), (key1423, 1), (key1823, 2), (key1665, 2), (key1631, 2), (key1812, -1), (key1654, -1), (key1771, -1), (key1336, -1), (key1545, -1), (key1315, -1), (key1823, -1), (key1665, -1), (key1796, -1), (key1464, -1), (key1591, -1), (key1442, -1), (key1815, 1), (key1657, 1), (key1778, 1), (key1343, 1), (key1554, 1), (key1324, 1)]

theorem rawRowCheck4084 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form12 = rawRow4084 := by decide +kernel

def row4084 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4084 : row4084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4084 := by decide +kernel

theorem rowEval4084 (x : Key → ℝ) : Integer.Sparse.eval row4084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4084, Integer.Sparse.eval_collectBalanced, rawRowCheck4084]

def rawRow4085 : Integer.Sparse Key := [(key1591, -2), (key1591, -2), (key1796, -2), (key1442, 1), (key1442, 1), (key1631, 1), (key1631, 1), (key1823, 1), (key1823, 1), (key1554, 2), (key1554, 2), (key1778, 2), (key1324, -1), (key1324, -1), (key1622, -1), (key1622, -1), (key1815, -1), (key1815, -1), (key1390, -1), (key1390, -1), (key1545, -1), (key1545, -1), (key1771, -1), (key1771, -1), (key1295, 1), (key1295, 1), (key1572, 1), (key1572, 1), (key1787, 1), (key1787, 1)]

theorem rawRowCheck4085 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form12 = rawRow4085 := by decide +kernel

def row4085 : Integer.Sparse Key := [(key1295, 2), (key1324, -2), (key1390, -2), (key1442, 2), (key1545, -2), (key1554, 4), (key1572, 2), (key1591, -4), (key1622, -2), (key1631, 2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

theorem rowCheck4085 : row4085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4085 := by decide +kernel

theorem rowEval4085 (x : Key → ℝ) : Integer.Sparse.eval row4085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4085, Integer.Sparse.eval_collectBalanced, rawRowCheck4085]

def rawRow4086 : Integer.Sparse Key := [(key1591, -2), (key1796, -2), (key1591, -2), (key1631, 1), (key1823, 1), (key1442, 1), (key1823, 1), (key1442, 1), (key1631, 1), (key1554, 2), (key1778, 2), (key1554, 2), (key1622, -1), (key1815, -1), (key1324, -1), (key1815, -1), (key1324, -1), (key1622, -1), (key1545, -1), (key1771, -1), (key1390, -1), (key1771, -1), (key1390, -1), (key1545, -1), (key1572, 1), (key1787, 1), (key1295, 1), (key1787, 1), (key1295, 1), (key1572, 1)]

theorem rawRowCheck4086 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form12 = rawRow4086 := by decide +kernel

def row4086 : Integer.Sparse Key := [(key1295, 2), (key1324, -2), (key1390, -2), (key1442, 2), (key1545, -2), (key1554, 4), (key1572, 2), (key1591, -4), (key1622, -2), (key1631, 2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

theorem rowCheck4086 : row4086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4086 := by decide +kernel

theorem rowEval4086 (x : Key → ℝ) : Integer.Sparse.eval row4086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4086, Integer.Sparse.eval_collectBalanced, rawRowCheck4086]

def rawRow4087 : Integer.Sparse Key := [(key1796, -2), (key1591, -2), (key1591, -2), (key1823, 1), (key1631, 1), (key1823, 1), (key1442, 1), (key1631, 1), (key1442, 1), (key1778, 2), (key1554, 2), (key1554, 2), (key1815, -1), (key1622, -1), (key1815, -1), (key1324, -1), (key1622, -1), (key1324, -1), (key1771, -1), (key1545, -1), (key1771, -1), (key1390, -1), (key1545, -1), (key1390, -1), (key1787, 1), (key1572, 1), (key1787, 1), (key1295, 1), (key1572, 1), (key1295, 1)]

theorem rawRowCheck4087 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form12 = rawRow4087 := by decide +kernel

def row4087 : Integer.Sparse Key := [(key1295, 2), (key1324, -2), (key1390, -2), (key1442, 2), (key1545, -2), (key1554, 4), (key1572, 2), (key1591, -4), (key1622, -2), (key1631, 2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

theorem rowCheck4087 : row4087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4087 := by decide +kernel

theorem rowEval4087 (x : Key → ℝ) : Integer.Sparse.eval row4087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4087, Integer.Sparse.eval_collectBalanced, rawRowCheck4087]

def rawRow4088 : Integer.Sparse Key := [(key1631, -2), (key1665, -2), (key1823, -2), (key1442, 1), (key1464, 1), (key1591, 1), (key1665, 1), (key1796, 1), (key1823, 1), (key1622, 2), (key1657, 2), (key1815, 2), (key1324, -1), (key1343, -1), (key1554, -1), (key1657, -1), (key1778, -1), (key1815, -1), (key1423, -1), (key1454, -1), (key1572, -1), (key1654, -1), (key1787, -1), (key1812, -1), (key1315, 1), (key1336, 1), (key1545, 1), (key1654, 1), (key1771, 1), (key1812, 1)]

theorem rawRowCheck4088 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form12 = rawRow4088 := by decide +kernel

def row4088 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4088 : row4088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4088 := by decide +kernel

theorem rowEval4088 (x : Key → ℝ) : Integer.Sparse.eval row4088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4088, Integer.Sparse.eval_collectBalanced, rawRowCheck4088]

def rawRow4089 : Integer.Sparse Key := [(key1665, -2), (key1631, -2), (key1823, -2), (key1464, 1), (key1442, 1), (key1665, 1), (key1591, 1), (key1823, 1), (key1796, 1), (key1657, 2), (key1622, 2), (key1815, 2), (key1343, -1), (key1324, -1), (key1657, -1), (key1554, -1), (key1815, -1), (key1778, -1), (key1454, -1), (key1423, -1), (key1654, -1), (key1572, -1), (key1812, -1), (key1787, -1), (key1336, 1), (key1315, 1), (key1654, 1), (key1545, 1), (key1812, 1), (key1771, 1)]

theorem rawRowCheck4089 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form12 = rawRow4089 := by decide +kernel

def row4089 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4089 : row4089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4089 := by decide +kernel

theorem rowEval4089 (x : Key → ℝ) : Integer.Sparse.eval row4089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4089, Integer.Sparse.eval_collectBalanced, rawRowCheck4089]

def rawRow4090 : Integer.Sparse Key := [(key1631, -2), (key1823, -2), (key1665, -2), (key1591, 1), (key1796, 1), (key1442, 1), (key1823, 1), (key1464, 1), (key1665, 1), (key1622, 2), (key1815, 2), (key1657, 2), (key1554, -1), (key1778, -1), (key1324, -1), (key1815, -1), (key1343, -1), (key1657, -1), (key1572, -1), (key1787, -1), (key1423, -1), (key1812, -1), (key1454, -1), (key1654, -1), (key1545, 1), (key1771, 1), (key1315, 1), (key1812, 1), (key1336, 1), (key1654, 1)]

theorem rawRowCheck4090 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form12 = rawRow4090 := by decide +kernel

def row4090 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4090 : row4090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4090 := by decide +kernel

theorem rowEval4090 (x : Key → ℝ) : Integer.Sparse.eval row4090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4090, Integer.Sparse.eval_collectBalanced, rawRowCheck4090]

def rawRow4091 : Integer.Sparse Key := [(key1823, -2), (key1631, -2), (key1665, -2), (key1796, 1), (key1591, 1), (key1823, 1), (key1442, 1), (key1665, 1), (key1464, 1), (key1815, 2), (key1622, 2), (key1657, 2), (key1778, -1), (key1554, -1), (key1815, -1), (key1324, -1), (key1657, -1), (key1343, -1), (key1787, -1), (key1572, -1), (key1812, -1), (key1423, -1), (key1654, -1), (key1454, -1), (key1771, 1), (key1545, 1), (key1812, 1), (key1315, 1), (key1654, 1), (key1336, 1)]

theorem rawRowCheck4091 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form12 = rawRow4091 := by decide +kernel

def row4091 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4091 : row4091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4091 := by decide +kernel

theorem rowEval4091 (x : Key → ℝ) : Integer.Sparse.eval row4091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4091, Integer.Sparse.eval_collectBalanced, rawRowCheck4091]

def rawRow4092 : Integer.Sparse Key := [(key1665, -2), (key1823, -2), (key1631, -2), (key1665, 1), (key1823, 1), (key1464, 1), (key1796, 1), (key1442, 1), (key1591, 1), (key1657, 2), (key1815, 2), (key1622, 2), (key1657, -1), (key1815, -1), (key1343, -1), (key1778, -1), (key1324, -1), (key1554, -1), (key1654, -1), (key1812, -1), (key1454, -1), (key1787, -1), (key1423, -1), (key1572, -1), (key1654, 1), (key1812, 1), (key1336, 1), (key1771, 1), (key1315, 1), (key1545, 1)]

theorem rawRowCheck4092 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form12 = rawRow4092 := by decide +kernel

def row4092 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4092 : row4092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4092 := by decide +kernel

theorem rowEval4092 (x : Key → ℝ) : Integer.Sparse.eval row4092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4092, Integer.Sparse.eval_collectBalanced, rawRowCheck4092]

def rawRow4093 : Integer.Sparse Key := [(key1823, -2), (key1665, -2), (key1631, -2), (key1823, 1), (key1665, 1), (key1796, 1), (key1464, 1), (key1591, 1), (key1442, 1), (key1815, 2), (key1657, 2), (key1622, 2), (key1815, -1), (key1657, -1), (key1778, -1), (key1343, -1), (key1554, -1), (key1324, -1), (key1812, -1), (key1654, -1), (key1787, -1), (key1454, -1), (key1572, -1), (key1423, -1), (key1812, 1), (key1654, 1), (key1771, 1), (key1336, 1), (key1545, 1), (key1315, 1)]

theorem rawRowCheck4093 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form12 = rawRow4093 := by decide +kernel

def row4093 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4093 : row4093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4093 := by decide +kernel

theorem rowEval4093 (x : Key → ℝ) : Integer.Sparse.eval row4093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4093, Integer.Sparse.eval_collectBalanced, rawRowCheck4093]

def rawRow4094 : Integer.Sparse Key := [(key830, -2), (key831, -2), (key840, -2), (key831, 6), (key924, 2), (key925, 2), (key935, 2), (key747, -2), (key925, -2), (key960, -2), (key928, -6), (key751, 2), (key928, 2), (key962, 2)]

theorem rawRowCheck4094 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form13 = rawRow4094 := by decide +kernel

def row4094 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

theorem rowCheck4094 : row4094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4094 := by decide +kernel

theorem rowEval4094 (x : Key → ℝ) : Integer.Sparse.eval row4094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4094, Integer.Sparse.eval_collectBalanced, rawRowCheck4094]

def rawRow4095 : Integer.Sparse Key := [(key831, -2), (key830, -2), (key840, -2), (key831, 6), (key925, 2), (key924, 2), (key935, 2), (key747, -2), (key960, -2), (key925, -2), (key928, -6), (key751, 2), (key962, 2), (key928, 2)]

theorem rawRowCheck4095 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form13 = rawRow4095 := by decide +kernel

def row4095 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

theorem rowCheck4095 : row4095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4095 := by decide +kernel

theorem rowEval4095 (x : Key → ℝ) : Integer.Sparse.eval row4095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4095, Integer.Sparse.eval_collectBalanced, rawRowCheck4095]

end MUB6.Certificate.GramRows

end OAI
