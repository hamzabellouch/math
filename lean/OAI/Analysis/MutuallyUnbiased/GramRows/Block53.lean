import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3712 : Integer.Sparse Key := [(key1790, -2), (key1790, -2), (key1302, -2), (key1788, 1), (key1573, 1), (key1788, 1), (key1296, 1), (key1573, 1), (key1296, 1), (key1817, 2), (key1817, 2), (key1329, 2), (key1813, -1), (key1424, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1316, -1), (key1841, -1), (key1659, -1), (key1841, -1), (key1345, -1), (key1659, -1), (key1345, -1), (key1839, 1), (key1457, 1), (key1839, 1), (key1339, 1), (key1457, 1), (key1339, 1)]

theorem rawRowCheck3712 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form0 = rawRow3712 := by decide +kernel

def row3712 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1457, 2), (key1573, 2), (key1659, -2), (key1788, 2), (key1790, -4), (key1813, -2), (key1817, 4), (key1839, 2), (key1841, -2)]

theorem rowCheck3712 : row3712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3712 := by decide +kernel

theorem rowEval3712 (x : Key → ℝ) : Integer.Sparse.eval row3712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3712, Integer.Sparse.eval_collectBalanced, rawRowCheck3712]

def rawRow3713 : Integer.Sparse Key := [(key1316, -2), (key1813, -2), (key1825, -2), (key1337, 1), (key1339, 1), (key1655, 1), (key1667, 1), (key1839, 1), (key1844, 1), (key1296, 2), (key1788, 2), (key1798, 2), (key1337, -1), (key1345, -1), (key1455, -1), (key1466, -1), (key1841, -1), (key1844, -1), (key1296, -1), (key1302, -1), (key1573, -1), (key1596, -1), (key1790, -1), (key1798, -1), (key1316, 1), (key1329, 1), (key1424, 1), (key1447, 1), (key1817, 1), (key1825, 1)]

theorem rawRowCheck3713 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form0 = rawRow3713 := by decide +kernel

def row3713 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck3713 : row3713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3713 := by decide +kernel

theorem rowEval3713 (x : Key → ℝ) : Integer.Sparse.eval row3713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck3713, Integer.Sparse.eval_collectBalanced, rawRowCheck3713]

def rawRow3714 : Integer.Sparse Key := [(key1316, -2), (key1825, -2), (key1813, -2), (key1339, 1), (key1337, 1), (key1667, 1), (key1655, 1), (key1844, 1), (key1839, 1), (key1296, 2), (key1798, 2), (key1788, 2), (key1345, -1), (key1337, -1), (key1466, -1), (key1455, -1), (key1844, -1), (key1841, -1), (key1302, -1), (key1296, -1), (key1596, -1), (key1573, -1), (key1798, -1), (key1790, -1), (key1329, 1), (key1316, 1), (key1447, 1), (key1424, 1), (key1825, 1), (key1817, 1)]

theorem rawRowCheck3714 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form0 = rawRow3714 := by decide +kernel

def row3714 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck3714 : row3714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3714 := by decide +kernel

theorem rowEval3714 (x : Key → ℝ) : Integer.Sparse.eval row3714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3714, Integer.Sparse.eval_collectBalanced, rawRowCheck3714]

def rawRow3715 : Integer.Sparse Key := [(key1813, -2), (key1316, -2), (key1825, -2), (key1655, 1), (key1839, 1), (key1337, 1), (key1844, 1), (key1339, 1), (key1667, 1), (key1788, 2), (key1296, 2), (key1798, 2), (key1455, -1), (key1841, -1), (key1337, -1), (key1844, -1), (key1345, -1), (key1466, -1), (key1573, -1), (key1790, -1), (key1296, -1), (key1798, -1), (key1302, -1), (key1596, -1), (key1424, 1), (key1817, 1), (key1316, 1), (key1825, 1), (key1329, 1), (key1447, 1)]

theorem rawRowCheck3715 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form0 = rawRow3715 := by decide +kernel

def row3715 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck3715 : row3715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3715 := by decide +kernel

theorem rowEval3715 (x : Key → ℝ) : Integer.Sparse.eval row3715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck3715, Integer.Sparse.eval_collectBalanced, rawRowCheck3715]

def rawRow3716 : Integer.Sparse Key := [(key1813, -2), (key1825, -2), (key1316, -2), (key1839, 1), (key1655, 1), (key1844, 1), (key1337, 1), (key1667, 1), (key1339, 1), (key1788, 2), (key1798, 2), (key1296, 2), (key1841, -1), (key1455, -1), (key1844, -1), (key1337, -1), (key1466, -1), (key1345, -1), (key1790, -1), (key1573, -1), (key1798, -1), (key1296, -1), (key1596, -1), (key1302, -1), (key1817, 1), (key1424, 1), (key1825, 1), (key1316, 1), (key1447, 1), (key1329, 1)]

theorem rawRowCheck3716 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form0 = rawRow3716 := by decide +kernel

def row3716 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck3716 : row3716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3716 := by decide +kernel

theorem rowEval3716 (x : Key → ℝ) : Integer.Sparse.eval row3716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3716, Integer.Sparse.eval_collectBalanced, rawRowCheck3716]

def rawRow3717 : Integer.Sparse Key := [(key1825, -2), (key1316, -2), (key1813, -2), (key1667, 1), (key1844, 1), (key1339, 1), (key1839, 1), (key1337, 1), (key1655, 1), (key1798, 2), (key1296, 2), (key1788, 2), (key1466, -1), (key1844, -1), (key1345, -1), (key1841, -1), (key1337, -1), (key1455, -1), (key1596, -1), (key1798, -1), (key1302, -1), (key1790, -1), (key1296, -1), (key1573, -1), (key1447, 1), (key1825, 1), (key1329, 1), (key1817, 1), (key1316, 1), (key1424, 1)]

theorem rawRowCheck3717 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form0 = rawRow3717 := by decide +kernel

def row3717 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck3717 : row3717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3717 := by decide +kernel

theorem rowEval3717 (x : Key → ℝ) : Integer.Sparse.eval row3717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3717, Integer.Sparse.eval_collectBalanced, rawRowCheck3717]

def rawRow3718 : Integer.Sparse Key := [(key1825, -2), (key1813, -2), (key1316, -2), (key1844, 1), (key1667, 1), (key1839, 1), (key1339, 1), (key1655, 1), (key1337, 1), (key1798, 2), (key1788, 2), (key1296, 2), (key1844, -1), (key1466, -1), (key1841, -1), (key1345, -1), (key1455, -1), (key1337, -1), (key1798, -1), (key1596, -1), (key1790, -1), (key1302, -1), (key1573, -1), (key1296, -1), (key1825, 1), (key1447, 1), (key1817, 1), (key1329, 1), (key1424, 1), (key1316, 1)]

theorem rawRowCheck3718 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form0 = rawRow3718 := by decide +kernel

def row3718 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck3718 : row3718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3718 := by decide +kernel

theorem rowEval3718 (x : Key → ℝ) : Integer.Sparse.eval row3718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3718, Integer.Sparse.eval_collectBalanced, rawRowCheck3718]

def rawRow3719 : Integer.Sparse Key := [(key1339, -2), (key1774, -2), (key1839, -2), (key1316, 1), (key1337, 1), (key1546, 1), (key1655, 1), (key1772, 1), (key1813, 1), (key1345, 2), (key1780, 2), (key1841, 2), (key1296, -1), (key1337, -1), (key1391, -1), (key1455, -1), (key1772, -1), (key1788, -1), (key1329, -1), (key1345, -1), (key1559, -1), (key1659, -1), (key1780, -1), (key1817, -1), (key1302, 1), (key1339, 1), (key1397, 1), (key1457, 1), (key1774, 1), (key1790, 1)]

theorem rawRowCheck3719 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form0 = rawRow3719 := by decide +kernel

def row3719 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

theorem rowCheck3719 : row3719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3719 := by decide +kernel

theorem rowEval3719 (x : Key → ℝ) : Integer.Sparse.eval row3719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3719, Integer.Sparse.eval_collectBalanced, rawRowCheck3719]

def rawRow3720 : Integer.Sparse Key := [(key1339, -2), (key1839, -2), (key1774, -2), (key1337, 1), (key1316, 1), (key1655, 1), (key1546, 1), (key1813, 1), (key1772, 1), (key1345, 2), (key1841, 2), (key1780, 2), (key1337, -1), (key1296, -1), (key1455, -1), (key1391, -1), (key1788, -1), (key1772, -1), (key1345, -1), (key1329, -1), (key1659, -1), (key1559, -1), (key1817, -1), (key1780, -1), (key1339, 1), (key1302, 1), (key1457, 1), (key1397, 1), (key1790, 1), (key1774, 1)]

theorem rawRowCheck3720 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form0 = rawRow3720 := by decide +kernel

def row3720 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

theorem rowCheck3720 : row3720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3720 := by decide +kernel

theorem rowEval3720 (x : Key → ℝ) : Integer.Sparse.eval row3720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck3720, Integer.Sparse.eval_collectBalanced, rawRowCheck3720]

def rawRow3721 : Integer.Sparse Key := [(key1774, -2), (key1339, -2), (key1839, -2), (key1546, 1), (key1772, 1), (key1316, 1), (key1813, 1), (key1337, 1), (key1655, 1), (key1780, 2), (key1345, 2), (key1841, 2), (key1391, -1), (key1772, -1), (key1296, -1), (key1788, -1), (key1337, -1), (key1455, -1), (key1559, -1), (key1780, -1), (key1329, -1), (key1817, -1), (key1345, -1), (key1659, -1), (key1397, 1), (key1774, 1), (key1302, 1), (key1790, 1), (key1339, 1), (key1457, 1)]

theorem rawRowCheck3721 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form0 = rawRow3721 := by decide +kernel

def row3721 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

theorem rowCheck3721 : row3721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3721 := by decide +kernel

theorem rowEval3721 (x : Key → ℝ) : Integer.Sparse.eval row3721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3721, Integer.Sparse.eval_collectBalanced, rawRowCheck3721]

def rawRow3722 : Integer.Sparse Key := [(key1774, -2), (key1839, -2), (key1339, -2), (key1772, 1), (key1546, 1), (key1813, 1), (key1316, 1), (key1655, 1), (key1337, 1), (key1780, 2), (key1841, 2), (key1345, 2), (key1772, -1), (key1391, -1), (key1788, -1), (key1296, -1), (key1455, -1), (key1337, -1), (key1780, -1), (key1559, -1), (key1817, -1), (key1329, -1), (key1659, -1), (key1345, -1), (key1774, 1), (key1397, 1), (key1790, 1), (key1302, 1), (key1457, 1), (key1339, 1)]

theorem rawRowCheck3722 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form0 = rawRow3722 := by decide +kernel

def row3722 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

theorem rowCheck3722 : row3722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3722 := by decide +kernel

theorem rowEval3722 (x : Key → ℝ) : Integer.Sparse.eval row3722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3722, Integer.Sparse.eval_collectBalanced, rawRowCheck3722]

def rawRow3723 : Integer.Sparse Key := [(key1839, -2), (key1339, -2), (key1774, -2), (key1655, 1), (key1813, 1), (key1337, 1), (key1772, 1), (key1316, 1), (key1546, 1), (key1841, 2), (key1345, 2), (key1780, 2), (key1455, -1), (key1788, -1), (key1337, -1), (key1772, -1), (key1296, -1), (key1391, -1), (key1659, -1), (key1817, -1), (key1345, -1), (key1780, -1), (key1329, -1), (key1559, -1), (key1457, 1), (key1790, 1), (key1339, 1), (key1774, 1), (key1302, 1), (key1397, 1)]

theorem rawRowCheck3723 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form0 = rawRow3723 := by decide +kernel

def row3723 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

theorem rowCheck3723 : row3723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3723 := by decide +kernel

theorem rowEval3723 (x : Key → ℝ) : Integer.Sparse.eval row3723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck3723, Integer.Sparse.eval_collectBalanced, rawRowCheck3723]

def rawRow3724 : Integer.Sparse Key := [(key1839, -2), (key1774, -2), (key1339, -2), (key1813, 1), (key1655, 1), (key1772, 1), (key1337, 1), (key1546, 1), (key1316, 1), (key1841, 2), (key1780, 2), (key1345, 2), (key1788, -1), (key1455, -1), (key1772, -1), (key1337, -1), (key1391, -1), (key1296, -1), (key1817, -1), (key1659, -1), (key1780, -1), (key1345, -1), (key1559, -1), (key1329, -1), (key1790, 1), (key1457, 1), (key1774, 1), (key1339, 1), (key1397, 1), (key1302, 1)]

theorem rawRowCheck3724 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form0 = rawRow3724 := by decide +kernel

def row3724 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

theorem rowCheck3724 : row3724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3724 := by decide +kernel

theorem rowEval3724 (x : Key → ℝ) : Integer.Sparse.eval row3724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3724, Integer.Sparse.eval_collectBalanced, rawRowCheck3724]

def rawRow3725 : Integer.Sparse Key := [(key1329, -2), (key1817, -2), (key1817, -2), (key1345, 1), (key1345, 1), (key1659, 1), (key1659, 1), (key1841, 1), (key1841, 1), (key1302, 2), (key1790, 2), (key1790, 2), (key1339, -1), (key1339, -1), (key1457, -1), (key1457, -1), (key1839, -1), (key1839, -1), (key1296, -1), (key1296, -1), (key1573, -1), (key1573, -1), (key1788, -1), (key1788, -1), (key1316, 1), (key1316, 1), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1)]

theorem rawRowCheck3725 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form0 = rawRow3725 := by decide +kernel

def row3725 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1424, 2), (key1457, -2), (key1573, -2), (key1659, 2), (key1788, -2), (key1790, 4), (key1813, 2), (key1817, -4), (key1839, -2), (key1841, 2)]

theorem rowCheck3725 : row3725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3725 := by decide +kernel

theorem rowEval3725 (x : Key → ℝ) : Integer.Sparse.eval row3725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3725, Integer.Sparse.eval_collectBalanced, rawRowCheck3725]

def rawRow3726 : Integer.Sparse Key := [(key1817, -2), (key1329, -2), (key1817, -2), (key1659, 1), (key1841, 1), (key1345, 1), (key1841, 1), (key1345, 1), (key1659, 1), (key1790, 2), (key1302, 2), (key1790, 2), (key1457, -1), (key1839, -1), (key1339, -1), (key1839, -1), (key1339, -1), (key1457, -1), (key1573, -1), (key1788, -1), (key1296, -1), (key1788, -1), (key1296, -1), (key1573, -1), (key1424, 1), (key1813, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1424, 1)]

theorem rawRowCheck3726 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form0 = rawRow3726 := by decide +kernel

def row3726 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1424, 2), (key1457, -2), (key1573, -2), (key1659, 2), (key1788, -2), (key1790, 4), (key1813, 2), (key1817, -4), (key1839, -2), (key1841, 2)]

theorem rowCheck3726 : row3726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3726 := by decide +kernel

theorem rowEval3726 (x : Key → ℝ) : Integer.Sparse.eval row3726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3726, Integer.Sparse.eval_collectBalanced, rawRowCheck3726]

def rawRow3727 : Integer.Sparse Key := [(key1817, -2), (key1817, -2), (key1329, -2), (key1841, 1), (key1659, 1), (key1841, 1), (key1345, 1), (key1659, 1), (key1345, 1), (key1790, 2), (key1790, 2), (key1302, 2), (key1839, -1), (key1457, -1), (key1839, -1), (key1339, -1), (key1457, -1), (key1339, -1), (key1788, -1), (key1573, -1), (key1788, -1), (key1296, -1), (key1573, -1), (key1296, -1), (key1813, 1), (key1424, 1), (key1813, 1), (key1316, 1), (key1424, 1), (key1316, 1)]

theorem rawRowCheck3727 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form0 = rawRow3727 := by decide +kernel

def row3727 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1424, 2), (key1457, -2), (key1573, -2), (key1659, 2), (key1788, -2), (key1790, 4), (key1813, 2), (key1817, -4), (key1839, -2), (key1841, 2)]

theorem rowCheck3727 : row3727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3727 := by decide +kernel

theorem rowEval3727 (x : Key → ℝ) : Integer.Sparse.eval row3727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3727, Integer.Sparse.eval_collectBalanced, rawRowCheck3727]

def rawRow3728 : Integer.Sparse Key := [(key1345, -2), (key1780, -2), (key1841, -2), (key1329, 1), (key1345, 1), (key1559, 1), (key1659, 1), (key1780, 1), (key1817, 1), (key1339, 2), (key1774, 2), (key1839, 2), (key1302, -1), (key1339, -1), (key1397, -1), (key1457, -1), (key1774, -1), (key1790, -1), (key1316, -1), (key1337, -1), (key1546, -1), (key1655, -1), (key1772, -1), (key1813, -1), (key1296, 1), (key1337, 1), (key1391, 1), (key1455, 1), (key1772, 1), (key1788, 1)]

theorem rawRowCheck3728 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form0 = rawRow3728 := by decide +kernel

def row3728 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

theorem rowCheck3728 : row3728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3728 := by decide +kernel

theorem rowEval3728 (x : Key → ℝ) : Integer.Sparse.eval row3728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3728, Integer.Sparse.eval_collectBalanced, rawRowCheck3728]

def rawRow3729 : Integer.Sparse Key := [(key1345, -2), (key1841, -2), (key1780, -2), (key1345, 1), (key1329, 1), (key1659, 1), (key1559, 1), (key1817, 1), (key1780, 1), (key1339, 2), (key1839, 2), (key1774, 2), (key1339, -1), (key1302, -1), (key1457, -1), (key1397, -1), (key1790, -1), (key1774, -1), (key1337, -1), (key1316, -1), (key1655, -1), (key1546, -1), (key1813, -1), (key1772, -1), (key1337, 1), (key1296, 1), (key1455, 1), (key1391, 1), (key1788, 1), (key1772, 1)]

theorem rawRowCheck3729 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form0 = rawRow3729 := by decide +kernel

def row3729 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

theorem rowCheck3729 : row3729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3729 := by decide +kernel

theorem rowEval3729 (x : Key → ℝ) : Integer.Sparse.eval row3729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck3729, Integer.Sparse.eval_collectBalanced, rawRowCheck3729]

def rawRow3730 : Integer.Sparse Key := [(key1780, -2), (key1345, -2), (key1841, -2), (key1559, 1), (key1780, 1), (key1329, 1), (key1817, 1), (key1345, 1), (key1659, 1), (key1774, 2), (key1339, 2), (key1839, 2), (key1397, -1), (key1774, -1), (key1302, -1), (key1790, -1), (key1339, -1), (key1457, -1), (key1546, -1), (key1772, -1), (key1316, -1), (key1813, -1), (key1337, -1), (key1655, -1), (key1391, 1), (key1772, 1), (key1296, 1), (key1788, 1), (key1337, 1), (key1455, 1)]

theorem rawRowCheck3730 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form0 = rawRow3730 := by decide +kernel

def row3730 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

theorem rowCheck3730 : row3730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3730 := by decide +kernel

theorem rowEval3730 (x : Key → ℝ) : Integer.Sparse.eval row3730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3730, Integer.Sparse.eval_collectBalanced, rawRowCheck3730]

def rawRow3731 : Integer.Sparse Key := [(key1780, -2), (key1841, -2), (key1345, -2), (key1780, 1), (key1559, 1), (key1817, 1), (key1329, 1), (key1659, 1), (key1345, 1), (key1774, 2), (key1839, 2), (key1339, 2), (key1774, -1), (key1397, -1), (key1790, -1), (key1302, -1), (key1457, -1), (key1339, -1), (key1772, -1), (key1546, -1), (key1813, -1), (key1316, -1), (key1655, -1), (key1337, -1), (key1772, 1), (key1391, 1), (key1788, 1), (key1296, 1), (key1455, 1), (key1337, 1)]

theorem rawRowCheck3731 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form0 = rawRow3731 := by decide +kernel

def row3731 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

theorem rowCheck3731 : row3731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3731 := by decide +kernel

theorem rowEval3731 (x : Key → ℝ) : Integer.Sparse.eval row3731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3731, Integer.Sparse.eval_collectBalanced, rawRowCheck3731]

def rawRow3732 : Integer.Sparse Key := [(key1841, -2), (key1345, -2), (key1780, -2), (key1659, 1), (key1817, 1), (key1345, 1), (key1780, 1), (key1329, 1), (key1559, 1), (key1839, 2), (key1339, 2), (key1774, 2), (key1457, -1), (key1790, -1), (key1339, -1), (key1774, -1), (key1302, -1), (key1397, -1), (key1655, -1), (key1813, -1), (key1337, -1), (key1772, -1), (key1316, -1), (key1546, -1), (key1455, 1), (key1788, 1), (key1337, 1), (key1772, 1), (key1296, 1), (key1391, 1)]

theorem rawRowCheck3732 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form0 = rawRow3732 := by decide +kernel

def row3732 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

theorem rowCheck3732 : row3732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3732 := by decide +kernel

theorem rowEval3732 (x : Key → ℝ) : Integer.Sparse.eval row3732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck3732, Integer.Sparse.eval_collectBalanced, rawRowCheck3732]

def rawRow3733 : Integer.Sparse Key := [(key1841, -2), (key1780, -2), (key1345, -2), (key1817, 1), (key1659, 1), (key1780, 1), (key1345, 1), (key1559, 1), (key1329, 1), (key1839, 2), (key1774, 2), (key1339, 2), (key1790, -1), (key1457, -1), (key1774, -1), (key1339, -1), (key1397, -1), (key1302, -1), (key1813, -1), (key1655, -1), (key1772, -1), (key1337, -1), (key1546, -1), (key1316, -1), (key1788, 1), (key1455, 1), (key1772, 1), (key1337, 1), (key1391, 1), (key1296, 1)]

theorem rawRowCheck3733 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form0 = rawRow3733 := by decide +kernel

def row3733 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

theorem rowCheck3733 : row3733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3733 := by decide +kernel

theorem rowEval3733 (x : Key → ℝ) : Integer.Sparse.eval row3733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3733, Integer.Sparse.eval_collectBalanced, rawRowCheck3733]

def rawRow3734 : Integer.Sparse Key := [(key384, -6), (key301, 2), (key384, 2), (key393, 2), (key405, 6), (key235, -2), (key405, -2), (key416, -2), (key315, -2), (key434, -2), (key438, -2), (key247, 2), (key434, 2), (key448, 2)]

theorem rawRowCheck3734 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form1 = rawRow3734 := by decide +kernel

def row3734 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

theorem rowCheck3734 : row3734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3734 := by decide +kernel

theorem rowEval3734 (x : Key → ℝ) : Integer.Sparse.eval row3734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3734, Integer.Sparse.eval_collectBalanced, rawRowCheck3734]

def rawRow3735 : Integer.Sparse Key := [(key384, -6), (key301, 2), (key393, 2), (key384, 2), (key405, 6), (key235, -2), (key416, -2), (key405, -2), (key315, -2), (key438, -2), (key434, -2), (key247, 2), (key448, 2), (key434, 2)]

theorem rawRowCheck3735 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form1 = rawRow3735 := by decide +kernel

def row3735 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

theorem rowCheck3735 : row3735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3735 := by decide +kernel

theorem rowEval3735 (x : Key → ℝ) : Integer.Sparse.eval row3735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3735, Integer.Sparse.eval_collectBalanced, rawRowCheck3735]

def rawRow3736 : Integer.Sparse Key := [(key384, -6), (key384, 2), (key301, 2), (key393, 2), (key405, 6), (key405, -2), (key235, -2), (key416, -2), (key434, -2), (key315, -2), (key438, -2), (key434, 2), (key247, 2), (key448, 2)]

theorem rawRowCheck3736 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form1 = rawRow3736 := by decide +kernel

def row3736 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

theorem rowCheck3736 : row3736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3736 := by decide +kernel

theorem rowEval3736 (x : Key → ℝ) : Integer.Sparse.eval row3736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3736, Integer.Sparse.eval_collectBalanced, rawRowCheck3736]

def rawRow3737 : Integer.Sparse Key := [(key384, -6), (key384, 2), (key393, 2), (key301, 2), (key405, 6), (key405, -2), (key416, -2), (key235, -2), (key434, -2), (key438, -2), (key315, -2), (key434, 2), (key448, 2), (key247, 2)]

theorem rawRowCheck3737 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form1 = rawRow3737 := by decide +kernel

def row3737 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

theorem rowCheck3737 : row3737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3737 := by decide +kernel

theorem rowEval3737 (x : Key → ℝ) : Integer.Sparse.eval row3737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3737, Integer.Sparse.eval_collectBalanced, rawRowCheck3737]

def rawRow3738 : Integer.Sparse Key := [(key384, -6), (key393, 2), (key301, 2), (key384, 2), (key405, 6), (key416, -2), (key235, -2), (key405, -2), (key438, -2), (key315, -2), (key434, -2), (key448, 2), (key247, 2), (key434, 2)]

theorem rawRowCheck3738 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form1 = rawRow3738 := by decide +kernel

def row3738 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

theorem rowCheck3738 : row3738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3738 := by decide +kernel

theorem rowEval3738 (x : Key → ℝ) : Integer.Sparse.eval row3738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3738, Integer.Sparse.eval_collectBalanced, rawRowCheck3738]

def rawRow3739 : Integer.Sparse Key := [(key384, -6), (key393, 2), (key384, 2), (key301, 2), (key405, 6), (key416, -2), (key405, -2), (key235, -2), (key438, -2), (key434, -2), (key315, -2), (key448, 2), (key434, 2), (key247, 2)]

theorem rawRowCheck3739 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form1 = rawRow3739 := by decide +kernel

def row3739 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

theorem rowCheck3739 : row3739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3739 := by decide +kernel

theorem rowEval3739 (x : Key → ℝ) : Integer.Sparse.eval row3739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3739, Integer.Sparse.eval_collectBalanced, rawRowCheck3739]

def rawRow3740 : Integer.Sparse Key := [(key393, -6), (key301, 2), (key384, 2), (key384, 2), (key416, 6), (key235, -2), (key405, -2), (key405, -2), (key326, -2), (key448, -2), (key448, -2), (key256, 2), (key438, 2), (key438, 2)]

theorem rawRowCheck3740 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow3740 := by decide +kernel

def row3740 : Integer.Sparse Key := [(key235, -2), (key256, 2), (key301, 2), (key326, -2), (key384, 4), (key393, -6), (key405, -4), (key416, 6), (key438, 4), (key448, -4)]

theorem rowCheck3740 : row3740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3740 := by decide +kernel

theorem rowEval3740 (x : Key → ℝ) : Integer.Sparse.eval row3740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3740, Integer.Sparse.eval_collectBalanced, rawRowCheck3740]

def rawRow3741 : Integer.Sparse Key := [(key393, -6), (key384, 2), (key301, 2), (key384, 2), (key416, 6), (key405, -2), (key235, -2), (key405, -2), (key448, -2), (key326, -2), (key448, -2), (key438, 2), (key256, 2), (key438, 2)]

theorem rawRowCheck3741 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow3741 := by decide +kernel

def row3741 : Integer.Sparse Key := [(key235, -2), (key256, 2), (key301, 2), (key326, -2), (key384, 4), (key393, -6), (key405, -4), (key416, 6), (key438, 4), (key448, -4)]

theorem rowCheck3741 : row3741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3741 := by decide +kernel

theorem rowEval3741 (x : Key → ℝ) : Integer.Sparse.eval row3741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3741, Integer.Sparse.eval_collectBalanced, rawRowCheck3741]

def rawRow3742 : Integer.Sparse Key := [(key393, -6), (key384, 2), (key384, 2), (key301, 2), (key416, 6), (key405, -2), (key405, -2), (key235, -2), (key448, -2), (key448, -2), (key326, -2), (key438, 2), (key438, 2), (key256, 2)]

theorem rawRowCheck3742 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow3742 := by decide +kernel

def row3742 : Integer.Sparse Key := [(key235, -2), (key256, 2), (key301, 2), (key326, -2), (key384, 4), (key393, -6), (key405, -4), (key416, 6), (key438, 4), (key448, -4)]

theorem rowCheck3742 : row3742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3742 := by decide +kernel

theorem rowEval3742 (x : Key → ℝ) : Integer.Sparse.eval row3742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3742, Integer.Sparse.eval_collectBalanced, rawRowCheck3742]

def rawRow3743 : Integer.Sparse Key := [(key405, -6), (key315, 2), (key434, 2), (key438, 2), (key384, 6), (key247, -2), (key434, -2), (key448, -2), (key301, -2), (key384, -2), (key393, -2), (key235, 2), (key405, 2), (key416, 2)]

theorem rawRowCheck3743 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form1 = rawRow3743 := by decide +kernel

def row3743 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

theorem rowCheck3743 : row3743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3743 := by decide +kernel

theorem rowEval3743 (x : Key → ℝ) : Integer.Sparse.eval row3743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3743, Integer.Sparse.eval_collectBalanced, rawRowCheck3743]

def rawRow3744 : Integer.Sparse Key := [(key405, -6), (key315, 2), (key438, 2), (key434, 2), (key384, 6), (key247, -2), (key448, -2), (key434, -2), (key301, -2), (key393, -2), (key384, -2), (key235, 2), (key416, 2), (key405, 2)]

theorem rawRowCheck3744 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form1 = rawRow3744 := by decide +kernel

def row3744 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

theorem rowCheck3744 : row3744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3744 := by decide +kernel

theorem rowEval3744 (x : Key → ℝ) : Integer.Sparse.eval row3744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3744, Integer.Sparse.eval_collectBalanced, rawRowCheck3744]

def rawRow3745 : Integer.Sparse Key := [(key405, -6), (key434, 2), (key315, 2), (key438, 2), (key384, 6), (key434, -2), (key247, -2), (key448, -2), (key384, -2), (key301, -2), (key393, -2), (key405, 2), (key235, 2), (key416, 2)]

theorem rawRowCheck3745 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form1 = rawRow3745 := by decide +kernel

def row3745 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

theorem rowCheck3745 : row3745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3745 := by decide +kernel

theorem rowEval3745 (x : Key → ℝ) : Integer.Sparse.eval row3745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3745, Integer.Sparse.eval_collectBalanced, rawRowCheck3745]

def rawRow3746 : Integer.Sparse Key := [(key405, -6), (key434, 2), (key438, 2), (key315, 2), (key384, 6), (key434, -2), (key448, -2), (key247, -2), (key384, -2), (key393, -2), (key301, -2), (key405, 2), (key416, 2), (key235, 2)]

theorem rawRowCheck3746 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form1 = rawRow3746 := by decide +kernel

def row3746 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

theorem rowCheck3746 : row3746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3746 := by decide +kernel

theorem rowEval3746 (x : Key → ℝ) : Integer.Sparse.eval row3746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3746, Integer.Sparse.eval_collectBalanced, rawRowCheck3746]

def rawRow3747 : Integer.Sparse Key := [(key405, -6), (key438, 2), (key315, 2), (key434, 2), (key384, 6), (key448, -2), (key247, -2), (key434, -2), (key393, -2), (key301, -2), (key384, -2), (key416, 2), (key235, 2), (key405, 2)]

theorem rawRowCheck3747 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form1 = rawRow3747 := by decide +kernel

def row3747 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

theorem rowCheck3747 : row3747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3747 := by decide +kernel

theorem rowEval3747 (x : Key → ℝ) : Integer.Sparse.eval row3747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3747, Integer.Sparse.eval_collectBalanced, rawRowCheck3747]

def rawRow3748 : Integer.Sparse Key := [(key405, -6), (key438, 2), (key434, 2), (key315, 2), (key384, 6), (key448, -2), (key434, -2), (key247, -2), (key393, -2), (key384, -2), (key301, -2), (key416, 2), (key405, 2), (key235, 2)]

theorem rawRowCheck3748 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form1 = rawRow3748 := by decide +kernel

def row3748 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

theorem rowCheck3748 : row3748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3748 := by decide +kernel

theorem rowEval3748 (x : Key → ℝ) : Integer.Sparse.eval row3748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3748, Integer.Sparse.eval_collectBalanced, rawRowCheck3748]

def rawRow3749 : Integer.Sparse Key := [(key438, -6), (key315, 2), (key405, 2), (key434, 2), (key448, 6), (key247, -2), (key384, -2), (key434, -2), (key326, -2), (key416, -2), (key448, -2), (key256, 2), (key393, 2), (key438, 2)]

theorem rawRowCheck3749 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form1 = rawRow3749 := by decide +kernel

def row3749 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

theorem rowCheck3749 : row3749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3749 := by decide +kernel

theorem rowEval3749 (x : Key → ℝ) : Integer.Sparse.eval row3749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3749, Integer.Sparse.eval_collectBalanced, rawRowCheck3749]

def rawRow3750 : Integer.Sparse Key := [(key438, -6), (key315, 2), (key434, 2), (key405, 2), (key448, 6), (key247, -2), (key434, -2), (key384, -2), (key326, -2), (key448, -2), (key416, -2), (key256, 2), (key438, 2), (key393, 2)]

theorem rawRowCheck3750 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form1 = rawRow3750 := by decide +kernel

def row3750 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

theorem rowCheck3750 : row3750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3750 := by decide +kernel

theorem rowEval3750 (x : Key → ℝ) : Integer.Sparse.eval row3750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3750, Integer.Sparse.eval_collectBalanced, rawRowCheck3750]

def rawRow3751 : Integer.Sparse Key := [(key438, -6), (key405, 2), (key315, 2), (key434, 2), (key448, 6), (key384, -2), (key247, -2), (key434, -2), (key416, -2), (key326, -2), (key448, -2), (key393, 2), (key256, 2), (key438, 2)]

theorem rawRowCheck3751 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form1 = rawRow3751 := by decide +kernel

def row3751 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

theorem rowCheck3751 : row3751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3751 := by decide +kernel

theorem rowEval3751 (x : Key → ℝ) : Integer.Sparse.eval row3751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3751, Integer.Sparse.eval_collectBalanced, rawRowCheck3751]

def rawRow3752 : Integer.Sparse Key := [(key438, -6), (key405, 2), (key434, 2), (key315, 2), (key448, 6), (key384, -2), (key434, -2), (key247, -2), (key416, -2), (key448, -2), (key326, -2), (key393, 2), (key438, 2), (key256, 2)]

theorem rawRowCheck3752 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form1 = rawRow3752 := by decide +kernel

def row3752 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

theorem rowCheck3752 : row3752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3752 := by decide +kernel

theorem rowEval3752 (x : Key → ℝ) : Integer.Sparse.eval row3752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3752, Integer.Sparse.eval_collectBalanced, rawRowCheck3752]

def rawRow3753 : Integer.Sparse Key := [(key438, -6), (key434, 2), (key315, 2), (key405, 2), (key448, 6), (key434, -2), (key247, -2), (key384, -2), (key448, -2), (key326, -2), (key416, -2), (key438, 2), (key256, 2), (key393, 2)]

theorem rawRowCheck3753 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form1 = rawRow3753 := by decide +kernel

def row3753 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

theorem rowCheck3753 : row3753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3753 := by decide +kernel

theorem rowEval3753 (x : Key → ℝ) : Integer.Sparse.eval row3753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3753, Integer.Sparse.eval_collectBalanced, rawRowCheck3753]

def rawRow3754 : Integer.Sparse Key := [(key438, -6), (key434, 2), (key405, 2), (key315, 2), (key448, 6), (key434, -2), (key384, -2), (key247, -2), (key448, -2), (key416, -2), (key326, -2), (key438, 2), (key393, 2), (key256, 2)]

theorem rawRowCheck3754 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form1 = rawRow3754 := by decide +kernel

def row3754 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

theorem rowCheck3754 : row3754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3754 := by decide +kernel

theorem rowEval3754 (x : Key → ℝ) : Integer.Sparse.eval row3754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3754, Integer.Sparse.eval_collectBalanced, rawRowCheck3754]

def rawRow3755 : Integer.Sparse Key := [(key416, -6), (key326, 2), (key448, 2), (key448, 2), (key393, 6), (key256, -2), (key438, -2), (key438, -2), (key301, -2), (key384, -2), (key384, -2), (key235, 2), (key405, 2), (key405, 2)]

theorem rawRowCheck3755 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow3755 := by decide +kernel

def row3755 : Integer.Sparse Key := [(key235, 2), (key256, -2), (key301, -2), (key326, 2), (key384, -4), (key393, 6), (key405, 4), (key416, -6), (key438, -4), (key448, 4)]

theorem rowCheck3755 : row3755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3755 := by decide +kernel

theorem rowEval3755 (x : Key → ℝ) : Integer.Sparse.eval row3755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3755, Integer.Sparse.eval_collectBalanced, rawRowCheck3755]

def rawRow3756 : Integer.Sparse Key := [(key416, -6), (key448, 2), (key326, 2), (key448, 2), (key393, 6), (key438, -2), (key256, -2), (key438, -2), (key384, -2), (key301, -2), (key384, -2), (key405, 2), (key235, 2), (key405, 2)]

theorem rawRowCheck3756 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow3756 := by decide +kernel

def row3756 : Integer.Sparse Key := [(key235, 2), (key256, -2), (key301, -2), (key326, 2), (key384, -4), (key393, 6), (key405, 4), (key416, -6), (key438, -4), (key448, 4)]

theorem rowCheck3756 : row3756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3756 := by decide +kernel

theorem rowEval3756 (x : Key → ℝ) : Integer.Sparse.eval row3756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3756, Integer.Sparse.eval_collectBalanced, rawRowCheck3756]

def rawRow3757 : Integer.Sparse Key := [(key416, -6), (key448, 2), (key448, 2), (key326, 2), (key393, 6), (key438, -2), (key438, -2), (key256, -2), (key384, -2), (key384, -2), (key301, -2), (key405, 2), (key405, 2), (key235, 2)]

theorem rawRowCheck3757 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow3757 := by decide +kernel

def row3757 : Integer.Sparse Key := [(key235, 2), (key256, -2), (key301, -2), (key326, 2), (key384, -4), (key393, 6), (key405, 4), (key416, -6), (key438, -4), (key448, 4)]

theorem rowCheck3757 : row3757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3757 := by decide +kernel

theorem rowEval3757 (x : Key → ℝ) : Integer.Sparse.eval row3757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3757, Integer.Sparse.eval_collectBalanced, rawRowCheck3757]

def rawRow3758 : Integer.Sparse Key := [(key448, -6), (key326, 2), (key416, 2), (key448, 2), (key438, 6), (key256, -2), (key393, -2), (key438, -2), (key315, -2), (key405, -2), (key434, -2), (key247, 2), (key384, 2), (key434, 2)]

theorem rawRowCheck3758 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form1 = rawRow3758 := by decide +kernel

def row3758 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

theorem rowCheck3758 : row3758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3758 := by decide +kernel

theorem rowEval3758 (x : Key → ℝ) : Integer.Sparse.eval row3758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3758, Integer.Sparse.eval_collectBalanced, rawRowCheck3758]

def rawRow3759 : Integer.Sparse Key := [(key448, -6), (key326, 2), (key448, 2), (key416, 2), (key438, 6), (key256, -2), (key438, -2), (key393, -2), (key315, -2), (key434, -2), (key405, -2), (key247, 2), (key434, 2), (key384, 2)]

theorem rawRowCheck3759 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form1 = rawRow3759 := by decide +kernel

def row3759 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

theorem rowCheck3759 : row3759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3759 := by decide +kernel

theorem rowEval3759 (x : Key → ℝ) : Integer.Sparse.eval row3759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3759, Integer.Sparse.eval_collectBalanced, rawRowCheck3759]

def rawRow3760 : Integer.Sparse Key := [(key448, -6), (key416, 2), (key326, 2), (key448, 2), (key438, 6), (key393, -2), (key256, -2), (key438, -2), (key405, -2), (key315, -2), (key434, -2), (key384, 2), (key247, 2), (key434, 2)]

theorem rawRowCheck3760 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form1 = rawRow3760 := by decide +kernel

def row3760 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

theorem rowCheck3760 : row3760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3760 := by decide +kernel

theorem rowEval3760 (x : Key → ℝ) : Integer.Sparse.eval row3760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3760, Integer.Sparse.eval_collectBalanced, rawRowCheck3760]

def rawRow3761 : Integer.Sparse Key := [(key448, -6), (key416, 2), (key448, 2), (key326, 2), (key438, 6), (key393, -2), (key438, -2), (key256, -2), (key405, -2), (key434, -2), (key315, -2), (key384, 2), (key434, 2), (key247, 2)]

theorem rawRowCheck3761 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form1 = rawRow3761 := by decide +kernel

def row3761 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

theorem rowCheck3761 : row3761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3761 := by decide +kernel

theorem rowEval3761 (x : Key → ℝ) : Integer.Sparse.eval row3761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3761, Integer.Sparse.eval_collectBalanced, rawRowCheck3761]

def rawRow3762 : Integer.Sparse Key := [(key448, -6), (key448, 2), (key326, 2), (key416, 2), (key438, 6), (key438, -2), (key256, -2), (key393, -2), (key434, -2), (key315, -2), (key405, -2), (key434, 2), (key247, 2), (key384, 2)]

theorem rawRowCheck3762 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form1 = rawRow3762 := by decide +kernel

def row3762 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

theorem rowCheck3762 : row3762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3762 := by decide +kernel

theorem rowEval3762 (x : Key → ℝ) : Integer.Sparse.eval row3762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3762, Integer.Sparse.eval_collectBalanced, rawRowCheck3762]

def rawRow3763 : Integer.Sparse Key := [(key448, -6), (key448, 2), (key416, 2), (key326, 2), (key438, 6), (key438, -2), (key393, -2), (key256, -2), (key434, -2), (key405, -2), (key315, -2), (key434, 2), (key384, 2), (key247, 2)]

theorem rawRowCheck3763 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form1 = rawRow3763 := by decide +kernel

def row3763 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

theorem rowCheck3763 : row3763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3763 := by decide +kernel

theorem rowEval3763 (x : Key → ℝ) : Integer.Sparse.eval row3763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3763, Integer.Sparse.eval_collectBalanced, rawRowCheck3763]

def rawRow3764 : Integer.Sparse Key := [(key1542, -2), (key1548, -2), (key1896, -2), (key1387, 1), (key1393, 1), (key1542, 1), (key1556, 1), (key1896, 1), (key1899, 1), (key1569, 2), (key1575, 2), (key1903, 2), (key1292, -1), (key1298, -1), (key1569, -1), (key1593, -1), (key1903, -1), (key1911, -1), (key1420, -1), (key1426, -1), (key1618, -1), (key1624, -1), (key1918, -1), (key1920, -1), (key1312, 1), (key1318, 1), (key1618, 1), (key1633, 1), (key1918, 1), (key1926, 1)]

theorem rawRowCheck3764 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form2 = rawRow3764 := by decide +kernel

def row3764 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck3764 : row3764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3764 := by decide +kernel

theorem rowEval3764 (x : Key → ℝ) : Integer.Sparse.eval row3764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3764, Integer.Sparse.eval_collectBalanced, rawRowCheck3764]

def rawRow3765 : Integer.Sparse Key := [(key1548, -2), (key1542, -2), (key1896, -2), (key1393, 1), (key1387, 1), (key1556, 1), (key1542, 1), (key1899, 1), (key1896, 1), (key1575, 2), (key1569, 2), (key1903, 2), (key1298, -1), (key1292, -1), (key1593, -1), (key1569, -1), (key1911, -1), (key1903, -1), (key1426, -1), (key1420, -1), (key1624, -1), (key1618, -1), (key1920, -1), (key1918, -1), (key1318, 1), (key1312, 1), (key1633, 1), (key1618, 1), (key1926, 1), (key1918, 1)]

theorem rawRowCheck3765 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form2 = rawRow3765 := by decide +kernel

def row3765 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck3765 : row3765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3765 := by decide +kernel

theorem rowEval3765 (x : Key → ℝ) : Integer.Sparse.eval row3765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3765, Integer.Sparse.eval_collectBalanced, rawRowCheck3765]

def rawRow3766 : Integer.Sparse Key := [(key1542, -2), (key1896, -2), (key1548, -2), (key1542, 1), (key1896, 1), (key1387, 1), (key1899, 1), (key1393, 1), (key1556, 1), (key1569, 2), (key1903, 2), (key1575, 2), (key1569, -1), (key1903, -1), (key1292, -1), (key1911, -1), (key1298, -1), (key1593, -1), (key1618, -1), (key1918, -1), (key1420, -1), (key1920, -1), (key1426, -1), (key1624, -1), (key1618, 1), (key1918, 1), (key1312, 1), (key1926, 1), (key1318, 1), (key1633, 1)]

theorem rawRowCheck3766 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form2 = rawRow3766 := by decide +kernel

def row3766 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck3766 : row3766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3766 := by decide +kernel

theorem rowEval3766 (x : Key → ℝ) : Integer.Sparse.eval row3766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3766, Integer.Sparse.eval_collectBalanced, rawRowCheck3766]

def rawRow3767 : Integer.Sparse Key := [(key1896, -2), (key1542, -2), (key1548, -2), (key1896, 1), (key1542, 1), (key1899, 1), (key1387, 1), (key1556, 1), (key1393, 1), (key1903, 2), (key1569, 2), (key1575, 2), (key1903, -1), (key1569, -1), (key1911, -1), (key1292, -1), (key1593, -1), (key1298, -1), (key1918, -1), (key1618, -1), (key1920, -1), (key1420, -1), (key1624, -1), (key1426, -1), (key1918, 1), (key1618, 1), (key1926, 1), (key1312, 1), (key1633, 1), (key1318, 1)]

theorem rawRowCheck3767 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form2 = rawRow3767 := by decide +kernel

def row3767 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck3767 : row3767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3767 := by decide +kernel

theorem rowEval3767 (x : Key → ℝ) : Integer.Sparse.eval row3767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3767, Integer.Sparse.eval_collectBalanced, rawRowCheck3767]

def rawRow3768 : Integer.Sparse Key := [(key1548, -2), (key1896, -2), (key1542, -2), (key1556, 1), (key1899, 1), (key1393, 1), (key1896, 1), (key1387, 1), (key1542, 1), (key1575, 2), (key1903, 2), (key1569, 2), (key1593, -1), (key1911, -1), (key1298, -1), (key1903, -1), (key1292, -1), (key1569, -1), (key1624, -1), (key1920, -1), (key1426, -1), (key1918, -1), (key1420, -1), (key1618, -1), (key1633, 1), (key1926, 1), (key1318, 1), (key1918, 1), (key1312, 1), (key1618, 1)]

theorem rawRowCheck3768 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form2 = rawRow3768 := by decide +kernel

def row3768 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck3768 : row3768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3768 := by decide +kernel

theorem rowEval3768 (x : Key → ℝ) : Integer.Sparse.eval row3768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3768, Integer.Sparse.eval_collectBalanced, rawRowCheck3768]

def rawRow3769 : Integer.Sparse Key := [(key1896, -2), (key1548, -2), (key1542, -2), (key1899, 1), (key1556, 1), (key1896, 1), (key1393, 1), (key1542, 1), (key1387, 1), (key1903, 2), (key1575, 2), (key1569, 2), (key1911, -1), (key1593, -1), (key1903, -1), (key1298, -1), (key1569, -1), (key1292, -1), (key1920, -1), (key1624, -1), (key1918, -1), (key1426, -1), (key1618, -1), (key1420, -1), (key1926, 1), (key1633, 1), (key1918, 1), (key1318, 1), (key1618, 1), (key1312, 1)]

theorem rawRowCheck3769 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form2 = rawRow3769 := by decide +kernel

def row3769 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck3769 : row3769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3769 := by decide +kernel

theorem rowEval3769 (x : Key → ℝ) : Integer.Sparse.eval row3769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3769, Integer.Sparse.eval_collectBalanced, rawRowCheck3769]

def rawRow3770 : Integer.Sparse Key := [(key1556, -2), (key1556, -2), (key1899, -2), (key1393, 1), (key1393, 1), (key1548, 1), (key1548, 1), (key1896, 1), (key1896, 1), (key1593, 2), (key1593, 2), (key1911, 2), (key1298, -1), (key1298, -1), (key1575, -1), (key1575, -1), (key1903, -1), (key1903, -1), (key1444, -1), (key1444, -1), (key1633, -1), (key1633, -1), (key1926, -1), (key1926, -1), (key1326, 1), (key1326, 1), (key1624, 1), (key1624, 1), (key1920, 1), (key1920, 1)]

theorem rawRowCheck3770 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form2 = rawRow3770 := by decide +kernel

def row3770 : Integer.Sparse Key := [(key1298, -2), (key1326, 2), (key1393, 2), (key1444, -2), (key1548, 2), (key1556, -4), (key1575, -2), (key1593, 4), (key1624, 2), (key1633, -2), (key1896, 2), (key1899, -2), (key1903, -2), (key1911, 2), (key1920, 2), (key1926, -2)]

theorem rowCheck3770 : row3770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3770 := by decide +kernel

theorem rowEval3770 (x : Key → ℝ) : Integer.Sparse.eval row3770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3770, Integer.Sparse.eval_collectBalanced, rawRowCheck3770]

def rawRow3771 : Integer.Sparse Key := [(key1556, -2), (key1899, -2), (key1556, -2), (key1548, 1), (key1896, 1), (key1393, 1), (key1896, 1), (key1393, 1), (key1548, 1), (key1593, 2), (key1911, 2), (key1593, 2), (key1575, -1), (key1903, -1), (key1298, -1), (key1903, -1), (key1298, -1), (key1575, -1), (key1633, -1), (key1926, -1), (key1444, -1), (key1926, -1), (key1444, -1), (key1633, -1), (key1624, 1), (key1920, 1), (key1326, 1), (key1920, 1), (key1326, 1), (key1624, 1)]

theorem rawRowCheck3771 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form2 = rawRow3771 := by decide +kernel

def row3771 : Integer.Sparse Key := [(key1298, -2), (key1326, 2), (key1393, 2), (key1444, -2), (key1548, 2), (key1556, -4), (key1575, -2), (key1593, 4), (key1624, 2), (key1633, -2), (key1896, 2), (key1899, -2), (key1903, -2), (key1911, 2), (key1920, 2), (key1926, -2)]

theorem rowCheck3771 : row3771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3771 := by decide +kernel

theorem rowEval3771 (x : Key → ℝ) : Integer.Sparse.eval row3771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3771, Integer.Sparse.eval_collectBalanced, rawRowCheck3771]

def rawRow3772 : Integer.Sparse Key := [(key1899, -2), (key1556, -2), (key1556, -2), (key1896, 1), (key1548, 1), (key1896, 1), (key1393, 1), (key1548, 1), (key1393, 1), (key1911, 2), (key1593, 2), (key1593, 2), (key1903, -1), (key1575, -1), (key1903, -1), (key1298, -1), (key1575, -1), (key1298, -1), (key1926, -1), (key1633, -1), (key1926, -1), (key1444, -1), (key1633, -1), (key1444, -1), (key1920, 1), (key1624, 1), (key1920, 1), (key1326, 1), (key1624, 1), (key1326, 1)]

theorem rawRowCheck3772 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form2 = rawRow3772 := by decide +kernel

def row3772 : Integer.Sparse Key := [(key1298, -2), (key1326, 2), (key1393, 2), (key1444, -2), (key1548, 2), (key1556, -4), (key1575, -2), (key1593, 4), (key1624, 2), (key1633, -2), (key1896, 2), (key1899, -2), (key1903, -2), (key1911, 2), (key1920, 2), (key1926, -2)]

theorem rowCheck3772 : row3772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3772 := by decide +kernel

theorem rowEval3772 (x : Key → ℝ) : Integer.Sparse.eval row3772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3772, Integer.Sparse.eval_collectBalanced, rawRowCheck3772]

def rawRow3773 : Integer.Sparse Key := [(key1569, -2), (key1575, -2), (key1903, -2), (key1420, 1), (key1426, 1), (key1618, 1), (key1624, 1), (key1918, 1), (key1920, 1), (key1542, 2), (key1548, 2), (key1896, 2), (key1312, -1), (key1318, -1), (key1618, -1), (key1633, -1), (key1918, -1), (key1926, -1), (key1387, -1), (key1393, -1), (key1542, -1), (key1556, -1), (key1896, -1), (key1899, -1), (key1292, 1), (key1298, 1), (key1569, 1), (key1593, 1), (key1903, 1), (key1911, 1)]

theorem rawRowCheck3773 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form2 = rawRow3773 := by decide +kernel

def row3773 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck3773 : row3773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3773 := by decide +kernel

theorem rowEval3773 (x : Key → ℝ) : Integer.Sparse.eval row3773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3773, Integer.Sparse.eval_collectBalanced, rawRowCheck3773]

def rawRow3774 : Integer.Sparse Key := [(key1575, -2), (key1569, -2), (key1903, -2), (key1426, 1), (key1420, 1), (key1624, 1), (key1618, 1), (key1920, 1), (key1918, 1), (key1548, 2), (key1542, 2), (key1896, 2), (key1318, -1), (key1312, -1), (key1633, -1), (key1618, -1), (key1926, -1), (key1918, -1), (key1393, -1), (key1387, -1), (key1556, -1), (key1542, -1), (key1899, -1), (key1896, -1), (key1298, 1), (key1292, 1), (key1593, 1), (key1569, 1), (key1911, 1), (key1903, 1)]

theorem rawRowCheck3774 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form2 = rawRow3774 := by decide +kernel

def row3774 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck3774 : row3774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3774 := by decide +kernel

theorem rowEval3774 (x : Key → ℝ) : Integer.Sparse.eval row3774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3774, Integer.Sparse.eval_collectBalanced, rawRowCheck3774]

def rawRow3775 : Integer.Sparse Key := [(key1569, -2), (key1903, -2), (key1575, -2), (key1618, 1), (key1918, 1), (key1420, 1), (key1920, 1), (key1426, 1), (key1624, 1), (key1542, 2), (key1896, 2), (key1548, 2), (key1618, -1), (key1918, -1), (key1312, -1), (key1926, -1), (key1318, -1), (key1633, -1), (key1542, -1), (key1896, -1), (key1387, -1), (key1899, -1), (key1393, -1), (key1556, -1), (key1569, 1), (key1903, 1), (key1292, 1), (key1911, 1), (key1298, 1), (key1593, 1)]

theorem rawRowCheck3775 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form2 = rawRow3775 := by decide +kernel

def row3775 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck3775 : row3775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3775 := by decide +kernel

theorem rowEval3775 (x : Key → ℝ) : Integer.Sparse.eval row3775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3775, Integer.Sparse.eval_collectBalanced, rawRowCheck3775]

def rawRow3776 : Integer.Sparse Key := [(key1903, -2), (key1569, -2), (key1575, -2), (key1918, 1), (key1618, 1), (key1920, 1), (key1420, 1), (key1624, 1), (key1426, 1), (key1896, 2), (key1542, 2), (key1548, 2), (key1918, -1), (key1618, -1), (key1926, -1), (key1312, -1), (key1633, -1), (key1318, -1), (key1896, -1), (key1542, -1), (key1899, -1), (key1387, -1), (key1556, -1), (key1393, -1), (key1903, 1), (key1569, 1), (key1911, 1), (key1292, 1), (key1593, 1), (key1298, 1)]

theorem rawRowCheck3776 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form2 = rawRow3776 := by decide +kernel

def row3776 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck3776 : row3776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3776 := by decide +kernel

theorem rowEval3776 (x : Key → ℝ) : Integer.Sparse.eval row3776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3776, Integer.Sparse.eval_collectBalanced, rawRowCheck3776]

def rawRow3777 : Integer.Sparse Key := [(key1575, -2), (key1903, -2), (key1569, -2), (key1624, 1), (key1920, 1), (key1426, 1), (key1918, 1), (key1420, 1), (key1618, 1), (key1548, 2), (key1896, 2), (key1542, 2), (key1633, -1), (key1926, -1), (key1318, -1), (key1918, -1), (key1312, -1), (key1618, -1), (key1556, -1), (key1899, -1), (key1393, -1), (key1896, -1), (key1387, -1), (key1542, -1), (key1593, 1), (key1911, 1), (key1298, 1), (key1903, 1), (key1292, 1), (key1569, 1)]

theorem rawRowCheck3777 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form2 = rawRow3777 := by decide +kernel

def row3777 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck3777 : row3777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3777 := by decide +kernel

theorem rowEval3777 (x : Key → ℝ) : Integer.Sparse.eval row3777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3777, Integer.Sparse.eval_collectBalanced, rawRowCheck3777]

def rawRow3778 : Integer.Sparse Key := [(key1903, -2), (key1575, -2), (key1569, -2), (key1920, 1), (key1624, 1), (key1918, 1), (key1426, 1), (key1618, 1), (key1420, 1), (key1896, 2), (key1548, 2), (key1542, 2), (key1926, -1), (key1633, -1), (key1918, -1), (key1318, -1), (key1618, -1), (key1312, -1), (key1899, -1), (key1556, -1), (key1896, -1), (key1393, -1), (key1542, -1), (key1387, -1), (key1911, 1), (key1593, 1), (key1903, 1), (key1298, 1), (key1569, 1), (key1292, 1)]

theorem rawRowCheck3778 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form2 = rawRow3778 := by decide +kernel

def row3778 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck3778 : row3778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3778 := by decide +kernel

theorem rowEval3778 (x : Key → ℝ) : Integer.Sparse.eval row3778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3778, Integer.Sparse.eval_collectBalanced, rawRowCheck3778]

def rawRow3779 : Integer.Sparse Key := [(key1624, -2), (key1683, -2), (key1920, -2), (key1426, 1), (key1472, 1), (key1575, 1), (key1681, 1), (key1903, 1), (key1918, 1), (key1633, 2), (key1689, 2), (key1926, 2), (key1318, -1), (key1351, -1), (key1548, -1), (key1681, -1), (key1896, -1), (key1918, -1), (key1444, -1), (key1480, -1), (key1593, -1), (key1689, -1), (key1911, -1), (key1926, -1), (key1326, 1), (key1354, 1), (key1556, 1), (key1683, 1), (key1899, 1), (key1920, 1)]

theorem rawRowCheck3779 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form2 = rawRow3779 := by decide +kernel

def row3779 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck3779 : row3779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3779 := by decide +kernel

theorem rowEval3779 (x : Key → ℝ) : Integer.Sparse.eval row3779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3779, Integer.Sparse.eval_collectBalanced, rawRowCheck3779]

def rawRow3780 : Integer.Sparse Key := [(key1683, -2), (key1624, -2), (key1920, -2), (key1472, 1), (key1426, 1), (key1681, 1), (key1575, 1), (key1918, 1), (key1903, 1), (key1689, 2), (key1633, 2), (key1926, 2), (key1351, -1), (key1318, -1), (key1681, -1), (key1548, -1), (key1918, -1), (key1896, -1), (key1480, -1), (key1444, -1), (key1689, -1), (key1593, -1), (key1926, -1), (key1911, -1), (key1354, 1), (key1326, 1), (key1683, 1), (key1556, 1), (key1920, 1), (key1899, 1)]

theorem rawRowCheck3780 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form2 = rawRow3780 := by decide +kernel

def row3780 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck3780 : row3780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3780 := by decide +kernel

theorem rowEval3780 (x : Key → ℝ) : Integer.Sparse.eval row3780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3780, Integer.Sparse.eval_collectBalanced, rawRowCheck3780]

def rawRow3781 : Integer.Sparse Key := [(key1624, -2), (key1920, -2), (key1683, -2), (key1575, 1), (key1903, 1), (key1426, 1), (key1918, 1), (key1472, 1), (key1681, 1), (key1633, 2), (key1926, 2), (key1689, 2), (key1548, -1), (key1896, -1), (key1318, -1), (key1918, -1), (key1351, -1), (key1681, -1), (key1593, -1), (key1911, -1), (key1444, -1), (key1926, -1), (key1480, -1), (key1689, -1), (key1556, 1), (key1899, 1), (key1326, 1), (key1920, 1), (key1354, 1), (key1683, 1)]

theorem rawRowCheck3781 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form2 = rawRow3781 := by decide +kernel

def row3781 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck3781 : row3781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3781 := by decide +kernel

theorem rowEval3781 (x : Key → ℝ) : Integer.Sparse.eval row3781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3781, Integer.Sparse.eval_collectBalanced, rawRowCheck3781]

def rawRow3782 : Integer.Sparse Key := [(key1920, -2), (key1624, -2), (key1683, -2), (key1903, 1), (key1575, 1), (key1918, 1), (key1426, 1), (key1681, 1), (key1472, 1), (key1926, 2), (key1633, 2), (key1689, 2), (key1896, -1), (key1548, -1), (key1918, -1), (key1318, -1), (key1681, -1), (key1351, -1), (key1911, -1), (key1593, -1), (key1926, -1), (key1444, -1), (key1689, -1), (key1480, -1), (key1899, 1), (key1556, 1), (key1920, 1), (key1326, 1), (key1683, 1), (key1354, 1)]

theorem rawRowCheck3782 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form2 = rawRow3782 := by decide +kernel

def row3782 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck3782 : row3782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3782 := by decide +kernel

theorem rowEval3782 (x : Key → ℝ) : Integer.Sparse.eval row3782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3782, Integer.Sparse.eval_collectBalanced, rawRowCheck3782]

def rawRow3783 : Integer.Sparse Key := [(key1683, -2), (key1920, -2), (key1624, -2), (key1681, 1), (key1918, 1), (key1472, 1), (key1903, 1), (key1426, 1), (key1575, 1), (key1689, 2), (key1926, 2), (key1633, 2), (key1681, -1), (key1918, -1), (key1351, -1), (key1896, -1), (key1318, -1), (key1548, -1), (key1689, -1), (key1926, -1), (key1480, -1), (key1911, -1), (key1444, -1), (key1593, -1), (key1683, 1), (key1920, 1), (key1354, 1), (key1899, 1), (key1326, 1), (key1556, 1)]

theorem rawRowCheck3783 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form2 = rawRow3783 := by decide +kernel

def row3783 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck3783 : row3783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3783 := by decide +kernel

theorem rowEval3783 (x : Key → ℝ) : Integer.Sparse.eval row3783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3783, Integer.Sparse.eval_collectBalanced, rawRowCheck3783]

def rawRow3784 : Integer.Sparse Key := [(key1920, -2), (key1683, -2), (key1624, -2), (key1918, 1), (key1681, 1), (key1903, 1), (key1472, 1), (key1575, 1), (key1426, 1), (key1926, 2), (key1689, 2), (key1633, 2), (key1918, -1), (key1681, -1), (key1896, -1), (key1351, -1), (key1548, -1), (key1318, -1), (key1926, -1), (key1689, -1), (key1911, -1), (key1480, -1), (key1593, -1), (key1444, -1), (key1920, 1), (key1683, 1), (key1899, 1), (key1354, 1), (key1556, 1), (key1326, 1)]

theorem rawRowCheck3784 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form2 = rawRow3784 := by decide +kernel

def row3784 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck3784 : row3784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3784 := by decide +kernel

theorem rowEval3784 (x : Key → ℝ) : Integer.Sparse.eval row3784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3784, Integer.Sparse.eval_collectBalanced, rawRowCheck3784]

def rawRow3785 : Integer.Sparse Key := [(key1593, -2), (key1593, -2), (key1911, -2), (key1444, 1), (key1444, 1), (key1633, 1), (key1633, 1), (key1926, 1), (key1926, 1), (key1556, 2), (key1556, 2), (key1899, 2), (key1326, -1), (key1326, -1), (key1624, -1), (key1624, -1), (key1920, -1), (key1920, -1), (key1393, -1), (key1393, -1), (key1548, -1), (key1548, -1), (key1896, -1), (key1896, -1), (key1298, 1), (key1298, 1), (key1575, 1), (key1575, 1), (key1903, 1), (key1903, 1)]

theorem rawRowCheck3785 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form2 = rawRow3785 := by decide +kernel

def row3785 : Integer.Sparse Key := [(key1298, 2), (key1326, -2), (key1393, -2), (key1444, 2), (key1548, -2), (key1556, 4), (key1575, 2), (key1593, -4), (key1624, -2), (key1633, 2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

theorem rowCheck3785 : row3785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3785 := by decide +kernel

theorem rowEval3785 (x : Key → ℝ) : Integer.Sparse.eval row3785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3785, Integer.Sparse.eval_collectBalanced, rawRowCheck3785]

def rawRow3786 : Integer.Sparse Key := [(key1593, -2), (key1911, -2), (key1593, -2), (key1633, 1), (key1926, 1), (key1444, 1), (key1926, 1), (key1444, 1), (key1633, 1), (key1556, 2), (key1899, 2), (key1556, 2), (key1624, -1), (key1920, -1), (key1326, -1), (key1920, -1), (key1326, -1), (key1624, -1), (key1548, -1), (key1896, -1), (key1393, -1), (key1896, -1), (key1393, -1), (key1548, -1), (key1575, 1), (key1903, 1), (key1298, 1), (key1903, 1), (key1298, 1), (key1575, 1)]

theorem rawRowCheck3786 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form2 = rawRow3786 := by decide +kernel

def row3786 : Integer.Sparse Key := [(key1298, 2), (key1326, -2), (key1393, -2), (key1444, 2), (key1548, -2), (key1556, 4), (key1575, 2), (key1593, -4), (key1624, -2), (key1633, 2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

theorem rowCheck3786 : row3786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3786 := by decide +kernel

theorem rowEval3786 (x : Key → ℝ) : Integer.Sparse.eval row3786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3786, Integer.Sparse.eval_collectBalanced, rawRowCheck3786]

def rawRow3787 : Integer.Sparse Key := [(key1911, -2), (key1593, -2), (key1593, -2), (key1926, 1), (key1633, 1), (key1926, 1), (key1444, 1), (key1633, 1), (key1444, 1), (key1899, 2), (key1556, 2), (key1556, 2), (key1920, -1), (key1624, -1), (key1920, -1), (key1326, -1), (key1624, -1), (key1326, -1), (key1896, -1), (key1548, -1), (key1896, -1), (key1393, -1), (key1548, -1), (key1393, -1), (key1903, 1), (key1575, 1), (key1903, 1), (key1298, 1), (key1575, 1), (key1298, 1)]

theorem rawRowCheck3787 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form2 = rawRow3787 := by decide +kernel

def row3787 : Integer.Sparse Key := [(key1298, 2), (key1326, -2), (key1393, -2), (key1444, 2), (key1548, -2), (key1556, 4), (key1575, 2), (key1593, -4), (key1624, -2), (key1633, 2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

theorem rowCheck3787 : row3787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3787 := by decide +kernel

theorem rowEval3787 (x : Key → ℝ) : Integer.Sparse.eval row3787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3787, Integer.Sparse.eval_collectBalanced, rawRowCheck3787]

def rawRow3788 : Integer.Sparse Key := [(key1633, -2), (key1689, -2), (key1926, -2), (key1444, 1), (key1480, 1), (key1593, 1), (key1689, 1), (key1911, 1), (key1926, 1), (key1624, 2), (key1683, 2), (key1920, 2), (key1326, -1), (key1354, -1), (key1556, -1), (key1683, -1), (key1899, -1), (key1920, -1), (key1426, -1), (key1472, -1), (key1575, -1), (key1681, -1), (key1903, -1), (key1918, -1), (key1318, 1), (key1351, 1), (key1548, 1), (key1681, 1), (key1896, 1), (key1918, 1)]

theorem rawRowCheck3788 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form2 = rawRow3788 := by decide +kernel

def row3788 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck3788 : row3788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3788 := by decide +kernel

theorem rowEval3788 (x : Key → ℝ) : Integer.Sparse.eval row3788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3788, Integer.Sparse.eval_collectBalanced, rawRowCheck3788]

def rawRow3789 : Integer.Sparse Key := [(key1689, -2), (key1633, -2), (key1926, -2), (key1480, 1), (key1444, 1), (key1689, 1), (key1593, 1), (key1926, 1), (key1911, 1), (key1683, 2), (key1624, 2), (key1920, 2), (key1354, -1), (key1326, -1), (key1683, -1), (key1556, -1), (key1920, -1), (key1899, -1), (key1472, -1), (key1426, -1), (key1681, -1), (key1575, -1), (key1918, -1), (key1903, -1), (key1351, 1), (key1318, 1), (key1681, 1), (key1548, 1), (key1918, 1), (key1896, 1)]

theorem rawRowCheck3789 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form2 = rawRow3789 := by decide +kernel

def row3789 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck3789 : row3789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3789 := by decide +kernel

theorem rowEval3789 (x : Key → ℝ) : Integer.Sparse.eval row3789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3789, Integer.Sparse.eval_collectBalanced, rawRowCheck3789]

def rawRow3790 : Integer.Sparse Key := [(key1633, -2), (key1926, -2), (key1689, -2), (key1593, 1), (key1911, 1), (key1444, 1), (key1926, 1), (key1480, 1), (key1689, 1), (key1624, 2), (key1920, 2), (key1683, 2), (key1556, -1), (key1899, -1), (key1326, -1), (key1920, -1), (key1354, -1), (key1683, -1), (key1575, -1), (key1903, -1), (key1426, -1), (key1918, -1), (key1472, -1), (key1681, -1), (key1548, 1), (key1896, 1), (key1318, 1), (key1918, 1), (key1351, 1), (key1681, 1)]

theorem rawRowCheck3790 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form2 = rawRow3790 := by decide +kernel

def row3790 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck3790 : row3790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3790 := by decide +kernel

theorem rowEval3790 (x : Key → ℝ) : Integer.Sparse.eval row3790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3790, Integer.Sparse.eval_collectBalanced, rawRowCheck3790]

def rawRow3791 : Integer.Sparse Key := [(key1926, -2), (key1633, -2), (key1689, -2), (key1911, 1), (key1593, 1), (key1926, 1), (key1444, 1), (key1689, 1), (key1480, 1), (key1920, 2), (key1624, 2), (key1683, 2), (key1899, -1), (key1556, -1), (key1920, -1), (key1326, -1), (key1683, -1), (key1354, -1), (key1903, -1), (key1575, -1), (key1918, -1), (key1426, -1), (key1681, -1), (key1472, -1), (key1896, 1), (key1548, 1), (key1918, 1), (key1318, 1), (key1681, 1), (key1351, 1)]

theorem rawRowCheck3791 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form2 = rawRow3791 := by decide +kernel

def row3791 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck3791 : row3791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3791 := by decide +kernel

theorem rowEval3791 (x : Key → ℝ) : Integer.Sparse.eval row3791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3791, Integer.Sparse.eval_collectBalanced, rawRowCheck3791]

def rawRow3792 : Integer.Sparse Key := [(key1689, -2), (key1926, -2), (key1633, -2), (key1689, 1), (key1926, 1), (key1480, 1), (key1911, 1), (key1444, 1), (key1593, 1), (key1683, 2), (key1920, 2), (key1624, 2), (key1683, -1), (key1920, -1), (key1354, -1), (key1899, -1), (key1326, -1), (key1556, -1), (key1681, -1), (key1918, -1), (key1472, -1), (key1903, -1), (key1426, -1), (key1575, -1), (key1681, 1), (key1918, 1), (key1351, 1), (key1896, 1), (key1318, 1), (key1548, 1)]

theorem rawRowCheck3792 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form2 = rawRow3792 := by decide +kernel

def row3792 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck3792 : row3792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3792 := by decide +kernel

theorem rowEval3792 (x : Key → ℝ) : Integer.Sparse.eval row3792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3792, Integer.Sparse.eval_collectBalanced, rawRowCheck3792]

def rawRow3793 : Integer.Sparse Key := [(key1926, -2), (key1689, -2), (key1633, -2), (key1926, 1), (key1689, 1), (key1911, 1), (key1480, 1), (key1593, 1), (key1444, 1), (key1920, 2), (key1683, 2), (key1624, 2), (key1920, -1), (key1683, -1), (key1899, -1), (key1354, -1), (key1556, -1), (key1326, -1), (key1918, -1), (key1681, -1), (key1903, -1), (key1472, -1), (key1575, -1), (key1426, -1), (key1918, 1), (key1681, 1), (key1896, 1), (key1351, 1), (key1548, 1), (key1318, 1)]

theorem rawRowCheck3793 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form2 = rawRow3793 := by decide +kernel

def row3793 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck3793 : row3793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3793 := by decide +kernel

theorem rowEval3793 (x : Key → ℝ) : Integer.Sparse.eval row3793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3793, Integer.Sparse.eval_collectBalanced, rawRowCheck3793]

def rawRow3794 : Integer.Sparse Key := [(key44, -2), (key47, -2), (key73, -2), (key47, 6), (key101, 2), (key104, 2), (key136, 2), (key22, -2), (key104, -2), (key172, -2), (key114, -6), (key34, 2), (key114, 2), (key176, 2)]

theorem rawRowCheck3794 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form3 = rawRow3794 := by decide +kernel

def row3794 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

theorem rowCheck3794 : row3794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3794 := by decide +kernel

theorem rowEval3794 (x : Key → ℝ) : Integer.Sparse.eval row3794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3794, Integer.Sparse.eval_collectBalanced, rawRowCheck3794]

def rawRow3795 : Integer.Sparse Key := [(key47, -2), (key44, -2), (key73, -2), (key47, 6), (key104, 2), (key101, 2), (key136, 2), (key22, -2), (key172, -2), (key104, -2), (key114, -6), (key34, 2), (key176, 2), (key114, 2)]

theorem rawRowCheck3795 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form3 = rawRow3795 := by decide +kernel

def row3795 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

theorem rowCheck3795 : row3795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3795 := by decide +kernel

theorem rowEval3795 (x : Key → ℝ) : Integer.Sparse.eval row3795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3795, Integer.Sparse.eval_collectBalanced, rawRowCheck3795]

def rawRow3796 : Integer.Sparse Key := [(key44, -2), (key73, -2), (key47, -2), (key47, 6), (key101, 2), (key136, 2), (key104, 2), (key104, -2), (key22, -2), (key172, -2), (key114, -6), (key114, 2), (key34, 2), (key176, 2)]

theorem rawRowCheck3796 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form3 = rawRow3796 := by decide +kernel

def row3796 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

theorem rowCheck3796 : row3796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3796 := by decide +kernel

theorem rowEval3796 (x : Key → ℝ) : Integer.Sparse.eval row3796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3796, Integer.Sparse.eval_collectBalanced, rawRowCheck3796]

def rawRow3797 : Integer.Sparse Key := [(key73, -2), (key44, -2), (key47, -2), (key47, 6), (key136, 2), (key101, 2), (key104, 2), (key104, -2), (key172, -2), (key22, -2), (key114, -6), (key114, 2), (key176, 2), (key34, 2)]

theorem rawRowCheck3797 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form3 = rawRow3797 := by decide +kernel

def row3797 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

theorem rowCheck3797 : row3797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3797 := by decide +kernel

theorem rowEval3797 (x : Key → ℝ) : Integer.Sparse.eval row3797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3797, Integer.Sparse.eval_collectBalanced, rawRowCheck3797]

def rawRow3798 : Integer.Sparse Key := [(key47, -2), (key73, -2), (key44, -2), (key47, 6), (key104, 2), (key136, 2), (key101, 2), (key172, -2), (key22, -2), (key104, -2), (key114, -6), (key176, 2), (key34, 2), (key114, 2)]

theorem rawRowCheck3798 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form3 = rawRow3798 := by decide +kernel

def row3798 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

theorem rowCheck3798 : row3798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3798 := by decide +kernel

theorem rowEval3798 (x : Key → ℝ) : Integer.Sparse.eval row3798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3798, Integer.Sparse.eval_collectBalanced, rawRowCheck3798]

def rawRow3799 : Integer.Sparse Key := [(key73, -2), (key47, -2), (key44, -2), (key47, 6), (key136, 2), (key104, 2), (key101, 2), (key172, -2), (key104, -2), (key22, -2), (key114, -6), (key176, 2), (key114, 2), (key34, 2)]

theorem rawRowCheck3799 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form3 = rawRow3799 := by decide +kernel

def row3799 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

theorem rowCheck3799 : row3799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3799 := by decide +kernel

theorem rowEval3799 (x : Key → ℝ) : Integer.Sparse.eval row3799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3799, Integer.Sparse.eval_collectBalanced, rawRowCheck3799]

def rawRow3800 : Integer.Sparse Key := [(key47, -2), (key47, -2), (key73, -2), (key44, 6), (key172, 2), (key172, 2), (key181, 2), (key19, -2), (key101, -2), (key101, -2), (key176, -6), (key34, 2), (key114, 2), (key114, 2)]

theorem rawRowCheck3800 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow3800 := by decide +kernel

def row3800 : Integer.Sparse Key := [(key19, -2), (key34, 2), (key44, 6), (key47, -4), (key73, -2), (key101, -4), (key114, 4), (key172, 4), (key176, -6), (key181, 2)]

theorem rowCheck3800 : row3800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3800 := by decide +kernel

theorem rowEval3800 (x : Key → ℝ) : Integer.Sparse.eval row3800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3800, Integer.Sparse.eval_collectBalanced, rawRowCheck3800]

def rawRow3801 : Integer.Sparse Key := [(key47, -2), (key73, -2), (key47, -2), (key44, 6), (key172, 2), (key181, 2), (key172, 2), (key101, -2), (key19, -2), (key101, -2), (key176, -6), (key114, 2), (key34, 2), (key114, 2)]

theorem rawRowCheck3801 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow3801 := by decide +kernel

def row3801 : Integer.Sparse Key := [(key19, -2), (key34, 2), (key44, 6), (key47, -4), (key73, -2), (key101, -4), (key114, 4), (key172, 4), (key176, -6), (key181, 2)]

theorem rowCheck3801 : row3801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3801 := by decide +kernel

theorem rowEval3801 (x : Key → ℝ) : Integer.Sparse.eval row3801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3801, Integer.Sparse.eval_collectBalanced, rawRowCheck3801]

def rawRow3802 : Integer.Sparse Key := [(key73, -2), (key47, -2), (key47, -2), (key44, 6), (key181, 2), (key172, 2), (key172, 2), (key101, -2), (key101, -2), (key19, -2), (key176, -6), (key114, 2), (key114, 2), (key34, 2)]

theorem rawRowCheck3802 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow3802 := by decide +kernel

def row3802 : Integer.Sparse Key := [(key19, -2), (key34, 2), (key44, 6), (key47, -4), (key73, -2), (key101, -4), (key114, 4), (key172, 4), (key176, -6), (key181, 2)]

theorem rowCheck3802 : row3802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3802 := by decide +kernel

theorem rowEval3802 (x : Key → ℝ) : Integer.Sparse.eval row3802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3802, Integer.Sparse.eval_collectBalanced, rawRowCheck3802]

def rawRow3803 : Integer.Sparse Key := [(key101, -2), (key104, -2), (key136, -2), (key114, 6), (key44, 2), (key47, 2), (key73, 2), (key34, -2), (key114, -2), (key176, -2), (key47, -6), (key22, 2), (key104, 2), (key172, 2)]

theorem rawRowCheck3803 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form3 = rawRow3803 := by decide +kernel

def row3803 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

theorem rowCheck3803 : row3803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3803 := by decide +kernel

theorem rowEval3803 (x : Key → ℝ) : Integer.Sparse.eval row3803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3803, Integer.Sparse.eval_collectBalanced, rawRowCheck3803]

def rawRow3804 : Integer.Sparse Key := [(key104, -2), (key101, -2), (key136, -2), (key114, 6), (key47, 2), (key44, 2), (key73, 2), (key34, -2), (key176, -2), (key114, -2), (key47, -6), (key22, 2), (key172, 2), (key104, 2)]

theorem rawRowCheck3804 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form3 = rawRow3804 := by decide +kernel

def row3804 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

theorem rowCheck3804 : row3804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3804 := by decide +kernel

theorem rowEval3804 (x : Key → ℝ) : Integer.Sparse.eval row3804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3804, Integer.Sparse.eval_collectBalanced, rawRowCheck3804]

def rawRow3805 : Integer.Sparse Key := [(key101, -2), (key136, -2), (key104, -2), (key114, 6), (key44, 2), (key73, 2), (key47, 2), (key114, -2), (key34, -2), (key176, -2), (key47, -6), (key104, 2), (key22, 2), (key172, 2)]

theorem rawRowCheck3805 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form3 = rawRow3805 := by decide +kernel

def row3805 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

theorem rowCheck3805 : row3805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3805 := by decide +kernel

theorem rowEval3805 (x : Key → ℝ) : Integer.Sparse.eval row3805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3805, Integer.Sparse.eval_collectBalanced, rawRowCheck3805]

def rawRow3806 : Integer.Sparse Key := [(key136, -2), (key101, -2), (key104, -2), (key114, 6), (key73, 2), (key44, 2), (key47, 2), (key114, -2), (key176, -2), (key34, -2), (key47, -6), (key104, 2), (key172, 2), (key22, 2)]

theorem rawRowCheck3806 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form3 = rawRow3806 := by decide +kernel

def row3806 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

theorem rowCheck3806 : row3806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3806 := by decide +kernel

theorem rowEval3806 (x : Key → ℝ) : Integer.Sparse.eval row3806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3806, Integer.Sparse.eval_collectBalanced, rawRowCheck3806]

def rawRow3807 : Integer.Sparse Key := [(key104, -2), (key136, -2), (key101, -2), (key114, 6), (key47, 2), (key73, 2), (key44, 2), (key176, -2), (key34, -2), (key114, -2), (key47, -6), (key172, 2), (key22, 2), (key104, 2)]

theorem rawRowCheck3807 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form3 = rawRow3807 := by decide +kernel

def row3807 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

theorem rowCheck3807 : row3807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3807 := by decide +kernel

theorem rowEval3807 (x : Key → ℝ) : Integer.Sparse.eval row3807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3807, Integer.Sparse.eval_collectBalanced, rawRowCheck3807]

def rawRow3808 : Integer.Sparse Key := [(key136, -2), (key104, -2), (key101, -2), (key114, 6), (key73, 2), (key47, 2), (key44, 2), (key176, -2), (key114, -2), (key34, -2), (key47, -6), (key172, 2), (key104, 2), (key22, 2)]

theorem rawRowCheck3808 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form3 = rawRow3808 := by decide +kernel

def row3808 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

theorem rowCheck3808 : row3808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3808 := by decide +kernel

theorem rowEval3808 (x : Key → ℝ) : Integer.Sparse.eval row3808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3808, Integer.Sparse.eval_collectBalanced, rawRowCheck3808]

def rawRow3809 : Integer.Sparse Key := [(key104, -2), (key114, -2), (key136, -2), (key101, 6), (key172, 2), (key176, 2), (key181, 2), (key19, -2), (key44, -2), (key101, -2), (key172, -6), (key22, 2), (key47, 2), (key104, 2)]

theorem rawRowCheck3809 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form3 = rawRow3809 := by decide +kernel

def row3809 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

theorem rowCheck3809 : row3809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3809 := by decide +kernel

theorem rowEval3809 (x : Key → ℝ) : Integer.Sparse.eval row3809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3809, Integer.Sparse.eval_collectBalanced, rawRowCheck3809]

def rawRow3810 : Integer.Sparse Key := [(key114, -2), (key104, -2), (key136, -2), (key101, 6), (key176, 2), (key172, 2), (key181, 2), (key19, -2), (key101, -2), (key44, -2), (key172, -6), (key22, 2), (key104, 2), (key47, 2)]

theorem rawRowCheck3810 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form3 = rawRow3810 := by decide +kernel

def row3810 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

theorem rowCheck3810 : row3810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3810 := by decide +kernel

theorem rowEval3810 (x : Key → ℝ) : Integer.Sparse.eval row3810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3810, Integer.Sparse.eval_collectBalanced, rawRowCheck3810]

def rawRow3811 : Integer.Sparse Key := [(key104, -2), (key136, -2), (key114, -2), (key101, 6), (key172, 2), (key181, 2), (key176, 2), (key44, -2), (key19, -2), (key101, -2), (key172, -6), (key47, 2), (key22, 2), (key104, 2)]

theorem rawRowCheck3811 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form3 = rawRow3811 := by decide +kernel

def row3811 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

theorem rowCheck3811 : row3811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3811 := by decide +kernel

theorem rowEval3811 (x : Key → ℝ) : Integer.Sparse.eval row3811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3811, Integer.Sparse.eval_collectBalanced, rawRowCheck3811]

def rawRow3812 : Integer.Sparse Key := [(key136, -2), (key104, -2), (key114, -2), (key101, 6), (key181, 2), (key172, 2), (key176, 2), (key44, -2), (key101, -2), (key19, -2), (key172, -6), (key47, 2), (key104, 2), (key22, 2)]

theorem rawRowCheck3812 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form3 = rawRow3812 := by decide +kernel

def row3812 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

theorem rowCheck3812 : row3812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3812 := by decide +kernel

theorem rowEval3812 (x : Key → ℝ) : Integer.Sparse.eval row3812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3812, Integer.Sparse.eval_collectBalanced, rawRowCheck3812]

def rawRow3813 : Integer.Sparse Key := [(key114, -2), (key136, -2), (key104, -2), (key101, 6), (key176, 2), (key181, 2), (key172, 2), (key101, -2), (key19, -2), (key44, -2), (key172, -6), (key104, 2), (key22, 2), (key47, 2)]

theorem rawRowCheck3813 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form3 = rawRow3813 := by decide +kernel

def row3813 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

theorem rowCheck3813 : row3813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3813 := by decide +kernel

theorem rowEval3813 (x : Key → ℝ) : Integer.Sparse.eval row3813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3813, Integer.Sparse.eval_collectBalanced, rawRowCheck3813]

def rawRow3814 : Integer.Sparse Key := [(key136, -2), (key114, -2), (key104, -2), (key101, 6), (key181, 2), (key176, 2), (key172, 2), (key101, -2), (key44, -2), (key19, -2), (key172, -6), (key104, 2), (key47, 2), (key22, 2)]

theorem rawRowCheck3814 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form3 = rawRow3814 := by decide +kernel

def row3814 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

theorem rowCheck3814 : row3814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3814 := by decide +kernel

theorem rowEval3814 (x : Key → ℝ) : Integer.Sparse.eval row3814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3814, Integer.Sparse.eval_collectBalanced, rawRowCheck3814]

def rawRow3815 : Integer.Sparse Key := [(key172, -2), (key172, -2), (key181, -2), (key176, 6), (key47, 2), (key47, 2), (key73, 2), (key34, -2), (key114, -2), (key114, -2), (key44, -6), (key19, 2), (key101, 2), (key101, 2)]

theorem rawRowCheck3815 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow3815 := by decide +kernel

def row3815 : Integer.Sparse Key := [(key19, 2), (key34, -2), (key44, -6), (key47, 4), (key73, 2), (key101, 4), (key114, -4), (key172, -4), (key176, 6), (key181, -2)]

theorem rowCheck3815 : row3815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3815 := by decide +kernel

theorem rowEval3815 (x : Key → ℝ) : Integer.Sparse.eval row3815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3815, Integer.Sparse.eval_collectBalanced, rawRowCheck3815]

def rawRow3816 : Integer.Sparse Key := [(key172, -2), (key181, -2), (key172, -2), (key176, 6), (key47, 2), (key73, 2), (key47, 2), (key114, -2), (key34, -2), (key114, -2), (key44, -6), (key101, 2), (key19, 2), (key101, 2)]

theorem rawRowCheck3816 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow3816 := by decide +kernel

def row3816 : Integer.Sparse Key := [(key19, 2), (key34, -2), (key44, -6), (key47, 4), (key73, 2), (key101, 4), (key114, -4), (key172, -4), (key176, 6), (key181, -2)]

theorem rowCheck3816 : row3816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3816 := by decide +kernel

theorem rowEval3816 (x : Key → ℝ) : Integer.Sparse.eval row3816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3816, Integer.Sparse.eval_collectBalanced, rawRowCheck3816]

def rawRow3817 : Integer.Sparse Key := [(key181, -2), (key172, -2), (key172, -2), (key176, 6), (key73, 2), (key47, 2), (key47, 2), (key114, -2), (key114, -2), (key34, -2), (key44, -6), (key101, 2), (key101, 2), (key19, 2)]

theorem rawRowCheck3817 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow3817 := by decide +kernel

def row3817 : Integer.Sparse Key := [(key19, 2), (key34, -2), (key44, -6), (key47, 4), (key73, 2), (key101, 4), (key114, -4), (key172, -4), (key176, 6), (key181, -2)]

theorem rowCheck3817 : row3817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3817 := by decide +kernel

theorem rowEval3817 (x : Key → ℝ) : Integer.Sparse.eval row3817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3817, Integer.Sparse.eval_collectBalanced, rawRowCheck3817]

def rawRow3818 : Integer.Sparse Key := [(key172, -2), (key176, -2), (key181, -2), (key172, 6), (key104, 2), (key114, 2), (key136, 2), (key22, -2), (key47, -2), (key104, -2), (key101, -6), (key19, 2), (key44, 2), (key101, 2)]

theorem rawRowCheck3818 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form3 = rawRow3818 := by decide +kernel

def row3818 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

theorem rowCheck3818 : row3818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3818 := by decide +kernel

theorem rowEval3818 (x : Key → ℝ) : Integer.Sparse.eval row3818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3818, Integer.Sparse.eval_collectBalanced, rawRowCheck3818]

def rawRow3819 : Integer.Sparse Key := [(key176, -2), (key172, -2), (key181, -2), (key172, 6), (key114, 2), (key104, 2), (key136, 2), (key22, -2), (key104, -2), (key47, -2), (key101, -6), (key19, 2), (key101, 2), (key44, 2)]

theorem rawRowCheck3819 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form3 = rawRow3819 := by decide +kernel

def row3819 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

theorem rowCheck3819 : row3819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3819 := by decide +kernel

theorem rowEval3819 (x : Key → ℝ) : Integer.Sparse.eval row3819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3819, Integer.Sparse.eval_collectBalanced, rawRowCheck3819]

def rawRow3820 : Integer.Sparse Key := [(key172, -2), (key181, -2), (key176, -2), (key172, 6), (key104, 2), (key136, 2), (key114, 2), (key47, -2), (key22, -2), (key104, -2), (key101, -6), (key44, 2), (key19, 2), (key101, 2)]

theorem rawRowCheck3820 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form3 = rawRow3820 := by decide +kernel

def row3820 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

theorem rowCheck3820 : row3820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3820 := by decide +kernel

theorem rowEval3820 (x : Key → ℝ) : Integer.Sparse.eval row3820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3820, Integer.Sparse.eval_collectBalanced, rawRowCheck3820]

def rawRow3821 : Integer.Sparse Key := [(key181, -2), (key172, -2), (key176, -2), (key172, 6), (key136, 2), (key104, 2), (key114, 2), (key47, -2), (key104, -2), (key22, -2), (key101, -6), (key44, 2), (key101, 2), (key19, 2)]

theorem rawRowCheck3821 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form3 = rawRow3821 := by decide +kernel

def row3821 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

theorem rowCheck3821 : row3821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3821 := by decide +kernel

theorem rowEval3821 (x : Key → ℝ) : Integer.Sparse.eval row3821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3821, Integer.Sparse.eval_collectBalanced, rawRowCheck3821]

def rawRow3822 : Integer.Sparse Key := [(key176, -2), (key181, -2), (key172, -2), (key172, 6), (key114, 2), (key136, 2), (key104, 2), (key104, -2), (key22, -2), (key47, -2), (key101, -6), (key101, 2), (key19, 2), (key44, 2)]

theorem rawRowCheck3822 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form3 = rawRow3822 := by decide +kernel

def row3822 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

theorem rowCheck3822 : row3822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3822 := by decide +kernel

theorem rowEval3822 (x : Key → ℝ) : Integer.Sparse.eval row3822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3822, Integer.Sparse.eval_collectBalanced, rawRowCheck3822]

def rawRow3823 : Integer.Sparse Key := [(key181, -2), (key176, -2), (key172, -2), (key172, 6), (key136, 2), (key114, 2), (key104, 2), (key104, -2), (key47, -2), (key22, -2), (key101, -6), (key101, 2), (key44, 2), (key19, 2)]

theorem rawRowCheck3823 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form3 = rawRow3823 := by decide +kernel

def row3823 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

theorem rowCheck3823 : row3823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3823 := by decide +kernel

theorem rowEval3823 (x : Key → ℝ) : Integer.Sparse.eval row3823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3823, Integer.Sparse.eval_collectBalanced, rawRowCheck3823]

def rawRow3824 : Integer.Sparse Key := [(key1540, -6), (key1385, 2), (key1540, 2), (key1552, 2), (key1567, 6), (key1290, -2), (key1567, -2), (key1589, -2), (key1418, -2), (key1616, -2), (key1620, -2), (key1310, 2), (key1616, 2), (key1629, 2)]

theorem rawRowCheck3824 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form4 = rawRow3824 := by decide +kernel

def row3824 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

theorem rowCheck3824 : row3824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3824 := by decide +kernel

theorem rowEval3824 (x : Key → ℝ) : Integer.Sparse.eval row3824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3824, Integer.Sparse.eval_collectBalanced, rawRowCheck3824]

def rawRow3825 : Integer.Sparse Key := [(key1540, -6), (key1385, 2), (key1552, 2), (key1540, 2), (key1567, 6), (key1290, -2), (key1589, -2), (key1567, -2), (key1418, -2), (key1620, -2), (key1616, -2), (key1310, 2), (key1629, 2), (key1616, 2)]

theorem rawRowCheck3825 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form4 = rawRow3825 := by decide +kernel

def row3825 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

theorem rowCheck3825 : row3825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3825 := by decide +kernel

theorem rowEval3825 (x : Key → ℝ) : Integer.Sparse.eval row3825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3825, Integer.Sparse.eval_collectBalanced, rawRowCheck3825]

def rawRow3826 : Integer.Sparse Key := [(key1540, -6), (key1540, 2), (key1385, 2), (key1552, 2), (key1567, 6), (key1567, -2), (key1290, -2), (key1589, -2), (key1616, -2), (key1418, -2), (key1620, -2), (key1616, 2), (key1310, 2), (key1629, 2)]

theorem rawRowCheck3826 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form4 = rawRow3826 := by decide +kernel

def row3826 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

theorem rowCheck3826 : row3826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3826 := by decide +kernel

theorem rowEval3826 (x : Key → ℝ) : Integer.Sparse.eval row3826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3826, Integer.Sparse.eval_collectBalanced, rawRowCheck3826]

def rawRow3827 : Integer.Sparse Key := [(key1540, -6), (key1540, 2), (key1552, 2), (key1385, 2), (key1567, 6), (key1567, -2), (key1589, -2), (key1290, -2), (key1616, -2), (key1620, -2), (key1418, -2), (key1616, 2), (key1629, 2), (key1310, 2)]

theorem rawRowCheck3827 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form4 = rawRow3827 := by decide +kernel

def row3827 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

theorem rowCheck3827 : row3827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3827 := by decide +kernel

theorem rowEval3827 (x : Key → ℝ) : Integer.Sparse.eval row3827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3827, Integer.Sparse.eval_collectBalanced, rawRowCheck3827]

def rawRow3828 : Integer.Sparse Key := [(key1540, -6), (key1552, 2), (key1385, 2), (key1540, 2), (key1567, 6), (key1589, -2), (key1290, -2), (key1567, -2), (key1620, -2), (key1418, -2), (key1616, -2), (key1629, 2), (key1310, 2), (key1616, 2)]

theorem rawRowCheck3828 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form4 = rawRow3828 := by decide +kernel

def row3828 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

theorem rowCheck3828 : row3828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3828 := by decide +kernel

theorem rowEval3828 (x : Key → ℝ) : Integer.Sparse.eval row3828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3828, Integer.Sparse.eval_collectBalanced, rawRowCheck3828]

def rawRow3829 : Integer.Sparse Key := [(key1540, -6), (key1552, 2), (key1540, 2), (key1385, 2), (key1567, 6), (key1589, -2), (key1567, -2), (key1290, -2), (key1620, -2), (key1616, -2), (key1418, -2), (key1629, 2), (key1616, 2), (key1310, 2)]

theorem rawRowCheck3829 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form4 = rawRow3829 := by decide +kernel

def row3829 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

theorem rowCheck3829 : row3829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3829 := by decide +kernel

theorem rowEval3829 (x : Key → ℝ) : Integer.Sparse.eval row3829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3829, Integer.Sparse.eval_collectBalanced, rawRowCheck3829]

def rawRow3830 : Integer.Sparse Key := [(key1552, -6), (key1385, 2), (key1540, 2), (key1540, 2), (key1589, 6), (key1290, -2), (key1567, -2), (key1567, -2), (key1440, -2), (key1629, -2), (key1629, -2), (key1322, 2), (key1620, 2), (key1620, 2)]

theorem rawRowCheck3830 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form4 = rawRow3830 := by decide +kernel

def row3830 : Integer.Sparse Key := [(key1290, -2), (key1322, 2), (key1385, 2), (key1440, -2), (key1540, 4), (key1552, -6), (key1567, -4), (key1589, 6), (key1620, 4), (key1629, -4)]

theorem rowCheck3830 : row3830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3830 := by decide +kernel

theorem rowEval3830 (x : Key → ℝ) : Integer.Sparse.eval row3830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3830, Integer.Sparse.eval_collectBalanced, rawRowCheck3830]

def rawRow3831 : Integer.Sparse Key := [(key1552, -6), (key1540, 2), (key1385, 2), (key1540, 2), (key1589, 6), (key1567, -2), (key1290, -2), (key1567, -2), (key1629, -2), (key1440, -2), (key1629, -2), (key1620, 2), (key1322, 2), (key1620, 2)]

theorem rawRowCheck3831 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form4 = rawRow3831 := by decide +kernel

def row3831 : Integer.Sparse Key := [(key1290, -2), (key1322, 2), (key1385, 2), (key1440, -2), (key1540, 4), (key1552, -6), (key1567, -4), (key1589, 6), (key1620, 4), (key1629, -4)]

theorem rowCheck3831 : row3831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3831 := by decide +kernel

theorem rowEval3831 (x : Key → ℝ) : Integer.Sparse.eval row3831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3831, Integer.Sparse.eval_collectBalanced, rawRowCheck3831]

def rawRow3832 : Integer.Sparse Key := [(key1552, -6), (key1540, 2), (key1540, 2), (key1385, 2), (key1589, 6), (key1567, -2), (key1567, -2), (key1290, -2), (key1629, -2), (key1629, -2), (key1440, -2), (key1620, 2), (key1620, 2), (key1322, 2)]

theorem rawRowCheck3832 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form4 = rawRow3832 := by decide +kernel

def row3832 : Integer.Sparse Key := [(key1290, -2), (key1322, 2), (key1385, 2), (key1440, -2), (key1540, 4), (key1552, -6), (key1567, -4), (key1589, 6), (key1620, 4), (key1629, -4)]

theorem rowCheck3832 : row3832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3832 := by decide +kernel

theorem rowEval3832 (x : Key → ℝ) : Integer.Sparse.eval row3832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3832, Integer.Sparse.eval_collectBalanced, rawRowCheck3832]

def rawRow3833 : Integer.Sparse Key := [(key1567, -6), (key1418, 2), (key1616, 2), (key1620, 2), (key1540, 6), (key1310, -2), (key1616, -2), (key1629, -2), (key1385, -2), (key1540, -2), (key1552, -2), (key1290, 2), (key1567, 2), (key1589, 2)]

theorem rawRowCheck3833 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form4 = rawRow3833 := by decide +kernel

def row3833 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

theorem rowCheck3833 : row3833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3833 := by decide +kernel

theorem rowEval3833 (x : Key → ℝ) : Integer.Sparse.eval row3833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3833, Integer.Sparse.eval_collectBalanced, rawRowCheck3833]

def rawRow3834 : Integer.Sparse Key := [(key1567, -6), (key1418, 2), (key1620, 2), (key1616, 2), (key1540, 6), (key1310, -2), (key1629, -2), (key1616, -2), (key1385, -2), (key1552, -2), (key1540, -2), (key1290, 2), (key1589, 2), (key1567, 2)]

theorem rawRowCheck3834 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form4 = rawRow3834 := by decide +kernel

def row3834 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

theorem rowCheck3834 : row3834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3834 := by decide +kernel

theorem rowEval3834 (x : Key → ℝ) : Integer.Sparse.eval row3834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3834, Integer.Sparse.eval_collectBalanced, rawRowCheck3834]

def rawRow3835 : Integer.Sparse Key := [(key1567, -6), (key1616, 2), (key1418, 2), (key1620, 2), (key1540, 6), (key1616, -2), (key1310, -2), (key1629, -2), (key1540, -2), (key1385, -2), (key1552, -2), (key1567, 2), (key1290, 2), (key1589, 2)]

theorem rawRowCheck3835 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form4 = rawRow3835 := by decide +kernel

def row3835 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

theorem rowCheck3835 : row3835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3835 := by decide +kernel

theorem rowEval3835 (x : Key → ℝ) : Integer.Sparse.eval row3835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3835, Integer.Sparse.eval_collectBalanced, rawRowCheck3835]

def rawRow3836 : Integer.Sparse Key := [(key1567, -6), (key1616, 2), (key1620, 2), (key1418, 2), (key1540, 6), (key1616, -2), (key1629, -2), (key1310, -2), (key1540, -2), (key1552, -2), (key1385, -2), (key1567, 2), (key1589, 2), (key1290, 2)]

theorem rawRowCheck3836 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form4 = rawRow3836 := by decide +kernel

def row3836 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

theorem rowCheck3836 : row3836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3836 := by decide +kernel

theorem rowEval3836 (x : Key → ℝ) : Integer.Sparse.eval row3836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3836, Integer.Sparse.eval_collectBalanced, rawRowCheck3836]

def rawRow3837 : Integer.Sparse Key := [(key1567, -6), (key1620, 2), (key1418, 2), (key1616, 2), (key1540, 6), (key1629, -2), (key1310, -2), (key1616, -2), (key1552, -2), (key1385, -2), (key1540, -2), (key1589, 2), (key1290, 2), (key1567, 2)]

theorem rawRowCheck3837 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form4 = rawRow3837 := by decide +kernel

def row3837 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

theorem rowCheck3837 : row3837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3837 := by decide +kernel

theorem rowEval3837 (x : Key → ℝ) : Integer.Sparse.eval row3837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3837, Integer.Sparse.eval_collectBalanced, rawRowCheck3837]

def rawRow3838 : Integer.Sparse Key := [(key1567, -6), (key1620, 2), (key1616, 2), (key1418, 2), (key1540, 6), (key1629, -2), (key1616, -2), (key1310, -2), (key1552, -2), (key1540, -2), (key1385, -2), (key1589, 2), (key1567, 2), (key1290, 2)]

theorem rawRowCheck3838 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form4 = rawRow3838 := by decide +kernel

def row3838 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

theorem rowCheck3838 : row3838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3838 := by decide +kernel

theorem rowEval3838 (x : Key → ℝ) : Integer.Sparse.eval row3838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3838, Integer.Sparse.eval_collectBalanced, rawRowCheck3838]

def rawRow3839 : Integer.Sparse Key := [(key1620, -6), (key1418, 2), (key1567, 2), (key1616, 2), (key1629, 6), (key1310, -2), (key1540, -2), (key1616, -2), (key1440, -2), (key1589, -2), (key1629, -2), (key1322, 2), (key1552, 2), (key1620, 2)]

theorem rawRowCheck3839 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form4 = rawRow3839 := by decide +kernel

def row3839 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

theorem rowCheck3839 : row3839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3839 := by decide +kernel

theorem rowEval3839 (x : Key → ℝ) : Integer.Sparse.eval row3839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3839, Integer.Sparse.eval_collectBalanced, rawRowCheck3839]

end MUB6.Certificate.GramRows

end OAI
