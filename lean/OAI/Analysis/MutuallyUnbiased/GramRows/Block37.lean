import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1664 : Integer.Sparse Key := [(key3107, -2), (key3146, -2), (key3116, -2), (key3112, 2), (key3147, 2), (key3117, 2), (key3051, 2), (key3074, 2), (key3057, 2), (key3112, -6), (key2686, -2), (key2719, -2), (key2693, -2), (key2822, 6)]

theorem rawRowCheck1664 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form6 = rawRow1664 := by decide +kernel

def row1664 : Integer.Sparse Key := [(key2686, -2), (key2693, -2), (key2719, -2), (key2822, 6), (key3051, 2), (key3057, 2), (key3074, 2), (key3107, -2), (key3112, -4), (key3116, -2), (key3117, 2), (key3146, -2), (key3147, 2)]

theorem rowCheck1664 : row1664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1664 := by decide +kernel

theorem rowEval1664 (x : Key → ℝ) : Integer.Sparse.eval row1664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1664, Integer.Sparse.eval_collectBalanced, rawRowCheck1664]

def rawRow1665 : Integer.Sparse Key := [(key3146, -2), (key3107, -2), (key3116, -2), (key3147, 2), (key3112, 2), (key3117, 2), (key3074, 2), (key3051, 2), (key3057, 2), (key3112, -6), (key2719, -2), (key2686, -2), (key2693, -2), (key2822, 6)]

theorem rawRowCheck1665 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form6 = rawRow1665 := by decide +kernel

def row1665 : Integer.Sparse Key := [(key2686, -2), (key2693, -2), (key2719, -2), (key2822, 6), (key3051, 2), (key3057, 2), (key3074, 2), (key3107, -2), (key3112, -4), (key3116, -2), (key3117, 2), (key3146, -2), (key3147, 2)]

theorem rowCheck1665 : row1665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1665 := by decide +kernel

theorem rowEval1665 (x : Key → ℝ) : Integer.Sparse.eval row1665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1665, Integer.Sparse.eval_collectBalanced, rawRowCheck1665]

def rawRow1666 : Integer.Sparse Key := [(key3116, -2), (key3146, -2), (key3107, -2), (key3117, 2), (key3147, 2), (key3112, 2), (key3057, 2), (key3074, 2), (key3051, 2), (key3112, -6), (key2693, -2), (key2719, -2), (key2686, -2), (key2822, 6)]

theorem rawRowCheck1666 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form6 = rawRow1666 := by decide +kernel

def row1666 : Integer.Sparse Key := [(key2686, -2), (key2693, -2), (key2719, -2), (key2822, 6), (key3051, 2), (key3057, 2), (key3074, 2), (key3107, -2), (key3112, -4), (key3116, -2), (key3117, 2), (key3146, -2), (key3147, 2)]

theorem rowCheck1666 : row1666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1666 := by decide +kernel

theorem rowEval1666 (x : Key → ℝ) : Integer.Sparse.eval row1666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1666, Integer.Sparse.eval_collectBalanced, rawRowCheck1666]

def rawRow1667 : Integer.Sparse Key := [(key3146, -2), (key3116, -2), (key3107, -2), (key3147, 2), (key3117, 2), (key3112, 2), (key3074, 2), (key3057, 2), (key3051, 2), (key3112, -6), (key2719, -2), (key2693, -2), (key2686, -2), (key2822, 6)]

theorem rawRowCheck1667 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form6 = rawRow1667 := by decide +kernel

def row1667 : Integer.Sparse Key := [(key2686, -2), (key2693, -2), (key2719, -2), (key2822, 6), (key3051, 2), (key3057, 2), (key3074, 2), (key3107, -2), (key3112, -4), (key3116, -2), (key3117, 2), (key3146, -2), (key3147, 2)]

theorem rowCheck1667 : row1667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1667 := by decide +kernel

theorem rowEval1667 (x : Key → ℝ) : Integer.Sparse.eval row1667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1667, Integer.Sparse.eval_collectBalanced, rawRowCheck1667]

def rawRow1668 : Integer.Sparse Key := [(key3055, -2), (key3078, -2), (key3117, -2), (key3057, 2), (key3077, 2), (key3116, 2), (key3051, 2), (key3074, 2), (key3112, 2), (key3057, -6), (key2686, -2), (key2719, -2), (key2822, -2), (key2693, 6)]

theorem rawRowCheck1668 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form6 = rawRow1668 := by decide +kernel

def row1668 : Integer.Sparse Key := [(key2686, -2), (key2693, 6), (key2719, -2), (key2822, -2), (key3051, 2), (key3055, -2), (key3057, -4), (key3074, 2), (key3077, 2), (key3078, -2), (key3112, 2), (key3116, 2), (key3117, -2)]

theorem rowCheck1668 : row1668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1668 := by decide +kernel

theorem rowEval1668 (x : Key → ℝ) : Integer.Sparse.eval row1668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1668, Integer.Sparse.eval_collectBalanced, rawRowCheck1668]

def rawRow1669 : Integer.Sparse Key := [(key3078, -2), (key3055, -2), (key3117, -2), (key3077, 2), (key3057, 2), (key3116, 2), (key3074, 2), (key3051, 2), (key3112, 2), (key3057, -6), (key2719, -2), (key2686, -2), (key2822, -2), (key2693, 6)]

theorem rawRowCheck1669 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form6 = rawRow1669 := by decide +kernel

def row1669 : Integer.Sparse Key := [(key2686, -2), (key2693, 6), (key2719, -2), (key2822, -2), (key3051, 2), (key3055, -2), (key3057, -4), (key3074, 2), (key3077, 2), (key3078, -2), (key3112, 2), (key3116, 2), (key3117, -2)]

theorem rowCheck1669 : row1669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1669 := by decide +kernel

theorem rowEval1669 (x : Key → ℝ) : Integer.Sparse.eval row1669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1669, Integer.Sparse.eval_collectBalanced, rawRowCheck1669]

def rawRow1670 : Integer.Sparse Key := [(key3055, -2), (key3117, -2), (key3078, -2), (key3057, 2), (key3116, 2), (key3077, 2), (key3051, 2), (key3112, 2), (key3074, 2), (key3057, -6), (key2686, -2), (key2822, -2), (key2719, -2), (key2693, 6)]

theorem rawRowCheck1670 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form6 = rawRow1670 := by decide +kernel

def row1670 : Integer.Sparse Key := [(key2686, -2), (key2693, 6), (key2719, -2), (key2822, -2), (key3051, 2), (key3055, -2), (key3057, -4), (key3074, 2), (key3077, 2), (key3078, -2), (key3112, 2), (key3116, 2), (key3117, -2)]

theorem rowCheck1670 : row1670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1670 := by decide +kernel

theorem rowEval1670 (x : Key → ℝ) : Integer.Sparse.eval row1670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1670, Integer.Sparse.eval_collectBalanced, rawRowCheck1670]

def rawRow1671 : Integer.Sparse Key := [(key3117, -2), (key3055, -2), (key3078, -2), (key3116, 2), (key3057, 2), (key3077, 2), (key3112, 2), (key3051, 2), (key3074, 2), (key3057, -6), (key2822, -2), (key2686, -2), (key2719, -2), (key2693, 6)]

theorem rawRowCheck1671 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form6 = rawRow1671 := by decide +kernel

def row1671 : Integer.Sparse Key := [(key2686, -2), (key2693, 6), (key2719, -2), (key2822, -2), (key3051, 2), (key3055, -2), (key3057, -4), (key3074, 2), (key3077, 2), (key3078, -2), (key3112, 2), (key3116, 2), (key3117, -2)]

theorem rowCheck1671 : row1671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1671 := by decide +kernel

theorem rowEval1671 (x : Key → ℝ) : Integer.Sparse.eval row1671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1671, Integer.Sparse.eval_collectBalanced, rawRowCheck1671]

def rawRow1672 : Integer.Sparse Key := [(key3078, -2), (key3117, -2), (key3055, -2), (key3077, 2), (key3116, 2), (key3057, 2), (key3074, 2), (key3112, 2), (key3051, 2), (key3057, -6), (key2719, -2), (key2822, -2), (key2686, -2), (key2693, 6)]

theorem rawRowCheck1672 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form6 = rawRow1672 := by decide +kernel

def row1672 : Integer.Sparse Key := [(key2686, -2), (key2693, 6), (key2719, -2), (key2822, -2), (key3051, 2), (key3055, -2), (key3057, -4), (key3074, 2), (key3077, 2), (key3078, -2), (key3112, 2), (key3116, 2), (key3117, -2)]

theorem rowCheck1672 : row1672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1672 := by decide +kernel

theorem rowEval1672 (x : Key → ℝ) : Integer.Sparse.eval row1672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1672, Integer.Sparse.eval_collectBalanced, rawRowCheck1672]

def rawRow1673 : Integer.Sparse Key := [(key3117, -2), (key3078, -2), (key3055, -2), (key3116, 2), (key3077, 2), (key3057, 2), (key3112, 2), (key3074, 2), (key3051, 2), (key3057, -6), (key2822, -2), (key2719, -2), (key2686, -2), (key2693, 6)]

theorem rawRowCheck1673 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form6 = rawRow1673 := by decide +kernel

def row1673 : Integer.Sparse Key := [(key2686, -2), (key2693, 6), (key2719, -2), (key2822, -2), (key3051, 2), (key3055, -2), (key3057, -4), (key3074, 2), (key3077, 2), (key3078, -2), (key3112, 2), (key3116, 2), (key3117, -2)]

theorem rowCheck1673 : row1673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1673 := by decide +kernel

theorem rowEval1673 (x : Key → ℝ) : Integer.Sparse.eval row1673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1673, Integer.Sparse.eval_collectBalanced, rawRowCheck1673]

def rawRow1674 : Integer.Sparse Key := [(key1316, -2), (key1316, -2), (key1330, -2), (key1296, 1), (key1296, 1), (key1337, 1), (key1337, 1), (key1346, 1), (key1346, 1), (key1546, 2), (key1546, 2), (key1560, 2), (key1391, -1), (key1391, -1), (key1772, -1), (key1772, -1), (key1781, -1), (key1781, -1), (key1573, -1), (key1573, -1), (key1655, -1), (key1655, -1), (key1660, -1), (key1660, -1), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1), (key1818, 1), (key1818, 1)]

theorem rawRowCheck1674 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form7 = rawRow1674 := by decide +kernel

def row1674 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, -2), (key1424, 2), (key1546, 4), (key1560, 2), (key1573, -2), (key1655, -2), (key1660, -2), (key1772, -2), (key1781, -2), (key1813, 2), (key1818, 2)]

theorem rowCheck1674 : row1674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1674 := by decide +kernel

theorem rowEval1674 (x : Key → ℝ) : Integer.Sparse.eval row1674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1674, Integer.Sparse.eval_collectBalanced, rawRowCheck1674]

def rawRow1675 : Integer.Sparse Key := [(key1316, -2), (key1330, -2), (key1316, -2), (key1337, 1), (key1346, 1), (key1296, 1), (key1346, 1), (key1296, 1), (key1337, 1), (key1546, 2), (key1560, 2), (key1546, 2), (key1772, -1), (key1781, -1), (key1391, -1), (key1781, -1), (key1391, -1), (key1772, -1), (key1655, -1), (key1660, -1), (key1573, -1), (key1660, -1), (key1573, -1), (key1655, -1), (key1813, 1), (key1818, 1), (key1424, 1), (key1818, 1), (key1424, 1), (key1813, 1)]

theorem rawRowCheck1675 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form7 = rawRow1675 := by decide +kernel

def row1675 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, -2), (key1424, 2), (key1546, 4), (key1560, 2), (key1573, -2), (key1655, -2), (key1660, -2), (key1772, -2), (key1781, -2), (key1813, 2), (key1818, 2)]

theorem rowCheck1675 : row1675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1675 := by decide +kernel

theorem rowEval1675 (x : Key → ℝ) : Integer.Sparse.eval row1675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1675, Integer.Sparse.eval_collectBalanced, rawRowCheck1675]

def rawRow1676 : Integer.Sparse Key := [(key1330, -2), (key1316, -2), (key1316, -2), (key1346, 1), (key1337, 1), (key1346, 1), (key1296, 1), (key1337, 1), (key1296, 1), (key1560, 2), (key1546, 2), (key1546, 2), (key1781, -1), (key1772, -1), (key1781, -1), (key1391, -1), (key1772, -1), (key1391, -1), (key1660, -1), (key1655, -1), (key1660, -1), (key1573, -1), (key1655, -1), (key1573, -1), (key1818, 1), (key1813, 1), (key1818, 1), (key1424, 1), (key1813, 1), (key1424, 1)]

theorem rawRowCheck1676 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form7 = rawRow1676 := by decide +kernel

def row1676 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, -2), (key1424, 2), (key1546, 4), (key1560, 2), (key1573, -2), (key1655, -2), (key1660, -2), (key1772, -2), (key1781, -2), (key1813, 2), (key1818, 2)]

theorem rowCheck1676 : row1676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1676 := by decide +kernel

theorem rowEval1676 (x : Key → ℝ) : Integer.Sparse.eval row1676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1676, Integer.Sparse.eval_collectBalanced, rawRowCheck1676]

def rawRow1677 : Integer.Sparse Key := [(key1337, -2), (key1340, -2), (key1346, -2), (key1296, 1), (key1303, 1), (key1316, 1), (key1340, 1), (key1330, 1), (key1346, 1), (key1772, 2), (key1775, 2), (key1781, 2), (key1391, -1), (key1398, -1), (key1546, -1), (key1775, -1), (key1560, -1), (key1781, -1), (key1788, -1), (key1791, -1), (key1813, -1), (key1840, -1), (key1818, -1), (key1842, -1), (key1455, 1), (key1458, 1), (key1655, 1), (key1840, 1), (key1660, 1), (key1842, 1)]

theorem rawRowCheck1677 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form7 = rawRow1677 := by decide +kernel

def row1677 : Integer.Sparse Key := [(key1296, 1), (key1303, 1), (key1316, 1), (key1330, 1), (key1337, -2), (key1340, -1), (key1346, -1), (key1391, -1), (key1398, -1), (key1455, 1), (key1458, 1), (key1546, -1), (key1560, -1), (key1655, 1), (key1660, 1), (key1772, 2), (key1775, 1), (key1781, 1), (key1788, -1), (key1791, -1), (key1813, -1), (key1818, -1)]

theorem rowCheck1677 : row1677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1677 := by decide +kernel

theorem rowEval1677 (x : Key → ℝ) : Integer.Sparse.eval row1677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1677, Integer.Sparse.eval_collectBalanced, rawRowCheck1677]

def rawRow1678 : Integer.Sparse Key := [(key1340, -2), (key1337, -2), (key1346, -2), (key1303, 1), (key1296, 1), (key1340, 1), (key1316, 1), (key1346, 1), (key1330, 1), (key1775, 2), (key1772, 2), (key1781, 2), (key1398, -1), (key1391, -1), (key1775, -1), (key1546, -1), (key1781, -1), (key1560, -1), (key1791, -1), (key1788, -1), (key1840, -1), (key1813, -1), (key1842, -1), (key1818, -1), (key1458, 1), (key1455, 1), (key1840, 1), (key1655, 1), (key1842, 1), (key1660, 1)]

theorem rawRowCheck1678 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form7 = rawRow1678 := by decide +kernel

def row1678 : Integer.Sparse Key := [(key1296, 1), (key1303, 1), (key1316, 1), (key1330, 1), (key1337, -2), (key1340, -1), (key1346, -1), (key1391, -1), (key1398, -1), (key1455, 1), (key1458, 1), (key1546, -1), (key1560, -1), (key1655, 1), (key1660, 1), (key1772, 2), (key1775, 1), (key1781, 1), (key1788, -1), (key1791, -1), (key1813, -1), (key1818, -1)]

theorem rowCheck1678 : row1678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1678 := by decide +kernel

theorem rowEval1678 (x : Key → ℝ) : Integer.Sparse.eval row1678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1678, Integer.Sparse.eval_collectBalanced, rawRowCheck1678]

def rawRow1679 : Integer.Sparse Key := [(key1337, -2), (key1346, -2), (key1340, -2), (key1316, 1), (key1330, 1), (key1296, 1), (key1346, 1), (key1303, 1), (key1340, 1), (key1772, 2), (key1781, 2), (key1775, 2), (key1546, -1), (key1560, -1), (key1391, -1), (key1781, -1), (key1398, -1), (key1775, -1), (key1813, -1), (key1818, -1), (key1788, -1), (key1842, -1), (key1791, -1), (key1840, -1), (key1655, 1), (key1660, 1), (key1455, 1), (key1842, 1), (key1458, 1), (key1840, 1)]

theorem rawRowCheck1679 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form7 = rawRow1679 := by decide +kernel

def row1679 : Integer.Sparse Key := [(key1296, 1), (key1303, 1), (key1316, 1), (key1330, 1), (key1337, -2), (key1340, -1), (key1346, -1), (key1391, -1), (key1398, -1), (key1455, 1), (key1458, 1), (key1546, -1), (key1560, -1), (key1655, 1), (key1660, 1), (key1772, 2), (key1775, 1), (key1781, 1), (key1788, -1), (key1791, -1), (key1813, -1), (key1818, -1)]

theorem rowCheck1679 : row1679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1679 := by decide +kernel

theorem rowEval1679 (x : Key → ℝ) : Integer.Sparse.eval row1679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1679, Integer.Sparse.eval_collectBalanced, rawRowCheck1679]

def rawRow1680 : Integer.Sparse Key := [(key1346, -2), (key1337, -2), (key1340, -2), (key1330, 1), (key1316, 1), (key1346, 1), (key1296, 1), (key1340, 1), (key1303, 1), (key1781, 2), (key1772, 2), (key1775, 2), (key1560, -1), (key1546, -1), (key1781, -1), (key1391, -1), (key1775, -1), (key1398, -1), (key1818, -1), (key1813, -1), (key1842, -1), (key1788, -1), (key1840, -1), (key1791, -1), (key1660, 1), (key1655, 1), (key1842, 1), (key1455, 1), (key1840, 1), (key1458, 1)]

theorem rawRowCheck1680 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form7 = rawRow1680 := by decide +kernel

def row1680 : Integer.Sparse Key := [(key1296, 1), (key1303, 1), (key1316, 1), (key1330, 1), (key1337, -2), (key1340, -1), (key1346, -1), (key1391, -1), (key1398, -1), (key1455, 1), (key1458, 1), (key1546, -1), (key1560, -1), (key1655, 1), (key1660, 1), (key1772, 2), (key1775, 1), (key1781, 1), (key1788, -1), (key1791, -1), (key1813, -1), (key1818, -1)]

theorem rowCheck1680 : row1680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1680 := by decide +kernel

theorem rowEval1680 (x : Key → ℝ) : Integer.Sparse.eval row1680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1680, Integer.Sparse.eval_collectBalanced, rawRowCheck1680]

def rawRow1681 : Integer.Sparse Key := [(key1340, -2), (key1346, -2), (key1337, -2), (key1340, 1), (key1346, 1), (key1303, 1), (key1330, 1), (key1296, 1), (key1316, 1), (key1775, 2), (key1781, 2), (key1772, 2), (key1775, -1), (key1781, -1), (key1398, -1), (key1560, -1), (key1391, -1), (key1546, -1), (key1840, -1), (key1842, -1), (key1791, -1), (key1818, -1), (key1788, -1), (key1813, -1), (key1840, 1), (key1842, 1), (key1458, 1), (key1660, 1), (key1455, 1), (key1655, 1)]

theorem rawRowCheck1681 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form7 = rawRow1681 := by decide +kernel

def row1681 : Integer.Sparse Key := [(key1296, 1), (key1303, 1), (key1316, 1), (key1330, 1), (key1337, -2), (key1340, -1), (key1346, -1), (key1391, -1), (key1398, -1), (key1455, 1), (key1458, 1), (key1546, -1), (key1560, -1), (key1655, 1), (key1660, 1), (key1772, 2), (key1775, 1), (key1781, 1), (key1788, -1), (key1791, -1), (key1813, -1), (key1818, -1)]

theorem rowCheck1681 : row1681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1681 := by decide +kernel

theorem rowEval1681 (x : Key → ℝ) : Integer.Sparse.eval row1681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1681, Integer.Sparse.eval_collectBalanced, rawRowCheck1681]

def rawRow1682 : Integer.Sparse Key := [(key1346, -2), (key1340, -2), (key1337, -2), (key1346, 1), (key1340, 1), (key1330, 1), (key1303, 1), (key1316, 1), (key1296, 1), (key1781, 2), (key1775, 2), (key1772, 2), (key1781, -1), (key1775, -1), (key1560, -1), (key1398, -1), (key1546, -1), (key1391, -1), (key1842, -1), (key1840, -1), (key1818, -1), (key1791, -1), (key1813, -1), (key1788, -1), (key1842, 1), (key1840, 1), (key1660, 1), (key1458, 1), (key1655, 1), (key1455, 1)]

theorem rawRowCheck1682 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form7 = rawRow1682 := by decide +kernel

def row1682 : Integer.Sparse Key := [(key1296, 1), (key1303, 1), (key1316, 1), (key1330, 1), (key1337, -2), (key1340, -1), (key1346, -1), (key1391, -1), (key1398, -1), (key1455, 1), (key1458, 1), (key1546, -1), (key1560, -1), (key1655, 1), (key1660, 1), (key1772, 2), (key1775, 1), (key1781, 1), (key1788, -1), (key1791, -1), (key1813, -1), (key1818, -1)]

theorem rowCheck1682 : row1682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1682 := by decide +kernel

theorem rowEval1682 (x : Key → ℝ) : Integer.Sparse.eval row1682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1682, Integer.Sparse.eval_collectBalanced, rawRowCheck1682]

def rawRow1683 : Integer.Sparse Key := [(key1546, -2), (key1546, -2), (key1560, -2), (key1573, 1), (key1573, 1), (key1655, 1), (key1655, 1), (key1660, 1), (key1660, 1), (key1316, 2), (key1316, 2), (key1330, 2), (key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1818, -1), (key1818, -1), (key1296, -1), (key1296, -1), (key1337, -1), (key1337, -1), (key1346, -1), (key1346, -1), (key1391, 1), (key1391, 1), (key1772, 1), (key1772, 1), (key1781, 1), (key1781, 1)]

theorem rawRowCheck1683 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form7 = rawRow1683 := by decide +kernel

def row1683 : Integer.Sparse Key := [(key1296, -2), (key1316, 4), (key1330, 2), (key1337, -2), (key1346, -2), (key1391, 2), (key1424, -2), (key1546, -4), (key1560, -2), (key1573, 2), (key1655, 2), (key1660, 2), (key1772, 2), (key1781, 2), (key1813, -2), (key1818, -2)]

theorem rowCheck1683 : row1683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1683 := by decide +kernel

theorem rowEval1683 (x : Key → ℝ) : Integer.Sparse.eval row1683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1683, Integer.Sparse.eval_collectBalanced, rawRowCheck1683]

def rawRow1684 : Integer.Sparse Key := [(key1546, -2), (key1560, -2), (key1546, -2), (key1655, 1), (key1660, 1), (key1573, 1), (key1660, 1), (key1573, 1), (key1655, 1), (key1316, 2), (key1330, 2), (key1316, 2), (key1813, -1), (key1818, -1), (key1424, -1), (key1818, -1), (key1424, -1), (key1813, -1), (key1337, -1), (key1346, -1), (key1296, -1), (key1346, -1), (key1296, -1), (key1337, -1), (key1772, 1), (key1781, 1), (key1391, 1), (key1781, 1), (key1391, 1), (key1772, 1)]

theorem rawRowCheck1684 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form7 = rawRow1684 := by decide +kernel

def row1684 : Integer.Sparse Key := [(key1296, -2), (key1316, 4), (key1330, 2), (key1337, -2), (key1346, -2), (key1391, 2), (key1424, -2), (key1546, -4), (key1560, -2), (key1573, 2), (key1655, 2), (key1660, 2), (key1772, 2), (key1781, 2), (key1813, -2), (key1818, -2)]

theorem rowCheck1684 : row1684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1684 := by decide +kernel

theorem rowEval1684 (x : Key → ℝ) : Integer.Sparse.eval row1684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1684, Integer.Sparse.eval_collectBalanced, rawRowCheck1684]

def rawRow1685 : Integer.Sparse Key := [(key1560, -2), (key1546, -2), (key1546, -2), (key1660, 1), (key1655, 1), (key1660, 1), (key1573, 1), (key1655, 1), (key1573, 1), (key1330, 2), (key1316, 2), (key1316, 2), (key1818, -1), (key1813, -1), (key1818, -1), (key1424, -1), (key1813, -1), (key1424, -1), (key1346, -1), (key1337, -1), (key1346, -1), (key1296, -1), (key1337, -1), (key1296, -1), (key1781, 1), (key1772, 1), (key1781, 1), (key1391, 1), (key1772, 1), (key1391, 1)]

theorem rawRowCheck1685 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form7 = rawRow1685 := by decide +kernel

def row1685 : Integer.Sparse Key := [(key1296, -2), (key1316, 4), (key1330, 2), (key1337, -2), (key1346, -2), (key1391, 2), (key1424, -2), (key1546, -4), (key1560, -2), (key1573, 2), (key1655, 2), (key1660, 2), (key1772, 2), (key1781, 2), (key1813, -2), (key1818, -2)]

theorem rowCheck1685 : row1685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1685 := by decide +kernel

theorem rowEval1685 (x : Key → ℝ) : Integer.Sparse.eval row1685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1685, Integer.Sparse.eval_collectBalanced, rawRowCheck1685]

def rawRow1686 : Integer.Sparse Key := [(key1655, -2), (key1660, -2), (key1668, -2), (key1546, 1), (key1560, 1), (key1573, 1), (key1660, 1), (key1597, 1), (key1668, 1), (key1813, 2), (key1818, 2), (key1826, 2), (key1316, -1), (key1330, -1), (key1424, -1), (key1818, -1), (key1448, -1), (key1826, -1), (key1772, -1), (key1781, -1), (key1788, -1), (key1842, -1), (key1799, -1), (key1845, -1), (key1337, 1), (key1346, 1), (key1455, 1), (key1842, 1), (key1467, 1), (key1845, 1)]

theorem rawRowCheck1686 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form7 = rawRow1686 := by decide +kernel

def row1686 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1337, 1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1546, 1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, -1), (key1668, -1), (key1772, -1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 2), (key1818, 1), (key1826, 1)]

theorem rowCheck1686 : row1686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1686 := by decide +kernel

theorem rowEval1686 (x : Key → ℝ) : Integer.Sparse.eval row1686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1686, Integer.Sparse.eval_collectBalanced, rawRowCheck1686]

def rawRow1687 : Integer.Sparse Key := [(key1660, -2), (key1655, -2), (key1668, -2), (key1560, 1), (key1546, 1), (key1660, 1), (key1573, 1), (key1668, 1), (key1597, 1), (key1818, 2), (key1813, 2), (key1826, 2), (key1330, -1), (key1316, -1), (key1818, -1), (key1424, -1), (key1826, -1), (key1448, -1), (key1781, -1), (key1772, -1), (key1842, -1), (key1788, -1), (key1845, -1), (key1799, -1), (key1346, 1), (key1337, 1), (key1842, 1), (key1455, 1), (key1845, 1), (key1467, 1)]

theorem rawRowCheck1687 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form7 = rawRow1687 := by decide +kernel

def row1687 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1337, 1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1546, 1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, -1), (key1668, -1), (key1772, -1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 2), (key1818, 1), (key1826, 1)]

theorem rowCheck1687 : row1687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1687 := by decide +kernel

theorem rowEval1687 (x : Key → ℝ) : Integer.Sparse.eval row1687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1687, Integer.Sparse.eval_collectBalanced, rawRowCheck1687]

def rawRow1688 : Integer.Sparse Key := [(key1655, -2), (key1668, -2), (key1660, -2), (key1573, 1), (key1597, 1), (key1546, 1), (key1668, 1), (key1560, 1), (key1660, 1), (key1813, 2), (key1826, 2), (key1818, 2), (key1424, -1), (key1448, -1), (key1316, -1), (key1826, -1), (key1330, -1), (key1818, -1), (key1788, -1), (key1799, -1), (key1772, -1), (key1845, -1), (key1781, -1), (key1842, -1), (key1455, 1), (key1467, 1), (key1337, 1), (key1845, 1), (key1346, 1), (key1842, 1)]

theorem rawRowCheck1688 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form7 = rawRow1688 := by decide +kernel

def row1688 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1337, 1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1546, 1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, -1), (key1668, -1), (key1772, -1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 2), (key1818, 1), (key1826, 1)]

theorem rowCheck1688 : row1688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1688 := by decide +kernel

theorem rowEval1688 (x : Key → ℝ) : Integer.Sparse.eval row1688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1688, Integer.Sparse.eval_collectBalanced, rawRowCheck1688]

def rawRow1689 : Integer.Sparse Key := [(key1668, -2), (key1655, -2), (key1660, -2), (key1597, 1), (key1573, 1), (key1668, 1), (key1546, 1), (key1660, 1), (key1560, 1), (key1826, 2), (key1813, 2), (key1818, 2), (key1448, -1), (key1424, -1), (key1826, -1), (key1316, -1), (key1818, -1), (key1330, -1), (key1799, -1), (key1788, -1), (key1845, -1), (key1772, -1), (key1842, -1), (key1781, -1), (key1467, 1), (key1455, 1), (key1845, 1), (key1337, 1), (key1842, 1), (key1346, 1)]

theorem rawRowCheck1689 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form7 = rawRow1689 := by decide +kernel

def row1689 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1337, 1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1546, 1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, -1), (key1668, -1), (key1772, -1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 2), (key1818, 1), (key1826, 1)]

theorem rowCheck1689 : row1689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1689 := by decide +kernel

theorem rowEval1689 (x : Key → ℝ) : Integer.Sparse.eval row1689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1689, Integer.Sparse.eval_collectBalanced, rawRowCheck1689]

def rawRow1690 : Integer.Sparse Key := [(key1660, -2), (key1668, -2), (key1655, -2), (key1660, 1), (key1668, 1), (key1560, 1), (key1597, 1), (key1546, 1), (key1573, 1), (key1818, 2), (key1826, 2), (key1813, 2), (key1818, -1), (key1826, -1), (key1330, -1), (key1448, -1), (key1316, -1), (key1424, -1), (key1842, -1), (key1845, -1), (key1781, -1), (key1799, -1), (key1772, -1), (key1788, -1), (key1842, 1), (key1845, 1), (key1346, 1), (key1467, 1), (key1337, 1), (key1455, 1)]

theorem rawRowCheck1690 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form7 = rawRow1690 := by decide +kernel

def row1690 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1337, 1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1546, 1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, -1), (key1668, -1), (key1772, -1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 2), (key1818, 1), (key1826, 1)]

theorem rowCheck1690 : row1690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1690 := by decide +kernel

theorem rowEval1690 (x : Key → ℝ) : Integer.Sparse.eval row1690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1690, Integer.Sparse.eval_collectBalanced, rawRowCheck1690]

def rawRow1691 : Integer.Sparse Key := [(key1668, -2), (key1660, -2), (key1655, -2), (key1668, 1), (key1660, 1), (key1597, 1), (key1560, 1), (key1573, 1), (key1546, 1), (key1826, 2), (key1818, 2), (key1813, 2), (key1826, -1), (key1818, -1), (key1448, -1), (key1330, -1), (key1424, -1), (key1316, -1), (key1845, -1), (key1842, -1), (key1799, -1), (key1781, -1), (key1788, -1), (key1772, -1), (key1845, 1), (key1842, 1), (key1467, 1), (key1346, 1), (key1455, 1), (key1337, 1)]

theorem rawRowCheck1691 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form7 = rawRow1691 := by decide +kernel

def row1691 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1337, 1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1546, 1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, -1), (key1668, -1), (key1772, -1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 2), (key1818, 1), (key1826, 1)]

theorem rowCheck1691 : row1691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1691 := by decide +kernel

theorem rowEval1691 (x : Key → ℝ) : Integer.Sparse.eval row1691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1691, Integer.Sparse.eval_collectBalanced, rawRowCheck1691]

def rawRow1692 : Integer.Sparse Key := [(key1772, -2), (key1775, -2), (key1781, -2), (key1788, 1), (key1791, 1), (key1813, 1), (key1840, 1), (key1818, 1), (key1842, 1), (key1337, 2), (key1340, 2), (key1346, 2), (key1455, -1), (key1458, -1), (key1655, -1), (key1840, -1), (key1660, -1), (key1842, -1), (key1296, -1), (key1303, -1), (key1316, -1), (key1340, -1), (key1330, -1), (key1346, -1), (key1391, 1), (key1398, 1), (key1546, 1), (key1775, 1), (key1560, 1), (key1781, 1)]

theorem rawRowCheck1692 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form7 = rawRow1692 := by decide +kernel

def row1692 : Integer.Sparse Key := [(key1296, -1), (key1303, -1), (key1316, -1), (key1330, -1), (key1337, 2), (key1340, 1), (key1346, 1), (key1391, 1), (key1398, 1), (key1455, -1), (key1458, -1), (key1546, 1), (key1560, 1), (key1655, -1), (key1660, -1), (key1772, -2), (key1775, -1), (key1781, -1), (key1788, 1), (key1791, 1), (key1813, 1), (key1818, 1)]

theorem rowCheck1692 : row1692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1692 := by decide +kernel

theorem rowEval1692 (x : Key → ℝ) : Integer.Sparse.eval row1692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1692, Integer.Sparse.eval_collectBalanced, rawRowCheck1692]

def rawRow1693 : Integer.Sparse Key := [(key1775, -2), (key1772, -2), (key1781, -2), (key1791, 1), (key1788, 1), (key1840, 1), (key1813, 1), (key1842, 1), (key1818, 1), (key1340, 2), (key1337, 2), (key1346, 2), (key1458, -1), (key1455, -1), (key1840, -1), (key1655, -1), (key1842, -1), (key1660, -1), (key1303, -1), (key1296, -1), (key1340, -1), (key1316, -1), (key1346, -1), (key1330, -1), (key1398, 1), (key1391, 1), (key1775, 1), (key1546, 1), (key1781, 1), (key1560, 1)]

theorem rawRowCheck1693 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form7 = rawRow1693 := by decide +kernel

def row1693 : Integer.Sparse Key := [(key1296, -1), (key1303, -1), (key1316, -1), (key1330, -1), (key1337, 2), (key1340, 1), (key1346, 1), (key1391, 1), (key1398, 1), (key1455, -1), (key1458, -1), (key1546, 1), (key1560, 1), (key1655, -1), (key1660, -1), (key1772, -2), (key1775, -1), (key1781, -1), (key1788, 1), (key1791, 1), (key1813, 1), (key1818, 1)]

theorem rowCheck1693 : row1693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1693 := by decide +kernel

theorem rowEval1693 (x : Key → ℝ) : Integer.Sparse.eval row1693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1693, Integer.Sparse.eval_collectBalanced, rawRowCheck1693]

def rawRow1694 : Integer.Sparse Key := [(key1772, -2), (key1781, -2), (key1775, -2), (key1813, 1), (key1818, 1), (key1788, 1), (key1842, 1), (key1791, 1), (key1840, 1), (key1337, 2), (key1346, 2), (key1340, 2), (key1655, -1), (key1660, -1), (key1455, -1), (key1842, -1), (key1458, -1), (key1840, -1), (key1316, -1), (key1330, -1), (key1296, -1), (key1346, -1), (key1303, -1), (key1340, -1), (key1546, 1), (key1560, 1), (key1391, 1), (key1781, 1), (key1398, 1), (key1775, 1)]

theorem rawRowCheck1694 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form7 = rawRow1694 := by decide +kernel

def row1694 : Integer.Sparse Key := [(key1296, -1), (key1303, -1), (key1316, -1), (key1330, -1), (key1337, 2), (key1340, 1), (key1346, 1), (key1391, 1), (key1398, 1), (key1455, -1), (key1458, -1), (key1546, 1), (key1560, 1), (key1655, -1), (key1660, -1), (key1772, -2), (key1775, -1), (key1781, -1), (key1788, 1), (key1791, 1), (key1813, 1), (key1818, 1)]

theorem rowCheck1694 : row1694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1694 := by decide +kernel

theorem rowEval1694 (x : Key → ℝ) : Integer.Sparse.eval row1694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1694, Integer.Sparse.eval_collectBalanced, rawRowCheck1694]

def rawRow1695 : Integer.Sparse Key := [(key1781, -2), (key1772, -2), (key1775, -2), (key1818, 1), (key1813, 1), (key1842, 1), (key1788, 1), (key1840, 1), (key1791, 1), (key1346, 2), (key1337, 2), (key1340, 2), (key1660, -1), (key1655, -1), (key1842, -1), (key1455, -1), (key1840, -1), (key1458, -1), (key1330, -1), (key1316, -1), (key1346, -1), (key1296, -1), (key1340, -1), (key1303, -1), (key1560, 1), (key1546, 1), (key1781, 1), (key1391, 1), (key1775, 1), (key1398, 1)]

theorem rawRowCheck1695 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form7 = rawRow1695 := by decide +kernel

def row1695 : Integer.Sparse Key := [(key1296, -1), (key1303, -1), (key1316, -1), (key1330, -1), (key1337, 2), (key1340, 1), (key1346, 1), (key1391, 1), (key1398, 1), (key1455, -1), (key1458, -1), (key1546, 1), (key1560, 1), (key1655, -1), (key1660, -1), (key1772, -2), (key1775, -1), (key1781, -1), (key1788, 1), (key1791, 1), (key1813, 1), (key1818, 1)]

theorem rowCheck1695 : row1695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1695 := by decide +kernel

theorem rowEval1695 (x : Key → ℝ) : Integer.Sparse.eval row1695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1695, Integer.Sparse.eval_collectBalanced, rawRowCheck1695]

def rawRow1696 : Integer.Sparse Key := [(key1775, -2), (key1781, -2), (key1772, -2), (key1840, 1), (key1842, 1), (key1791, 1), (key1818, 1), (key1788, 1), (key1813, 1), (key1340, 2), (key1346, 2), (key1337, 2), (key1840, -1), (key1842, -1), (key1458, -1), (key1660, -1), (key1455, -1), (key1655, -1), (key1340, -1), (key1346, -1), (key1303, -1), (key1330, -1), (key1296, -1), (key1316, -1), (key1775, 1), (key1781, 1), (key1398, 1), (key1560, 1), (key1391, 1), (key1546, 1)]

theorem rawRowCheck1696 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form7 = rawRow1696 := by decide +kernel

def row1696 : Integer.Sparse Key := [(key1296, -1), (key1303, -1), (key1316, -1), (key1330, -1), (key1337, 2), (key1340, 1), (key1346, 1), (key1391, 1), (key1398, 1), (key1455, -1), (key1458, -1), (key1546, 1), (key1560, 1), (key1655, -1), (key1660, -1), (key1772, -2), (key1775, -1), (key1781, -1), (key1788, 1), (key1791, 1), (key1813, 1), (key1818, 1)]

theorem rowCheck1696 : row1696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1696 := by decide +kernel

theorem rowEval1696 (x : Key → ℝ) : Integer.Sparse.eval row1696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1696, Integer.Sparse.eval_collectBalanced, rawRowCheck1696]

def rawRow1697 : Integer.Sparse Key := [(key1781, -2), (key1775, -2), (key1772, -2), (key1842, 1), (key1840, 1), (key1818, 1), (key1791, 1), (key1813, 1), (key1788, 1), (key1346, 2), (key1340, 2), (key1337, 2), (key1842, -1), (key1840, -1), (key1660, -1), (key1458, -1), (key1655, -1), (key1455, -1), (key1346, -1), (key1340, -1), (key1330, -1), (key1303, -1), (key1316, -1), (key1296, -1), (key1781, 1), (key1775, 1), (key1560, 1), (key1398, 1), (key1546, 1), (key1391, 1)]

theorem rawRowCheck1697 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form7 = rawRow1697 := by decide +kernel

def row1697 : Integer.Sparse Key := [(key1296, -1), (key1303, -1), (key1316, -1), (key1330, -1), (key1337, 2), (key1340, 1), (key1346, 1), (key1391, 1), (key1398, 1), (key1455, -1), (key1458, -1), (key1546, 1), (key1560, 1), (key1655, -1), (key1660, -1), (key1772, -2), (key1775, -1), (key1781, -1), (key1788, 1), (key1791, 1), (key1813, 1), (key1818, 1)]

theorem rowCheck1697 : row1697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1697 := by decide +kernel

theorem rowEval1697 (x : Key → ℝ) : Integer.Sparse.eval row1697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1697, Integer.Sparse.eval_collectBalanced, rawRowCheck1697]

def rawRow1698 : Integer.Sparse Key := [(key1813, -2), (key1818, -2), (key1826, -2), (key1772, 1), (key1781, 1), (key1788, 1), (key1842, 1), (key1799, 1), (key1845, 1), (key1655, 2), (key1660, 2), (key1668, 2), (key1337, -1), (key1346, -1), (key1455, -1), (key1842, -1), (key1467, -1), (key1845, -1), (key1546, -1), (key1560, -1), (key1573, -1), (key1660, -1), (key1597, -1), (key1668, -1), (key1316, 1), (key1330, 1), (key1424, 1), (key1818, 1), (key1448, 1), (key1826, 1)]

theorem rawRowCheck1698 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form7 = rawRow1698 := by decide +kernel

def row1698 : Integer.Sparse Key := [(key1316, 1), (key1330, 1), (key1337, -1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1546, -1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, 1), (key1668, 1), (key1772, 1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -2), (key1818, -1), (key1826, -1)]

theorem rowCheck1698 : row1698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1698 := by decide +kernel

theorem rowEval1698 (x : Key → ℝ) : Integer.Sparse.eval row1698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1698, Integer.Sparse.eval_collectBalanced, rawRowCheck1698]

def rawRow1699 : Integer.Sparse Key := [(key1818, -2), (key1813, -2), (key1826, -2), (key1781, 1), (key1772, 1), (key1842, 1), (key1788, 1), (key1845, 1), (key1799, 1), (key1660, 2), (key1655, 2), (key1668, 2), (key1346, -1), (key1337, -1), (key1842, -1), (key1455, -1), (key1845, -1), (key1467, -1), (key1560, -1), (key1546, -1), (key1660, -1), (key1573, -1), (key1668, -1), (key1597, -1), (key1330, 1), (key1316, 1), (key1818, 1), (key1424, 1), (key1826, 1), (key1448, 1)]

theorem rawRowCheck1699 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form7 = rawRow1699 := by decide +kernel

def row1699 : Integer.Sparse Key := [(key1316, 1), (key1330, 1), (key1337, -1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1546, -1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, 1), (key1668, 1), (key1772, 1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -2), (key1818, -1), (key1826, -1)]

theorem rowCheck1699 : row1699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1699 := by decide +kernel

theorem rowEval1699 (x : Key → ℝ) : Integer.Sparse.eval row1699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1699, Integer.Sparse.eval_collectBalanced, rawRowCheck1699]

def rawRow1700 : Integer.Sparse Key := [(key1813, -2), (key1826, -2), (key1818, -2), (key1788, 1), (key1799, 1), (key1772, 1), (key1845, 1), (key1781, 1), (key1842, 1), (key1655, 2), (key1668, 2), (key1660, 2), (key1455, -1), (key1467, -1), (key1337, -1), (key1845, -1), (key1346, -1), (key1842, -1), (key1573, -1), (key1597, -1), (key1546, -1), (key1668, -1), (key1560, -1), (key1660, -1), (key1424, 1), (key1448, 1), (key1316, 1), (key1826, 1), (key1330, 1), (key1818, 1)]

theorem rawRowCheck1700 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form7 = rawRow1700 := by decide +kernel

def row1700 : Integer.Sparse Key := [(key1316, 1), (key1330, 1), (key1337, -1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1546, -1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, 1), (key1668, 1), (key1772, 1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -2), (key1818, -1), (key1826, -1)]

theorem rowCheck1700 : row1700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1700 := by decide +kernel

theorem rowEval1700 (x : Key → ℝ) : Integer.Sparse.eval row1700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1700, Integer.Sparse.eval_collectBalanced, rawRowCheck1700]

def rawRow1701 : Integer.Sparse Key := [(key1826, -2), (key1813, -2), (key1818, -2), (key1799, 1), (key1788, 1), (key1845, 1), (key1772, 1), (key1842, 1), (key1781, 1), (key1668, 2), (key1655, 2), (key1660, 2), (key1467, -1), (key1455, -1), (key1845, -1), (key1337, -1), (key1842, -1), (key1346, -1), (key1597, -1), (key1573, -1), (key1668, -1), (key1546, -1), (key1660, -1), (key1560, -1), (key1448, 1), (key1424, 1), (key1826, 1), (key1316, 1), (key1818, 1), (key1330, 1)]

theorem rawRowCheck1701 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form7 = rawRow1701 := by decide +kernel

def row1701 : Integer.Sparse Key := [(key1316, 1), (key1330, 1), (key1337, -1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1546, -1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, 1), (key1668, 1), (key1772, 1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -2), (key1818, -1), (key1826, -1)]

theorem rowCheck1701 : row1701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1701 := by decide +kernel

theorem rowEval1701 (x : Key → ℝ) : Integer.Sparse.eval row1701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1701, Integer.Sparse.eval_collectBalanced, rawRowCheck1701]

def rawRow1702 : Integer.Sparse Key := [(key1818, -2), (key1826, -2), (key1813, -2), (key1842, 1), (key1845, 1), (key1781, 1), (key1799, 1), (key1772, 1), (key1788, 1), (key1660, 2), (key1668, 2), (key1655, 2), (key1842, -1), (key1845, -1), (key1346, -1), (key1467, -1), (key1337, -1), (key1455, -1), (key1660, -1), (key1668, -1), (key1560, -1), (key1597, -1), (key1546, -1), (key1573, -1), (key1818, 1), (key1826, 1), (key1330, 1), (key1448, 1), (key1316, 1), (key1424, 1)]

theorem rawRowCheck1702 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form7 = rawRow1702 := by decide +kernel

def row1702 : Integer.Sparse Key := [(key1316, 1), (key1330, 1), (key1337, -1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1546, -1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, 1), (key1668, 1), (key1772, 1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -2), (key1818, -1), (key1826, -1)]

theorem rowCheck1702 : row1702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1702 := by decide +kernel

theorem rowEval1702 (x : Key → ℝ) : Integer.Sparse.eval row1702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1702, Integer.Sparse.eval_collectBalanced, rawRowCheck1702]

def rawRow1703 : Integer.Sparse Key := [(key1826, -2), (key1818, -2), (key1813, -2), (key1845, 1), (key1842, 1), (key1799, 1), (key1781, 1), (key1788, 1), (key1772, 1), (key1668, 2), (key1660, 2), (key1655, 2), (key1845, -1), (key1842, -1), (key1467, -1), (key1346, -1), (key1455, -1), (key1337, -1), (key1668, -1), (key1660, -1), (key1597, -1), (key1560, -1), (key1573, -1), (key1546, -1), (key1826, 1), (key1818, 1), (key1448, 1), (key1330, 1), (key1424, 1), (key1316, 1)]

theorem rawRowCheck1703 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form7 = rawRow1703 := by decide +kernel

def row1703 : Integer.Sparse Key := [(key1316, 1), (key1330, 1), (key1337, -1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1546, -1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, 1), (key1668, 1), (key1772, 1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -2), (key1818, -1), (key1826, -1)]

theorem rowCheck1703 : row1703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1703 := by decide +kernel

theorem rowEval1703 (x : Key → ℝ) : Integer.Sparse.eval row1703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1703, Integer.Sparse.eval_collectBalanced, rawRowCheck1703]

def rawRow1704 : Integer.Sparse Key := [(key998, -2), (key998, -2), (key1018, -2), (key1005, 6), (key1111, 2), (key1111, 2), (key1126, 2), (key1040, -2), (key1192, -2), (key1192, -2), (key1154, -6), (key1075, 2), (key1211, 2), (key1211, 2)]

theorem rawRowCheck1704 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form8 = rawRow1704 := by decide +kernel

def row1704 : Integer.Sparse Key := [(key998, -4), (key1005, 6), (key1018, -2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, 2), (key1154, -6), (key1192, -4), (key1211, 4)]

theorem rowCheck1704 : row1704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1704 := by decide +kernel

theorem rowEval1704 (x : Key → ℝ) : Integer.Sparse.eval row1704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1704, Integer.Sparse.eval_collectBalanced, rawRowCheck1704]

def rawRow1705 : Integer.Sparse Key := [(key998, -2), (key1018, -2), (key998, -2), (key1005, 6), (key1111, 2), (key1126, 2), (key1111, 2), (key1192, -2), (key1040, -2), (key1192, -2), (key1154, -6), (key1211, 2), (key1075, 2), (key1211, 2)]

theorem rawRowCheck1705 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form8 = rawRow1705 := by decide +kernel

def row1705 : Integer.Sparse Key := [(key998, -4), (key1005, 6), (key1018, -2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, 2), (key1154, -6), (key1192, -4), (key1211, 4)]

theorem rowCheck1705 : row1705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1705 := by decide +kernel

theorem rowEval1705 (x : Key → ℝ) : Integer.Sparse.eval row1705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1705, Integer.Sparse.eval_collectBalanced, rawRowCheck1705]

def rawRow1706 : Integer.Sparse Key := [(key1018, -2), (key998, -2), (key998, -2), (key1005, 6), (key1126, 2), (key1111, 2), (key1111, 2), (key1192, -2), (key1192, -2), (key1040, -2), (key1154, -6), (key1211, 2), (key1211, 2), (key1075, 2)]

theorem rawRowCheck1706 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form8 = rawRow1706 := by decide +kernel

def row1706 : Integer.Sparse Key := [(key998, -4), (key1005, 6), (key1018, -2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, 2), (key1154, -6), (key1192, -4), (key1211, 4)]

theorem rowCheck1706 : row1706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1706 := by decide +kernel

theorem rowEval1706 (x : Key → ℝ) : Integer.Sparse.eval row1706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1706, Integer.Sparse.eval_collectBalanced, rawRowCheck1706]

def rawRow1707 : Integer.Sparse Key := [(key998, -2), (key1005, -2), (key1018, -2), (key998, 6), (key1190, 2), (key1192, 2), (key1198, 2), (key1033, -2), (key1111, -2), (key1190, -2), (key1211, -6), (key1075, 2), (key1154, 2), (key1211, 2)]

theorem rawRowCheck1707 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form8 = rawRow1707 := by decide +kernel

def row1707 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -2), (key1075, 2), (key1111, -2), (key1154, 2), (key1192, 2), (key1198, 2), (key1211, -4)]

theorem rowCheck1707 : row1707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1707 := by decide +kernel

theorem rowEval1707 (x : Key → ℝ) : Integer.Sparse.eval row1707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1707, Integer.Sparse.eval_collectBalanced, rawRowCheck1707]

def rawRow1708 : Integer.Sparse Key := [(key1005, -2), (key998, -2), (key1018, -2), (key998, 6), (key1192, 2), (key1190, 2), (key1198, 2), (key1033, -2), (key1190, -2), (key1111, -2), (key1211, -6), (key1075, 2), (key1211, 2), (key1154, 2)]

theorem rawRowCheck1708 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form8 = rawRow1708 := by decide +kernel

def row1708 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -2), (key1075, 2), (key1111, -2), (key1154, 2), (key1192, 2), (key1198, 2), (key1211, -4)]

theorem rowCheck1708 : row1708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1708 := by decide +kernel

theorem rowEval1708 (x : Key → ℝ) : Integer.Sparse.eval row1708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1708, Integer.Sparse.eval_collectBalanced, rawRowCheck1708]

def rawRow1709 : Integer.Sparse Key := [(key998, -2), (key1018, -2), (key1005, -2), (key998, 6), (key1190, 2), (key1198, 2), (key1192, 2), (key1111, -2), (key1033, -2), (key1190, -2), (key1211, -6), (key1154, 2), (key1075, 2), (key1211, 2)]

theorem rawRowCheck1709 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form8 = rawRow1709 := by decide +kernel

def row1709 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -2), (key1075, 2), (key1111, -2), (key1154, 2), (key1192, 2), (key1198, 2), (key1211, -4)]

theorem rowCheck1709 : row1709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1709 := by decide +kernel

theorem rowEval1709 (x : Key → ℝ) : Integer.Sparse.eval row1709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1709, Integer.Sparse.eval_collectBalanced, rawRowCheck1709]

def rawRow1710 : Integer.Sparse Key := [(key1018, -2), (key998, -2), (key1005, -2), (key998, 6), (key1198, 2), (key1190, 2), (key1192, 2), (key1111, -2), (key1190, -2), (key1033, -2), (key1211, -6), (key1154, 2), (key1211, 2), (key1075, 2)]

theorem rawRowCheck1710 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form8 = rawRow1710 := by decide +kernel

def row1710 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -2), (key1075, 2), (key1111, -2), (key1154, 2), (key1192, 2), (key1198, 2), (key1211, -4)]

theorem rowCheck1710 : row1710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1710 := by decide +kernel

theorem rowEval1710 (x : Key → ℝ) : Integer.Sparse.eval row1710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1710, Integer.Sparse.eval_collectBalanced, rawRowCheck1710]

def rawRow1711 : Integer.Sparse Key := [(key1005, -2), (key1018, -2), (key998, -2), (key998, 6), (key1192, 2), (key1198, 2), (key1190, 2), (key1190, -2), (key1033, -2), (key1111, -2), (key1211, -6), (key1211, 2), (key1075, 2), (key1154, 2)]

theorem rawRowCheck1711 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form8 = rawRow1711 := by decide +kernel

def row1711 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -2), (key1075, 2), (key1111, -2), (key1154, 2), (key1192, 2), (key1198, 2), (key1211, -4)]

theorem rowCheck1711 : row1711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1711 := by decide +kernel

theorem rowEval1711 (x : Key → ℝ) : Integer.Sparse.eval row1711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1711, Integer.Sparse.eval_collectBalanced, rawRowCheck1711]

def rawRow1712 : Integer.Sparse Key := [(key1018, -2), (key1005, -2), (key998, -2), (key998, 6), (key1198, 2), (key1192, 2), (key1190, 2), (key1190, -2), (key1111, -2), (key1033, -2), (key1211, -6), (key1211, 2), (key1154, 2), (key1075, 2)]

theorem rawRowCheck1712 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form8 = rawRow1712 := by decide +kernel

def row1712 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -2), (key1075, 2), (key1111, -2), (key1154, 2), (key1192, 2), (key1198, 2), (key1211, -4)]

theorem rowCheck1712 : row1712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1712 := by decide +kernel

theorem rowEval1712 (x : Key → ℝ) : Integer.Sparse.eval row1712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1712, Integer.Sparse.eval_collectBalanced, rawRowCheck1712]

def rawRow1713 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1126, -2), (key1154, 6), (key998, 2), (key998, 2), (key1018, 2), (key1075, -2), (key1211, -2), (key1211, -2), (key1005, -6), (key1040, 2), (key1192, 2), (key1192, 2)]

theorem rawRowCheck1713 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form8 = rawRow1713 := by decide +kernel

def row1713 : Integer.Sparse Key := [(key998, 4), (key1005, -6), (key1018, 2), (key1040, 2), (key1075, -2), (key1111, -4), (key1126, -2), (key1154, 6), (key1192, 4), (key1211, -4)]

theorem rowCheck1713 : row1713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1713 := by decide +kernel

theorem rowEval1713 (x : Key → ℝ) : Integer.Sparse.eval row1713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1713, Integer.Sparse.eval_collectBalanced, rawRowCheck1713]

def rawRow1714 : Integer.Sparse Key := [(key1111, -2), (key1126, -2), (key1111, -2), (key1154, 6), (key998, 2), (key1018, 2), (key998, 2), (key1211, -2), (key1075, -2), (key1211, -2), (key1005, -6), (key1192, 2), (key1040, 2), (key1192, 2)]

theorem rawRowCheck1714 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form8 = rawRow1714 := by decide +kernel

def row1714 : Integer.Sparse Key := [(key998, 4), (key1005, -6), (key1018, 2), (key1040, 2), (key1075, -2), (key1111, -4), (key1126, -2), (key1154, 6), (key1192, 4), (key1211, -4)]

theorem rowCheck1714 : row1714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1714 := by decide +kernel

theorem rowEval1714 (x : Key → ℝ) : Integer.Sparse.eval row1714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1714, Integer.Sparse.eval_collectBalanced, rawRowCheck1714]

def rawRow1715 : Integer.Sparse Key := [(key1126, -2), (key1111, -2), (key1111, -2), (key1154, 6), (key1018, 2), (key998, 2), (key998, 2), (key1211, -2), (key1211, -2), (key1075, -2), (key1005, -6), (key1192, 2), (key1192, 2), (key1040, 2)]

theorem rawRowCheck1715 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form8 = rawRow1715 := by decide +kernel

def row1715 : Integer.Sparse Key := [(key998, 4), (key1005, -6), (key1018, 2), (key1040, 2), (key1075, -2), (key1111, -4), (key1126, -2), (key1154, 6), (key1192, 4), (key1211, -4)]

theorem rowCheck1715 : row1715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1715 := by decide +kernel

theorem rowEval1715 (x : Key → ℝ) : Integer.Sparse.eval row1715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1715, Integer.Sparse.eval_collectBalanced, rawRowCheck1715]

def rawRow1716 : Integer.Sparse Key := [(key1111, -2), (key1126, -2), (key1154, -2), (key1111, 6), (key1190, 2), (key1198, 2), (key1211, 2), (key998, -2), (key1033, -2), (key1190, -2), (key1192, -6), (key1005, 2), (key1040, 2), (key1192, 2)]

theorem rawRowCheck1716 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form8 = rawRow1716 := by decide +kernel

def row1716 : Integer.Sparse Key := [(key998, -2), (key1005, 2), (key1033, -2), (key1040, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1192, -4), (key1198, 2), (key1211, 2)]

theorem rowCheck1716 : row1716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1716 := by decide +kernel

theorem rowEval1716 (x : Key → ℝ) : Integer.Sparse.eval row1716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1716, Integer.Sparse.eval_collectBalanced, rawRowCheck1716]

def rawRow1717 : Integer.Sparse Key := [(key1126, -2), (key1111, -2), (key1154, -2), (key1111, 6), (key1198, 2), (key1190, 2), (key1211, 2), (key998, -2), (key1190, -2), (key1033, -2), (key1192, -6), (key1005, 2), (key1192, 2), (key1040, 2)]

theorem rawRowCheck1717 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form8 = rawRow1717 := by decide +kernel

def row1717 : Integer.Sparse Key := [(key998, -2), (key1005, 2), (key1033, -2), (key1040, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1192, -4), (key1198, 2), (key1211, 2)]

theorem rowCheck1717 : row1717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1717 := by decide +kernel

theorem rowEval1717 (x : Key → ℝ) : Integer.Sparse.eval row1717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1717, Integer.Sparse.eval_collectBalanced, rawRowCheck1717]

def rawRow1718 : Integer.Sparse Key := [(key1111, -2), (key1154, -2), (key1126, -2), (key1111, 6), (key1190, 2), (key1211, 2), (key1198, 2), (key1033, -2), (key998, -2), (key1190, -2), (key1192, -6), (key1040, 2), (key1005, 2), (key1192, 2)]

theorem rawRowCheck1718 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form8 = rawRow1718 := by decide +kernel

def row1718 : Integer.Sparse Key := [(key998, -2), (key1005, 2), (key1033, -2), (key1040, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1192, -4), (key1198, 2), (key1211, 2)]

theorem rowCheck1718 : row1718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1718 := by decide +kernel

theorem rowEval1718 (x : Key → ℝ) : Integer.Sparse.eval row1718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1718, Integer.Sparse.eval_collectBalanced, rawRowCheck1718]

def rawRow1719 : Integer.Sparse Key := [(key1154, -2), (key1111, -2), (key1126, -2), (key1111, 6), (key1211, 2), (key1190, 2), (key1198, 2), (key1033, -2), (key1190, -2), (key998, -2), (key1192, -6), (key1040, 2), (key1192, 2), (key1005, 2)]

theorem rawRowCheck1719 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form8 = rawRow1719 := by decide +kernel

def row1719 : Integer.Sparse Key := [(key998, -2), (key1005, 2), (key1033, -2), (key1040, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1192, -4), (key1198, 2), (key1211, 2)]

theorem rowCheck1719 : row1719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1719 := by decide +kernel

theorem rowEval1719 (x : Key → ℝ) : Integer.Sparse.eval row1719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck1719, Integer.Sparse.eval_collectBalanced, rawRowCheck1719]

def rawRow1720 : Integer.Sparse Key := [(key1126, -2), (key1154, -2), (key1111, -2), (key1111, 6), (key1198, 2), (key1211, 2), (key1190, 2), (key1190, -2), (key998, -2), (key1033, -2), (key1192, -6), (key1192, 2), (key1005, 2), (key1040, 2)]

theorem rawRowCheck1720 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form8 = rawRow1720 := by decide +kernel

def row1720 : Integer.Sparse Key := [(key998, -2), (key1005, 2), (key1033, -2), (key1040, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1192, -4), (key1198, 2), (key1211, 2)]

theorem rowCheck1720 : row1720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1720 := by decide +kernel

theorem rowEval1720 (x : Key → ℝ) : Integer.Sparse.eval row1720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1720, Integer.Sparse.eval_collectBalanced, rawRowCheck1720]

def rawRow1721 : Integer.Sparse Key := [(key1154, -2), (key1126, -2), (key1111, -2), (key1111, 6), (key1211, 2), (key1198, 2), (key1190, 2), (key1190, -2), (key1033, -2), (key998, -2), (key1192, -6), (key1192, 2), (key1040, 2), (key1005, 2)]

theorem rawRowCheck1721 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form8 = rawRow1721 := by decide +kernel

def row1721 : Integer.Sparse Key := [(key998, -2), (key1005, 2), (key1033, -2), (key1040, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1192, -4), (key1198, 2), (key1211, 2)]

theorem rowCheck1721 : row1721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1721 := by decide +kernel

theorem rowEval1721 (x : Key → ℝ) : Integer.Sparse.eval row1721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck1721, Integer.Sparse.eval_collectBalanced, rawRowCheck1721]

def rawRow1722 : Integer.Sparse Key := [(key1190, -2), (key1192, -2), (key1198, -2), (key1211, 6), (key998, 2), (key1005, 2), (key1018, 2), (key1075, -2), (key1154, -2), (key1211, -2), (key998, -6), (key1033, 2), (key1111, 2), (key1190, 2)]

theorem rawRowCheck1722 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form8 = rawRow1722 := by decide +kernel

def row1722 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, 2), (key1075, -2), (key1111, 2), (key1154, -2), (key1192, -2), (key1198, -2), (key1211, 4)]

theorem rowCheck1722 : row1722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1722 := by decide +kernel

theorem rowEval1722 (x : Key → ℝ) : Integer.Sparse.eval row1722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1722, Integer.Sparse.eval_collectBalanced, rawRowCheck1722]

def rawRow1723 : Integer.Sparse Key := [(key1192, -2), (key1190, -2), (key1198, -2), (key1211, 6), (key1005, 2), (key998, 2), (key1018, 2), (key1075, -2), (key1211, -2), (key1154, -2), (key998, -6), (key1033, 2), (key1190, 2), (key1111, 2)]

theorem rawRowCheck1723 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form8 = rawRow1723 := by decide +kernel

def row1723 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, 2), (key1075, -2), (key1111, 2), (key1154, -2), (key1192, -2), (key1198, -2), (key1211, 4)]

theorem rowCheck1723 : row1723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1723 := by decide +kernel

theorem rowEval1723 (x : Key → ℝ) : Integer.Sparse.eval row1723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1723, Integer.Sparse.eval_collectBalanced, rawRowCheck1723]

def rawRow1724 : Integer.Sparse Key := [(key1190, -2), (key1198, -2), (key1192, -2), (key1211, 6), (key998, 2), (key1018, 2), (key1005, 2), (key1154, -2), (key1075, -2), (key1211, -2), (key998, -6), (key1111, 2), (key1033, 2), (key1190, 2)]

theorem rawRowCheck1724 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form8 = rawRow1724 := by decide +kernel

def row1724 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, 2), (key1075, -2), (key1111, 2), (key1154, -2), (key1192, -2), (key1198, -2), (key1211, 4)]

theorem rowCheck1724 : row1724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1724 := by decide +kernel

theorem rowEval1724 (x : Key → ℝ) : Integer.Sparse.eval row1724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1724, Integer.Sparse.eval_collectBalanced, rawRowCheck1724]

def rawRow1725 : Integer.Sparse Key := [(key1198, -2), (key1190, -2), (key1192, -2), (key1211, 6), (key1018, 2), (key998, 2), (key1005, 2), (key1154, -2), (key1211, -2), (key1075, -2), (key998, -6), (key1111, 2), (key1190, 2), (key1033, 2)]

theorem rawRowCheck1725 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form8 = rawRow1725 := by decide +kernel

def row1725 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, 2), (key1075, -2), (key1111, 2), (key1154, -2), (key1192, -2), (key1198, -2), (key1211, 4)]

theorem rowCheck1725 : row1725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1725 := by decide +kernel

theorem rowEval1725 (x : Key → ℝ) : Integer.Sparse.eval row1725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1725, Integer.Sparse.eval_collectBalanced, rawRowCheck1725]

def rawRow1726 : Integer.Sparse Key := [(key1192, -2), (key1198, -2), (key1190, -2), (key1211, 6), (key1005, 2), (key1018, 2), (key998, 2), (key1211, -2), (key1075, -2), (key1154, -2), (key998, -6), (key1190, 2), (key1033, 2), (key1111, 2)]

theorem rawRowCheck1726 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form8 = rawRow1726 := by decide +kernel

def row1726 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, 2), (key1075, -2), (key1111, 2), (key1154, -2), (key1192, -2), (key1198, -2), (key1211, 4)]

theorem rowCheck1726 : row1726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1726 := by decide +kernel

theorem rowEval1726 (x : Key → ℝ) : Integer.Sparse.eval row1726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1726, Integer.Sparse.eval_collectBalanced, rawRowCheck1726]

def rawRow1727 : Integer.Sparse Key := [(key1198, -2), (key1192, -2), (key1190, -2), (key1211, 6), (key1018, 2), (key1005, 2), (key998, 2), (key1211, -2), (key1154, -2), (key1075, -2), (key998, -6), (key1190, 2), (key1111, 2), (key1033, 2)]

theorem rawRowCheck1727 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form8 = rawRow1727 := by decide +kernel

def row1727 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, 2), (key1075, -2), (key1111, 2), (key1154, -2), (key1192, -2), (key1198, -2), (key1211, 4)]

theorem rowCheck1727 : row1727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1727 := by decide +kernel

theorem rowEval1727 (x : Key → ℝ) : Integer.Sparse.eval row1727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1727, Integer.Sparse.eval_collectBalanced, rawRowCheck1727]

def rawRow1728 : Integer.Sparse Key := [(key1190, -2), (key1198, -2), (key1211, -2), (key1192, 6), (key1111, 2), (key1126, 2), (key1154, 2), (key1005, -2), (key1040, -2), (key1192, -2), (key1111, -6), (key998, 2), (key1033, 2), (key1190, 2)]

theorem rawRowCheck1728 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form8 = rawRow1728 := by decide +kernel

def row1728 : Integer.Sparse Key := [(key998, 2), (key1005, -2), (key1033, 2), (key1040, -2), (key1111, -4), (key1126, 2), (key1154, 2), (key1192, 4), (key1198, -2), (key1211, -2)]

theorem rowCheck1728 : row1728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1728 := by decide +kernel

theorem rowEval1728 (x : Key → ℝ) : Integer.Sparse.eval row1728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1728, Integer.Sparse.eval_collectBalanced, rawRowCheck1728]

def rawRow1729 : Integer.Sparse Key := [(key1198, -2), (key1190, -2), (key1211, -2), (key1192, 6), (key1126, 2), (key1111, 2), (key1154, 2), (key1005, -2), (key1192, -2), (key1040, -2), (key1111, -6), (key998, 2), (key1190, 2), (key1033, 2)]

theorem rawRowCheck1729 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form8 = rawRow1729 := by decide +kernel

def row1729 : Integer.Sparse Key := [(key998, 2), (key1005, -2), (key1033, 2), (key1040, -2), (key1111, -4), (key1126, 2), (key1154, 2), (key1192, 4), (key1198, -2), (key1211, -2)]

theorem rowCheck1729 : row1729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1729 := by decide +kernel

theorem rowEval1729 (x : Key → ℝ) : Integer.Sparse.eval row1729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1729, Integer.Sparse.eval_collectBalanced, rawRowCheck1729]

def rawRow1730 : Integer.Sparse Key := [(key1190, -2), (key1211, -2), (key1198, -2), (key1192, 6), (key1111, 2), (key1154, 2), (key1126, 2), (key1040, -2), (key1005, -2), (key1192, -2), (key1111, -6), (key1033, 2), (key998, 2), (key1190, 2)]

theorem rawRowCheck1730 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form8 = rawRow1730 := by decide +kernel

def row1730 : Integer.Sparse Key := [(key998, 2), (key1005, -2), (key1033, 2), (key1040, -2), (key1111, -4), (key1126, 2), (key1154, 2), (key1192, 4), (key1198, -2), (key1211, -2)]

theorem rowCheck1730 : row1730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1730 := by decide +kernel

theorem rowEval1730 (x : Key → ℝ) : Integer.Sparse.eval row1730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1730, Integer.Sparse.eval_collectBalanced, rawRowCheck1730]

def rawRow1731 : Integer.Sparse Key := [(key1211, -2), (key1190, -2), (key1198, -2), (key1192, 6), (key1154, 2), (key1111, 2), (key1126, 2), (key1040, -2), (key1192, -2), (key1005, -2), (key1111, -6), (key1033, 2), (key1190, 2), (key998, 2)]

theorem rawRowCheck1731 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form8 = rawRow1731 := by decide +kernel

def row1731 : Integer.Sparse Key := [(key998, 2), (key1005, -2), (key1033, 2), (key1040, -2), (key1111, -4), (key1126, 2), (key1154, 2), (key1192, 4), (key1198, -2), (key1211, -2)]

theorem rowCheck1731 : row1731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1731 := by decide +kernel

theorem rowEval1731 (x : Key → ℝ) : Integer.Sparse.eval row1731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck1731, Integer.Sparse.eval_collectBalanced, rawRowCheck1731]

def rawRow1732 : Integer.Sparse Key := [(key1198, -2), (key1211, -2), (key1190, -2), (key1192, 6), (key1126, 2), (key1154, 2), (key1111, 2), (key1192, -2), (key1005, -2), (key1040, -2), (key1111, -6), (key1190, 2), (key998, 2), (key1033, 2)]

theorem rawRowCheck1732 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form8 = rawRow1732 := by decide +kernel

def row1732 : Integer.Sparse Key := [(key998, 2), (key1005, -2), (key1033, 2), (key1040, -2), (key1111, -4), (key1126, 2), (key1154, 2), (key1192, 4), (key1198, -2), (key1211, -2)]

theorem rowCheck1732 : row1732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1732 := by decide +kernel

theorem rowEval1732 (x : Key → ℝ) : Integer.Sparse.eval row1732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1732, Integer.Sparse.eval_collectBalanced, rawRowCheck1732]

def rawRow1733 : Integer.Sparse Key := [(key1211, -2), (key1198, -2), (key1190, -2), (key1192, 6), (key1154, 2), (key1126, 2), (key1111, 2), (key1192, -2), (key1040, -2), (key1005, -2), (key1111, -6), (key1190, 2), (key1033, 2), (key998, 2)]

theorem rawRowCheck1733 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form8 = rawRow1733 := by decide +kernel

def row1733 : Integer.Sparse Key := [(key998, 2), (key1005, -2), (key1033, 2), (key1040, -2), (key1111, -4), (key1126, 2), (key1154, 2), (key1192, 4), (key1198, -2), (key1211, -2)]

theorem rowCheck1733 : row1733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1733 := by decide +kernel

theorem rowEval1733 (x : Key → ℝ) : Integer.Sparse.eval row1733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck1733, Integer.Sparse.eval_collectBalanced, rawRowCheck1733]

def rawRow1734 : Integer.Sparse Key := [(key2617, -2), (key2655, -2), (key2655, -2), (key2620, 1), (key2620, 1), (key2643, 1), (key2643, 1), (key2656, 1), (key2656, 1), (key2810, 2), (key2899, 2), (key2899, 2), (key2797, -1), (key2797, -1), (key2833, -1), (key2833, -1), (key2915, -1), (key2915, -1), (key2952, -1), (key2952, -1), (key2978, -1), (key2978, -1), (key2999, -1), (key2999, -1), (key2945, 1), (key2945, 1), (key2962, 1), (key2962, 1), (key3004, 1), (key3004, 1)]

theorem rawRowCheck1734 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form9 = rawRow1734 := by decide +kernel

def row1734 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2643, 2), (key2655, -4), (key2656, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, 4), (key2915, -2), (key2945, 2), (key2952, -2), (key2962, 2), (key2978, -2), (key2999, -2), (key3004, 2)]

theorem rowCheck1734 : row1734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1734 := by decide +kernel

theorem rowEval1734 (x : Key → ℝ) : Integer.Sparse.eval row1734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1734, Integer.Sparse.eval_collectBalanced, rawRowCheck1734]

def rawRow1735 : Integer.Sparse Key := [(key2655, -2), (key2617, -2), (key2655, -2), (key2643, 1), (key2656, 1), (key2620, 1), (key2656, 1), (key2620, 1), (key2643, 1), (key2899, 2), (key2810, 2), (key2899, 2), (key2833, -1), (key2915, -1), (key2797, -1), (key2915, -1), (key2797, -1), (key2833, -1), (key2978, -1), (key2999, -1), (key2952, -1), (key2999, -1), (key2952, -1), (key2978, -1), (key2962, 1), (key3004, 1), (key2945, 1), (key3004, 1), (key2945, 1), (key2962, 1)]

theorem rawRowCheck1735 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form9 = rawRow1735 := by decide +kernel

def row1735 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2643, 2), (key2655, -4), (key2656, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, 4), (key2915, -2), (key2945, 2), (key2952, -2), (key2962, 2), (key2978, -2), (key2999, -2), (key3004, 2)]

theorem rowCheck1735 : row1735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1735 := by decide +kernel

theorem rowEval1735 (x : Key → ℝ) : Integer.Sparse.eval row1735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1735, Integer.Sparse.eval_collectBalanced, rawRowCheck1735]

def rawRow1736 : Integer.Sparse Key := [(key2655, -2), (key2655, -2), (key2617, -2), (key2656, 1), (key2643, 1), (key2656, 1), (key2620, 1), (key2643, 1), (key2620, 1), (key2899, 2), (key2899, 2), (key2810, 2), (key2915, -1), (key2833, -1), (key2915, -1), (key2797, -1), (key2833, -1), (key2797, -1), (key2999, -1), (key2978, -1), (key2999, -1), (key2952, -1), (key2978, -1), (key2952, -1), (key3004, 1), (key2962, 1), (key3004, 1), (key2945, 1), (key2962, 1), (key2945, 1)]

theorem rawRowCheck1736 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form9 = rawRow1736 := by decide +kernel

def row1736 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2643, 2), (key2655, -4), (key2656, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, 4), (key2915, -2), (key2945, 2), (key2952, -2), (key2962, 2), (key2978, -2), (key2999, -2), (key3004, 2)]

theorem rowCheck1736 : row1736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1736 := by decide +kernel

theorem rowEval1736 (x : Key → ℝ) : Integer.Sparse.eval row1736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1736, Integer.Sparse.eval_collectBalanced, rawRowCheck1736]

def rawRow1737 : Integer.Sparse Key := [(key2620, -2), (key2643, -2), (key2656, -2), (key2617, 1), (key2620, 1), (key2633, 1), (key2643, 1), (key2650, 1), (key2655, 1), (key2833, 2), (key2906, 2), (key2915, 2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, -1), (key2899, -1), (key2906, -1), (key2962, -1), (key2964, -1), (key2985, -1), (key2994, -1), (key3001, -1), (key3004, -1), (key2940, 1), (key2946, 1), (key2952, 1), (key2964, 1), (key2999, 1), (key3001, 1)]

theorem rawRowCheck1737 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form9 = rawRow1737 := by decide +kernel

def row1737 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, 1), (key2915, 2), (key2940, 1), (key2946, 1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, -1), (key2999, 1), (key3004, -1)]

theorem rowCheck1737 : row1737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1737 := by decide +kernel

theorem rowEval1737 (x : Key → ℝ) : Integer.Sparse.eval row1737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1737, Integer.Sparse.eval_collectBalanced, rawRowCheck1737]

def rawRow1738 : Integer.Sparse Key := [(key2620, -2), (key2656, -2), (key2643, -2), (key2620, 1), (key2617, 1), (key2643, 1), (key2633, 1), (key2655, 1), (key2650, 1), (key2833, 2), (key2915, 2), (key2906, 2), (key2797, -1), (key2787, -1), (key2833, -1), (key2810, -1), (key2906, -1), (key2899, -1), (key2964, -1), (key2962, -1), (key2994, -1), (key2985, -1), (key3004, -1), (key3001, -1), (key2946, 1), (key2940, 1), (key2964, 1), (key2952, 1), (key3001, 1), (key2999, 1)]

theorem rawRowCheck1738 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form9 = rawRow1738 := by decide +kernel

def row1738 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, 1), (key2915, 2), (key2940, 1), (key2946, 1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, -1), (key2999, 1), (key3004, -1)]

theorem rowCheck1738 : row1738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1738 := by decide +kernel

theorem rowEval1738 (x : Key → ℝ) : Integer.Sparse.eval row1738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1738, Integer.Sparse.eval_collectBalanced, rawRowCheck1738]

def rawRow1739 : Integer.Sparse Key := [(key2643, -2), (key2620, -2), (key2656, -2), (key2633, 1), (key2643, 1), (key2617, 1), (key2655, 1), (key2620, 1), (key2643, 1), (key2906, 2), (key2833, 2), (key2915, 2), (key2810, -1), (key2899, -1), (key2787, -1), (key2906, -1), (key2797, -1), (key2833, -1), (key2985, -1), (key3001, -1), (key2962, -1), (key3004, -1), (key2964, -1), (key2994, -1), (key2952, 1), (key2999, 1), (key2940, 1), (key3001, 1), (key2946, 1), (key2964, 1)]

theorem rawRowCheck1739 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form9 = rawRow1739 := by decide +kernel

def row1739 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2655, 1), (key2656, -2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, 1), (key2915, 2), (key2940, 1), (key2946, 1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, -1), (key2999, 1), (key3004, -1)]

theorem rowCheck1739 : row1739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1739 := by decide +kernel

theorem rowEval1739 (x : Key → ℝ) : Integer.Sparse.eval row1739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1739, Integer.Sparse.eval_collectBalanced, rawRowCheck1739]

def rawRow1740 : Integer.Sparse Key := [(key2643, -2), (key2656, -2), (key2620, -2), (key2643, 1), (key2633, 1), (key2655, 1), (key2617, 1), (key2643, 1), (key2620, 1), (key2906, 2), (key2915, 2), (key2833, 2), (key2899, -1), (key2810, -1), (key2906, -1), (key2787, -1), (key2833, -1), (key2797, -1), (key3001, -1), (key2985, -1), (key3004, -1), (key2962, -1), (key2994, -1), (key2964, -1), (key2999, 1), (key2952, 1), (key3001, 1), (key2940, 1), (key2964, 1), (key2946, 1)]

theorem rawRowCheck1740 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form9 = rawRow1740 := by decide +kernel

def row1740 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2655, 1), (key2656, -2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, 1), (key2915, 2), (key2940, 1), (key2946, 1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, -1), (key2999, 1), (key3004, -1)]

theorem rowCheck1740 : row1740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1740 := by decide +kernel

theorem rowEval1740 (x : Key → ℝ) : Integer.Sparse.eval row1740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1740, Integer.Sparse.eval_collectBalanced, rawRowCheck1740]

def rawRow1741 : Integer.Sparse Key := [(key2656, -2), (key2620, -2), (key2643, -2), (key2650, 1), (key2655, 1), (key2620, 1), (key2643, 1), (key2617, 1), (key2633, 1), (key2915, 2), (key2833, 2), (key2906, 2), (key2833, -1), (key2906, -1), (key2797, -1), (key2899, -1), (key2787, -1), (key2810, -1), (key2994, -1), (key3004, -1), (key2964, -1), (key3001, -1), (key2962, -1), (key2985, -1), (key2964, 1), (key3001, 1), (key2946, 1), (key2999, 1), (key2940, 1), (key2952, 1)]

theorem rawRowCheck1741 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form9 = rawRow1741 := by decide +kernel

def row1741 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, 1), (key2915, 2), (key2940, 1), (key2946, 1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, -1), (key2999, 1), (key3004, -1)]

theorem rowCheck1741 : row1741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1741 := by decide +kernel

theorem rowEval1741 (x : Key → ℝ) : Integer.Sparse.eval row1741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1741, Integer.Sparse.eval_collectBalanced, rawRowCheck1741]

def rawRow1742 : Integer.Sparse Key := [(key2656, -2), (key2643, -2), (key2620, -2), (key2655, 1), (key2650, 1), (key2643, 1), (key2620, 1), (key2633, 1), (key2617, 1), (key2915, 2), (key2906, 2), (key2833, 2), (key2906, -1), (key2833, -1), (key2899, -1), (key2797, -1), (key2810, -1), (key2787, -1), (key3004, -1), (key2994, -1), (key3001, -1), (key2964, -1), (key2985, -1), (key2962, -1), (key3001, 1), (key2964, 1), (key2999, 1), (key2946, 1), (key2952, 1), (key2940, 1)]

theorem rawRowCheck1742 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form9 = rawRow1742 := by decide +kernel

def row1742 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, 1), (key2915, 2), (key2940, 1), (key2946, 1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, -1), (key2999, 1), (key3004, -1)]

theorem rowCheck1742 : row1742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1742 := by decide +kernel

theorem rowEval1742 (x : Key → ℝ) : Integer.Sparse.eval row1742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1742, Integer.Sparse.eval_collectBalanced, rawRowCheck1742]

def rawRow1743 : Integer.Sparse Key := [(key2810, -2), (key2899, -2), (key2899, -2), (key2833, 1), (key2833, 1), (key2906, 1), (key2906, 1), (key2915, 1), (key2915, 1), (key2617, 2), (key2655, 2), (key2655, 2), (key2945, -1), (key2945, -1), (key2962, -1), (key2962, -1), (key3004, -1), (key3004, -1), (key2620, -1), (key2620, -1), (key2643, -1), (key2643, -1), (key2656, -1), (key2656, -1), (key2797, 1), (key2797, 1), (key2833, 1), (key2833, 1), (key2915, 1), (key2915, 1)]

theorem rawRowCheck1743 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form9 = rawRow1743 := by decide +kernel

def row1743 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2643, -2), (key2655, 4), (key2656, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, -4), (key2906, 2), (key2915, 4), (key2945, -2), (key2962, -2), (key3004, -2)]

theorem rowCheck1743 : row1743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1743 := by decide +kernel

theorem rowEval1743 (x : Key → ℝ) : Integer.Sparse.eval row1743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1743, Integer.Sparse.eval_collectBalanced, rawRowCheck1743]

def rawRow1744 : Integer.Sparse Key := [(key2899, -2), (key2810, -2), (key2899, -2), (key2906, 1), (key2915, 1), (key2833, 1), (key2915, 1), (key2833, 1), (key2906, 1), (key2655, 2), (key2617, 2), (key2655, 2), (key2962, -1), (key3004, -1), (key2945, -1), (key3004, -1), (key2945, -1), (key2962, -1), (key2643, -1), (key2656, -1), (key2620, -1), (key2656, -1), (key2620, -1), (key2643, -1), (key2833, 1), (key2915, 1), (key2797, 1), (key2915, 1), (key2797, 1), (key2833, 1)]

theorem rawRowCheck1744 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form9 = rawRow1744 := by decide +kernel

def row1744 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2643, -2), (key2655, 4), (key2656, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, -4), (key2906, 2), (key2915, 4), (key2945, -2), (key2962, -2), (key3004, -2)]

theorem rowCheck1744 : row1744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1744 := by decide +kernel

theorem rowEval1744 (x : Key → ℝ) : Integer.Sparse.eval row1744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1744, Integer.Sparse.eval_collectBalanced, rawRowCheck1744]

def rawRow1745 : Integer.Sparse Key := [(key2899, -2), (key2899, -2), (key2810, -2), (key2915, 1), (key2906, 1), (key2915, 1), (key2833, 1), (key2906, 1), (key2833, 1), (key2655, 2), (key2655, 2), (key2617, 2), (key3004, -1), (key2962, -1), (key3004, -1), (key2945, -1), (key2962, -1), (key2945, -1), (key2656, -1), (key2643, -1), (key2656, -1), (key2620, -1), (key2643, -1), (key2620, -1), (key2915, 1), (key2833, 1), (key2915, 1), (key2797, 1), (key2833, 1), (key2797, 1)]

theorem rawRowCheck1745 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form9 = rawRow1745 := by decide +kernel

def row1745 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2643, -2), (key2655, 4), (key2656, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, -4), (key2906, 2), (key2915, 4), (key2945, -2), (key2962, -2), (key3004, -2)]

theorem rowCheck1745 : row1745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1745 := by decide +kernel

theorem rowEval1745 (x : Key → ℝ) : Integer.Sparse.eval row1745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1745, Integer.Sparse.eval_collectBalanced, rawRowCheck1745]

def rawRow1746 : Integer.Sparse Key := [(key2797, -2), (key2833, -2), (key2915, -2), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2833, 1), (key2906, 1), (key2945, 2), (key2962, 2), (key3004, 2), (key2617, -1), (key2655, -1), (key2672, -1), (key2749, -1), (key2945, -1), (key2962, -1), (key2730, -1), (key2751, -1), (key2833, -1), (key2915, -1), (key2964, -1), (key2994, -1), (key2620, 1), (key2656, 1), (key2675, 1), (key2751, 1), (key2946, 1), (key2964, 1)]

theorem rawRowCheck1746 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form9 = rawRow1746 := by decide +kernel

def row1746 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, -1), (key2656, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, 1), (key2906, 1), (key2915, -3), (key2945, 1), (key2946, 1), (key2962, 1), (key2994, -1), (key3004, 2)]

theorem rowCheck1746 : row1746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1746 := by decide +kernel

theorem rowEval1746 (x : Key → ℝ) : Integer.Sparse.eval row1746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1746, Integer.Sparse.eval_collectBalanced, rawRowCheck1746]

def rawRow1747 : Integer.Sparse Key := [(key2797, -2), (key2915, -2), (key2833, -2), (key2797, 1), (key2787, 1), (key2899, 1), (key2810, 1), (key2906, 1), (key2833, 1), (key2945, 2), (key3004, 2), (key2962, 2), (key2655, -1), (key2617, -1), (key2749, -1), (key2672, -1), (key2962, -1), (key2945, -1), (key2751, -1), (key2730, -1), (key2915, -1), (key2833, -1), (key2994, -1), (key2964, -1), (key2656, 1), (key2620, 1), (key2751, 1), (key2675, 1), (key2964, 1), (key2946, 1)]

theorem rawRowCheck1747 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form9 = rawRow1747 := by decide +kernel

def row1747 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, -1), (key2656, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, 1), (key2906, 1), (key2915, -3), (key2945, 1), (key2946, 1), (key2962, 1), (key2994, -1), (key3004, 2)]

theorem rowCheck1747 : row1747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1747 := by decide +kernel

theorem rowEval1747 (x : Key → ℝ) : Integer.Sparse.eval row1747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1747, Integer.Sparse.eval_collectBalanced, rawRowCheck1747]

def rawRow1748 : Integer.Sparse Key := [(key2833, -2), (key2797, -2), (key2915, -2), (key2810, 1), (key2833, 1), (key2787, 1), (key2906, 1), (key2797, 1), (key2899, 1), (key2962, 2), (key2945, 2), (key3004, 2), (key2672, -1), (key2749, -1), (key2617, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2833, -1), (key2964, -1), (key2730, -1), (key2994, -1), (key2751, -1), (key2915, -1), (key2675, 1), (key2946, 1), (key2620, 1), (key2964, 1), (key2656, 1), (key2751, 1)]

theorem rawRowCheck1748 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form9 = rawRow1748 := by decide +kernel

def row1748 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, -1), (key2656, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, 1), (key2906, 1), (key2915, -3), (key2945, 2), (key2946, 1), (key2962, 1), (key2994, -1), (key3004, 2)]

theorem rowCheck1748 : row1748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1748 := by decide +kernel

theorem rowEval1748 (x : Key → ℝ) : Integer.Sparse.eval row1748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1748, Integer.Sparse.eval_collectBalanced, rawRowCheck1748]

def rawRow1749 : Integer.Sparse Key := [(key2833, -2), (key2915, -2), (key2797, -2), (key2833, 1), (key2810, 1), (key2906, 1), (key2787, 1), (key2899, 1), (key2797, 1), (key2962, 2), (key3004, 2), (key2945, 2), (key2749, -1), (key2672, -1), (key2962, -1), (key2617, -1), (key2749, -1), (key2655, -1), (key2964, -1), (key2833, -1), (key2994, -1), (key2730, -1), (key2915, -1), (key2751, -1), (key2946, 1), (key2675, 1), (key2964, 1), (key2620, 1), (key2751, 1), (key2656, 1)]

theorem rawRowCheck1749 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form9 = rawRow1749 := by decide +kernel

def row1749 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, -1), (key2656, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, 1), (key2906, 1), (key2915, -3), (key2945, 2), (key2946, 1), (key2962, 1), (key2994, -1), (key3004, 2)]

theorem rowCheck1749 : row1749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1749 := by decide +kernel

theorem rowEval1749 (x : Key → ℝ) : Integer.Sparse.eval row1749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck1749, Integer.Sparse.eval_collectBalanced, rawRowCheck1749]

def rawRow1750 : Integer.Sparse Key := [(key2915, -2), (key2797, -2), (key2833, -2), (key2899, 1), (key2906, 1), (key2797, 1), (key2833, 1), (key2787, 1), (key2810, 1), (key3004, 2), (key2945, 2), (key2962, 2), (key2945, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2617, -1), (key2672, -1), (key2915, -1), (key2994, -1), (key2751, -1), (key2964, -1), (key2730, -1), (key2833, -1), (key2751, 1), (key2964, 1), (key2656, 1), (key2946, 1), (key2620, 1), (key2675, 1)]

theorem rawRowCheck1750 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form9 = rawRow1750 := by decide +kernel

def row1750 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, -1), (key2656, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, 1), (key2906, 1), (key2915, -3), (key2945, 1), (key2946, 1), (key2962, 1), (key2994, -1), (key3004, 2)]

theorem rowCheck1750 : row1750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1750 := by decide +kernel

theorem rowEval1750 (x : Key → ℝ) : Integer.Sparse.eval row1750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1750, Integer.Sparse.eval_collectBalanced, rawRowCheck1750]

def rawRow1751 : Integer.Sparse Key := [(key2915, -2), (key2833, -2), (key2797, -2), (key2906, 1), (key2899, 1), (key2833, 1), (key2797, 1), (key2810, 1), (key2787, 1), (key3004, 2), (key2962, 2), (key2945, 2), (key2962, -1), (key2945, -1), (key2749, -1), (key2655, -1), (key2672, -1), (key2617, -1), (key2994, -1), (key2915, -1), (key2964, -1), (key2751, -1), (key2833, -1), (key2730, -1), (key2964, 1), (key2751, 1), (key2946, 1), (key2656, 1), (key2675, 1), (key2620, 1)]

theorem rawRowCheck1751 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form9 = rawRow1751 := by decide +kernel

def row1751 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, -1), (key2656, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, 1), (key2906, 1), (key2915, -3), (key2945, 1), (key2946, 1), (key2962, 1), (key2994, -1), (key3004, 2)]

theorem rowCheck1751 : row1751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1751 := by decide +kernel

theorem rowEval1751 (x : Key → ℝ) : Integer.Sparse.eval row1751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck1751, Integer.Sparse.eval_collectBalanced, rawRowCheck1751]

def rawRow1752 : Integer.Sparse Key := [(key2952, -2), (key2978, -2), (key2999, -2), (key2962, 1), (key2964, 1), (key2985, 1), (key3001, 1), (key2994, 1), (key3004, 1), (key2620, 2), (key2643, 2), (key2656, 2), (key2730, -1), (key2751, -1), (key2833, -1), (key2964, -1), (key2915, -1), (key2994, -1), (key2617, -1), (key2620, -1), (key2633, -1), (key2643, -1), (key2650, -1), (key2655, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2833, 1), (key2899, 1), (key2906, 1)]

theorem rawRowCheck1752 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form9 = rawRow1752 := by decide +kernel

def row1752 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, -1), (key2751, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2906, 1), (key2915, -1), (key2952, -2), (key2962, 1), (key2978, -2), (key2985, 1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck1752 : row1752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1752 := by decide +kernel

theorem rowEval1752 (x : Key → ℝ) : Integer.Sparse.eval row1752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1752, Integer.Sparse.eval_collectBalanced, rawRowCheck1752]

def rawRow1753 : Integer.Sparse Key := [(key2952, -2), (key2999, -2), (key2978, -2), (key2964, 1), (key2962, 1), (key3001, 1), (key2985, 1), (key3004, 1), (key2994, 1), (key2620, 2), (key2656, 2), (key2643, 2), (key2751, -1), (key2730, -1), (key2964, -1), (key2833, -1), (key2994, -1), (key2915, -1), (key2620, -1), (key2617, -1), (key2643, -1), (key2633, -1), (key2655, -1), (key2650, -1), (key2797, 1), (key2787, 1), (key2833, 1), (key2810, 1), (key2906, 1), (key2899, 1)]

theorem rawRowCheck1753 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form9 = rawRow1753 := by decide +kernel

def row1753 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, -1), (key2751, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2906, 1), (key2915, -1), (key2952, -2), (key2962, 1), (key2978, -2), (key2985, 1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck1753 : row1753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1753 := by decide +kernel

theorem rowEval1753 (x : Key → ℝ) : Integer.Sparse.eval row1753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1753, Integer.Sparse.eval_collectBalanced, rawRowCheck1753]

def rawRow1754 : Integer.Sparse Key := [(key2978, -2), (key2952, -2), (key2999, -2), (key2985, 1), (key2994, 1), (key2962, 1), (key3004, 1), (key2964, 1), (key3001, 1), (key2643, 2), (key2620, 2), (key2656, 2), (key2833, -1), (key2915, -1), (key2730, -1), (key2994, -1), (key2751, -1), (key2964, -1), (key2633, -1), (key2643, -1), (key2617, -1), (key2655, -1), (key2620, -1), (key2643, -1), (key2810, 1), (key2899, 1), (key2787, 1), (key2906, 1), (key2797, 1), (key2833, 1)]

theorem rawRowCheck1754 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form9 = rawRow1754 := by decide +kernel

def row1754 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2655, -1), (key2656, 2), (key2730, -1), (key2751, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2906, 1), (key2915, -1), (key2952, -2), (key2962, 1), (key2978, -2), (key2985, 1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck1754 : row1754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1754 := by decide +kernel

theorem rowEval1754 (x : Key → ℝ) : Integer.Sparse.eval row1754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1754, Integer.Sparse.eval_collectBalanced, rawRowCheck1754]

def rawRow1755 : Integer.Sparse Key := [(key2978, -2), (key2999, -2), (key2952, -2), (key2994, 1), (key2985, 1), (key3004, 1), (key2962, 1), (key3001, 1), (key2964, 1), (key2643, 2), (key2656, 2), (key2620, 2), (key2915, -1), (key2833, -1), (key2994, -1), (key2730, -1), (key2964, -1), (key2751, -1), (key2643, -1), (key2633, -1), (key2655, -1), (key2617, -1), (key2643, -1), (key2620, -1), (key2899, 1), (key2810, 1), (key2906, 1), (key2787, 1), (key2833, 1), (key2797, 1)]

theorem rawRowCheck1755 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form9 = rawRow1755 := by decide +kernel

def row1755 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2655, -1), (key2656, 2), (key2730, -1), (key2751, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2906, 1), (key2915, -1), (key2952, -2), (key2962, 1), (key2978, -2), (key2985, 1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck1755 : row1755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1755 := by decide +kernel

theorem rowEval1755 (x : Key → ℝ) : Integer.Sparse.eval row1755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1755, Integer.Sparse.eval_collectBalanced, rawRowCheck1755]

def rawRow1756 : Integer.Sparse Key := [(key2999, -2), (key2952, -2), (key2978, -2), (key3001, 1), (key3004, 1), (key2964, 1), (key2994, 1), (key2962, 1), (key2985, 1), (key2656, 2), (key2620, 2), (key2643, 2), (key2964, -1), (key2994, -1), (key2751, -1), (key2915, -1), (key2730, -1), (key2833, -1), (key2650, -1), (key2655, -1), (key2620, -1), (key2643, -1), (key2617, -1), (key2633, -1), (key2833, 1), (key2906, 1), (key2797, 1), (key2899, 1), (key2787, 1), (key2810, 1)]

theorem rawRowCheck1756 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form9 = rawRow1756 := by decide +kernel

def row1756 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, -1), (key2751, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2906, 1), (key2915, -1), (key2952, -2), (key2962, 1), (key2978, -2), (key2985, 1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck1756 : row1756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1756 := by decide +kernel

theorem rowEval1756 (x : Key → ℝ) : Integer.Sparse.eval row1756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1756, Integer.Sparse.eval_collectBalanced, rawRowCheck1756]

def rawRow1757 : Integer.Sparse Key := [(key2999, -2), (key2978, -2), (key2952, -2), (key3004, 1), (key3001, 1), (key2994, 1), (key2964, 1), (key2985, 1), (key2962, 1), (key2656, 2), (key2643, 2), (key2620, 2), (key2994, -1), (key2964, -1), (key2915, -1), (key2751, -1), (key2833, -1), (key2730, -1), (key2655, -1), (key2650, -1), (key2643, -1), (key2620, -1), (key2633, -1), (key2617, -1), (key2906, 1), (key2833, 1), (key2899, 1), (key2797, 1), (key2810, 1), (key2787, 1)]

theorem rawRowCheck1757 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form9 = rawRow1757 := by decide +kernel

def row1757 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, -1), (key2751, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2906, 1), (key2915, -1), (key2952, -2), (key2962, 1), (key2978, -2), (key2985, 1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck1757 : row1757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1757 := by decide +kernel

theorem rowEval1757 (x : Key → ℝ) : Integer.Sparse.eval row1757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1757, Integer.Sparse.eval_collectBalanced, rawRowCheck1757]

def rawRow1758 : Integer.Sparse Key := [(key2945, -2), (key2962, -2), (key3004, -2), (key2940, 1), (key2946, 1), (key2952, 1), (key2999, 1), (key2964, 1), (key3001, 1), (key2797, 2), (key2833, 2), (key2915, 2), (key2620, -1), (key2656, -1), (key2675, -1), (key2946, -1), (key2751, -1), (key2964, -1), (key2787, -1), (key2797, -1), (key2810, -1), (key2899, -1), (key2833, -1), (key2906, -1), (key2617, 1), (key2655, 1), (key2672, 1), (key2749, 1), (key2945, 1), (key2962, 1)]

theorem rawRowCheck1758 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form9 = rawRow1758 := by decide +kernel

def row1758 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2655, 1), (key2656, -1), (key2672, 1), (key2675, -1), (key2749, 1), (key2751, -1), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2962, -1), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck1758 : row1758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1758 := by decide +kernel

theorem rowEval1758 (x : Key → ℝ) : Integer.Sparse.eval row1758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1758, Integer.Sparse.eval_collectBalanced, rawRowCheck1758]

def rawRow1759 : Integer.Sparse Key := [(key2945, -2), (key3004, -2), (key2962, -2), (key2946, 1), (key2940, 1), (key2999, 1), (key2952, 1), (key3001, 1), (key2964, 1), (key2797, 2), (key2915, 2), (key2833, 2), (key2656, -1), (key2620, -1), (key2946, -1), (key2675, -1), (key2964, -1), (key2751, -1), (key2797, -1), (key2787, -1), (key2899, -1), (key2810, -1), (key2906, -1), (key2833, -1), (key2655, 1), (key2617, 1), (key2749, 1), (key2672, 1), (key2962, 1), (key2945, 1)]

theorem rawRowCheck1759 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form9 = rawRow1759 := by decide +kernel

def row1759 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2655, 1), (key2656, -1), (key2672, 1), (key2675, -1), (key2749, 1), (key2751, -1), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2962, -1), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck1759 : row1759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1759 := by decide +kernel

theorem rowEval1759 (x : Key → ℝ) : Integer.Sparse.eval row1759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1759, Integer.Sparse.eval_collectBalanced, rawRowCheck1759]

def rawRow1760 : Integer.Sparse Key := [(key2962, -2), (key2945, -2), (key3004, -2), (key2952, 1), (key2964, 1), (key2940, 1), (key3001, 1), (key2946, 1), (key2999, 1), (key2833, 2), (key2797, 2), (key2915, 2), (key2675, -1), (key2751, -1), (key2620, -1), (key2964, -1), (key2656, -1), (key2946, -1), (key2810, -1), (key2833, -1), (key2787, -1), (key2906, -1), (key2797, -1), (key2899, -1), (key2672, 1), (key2749, 1), (key2617, 1), (key2962, 1), (key2655, 1), (key2749, 1)]

theorem rawRowCheck1760 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form9 = rawRow1760 := by decide +kernel

def row1760 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2655, 1), (key2656, -1), (key2672, 1), (key2675, -1), (key2749, 2), (key2751, -1), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -2), (key2952, 1), (key2962, -1), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck1760 : row1760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1760 := by decide +kernel

theorem rowEval1760 (x : Key → ℝ) : Integer.Sparse.eval row1760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1760, Integer.Sparse.eval_collectBalanced, rawRowCheck1760]

def rawRow1761 : Integer.Sparse Key := [(key2962, -2), (key3004, -2), (key2945, -2), (key2964, 1), (key2952, 1), (key3001, 1), (key2940, 1), (key2999, 1), (key2946, 1), (key2833, 2), (key2915, 2), (key2797, 2), (key2751, -1), (key2675, -1), (key2964, -1), (key2620, -1), (key2946, -1), (key2656, -1), (key2833, -1), (key2810, -1), (key2906, -1), (key2787, -1), (key2899, -1), (key2797, -1), (key2749, 1), (key2672, 1), (key2962, 1), (key2617, 1), (key2749, 1), (key2655, 1)]

theorem rawRowCheck1761 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form9 = rawRow1761 := by decide +kernel

def row1761 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2655, 1), (key2656, -1), (key2672, 1), (key2675, -1), (key2749, 2), (key2751, -1), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -2), (key2952, 1), (key2962, -1), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck1761 : row1761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1761 := by decide +kernel

theorem rowEval1761 (x : Key → ℝ) : Integer.Sparse.eval row1761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck1761, Integer.Sparse.eval_collectBalanced, rawRowCheck1761]

def rawRow1762 : Integer.Sparse Key := [(key3004, -2), (key2945, -2), (key2962, -2), (key2999, 1), (key3001, 1), (key2946, 1), (key2964, 1), (key2940, 1), (key2952, 1), (key2915, 2), (key2797, 2), (key2833, 2), (key2946, -1), (key2964, -1), (key2656, -1), (key2751, -1), (key2620, -1), (key2675, -1), (key2899, -1), (key2906, -1), (key2797, -1), (key2833, -1), (key2787, -1), (key2810, -1), (key2945, 1), (key2962, 1), (key2655, 1), (key2749, 1), (key2617, 1), (key2672, 1)]

theorem rawRowCheck1762 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form9 = rawRow1762 := by decide +kernel

def row1762 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2655, 1), (key2656, -1), (key2672, 1), (key2675, -1), (key2749, 1), (key2751, -1), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2962, -1), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck1762 : row1762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1762 := by decide +kernel

theorem rowEval1762 (x : Key → ℝ) : Integer.Sparse.eval row1762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1762, Integer.Sparse.eval_collectBalanced, rawRowCheck1762]

def rawRow1763 : Integer.Sparse Key := [(key3004, -2), (key2962, -2), (key2945, -2), (key3001, 1), (key2999, 1), (key2964, 1), (key2946, 1), (key2952, 1), (key2940, 1), (key2915, 2), (key2833, 2), (key2797, 2), (key2964, -1), (key2946, -1), (key2751, -1), (key2656, -1), (key2675, -1), (key2620, -1), (key2906, -1), (key2899, -1), (key2833, -1), (key2797, -1), (key2810, -1), (key2787, -1), (key2962, 1), (key2945, 1), (key2749, 1), (key2655, 1), (key2672, 1), (key2617, 1)]

theorem rawRowCheck1763 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form9 = rawRow1763 := by decide +kernel

def row1763 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2655, 1), (key2656, -1), (key2672, 1), (key2675, -1), (key2749, 1), (key2751, -1), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2962, -1), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck1763 : row1763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1763 := by decide +kernel

theorem rowEval1763 (x : Key → ℝ) : Integer.Sparse.eval row1763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck1763, Integer.Sparse.eval_collectBalanced, rawRowCheck1763]

def rawRow1764 : Integer.Sparse Key := [(key2402, -2), (key2402, -2), (key2439, -2), (key2402, 1), (key2408, 1), (key2402, 1), (key2439, 1), (key2408, 1), (key2439, 1), (key2468, 2), (key2468, 2), (key2505, 2), (key2468, -1), (key2481, -1), (key2468, -1), (key2505, -1), (key2481, -1), (key2505, -1), (key2535, -1), (key2537, -1), (key2535, -1), (key2553, -1), (key2537, -1), (key2553, -1), (key2535, 1), (key2542, 1), (key2535, 1), (key2553, 1), (key2542, 1), (key2553, 1)]

theorem rawRowCheck1764 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form0 = rawRow1764 := by decide +kernel

def row1764 : Integer.Sparse Key := [(key2402, -2), (key2408, 2), (key2468, 2), (key2481, -2), (key2537, -2), (key2542, 2)]

theorem rowCheck1764 : row1764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1764 := by decide +kernel

theorem rowEval1764 (x : Key → ℝ) : Integer.Sparse.eval row1764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1764, Integer.Sparse.eval_collectBalanced, rawRowCheck1764]

def rawRow1765 : Integer.Sparse Key := [(key2402, -2), (key2439, -2), (key2402, -2), (key2408, 1), (key2402, 1), (key2439, 1), (key2402, 1), (key2439, 1), (key2408, 1), (key2468, 2), (key2505, 2), (key2468, 2), (key2481, -1), (key2468, -1), (key2505, -1), (key2468, -1), (key2505, -1), (key2481, -1), (key2537, -1), (key2535, -1), (key2553, -1), (key2535, -1), (key2553, -1), (key2537, -1), (key2542, 1), (key2535, 1), (key2553, 1), (key2535, 1), (key2553, 1), (key2542, 1)]

theorem rawRowCheck1765 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form0 = rawRow1765 := by decide +kernel

def row1765 : Integer.Sparse Key := [(key2402, -2), (key2408, 2), (key2468, 2), (key2481, -2), (key2537, -2), (key2542, 2)]

theorem rowCheck1765 : row1765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1765 := by decide +kernel

theorem rowEval1765 (x : Key → ℝ) : Integer.Sparse.eval row1765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1765, Integer.Sparse.eval_collectBalanced, rawRowCheck1765]

def rawRow1766 : Integer.Sparse Key := [(key2439, -2), (key2402, -2), (key2402, -2), (key2439, 1), (key2439, 1), (key2408, 1), (key2408, 1), (key2402, 1), (key2402, 1), (key2505, 2), (key2468, 2), (key2468, 2), (key2505, -1), (key2505, -1), (key2481, -1), (key2481, -1), (key2468, -1), (key2468, -1), (key2553, -1), (key2553, -1), (key2537, -1), (key2537, -1), (key2535, -1), (key2535, -1), (key2553, 1), (key2553, 1), (key2542, 1), (key2542, 1), (key2535, 1), (key2535, 1)]

theorem rawRowCheck1766 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form0 = rawRow1766 := by decide +kernel

def row1766 : Integer.Sparse Key := [(key2402, -2), (key2408, 2), (key2468, 2), (key2481, -2), (key2537, -2), (key2542, 2)]

theorem rowCheck1766 : row1766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1766 := by decide +kernel

theorem rowEval1766 (x : Key → ℝ) : Integer.Sparse.eval row1766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1766, Integer.Sparse.eval_collectBalanced, rawRowCheck1766]

def rawRow1767 : Integer.Sparse Key := [(key2408, -2), (key2408, -2), (key2408, -2), (key2402, 1), (key2402, 1), (key2402, 1), (key2402, 1), (key2402, 1), (key2402, 1), (key2481, 2), (key2481, 2), (key2481, 2), (key2468, -1), (key2468, -1), (key2468, -1), (key2468, -1), (key2468, -1), (key2468, -1), (key2542, -1), (key2542, -1), (key2542, -1), (key2542, -1), (key2542, -1), (key2542, -1), (key2537, 1), (key2537, 1), (key2537, 1), (key2537, 1), (key2537, 1), (key2537, 1)]

theorem rawRowCheck1767 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form0 = rawRow1767 := by decide +kernel

def row1767 : Integer.Sparse Key := [(key2402, 6), (key2408, -6), (key2468, -6), (key2481, 6), (key2537, 6), (key2542, -6)]

theorem rowCheck1767 : row1767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1767 := by decide +kernel

theorem rowEval1767 (x : Key → ℝ) : Integer.Sparse.eval row1767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1767, Integer.Sparse.eval_collectBalanced, rawRowCheck1767]

def rawRow1768 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key3020, -2), (key2878, 1), (key2884, 1), (key2878, 1), (key3029, 1), (key2884, 1), (key3029, 1), (key2402, 2), (key2402, 2), (key2439, 2), (key2535, -1), (key2542, -1), (key2535, -1), (key2553, -1), (key2542, -1), (key2553, -1), (key2402, -1), (key2408, -1), (key2402, -1), (key2439, -1), (key2408, -1), (key2439, -1), (key2468, 1), (key2481, 1), (key2468, 1), (key2505, 1), (key2481, 1), (key2505, 1)]

theorem rawRowCheck1768 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form0 = rawRow1768 := by decide +kernel

def row1768 : Integer.Sparse Key := [(key2402, 2), (key2408, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key3020, -2), (key3029, 2)]

theorem rowCheck1768 : row1768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1768 := by decide +kernel

theorem rowEval1768 (x : Key → ℝ) : Integer.Sparse.eval row1768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1768, Integer.Sparse.eval_collectBalanced, rawRowCheck1768]

def rawRow1769 : Integer.Sparse Key := [(key2847, -2), (key3020, -2), (key2847, -2), (key2884, 1), (key2878, 1), (key3029, 1), (key2878, 1), (key3029, 1), (key2884, 1), (key2402, 2), (key2439, 2), (key2402, 2), (key2542, -1), (key2535, -1), (key2553, -1), (key2535, -1), (key2553, -1), (key2542, -1), (key2408, -1), (key2402, -1), (key2439, -1), (key2402, -1), (key2439, -1), (key2408, -1), (key2481, 1), (key2468, 1), (key2505, 1), (key2468, 1), (key2505, 1), (key2481, 1)]

theorem rawRowCheck1769 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form0 = rawRow1769 := by decide +kernel

def row1769 : Integer.Sparse Key := [(key2402, 2), (key2408, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key3020, -2), (key3029, 2)]

theorem rowCheck1769 : row1769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1769 := by decide +kernel

theorem rowEval1769 (x : Key → ℝ) : Integer.Sparse.eval row1769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1769, Integer.Sparse.eval_collectBalanced, rawRowCheck1769]

def rawRow1770 : Integer.Sparse Key := [(key3020, -2), (key2847, -2), (key2847, -2), (key3029, 1), (key3029, 1), (key2884, 1), (key2884, 1), (key2878, 1), (key2878, 1), (key2439, 2), (key2402, 2), (key2402, 2), (key2553, -1), (key2553, -1), (key2542, -1), (key2542, -1), (key2535, -1), (key2535, -1), (key2439, -1), (key2439, -1), (key2408, -1), (key2408, -1), (key2402, -1), (key2402, -1), (key2505, 1), (key2505, 1), (key2481, 1), (key2481, 1), (key2468, 1), (key2468, 1)]

theorem rawRowCheck1770 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form0 = rawRow1770 := by decide +kernel

def row1770 : Integer.Sparse Key := [(key2402, 2), (key2408, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key3020, -2), (key3029, 2)]

theorem rowCheck1770 : row1770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1770 := by decide +kernel

theorem rowEval1770 (x : Key → ℝ) : Integer.Sparse.eval row1770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1770, Integer.Sparse.eval_collectBalanced, rawRowCheck1770]

def rawRow1771 : Integer.Sparse Key := [(key2596, -2), (key2884, -2), (key2884, -2), (key2591, 1), (key2591, 1), (key2847, 1), (key2847, 1), (key2878, 1), (key2878, 1), (key2605, 2), (key2926, 2), (key2926, 2), (key2591, -1), (key2591, -1), (key2770, -1), (key2770, -1), (key2878, -1), (key2878, -1), (key2391, -1), (key2391, -1), (key2481, -1), (key2481, -1), (key2542, -1), (key2542, -1), (key2380, 1), (key2380, 1), (key2408, 1), (key2408, 1), (key2537, 1), (key2537, 1)]

theorem rawRowCheck1771 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form0 = rawRow1771 := by decide +kernel

def row1771 : Integer.Sparse Key := [(key2380, 2), (key2391, -2), (key2408, 2), (key2481, -2), (key2537, 2), (key2542, -2), (key2596, -2), (key2605, 2), (key2770, -2), (key2847, 2), (key2884, -4), (key2926, 4)]

theorem rowCheck1771 : row1771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1771 := by decide +kernel

theorem rowEval1771 (x : Key → ℝ) : Integer.Sparse.eval row1771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1771, Integer.Sparse.eval_collectBalanced, rawRowCheck1771]

def rawRow1772 : Integer.Sparse Key := [(key2884, -2), (key2596, -2), (key2884, -2), (key2847, 1), (key2878, 1), (key2591, 1), (key2878, 1), (key2591, 1), (key2847, 1), (key2926, 2), (key2605, 2), (key2926, 2), (key2770, -1), (key2878, -1), (key2591, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2481, -1), (key2542, -1), (key2391, -1), (key2542, -1), (key2391, -1), (key2481, -1), (key2408, 1), (key2537, 1), (key2380, 1), (key2537, 1), (key2380, 1), (key2408, 1)]

theorem rawRowCheck1772 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form0 = rawRow1772 := by decide +kernel

def row1772 : Integer.Sparse Key := [(key2380, 2), (key2391, -2), (key2408, 2), (key2481, -2), (key2537, 2), (key2542, -2), (key2596, -2), (key2605, 2), (key2770, -2), (key2847, 2), (key2884, -4), (key2926, 4)]

theorem rowCheck1772 : row1772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1772 := by decide +kernel

theorem rowEval1772 (x : Key → ℝ) : Integer.Sparse.eval row1772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1772, Integer.Sparse.eval_collectBalanced, rawRowCheck1772]

def rawRow1773 : Integer.Sparse Key := [(key2884, -2), (key2884, -2), (key2596, -2), (key2878, 1), (key2847, 1), (key2878, 1), (key2591, 1), (key2847, 1), (key2591, 1), (key2926, 2), (key2926, 2), (key2605, 2), (key2878, -1), (key2770, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2591, -1), (key2542, -1), (key2481, -1), (key2542, -1), (key2391, -1), (key2481, -1), (key2391, -1), (key2537, 1), (key2408, 1), (key2537, 1), (key2380, 1), (key2408, 1), (key2380, 1)]

theorem rawRowCheck1773 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form0 = rawRow1773 := by decide +kernel

def row1773 : Integer.Sparse Key := [(key2380, 2), (key2391, -2), (key2408, 2), (key2481, -2), (key2537, 2), (key2542, -2), (key2596, -2), (key2605, 2), (key2770, -2), (key2847, 2), (key2884, -4), (key2926, 4)]

theorem rowCheck1773 : row1773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1773 := by decide +kernel

theorem rowEval1773 (x : Key → ℝ) : Integer.Sparse.eval row1773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck1773, Integer.Sparse.eval_collectBalanced, rawRowCheck1773]

def rawRow1774 : Integer.Sparse Key := [(key2917, -2), (key2917, -2), (key2917, -2), (key2926, 1), (key2926, 1), (key2926, 1), (key2926, 1), (key2926, 1), (key2926, 1), (key2775, 2), (key2775, 2), (key2775, 2), (key2884, -1), (key2884, -1), (key2884, -1), (key2884, -1), (key2884, -1), (key2884, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1)]

theorem rawRowCheck1774 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form0 = rawRow1774 := by decide +kernel

def row1774 : Integer.Sparse Key := [(key2770, -6), (key2775, 6), (key2847, 6), (key2884, -6), (key2917, -6), (key2926, 6)]

theorem rowCheck1774 : row1774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1774 := by decide +kernel

theorem rowEval1774 (x : Key → ℝ) : Integer.Sparse.eval row1774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1774, Integer.Sparse.eval_collectBalanced, rawRowCheck1774]

def rawRow1775 : Integer.Sparse Key := [(key2605, -2), (key2926, -2), (key2926, -2), (key2605, 1), (key2605, 1), (key2917, 1), (key2917, 1), (key2926, 1), (key2926, 1), (key2596, 2), (key2884, 2), (key2884, 2), (key2596, -1), (key2596, -1), (key2775, -1), (key2775, -1), (key2884, -1), (key2884, -1), (key2591, -1), (key2591, -1), (key2847, -1), (key2847, -1), (key2878, -1), (key2878, -1), (key2591, 1), (key2591, 1), (key2770, 1), (key2770, 1), (key2878, 1), (key2878, 1)]

theorem rawRowCheck1775 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form0 = rawRow1775 := by decide +kernel

def row1775 : Integer.Sparse Key := [(key2770, 2), (key2775, -2), (key2847, -2), (key2884, 2), (key2917, 2), (key2926, -2)]

theorem rowCheck1775 : row1775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1775 := by decide +kernel

theorem rowEval1775 (x : Key → ℝ) : Integer.Sparse.eval row1775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1775, Integer.Sparse.eval_collectBalanced, rawRowCheck1775]

def rawRow1776 : Integer.Sparse Key := [(key2926, -2), (key2605, -2), (key2926, -2), (key2917, 1), (key2926, 1), (key2605, 1), (key2926, 1), (key2605, 1), (key2917, 1), (key2884, 2), (key2596, 2), (key2884, 2), (key2775, -1), (key2884, -1), (key2596, -1), (key2884, -1), (key2596, -1), (key2775, -1), (key2847, -1), (key2878, -1), (key2591, -1), (key2878, -1), (key2591, -1), (key2847, -1), (key2770, 1), (key2878, 1), (key2591, 1), (key2878, 1), (key2591, 1), (key2770, 1)]

theorem rawRowCheck1776 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form0 = rawRow1776 := by decide +kernel

def row1776 : Integer.Sparse Key := [(key2770, 2), (key2775, -2), (key2847, -2), (key2884, 2), (key2917, 2), (key2926, -2)]

theorem rowCheck1776 : row1776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1776 := by decide +kernel

theorem rowEval1776 (x : Key → ℝ) : Integer.Sparse.eval row1776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1776, Integer.Sparse.eval_collectBalanced, rawRowCheck1776]

def rawRow1777 : Integer.Sparse Key := [(key2926, -2), (key2926, -2), (key2605, -2), (key2926, 1), (key2917, 1), (key2926, 1), (key2605, 1), (key2917, 1), (key2605, 1), (key2884, 2), (key2884, 2), (key2596, 2), (key2884, -1), (key2775, -1), (key2884, -1), (key2596, -1), (key2775, -1), (key2596, -1), (key2878, -1), (key2847, -1), (key2878, -1), (key2591, -1), (key2847, -1), (key2591, -1), (key2878, 1), (key2770, 1), (key2878, 1), (key2591, 1), (key2770, 1), (key2591, 1)]

theorem rawRowCheck1777 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form0 = rawRow1777 := by decide +kernel

def row1777 : Integer.Sparse Key := [(key2770, 2), (key2775, -2), (key2847, -2), (key2884, 2), (key2917, 2), (key2926, -2)]

theorem rowCheck1777 : row1777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1777 := by decide +kernel

theorem rowEval1777 (x : Key → ℝ) : Integer.Sparse.eval row1777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck1777, Integer.Sparse.eval_collectBalanced, rawRowCheck1777]

def rawRow1778 : Integer.Sparse Key := [(key1250, -6), (key1250, 2), (key1250, 2), (key1269, 2), (key1525, 6), (key1525, -2), (key1525, -2), (key1892, -2), (key1603, -2), (key1603, -2), (key1677, -2), (key1603, 2), (key1603, 2), (key1914, 2)]

theorem rawRowCheck1778 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form1 = rawRow1778 := by decide +kernel

def row1778 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

theorem rowCheck1778 : row1778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1778 := by decide +kernel

theorem rowEval1778 (x : Key → ℝ) : Integer.Sparse.eval row1778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1778, Integer.Sparse.eval_collectBalanced, rawRowCheck1778]

def rawRow1779 : Integer.Sparse Key := [(key1250, -6), (key1250, 2), (key1269, 2), (key1250, 2), (key1525, 6), (key1525, -2), (key1892, -2), (key1525, -2), (key1603, -2), (key1677, -2), (key1603, -2), (key1603, 2), (key1914, 2), (key1603, 2)]

theorem rawRowCheck1779 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form1 = rawRow1779 := by decide +kernel

def row1779 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

theorem rowCheck1779 : row1779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1779 := by decide +kernel

theorem rowEval1779 (x : Key → ℝ) : Integer.Sparse.eval row1779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1779, Integer.Sparse.eval_collectBalanced, rawRowCheck1779]

def rawRow1780 : Integer.Sparse Key := [(key1250, -6), (key1269, 2), (key1250, 2), (key1250, 2), (key1525, 6), (key1892, -2), (key1525, -2), (key1525, -2), (key1677, -2), (key1603, -2), (key1603, -2), (key1914, 2), (key1603, 2), (key1603, 2)]

theorem rawRowCheck1780 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form1 = rawRow1780 := by decide +kernel

def row1780 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

theorem rowCheck1780 : row1780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1780 := by decide +kernel

theorem rowEval1780 (x : Key → ℝ) : Integer.Sparse.eval row1780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1780, Integer.Sparse.eval_collectBalanced, rawRowCheck1780]

def rawRow1781 : Integer.Sparse Key := [(key1269, -6), (key1250, 2), (key1250, 2), (key1250, 2), (key1892, 6), (key1525, -2), (key1525, -2), (key1525, -2), (key1914, -2), (key1914, -2), (key1914, -2), (key1677, 2), (key1677, 2), (key1677, 2)]

theorem rawRowCheck1781 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form1 = rawRow1781 := by decide +kernel

def row1781 : Integer.Sparse Key := [(key1250, 6), (key1269, -6), (key1525, -6), (key1677, 6), (key1892, 6), (key1914, -6)]

theorem rowCheck1781 : row1781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1781 := by decide +kernel

theorem rowEval1781 (x : Key → ℝ) : Integer.Sparse.eval row1781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1781, Integer.Sparse.eval_collectBalanced, rawRowCheck1781]

def rawRow1782 : Integer.Sparse Key := [(key1525, -6), (key1603, 2), (key1603, 2), (key1677, 2), (key1250, 6), (key1603, -2), (key1603, -2), (key1914, -2), (key1250, -2), (key1250, -2), (key1269, -2), (key1525, 2), (key1525, 2), (key1892, 2)]

theorem rawRowCheck1782 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form1 = rawRow1782 := by decide +kernel

def row1782 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

theorem rowCheck1782 : row1782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1782 := by decide +kernel

theorem rowEval1782 (x : Key → ℝ) : Integer.Sparse.eval row1782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1782, Integer.Sparse.eval_collectBalanced, rawRowCheck1782]

def rawRow1783 : Integer.Sparse Key := [(key1525, -6), (key1603, 2), (key1677, 2), (key1603, 2), (key1250, 6), (key1603, -2), (key1914, -2), (key1603, -2), (key1250, -2), (key1269, -2), (key1250, -2), (key1525, 2), (key1892, 2), (key1525, 2)]

theorem rawRowCheck1783 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form1 = rawRow1783 := by decide +kernel

def row1783 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

theorem rowCheck1783 : row1783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1783 := by decide +kernel

theorem rowEval1783 (x : Key → ℝ) : Integer.Sparse.eval row1783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1783, Integer.Sparse.eval_collectBalanced, rawRowCheck1783]

def rawRow1784 : Integer.Sparse Key := [(key1525, -6), (key1677, 2), (key1603, 2), (key1603, 2), (key1250, 6), (key1914, -2), (key1603, -2), (key1603, -2), (key1269, -2), (key1250, -2), (key1250, -2), (key1892, 2), (key1525, 2), (key1525, 2)]

theorem rawRowCheck1784 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form1 = rawRow1784 := by decide +kernel

def row1784 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

theorem rowCheck1784 : row1784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1784 := by decide +kernel

theorem rowEval1784 (x : Key → ℝ) : Integer.Sparse.eval row1784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1784, Integer.Sparse.eval_collectBalanced, rawRowCheck1784]

def rawRow1785 : Integer.Sparse Key := [(key1677, -6), (key1525, 2), (key1603, 2), (key1603, 2), (key1914, 6), (key1250, -2), (key1603, -2), (key1603, -2), (key1892, -2), (key1914, -2), (key1914, -2), (key1269, 2), (key1677, 2), (key1677, 2)]

theorem rawRowCheck1785 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form1 = rawRow1785 := by decide +kernel

def row1785 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

theorem rowCheck1785 : row1785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1785 := by decide +kernel

theorem rowEval1785 (x : Key → ℝ) : Integer.Sparse.eval row1785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1785, Integer.Sparse.eval_collectBalanced, rawRowCheck1785]

def rawRow1786 : Integer.Sparse Key := [(key1677, -6), (key1603, 2), (key1525, 2), (key1603, 2), (key1914, 6), (key1603, -2), (key1250, -2), (key1603, -2), (key1914, -2), (key1892, -2), (key1914, -2), (key1677, 2), (key1269, 2), (key1677, 2)]

theorem rawRowCheck1786 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form1 = rawRow1786 := by decide +kernel

def row1786 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

theorem rowCheck1786 : row1786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1786 := by decide +kernel

theorem rowEval1786 (x : Key → ℝ) : Integer.Sparse.eval row1786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1786, Integer.Sparse.eval_collectBalanced, rawRowCheck1786]

def rawRow1787 : Integer.Sparse Key := [(key1677, -6), (key1603, 2), (key1603, 2), (key1525, 2), (key1914, 6), (key1603, -2), (key1603, -2), (key1250, -2), (key1914, -2), (key1914, -2), (key1892, -2), (key1677, 2), (key1677, 2), (key1269, 2)]

theorem rawRowCheck1787 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form1 = rawRow1787 := by decide +kernel

def row1787 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

theorem rowCheck1787 : row1787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1787 := by decide +kernel

theorem rowEval1787 (x : Key → ℝ) : Integer.Sparse.eval row1787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck1787, Integer.Sparse.eval_collectBalanced, rawRowCheck1787]

def rawRow1788 : Integer.Sparse Key := [(key1892, -6), (key1914, 2), (key1914, 2), (key1914, 2), (key1269, 6), (key1677, -2), (key1677, -2), (key1677, -2), (key1250, -2), (key1250, -2), (key1250, -2), (key1525, 2), (key1525, 2), (key1525, 2)]

theorem rawRowCheck1788 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form1 = rawRow1788 := by decide +kernel

def row1788 : Integer.Sparse Key := [(key1250, -6), (key1269, 6), (key1525, 6), (key1677, -6), (key1892, -6), (key1914, 6)]

theorem rowCheck1788 : row1788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1788 := by decide +kernel

theorem rowEval1788 (x : Key → ℝ) : Integer.Sparse.eval row1788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1788, Integer.Sparse.eval_collectBalanced, rawRowCheck1788]

def rawRow1789 : Integer.Sparse Key := [(key1914, -6), (key1892, 2), (key1914, 2), (key1914, 2), (key1677, 6), (key1269, -2), (key1677, -2), (key1677, -2), (key1525, -2), (key1603, -2), (key1603, -2), (key1250, 2), (key1603, 2), (key1603, 2)]

theorem rawRowCheck1789 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form1 = rawRow1789 := by decide +kernel

def row1789 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

theorem rowCheck1789 : row1789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1789 := by decide +kernel

theorem rowEval1789 (x : Key → ℝ) : Integer.Sparse.eval row1789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1789, Integer.Sparse.eval_collectBalanced, rawRowCheck1789]

def rawRow1790 : Integer.Sparse Key := [(key1914, -6), (key1914, 2), (key1892, 2), (key1914, 2), (key1677, 6), (key1677, -2), (key1269, -2), (key1677, -2), (key1603, -2), (key1525, -2), (key1603, -2), (key1603, 2), (key1250, 2), (key1603, 2)]

theorem rawRowCheck1790 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form1 = rawRow1790 := by decide +kernel

def row1790 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

theorem rowCheck1790 : row1790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1790 := by decide +kernel

theorem rowEval1790 (x : Key → ℝ) : Integer.Sparse.eval row1790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1790, Integer.Sparse.eval_collectBalanced, rawRowCheck1790]

def rawRow1791 : Integer.Sparse Key := [(key1914, -6), (key1914, 2), (key1914, 2), (key1892, 2), (key1677, 6), (key1677, -2), (key1677, -2), (key1269, -2), (key1603, -2), (key1603, -2), (key1525, -2), (key1603, 2), (key1603, 2), (key1250, 2)]

theorem rawRowCheck1791 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form1 = rawRow1791 := by decide +kernel

def row1791 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

theorem rowCheck1791 : row1791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1791 := by decide +kernel

theorem rowEval1791 (x : Key → ℝ) : Integer.Sparse.eval row1791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck1791, Integer.Sparse.eval_collectBalanced, rawRowCheck1791]

end MUB6.Certificate.GramRows

end OAI
