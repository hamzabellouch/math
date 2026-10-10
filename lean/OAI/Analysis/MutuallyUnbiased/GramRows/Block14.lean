import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
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

def rawRow544 : Integer.Sparse Key := [(key2973, -1), (key2982, -1), (key2975, 2), (key2949, 1), (key2959, 1), (key2942, -1), (key2975, -1), (key2949, -2), (key2937, 1), (key2973, 1), (key2894, 1), (key2903, 1), (key2896, -2), (key2736, -1), (key2746, -1), (key2652, 1), (key2896, 1), (key2736, 2), (key2647, -1), (key2894, -1), (key2806, -1), (key2826, -1), (key2791, 1), (key2857, 1), (key2703, 1), (key2723, 1), (key2637, -1), (key2857, -1), (key2668, -1), (key2703, -1), (key2613, 1), (key2806, 1), (key2802, 2), (key2779, -1), (key2852, -1), (key2699, -2), (key2625, 1), (key2852, 1), (key2664, 1), (key2699, 1), (key2609, -1), (key2802, -1)]

theorem rawRowCheck544 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form2 = rawRow544 := by decide +kernel

def row544 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck544 : row544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow544 := by decide +kernel

theorem rowEval544 (x : Key → ℝ) : Integer.Sparse.eval row544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck544, Integer.Sparse.eval_collectBalanced, rawRowCheck544]

def rawRow545 : Integer.Sparse Key := [(key2982, -1), (key2973, -1), (key2975, 2), (key2959, 1), (key2949, 1), (key2975, -1), (key2942, -1), (key2949, -2), (key2973, 1), (key2937, 1), (key2903, 1), (key2894, 1), (key2896, -2), (key2746, -1), (key2736, -1), (key2896, 1), (key2652, 1), (key2736, 2), (key2894, -1), (key2647, -1), (key2826, -1), (key2806, -1), (key2857, 1), (key2791, 1), (key2723, 1), (key2703, 1), (key2857, -1), (key2637, -1), (key2703, -1), (key2668, -1), (key2806, 1), (key2613, 1), (key2802, 2), (key2852, -1), (key2779, -1), (key2699, -2), (key2852, 1), (key2625, 1), (key2699, 1), (key2664, 1), (key2802, -1), (key2609, -1)]

theorem rawRowCheck545 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form2 = rawRow545 := by decide +kernel

def row545 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck545 : row545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow545 := by decide +kernel

theorem rowEval545 (x : Key → ℝ) : Integer.Sparse.eval row545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck545, Integer.Sparse.eval_collectBalanced, rawRowCheck545]

def rawRow546 : Integer.Sparse Key := [(key1300, -2), (key1300, 1), (key1304, 1), (key1320, 2), (key1320, -1), (key1341, -1), (key1328, -1), (key1331, -1), (key1328, 1), (key1347, 1), (key1395, 2), (key1395, -1), (key1399, -1), (key1550, -2), (key1550, 1), (key1776, 1), (key1558, 1), (key1561, 1), (key1558, -1), (key1782, -1), (key1428, -2), (key1428, 1), (key1459, 1), (key1577, 2), (key1577, -1), (key1792, -1), (key1626, -1), (key1661, -1), (key1626, 1), (key1819, 1), (key1446, 1), (key1449, 1), (key1446, -1), (key1468, -1), (key1595, -1), (key1598, -1), (key1595, 1), (key1800, 1), (key1635, 1), (key1669, 1), (key1635, -1), (key1827, -1)]

theorem rawRowCheck546 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form3 = rawRow546 := by decide +kernel

def row546 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck546 : row546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow546 := by decide +kernel

theorem rowEval546 (x : Key → ℝ) : Integer.Sparse.eval row546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck546, Integer.Sparse.eval_collectBalanced, rawRowCheck546]

def rawRow547 : Integer.Sparse Key := [(key1300, -2), (key1304, 1), (key1300, 1), (key1320, 2), (key1341, -1), (key1320, -1), (key1331, -1), (key1328, -1), (key1347, 1), (key1328, 1), (key1395, 2), (key1399, -1), (key1395, -1), (key1550, -2), (key1776, 1), (key1550, 1), (key1561, 1), (key1558, 1), (key1782, -1), (key1558, -1), (key1428, -2), (key1459, 1), (key1428, 1), (key1577, 2), (key1792, -1), (key1577, -1), (key1661, -1), (key1626, -1), (key1819, 1), (key1626, 1), (key1449, 1), (key1446, 1), (key1468, -1), (key1446, -1), (key1598, -1), (key1595, -1), (key1800, 1), (key1595, 1), (key1669, 1), (key1635, 1), (key1827, -1), (key1635, -1)]

theorem rawRowCheck547 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form3 = rawRow547 := by decide +kernel

def row547 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck547 : row547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow547 := by decide +kernel

theorem rowEval547 (x : Key → ℝ) : Integer.Sparse.eval row547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck547, Integer.Sparse.eval_collectBalanced, rawRowCheck547]

def rawRow548 : Integer.Sparse Key := [(key1304, -2), (key1300, 1), (key1300, 1), (key1341, 2), (key1320, -1), (key1320, -1), (key1347, -1), (key1347, -1), (key1331, 1), (key1331, 1), (key1399, 2), (key1395, -1), (key1395, -1), (key1776, -2), (key1550, 1), (key1550, 1), (key1782, 1), (key1782, 1), (key1561, -1), (key1561, -1), (key1459, -2), (key1428, 1), (key1428, 1), (key1792, 2), (key1577, -1), (key1577, -1), (key1819, -1), (key1819, -1), (key1661, 1), (key1661, 1), (key1468, 1), (key1468, 1), (key1449, -1), (key1449, -1), (key1800, -1), (key1800, -1), (key1598, 1), (key1598, 1), (key1827, 1), (key1827, 1), (key1669, -1), (key1669, -1)]

theorem rawRowCheck548 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form3 = rawRow548 := by decide +kernel

def row548 : Integer.Sparse Key := [(key1300, 2), (key1304, -2), (key1320, -2), (key1331, 2), (key1341, 2), (key1347, -2), (key1395, -2), (key1399, 2), (key1428, 2), (key1449, -2), (key1459, -2), (key1468, 2), (key1550, 2), (key1561, -2), (key1577, -2), (key1598, 2), (key1661, 2), (key1669, -2), (key1776, -2), (key1782, 2), (key1792, 2), (key1800, -2), (key1819, -2), (key1827, 2)]

theorem rowCheck548 : row548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow548 := by decide +kernel

theorem rowEval548 (x : Key → ℝ) : Integer.Sparse.eval row548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck548, Integer.Sparse.eval_collectBalanced, rawRowCheck548]

def rawRow549 : Integer.Sparse Key := [(key1320, -2), (key1328, 1), (key1331, 1), (key1300, 2), (key1328, -1), (key1347, -1), (key1300, -1), (key1304, -1), (key1320, 1), (key1341, 1), (key1550, 2), (key1558, -1), (key1561, -1), (key1395, -2), (key1558, 1), (key1782, 1), (key1395, 1), (key1399, 1), (key1550, -1), (key1776, -1), (key1577, -2), (key1626, 1), (key1661, 1), (key1428, 2), (key1626, -1), (key1819, -1), (key1428, -1), (key1459, -1), (key1577, 1), (key1792, 1), (key1595, 1), (key1598, 1), (key1635, -1), (key1669, -1), (key1446, -1), (key1449, -1), (key1635, 1), (key1827, 1), (key1446, 1), (key1468, 1), (key1595, -1), (key1800, -1)]

theorem rawRowCheck549 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form3 = rawRow549 := by decide +kernel

def row549 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck549 : row549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow549 := by decide +kernel

theorem rowEval549 (x : Key → ℝ) : Integer.Sparse.eval row549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck549, Integer.Sparse.eval_collectBalanced, rawRowCheck549]

def rawRow550 : Integer.Sparse Key := [(key1320, -2), (key1331, 1), (key1328, 1), (key1300, 2), (key1347, -1), (key1328, -1), (key1304, -1), (key1300, -1), (key1341, 1), (key1320, 1), (key1550, 2), (key1561, -1), (key1558, -1), (key1395, -2), (key1782, 1), (key1558, 1), (key1399, 1), (key1395, 1), (key1776, -1), (key1550, -1), (key1577, -2), (key1661, 1), (key1626, 1), (key1428, 2), (key1819, -1), (key1626, -1), (key1459, -1), (key1428, -1), (key1792, 1), (key1577, 1), (key1598, 1), (key1595, 1), (key1669, -1), (key1635, -1), (key1449, -1), (key1446, -1), (key1827, 1), (key1635, 1), (key1468, 1), (key1446, 1), (key1800, -1), (key1595, -1)]

theorem rawRowCheck550 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form3 = rawRow550 := by decide +kernel

def row550 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck550 : row550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow550 := by decide +kernel

theorem rowEval550 (x : Key → ℝ) : Integer.Sparse.eval row550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck550, Integer.Sparse.eval_collectBalanced, rawRowCheck550]

def rawRow551 : Integer.Sparse Key := [(key1331, -2), (key1320, 1), (key1328, 1), (key1347, 2), (key1300, -1), (key1328, -1), (key1341, -1), (key1347, -1), (key1304, 1), (key1331, 1), (key1561, 2), (key1550, -1), (key1558, -1), (key1782, -2), (key1395, 1), (key1558, 1), (key1776, 1), (key1782, 1), (key1399, -1), (key1561, -1), (key1661, -2), (key1577, 1), (key1626, 1), (key1819, 2), (key1428, -1), (key1626, -1), (key1792, -1), (key1819, -1), (key1459, 1), (key1661, 1), (key1669, 1), (key1675, 1), (key1598, -1), (key1643, -1), (key1827, -1), (key1833, -1), (key1449, 1), (key1643, 1), (key1800, 1), (key1833, 1), (key1468, -1), (key1675, -1)]

theorem rawRowCheck551 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form3 = rawRow551 := by decide +kernel

def row551 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck551 : row551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow551 := by decide +kernel

theorem rowEval551 (x : Key → ℝ) : Integer.Sparse.eval row551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck551, Integer.Sparse.eval_collectBalanced, rawRowCheck551]

def rawRow552 : Integer.Sparse Key := [(key1331, -2), (key1328, 1), (key1320, 1), (key1347, 2), (key1328, -1), (key1300, -1), (key1347, -1), (key1341, -1), (key1331, 1), (key1304, 1), (key1561, 2), (key1558, -1), (key1550, -1), (key1782, -2), (key1558, 1), (key1395, 1), (key1782, 1), (key1776, 1), (key1561, -1), (key1399, -1), (key1661, -2), (key1626, 1), (key1577, 1), (key1819, 2), (key1626, -1), (key1428, -1), (key1819, -1), (key1792, -1), (key1661, 1), (key1459, 1), (key1675, 1), (key1669, 1), (key1643, -1), (key1598, -1), (key1833, -1), (key1827, -1), (key1643, 1), (key1449, 1), (key1833, 1), (key1800, 1), (key1675, -1), (key1468, -1)]

theorem rawRowCheck552 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form3 = rawRow552 := by decide +kernel

def row552 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck552 : row552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow552 := by decide +kernel

theorem rowEval552 (x : Key → ℝ) : Integer.Sparse.eval row552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form3) x := by
  rw [rowCheck552, Integer.Sparse.eval_collectBalanced, rawRowCheck552]

def rawRow553 : Integer.Sparse Key := [(key1341, -2), (key1347, 1), (key1347, 1), (key1304, 2), (key1331, -1), (key1331, -1), (key1300, -1), (key1300, -1), (key1320, 1), (key1320, 1), (key1776, 2), (key1782, -1), (key1782, -1), (key1399, -2), (key1561, 1), (key1561, 1), (key1395, 1), (key1395, 1), (key1550, -1), (key1550, -1), (key1792, -2), (key1819, 1), (key1819, 1), (key1459, 2), (key1661, -1), (key1661, -1), (key1428, -1), (key1428, -1), (key1577, 1), (key1577, 1), (key1800, 1), (key1800, 1), (key1827, -1), (key1827, -1), (key1468, -1), (key1468, -1), (key1669, 1), (key1669, 1), (key1449, 1), (key1449, 1), (key1598, -1), (key1598, -1)]

theorem rawRowCheck553 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form3 = rawRow553 := by decide +kernel

def row553 : Integer.Sparse Key := [(key1300, -2), (key1304, 2), (key1320, 2), (key1331, -2), (key1341, -2), (key1347, 2), (key1395, 2), (key1399, -2), (key1428, -2), (key1449, 2), (key1459, 2), (key1468, -2), (key1550, -2), (key1561, 2), (key1577, 2), (key1598, -2), (key1661, -2), (key1669, 2), (key1776, 2), (key1782, -2), (key1792, -2), (key1800, 2), (key1819, 2), (key1827, -2)]

theorem rowCheck553 : row553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow553 := by decide +kernel

theorem rowEval553 (x : Key → ℝ) : Integer.Sparse.eval row553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck553, Integer.Sparse.eval_collectBalanced, rawRowCheck553]

def rawRow554 : Integer.Sparse Key := [(key1347, -2), (key1341, 1), (key1347, 1), (key1331, 2), (key1304, -1), (key1331, -1), (key1320, -1), (key1328, -1), (key1300, 1), (key1328, 1), (key1782, 2), (key1776, -1), (key1782, -1), (key1561, -2), (key1399, 1), (key1561, 1), (key1550, 1), (key1558, 1), (key1395, -1), (key1558, -1), (key1819, -2), (key1792, 1), (key1819, 1), (key1661, 2), (key1459, -1), (key1661, -1), (key1577, -1), (key1626, -1), (key1428, 1), (key1626, 1), (key1827, 1), (key1833, 1), (key1800, -1), (key1833, -1), (key1669, -1), (key1675, -1), (key1468, 1), (key1675, 1), (key1598, 1), (key1643, 1), (key1449, -1), (key1643, -1)]

theorem rawRowCheck554 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form3 = rawRow554 := by decide +kernel

def row554 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck554 : row554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow554 := by decide +kernel

theorem rowEval554 (x : Key → ℝ) : Integer.Sparse.eval row554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck554, Integer.Sparse.eval_collectBalanced, rawRowCheck554]

def rawRow555 : Integer.Sparse Key := [(key1347, -2), (key1347, 1), (key1341, 1), (key1331, 2), (key1331, -1), (key1304, -1), (key1328, -1), (key1320, -1), (key1328, 1), (key1300, 1), (key1782, 2), (key1782, -1), (key1776, -1), (key1561, -2), (key1561, 1), (key1399, 1), (key1558, 1), (key1550, 1), (key1558, -1), (key1395, -1), (key1819, -2), (key1819, 1), (key1792, 1), (key1661, 2), (key1661, -1), (key1459, -1), (key1626, -1), (key1577, -1), (key1626, 1), (key1428, 1), (key1833, 1), (key1827, 1), (key1833, -1), (key1800, -1), (key1675, -1), (key1669, -1), (key1675, 1), (key1468, 1), (key1643, 1), (key1598, 1), (key1643, -1), (key1449, -1)]

theorem rawRowCheck555 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form3 = rawRow555 := by decide +kernel

def row555 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck555 : row555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow555 := by decide +kernel

theorem rowEval555 (x : Key → ℝ) : Integer.Sparse.eval row555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form3) x := by
  rw [rowCheck555, Integer.Sparse.eval_collectBalanced, rawRowCheck555]

def rawRow556 : Integer.Sparse Key := [(key1395, -2), (key1395, 1), (key1399, 1), (key1428, 2), (key1428, -1), (key1459, -1), (key1446, -1), (key1449, -1), (key1446, 1), (key1468, 1), (key1300, 2), (key1300, -1), (key1304, -1), (key1577, -2), (key1577, 1), (key1792, 1), (key1595, 1), (key1598, 1), (key1595, -1), (key1800, -1), (key1320, -2), (key1320, 1), (key1341, 1), (key1550, 2), (key1550, -1), (key1776, -1), (key1635, -1), (key1669, -1), (key1635, 1), (key1827, 1), (key1328, 1), (key1331, 1), (key1328, -1), (key1347, -1), (key1558, -1), (key1561, -1), (key1558, 1), (key1782, 1), (key1626, 1), (key1661, 1), (key1626, -1), (key1819, -1)]

theorem rawRowCheck556 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form3 = rawRow556 := by decide +kernel

def row556 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck556 : row556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow556 := by decide +kernel

theorem rowEval556 (x : Key → ℝ) : Integer.Sparse.eval row556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck556, Integer.Sparse.eval_collectBalanced, rawRowCheck556]

def rawRow557 : Integer.Sparse Key := [(key1395, -2), (key1399, 1), (key1395, 1), (key1428, 2), (key1459, -1), (key1428, -1), (key1449, -1), (key1446, -1), (key1468, 1), (key1446, 1), (key1300, 2), (key1304, -1), (key1300, -1), (key1577, -2), (key1792, 1), (key1577, 1), (key1598, 1), (key1595, 1), (key1800, -1), (key1595, -1), (key1320, -2), (key1341, 1), (key1320, 1), (key1550, 2), (key1776, -1), (key1550, -1), (key1669, -1), (key1635, -1), (key1827, 1), (key1635, 1), (key1331, 1), (key1328, 1), (key1347, -1), (key1328, -1), (key1561, -1), (key1558, -1), (key1782, 1), (key1558, 1), (key1661, 1), (key1626, 1), (key1819, -1), (key1626, -1)]

theorem rawRowCheck557 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form3 = rawRow557 := by decide +kernel

def row557 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck557 : row557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow557 := by decide +kernel

theorem rowEval557 (x : Key → ℝ) : Integer.Sparse.eval row557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck557, Integer.Sparse.eval_collectBalanced, rawRowCheck557]

def rawRow558 : Integer.Sparse Key := [(key1399, -2), (key1395, 1), (key1395, 1), (key1459, 2), (key1428, -1), (key1428, -1), (key1468, -1), (key1468, -1), (key1449, 1), (key1449, 1), (key1304, 2), (key1300, -1), (key1300, -1), (key1792, -2), (key1577, 1), (key1577, 1), (key1800, 1), (key1800, 1), (key1598, -1), (key1598, -1), (key1341, -2), (key1320, 1), (key1320, 1), (key1776, 2), (key1550, -1), (key1550, -1), (key1827, -1), (key1827, -1), (key1669, 1), (key1669, 1), (key1347, 1), (key1347, 1), (key1331, -1), (key1331, -1), (key1782, -1), (key1782, -1), (key1561, 1), (key1561, 1), (key1819, 1), (key1819, 1), (key1661, -1), (key1661, -1)]

theorem rawRowCheck558 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form3 = rawRow558 := by decide +kernel

def row558 : Integer.Sparse Key := [(key1300, -2), (key1304, 2), (key1320, 2), (key1331, -2), (key1341, -2), (key1347, 2), (key1395, 2), (key1399, -2), (key1428, -2), (key1449, 2), (key1459, 2), (key1468, -2), (key1550, -2), (key1561, 2), (key1577, 2), (key1598, -2), (key1661, -2), (key1669, 2), (key1776, 2), (key1782, -2), (key1792, -2), (key1800, 2), (key1819, 2), (key1827, -2)]

theorem rowCheck558 : row558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow558 := by decide +kernel

theorem rowEval558 (x : Key → ℝ) : Integer.Sparse.eval row558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck558, Integer.Sparse.eval_collectBalanced, rawRowCheck558]

def rawRow559 : Integer.Sparse Key := [(key1428, -2), (key1446, 1), (key1449, 1), (key1395, 2), (key1446, -1), (key1468, -1), (key1395, -1), (key1399, -1), (key1428, 1), (key1459, 1), (key1577, 2), (key1595, -1), (key1598, -1), (key1300, -2), (key1595, 1), (key1800, 1), (key1300, 1), (key1304, 1), (key1577, -1), (key1792, -1), (key1550, -2), (key1635, 1), (key1669, 1), (key1320, 2), (key1635, -1), (key1827, -1), (key1320, -1), (key1341, -1), (key1550, 1), (key1776, 1), (key1558, 1), (key1561, 1), (key1626, -1), (key1661, -1), (key1328, -1), (key1331, -1), (key1626, 1), (key1819, 1), (key1328, 1), (key1347, 1), (key1558, -1), (key1782, -1)]

theorem rawRowCheck559 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form3 = rawRow559 := by decide +kernel

def row559 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck559 : row559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow559 := by decide +kernel

theorem rowEval559 (x : Key → ℝ) : Integer.Sparse.eval row559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck559, Integer.Sparse.eval_collectBalanced, rawRowCheck559]

def rawRow560 : Integer.Sparse Key := [(key1428, -2), (key1449, 1), (key1446, 1), (key1395, 2), (key1468, -1), (key1446, -1), (key1399, -1), (key1395, -1), (key1459, 1), (key1428, 1), (key1577, 2), (key1598, -1), (key1595, -1), (key1300, -2), (key1800, 1), (key1595, 1), (key1304, 1), (key1300, 1), (key1792, -1), (key1577, -1), (key1550, -2), (key1669, 1), (key1635, 1), (key1320, 2), (key1827, -1), (key1635, -1), (key1341, -1), (key1320, -1), (key1776, 1), (key1550, 1), (key1561, 1), (key1558, 1), (key1661, -1), (key1626, -1), (key1331, -1), (key1328, -1), (key1819, 1), (key1626, 1), (key1347, 1), (key1328, 1), (key1782, -1), (key1558, -1)]

theorem rawRowCheck560 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form3 = rawRow560 := by decide +kernel

def row560 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck560 : row560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow560 := by decide +kernel

theorem rowEval560 (x : Key → ℝ) : Integer.Sparse.eval row560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck560, Integer.Sparse.eval_collectBalanced, rawRowCheck560]

def rawRow561 : Integer.Sparse Key := [(key1449, -2), (key1428, 1), (key1446, 1), (key1468, 2), (key1395, -1), (key1446, -1), (key1459, -1), (key1468, -1), (key1399, 1), (key1449, 1), (key1598, 2), (key1577, -1), (key1595, -1), (key1800, -2), (key1300, 1), (key1595, 1), (key1792, 1), (key1800, 1), (key1304, -1), (key1598, -1), (key1669, -2), (key1550, 1), (key1635, 1), (key1827, 2), (key1320, -1), (key1635, -1), (key1776, -1), (key1827, -1), (key1341, 1), (key1669, 1), (key1661, 1), (key1675, 1), (key1561, -1), (key1643, -1), (key1819, -1), (key1833, -1), (key1331, 1), (key1643, 1), (key1782, 1), (key1833, 1), (key1347, -1), (key1675, -1)]

theorem rawRowCheck561 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form3 = rawRow561 := by decide +kernel

def row561 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck561 : row561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow561 := by decide +kernel

theorem rowEval561 (x : Key → ℝ) : Integer.Sparse.eval row561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck561, Integer.Sparse.eval_collectBalanced, rawRowCheck561]

def rawRow562 : Integer.Sparse Key := [(key1449, -2), (key1446, 1), (key1428, 1), (key1468, 2), (key1446, -1), (key1395, -1), (key1468, -1), (key1459, -1), (key1449, 1), (key1399, 1), (key1598, 2), (key1595, -1), (key1577, -1), (key1800, -2), (key1595, 1), (key1300, 1), (key1800, 1), (key1792, 1), (key1598, -1), (key1304, -1), (key1669, -2), (key1635, 1), (key1550, 1), (key1827, 2), (key1635, -1), (key1320, -1), (key1827, -1), (key1776, -1), (key1669, 1), (key1341, 1), (key1675, 1), (key1661, 1), (key1643, -1), (key1561, -1), (key1833, -1), (key1819, -1), (key1643, 1), (key1331, 1), (key1833, 1), (key1782, 1), (key1675, -1), (key1347, -1)]

theorem rawRowCheck562 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form3 = rawRow562 := by decide +kernel

def row562 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck562 : row562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow562 := by decide +kernel

theorem rowEval562 (x : Key → ℝ) : Integer.Sparse.eval row562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form3) x := by
  rw [rowCheck562, Integer.Sparse.eval_collectBalanced, rawRowCheck562]

def rawRow563 : Integer.Sparse Key := [(key1459, -2), (key1468, 1), (key1468, 1), (key1399, 2), (key1449, -1), (key1449, -1), (key1395, -1), (key1395, -1), (key1428, 1), (key1428, 1), (key1792, 2), (key1800, -1), (key1800, -1), (key1304, -2), (key1598, 1), (key1598, 1), (key1300, 1), (key1300, 1), (key1577, -1), (key1577, -1), (key1776, -2), (key1827, 1), (key1827, 1), (key1341, 2), (key1669, -1), (key1669, -1), (key1320, -1), (key1320, -1), (key1550, 1), (key1550, 1), (key1782, 1), (key1782, 1), (key1819, -1), (key1819, -1), (key1347, -1), (key1347, -1), (key1661, 1), (key1661, 1), (key1331, 1), (key1331, 1), (key1561, -1), (key1561, -1)]

theorem rawRowCheck563 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form3 = rawRow563 := by decide +kernel

def row563 : Integer.Sparse Key := [(key1300, 2), (key1304, -2), (key1320, -2), (key1331, 2), (key1341, 2), (key1347, -2), (key1395, -2), (key1399, 2), (key1428, 2), (key1449, -2), (key1459, -2), (key1468, 2), (key1550, 2), (key1561, -2), (key1577, -2), (key1598, 2), (key1661, 2), (key1669, -2), (key1776, -2), (key1782, 2), (key1792, 2), (key1800, -2), (key1819, -2), (key1827, 2)]

theorem rowCheck563 : row563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow563 := by decide +kernel

theorem rowEval563 (x : Key → ℝ) : Integer.Sparse.eval row563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck563, Integer.Sparse.eval_collectBalanced, rawRowCheck563]

def rawRow564 : Integer.Sparse Key := [(key1468, -2), (key1459, 1), (key1468, 1), (key1449, 2), (key1399, -1), (key1449, -1), (key1428, -1), (key1446, -1), (key1395, 1), (key1446, 1), (key1800, 2), (key1792, -1), (key1800, -1), (key1598, -2), (key1304, 1), (key1598, 1), (key1577, 1), (key1595, 1), (key1300, -1), (key1595, -1), (key1827, -2), (key1776, 1), (key1827, 1), (key1669, 2), (key1341, -1), (key1669, -1), (key1550, -1), (key1635, -1), (key1320, 1), (key1635, 1), (key1819, 1), (key1833, 1), (key1782, -1), (key1833, -1), (key1661, -1), (key1675, -1), (key1347, 1), (key1675, 1), (key1561, 1), (key1643, 1), (key1331, -1), (key1643, -1)]

theorem rawRowCheck564 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form3 = rawRow564 := by decide +kernel

def row564 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck564 : row564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow564 := by decide +kernel

theorem rowEval564 (x : Key → ℝ) : Integer.Sparse.eval row564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck564, Integer.Sparse.eval_collectBalanced, rawRowCheck564]

def rawRow565 : Integer.Sparse Key := [(key1468, -2), (key1468, 1), (key1459, 1), (key1449, 2), (key1449, -1), (key1399, -1), (key1446, -1), (key1428, -1), (key1446, 1), (key1395, 1), (key1800, 2), (key1800, -1), (key1792, -1), (key1598, -2), (key1598, 1), (key1304, 1), (key1595, 1), (key1577, 1), (key1595, -1), (key1300, -1), (key1827, -2), (key1827, 1), (key1776, 1), (key1669, 2), (key1669, -1), (key1341, -1), (key1635, -1), (key1550, -1), (key1635, 1), (key1320, 1), (key1833, 1), (key1819, 1), (key1833, -1), (key1782, -1), (key1675, -1), (key1661, -1), (key1675, 1), (key1347, 1), (key1643, 1), (key1561, 1), (key1643, -1), (key1331, -1)]

theorem rawRowCheck565 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form3 = rawRow565 := by decide +kernel

def row565 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck565 : row565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow565 := by decide +kernel

theorem rowEval565 (x : Key → ℝ) : Integer.Sparse.eval row565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form3) x := by
  rw [rowCheck565, Integer.Sparse.eval_collectBalanced, rawRowCheck565]

def rawRow566 : Integer.Sparse Key := [(key1550, -2), (key1558, 1), (key1561, 1), (key1577, 2), (key1626, -1), (key1661, -1), (key1595, -1), (key1598, -1), (key1635, 1), (key1669, 1), (key1320, 2), (key1328, -1), (key1331, -1), (key1428, -2), (key1626, 1), (key1819, 1), (key1446, 1), (key1449, 1), (key1635, -1), (key1827, -1), (key1300, -2), (key1328, 1), (key1347, 1), (key1395, 2), (key1558, -1), (key1782, -1), (key1446, -1), (key1468, -1), (key1595, 1), (key1800, 1), (key1300, 1), (key1304, 1), (key1320, -1), (key1341, -1), (key1395, -1), (key1399, -1), (key1550, 1), (key1776, 1), (key1428, 1), (key1459, 1), (key1577, -1), (key1792, -1)]

theorem rawRowCheck566 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form3 = rawRow566 := by decide +kernel

def row566 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck566 : row566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow566 := by decide +kernel

theorem rowEval566 (x : Key → ℝ) : Integer.Sparse.eval row566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck566, Integer.Sparse.eval_collectBalanced, rawRowCheck566]

def rawRow567 : Integer.Sparse Key := [(key1550, -2), (key1561, 1), (key1558, 1), (key1577, 2), (key1661, -1), (key1626, -1), (key1598, -1), (key1595, -1), (key1669, 1), (key1635, 1), (key1320, 2), (key1331, -1), (key1328, -1), (key1428, -2), (key1819, 1), (key1626, 1), (key1449, 1), (key1446, 1), (key1827, -1), (key1635, -1), (key1300, -2), (key1347, 1), (key1328, 1), (key1395, 2), (key1782, -1), (key1558, -1), (key1468, -1), (key1446, -1), (key1800, 1), (key1595, 1), (key1304, 1), (key1300, 1), (key1341, -1), (key1320, -1), (key1399, -1), (key1395, -1), (key1776, 1), (key1550, 1), (key1459, 1), (key1428, 1), (key1792, -1), (key1577, -1)]

theorem rawRowCheck567 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form3 = rawRow567 := by decide +kernel

def row567 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck567 : row567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow567 := by decide +kernel

theorem rowEval567 (x : Key → ℝ) : Integer.Sparse.eval row567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck567, Integer.Sparse.eval_collectBalanced, rawRowCheck567]

def rawRow568 : Integer.Sparse Key := [(key1561, -2), (key1550, 1), (key1558, 1), (key1661, 2), (key1577, -1), (key1626, -1), (key1669, -1), (key1675, -1), (key1598, 1), (key1643, 1), (key1331, 2), (key1320, -1), (key1328, -1), (key1819, -2), (key1428, 1), (key1626, 1), (key1827, 1), (key1833, 1), (key1449, -1), (key1643, -1), (key1347, -2), (key1300, 1), (key1328, 1), (key1782, 2), (key1395, -1), (key1558, -1), (key1800, -1), (key1833, -1), (key1468, 1), (key1675, 1), (key1341, 1), (key1347, 1), (key1304, -1), (key1331, -1), (key1776, -1), (key1782, -1), (key1399, 1), (key1561, 1), (key1792, 1), (key1819, 1), (key1459, -1), (key1661, -1)]

theorem rawRowCheck568 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form3 = rawRow568 := by decide +kernel

def row568 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck568 : row568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow568 := by decide +kernel

theorem rowEval568 (x : Key → ℝ) : Integer.Sparse.eval row568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck568, Integer.Sparse.eval_collectBalanced, rawRowCheck568]

def rawRow569 : Integer.Sparse Key := [(key1561, -2), (key1558, 1), (key1550, 1), (key1661, 2), (key1626, -1), (key1577, -1), (key1675, -1), (key1669, -1), (key1643, 1), (key1598, 1), (key1331, 2), (key1328, -1), (key1320, -1), (key1819, -2), (key1626, 1), (key1428, 1), (key1833, 1), (key1827, 1), (key1643, -1), (key1449, -1), (key1347, -2), (key1328, 1), (key1300, 1), (key1782, 2), (key1558, -1), (key1395, -1), (key1833, -1), (key1800, -1), (key1675, 1), (key1468, 1), (key1347, 1), (key1341, 1), (key1331, -1), (key1304, -1), (key1782, -1), (key1776, -1), (key1561, 1), (key1399, 1), (key1819, 1), (key1792, 1), (key1661, -1), (key1459, -1)]

theorem rawRowCheck569 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form3 = rawRow569 := by decide +kernel

def row569 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck569 : row569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow569 := by decide +kernel

theorem rowEval569 (x : Key → ℝ) : Integer.Sparse.eval row569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form3) x := by
  rw [rowCheck569, Integer.Sparse.eval_collectBalanced, rawRowCheck569]

def rawRow570 : Integer.Sparse Key := [(key1577, -2), (key1595, 1), (key1598, 1), (key1550, 2), (key1635, -1), (key1669, -1), (key1558, -1), (key1561, -1), (key1626, 1), (key1661, 1), (key1428, 2), (key1446, -1), (key1449, -1), (key1320, -2), (key1635, 1), (key1827, 1), (key1328, 1), (key1331, 1), (key1626, -1), (key1819, -1), (key1395, -2), (key1446, 1), (key1468, 1), (key1300, 2), (key1595, -1), (key1800, -1), (key1328, -1), (key1347, -1), (key1558, 1), (key1782, 1), (key1395, 1), (key1399, 1), (key1428, -1), (key1459, -1), (key1300, -1), (key1304, -1), (key1577, 1), (key1792, 1), (key1320, 1), (key1341, 1), (key1550, -1), (key1776, -1)]

theorem rawRowCheck570 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form3 = rawRow570 := by decide +kernel

def row570 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck570 : row570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow570 := by decide +kernel

theorem rowEval570 (x : Key → ℝ) : Integer.Sparse.eval row570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck570, Integer.Sparse.eval_collectBalanced, rawRowCheck570]

def rawRow571 : Integer.Sparse Key := [(key1577, -2), (key1598, 1), (key1595, 1), (key1550, 2), (key1669, -1), (key1635, -1), (key1561, -1), (key1558, -1), (key1661, 1), (key1626, 1), (key1428, 2), (key1449, -1), (key1446, -1), (key1320, -2), (key1827, 1), (key1635, 1), (key1331, 1), (key1328, 1), (key1819, -1), (key1626, -1), (key1395, -2), (key1468, 1), (key1446, 1), (key1300, 2), (key1800, -1), (key1595, -1), (key1347, -1), (key1328, -1), (key1782, 1), (key1558, 1), (key1399, 1), (key1395, 1), (key1459, -1), (key1428, -1), (key1304, -1), (key1300, -1), (key1792, 1), (key1577, 1), (key1341, 1), (key1320, 1), (key1776, -1), (key1550, -1)]

theorem rawRowCheck571 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form3 = rawRow571 := by decide +kernel

def row571 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck571 : row571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow571 := by decide +kernel

theorem rowEval571 (x : Key → ℝ) : Integer.Sparse.eval row571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck571, Integer.Sparse.eval_collectBalanced, rawRowCheck571]

def rawRow572 : Integer.Sparse Key := [(key1598, -2), (key1577, 1), (key1595, 1), (key1669, 2), (key1550, -1), (key1635, -1), (key1661, -1), (key1675, -1), (key1561, 1), (key1643, 1), (key1449, 2), (key1428, -1), (key1446, -1), (key1827, -2), (key1320, 1), (key1635, 1), (key1819, 1), (key1833, 1), (key1331, -1), (key1643, -1), (key1468, -2), (key1395, 1), (key1446, 1), (key1800, 2), (key1300, -1), (key1595, -1), (key1782, -1), (key1833, -1), (key1347, 1), (key1675, 1), (key1459, 1), (key1468, 1), (key1399, -1), (key1449, -1), (key1792, -1), (key1800, -1), (key1304, 1), (key1598, 1), (key1776, 1), (key1827, 1), (key1341, -1), (key1669, -1)]

theorem rawRowCheck572 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form3 = rawRow572 := by decide +kernel

def row572 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck572 : row572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow572 := by decide +kernel

theorem rowEval572 (x : Key → ℝ) : Integer.Sparse.eval row572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck572, Integer.Sparse.eval_collectBalanced, rawRowCheck572]

def rawRow573 : Integer.Sparse Key := [(key1598, -2), (key1595, 1), (key1577, 1), (key1669, 2), (key1635, -1), (key1550, -1), (key1675, -1), (key1661, -1), (key1643, 1), (key1561, 1), (key1449, 2), (key1446, -1), (key1428, -1), (key1827, -2), (key1635, 1), (key1320, 1), (key1833, 1), (key1819, 1), (key1643, -1), (key1331, -1), (key1468, -2), (key1446, 1), (key1395, 1), (key1800, 2), (key1595, -1), (key1300, -1), (key1833, -1), (key1782, -1), (key1675, 1), (key1347, 1), (key1468, 1), (key1459, 1), (key1449, -1), (key1399, -1), (key1800, -1), (key1792, -1), (key1598, 1), (key1304, 1), (key1827, 1), (key1776, 1), (key1669, -1), (key1341, -1)]

theorem rawRowCheck573 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form3 = rawRow573 := by decide +kernel

def row573 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck573 : row573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow573 := by decide +kernel

theorem rowEval573 (x : Key → ℝ) : Integer.Sparse.eval row573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form3) x := by
  rw [rowCheck573, Integer.Sparse.eval_collectBalanced, rawRowCheck573]

def rawRow574 : Integer.Sparse Key := [(key1661, -2), (key1669, 1), (key1675, 1), (key1561, 2), (key1598, -1), (key1643, -1), (key1550, -1), (key1558, -1), (key1577, 1), (key1626, 1), (key1819, 2), (key1827, -1), (key1833, -1), (key1331, -2), (key1449, 1), (key1643, 1), (key1320, 1), (key1328, 1), (key1428, -1), (key1626, -1), (key1782, -2), (key1800, 1), (key1833, 1), (key1347, 2), (key1468, -1), (key1675, -1), (key1300, -1), (key1328, -1), (key1395, 1), (key1558, 1), (key1776, 1), (key1782, 1), (key1792, -1), (key1819, -1), (key1341, -1), (key1347, -1), (key1459, 1), (key1661, 1), (key1304, 1), (key1331, 1), (key1399, -1), (key1561, -1)]

theorem rawRowCheck574 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form3 = rawRow574 := by decide +kernel

def row574 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck574 : row574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow574 := by decide +kernel

theorem rowEval574 (x : Key → ℝ) : Integer.Sparse.eval row574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck574, Integer.Sparse.eval_collectBalanced, rawRowCheck574]

def rawRow575 : Integer.Sparse Key := [(key1661, -2), (key1675, 1), (key1669, 1), (key1561, 2), (key1643, -1), (key1598, -1), (key1558, -1), (key1550, -1), (key1626, 1), (key1577, 1), (key1819, 2), (key1833, -1), (key1827, -1), (key1331, -2), (key1643, 1), (key1449, 1), (key1328, 1), (key1320, 1), (key1626, -1), (key1428, -1), (key1782, -2), (key1833, 1), (key1800, 1), (key1347, 2), (key1675, -1), (key1468, -1), (key1328, -1), (key1300, -1), (key1558, 1), (key1395, 1), (key1782, 1), (key1776, 1), (key1819, -1), (key1792, -1), (key1347, -1), (key1341, -1), (key1661, 1), (key1459, 1), (key1331, 1), (key1304, 1), (key1561, -1), (key1399, -1)]

theorem rawRowCheck575 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form3 = rawRow575 := by decide +kernel

def row575 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck575 : row575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow575 := by decide +kernel

theorem rowEval575 (x : Key → ℝ) : Integer.Sparse.eval row575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form3) x := by
  rw [rowCheck575, Integer.Sparse.eval_collectBalanced, rawRowCheck575]

end MUB6.Certificate.GramRows

end OAI
