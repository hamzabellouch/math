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

def rawRow576 : Integer.Sparse Key := [(key1669, -2), (key1661, 1), (key1675, 1), (key1598, 2), (key1561, -1), (key1643, -1), (key1577, -1), (key1595, -1), (key1550, 1), (key1635, 1), (key1827, 2), (key1819, -1), (key1833, -1), (key1449, -2), (key1331, 1), (key1643, 1), (key1428, 1), (key1446, 1), (key1320, -1), (key1635, -1), (key1800, -2), (key1782, 1), (key1833, 1), (key1468, 2), (key1347, -1), (key1675, -1), (key1395, -1), (key1446, -1), (key1300, 1), (key1595, 1), (key1792, 1), (key1800, 1), (key1776, -1), (key1827, -1), (key1459, -1), (key1468, -1), (key1341, 1), (key1669, 1), (key1399, 1), (key1449, 1), (key1304, -1), (key1598, -1)]

theorem rawRowCheck576 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form3 = rawRow576 := by decide +kernel

def row576 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck576 : row576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow576 := by decide +kernel

theorem rowEval576 (x : Key → ℝ) : Integer.Sparse.eval row576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck576, Integer.Sparse.eval_collectBalanced, rawRowCheck576]

def rawRow577 : Integer.Sparse Key := [(key1669, -2), (key1675, 1), (key1661, 1), (key1598, 2), (key1643, -1), (key1561, -1), (key1595, -1), (key1577, -1), (key1635, 1), (key1550, 1), (key1827, 2), (key1833, -1), (key1819, -1), (key1449, -2), (key1643, 1), (key1331, 1), (key1446, 1), (key1428, 1), (key1635, -1), (key1320, -1), (key1800, -2), (key1833, 1), (key1782, 1), (key1468, 2), (key1675, -1), (key1347, -1), (key1446, -1), (key1395, -1), (key1595, 1), (key1300, 1), (key1800, 1), (key1792, 1), (key1827, -1), (key1776, -1), (key1468, -1), (key1459, -1), (key1669, 1), (key1341, 1), (key1449, 1), (key1399, 1), (key1598, -1), (key1304, -1)]

theorem rawRowCheck577 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form3 = rawRow577 := by decide +kernel

def row577 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck577 : row577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow577 := by decide +kernel

theorem rowEval577 (x : Key → ℝ) : Integer.Sparse.eval row577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form3) x := by
  rw [rowCheck577, Integer.Sparse.eval_collectBalanced, rawRowCheck577]

def rawRow578 : Integer.Sparse Key := [(key1776, -2), (key1782, 1), (key1782, 1), (key1792, 2), (key1819, -1), (key1819, -1), (key1800, -1), (key1800, -1), (key1827, 1), (key1827, 1), (key1341, 2), (key1347, -1), (key1347, -1), (key1459, -2), (key1661, 1), (key1661, 1), (key1468, 1), (key1468, 1), (key1669, -1), (key1669, -1), (key1304, -2), (key1331, 1), (key1331, 1), (key1399, 2), (key1561, -1), (key1561, -1), (key1449, -1), (key1449, -1), (key1598, 1), (key1598, 1), (key1300, 1), (key1300, 1), (key1320, -1), (key1320, -1), (key1395, -1), (key1395, -1), (key1550, 1), (key1550, 1), (key1428, 1), (key1428, 1), (key1577, -1), (key1577, -1)]

theorem rawRowCheck578 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form3 = rawRow578 := by decide +kernel

def row578 : Integer.Sparse Key := [(key1300, 2), (key1304, -2), (key1320, -2), (key1331, 2), (key1341, 2), (key1347, -2), (key1395, -2), (key1399, 2), (key1428, 2), (key1449, -2), (key1459, -2), (key1468, 2), (key1550, 2), (key1561, -2), (key1577, -2), (key1598, 2), (key1661, 2), (key1669, -2), (key1776, -2), (key1782, 2), (key1792, 2), (key1800, -2), (key1819, -2), (key1827, 2)]

theorem rowCheck578 : row578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow578 := by decide +kernel

theorem rowEval578 (x : Key → ℝ) : Integer.Sparse.eval row578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck578, Integer.Sparse.eval_collectBalanced, rawRowCheck578]

def rawRow579 : Integer.Sparse Key := [(key1782, -2), (key1776, 1), (key1782, 1), (key1819, 2), (key1792, -1), (key1819, -1), (key1827, -1), (key1833, -1), (key1800, 1), (key1833, 1), (key1347, 2), (key1341, -1), (key1347, -1), (key1661, -2), (key1459, 1), (key1661, 1), (key1669, 1), (key1675, 1), (key1468, -1), (key1675, -1), (key1331, -2), (key1304, 1), (key1331, 1), (key1561, 2), (key1399, -1), (key1561, -1), (key1598, -1), (key1643, -1), (key1449, 1), (key1643, 1), (key1320, 1), (key1328, 1), (key1300, -1), (key1328, -1), (key1550, -1), (key1558, -1), (key1395, 1), (key1558, 1), (key1577, 1), (key1626, 1), (key1428, -1), (key1626, -1)]

theorem rawRowCheck579 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form3 = rawRow579 := by decide +kernel

def row579 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck579 : row579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow579 := by decide +kernel

theorem rowEval579 (x : Key → ℝ) : Integer.Sparse.eval row579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck579, Integer.Sparse.eval_collectBalanced, rawRowCheck579]

def rawRow580 : Integer.Sparse Key := [(key1782, -2), (key1782, 1), (key1776, 1), (key1819, 2), (key1819, -1), (key1792, -1), (key1833, -1), (key1827, -1), (key1833, 1), (key1800, 1), (key1347, 2), (key1347, -1), (key1341, -1), (key1661, -2), (key1661, 1), (key1459, 1), (key1675, 1), (key1669, 1), (key1675, -1), (key1468, -1), (key1331, -2), (key1331, 1), (key1304, 1), (key1561, 2), (key1561, -1), (key1399, -1), (key1643, -1), (key1598, -1), (key1643, 1), (key1449, 1), (key1328, 1), (key1320, 1), (key1328, -1), (key1300, -1), (key1558, -1), (key1550, -1), (key1558, 1), (key1395, 1), (key1626, 1), (key1577, 1), (key1626, -1), (key1428, -1)]

theorem rawRowCheck580 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form3 = rawRow580 := by decide +kernel

def row580 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck580 : row580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow580 := by decide +kernel

theorem rowEval580 (x : Key → ℝ) : Integer.Sparse.eval row580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form3) x := by
  rw [rowCheck580, Integer.Sparse.eval_collectBalanced, rawRowCheck580]

def rawRow581 : Integer.Sparse Key := [(key1792, -2), (key1800, 1), (key1800, 1), (key1776, 2), (key1827, -1), (key1827, -1), (key1782, -1), (key1782, -1), (key1819, 1), (key1819, 1), (key1459, 2), (key1468, -1), (key1468, -1), (key1341, -2), (key1669, 1), (key1669, 1), (key1347, 1), (key1347, 1), (key1661, -1), (key1661, -1), (key1399, -2), (key1449, 1), (key1449, 1), (key1304, 2), (key1598, -1), (key1598, -1), (key1331, -1), (key1331, -1), (key1561, 1), (key1561, 1), (key1395, 1), (key1395, 1), (key1428, -1), (key1428, -1), (key1300, -1), (key1300, -1), (key1577, 1), (key1577, 1), (key1320, 1), (key1320, 1), (key1550, -1), (key1550, -1)]

theorem rawRowCheck581 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form3 = rawRow581 := by decide +kernel

def row581 : Integer.Sparse Key := [(key1300, -2), (key1304, 2), (key1320, 2), (key1331, -2), (key1341, -2), (key1347, 2), (key1395, 2), (key1399, -2), (key1428, -2), (key1449, 2), (key1459, 2), (key1468, -2), (key1550, -2), (key1561, 2), (key1577, 2), (key1598, -2), (key1661, -2), (key1669, 2), (key1776, 2), (key1782, -2), (key1792, -2), (key1800, 2), (key1819, 2), (key1827, -2)]

theorem rowCheck581 : row581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow581 := by decide +kernel

theorem rowEval581 (x : Key → ℝ) : Integer.Sparse.eval row581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck581, Integer.Sparse.eval_collectBalanced, rawRowCheck581]

def rawRow582 : Integer.Sparse Key := [(key1800, -2), (key1792, 1), (key1800, 1), (key1827, 2), (key1776, -1), (key1827, -1), (key1819, -1), (key1833, -1), (key1782, 1), (key1833, 1), (key1468, 2), (key1459, -1), (key1468, -1), (key1669, -2), (key1341, 1), (key1669, 1), (key1661, 1), (key1675, 1), (key1347, -1), (key1675, -1), (key1449, -2), (key1399, 1), (key1449, 1), (key1598, 2), (key1304, -1), (key1598, -1), (key1561, -1), (key1643, -1), (key1331, 1), (key1643, 1), (key1428, 1), (key1446, 1), (key1395, -1), (key1446, -1), (key1577, -1), (key1595, -1), (key1300, 1), (key1595, 1), (key1550, 1), (key1635, 1), (key1320, -1), (key1635, -1)]

theorem rawRowCheck582 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form3 = rawRow582 := by decide +kernel

def row582 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck582 : row582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow582 := by decide +kernel

theorem rowEval582 (x : Key → ℝ) : Integer.Sparse.eval row582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck582, Integer.Sparse.eval_collectBalanced, rawRowCheck582]

def rawRow583 : Integer.Sparse Key := [(key1800, -2), (key1800, 1), (key1792, 1), (key1827, 2), (key1827, -1), (key1776, -1), (key1833, -1), (key1819, -1), (key1833, 1), (key1782, 1), (key1468, 2), (key1468, -1), (key1459, -1), (key1669, -2), (key1669, 1), (key1341, 1), (key1675, 1), (key1661, 1), (key1675, -1), (key1347, -1), (key1449, -2), (key1449, 1), (key1399, 1), (key1598, 2), (key1598, -1), (key1304, -1), (key1643, -1), (key1561, -1), (key1643, 1), (key1331, 1), (key1446, 1), (key1428, 1), (key1446, -1), (key1395, -1), (key1595, -1), (key1577, -1), (key1595, 1), (key1300, 1), (key1635, 1), (key1550, 1), (key1635, -1), (key1320, -1)]

theorem rawRowCheck583 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form3 = rawRow583 := by decide +kernel

def row583 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck583 : row583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow583 := by decide +kernel

theorem rowEval583 (x : Key → ℝ) : Integer.Sparse.eval row583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form3) x := by
  rw [rowCheck583, Integer.Sparse.eval_collectBalanced, rawRowCheck583]

def rawRow584 : Integer.Sparse Key := [(key1819, -2), (key1827, 1), (key1833, 1), (key1782, 2), (key1800, -1), (key1833, -1), (key1776, -1), (key1782, -1), (key1792, 1), (key1819, 1), (key1661, 2), (key1669, -1), (key1675, -1), (key1347, -2), (key1468, 1), (key1675, 1), (key1341, 1), (key1347, 1), (key1459, -1), (key1661, -1), (key1561, -2), (key1598, 1), (key1643, 1), (key1331, 2), (key1449, -1), (key1643, -1), (key1304, -1), (key1331, -1), (key1399, 1), (key1561, 1), (key1550, 1), (key1558, 1), (key1577, -1), (key1626, -1), (key1320, -1), (key1328, -1), (key1428, 1), (key1626, 1), (key1300, 1), (key1328, 1), (key1395, -1), (key1558, -1)]

theorem rawRowCheck584 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form3 = rawRow584 := by decide +kernel

def row584 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck584 : row584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow584 := by decide +kernel

theorem rowEval584 (x : Key → ℝ) : Integer.Sparse.eval row584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck584, Integer.Sparse.eval_collectBalanced, rawRowCheck584]

def rawRow585 : Integer.Sparse Key := [(key1819, -2), (key1833, 1), (key1827, 1), (key1782, 2), (key1833, -1), (key1800, -1), (key1782, -1), (key1776, -1), (key1819, 1), (key1792, 1), (key1661, 2), (key1675, -1), (key1669, -1), (key1347, -2), (key1675, 1), (key1468, 1), (key1347, 1), (key1341, 1), (key1661, -1), (key1459, -1), (key1561, -2), (key1643, 1), (key1598, 1), (key1331, 2), (key1643, -1), (key1449, -1), (key1331, -1), (key1304, -1), (key1561, 1), (key1399, 1), (key1558, 1), (key1550, 1), (key1626, -1), (key1577, -1), (key1328, -1), (key1320, -1), (key1626, 1), (key1428, 1), (key1328, 1), (key1300, 1), (key1558, -1), (key1395, -1)]

theorem rawRowCheck585 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form3 = rawRow585 := by decide +kernel

def row585 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

theorem rowCheck585 : row585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow585 := by decide +kernel

theorem rowEval585 (x : Key → ℝ) : Integer.Sparse.eval row585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form3) x := by
  rw [rowCheck585, Integer.Sparse.eval_collectBalanced, rawRowCheck585]

def rawRow586 : Integer.Sparse Key := [(key1827, -2), (key1819, 1), (key1833, 1), (key1800, 2), (key1782, -1), (key1833, -1), (key1792, -1), (key1800, -1), (key1776, 1), (key1827, 1), (key1669, 2), (key1661, -1), (key1675, -1), (key1468, -2), (key1347, 1), (key1675, 1), (key1459, 1), (key1468, 1), (key1341, -1), (key1669, -1), (key1598, -2), (key1561, 1), (key1643, 1), (key1449, 2), (key1331, -1), (key1643, -1), (key1399, -1), (key1449, -1), (key1304, 1), (key1598, 1), (key1577, 1), (key1595, 1), (key1550, -1), (key1635, -1), (key1428, -1), (key1446, -1), (key1320, 1), (key1635, 1), (key1395, 1), (key1446, 1), (key1300, -1), (key1595, -1)]

theorem rawRowCheck586 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form3 = rawRow586 := by decide +kernel

def row586 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck586 : row586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow586 := by decide +kernel

theorem rowEval586 (x : Key → ℝ) : Integer.Sparse.eval row586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck586, Integer.Sparse.eval_collectBalanced, rawRowCheck586]

def rawRow587 : Integer.Sparse Key := [(key1827, -2), (key1833, 1), (key1819, 1), (key1800, 2), (key1833, -1), (key1782, -1), (key1800, -1), (key1792, -1), (key1827, 1), (key1776, 1), (key1669, 2), (key1675, -1), (key1661, -1), (key1468, -2), (key1675, 1), (key1347, 1), (key1468, 1), (key1459, 1), (key1669, -1), (key1341, -1), (key1598, -2), (key1643, 1), (key1561, 1), (key1449, 2), (key1643, -1), (key1331, -1), (key1449, -1), (key1399, -1), (key1598, 1), (key1304, 1), (key1595, 1), (key1577, 1), (key1635, -1), (key1550, -1), (key1446, -1), (key1428, -1), (key1635, 1), (key1320, 1), (key1446, 1), (key1395, 1), (key1595, -1), (key1300, -1)]

theorem rawRowCheck587 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form3 = rawRow587 := by decide +kernel

def row587 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

theorem rowCheck587 : row587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow587 := by decide +kernel

theorem rowEval587 (x : Key → ℝ) : Integer.Sparse.eval row587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form3) x := by
  rw [rowCheck587, Integer.Sparse.eval_collectBalanced, rawRowCheck587]

def rawRow588 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2611, 2), (key2624, 1), (key2627, 1), (key2627, -1), (key2636, -1), (key2645, -2), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2666, -2), (key2698, -1), (key2701, -1), (key2701, 1), (key2722, 1), (key2734, 2), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, -1), (key2781, 1), (key2790, 1), (key2801, 1), (key2804, 1), (key2804, -1), (key2825, -1), (key2892, -1), (key2895, -1), (key2892, 1), (key2902, 1), (key2935, 2), (key2935, -1), (key2941, -1), (key2947, -2), (key2947, 1), (key2958, 1), (key2971, 1), (key2974, 1), (key2971, -1), (key2981, -1)]

theorem rawRowCheck588 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form4 = rawRow588 := by decide +kernel

def row588 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck588 : row588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow588 := by decide +kernel

theorem rowEval588 (x : Key → ℝ) : Integer.Sparse.eval row588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form4) x := by
  rw [rowCheck588, Integer.Sparse.eval_collectBalanced, rawRowCheck588]

def rawRow589 : Integer.Sparse Key := [(key2611, -1), (key2608, -1), (key2611, 2), (key2627, 1), (key2624, 1), (key2636, -1), (key2627, -1), (key2645, -2), (key2651, 1), (key2645, 1), (key2666, 1), (key2663, 1), (key2666, -2), (key2701, -1), (key2698, -1), (key2722, 1), (key2701, 1), (key2734, 2), (key2745, -1), (key2734, -1), (key2781, -1), (key2778, -1), (key2790, 1), (key2781, 1), (key2804, 1), (key2801, 1), (key2825, -1), (key2804, -1), (key2895, -1), (key2892, -1), (key2902, 1), (key2892, 1), (key2935, 2), (key2941, -1), (key2935, -1), (key2947, -2), (key2958, 1), (key2947, 1), (key2974, 1), (key2971, 1), (key2981, -1), (key2971, -1)]

theorem rawRowCheck589 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form4 = rawRow589 := by decide +kernel

def row589 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck589 : row589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow589 := by decide +kernel

theorem rowEval589 (x : Key → ℝ) : Integer.Sparse.eval row589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck589, Integer.Sparse.eval_collectBalanced, rawRowCheck589]

def rawRow590 : Integer.Sparse Key := [(key2611, -1), (key2611, -1), (key2608, 2), (key2636, 1), (key2636, 1), (key2624, -1), (key2624, -1), (key2651, -2), (key2645, 1), (key2645, 1), (key2666, 1), (key2666, 1), (key2663, -2), (key2722, -1), (key2722, -1), (key2698, 1), (key2698, 1), (key2745, 2), (key2734, -1), (key2734, -1), (key2790, -1), (key2790, -1), (key2778, 1), (key2778, 1), (key2825, 1), (key2825, 1), (key2801, -1), (key2801, -1), (key2902, -1), (key2902, -1), (key2895, 1), (key2895, 1), (key2941, 2), (key2935, -1), (key2935, -1), (key2958, -2), (key2947, 1), (key2947, 1), (key2981, 1), (key2981, 1), (key2974, -1), (key2974, -1)]

theorem rawRowCheck590 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form4 = rawRow590 := by decide +kernel

def row590 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2663, -2), (key2666, 2), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2778, 2), (key2790, -2), (key2801, -2), (key2825, 2), (key2895, 2), (key2902, -2), (key2935, -2), (key2941, 2), (key2947, 2), (key2958, -2), (key2974, -2), (key2981, 2)]

theorem rowCheck590 : row590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow590 := by decide +kernel

theorem rowEval590 (x : Key → ℝ) : Integer.Sparse.eval row590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck590, Integer.Sparse.eval_collectBalanced, rawRowCheck590]

def rawRow591 : Integer.Sparse Key := [(key2624, -1), (key2627, -1), (key2636, 2), (key2608, 1), (key2611, 1), (key2645, -1), (key2651, -1), (key2611, -2), (key2627, 1), (key2636, 1), (key2698, 1), (key2701, 1), (key2734, -2), (key2663, -1), (key2666, -1), (key2734, 1), (key2745, 1), (key2666, 2), (key2701, -1), (key2722, -1), (key2801, -1), (key2804, -1), (key2892, 1), (key2895, 1), (key2778, 1), (key2781, 1), (key2892, -1), (key2902, -1), (key2781, -1), (key2790, -1), (key2804, 1), (key2825, 1), (key2947, 2), (key2971, -1), (key2974, -1), (key2935, -2), (key2971, 1), (key2981, 1), (key2935, 1), (key2941, 1), (key2947, -1), (key2958, -1)]

theorem rawRowCheck591 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form4 = rawRow591 := by decide +kernel

def row591 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck591 : row591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow591 := by decide +kernel

theorem rowEval591 (x : Key → ℝ) : Integer.Sparse.eval row591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form4) x := by
  rw [rowCheck591, Integer.Sparse.eval_collectBalanced, rawRowCheck591]

def rawRow592 : Integer.Sparse Key := [(key2627, -1), (key2624, -1), (key2636, 2), (key2611, 1), (key2608, 1), (key2651, -1), (key2645, -1), (key2611, -2), (key2636, 1), (key2627, 1), (key2701, 1), (key2698, 1), (key2734, -2), (key2666, -1), (key2663, -1), (key2745, 1), (key2734, 1), (key2666, 2), (key2722, -1), (key2701, -1), (key2804, -1), (key2801, -1), (key2895, 1), (key2892, 1), (key2781, 1), (key2778, 1), (key2902, -1), (key2892, -1), (key2790, -1), (key2781, -1), (key2825, 1), (key2804, 1), (key2947, 2), (key2974, -1), (key2971, -1), (key2935, -2), (key2981, 1), (key2971, 1), (key2941, 1), (key2935, 1), (key2958, -1), (key2947, -1)]

theorem rawRowCheck592 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form4 = rawRow592 := by decide +kernel

def row592 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck592 : row592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow592 := by decide +kernel

theorem rowEval592 (x : Key → ℝ) : Integer.Sparse.eval row592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck592, Integer.Sparse.eval_collectBalanced, rawRowCheck592]

def rawRow593 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2624, 2), (key2645, 1), (key2651, 1), (key2608, -1), (key2624, -1), (key2636, -2), (key2611, 1), (key2627, 1), (key2701, 1), (key2734, 1), (key2698, -2), (key2722, -1), (key2745, -1), (key2663, 1), (key2698, 1), (key2722, 2), (key2666, -1), (key2701, -1), (key2856, -1), (key2895, -1), (key2801, 1), (key2851, 1), (key2866, 1), (key2902, 1), (key2778, -1), (key2851, -1), (key2825, -1), (key2866, -1), (key2790, 1), (key2856, 1), (key2974, 2), (key2947, -1), (key2971, -1), (key2981, -2), (key2935, 1), (key2971, 1), (key2958, 1), (key2981, 1), (key2941, -1), (key2974, -1)]

theorem rawRowCheck593 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form4 = rawRow593 := by decide +kernel

def row593 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck593 : row593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow593 := by decide +kernel

theorem rowEval593 (x : Key → ℝ) : Integer.Sparse.eval row593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck593, Integer.Sparse.eval_collectBalanced, rawRowCheck593]

def rawRow594 : Integer.Sparse Key := [(key2636, -1), (key2627, -1), (key2624, 2), (key2651, 1), (key2645, 1), (key2624, -1), (key2608, -1), (key2636, -2), (key2627, 1), (key2611, 1), (key2734, 1), (key2701, 1), (key2698, -2), (key2745, -1), (key2722, -1), (key2698, 1), (key2663, 1), (key2722, 2), (key2701, -1), (key2666, -1), (key2895, -1), (key2856, -1), (key2851, 1), (key2801, 1), (key2902, 1), (key2866, 1), (key2851, -1), (key2778, -1), (key2866, -1), (key2825, -1), (key2856, 1), (key2790, 1), (key2974, 2), (key2971, -1), (key2947, -1), (key2981, -2), (key2971, 1), (key2935, 1), (key2981, 1), (key2958, 1), (key2974, -1), (key2941, -1)]

theorem rawRowCheck594 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form4 = rawRow594 := by decide +kernel

def row594 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck594 : row594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow594 := by decide +kernel

theorem rowEval594 (x : Key → ℝ) : Integer.Sparse.eval row594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form4) x := by
  rw [rowCheck594, Integer.Sparse.eval_collectBalanced, rawRowCheck594]

def rawRow595 : Integer.Sparse Key := [(key2645, -1), (key2645, -1), (key2651, 2), (key2611, 1), (key2611, 1), (key2636, -1), (key2636, -1), (key2608, -2), (key2624, 1), (key2624, 1), (key2722, 1), (key2722, 1), (key2745, -2), (key2666, -1), (key2666, -1), (key2734, 1), (key2734, 1), (key2663, 2), (key2698, -1), (key2698, -1), (key2825, -1), (key2825, -1), (key2902, 1), (key2902, 1), (key2790, 1), (key2790, 1), (key2895, -1), (key2895, -1), (key2778, -1), (key2778, -1), (key2801, 1), (key2801, 1), (key2958, 2), (key2981, -1), (key2981, -1), (key2941, -2), (key2974, 1), (key2974, 1), (key2935, 1), (key2935, 1), (key2947, -1), (key2947, -1)]

theorem rawRowCheck595 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form4 = rawRow595 := by decide +kernel

def row595 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2722, 2), (key2734, 2), (key2745, -2), (key2778, -2), (key2790, 2), (key2801, 2), (key2825, -2), (key2895, -2), (key2902, 2), (key2935, 2), (key2941, -2), (key2947, -2), (key2958, 2), (key2974, 2), (key2981, -2)]

theorem rowCheck595 : row595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow595 := by decide +kernel

theorem rowEval595 (x : Key → ℝ) : Integer.Sparse.eval row595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck595, Integer.Sparse.eval_collectBalanced, rawRowCheck595]

def rawRow596 : Integer.Sparse Key := [(key2645, -1), (key2651, -1), (key2645, 2), (key2627, 1), (key2636, 1), (key2611, -1), (key2627, -1), (key2624, -2), (key2608, 1), (key2624, 1), (key2722, 1), (key2745, 1), (key2722, -2), (key2701, -1), (key2734, -1), (key2666, 1), (key2701, 1), (key2698, 2), (key2663, -1), (key2698, -1), (key2866, -1), (key2902, -1), (key2825, 1), (key2866, 1), (key2856, 1), (key2895, 1), (key2790, -1), (key2856, -1), (key2801, -1), (key2851, -1), (key2778, 1), (key2851, 1), (key2981, 2), (key2958, -1), (key2981, -1), (key2974, -2), (key2941, 1), (key2974, 1), (key2947, 1), (key2971, 1), (key2935, -1), (key2971, -1)]

theorem rawRowCheck596 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form4 = rawRow596 := by decide +kernel

def row596 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck596 : row596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow596 := by decide +kernel

theorem rowEval596 (x : Key → ℝ) : Integer.Sparse.eval row596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck596, Integer.Sparse.eval_collectBalanced, rawRowCheck596]

def rawRow597 : Integer.Sparse Key := [(key2651, -1), (key2645, -1), (key2645, 2), (key2636, 1), (key2627, 1), (key2627, -1), (key2611, -1), (key2624, -2), (key2624, 1), (key2608, 1), (key2745, 1), (key2722, 1), (key2722, -2), (key2734, -1), (key2701, -1), (key2701, 1), (key2666, 1), (key2698, 2), (key2698, -1), (key2663, -1), (key2902, -1), (key2866, -1), (key2866, 1), (key2825, 1), (key2895, 1), (key2856, 1), (key2856, -1), (key2790, -1), (key2851, -1), (key2801, -1), (key2851, 1), (key2778, 1), (key2981, 2), (key2981, -1), (key2958, -1), (key2974, -2), (key2974, 1), (key2941, 1), (key2971, 1), (key2947, 1), (key2971, -1), (key2935, -1)]

theorem rawRowCheck597 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form4 = rawRow597 := by decide +kernel

def row597 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck597 : row597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow597 := by decide +kernel

theorem rowEval597 (x : Key → ℝ) : Integer.Sparse.eval row597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form4) x := by
  rw [rowCheck597, Integer.Sparse.eval_collectBalanced, rawRowCheck597]

def rawRow598 : Integer.Sparse Key := [(key2663, -1), (key2666, -1), (key2666, 2), (key2698, 1), (key2701, 1), (key2701, -1), (key2734, -1), (key2722, -2), (key2722, 1), (key2745, 1), (key2608, 1), (key2611, 1), (key2611, -2), (key2801, -1), (key2804, -1), (key2804, 1), (key2825, 1), (key2947, 2), (key2947, -1), (key2958, -1), (key2624, -1), (key2627, -1), (key2627, 1), (key2636, 1), (key2698, 1), (key2701, 1), (key2701, -1), (key2722, -1), (key2971, -1), (key2974, -1), (key2971, 1), (key2981, 1), (key2645, 2), (key2645, -1), (key2651, -1), (key2734, -2), (key2734, 1), (key2745, 1), (key2892, 1), (key2895, 1), (key2892, -1), (key2902, -1)]

theorem rawRowCheck598 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form4 = rawRow598 := by decide +kernel

def row598 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck598 : row598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow598 := by decide +kernel

theorem rowEval598 (x : Key → ℝ) : Integer.Sparse.eval row598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form4) x := by
  rw [rowCheck598, Integer.Sparse.eval_collectBalanced, rawRowCheck598]

def rawRow599 : Integer.Sparse Key := [(key2666, -1), (key2663, -1), (key2666, 2), (key2701, 1), (key2698, 1), (key2734, -1), (key2701, -1), (key2722, -2), (key2745, 1), (key2722, 1), (key2611, 1), (key2608, 1), (key2611, -2), (key2804, -1), (key2801, -1), (key2825, 1), (key2804, 1), (key2947, 2), (key2958, -1), (key2947, -1), (key2627, -1), (key2624, -1), (key2636, 1), (key2627, 1), (key2701, 1), (key2698, 1), (key2722, -1), (key2701, -1), (key2974, -1), (key2971, -1), (key2981, 1), (key2971, 1), (key2645, 2), (key2651, -1), (key2645, -1), (key2734, -2), (key2745, 1), (key2734, 1), (key2895, 1), (key2892, 1), (key2902, -1), (key2892, -1)]

theorem rawRowCheck599 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form4 = rawRow599 := by decide +kernel

def row599 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck599 : row599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow599 := by decide +kernel

theorem rowEval599 (x : Key → ℝ) : Integer.Sparse.eval row599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck599, Integer.Sparse.eval_collectBalanced, rawRowCheck599]

def rawRow600 : Integer.Sparse Key := [(key2666, -1), (key2666, -1), (key2663, 2), (key2734, 1), (key2734, 1), (key2698, -1), (key2698, -1), (key2745, -2), (key2722, 1), (key2722, 1), (key2611, 1), (key2611, 1), (key2608, -2), (key2825, -1), (key2825, -1), (key2801, 1), (key2801, 1), (key2958, 2), (key2947, -1), (key2947, -1), (key2636, -1), (key2636, -1), (key2624, 1), (key2624, 1), (key2722, 1), (key2722, 1), (key2698, -1), (key2698, -1), (key2981, -1), (key2981, -1), (key2974, 1), (key2974, 1), (key2651, 2), (key2645, -1), (key2645, -1), (key2745, -2), (key2734, 1), (key2734, 1), (key2902, 1), (key2902, 1), (key2895, -1), (key2895, -1)]

theorem rawRowCheck600 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form4 = rawRow600 := by decide +kernel

def row600 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -4), (key2722, 4), (key2734, 4), (key2745, -4), (key2801, 2), (key2825, -2), (key2895, -2), (key2902, 2), (key2947, -2), (key2958, 2), (key2974, 2), (key2981, -2)]

theorem rowCheck600 : row600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow600 := by decide +kernel

theorem rowEval600 (x : Key → ℝ) : Integer.Sparse.eval row600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck600, Integer.Sparse.eval_collectBalanced, rawRowCheck600]

def rawRow601 : Integer.Sparse Key := [(key2698, -1), (key2701, -1), (key2722, 2), (key2663, 1), (key2666, 1), (key2722, -1), (key2745, -1), (key2666, -2), (key2701, 1), (key2734, 1), (key2801, 1), (key2804, 1), (key2825, -2), (key2608, -1), (key2611, -1), (key2947, 1), (key2958, 1), (key2611, 2), (key2804, -1), (key2825, -1), (key2698, -1), (key2701, -1), (key2971, 1), (key2974, 1), (key2624, 1), (key2627, 1), (key2971, -1), (key2981, -1), (key2627, -1), (key2636, -1), (key2701, 1), (key2722, 1), (key2734, 2), (key2892, -1), (key2895, -1), (key2645, -2), (key2892, 1), (key2902, 1), (key2645, 1), (key2651, 1), (key2734, -1), (key2745, -1)]

theorem rawRowCheck601 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form4 = rawRow601 := by decide +kernel

def row601 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -2), (key2722, 2), (key2734, 2), (key2745, -2), (key2801, 1), (key2825, -3), (key2895, -1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck601 : row601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow601 := by decide +kernel

theorem rowEval601 (x : Key → ℝ) : Integer.Sparse.eval row601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form4) x := by
  rw [rowCheck601, Integer.Sparse.eval_collectBalanced, rawRowCheck601]

def rawRow602 : Integer.Sparse Key := [(key2701, -1), (key2698, -1), (key2722, 2), (key2666, 1), (key2663, 1), (key2745, -1), (key2722, -1), (key2666, -2), (key2734, 1), (key2701, 1), (key2804, 1), (key2801, 1), (key2825, -2), (key2611, -1), (key2608, -1), (key2958, 1), (key2947, 1), (key2611, 2), (key2825, -1), (key2804, -1), (key2701, -1), (key2698, -1), (key2974, 1), (key2971, 1), (key2627, 1), (key2624, 1), (key2981, -1), (key2971, -1), (key2636, -1), (key2627, -1), (key2722, 1), (key2701, 1), (key2734, 2), (key2895, -1), (key2892, -1), (key2645, -2), (key2902, 1), (key2892, 1), (key2651, 1), (key2645, 1), (key2745, -1), (key2734, -1)]

theorem rawRowCheck602 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form4 = rawRow602 := by decide +kernel

def row602 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -2), (key2722, 2), (key2734, 2), (key2745, -2), (key2801, 1), (key2825, -3), (key2895, -1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck602 : row602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow602 := by decide +kernel

theorem rowEval602 (x : Key → ℝ) : Integer.Sparse.eval row602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck602, Integer.Sparse.eval_collectBalanced, rawRowCheck602]

def rawRow603 : Integer.Sparse Key := [(key2701, -1), (key2722, -1), (key2698, 2), (key2734, 1), (key2745, 1), (key2663, -1), (key2698, -1), (key2734, -2), (key2666, 1), (key2701, 1), (key2804, 1), (key2825, 1), (key2801, -2), (key2947, -1), (key2958, -1), (key2608, 1), (key2801, 1), (key2825, 2), (key2611, -1), (key2804, -1), (key2856, -1), (key2974, -1), (key2698, 1), (key2851, 1), (key2866, 1), (key2981, 1), (key2624, -1), (key2851, -1), (key2722, -1), (key2866, -1), (key2636, 1), (key2856, 1), (key2895, 2), (key2734, -1), (key2892, -1), (key2902, -2), (key2645, 1), (key2892, 1), (key2745, 1), (key2902, 1), (key2651, -1), (key2895, -1)]

theorem rawRowCheck603 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form4 = rawRow603 := by decide +kernel

def row603 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, -1), (key2825, 3), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck603 : row603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow603 := by decide +kernel

theorem rowEval603 (x : Key → ℝ) : Integer.Sparse.eval row603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck603, Integer.Sparse.eval_collectBalanced, rawRowCheck603]

def rawRow604 : Integer.Sparse Key := [(key2722, -1), (key2701, -1), (key2698, 2), (key2745, 1), (key2734, 1), (key2698, -1), (key2663, -1), (key2734, -2), (key2701, 1), (key2666, 1), (key2825, 1), (key2804, 1), (key2801, -2), (key2958, -1), (key2947, -1), (key2801, 1), (key2608, 1), (key2825, 2), (key2804, -1), (key2611, -1), (key2974, -1), (key2856, -1), (key2851, 1), (key2698, 1), (key2981, 1), (key2866, 1), (key2851, -1), (key2624, -1), (key2866, -1), (key2722, -1), (key2856, 1), (key2636, 1), (key2895, 2), (key2892, -1), (key2734, -1), (key2902, -2), (key2892, 1), (key2645, 1), (key2902, 1), (key2745, 1), (key2895, -1), (key2651, -1)]

theorem rawRowCheck604 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form4 = rawRow604 := by decide +kernel

def row604 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, -1), (key2825, 3), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck604 : row604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow604 := by decide +kernel

theorem rowEval604 (x : Key → ℝ) : Integer.Sparse.eval row604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form4) x := by
  rw [rowCheck604, Integer.Sparse.eval_collectBalanced, rawRowCheck604]

def rawRow605 : Integer.Sparse Key := [(key2734, -1), (key2734, -1), (key2745, 2), (key2666, 1), (key2666, 1), (key2722, -1), (key2722, -1), (key2663, -2), (key2698, 1), (key2698, 1), (key2947, 1), (key2947, 1), (key2958, -2), (key2611, -1), (key2611, -1), (key2825, 1), (key2825, 1), (key2608, 2), (key2801, -1), (key2801, -1), (key2722, -1), (key2722, -1), (key2981, 1), (key2981, 1), (key2636, 1), (key2636, 1), (key2974, -1), (key2974, -1), (key2624, -1), (key2624, -1), (key2698, 1), (key2698, 1), (key2745, 2), (key2902, -1), (key2902, -1), (key2651, -2), (key2895, 1), (key2895, 1), (key2645, 1), (key2645, 1), (key2734, -1), (key2734, -1)]

theorem rawRowCheck605 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form4 = rawRow605 := by decide +kernel

def row605 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2663, -2), (key2666, 2), (key2698, 4), (key2722, -4), (key2734, -4), (key2745, 4), (key2801, -2), (key2825, 2), (key2895, 2), (key2902, -2), (key2947, 2), (key2958, -2), (key2974, -2), (key2981, 2)]

theorem rowCheck605 : row605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow605 := by decide +kernel

theorem rowEval605 (x : Key → ℝ) : Integer.Sparse.eval row605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck605, Integer.Sparse.eval_collectBalanced, rawRowCheck605]

def rawRow606 : Integer.Sparse Key := [(key2734, -1), (key2745, -1), (key2734, 2), (key2701, 1), (key2722, 1), (key2666, -1), (key2701, -1), (key2698, -2), (key2663, 1), (key2698, 1), (key2947, 1), (key2958, 1), (key2947, -2), (key2804, -1), (key2825, -1), (key2611, 1), (key2804, 1), (key2801, 2), (key2608, -1), (key2801, -1), (key2866, -1), (key2981, -1), (key2722, 1), (key2866, 1), (key2856, 1), (key2974, 1), (key2636, -1), (key2856, -1), (key2698, -1), (key2851, -1), (key2624, 1), (key2851, 1), (key2902, 2), (key2745, -1), (key2902, -1), (key2895, -2), (key2651, 1), (key2895, 1), (key2734, 1), (key2892, 1), (key2645, -1), (key2892, -1)]

theorem rawRowCheck606 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form4 = rawRow606 := by decide +kernel

def row606 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -2), (key2722, 2), (key2734, 2), (key2745, -2), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck606 : row606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow606 := by decide +kernel

theorem rowEval606 (x : Key → ℝ) : Integer.Sparse.eval row606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck606, Integer.Sparse.eval_collectBalanced, rawRowCheck606]

def rawRow607 : Integer.Sparse Key := [(key2745, -1), (key2734, -1), (key2734, 2), (key2722, 1), (key2701, 1), (key2701, -1), (key2666, -1), (key2698, -2), (key2698, 1), (key2663, 1), (key2958, 1), (key2947, 1), (key2947, -2), (key2825, -1), (key2804, -1), (key2804, 1), (key2611, 1), (key2801, 2), (key2801, -1), (key2608, -1), (key2981, -1), (key2866, -1), (key2866, 1), (key2722, 1), (key2974, 1), (key2856, 1), (key2856, -1), (key2636, -1), (key2851, -1), (key2698, -1), (key2851, 1), (key2624, 1), (key2902, 2), (key2902, -1), (key2745, -1), (key2895, -2), (key2895, 1), (key2651, 1), (key2892, 1), (key2734, 1), (key2892, -1), (key2645, -1)]

theorem rawRowCheck607 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form4 = rawRow607 := by decide +kernel

def row607 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -2), (key2722, 2), (key2734, 2), (key2745, -2), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck607 : row607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow607 := by decide +kernel

theorem rowEval607 (x : Key → ℝ) : Integer.Sparse.eval row607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form4) x := by
  rw [rowCheck607, Integer.Sparse.eval_collectBalanced, rawRowCheck607]

end MUB6.Certificate.GramRows

end OAI
