import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
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

def rawRow19712 : Integer.Sparse Key := [(key456, 24), (key208, 24), (key377, 24), (key428, 24), (key428, 24)]

theorem rawRowCheck19712 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form1 = rawRow19712 := by decide +kernel

def row19712 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19712 : row19712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19712 := by decide +kernel

theorem rowEval19712 (x : Key → ℝ) : Integer.Sparse.eval row19712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19712, Integer.Sparse.eval_collectBalanced, rawRowCheck19712]

def rawRow19713 : Integer.Sparse Key := [(key456, 24), (key208, 24), (key428, 24), (key377, 24), (key428, 24)]

theorem rawRowCheck19713 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form1 = rawRow19713 := by decide +kernel

def row19713 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19713 : row19713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19713 := by decide +kernel

theorem rowEval19713 (x : Key → ℝ) : Integer.Sparse.eval row19713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19713, Integer.Sparse.eval_collectBalanced, rawRowCheck19713]

def rawRow19714 : Integer.Sparse Key := [(key456, 24), (key208, 24), (key428, 24), (key428, 24), (key377, 24)]

theorem rawRowCheck19714 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form1 = rawRow19714 := by decide +kernel

def row19714 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19714 : row19714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19714 := by decide +kernel

theorem rowEval19714 (x : Key → ℝ) : Integer.Sparse.eval row19714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19714, Integer.Sparse.eval_collectBalanced, rawRowCheck19714]

def rawRow19715 : Integer.Sparse Key := [(key456, 24), (key377, 24), (key208, 24), (key428, 24), (key428, 24)]

theorem rawRowCheck19715 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form1 = rawRow19715 := by decide +kernel

def row19715 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19715 : row19715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19715 := by decide +kernel

theorem rowEval19715 (x : Key → ℝ) : Integer.Sparse.eval row19715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19715, Integer.Sparse.eval_collectBalanced, rawRowCheck19715]

def rawRow19716 : Integer.Sparse Key := [(key456, 24), (key377, 24), (key428, 24), (key208, 24), (key428, 24)]

theorem rawRowCheck19716 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form1 = rawRow19716 := by decide +kernel

def row19716 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19716 : row19716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19716 := by decide +kernel

theorem rowEval19716 (x : Key → ℝ) : Integer.Sparse.eval row19716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19716, Integer.Sparse.eval_collectBalanced, rawRowCheck19716]

def rawRow19717 : Integer.Sparse Key := [(key456, 24), (key377, 24), (key428, 24), (key428, 24), (key208, 24)]

theorem rawRowCheck19717 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form1 = rawRow19717 := by decide +kernel

def row19717 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19717 : row19717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19717 := by decide +kernel

theorem rowEval19717 (x : Key → ℝ) : Integer.Sparse.eval row19717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19717, Integer.Sparse.eval_collectBalanced, rawRowCheck19717]

def rawRow19718 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key208, 24), (key377, 24), (key428, 24)]

theorem rawRowCheck19718 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form1 = rawRow19718 := by decide +kernel

def row19718 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19718 : row19718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19718 := by decide +kernel

theorem rowEval19718 (x : Key → ℝ) : Integer.Sparse.eval row19718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19718, Integer.Sparse.eval_collectBalanced, rawRowCheck19718]

def rawRow19719 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key208, 24), (key428, 24), (key377, 24)]

theorem rawRowCheck19719 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form1 = rawRow19719 := by decide +kernel

def row19719 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19719 : row19719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19719 := by decide +kernel

theorem rowEval19719 (x : Key → ℝ) : Integer.Sparse.eval row19719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19719, Integer.Sparse.eval_collectBalanced, rawRowCheck19719]

def rawRow19720 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key377, 24), (key208, 24), (key428, 24)]

theorem rawRowCheck19720 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form1 = rawRow19720 := by decide +kernel

def row19720 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19720 : row19720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19720 := by decide +kernel

theorem rowEval19720 (x : Key → ℝ) : Integer.Sparse.eval row19720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19720, Integer.Sparse.eval_collectBalanced, rawRowCheck19720]

def rawRow19721 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key377, 24), (key428, 24), (key208, 24)]

theorem rawRowCheck19721 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form1 = rawRow19721 := by decide +kernel

def row19721 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19721 : row19721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19721 := by decide +kernel

theorem rowEval19721 (x : Key → ℝ) : Integer.Sparse.eval row19721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19721, Integer.Sparse.eval_collectBalanced, rawRowCheck19721]

def rawRow19722 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key428, 24), (key208, 24), (key377, 24)]

theorem rawRowCheck19722 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form1 = rawRow19722 := by decide +kernel

def row19722 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19722 : row19722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19722 := by decide +kernel

theorem rowEval19722 (x : Key → ℝ) : Integer.Sparse.eval row19722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19722, Integer.Sparse.eval_collectBalanced, rawRowCheck19722]

def rawRow19723 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key428, 24), (key377, 24), (key208, 24)]

theorem rawRowCheck19723 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form1 = rawRow19723 := by decide +kernel

def row19723 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19723 : row19723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19723 := by decide +kernel

theorem rowEval19723 (x : Key → ℝ) : Integer.Sparse.eval row19723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19723, Integer.Sparse.eval_collectBalanced, rawRowCheck19723]

def rawRow19724 : Integer.Sparse Key := [(key1291, 2), (key1299, 2), (key1299, 2), (key1311, 2), (key1319, 2), (key1311, 2), (key1327, 2), (key1319, 2), (key1327, 2), (key1352, 2), (key1352, 2), (key1355, 2), (key1386, 2), (key1394, 2), (key1394, 2), (key1419, 2), (key1427, 2), (key1419, 2), (key1445, 2), (key1427, 2), (key1445, 2), (key1473, 2), (key1473, 2), (key1481, 2), (key1541, 2), (key1549, 2), (key1541, 2), (key1557, 2), (key1549, 2), (key1557, 2), (key1568, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1594, 2), (key1617, 2), (key1625, 2), (key1617, 2), (key1634, 2), (key1625, 2), (key1634, 2), (key1682, 2), (key1684, 2), (key1682, 2), (key1690, 2), (key1684, 2), (key1690, 2), (key1897, 2), (key1897, 2), (key1900, 2), (key1904, 2), (key1904, 2), (key1912, 2), (key1919, 2), (key1921, 2), (key1919, 2), (key1927, 2), (key1921, 2), (key1927, 2)]

theorem rawRowCheck19724 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form2 = rawRow19724 := by decide +kernel

def row19724 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19724 : row19724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19724 := by decide +kernel

theorem rowEval19724 (x : Key → ℝ) : Integer.Sparse.eval row19724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19724, Integer.Sparse.eval_collectBalanced, rawRowCheck19724]

def rawRow19725 : Integer.Sparse Key := [(key1299, 2), (key1291, 2), (key1299, 2), (key1319, 2), (key1311, 2), (key1327, 2), (key1311, 2), (key1327, 2), (key1319, 2), (key1352, 2), (key1355, 2), (key1352, 2), (key1394, 2), (key1386, 2), (key1394, 2), (key1427, 2), (key1419, 2), (key1445, 2), (key1419, 2), (key1445, 2), (key1427, 2), (key1473, 2), (key1481, 2), (key1473, 2), (key1549, 2), (key1541, 2), (key1557, 2), (key1541, 2), (key1557, 2), (key1549, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1625, 2), (key1617, 2), (key1634, 2), (key1617, 2), (key1634, 2), (key1625, 2), (key1684, 2), (key1682, 2), (key1690, 2), (key1682, 2), (key1690, 2), (key1684, 2), (key1897, 2), (key1900, 2), (key1897, 2), (key1904, 2), (key1912, 2), (key1904, 2), (key1921, 2), (key1919, 2), (key1927, 2), (key1919, 2), (key1927, 2), (key1921, 2)]

theorem rawRowCheck19725 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form2 = rawRow19725 := by decide +kernel

def row19725 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19725 : row19725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19725 := by decide +kernel

theorem rowEval19725 (x : Key → ℝ) : Integer.Sparse.eval row19725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19725, Integer.Sparse.eval_collectBalanced, rawRowCheck19725]

def rawRow19726 : Integer.Sparse Key := [(key1299, 2), (key1299, 2), (key1291, 2), (key1327, 2), (key1327, 2), (key1319, 2), (key1319, 2), (key1311, 2), (key1311, 2), (key1355, 2), (key1352, 2), (key1352, 2), (key1394, 2), (key1394, 2), (key1386, 2), (key1445, 2), (key1445, 2), (key1427, 2), (key1427, 2), (key1419, 2), (key1419, 2), (key1481, 2), (key1473, 2), (key1473, 2), (key1557, 2), (key1557, 2), (key1549, 2), (key1549, 2), (key1541, 2), (key1541, 2), (key1594, 2), (key1594, 2), (key1576, 2), (key1576, 2), (key1568, 2), (key1568, 2), (key1634, 2), (key1634, 2), (key1625, 2), (key1625, 2), (key1617, 2), (key1617, 2), (key1690, 2), (key1690, 2), (key1684, 2), (key1684, 2), (key1682, 2), (key1682, 2), (key1900, 2), (key1897, 2), (key1897, 2), (key1912, 2), (key1904, 2), (key1904, 2), (key1927, 2), (key1927, 2), (key1921, 2), (key1921, 2), (key1919, 2), (key1919, 2)]

theorem rawRowCheck19726 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form2 = rawRow19726 := by decide +kernel

def row19726 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19726 : row19726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19726 := by decide +kernel

theorem rowEval19726 (x : Key → ℝ) : Integer.Sparse.eval row19726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19726, Integer.Sparse.eval_collectBalanced, rawRowCheck19726]

def rawRow19727 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1291, 2), (key1299, 2), (key1311, 2), (key1327, 2), (key1352, 2), (key1355, 2), (key1299, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1473, 2), (key1386, 2), (key1394, 2), (key1419, 2), (key1445, 2), (key1473, 2), (key1481, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1568, 2), (key1576, 2), (key1617, 2), (key1625, 2), (key1682, 2), (key1684, 2), (key1541, 2), (key1549, 2), (key1617, 2), (key1634, 2), (key1682, 2), (key1690, 2), (key1541, 2), (key1557, 2), (key1568, 2), (key1594, 2), (key1684, 2), (key1690, 2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1904, 2), (key1919, 2), (key1921, 2), (key1897, 2), (key1919, 2), (key1927, 2), (key1897, 2), (key1900, 2), (key1904, 2), (key1912, 2), (key1921, 2), (key1927, 2)]

theorem rawRowCheck19727 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form2 = rawRow19727 := by decide +kernel

def row19727 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19727 : row19727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19727 := by decide +kernel

theorem rowEval19727 (x : Key → ℝ) : Integer.Sparse.eval row19727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19727, Integer.Sparse.eval_collectBalanced, rawRowCheck19727]

def rawRow19728 : Integer.Sparse Key := [(key1319, 2), (key1311, 2), (key1352, 2), (key1299, 2), (key1291, 2), (key1327, 2), (key1311, 2), (key1355, 2), (key1352, 2), (key1299, 2), (key1327, 2), (key1319, 2), (key1427, 2), (key1419, 2), (key1473, 2), (key1394, 2), (key1386, 2), (key1445, 2), (key1419, 2), (key1481, 2), (key1473, 2), (key1394, 2), (key1445, 2), (key1427, 2), (key1576, 2), (key1568, 2), (key1625, 2), (key1617, 2), (key1684, 2), (key1682, 2), (key1549, 2), (key1541, 2), (key1634, 2), (key1617, 2), (key1690, 2), (key1682, 2), (key1557, 2), (key1541, 2), (key1594, 2), (key1568, 2), (key1690, 2), (key1684, 2), (key1557, 2), (key1549, 2), (key1594, 2), (key1576, 2), (key1634, 2), (key1625, 2), (key1904, 2), (key1921, 2), (key1919, 2), (key1897, 2), (key1927, 2), (key1919, 2), (key1900, 2), (key1897, 2), (key1912, 2), (key1904, 2), (key1927, 2), (key1921, 2)]

theorem rawRowCheck19728 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form2 = rawRow19728 := by decide +kernel

def row19728 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19728 : row19728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19728 := by decide +kernel

theorem rowEval19728 (x : Key → ℝ) : Integer.Sparse.eval row19728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19728, Integer.Sparse.eval_collectBalanced, rawRowCheck19728]

def rawRow19729 : Integer.Sparse Key := [(key1311, 2), (key1352, 2), (key1319, 2), (key1311, 2), (key1352, 2), (key1291, 2), (key1355, 2), (key1299, 2), (key1327, 2), (key1319, 2), (key1299, 2), (key1327, 2), (key1419, 2), (key1473, 2), (key1427, 2), (key1419, 2), (key1473, 2), (key1386, 2), (key1481, 2), (key1394, 2), (key1445, 2), (key1427, 2), (key1394, 2), (key1445, 2), (key1617, 2), (key1682, 2), (key1568, 2), (key1684, 2), (key1576, 2), (key1625, 2), (key1617, 2), (key1682, 2), (key1541, 2), (key1690, 2), (key1549, 2), (key1634, 2), (key1568, 2), (key1684, 2), (key1541, 2), (key1690, 2), (key1557, 2), (key1594, 2), (key1576, 2), (key1625, 2), (key1549, 2), (key1634, 2), (key1557, 2), (key1594, 2), (key1919, 2), (key1904, 2), (key1921, 2), (key1919, 2), (key1897, 2), (key1927, 2), (key1904, 2), (key1921, 2), (key1897, 2), (key1927, 2), (key1900, 2), (key1912, 2)]

theorem rawRowCheck19729 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form2 = rawRow19729 := by decide +kernel

def row19729 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19729 : row19729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19729 := by decide +kernel

theorem rowEval19729 (x : Key → ℝ) : Integer.Sparse.eval row19729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19729, Integer.Sparse.eval_collectBalanced, rawRowCheck19729]

def rawRow19730 : Integer.Sparse Key := [(key1352, 2), (key1311, 2), (key1319, 2), (key1352, 2), (key1311, 2), (key1355, 2), (key1291, 2), (key1327, 2), (key1299, 2), (key1319, 2), (key1327, 2), (key1299, 2), (key1473, 2), (key1419, 2), (key1427, 2), (key1473, 2), (key1419, 2), (key1481, 2), (key1386, 2), (key1445, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1394, 2), (key1682, 2), (key1617, 2), (key1684, 2), (key1568, 2), (key1625, 2), (key1576, 2), (key1682, 2), (key1617, 2), (key1690, 2), (key1541, 2), (key1634, 2), (key1549, 2), (key1684, 2), (key1568, 2), (key1690, 2), (key1541, 2), (key1594, 2), (key1557, 2), (key1625, 2), (key1576, 2), (key1634, 2), (key1549, 2), (key1594, 2), (key1557, 2), (key1919, 2), (key1921, 2), (key1904, 2), (key1919, 2), (key1927, 2), (key1897, 2), (key1921, 2), (key1904, 2), (key1927, 2), (key1897, 2), (key1912, 2), (key1900, 2)]

theorem rawRowCheck19730 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form2 = rawRow19730 := by decide +kernel

def row19730 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19730 : row19730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19730 := by decide +kernel

theorem rowEval19730 (x : Key → ℝ) : Integer.Sparse.eval row19730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19730, Integer.Sparse.eval_collectBalanced, rawRowCheck19730]

def rawRow19731 : Integer.Sparse Key := [(key1319, 2), (key1352, 2), (key1311, 2), (key1327, 2), (key1355, 2), (key1299, 2), (key1352, 2), (key1291, 2), (key1311, 2), (key1327, 2), (key1299, 2), (key1319, 2), (key1427, 2), (key1473, 2), (key1419, 2), (key1445, 2), (key1481, 2), (key1394, 2), (key1473, 2), (key1386, 2), (key1419, 2), (key1445, 2), (key1394, 2), (key1427, 2), (key1625, 2), (key1684, 2), (key1576, 2), (key1682, 2), (key1568, 2), (key1617, 2), (key1634, 2), (key1690, 2), (key1549, 2), (key1682, 2), (key1541, 2), (key1617, 2), (key1594, 2), (key1690, 2), (key1557, 2), (key1684, 2), (key1541, 2), (key1568, 2), (key1594, 2), (key1634, 2), (key1557, 2), (key1625, 2), (key1549, 2), (key1576, 2), (key1921, 2), (key1904, 2), (key1919, 2), (key1927, 2), (key1897, 2), (key1919, 2), (key1912, 2), (key1927, 2), (key1900, 2), (key1921, 2), (key1897, 2), (key1904, 2)]

theorem rawRowCheck19731 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form2 = rawRow19731 := by decide +kernel

def row19731 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19731 : row19731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19731 := by decide +kernel

theorem rowEval19731 (x : Key → ℝ) : Integer.Sparse.eval row19731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19731, Integer.Sparse.eval_collectBalanced, rawRowCheck19731]

def rawRow19732 : Integer.Sparse Key := [(key1352, 2), (key1319, 2), (key1311, 2), (key1355, 2), (key1327, 2), (key1352, 2), (key1299, 2), (key1311, 2), (key1291, 2), (key1327, 2), (key1319, 2), (key1299, 2), (key1473, 2), (key1427, 2), (key1419, 2), (key1481, 2), (key1445, 2), (key1473, 2), (key1394, 2), (key1419, 2), (key1386, 2), (key1445, 2), (key1427, 2), (key1394, 2), (key1684, 2), (key1625, 2), (key1682, 2), (key1576, 2), (key1617, 2), (key1568, 2), (key1690, 2), (key1634, 2), (key1682, 2), (key1549, 2), (key1617, 2), (key1541, 2), (key1690, 2), (key1594, 2), (key1684, 2), (key1557, 2), (key1568, 2), (key1541, 2), (key1634, 2), (key1594, 2), (key1625, 2), (key1557, 2), (key1576, 2), (key1549, 2), (key1921, 2), (key1919, 2), (key1904, 2), (key1927, 2), (key1919, 2), (key1897, 2), (key1927, 2), (key1912, 2), (key1921, 2), (key1900, 2), (key1904, 2), (key1897, 2)]

theorem rawRowCheck19732 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form2 = rawRow19732 := by decide +kernel

def row19732 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19732 : row19732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19732 := by decide +kernel

theorem rowEval19732 (x : Key → ℝ) : Integer.Sparse.eval row19732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19732, Integer.Sparse.eval_collectBalanced, rawRowCheck19732]

def rawRow19733 : Integer.Sparse Key := [(key1327, 2), (key1327, 2), (key1355, 2), (key1299, 2), (key1299, 2), (key1319, 2), (key1319, 2), (key1352, 2), (key1352, 2), (key1291, 2), (key1311, 2), (key1311, 2), (key1445, 2), (key1445, 2), (key1481, 2), (key1394, 2), (key1394, 2), (key1427, 2), (key1427, 2), (key1473, 2), (key1473, 2), (key1386, 2), (key1419, 2), (key1419, 2), (key1594, 2), (key1594, 2), (key1634, 2), (key1634, 2), (key1690, 2), (key1690, 2), (key1557, 2), (key1557, 2), (key1625, 2), (key1625, 2), (key1684, 2), (key1684, 2), (key1549, 2), (key1549, 2), (key1576, 2), (key1576, 2), (key1682, 2), (key1682, 2), (key1541, 2), (key1541, 2), (key1568, 2), (key1568, 2), (key1617, 2), (key1617, 2), (key1912, 2), (key1927, 2), (key1927, 2), (key1900, 2), (key1921, 2), (key1921, 2), (key1897, 2), (key1897, 2), (key1904, 2), (key1904, 2), (key1919, 2), (key1919, 2)]

theorem rawRowCheck19733 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form2 = rawRow19733 := by decide +kernel

def row19733 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19733 : row19733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19733 := by decide +kernel

theorem rowEval19733 (x : Key → ℝ) : Integer.Sparse.eval row19733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19733, Integer.Sparse.eval_collectBalanced, rawRowCheck19733]

def rawRow19734 : Integer.Sparse Key := [(key1327, 2), (key1355, 2), (key1327, 2), (key1319, 2), (key1352, 2), (key1299, 2), (key1352, 2), (key1299, 2), (key1319, 2), (key1311, 2), (key1291, 2), (key1311, 2), (key1445, 2), (key1481, 2), (key1445, 2), (key1427, 2), (key1473, 2), (key1394, 2), (key1473, 2), (key1394, 2), (key1427, 2), (key1419, 2), (key1386, 2), (key1419, 2), (key1634, 2), (key1690, 2), (key1594, 2), (key1690, 2), (key1594, 2), (key1634, 2), (key1625, 2), (key1684, 2), (key1557, 2), (key1684, 2), (key1557, 2), (key1625, 2), (key1576, 2), (key1682, 2), (key1549, 2), (key1682, 2), (key1549, 2), (key1576, 2), (key1568, 2), (key1617, 2), (key1541, 2), (key1617, 2), (key1541, 2), (key1568, 2), (key1927, 2), (key1912, 2), (key1927, 2), (key1921, 2), (key1900, 2), (key1921, 2), (key1904, 2), (key1919, 2), (key1897, 2), (key1919, 2), (key1897, 2), (key1904, 2)]

theorem rawRowCheck19734 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form2 = rawRow19734 := by decide +kernel

def row19734 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19734 : row19734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19734 := by decide +kernel

theorem rowEval19734 (x : Key → ℝ) : Integer.Sparse.eval row19734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19734, Integer.Sparse.eval_collectBalanced, rawRowCheck19734]

def rawRow19735 : Integer.Sparse Key := [(key1355, 2), (key1327, 2), (key1327, 2), (key1352, 2), (key1319, 2), (key1352, 2), (key1299, 2), (key1319, 2), (key1299, 2), (key1311, 2), (key1311, 2), (key1291, 2), (key1481, 2), (key1445, 2), (key1445, 2), (key1473, 2), (key1427, 2), (key1473, 2), (key1394, 2), (key1427, 2), (key1394, 2), (key1419, 2), (key1419, 2), (key1386, 2), (key1690, 2), (key1634, 2), (key1690, 2), (key1594, 2), (key1634, 2), (key1594, 2), (key1684, 2), (key1625, 2), (key1684, 2), (key1557, 2), (key1625, 2), (key1557, 2), (key1682, 2), (key1576, 2), (key1682, 2), (key1549, 2), (key1576, 2), (key1549, 2), (key1617, 2), (key1568, 2), (key1617, 2), (key1541, 2), (key1568, 2), (key1541, 2), (key1927, 2), (key1927, 2), (key1912, 2), (key1921, 2), (key1921, 2), (key1900, 2), (key1919, 2), (key1904, 2), (key1919, 2), (key1897, 2), (key1904, 2), (key1897, 2)]

theorem rawRowCheck19735 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form2 = rawRow19735 := by decide +kernel

def row19735 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19735 : row19735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19735 := by decide +kernel

theorem rowEval19735 (x : Key → ℝ) : Integer.Sparse.eval row19735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19735, Integer.Sparse.eval_collectBalanced, rawRowCheck19735]

def rawRow19736 : Integer.Sparse Key := [(key1386, 2), (key1394, 2), (key1394, 2), (key1541, 2), (key1549, 2), (key1541, 2), (key1557, 2), (key1549, 2), (key1557, 2), (key1897, 2), (key1897, 2), (key1900, 2), (key1291, 2), (key1299, 2), (key1299, 2), (key1568, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1594, 2), (key1904, 2), (key1904, 2), (key1912, 2), (key1311, 2), (key1319, 2), (key1311, 2), (key1327, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1419, 2), (key1445, 2), (key1427, 2), (key1445, 2), (key1617, 2), (key1625, 2), (key1617, 2), (key1634, 2), (key1625, 2), (key1634, 2), (key1919, 2), (key1921, 2), (key1919, 2), (key1927, 2), (key1921, 2), (key1927, 2), (key1352, 2), (key1352, 2), (key1355, 2), (key1473, 2), (key1473, 2), (key1481, 2), (key1682, 2), (key1684, 2), (key1682, 2), (key1690, 2), (key1684, 2), (key1690, 2)]

theorem rawRowCheck19736 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form2 = rawRow19736 := by decide +kernel

def row19736 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19736 : row19736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19736 := by decide +kernel

theorem rowEval19736 (x : Key → ℝ) : Integer.Sparse.eval row19736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19736, Integer.Sparse.eval_collectBalanced, rawRowCheck19736]

def rawRow19737 : Integer.Sparse Key := [(key1394, 2), (key1386, 2), (key1394, 2), (key1549, 2), (key1541, 2), (key1557, 2), (key1541, 2), (key1557, 2), (key1549, 2), (key1897, 2), (key1900, 2), (key1897, 2), (key1299, 2), (key1291, 2), (key1299, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1904, 2), (key1912, 2), (key1904, 2), (key1319, 2), (key1311, 2), (key1327, 2), (key1311, 2), (key1327, 2), (key1319, 2), (key1427, 2), (key1419, 2), (key1445, 2), (key1419, 2), (key1445, 2), (key1427, 2), (key1625, 2), (key1617, 2), (key1634, 2), (key1617, 2), (key1634, 2), (key1625, 2), (key1921, 2), (key1919, 2), (key1927, 2), (key1919, 2), (key1927, 2), (key1921, 2), (key1352, 2), (key1355, 2), (key1352, 2), (key1473, 2), (key1481, 2), (key1473, 2), (key1684, 2), (key1682, 2), (key1690, 2), (key1682, 2), (key1690, 2), (key1684, 2)]

theorem rawRowCheck19737 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form2 = rawRow19737 := by decide +kernel

def row19737 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19737 : row19737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19737 := by decide +kernel

theorem rowEval19737 (x : Key → ℝ) : Integer.Sparse.eval row19737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19737, Integer.Sparse.eval_collectBalanced, rawRowCheck19737]

def rawRow19738 : Integer.Sparse Key := [(key1394, 2), (key1394, 2), (key1386, 2), (key1557, 2), (key1557, 2), (key1549, 2), (key1549, 2), (key1541, 2), (key1541, 2), (key1900, 2), (key1897, 2), (key1897, 2), (key1299, 2), (key1299, 2), (key1291, 2), (key1594, 2), (key1594, 2), (key1576, 2), (key1576, 2), (key1568, 2), (key1568, 2), (key1912, 2), (key1904, 2), (key1904, 2), (key1327, 2), (key1327, 2), (key1319, 2), (key1319, 2), (key1311, 2), (key1311, 2), (key1445, 2), (key1445, 2), (key1427, 2), (key1427, 2), (key1419, 2), (key1419, 2), (key1634, 2), (key1634, 2), (key1625, 2), (key1625, 2), (key1617, 2), (key1617, 2), (key1927, 2), (key1927, 2), (key1921, 2), (key1921, 2), (key1919, 2), (key1919, 2), (key1355, 2), (key1352, 2), (key1352, 2), (key1481, 2), (key1473, 2), (key1473, 2), (key1690, 2), (key1690, 2), (key1684, 2), (key1684, 2), (key1682, 2), (key1682, 2)]

theorem rawRowCheck19738 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form2 = rawRow19738 := by decide +kernel

def row19738 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19738 : row19738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19738 := by decide +kernel

theorem rowEval19738 (x : Key → ℝ) : Integer.Sparse.eval row19738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19738, Integer.Sparse.eval_collectBalanced, rawRowCheck19738]

def rawRow19739 : Integer.Sparse Key := [(key1541, 2), (key1549, 2), (key1897, 2), (key1386, 2), (key1394, 2), (key1541, 2), (key1557, 2), (key1897, 2), (key1900, 2), (key1394, 2), (key1549, 2), (key1557, 2), (key1568, 2), (key1576, 2), (key1904, 2), (key1291, 2), (key1299, 2), (key1568, 2), (key1594, 2), (key1904, 2), (key1912, 2), (key1299, 2), (key1576, 2), (key1594, 2), (key1419, 2), (key1427, 2), (key1617, 2), (key1625, 2), (key1919, 2), (key1921, 2), (key1311, 2), (key1319, 2), (key1617, 2), (key1634, 2), (key1919, 2), (key1927, 2), (key1311, 2), (key1327, 2), (key1419, 2), (key1445, 2), (key1921, 2), (key1927, 2), (key1319, 2), (key1327, 2), (key1427, 2), (key1445, 2), (key1625, 2), (key1634, 2), (key1473, 2), (key1682, 2), (key1684, 2), (key1352, 2), (key1682, 2), (key1690, 2), (key1352, 2), (key1355, 2), (key1473, 2), (key1481, 2), (key1684, 2), (key1690, 2)]

theorem rawRowCheck19739 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form2 = rawRow19739 := by decide +kernel

def row19739 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19739 : row19739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19739 := by decide +kernel

theorem rowEval19739 (x : Key → ℝ) : Integer.Sparse.eval row19739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19739, Integer.Sparse.eval_collectBalanced, rawRowCheck19739]

def rawRow19740 : Integer.Sparse Key := [(key1549, 2), (key1541, 2), (key1897, 2), (key1394, 2), (key1386, 2), (key1557, 2), (key1541, 2), (key1900, 2), (key1897, 2), (key1394, 2), (key1557, 2), (key1549, 2), (key1576, 2), (key1568, 2), (key1904, 2), (key1299, 2), (key1291, 2), (key1594, 2), (key1568, 2), (key1912, 2), (key1904, 2), (key1299, 2), (key1594, 2), (key1576, 2), (key1427, 2), (key1419, 2), (key1625, 2), (key1617, 2), (key1921, 2), (key1919, 2), (key1319, 2), (key1311, 2), (key1634, 2), (key1617, 2), (key1927, 2), (key1919, 2), (key1327, 2), (key1311, 2), (key1445, 2), (key1419, 2), (key1927, 2), (key1921, 2), (key1327, 2), (key1319, 2), (key1445, 2), (key1427, 2), (key1634, 2), (key1625, 2), (key1473, 2), (key1684, 2), (key1682, 2), (key1352, 2), (key1690, 2), (key1682, 2), (key1355, 2), (key1352, 2), (key1481, 2), (key1473, 2), (key1690, 2), (key1684, 2)]

theorem rawRowCheck19740 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form2 = rawRow19740 := by decide +kernel

def row19740 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19740 : row19740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19740 := by decide +kernel

theorem rowEval19740 (x : Key → ℝ) : Integer.Sparse.eval row19740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19740, Integer.Sparse.eval_collectBalanced, rawRowCheck19740]

def rawRow19741 : Integer.Sparse Key := [(key1541, 2), (key1897, 2), (key1549, 2), (key1541, 2), (key1897, 2), (key1386, 2), (key1900, 2), (key1394, 2), (key1557, 2), (key1549, 2), (key1394, 2), (key1557, 2), (key1568, 2), (key1904, 2), (key1576, 2), (key1568, 2), (key1904, 2), (key1291, 2), (key1912, 2), (key1299, 2), (key1594, 2), (key1576, 2), (key1299, 2), (key1594, 2), (key1617, 2), (key1919, 2), (key1419, 2), (key1921, 2), (key1427, 2), (key1625, 2), (key1617, 2), (key1919, 2), (key1311, 2), (key1927, 2), (key1319, 2), (key1634, 2), (key1419, 2), (key1921, 2), (key1311, 2), (key1927, 2), (key1327, 2), (key1445, 2), (key1427, 2), (key1625, 2), (key1319, 2), (key1634, 2), (key1327, 2), (key1445, 2), (key1682, 2), (key1473, 2), (key1684, 2), (key1682, 2), (key1352, 2), (key1690, 2), (key1473, 2), (key1684, 2), (key1352, 2), (key1690, 2), (key1355, 2), (key1481, 2)]

theorem rawRowCheck19741 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form2 = rawRow19741 := by decide +kernel

def row19741 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19741 : row19741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19741 := by decide +kernel

theorem rowEval19741 (x : Key → ℝ) : Integer.Sparse.eval row19741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19741, Integer.Sparse.eval_collectBalanced, rawRowCheck19741]

def rawRow19742 : Integer.Sparse Key := [(key1897, 2), (key1541, 2), (key1549, 2), (key1897, 2), (key1541, 2), (key1900, 2), (key1386, 2), (key1557, 2), (key1394, 2), (key1549, 2), (key1557, 2), (key1394, 2), (key1904, 2), (key1568, 2), (key1576, 2), (key1904, 2), (key1568, 2), (key1912, 2), (key1291, 2), (key1594, 2), (key1299, 2), (key1576, 2), (key1594, 2), (key1299, 2), (key1919, 2), (key1617, 2), (key1921, 2), (key1419, 2), (key1625, 2), (key1427, 2), (key1919, 2), (key1617, 2), (key1927, 2), (key1311, 2), (key1634, 2), (key1319, 2), (key1921, 2), (key1419, 2), (key1927, 2), (key1311, 2), (key1445, 2), (key1327, 2), (key1625, 2), (key1427, 2), (key1634, 2), (key1319, 2), (key1445, 2), (key1327, 2), (key1682, 2), (key1684, 2), (key1473, 2), (key1682, 2), (key1690, 2), (key1352, 2), (key1684, 2), (key1473, 2), (key1690, 2), (key1352, 2), (key1481, 2), (key1355, 2)]

theorem rawRowCheck19742 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form2 = rawRow19742 := by decide +kernel

def row19742 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19742 : row19742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19742 := by decide +kernel

theorem rowEval19742 (x : Key → ℝ) : Integer.Sparse.eval row19742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19742, Integer.Sparse.eval_collectBalanced, rawRowCheck19742]

def rawRow19743 : Integer.Sparse Key := [(key1549, 2), (key1897, 2), (key1541, 2), (key1557, 2), (key1900, 2), (key1394, 2), (key1897, 2), (key1386, 2), (key1541, 2), (key1557, 2), (key1394, 2), (key1549, 2), (key1576, 2), (key1904, 2), (key1568, 2), (key1594, 2), (key1912, 2), (key1299, 2), (key1904, 2), (key1291, 2), (key1568, 2), (key1594, 2), (key1299, 2), (key1576, 2), (key1625, 2), (key1921, 2), (key1427, 2), (key1919, 2), (key1419, 2), (key1617, 2), (key1634, 2), (key1927, 2), (key1319, 2), (key1919, 2), (key1311, 2), (key1617, 2), (key1445, 2), (key1927, 2), (key1327, 2), (key1921, 2), (key1311, 2), (key1419, 2), (key1445, 2), (key1634, 2), (key1327, 2), (key1625, 2), (key1319, 2), (key1427, 2), (key1684, 2), (key1473, 2), (key1682, 2), (key1690, 2), (key1352, 2), (key1682, 2), (key1481, 2), (key1690, 2), (key1355, 2), (key1684, 2), (key1352, 2), (key1473, 2)]

theorem rawRowCheck19743 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form2 = rawRow19743 := by decide +kernel

def row19743 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19743 : row19743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19743 := by decide +kernel

theorem rowEval19743 (x : Key → ℝ) : Integer.Sparse.eval row19743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19743, Integer.Sparse.eval_collectBalanced, rawRowCheck19743]

def rawRow19744 : Integer.Sparse Key := [(key1897, 2), (key1549, 2), (key1541, 2), (key1900, 2), (key1557, 2), (key1897, 2), (key1394, 2), (key1541, 2), (key1386, 2), (key1557, 2), (key1549, 2), (key1394, 2), (key1904, 2), (key1576, 2), (key1568, 2), (key1912, 2), (key1594, 2), (key1904, 2), (key1299, 2), (key1568, 2), (key1291, 2), (key1594, 2), (key1576, 2), (key1299, 2), (key1921, 2), (key1625, 2), (key1919, 2), (key1427, 2), (key1617, 2), (key1419, 2), (key1927, 2), (key1634, 2), (key1919, 2), (key1319, 2), (key1617, 2), (key1311, 2), (key1927, 2), (key1445, 2), (key1921, 2), (key1327, 2), (key1419, 2), (key1311, 2), (key1634, 2), (key1445, 2), (key1625, 2), (key1327, 2), (key1427, 2), (key1319, 2), (key1684, 2), (key1682, 2), (key1473, 2), (key1690, 2), (key1682, 2), (key1352, 2), (key1690, 2), (key1481, 2), (key1684, 2), (key1355, 2), (key1473, 2), (key1352, 2)]

theorem rawRowCheck19744 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form2 = rawRow19744 := by decide +kernel

def row19744 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19744 : row19744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19744 := by decide +kernel

theorem rowEval19744 (x : Key → ℝ) : Integer.Sparse.eval row19744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19744, Integer.Sparse.eval_collectBalanced, rawRowCheck19744]

def rawRow19745 : Integer.Sparse Key := [(key1557, 2), (key1557, 2), (key1900, 2), (key1394, 2), (key1394, 2), (key1549, 2), (key1549, 2), (key1897, 2), (key1897, 2), (key1386, 2), (key1541, 2), (key1541, 2), (key1594, 2), (key1594, 2), (key1912, 2), (key1299, 2), (key1299, 2), (key1576, 2), (key1576, 2), (key1904, 2), (key1904, 2), (key1291, 2), (key1568, 2), (key1568, 2), (key1445, 2), (key1445, 2), (key1634, 2), (key1634, 2), (key1927, 2), (key1927, 2), (key1327, 2), (key1327, 2), (key1625, 2), (key1625, 2), (key1921, 2), (key1921, 2), (key1319, 2), (key1319, 2), (key1427, 2), (key1427, 2), (key1919, 2), (key1919, 2), (key1311, 2), (key1311, 2), (key1419, 2), (key1419, 2), (key1617, 2), (key1617, 2), (key1481, 2), (key1690, 2), (key1690, 2), (key1355, 2), (key1684, 2), (key1684, 2), (key1352, 2), (key1352, 2), (key1473, 2), (key1473, 2), (key1682, 2), (key1682, 2)]

theorem rawRowCheck19745 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form2 = rawRow19745 := by decide +kernel

def row19745 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19745 : row19745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19745 := by decide +kernel

theorem rowEval19745 (x : Key → ℝ) : Integer.Sparse.eval row19745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19745, Integer.Sparse.eval_collectBalanced, rawRowCheck19745]

def rawRow19746 : Integer.Sparse Key := [(key1557, 2), (key1900, 2), (key1557, 2), (key1549, 2), (key1897, 2), (key1394, 2), (key1897, 2), (key1394, 2), (key1549, 2), (key1541, 2), (key1386, 2), (key1541, 2), (key1594, 2), (key1912, 2), (key1594, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1568, 2), (key1291, 2), (key1568, 2), (key1634, 2), (key1927, 2), (key1445, 2), (key1927, 2), (key1445, 2), (key1634, 2), (key1625, 2), (key1921, 2), (key1327, 2), (key1921, 2), (key1327, 2), (key1625, 2), (key1427, 2), (key1919, 2), (key1319, 2), (key1919, 2), (key1319, 2), (key1427, 2), (key1419, 2), (key1617, 2), (key1311, 2), (key1617, 2), (key1311, 2), (key1419, 2), (key1690, 2), (key1481, 2), (key1690, 2), (key1684, 2), (key1355, 2), (key1684, 2), (key1473, 2), (key1682, 2), (key1352, 2), (key1682, 2), (key1352, 2), (key1473, 2)]

theorem rawRowCheck19746 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form2 = rawRow19746 := by decide +kernel

def row19746 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19746 : row19746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19746 := by decide +kernel

theorem rowEval19746 (x : Key → ℝ) : Integer.Sparse.eval row19746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19746, Integer.Sparse.eval_collectBalanced, rawRowCheck19746]

def rawRow19747 : Integer.Sparse Key := [(key1900, 2), (key1557, 2), (key1557, 2), (key1897, 2), (key1549, 2), (key1897, 2), (key1394, 2), (key1549, 2), (key1394, 2), (key1541, 2), (key1541, 2), (key1386, 2), (key1912, 2), (key1594, 2), (key1594, 2), (key1904, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1299, 2), (key1568, 2), (key1568, 2), (key1291, 2), (key1927, 2), (key1634, 2), (key1927, 2), (key1445, 2), (key1634, 2), (key1445, 2), (key1921, 2), (key1625, 2), (key1921, 2), (key1327, 2), (key1625, 2), (key1327, 2), (key1919, 2), (key1427, 2), (key1919, 2), (key1319, 2), (key1427, 2), (key1319, 2), (key1617, 2), (key1419, 2), (key1617, 2), (key1311, 2), (key1419, 2), (key1311, 2), (key1690, 2), (key1690, 2), (key1481, 2), (key1684, 2), (key1684, 2), (key1355, 2), (key1682, 2), (key1473, 2), (key1682, 2), (key1352, 2), (key1473, 2), (key1352, 2)]

theorem rawRowCheck19747 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form2 = rawRow19747 := by decide +kernel

def row19747 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19747 : row19747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19747 := by decide +kernel

theorem rowEval19747 (x : Key → ℝ) : Integer.Sparse.eval row19747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19747, Integer.Sparse.eval_collectBalanced, rawRowCheck19747]

def rawRow19748 : Integer.Sparse Key := [(key1419, 2), (key1427, 2), (key1473, 2), (key1568, 2), (key1576, 2), (key1617, 2), (key1625, 2), (key1682, 2), (key1684, 2), (key1904, 2), (key1919, 2), (key1921, 2), (key1311, 2), (key1319, 2), (key1352, 2), (key1541, 2), (key1549, 2), (key1617, 2), (key1634, 2), (key1682, 2), (key1690, 2), (key1897, 2), (key1919, 2), (key1927, 2), (key1291, 2), (key1299, 2), (key1311, 2), (key1327, 2), (key1352, 2), (key1355, 2), (key1386, 2), (key1394, 2), (key1419, 2), (key1445, 2), (key1473, 2), (key1481, 2), (key1541, 2), (key1557, 2), (key1568, 2), (key1594, 2), (key1684, 2), (key1690, 2), (key1897, 2), (key1900, 2), (key1904, 2), (key1912, 2), (key1921, 2), (key1927, 2), (key1299, 2), (key1319, 2), (key1327, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2)]

theorem rawRowCheck19748 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form2 = rawRow19748 := by decide +kernel

def row19748 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19748 : row19748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19748 := by decide +kernel

theorem rowEval19748 (x : Key → ℝ) : Integer.Sparse.eval row19748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19748, Integer.Sparse.eval_collectBalanced, rawRowCheck19748]

def rawRow19749 : Integer.Sparse Key := [(key1427, 2), (key1419, 2), (key1473, 2), (key1576, 2), (key1568, 2), (key1625, 2), (key1617, 2), (key1684, 2), (key1682, 2), (key1904, 2), (key1921, 2), (key1919, 2), (key1319, 2), (key1311, 2), (key1352, 2), (key1549, 2), (key1541, 2), (key1634, 2), (key1617, 2), (key1690, 2), (key1682, 2), (key1897, 2), (key1927, 2), (key1919, 2), (key1299, 2), (key1291, 2), (key1327, 2), (key1311, 2), (key1355, 2), (key1352, 2), (key1394, 2), (key1386, 2), (key1445, 2), (key1419, 2), (key1481, 2), (key1473, 2), (key1557, 2), (key1541, 2), (key1594, 2), (key1568, 2), (key1690, 2), (key1684, 2), (key1900, 2), (key1897, 2), (key1912, 2), (key1904, 2), (key1927, 2), (key1921, 2), (key1299, 2), (key1327, 2), (key1319, 2), (key1394, 2), (key1445, 2), (key1427, 2), (key1557, 2), (key1549, 2), (key1594, 2), (key1576, 2), (key1634, 2), (key1625, 2)]

theorem rawRowCheck19749 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form2 = rawRow19749 := by decide +kernel

def row19749 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19749 : row19749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19749 := by decide +kernel

theorem rowEval19749 (x : Key → ℝ) : Integer.Sparse.eval row19749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19749, Integer.Sparse.eval_collectBalanced, rawRowCheck19749]

def rawRow19750 : Integer.Sparse Key := [(key1419, 2), (key1473, 2), (key1427, 2), (key1617, 2), (key1682, 2), (key1568, 2), (key1684, 2), (key1576, 2), (key1625, 2), (key1919, 2), (key1904, 2), (key1921, 2), (key1311, 2), (key1352, 2), (key1319, 2), (key1617, 2), (key1682, 2), (key1541, 2), (key1690, 2), (key1549, 2), (key1634, 2), (key1919, 2), (key1897, 2), (key1927, 2), (key1311, 2), (key1352, 2), (key1291, 2), (key1355, 2), (key1299, 2), (key1327, 2), (key1419, 2), (key1473, 2), (key1386, 2), (key1481, 2), (key1394, 2), (key1445, 2), (key1568, 2), (key1684, 2), (key1541, 2), (key1690, 2), (key1557, 2), (key1594, 2), (key1904, 2), (key1921, 2), (key1897, 2), (key1927, 2), (key1900, 2), (key1912, 2), (key1319, 2), (key1299, 2), (key1327, 2), (key1427, 2), (key1394, 2), (key1445, 2), (key1576, 2), (key1625, 2), (key1549, 2), (key1634, 2), (key1557, 2), (key1594, 2)]

theorem rawRowCheck19750 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form2 = rawRow19750 := by decide +kernel

def row19750 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19750 : row19750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19750 := by decide +kernel

theorem rowEval19750 (x : Key → ℝ) : Integer.Sparse.eval row19750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19750, Integer.Sparse.eval_collectBalanced, rawRowCheck19750]

def rawRow19751 : Integer.Sparse Key := [(key1473, 2), (key1419, 2), (key1427, 2), (key1682, 2), (key1617, 2), (key1684, 2), (key1568, 2), (key1625, 2), (key1576, 2), (key1919, 2), (key1921, 2), (key1904, 2), (key1352, 2), (key1311, 2), (key1319, 2), (key1682, 2), (key1617, 2), (key1690, 2), (key1541, 2), (key1634, 2), (key1549, 2), (key1919, 2), (key1927, 2), (key1897, 2), (key1352, 2), (key1311, 2), (key1355, 2), (key1291, 2), (key1327, 2), (key1299, 2), (key1473, 2), (key1419, 2), (key1481, 2), (key1386, 2), (key1445, 2), (key1394, 2), (key1684, 2), (key1568, 2), (key1690, 2), (key1541, 2), (key1594, 2), (key1557, 2), (key1921, 2), (key1904, 2), (key1927, 2), (key1897, 2), (key1912, 2), (key1900, 2), (key1319, 2), (key1327, 2), (key1299, 2), (key1427, 2), (key1445, 2), (key1394, 2), (key1625, 2), (key1576, 2), (key1634, 2), (key1549, 2), (key1594, 2), (key1557, 2)]

theorem rawRowCheck19751 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form2 = rawRow19751 := by decide +kernel

def row19751 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19751 : row19751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19751 := by decide +kernel

theorem rowEval19751 (x : Key → ℝ) : Integer.Sparse.eval row19751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19751, Integer.Sparse.eval_collectBalanced, rawRowCheck19751]

def rawRow19752 : Integer.Sparse Key := [(key1427, 2), (key1473, 2), (key1419, 2), (key1625, 2), (key1684, 2), (key1576, 2), (key1682, 2), (key1568, 2), (key1617, 2), (key1921, 2), (key1904, 2), (key1919, 2), (key1319, 2), (key1352, 2), (key1311, 2), (key1634, 2), (key1690, 2), (key1549, 2), (key1682, 2), (key1541, 2), (key1617, 2), (key1927, 2), (key1897, 2), (key1919, 2), (key1327, 2), (key1355, 2), (key1299, 2), (key1352, 2), (key1291, 2), (key1311, 2), (key1445, 2), (key1481, 2), (key1394, 2), (key1473, 2), (key1386, 2), (key1419, 2), (key1594, 2), (key1690, 2), (key1557, 2), (key1684, 2), (key1541, 2), (key1568, 2), (key1912, 2), (key1927, 2), (key1900, 2), (key1921, 2), (key1897, 2), (key1904, 2), (key1327, 2), (key1299, 2), (key1319, 2), (key1445, 2), (key1394, 2), (key1427, 2), (key1594, 2), (key1634, 2), (key1557, 2), (key1625, 2), (key1549, 2), (key1576, 2)]

theorem rawRowCheck19752 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form2 = rawRow19752 := by decide +kernel

def row19752 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19752 : row19752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19752 := by decide +kernel

theorem rowEval19752 (x : Key → ℝ) : Integer.Sparse.eval row19752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19752, Integer.Sparse.eval_collectBalanced, rawRowCheck19752]

def rawRow19753 : Integer.Sparse Key := [(key1473, 2), (key1427, 2), (key1419, 2), (key1684, 2), (key1625, 2), (key1682, 2), (key1576, 2), (key1617, 2), (key1568, 2), (key1921, 2), (key1919, 2), (key1904, 2), (key1352, 2), (key1319, 2), (key1311, 2), (key1690, 2), (key1634, 2), (key1682, 2), (key1549, 2), (key1617, 2), (key1541, 2), (key1927, 2), (key1919, 2), (key1897, 2), (key1355, 2), (key1327, 2), (key1352, 2), (key1299, 2), (key1311, 2), (key1291, 2), (key1481, 2), (key1445, 2), (key1473, 2), (key1394, 2), (key1419, 2), (key1386, 2), (key1690, 2), (key1594, 2), (key1684, 2), (key1557, 2), (key1568, 2), (key1541, 2), (key1927, 2), (key1912, 2), (key1921, 2), (key1900, 2), (key1904, 2), (key1897, 2), (key1327, 2), (key1319, 2), (key1299, 2), (key1445, 2), (key1427, 2), (key1394, 2), (key1634, 2), (key1594, 2), (key1625, 2), (key1557, 2), (key1576, 2), (key1549, 2)]

theorem rawRowCheck19753 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form2 = rawRow19753 := by decide +kernel

def row19753 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19753 : row19753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19753 := by decide +kernel

theorem rowEval19753 (x : Key → ℝ) : Integer.Sparse.eval row19753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19753, Integer.Sparse.eval_collectBalanced, rawRowCheck19753]

def rawRow19754 : Integer.Sparse Key := [(key1568, 2), (key1576, 2), (key1904, 2), (key1419, 2), (key1427, 2), (key1617, 2), (key1625, 2), (key1919, 2), (key1921, 2), (key1473, 2), (key1682, 2), (key1684, 2), (key1541, 2), (key1549, 2), (key1897, 2), (key1311, 2), (key1319, 2), (key1617, 2), (key1634, 2), (key1919, 2), (key1927, 2), (key1352, 2), (key1682, 2), (key1690, 2), (key1386, 2), (key1394, 2), (key1541, 2), (key1557, 2), (key1897, 2), (key1900, 2), (key1291, 2), (key1299, 2), (key1568, 2), (key1594, 2), (key1904, 2), (key1912, 2), (key1311, 2), (key1327, 2), (key1419, 2), (key1445, 2), (key1921, 2), (key1927, 2), (key1352, 2), (key1355, 2), (key1473, 2), (key1481, 2), (key1684, 2), (key1690, 2), (key1394, 2), (key1549, 2), (key1557, 2), (key1299, 2), (key1576, 2), (key1594, 2), (key1319, 2), (key1327, 2), (key1427, 2), (key1445, 2), (key1625, 2), (key1634, 2)]

theorem rawRowCheck19754 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form2 = rawRow19754 := by decide +kernel

def row19754 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19754 : row19754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19754 := by decide +kernel

theorem rowEval19754 (x : Key → ℝ) : Integer.Sparse.eval row19754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19754, Integer.Sparse.eval_collectBalanced, rawRowCheck19754]

def rawRow19755 : Integer.Sparse Key := [(key1576, 2), (key1568, 2), (key1904, 2), (key1427, 2), (key1419, 2), (key1625, 2), (key1617, 2), (key1921, 2), (key1919, 2), (key1473, 2), (key1684, 2), (key1682, 2), (key1549, 2), (key1541, 2), (key1897, 2), (key1319, 2), (key1311, 2), (key1634, 2), (key1617, 2), (key1927, 2), (key1919, 2), (key1352, 2), (key1690, 2), (key1682, 2), (key1394, 2), (key1386, 2), (key1557, 2), (key1541, 2), (key1900, 2), (key1897, 2), (key1299, 2), (key1291, 2), (key1594, 2), (key1568, 2), (key1912, 2), (key1904, 2), (key1327, 2), (key1311, 2), (key1445, 2), (key1419, 2), (key1927, 2), (key1921, 2), (key1355, 2), (key1352, 2), (key1481, 2), (key1473, 2), (key1690, 2), (key1684, 2), (key1394, 2), (key1557, 2), (key1549, 2), (key1299, 2), (key1594, 2), (key1576, 2), (key1327, 2), (key1319, 2), (key1445, 2), (key1427, 2), (key1634, 2), (key1625, 2)]

theorem rawRowCheck19755 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form2 = rawRow19755 := by decide +kernel

def row19755 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19755 : row19755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19755 := by decide +kernel

theorem rowEval19755 (x : Key → ℝ) : Integer.Sparse.eval row19755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19755, Integer.Sparse.eval_collectBalanced, rawRowCheck19755]

def rawRow19756 : Integer.Sparse Key := [(key1568, 2), (key1904, 2), (key1576, 2), (key1617, 2), (key1919, 2), (key1419, 2), (key1921, 2), (key1427, 2), (key1625, 2), (key1682, 2), (key1473, 2), (key1684, 2), (key1541, 2), (key1897, 2), (key1549, 2), (key1617, 2), (key1919, 2), (key1311, 2), (key1927, 2), (key1319, 2), (key1634, 2), (key1682, 2), (key1352, 2), (key1690, 2), (key1541, 2), (key1897, 2), (key1386, 2), (key1900, 2), (key1394, 2), (key1557, 2), (key1568, 2), (key1904, 2), (key1291, 2), (key1912, 2), (key1299, 2), (key1594, 2), (key1419, 2), (key1921, 2), (key1311, 2), (key1927, 2), (key1327, 2), (key1445, 2), (key1473, 2), (key1684, 2), (key1352, 2), (key1690, 2), (key1355, 2), (key1481, 2), (key1549, 2), (key1394, 2), (key1557, 2), (key1576, 2), (key1299, 2), (key1594, 2), (key1427, 2), (key1625, 2), (key1319, 2), (key1634, 2), (key1327, 2), (key1445, 2)]

theorem rawRowCheck19756 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form2 = rawRow19756 := by decide +kernel

def row19756 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19756 : row19756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19756 := by decide +kernel

theorem rowEval19756 (x : Key → ℝ) : Integer.Sparse.eval row19756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19756, Integer.Sparse.eval_collectBalanced, rawRowCheck19756]

def rawRow19757 : Integer.Sparse Key := [(key1904, 2), (key1568, 2), (key1576, 2), (key1919, 2), (key1617, 2), (key1921, 2), (key1419, 2), (key1625, 2), (key1427, 2), (key1682, 2), (key1684, 2), (key1473, 2), (key1897, 2), (key1541, 2), (key1549, 2), (key1919, 2), (key1617, 2), (key1927, 2), (key1311, 2), (key1634, 2), (key1319, 2), (key1682, 2), (key1690, 2), (key1352, 2), (key1897, 2), (key1541, 2), (key1900, 2), (key1386, 2), (key1557, 2), (key1394, 2), (key1904, 2), (key1568, 2), (key1912, 2), (key1291, 2), (key1594, 2), (key1299, 2), (key1921, 2), (key1419, 2), (key1927, 2), (key1311, 2), (key1445, 2), (key1327, 2), (key1684, 2), (key1473, 2), (key1690, 2), (key1352, 2), (key1481, 2), (key1355, 2), (key1549, 2), (key1557, 2), (key1394, 2), (key1576, 2), (key1594, 2), (key1299, 2), (key1625, 2), (key1427, 2), (key1634, 2), (key1319, 2), (key1445, 2), (key1327, 2)]

theorem rawRowCheck19757 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form2 = rawRow19757 := by decide +kernel

def row19757 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19757 : row19757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19757 := by decide +kernel

theorem rowEval19757 (x : Key → ℝ) : Integer.Sparse.eval row19757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19757, Integer.Sparse.eval_collectBalanced, rawRowCheck19757]

def rawRow19758 : Integer.Sparse Key := [(key1576, 2), (key1904, 2), (key1568, 2), (key1625, 2), (key1921, 2), (key1427, 2), (key1919, 2), (key1419, 2), (key1617, 2), (key1684, 2), (key1473, 2), (key1682, 2), (key1549, 2), (key1897, 2), (key1541, 2), (key1634, 2), (key1927, 2), (key1319, 2), (key1919, 2), (key1311, 2), (key1617, 2), (key1690, 2), (key1352, 2), (key1682, 2), (key1557, 2), (key1900, 2), (key1394, 2), (key1897, 2), (key1386, 2), (key1541, 2), (key1594, 2), (key1912, 2), (key1299, 2), (key1904, 2), (key1291, 2), (key1568, 2), (key1445, 2), (key1927, 2), (key1327, 2), (key1921, 2), (key1311, 2), (key1419, 2), (key1481, 2), (key1690, 2), (key1355, 2), (key1684, 2), (key1352, 2), (key1473, 2), (key1557, 2), (key1394, 2), (key1549, 2), (key1594, 2), (key1299, 2), (key1576, 2), (key1445, 2), (key1634, 2), (key1327, 2), (key1625, 2), (key1319, 2), (key1427, 2)]

theorem rawRowCheck19758 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form2 = rawRow19758 := by decide +kernel

def row19758 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19758 : row19758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19758 := by decide +kernel

theorem rowEval19758 (x : Key → ℝ) : Integer.Sparse.eval row19758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19758, Integer.Sparse.eval_collectBalanced, rawRowCheck19758]

def rawRow19759 : Integer.Sparse Key := [(key1904, 2), (key1576, 2), (key1568, 2), (key1921, 2), (key1625, 2), (key1919, 2), (key1427, 2), (key1617, 2), (key1419, 2), (key1684, 2), (key1682, 2), (key1473, 2), (key1897, 2), (key1549, 2), (key1541, 2), (key1927, 2), (key1634, 2), (key1919, 2), (key1319, 2), (key1617, 2), (key1311, 2), (key1690, 2), (key1682, 2), (key1352, 2), (key1900, 2), (key1557, 2), (key1897, 2), (key1394, 2), (key1541, 2), (key1386, 2), (key1912, 2), (key1594, 2), (key1904, 2), (key1299, 2), (key1568, 2), (key1291, 2), (key1927, 2), (key1445, 2), (key1921, 2), (key1327, 2), (key1419, 2), (key1311, 2), (key1690, 2), (key1481, 2), (key1684, 2), (key1355, 2), (key1473, 2), (key1352, 2), (key1557, 2), (key1549, 2), (key1394, 2), (key1594, 2), (key1576, 2), (key1299, 2), (key1634, 2), (key1445, 2), (key1625, 2), (key1327, 2), (key1427, 2), (key1319, 2)]

theorem rawRowCheck19759 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form2 = rawRow19759 := by decide +kernel

def row19759 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19759 : row19759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19759 := by decide +kernel

theorem rowEval19759 (x : Key → ℝ) : Integer.Sparse.eval row19759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19759, Integer.Sparse.eval_collectBalanced, rawRowCheck19759]

def rawRow19760 : Integer.Sparse Key := [(key1617, 2), (key1682, 2), (key1919, 2), (key1419, 2), (key1473, 2), (key1568, 2), (key1684, 2), (key1904, 2), (key1921, 2), (key1427, 2), (key1576, 2), (key1625, 2), (key1617, 2), (key1682, 2), (key1919, 2), (key1311, 2), (key1352, 2), (key1541, 2), (key1690, 2), (key1897, 2), (key1927, 2), (key1319, 2), (key1549, 2), (key1634, 2), (key1419, 2), (key1473, 2), (key1568, 2), (key1684, 2), (key1904, 2), (key1921, 2), (key1311, 2), (key1352, 2), (key1541, 2), (key1690, 2), (key1897, 2), (key1927, 2), (key1291, 2), (key1355, 2), (key1386, 2), (key1481, 2), (key1900, 2), (key1912, 2), (key1299, 2), (key1327, 2), (key1394, 2), (key1445, 2), (key1557, 2), (key1594, 2), (key1427, 2), (key1576, 2), (key1625, 2), (key1319, 2), (key1549, 2), (key1634, 2), (key1299, 2), (key1327, 2), (key1394, 2), (key1445, 2), (key1557, 2), (key1594, 2)]

theorem rawRowCheck19760 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form2 = rawRow19760 := by decide +kernel

def row19760 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19760 : row19760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19760 := by decide +kernel

theorem rowEval19760 (x : Key → ℝ) : Integer.Sparse.eval row19760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19760, Integer.Sparse.eval_collectBalanced, rawRowCheck19760]

def rawRow19761 : Integer.Sparse Key := [(key1682, 2), (key1617, 2), (key1919, 2), (key1473, 2), (key1419, 2), (key1684, 2), (key1568, 2), (key1921, 2), (key1904, 2), (key1427, 2), (key1625, 2), (key1576, 2), (key1682, 2), (key1617, 2), (key1919, 2), (key1352, 2), (key1311, 2), (key1690, 2), (key1541, 2), (key1927, 2), (key1897, 2), (key1319, 2), (key1634, 2), (key1549, 2), (key1473, 2), (key1419, 2), (key1684, 2), (key1568, 2), (key1921, 2), (key1904, 2), (key1352, 2), (key1311, 2), (key1690, 2), (key1541, 2), (key1927, 2), (key1897, 2), (key1355, 2), (key1291, 2), (key1481, 2), (key1386, 2), (key1912, 2), (key1900, 2), (key1327, 2), (key1299, 2), (key1445, 2), (key1394, 2), (key1594, 2), (key1557, 2), (key1427, 2), (key1625, 2), (key1576, 2), (key1319, 2), (key1634, 2), (key1549, 2), (key1327, 2), (key1299, 2), (key1445, 2), (key1394, 2), (key1594, 2), (key1557, 2)]

theorem rawRowCheck19761 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form2 = rawRow19761 := by decide +kernel

def row19761 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19761 : row19761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19761 := by decide +kernel

theorem rowEval19761 (x : Key → ℝ) : Integer.Sparse.eval row19761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19761, Integer.Sparse.eval_collectBalanced, rawRowCheck19761]

def rawRow19762 : Integer.Sparse Key := [(key1617, 2), (key1919, 2), (key1682, 2), (key1568, 2), (key1904, 2), (key1419, 2), (key1921, 2), (key1473, 2), (key1684, 2), (key1576, 2), (key1427, 2), (key1625, 2), (key1617, 2), (key1919, 2), (key1682, 2), (key1541, 2), (key1897, 2), (key1311, 2), (key1927, 2), (key1352, 2), (key1690, 2), (key1549, 2), (key1319, 2), (key1634, 2), (key1568, 2), (key1904, 2), (key1419, 2), (key1921, 2), (key1473, 2), (key1684, 2), (key1541, 2), (key1897, 2), (key1311, 2), (key1927, 2), (key1352, 2), (key1690, 2), (key1386, 2), (key1900, 2), (key1291, 2), (key1912, 2), (key1355, 2), (key1481, 2), (key1394, 2), (key1557, 2), (key1299, 2), (key1594, 2), (key1327, 2), (key1445, 2), (key1576, 2), (key1427, 2), (key1625, 2), (key1549, 2), (key1319, 2), (key1634, 2), (key1394, 2), (key1557, 2), (key1299, 2), (key1594, 2), (key1327, 2), (key1445, 2)]

theorem rawRowCheck19762 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form2 = rawRow19762 := by decide +kernel

def row19762 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19762 : row19762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19762 := by decide +kernel

theorem rowEval19762 (x : Key → ℝ) : Integer.Sparse.eval row19762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19762, Integer.Sparse.eval_collectBalanced, rawRowCheck19762]

def rawRow19763 : Integer.Sparse Key := [(key1919, 2), (key1617, 2), (key1682, 2), (key1904, 2), (key1568, 2), (key1921, 2), (key1419, 2), (key1684, 2), (key1473, 2), (key1576, 2), (key1625, 2), (key1427, 2), (key1919, 2), (key1617, 2), (key1682, 2), (key1897, 2), (key1541, 2), (key1927, 2), (key1311, 2), (key1690, 2), (key1352, 2), (key1549, 2), (key1634, 2), (key1319, 2), (key1904, 2), (key1568, 2), (key1921, 2), (key1419, 2), (key1684, 2), (key1473, 2), (key1897, 2), (key1541, 2), (key1927, 2), (key1311, 2), (key1690, 2), (key1352, 2), (key1900, 2), (key1386, 2), (key1912, 2), (key1291, 2), (key1481, 2), (key1355, 2), (key1557, 2), (key1394, 2), (key1594, 2), (key1299, 2), (key1445, 2), (key1327, 2), (key1576, 2), (key1625, 2), (key1427, 2), (key1549, 2), (key1634, 2), (key1319, 2), (key1557, 2), (key1394, 2), (key1594, 2), (key1299, 2), (key1445, 2), (key1327, 2)]

theorem rawRowCheck19763 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form2 = rawRow19763 := by decide +kernel

def row19763 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19763 : row19763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19763 := by decide +kernel

theorem rowEval19763 (x : Key → ℝ) : Integer.Sparse.eval row19763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19763, Integer.Sparse.eval_collectBalanced, rawRowCheck19763]

def rawRow19764 : Integer.Sparse Key := [(key1682, 2), (key1919, 2), (key1617, 2), (key1684, 2), (key1921, 2), (key1473, 2), (key1904, 2), (key1419, 2), (key1568, 2), (key1625, 2), (key1427, 2), (key1576, 2), (key1682, 2), (key1919, 2), (key1617, 2), (key1690, 2), (key1927, 2), (key1352, 2), (key1897, 2), (key1311, 2), (key1541, 2), (key1634, 2), (key1319, 2), (key1549, 2), (key1684, 2), (key1921, 2), (key1473, 2), (key1904, 2), (key1419, 2), (key1568, 2), (key1690, 2), (key1927, 2), (key1352, 2), (key1897, 2), (key1311, 2), (key1541, 2), (key1481, 2), (key1912, 2), (key1355, 2), (key1900, 2), (key1291, 2), (key1386, 2), (key1445, 2), (key1594, 2), (key1327, 2), (key1557, 2), (key1299, 2), (key1394, 2), (key1625, 2), (key1427, 2), (key1576, 2), (key1634, 2), (key1319, 2), (key1549, 2), (key1445, 2), (key1594, 2), (key1327, 2), (key1557, 2), (key1299, 2), (key1394, 2)]

theorem rawRowCheck19764 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form2 = rawRow19764 := by decide +kernel

def row19764 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19764 : row19764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19764 := by decide +kernel

theorem rowEval19764 (x : Key → ℝ) : Integer.Sparse.eval row19764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19764, Integer.Sparse.eval_collectBalanced, rawRowCheck19764]

def rawRow19765 : Integer.Sparse Key := [(key1919, 2), (key1682, 2), (key1617, 2), (key1921, 2), (key1684, 2), (key1904, 2), (key1473, 2), (key1568, 2), (key1419, 2), (key1625, 2), (key1576, 2), (key1427, 2), (key1919, 2), (key1682, 2), (key1617, 2), (key1927, 2), (key1690, 2), (key1897, 2), (key1352, 2), (key1541, 2), (key1311, 2), (key1634, 2), (key1549, 2), (key1319, 2), (key1921, 2), (key1684, 2), (key1904, 2), (key1473, 2), (key1568, 2), (key1419, 2), (key1927, 2), (key1690, 2), (key1897, 2), (key1352, 2), (key1541, 2), (key1311, 2), (key1912, 2), (key1481, 2), (key1900, 2), (key1355, 2), (key1386, 2), (key1291, 2), (key1594, 2), (key1445, 2), (key1557, 2), (key1327, 2), (key1394, 2), (key1299, 2), (key1625, 2), (key1576, 2), (key1427, 2), (key1634, 2), (key1549, 2), (key1319, 2), (key1594, 2), (key1445, 2), (key1557, 2), (key1327, 2), (key1394, 2), (key1299, 2)]

theorem rawRowCheck19765 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form2 = rawRow19765 := by decide +kernel

def row19765 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19765 : row19765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19765 := by decide +kernel

theorem rowEval19765 (x : Key → ℝ) : Integer.Sparse.eval row19765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19765, Integer.Sparse.eval_collectBalanced, rawRowCheck19765]

def rawRow19766 : Integer.Sparse Key := [(key1625, 2), (key1684, 2), (key1921, 2), (key1427, 2), (key1473, 2), (key1576, 2), (key1682, 2), (key1904, 2), (key1919, 2), (key1419, 2), (key1568, 2), (key1617, 2), (key1634, 2), (key1690, 2), (key1927, 2), (key1319, 2), (key1352, 2), (key1549, 2), (key1682, 2), (key1897, 2), (key1919, 2), (key1311, 2), (key1541, 2), (key1617, 2), (key1445, 2), (key1481, 2), (key1594, 2), (key1690, 2), (key1912, 2), (key1927, 2), (key1327, 2), (key1355, 2), (key1557, 2), (key1684, 2), (key1900, 2), (key1921, 2), (key1299, 2), (key1352, 2), (key1394, 2), (key1473, 2), (key1897, 2), (key1904, 2), (key1291, 2), (key1311, 2), (key1386, 2), (key1419, 2), (key1541, 2), (key1568, 2), (key1445, 2), (key1594, 2), (key1634, 2), (key1327, 2), (key1557, 2), (key1625, 2), (key1299, 2), (key1319, 2), (key1394, 2), (key1427, 2), (key1549, 2), (key1576, 2)]

theorem rawRowCheck19766 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form2 = rawRow19766 := by decide +kernel

def row19766 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19766 : row19766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19766 := by decide +kernel

theorem rowEval19766 (x : Key → ℝ) : Integer.Sparse.eval row19766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19766, Integer.Sparse.eval_collectBalanced, rawRowCheck19766]

def rawRow19767 : Integer.Sparse Key := [(key1684, 2), (key1625, 2), (key1921, 2), (key1473, 2), (key1427, 2), (key1682, 2), (key1576, 2), (key1919, 2), (key1904, 2), (key1419, 2), (key1617, 2), (key1568, 2), (key1690, 2), (key1634, 2), (key1927, 2), (key1352, 2), (key1319, 2), (key1682, 2), (key1549, 2), (key1919, 2), (key1897, 2), (key1311, 2), (key1617, 2), (key1541, 2), (key1481, 2), (key1445, 2), (key1690, 2), (key1594, 2), (key1927, 2), (key1912, 2), (key1355, 2), (key1327, 2), (key1684, 2), (key1557, 2), (key1921, 2), (key1900, 2), (key1352, 2), (key1299, 2), (key1473, 2), (key1394, 2), (key1904, 2), (key1897, 2), (key1311, 2), (key1291, 2), (key1419, 2), (key1386, 2), (key1568, 2), (key1541, 2), (key1445, 2), (key1634, 2), (key1594, 2), (key1327, 2), (key1625, 2), (key1557, 2), (key1319, 2), (key1299, 2), (key1427, 2), (key1394, 2), (key1576, 2), (key1549, 2)]

theorem rawRowCheck19767 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form2 = rawRow19767 := by decide +kernel

def row19767 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19767 : row19767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19767 := by decide +kernel

theorem rowEval19767 (x : Key → ℝ) : Integer.Sparse.eval row19767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19767, Integer.Sparse.eval_collectBalanced, rawRowCheck19767]

def rawRow19768 : Integer.Sparse Key := [(key1625, 2), (key1921, 2), (key1684, 2), (key1576, 2), (key1904, 2), (key1427, 2), (key1919, 2), (key1473, 2), (key1682, 2), (key1568, 2), (key1419, 2), (key1617, 2), (key1634, 2), (key1927, 2), (key1690, 2), (key1549, 2), (key1897, 2), (key1319, 2), (key1919, 2), (key1352, 2), (key1682, 2), (key1541, 2), (key1311, 2), (key1617, 2), (key1594, 2), (key1912, 2), (key1445, 2), (key1927, 2), (key1481, 2), (key1690, 2), (key1557, 2), (key1900, 2), (key1327, 2), (key1921, 2), (key1355, 2), (key1684, 2), (key1394, 2), (key1897, 2), (key1299, 2), (key1904, 2), (key1352, 2), (key1473, 2), (key1386, 2), (key1541, 2), (key1291, 2), (key1568, 2), (key1311, 2), (key1419, 2), (key1594, 2), (key1445, 2), (key1634, 2), (key1557, 2), (key1327, 2), (key1625, 2), (key1394, 2), (key1549, 2), (key1299, 2), (key1576, 2), (key1319, 2), (key1427, 2)]

theorem rawRowCheck19768 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form2 = rawRow19768 := by decide +kernel

def row19768 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19768 : row19768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19768 := by decide +kernel

theorem rowEval19768 (x : Key → ℝ) : Integer.Sparse.eval row19768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19768, Integer.Sparse.eval_collectBalanced, rawRowCheck19768]

def rawRow19769 : Integer.Sparse Key := [(key1921, 2), (key1625, 2), (key1684, 2), (key1904, 2), (key1576, 2), (key1919, 2), (key1427, 2), (key1682, 2), (key1473, 2), (key1568, 2), (key1617, 2), (key1419, 2), (key1927, 2), (key1634, 2), (key1690, 2), (key1897, 2), (key1549, 2), (key1919, 2), (key1319, 2), (key1682, 2), (key1352, 2), (key1541, 2), (key1617, 2), (key1311, 2), (key1912, 2), (key1594, 2), (key1927, 2), (key1445, 2), (key1690, 2), (key1481, 2), (key1900, 2), (key1557, 2), (key1921, 2), (key1327, 2), (key1684, 2), (key1355, 2), (key1897, 2), (key1394, 2), (key1904, 2), (key1299, 2), (key1473, 2), (key1352, 2), (key1541, 2), (key1386, 2), (key1568, 2), (key1291, 2), (key1419, 2), (key1311, 2), (key1594, 2), (key1634, 2), (key1445, 2), (key1557, 2), (key1625, 2), (key1327, 2), (key1549, 2), (key1394, 2), (key1576, 2), (key1299, 2), (key1427, 2), (key1319, 2)]

theorem rawRowCheck19769 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form2 = rawRow19769 := by decide +kernel

def row19769 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19769 : row19769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19769 := by decide +kernel

theorem rowEval19769 (x : Key → ℝ) : Integer.Sparse.eval row19769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19769, Integer.Sparse.eval_collectBalanced, rawRowCheck19769]

def rawRow19770 : Integer.Sparse Key := [(key1684, 2), (key1921, 2), (key1625, 2), (key1682, 2), (key1919, 2), (key1473, 2), (key1904, 2), (key1427, 2), (key1576, 2), (key1617, 2), (key1419, 2), (key1568, 2), (key1690, 2), (key1927, 2), (key1634, 2), (key1682, 2), (key1919, 2), (key1352, 2), (key1897, 2), (key1319, 2), (key1549, 2), (key1617, 2), (key1311, 2), (key1541, 2), (key1690, 2), (key1927, 2), (key1481, 2), (key1912, 2), (key1445, 2), (key1594, 2), (key1684, 2), (key1921, 2), (key1355, 2), (key1900, 2), (key1327, 2), (key1557, 2), (key1473, 2), (key1904, 2), (key1352, 2), (key1897, 2), (key1299, 2), (key1394, 2), (key1419, 2), (key1568, 2), (key1311, 2), (key1541, 2), (key1291, 2), (key1386, 2), (key1634, 2), (key1445, 2), (key1594, 2), (key1625, 2), (key1327, 2), (key1557, 2), (key1427, 2), (key1576, 2), (key1319, 2), (key1549, 2), (key1299, 2), (key1394, 2)]

theorem rawRowCheck19770 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form2 = rawRow19770 := by decide +kernel

def row19770 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19770 : row19770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19770 := by decide +kernel

theorem rowEval19770 (x : Key → ℝ) : Integer.Sparse.eval row19770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19770, Integer.Sparse.eval_collectBalanced, rawRowCheck19770]

def rawRow19771 : Integer.Sparse Key := [(key1921, 2), (key1684, 2), (key1625, 2), (key1919, 2), (key1682, 2), (key1904, 2), (key1473, 2), (key1576, 2), (key1427, 2), (key1617, 2), (key1568, 2), (key1419, 2), (key1927, 2), (key1690, 2), (key1634, 2), (key1919, 2), (key1682, 2), (key1897, 2), (key1352, 2), (key1549, 2), (key1319, 2), (key1617, 2), (key1541, 2), (key1311, 2), (key1927, 2), (key1690, 2), (key1912, 2), (key1481, 2), (key1594, 2), (key1445, 2), (key1921, 2), (key1684, 2), (key1900, 2), (key1355, 2), (key1557, 2), (key1327, 2), (key1904, 2), (key1473, 2), (key1897, 2), (key1352, 2), (key1394, 2), (key1299, 2), (key1568, 2), (key1419, 2), (key1541, 2), (key1311, 2), (key1386, 2), (key1291, 2), (key1634, 2), (key1594, 2), (key1445, 2), (key1625, 2), (key1557, 2), (key1327, 2), (key1576, 2), (key1427, 2), (key1549, 2), (key1319, 2), (key1394, 2), (key1299, 2)]

theorem rawRowCheck19771 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form2 = rawRow19771 := by decide +kernel

def row19771 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19771 : row19771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19771 := by decide +kernel

theorem rowEval19771 (x : Key → ℝ) : Integer.Sparse.eval row19771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19771, Integer.Sparse.eval_collectBalanced, rawRowCheck19771]

def rawRow19772 : Integer.Sparse Key := [(key1445, 2), (key1445, 2), (key1481, 2), (key1594, 2), (key1594, 2), (key1634, 2), (key1634, 2), (key1690, 2), (key1690, 2), (key1912, 2), (key1927, 2), (key1927, 2), (key1327, 2), (key1327, 2), (key1355, 2), (key1557, 2), (key1557, 2), (key1625, 2), (key1625, 2), (key1684, 2), (key1684, 2), (key1900, 2), (key1921, 2), (key1921, 2), (key1299, 2), (key1299, 2), (key1319, 2), (key1319, 2), (key1352, 2), (key1352, 2), (key1394, 2), (key1394, 2), (key1427, 2), (key1427, 2), (key1473, 2), (key1473, 2), (key1549, 2), (key1549, 2), (key1576, 2), (key1576, 2), (key1682, 2), (key1682, 2), (key1897, 2), (key1897, 2), (key1904, 2), (key1904, 2), (key1919, 2), (key1919, 2), (key1291, 2), (key1311, 2), (key1311, 2), (key1386, 2), (key1419, 2), (key1419, 2), (key1541, 2), (key1541, 2), (key1568, 2), (key1568, 2), (key1617, 2), (key1617, 2)]

theorem rawRowCheck19772 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form2 = rawRow19772 := by decide +kernel

def row19772 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19772 : row19772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19772 := by decide +kernel

theorem rowEval19772 (x : Key → ℝ) : Integer.Sparse.eval row19772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19772, Integer.Sparse.eval_collectBalanced, rawRowCheck19772]

def rawRow19773 : Integer.Sparse Key := [(key1445, 2), (key1481, 2), (key1445, 2), (key1634, 2), (key1690, 2), (key1594, 2), (key1690, 2), (key1594, 2), (key1634, 2), (key1927, 2), (key1912, 2), (key1927, 2), (key1327, 2), (key1355, 2), (key1327, 2), (key1625, 2), (key1684, 2), (key1557, 2), (key1684, 2), (key1557, 2), (key1625, 2), (key1921, 2), (key1900, 2), (key1921, 2), (key1319, 2), (key1352, 2), (key1299, 2), (key1352, 2), (key1299, 2), (key1319, 2), (key1427, 2), (key1473, 2), (key1394, 2), (key1473, 2), (key1394, 2), (key1427, 2), (key1576, 2), (key1682, 2), (key1549, 2), (key1682, 2), (key1549, 2), (key1576, 2), (key1904, 2), (key1919, 2), (key1897, 2), (key1919, 2), (key1897, 2), (key1904, 2), (key1311, 2), (key1291, 2), (key1311, 2), (key1419, 2), (key1386, 2), (key1419, 2), (key1568, 2), (key1617, 2), (key1541, 2), (key1617, 2), (key1541, 2), (key1568, 2)]

theorem rawRowCheck19773 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form2 = rawRow19773 := by decide +kernel

def row19773 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19773 : row19773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19773 := by decide +kernel

theorem rowEval19773 (x : Key → ℝ) : Integer.Sparse.eval row19773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19773, Integer.Sparse.eval_collectBalanced, rawRowCheck19773]

def rawRow19774 : Integer.Sparse Key := [(key1481, 2), (key1445, 2), (key1445, 2), (key1690, 2), (key1634, 2), (key1690, 2), (key1594, 2), (key1634, 2), (key1594, 2), (key1927, 2), (key1927, 2), (key1912, 2), (key1355, 2), (key1327, 2), (key1327, 2), (key1684, 2), (key1625, 2), (key1684, 2), (key1557, 2), (key1625, 2), (key1557, 2), (key1921, 2), (key1921, 2), (key1900, 2), (key1352, 2), (key1319, 2), (key1352, 2), (key1299, 2), (key1319, 2), (key1299, 2), (key1473, 2), (key1427, 2), (key1473, 2), (key1394, 2), (key1427, 2), (key1394, 2), (key1682, 2), (key1576, 2), (key1682, 2), (key1549, 2), (key1576, 2), (key1549, 2), (key1919, 2), (key1904, 2), (key1919, 2), (key1897, 2), (key1904, 2), (key1897, 2), (key1311, 2), (key1311, 2), (key1291, 2), (key1419, 2), (key1419, 2), (key1386, 2), (key1617, 2), (key1568, 2), (key1617, 2), (key1541, 2), (key1568, 2), (key1541, 2)]

theorem rawRowCheck19774 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form2 = rawRow19774 := by decide +kernel

def row19774 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19774 : row19774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19774 := by decide +kernel

theorem rowEval19774 (x : Key → ℝ) : Integer.Sparse.eval row19774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19774, Integer.Sparse.eval_collectBalanced, rawRowCheck19774]

def rawRow19775 : Integer.Sparse Key := [(key1594, 2), (key1594, 2), (key1912, 2), (key1445, 2), (key1445, 2), (key1634, 2), (key1634, 2), (key1927, 2), (key1927, 2), (key1481, 2), (key1690, 2), (key1690, 2), (key1557, 2), (key1557, 2), (key1900, 2), (key1327, 2), (key1327, 2), (key1625, 2), (key1625, 2), (key1921, 2), (key1921, 2), (key1355, 2), (key1684, 2), (key1684, 2), (key1394, 2), (key1394, 2), (key1549, 2), (key1549, 2), (key1897, 2), (key1897, 2), (key1299, 2), (key1299, 2), (key1576, 2), (key1576, 2), (key1904, 2), (key1904, 2), (key1319, 2), (key1319, 2), (key1427, 2), (key1427, 2), (key1919, 2), (key1919, 2), (key1352, 2), (key1352, 2), (key1473, 2), (key1473, 2), (key1682, 2), (key1682, 2), (key1386, 2), (key1541, 2), (key1541, 2), (key1291, 2), (key1568, 2), (key1568, 2), (key1311, 2), (key1311, 2), (key1419, 2), (key1419, 2), (key1617, 2), (key1617, 2)]

theorem rawRowCheck19775 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form2 = rawRow19775 := by decide +kernel

def row19775 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19775 : row19775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19775 := by decide +kernel

theorem rowEval19775 (x : Key → ℝ) : Integer.Sparse.eval row19775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19775, Integer.Sparse.eval_collectBalanced, rawRowCheck19775]

def rawRow19776 : Integer.Sparse Key := [(key1594, 2), (key1912, 2), (key1594, 2), (key1634, 2), (key1927, 2), (key1445, 2), (key1927, 2), (key1445, 2), (key1634, 2), (key1690, 2), (key1481, 2), (key1690, 2), (key1557, 2), (key1900, 2), (key1557, 2), (key1625, 2), (key1921, 2), (key1327, 2), (key1921, 2), (key1327, 2), (key1625, 2), (key1684, 2), (key1355, 2), (key1684, 2), (key1549, 2), (key1897, 2), (key1394, 2), (key1897, 2), (key1394, 2), (key1549, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1427, 2), (key1919, 2), (key1319, 2), (key1919, 2), (key1319, 2), (key1427, 2), (key1473, 2), (key1682, 2), (key1352, 2), (key1682, 2), (key1352, 2), (key1473, 2), (key1541, 2), (key1386, 2), (key1541, 2), (key1568, 2), (key1291, 2), (key1568, 2), (key1419, 2), (key1617, 2), (key1311, 2), (key1617, 2), (key1311, 2), (key1419, 2)]

theorem rawRowCheck19776 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form2 = rawRow19776 := by decide +kernel

def row19776 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19776 : row19776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19776 := by decide +kernel

theorem rowEval19776 (x : Key → ℝ) : Integer.Sparse.eval row19776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19776, Integer.Sparse.eval_collectBalanced, rawRowCheck19776]

def rawRow19777 : Integer.Sparse Key := [(key1912, 2), (key1594, 2), (key1594, 2), (key1927, 2), (key1634, 2), (key1927, 2), (key1445, 2), (key1634, 2), (key1445, 2), (key1690, 2), (key1690, 2), (key1481, 2), (key1900, 2), (key1557, 2), (key1557, 2), (key1921, 2), (key1625, 2), (key1921, 2), (key1327, 2), (key1625, 2), (key1327, 2), (key1684, 2), (key1684, 2), (key1355, 2), (key1897, 2), (key1549, 2), (key1897, 2), (key1394, 2), (key1549, 2), (key1394, 2), (key1904, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1299, 2), (key1919, 2), (key1427, 2), (key1919, 2), (key1319, 2), (key1427, 2), (key1319, 2), (key1682, 2), (key1473, 2), (key1682, 2), (key1352, 2), (key1473, 2), (key1352, 2), (key1541, 2), (key1541, 2), (key1386, 2), (key1568, 2), (key1568, 2), (key1291, 2), (key1617, 2), (key1419, 2), (key1617, 2), (key1311, 2), (key1419, 2), (key1311, 2)]

theorem rawRowCheck19777 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form2 = rawRow19777 := by decide +kernel

def row19777 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19777 : row19777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19777 := by decide +kernel

theorem rowEval19777 (x : Key → ℝ) : Integer.Sparse.eval row19777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19777, Integer.Sparse.eval_collectBalanced, rawRowCheck19777]

def rawRow19778 : Integer.Sparse Key := [(key1634, 2), (key1690, 2), (key1927, 2), (key1445, 2), (key1481, 2), (key1594, 2), (key1690, 2), (key1912, 2), (key1927, 2), (key1445, 2), (key1594, 2), (key1634, 2), (key1625, 2), (key1684, 2), (key1921, 2), (key1327, 2), (key1355, 2), (key1557, 2), (key1684, 2), (key1900, 2), (key1921, 2), (key1327, 2), (key1557, 2), (key1625, 2), (key1427, 2), (key1473, 2), (key1576, 2), (key1682, 2), (key1904, 2), (key1919, 2), (key1319, 2), (key1352, 2), (key1549, 2), (key1682, 2), (key1897, 2), (key1919, 2), (key1299, 2), (key1352, 2), (key1394, 2), (key1473, 2), (key1897, 2), (key1904, 2), (key1299, 2), (key1319, 2), (key1394, 2), (key1427, 2), (key1549, 2), (key1576, 2), (key1419, 2), (key1568, 2), (key1617, 2), (key1311, 2), (key1541, 2), (key1617, 2), (key1291, 2), (key1311, 2), (key1386, 2), (key1419, 2), (key1541, 2), (key1568, 2)]

theorem rawRowCheck19778 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form2 = rawRow19778 := by decide +kernel

def row19778 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19778 : row19778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19778 := by decide +kernel

theorem rowEval19778 (x : Key → ℝ) : Integer.Sparse.eval row19778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19778, Integer.Sparse.eval_collectBalanced, rawRowCheck19778]

def rawRow19779 : Integer.Sparse Key := [(key1690, 2), (key1634, 2), (key1927, 2), (key1481, 2), (key1445, 2), (key1690, 2), (key1594, 2), (key1927, 2), (key1912, 2), (key1445, 2), (key1634, 2), (key1594, 2), (key1684, 2), (key1625, 2), (key1921, 2), (key1355, 2), (key1327, 2), (key1684, 2), (key1557, 2), (key1921, 2), (key1900, 2), (key1327, 2), (key1625, 2), (key1557, 2), (key1473, 2), (key1427, 2), (key1682, 2), (key1576, 2), (key1919, 2), (key1904, 2), (key1352, 2), (key1319, 2), (key1682, 2), (key1549, 2), (key1919, 2), (key1897, 2), (key1352, 2), (key1299, 2), (key1473, 2), (key1394, 2), (key1904, 2), (key1897, 2), (key1319, 2), (key1299, 2), (key1427, 2), (key1394, 2), (key1576, 2), (key1549, 2), (key1419, 2), (key1617, 2), (key1568, 2), (key1311, 2), (key1617, 2), (key1541, 2), (key1311, 2), (key1291, 2), (key1419, 2), (key1386, 2), (key1568, 2), (key1541, 2)]

theorem rawRowCheck19779 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form2 = rawRow19779 := by decide +kernel

def row19779 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19779 : row19779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19779 := by decide +kernel

theorem rowEval19779 (x : Key → ℝ) : Integer.Sparse.eval row19779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19779, Integer.Sparse.eval_collectBalanced, rawRowCheck19779]

def rawRow19780 : Integer.Sparse Key := [(key1634, 2), (key1927, 2), (key1690, 2), (key1594, 2), (key1912, 2), (key1445, 2), (key1927, 2), (key1481, 2), (key1690, 2), (key1594, 2), (key1445, 2), (key1634, 2), (key1625, 2), (key1921, 2), (key1684, 2), (key1557, 2), (key1900, 2), (key1327, 2), (key1921, 2), (key1355, 2), (key1684, 2), (key1557, 2), (key1327, 2), (key1625, 2), (key1576, 2), (key1904, 2), (key1427, 2), (key1919, 2), (key1473, 2), (key1682, 2), (key1549, 2), (key1897, 2), (key1319, 2), (key1919, 2), (key1352, 2), (key1682, 2), (key1394, 2), (key1897, 2), (key1299, 2), (key1904, 2), (key1352, 2), (key1473, 2), (key1394, 2), (key1549, 2), (key1299, 2), (key1576, 2), (key1319, 2), (key1427, 2), (key1568, 2), (key1419, 2), (key1617, 2), (key1541, 2), (key1311, 2), (key1617, 2), (key1386, 2), (key1541, 2), (key1291, 2), (key1568, 2), (key1311, 2), (key1419, 2)]

theorem rawRowCheck19780 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form2 = rawRow19780 := by decide +kernel

def row19780 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19780 : row19780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19780 := by decide +kernel

theorem rowEval19780 (x : Key → ℝ) : Integer.Sparse.eval row19780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19780, Integer.Sparse.eval_collectBalanced, rawRowCheck19780]

def rawRow19781 : Integer.Sparse Key := [(key1927, 2), (key1634, 2), (key1690, 2), (key1912, 2), (key1594, 2), (key1927, 2), (key1445, 2), (key1690, 2), (key1481, 2), (key1594, 2), (key1634, 2), (key1445, 2), (key1921, 2), (key1625, 2), (key1684, 2), (key1900, 2), (key1557, 2), (key1921, 2), (key1327, 2), (key1684, 2), (key1355, 2), (key1557, 2), (key1625, 2), (key1327, 2), (key1904, 2), (key1576, 2), (key1919, 2), (key1427, 2), (key1682, 2), (key1473, 2), (key1897, 2), (key1549, 2), (key1919, 2), (key1319, 2), (key1682, 2), (key1352, 2), (key1897, 2), (key1394, 2), (key1904, 2), (key1299, 2), (key1473, 2), (key1352, 2), (key1549, 2), (key1394, 2), (key1576, 2), (key1299, 2), (key1427, 2), (key1319, 2), (key1568, 2), (key1617, 2), (key1419, 2), (key1541, 2), (key1617, 2), (key1311, 2), (key1541, 2), (key1386, 2), (key1568, 2), (key1291, 2), (key1419, 2), (key1311, 2)]

theorem rawRowCheck19781 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form2 = rawRow19781 := by decide +kernel

def row19781 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19781 : row19781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19781 := by decide +kernel

theorem rowEval19781 (x : Key → ℝ) : Integer.Sparse.eval row19781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19781, Integer.Sparse.eval_collectBalanced, rawRowCheck19781]

def rawRow19782 : Integer.Sparse Key := [(key1690, 2), (key1927, 2), (key1634, 2), (key1690, 2), (key1927, 2), (key1481, 2), (key1912, 2), (key1445, 2), (key1594, 2), (key1634, 2), (key1445, 2), (key1594, 2), (key1684, 2), (key1921, 2), (key1625, 2), (key1684, 2), (key1921, 2), (key1355, 2), (key1900, 2), (key1327, 2), (key1557, 2), (key1625, 2), (key1327, 2), (key1557, 2), (key1682, 2), (key1919, 2), (key1473, 2), (key1904, 2), (key1427, 2), (key1576, 2), (key1682, 2), (key1919, 2), (key1352, 2), (key1897, 2), (key1319, 2), (key1549, 2), (key1473, 2), (key1904, 2), (key1352, 2), (key1897, 2), (key1299, 2), (key1394, 2), (key1427, 2), (key1576, 2), (key1319, 2), (key1549, 2), (key1299, 2), (key1394, 2), (key1617, 2), (key1419, 2), (key1568, 2), (key1617, 2), (key1311, 2), (key1541, 2), (key1419, 2), (key1568, 2), (key1311, 2), (key1541, 2), (key1291, 2), (key1386, 2)]

theorem rawRowCheck19782 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form2 = rawRow19782 := by decide +kernel

def row19782 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19782 : row19782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19782 := by decide +kernel

theorem rowEval19782 (x : Key → ℝ) : Integer.Sparse.eval row19782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19782, Integer.Sparse.eval_collectBalanced, rawRowCheck19782]

def rawRow19783 : Integer.Sparse Key := [(key1927, 2), (key1690, 2), (key1634, 2), (key1927, 2), (key1690, 2), (key1912, 2), (key1481, 2), (key1594, 2), (key1445, 2), (key1634, 2), (key1594, 2), (key1445, 2), (key1921, 2), (key1684, 2), (key1625, 2), (key1921, 2), (key1684, 2), (key1900, 2), (key1355, 2), (key1557, 2), (key1327, 2), (key1625, 2), (key1557, 2), (key1327, 2), (key1919, 2), (key1682, 2), (key1904, 2), (key1473, 2), (key1576, 2), (key1427, 2), (key1919, 2), (key1682, 2), (key1897, 2), (key1352, 2), (key1549, 2), (key1319, 2), (key1904, 2), (key1473, 2), (key1897, 2), (key1352, 2), (key1394, 2), (key1299, 2), (key1576, 2), (key1427, 2), (key1549, 2), (key1319, 2), (key1394, 2), (key1299, 2), (key1617, 2), (key1568, 2), (key1419, 2), (key1617, 2), (key1541, 2), (key1311, 2), (key1568, 2), (key1419, 2), (key1541, 2), (key1311, 2), (key1386, 2), (key1291, 2)]

theorem rawRowCheck19783 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form2 = rawRow19783 := by decide +kernel

def row19783 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

theorem rowCheck19783 : row19783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19783 := by decide +kernel

theorem rowEval19783 (x : Key → ℝ) : Integer.Sparse.eval row19783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19783, Integer.Sparse.eval_collectBalanced, rawRowCheck19783]

def rawRow19784 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 24), (key1606, 24), (key1636, 24)]

theorem rawRowCheck19784 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form3 = rawRow19784 := by decide +kernel

def row19784 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19784 : row19784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19784 := by decide +kernel

theorem rowEval19784 (x : Key → ℝ) : Integer.Sparse.eval row19784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19784, Integer.Sparse.eval_collectBalanced, rawRowCheck19784]

def rawRow19785 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 24), (key1636, 24), (key1606, 24)]

theorem rawRowCheck19785 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form3 = rawRow19785 := by decide +kernel

def row19785 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19785 : row19785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19785 := by decide +kernel

theorem rowEval19785 (x : Key → ℝ) : Integer.Sparse.eval row19785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19785, Integer.Sparse.eval_collectBalanced, rawRowCheck19785]

def rawRow19786 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1636, 24), (key1606, 24), (key1606, 24)]

theorem rawRowCheck19786 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form3 = rawRow19786 := by decide +kernel

def row19786 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19786 : row19786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19786 := by decide +kernel

theorem rowEval19786 (x : Key → ℝ) : Integer.Sparse.eval row19786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19786, Integer.Sparse.eval_collectBalanced, rawRowCheck19786]

def rawRow19787 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1528, 24), (key1606, 24), (key1636, 24)]

theorem rawRowCheck19787 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form3 = rawRow19787 := by decide +kernel

def row19787 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19787 : row19787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19787 := by decide +kernel

theorem rowEval19787 (x : Key → ℝ) : Integer.Sparse.eval row19787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19787, Integer.Sparse.eval_collectBalanced, rawRowCheck19787]

def rawRow19788 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1528, 24), (key1636, 24), (key1606, 24)]

theorem rawRowCheck19788 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form3 = rawRow19788 := by decide +kernel

def row19788 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19788 : row19788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19788 := by decide +kernel

theorem rowEval19788 (x : Key → ℝ) : Integer.Sparse.eval row19788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19788, Integer.Sparse.eval_collectBalanced, rawRowCheck19788]

def rawRow19789 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1606, 24), (key1528, 24), (key1636, 24)]

theorem rawRowCheck19789 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form3 = rawRow19789 := by decide +kernel

def row19789 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19789 : row19789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19789 := by decide +kernel

theorem rowEval19789 (x : Key → ℝ) : Integer.Sparse.eval row19789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19789, Integer.Sparse.eval_collectBalanced, rawRowCheck19789]

def rawRow19790 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1606, 24), (key1636, 24), (key1528, 24)]

theorem rawRowCheck19790 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form3 = rawRow19790 := by decide +kernel

def row19790 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19790 : row19790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19790 := by decide +kernel

theorem rowEval19790 (x : Key → ℝ) : Integer.Sparse.eval row19790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19790, Integer.Sparse.eval_collectBalanced, rawRowCheck19790]

def rawRow19791 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1636, 24), (key1528, 24), (key1606, 24)]

theorem rawRowCheck19791 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form3 = rawRow19791 := by decide +kernel

def row19791 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19791 : row19791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19791 := by decide +kernel

theorem rowEval19791 (x : Key → ℝ) : Integer.Sparse.eval row19791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19791, Integer.Sparse.eval_collectBalanced, rawRowCheck19791]

def rawRow19792 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1636, 24), (key1606, 24), (key1528, 24)]

theorem rawRowCheck19792 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form3 = rawRow19792 := by decide +kernel

def row19792 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19792 : row19792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19792 := by decide +kernel

theorem rowEval19792 (x : Key → ℝ) : Integer.Sparse.eval row19792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19792, Integer.Sparse.eval_collectBalanced, rawRowCheck19792]

def rawRow19793 : Integer.Sparse Key := [(key1253, 24), (key1636, 24), (key1528, 24), (key1606, 24), (key1606, 24)]

theorem rawRowCheck19793 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form3 = rawRow19793 := by decide +kernel

def row19793 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19793 : row19793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19793 := by decide +kernel

theorem rowEval19793 (x : Key → ℝ) : Integer.Sparse.eval row19793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19793, Integer.Sparse.eval_collectBalanced, rawRowCheck19793]

def rawRow19794 : Integer.Sparse Key := [(key1253, 24), (key1636, 24), (key1606, 24), (key1528, 24), (key1606, 24)]

theorem rawRowCheck19794 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form3 = rawRow19794 := by decide +kernel

def row19794 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19794 : row19794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19794 := by decide +kernel

theorem rowEval19794 (x : Key → ℝ) : Integer.Sparse.eval row19794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19794, Integer.Sparse.eval_collectBalanced, rawRowCheck19794]

def rawRow19795 : Integer.Sparse Key := [(key1253, 24), (key1636, 24), (key1606, 24), (key1606, 24), (key1528, 24)]

theorem rawRowCheck19795 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form3 = rawRow19795 := by decide +kernel

def row19795 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19795 : row19795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19795 := by decide +kernel

theorem rowEval19795 (x : Key → ℝ) : Integer.Sparse.eval row19795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19795, Integer.Sparse.eval_collectBalanced, rawRowCheck19795]

def rawRow19796 : Integer.Sparse Key := [(key1528, 24), (key1253, 24), (key1606, 24), (key1606, 24), (key1636, 24)]

theorem rawRowCheck19796 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form3 = rawRow19796 := by decide +kernel

def row19796 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19796 : row19796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19796 := by decide +kernel

theorem rowEval19796 (x : Key → ℝ) : Integer.Sparse.eval row19796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19796, Integer.Sparse.eval_collectBalanced, rawRowCheck19796]

def rawRow19797 : Integer.Sparse Key := [(key1528, 24), (key1253, 24), (key1606, 24), (key1636, 24), (key1606, 24)]

theorem rawRowCheck19797 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form3 = rawRow19797 := by decide +kernel

def row19797 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19797 : row19797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19797 := by decide +kernel

theorem rowEval19797 (x : Key → ℝ) : Integer.Sparse.eval row19797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19797, Integer.Sparse.eval_collectBalanced, rawRowCheck19797]

def rawRow19798 : Integer.Sparse Key := [(key1528, 24), (key1253, 24), (key1636, 24), (key1606, 24), (key1606, 24)]

theorem rawRowCheck19798 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form3 = rawRow19798 := by decide +kernel

def row19798 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19798 : row19798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19798 := by decide +kernel

theorem rowEval19798 (x : Key → ℝ) : Integer.Sparse.eval row19798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19798, Integer.Sparse.eval_collectBalanced, rawRowCheck19798]

def rawRow19799 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1253, 24), (key1606, 24), (key1636, 24)]

theorem rawRowCheck19799 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form3 = rawRow19799 := by decide +kernel

def row19799 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19799 : row19799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19799 := by decide +kernel

theorem rowEval19799 (x : Key → ℝ) : Integer.Sparse.eval row19799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19799, Integer.Sparse.eval_collectBalanced, rawRowCheck19799]

def rawRow19800 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1253, 24), (key1636, 24), (key1606, 24)]

theorem rawRowCheck19800 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form3 = rawRow19800 := by decide +kernel

def row19800 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19800 : row19800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19800 := by decide +kernel

theorem rowEval19800 (x : Key → ℝ) : Integer.Sparse.eval row19800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19800, Integer.Sparse.eval_collectBalanced, rawRowCheck19800]

def rawRow19801 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1606, 24), (key1253, 24), (key1636, 24)]

theorem rawRowCheck19801 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form3 = rawRow19801 := by decide +kernel

def row19801 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19801 : row19801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19801 := by decide +kernel

theorem rowEval19801 (x : Key → ℝ) : Integer.Sparse.eval row19801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19801, Integer.Sparse.eval_collectBalanced, rawRowCheck19801]

def rawRow19802 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1606, 24), (key1636, 24), (key1253, 24)]

theorem rawRowCheck19802 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form3 = rawRow19802 := by decide +kernel

def row19802 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19802 : row19802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19802 := by decide +kernel

theorem rowEval19802 (x : Key → ℝ) : Integer.Sparse.eval row19802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19802, Integer.Sparse.eval_collectBalanced, rawRowCheck19802]

def rawRow19803 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1636, 24), (key1253, 24), (key1606, 24)]

theorem rawRowCheck19803 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form3 = rawRow19803 := by decide +kernel

def row19803 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19803 : row19803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19803 := by decide +kernel

theorem rowEval19803 (x : Key → ℝ) : Integer.Sparse.eval row19803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19803, Integer.Sparse.eval_collectBalanced, rawRowCheck19803]

def rawRow19804 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1636, 24), (key1606, 24), (key1253, 24)]

theorem rawRowCheck19804 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form3 = rawRow19804 := by decide +kernel

def row19804 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19804 : row19804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19804 := by decide +kernel

theorem rowEval19804 (x : Key → ℝ) : Integer.Sparse.eval row19804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19804, Integer.Sparse.eval_collectBalanced, rawRowCheck19804]

def rawRow19805 : Integer.Sparse Key := [(key1528, 24), (key1636, 24), (key1253, 24), (key1606, 24), (key1606, 24)]

theorem rawRowCheck19805 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form3 = rawRow19805 := by decide +kernel

def row19805 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19805 : row19805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19805 := by decide +kernel

theorem rowEval19805 (x : Key → ℝ) : Integer.Sparse.eval row19805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19805, Integer.Sparse.eval_collectBalanced, rawRowCheck19805]

def rawRow19806 : Integer.Sparse Key := [(key1528, 24), (key1636, 24), (key1606, 24), (key1253, 24), (key1606, 24)]

theorem rawRowCheck19806 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form3 = rawRow19806 := by decide +kernel

def row19806 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19806 : row19806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19806 := by decide +kernel

theorem rowEval19806 (x : Key → ℝ) : Integer.Sparse.eval row19806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19806, Integer.Sparse.eval_collectBalanced, rawRowCheck19806]

def rawRow19807 : Integer.Sparse Key := [(key1528, 24), (key1636, 24), (key1606, 24), (key1606, 24), (key1253, 24)]

theorem rawRowCheck19807 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form3 = rawRow19807 := by decide +kernel

def row19807 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19807 : row19807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19807 := by decide +kernel

theorem rowEval19807 (x : Key → ℝ) : Integer.Sparse.eval row19807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19807, Integer.Sparse.eval_collectBalanced, rawRowCheck19807]

def rawRow19808 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1528, 24), (key1606, 24), (key1636, 24)]

theorem rawRowCheck19808 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form3 = rawRow19808 := by decide +kernel

def row19808 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19808 : row19808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19808 := by decide +kernel

theorem rowEval19808 (x : Key → ℝ) : Integer.Sparse.eval row19808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19808, Integer.Sparse.eval_collectBalanced, rawRowCheck19808]

def rawRow19809 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1528, 24), (key1636, 24), (key1606, 24)]

theorem rawRowCheck19809 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form3 = rawRow19809 := by decide +kernel

def row19809 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19809 : row19809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19809 := by decide +kernel

theorem rowEval19809 (x : Key → ℝ) : Integer.Sparse.eval row19809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19809, Integer.Sparse.eval_collectBalanced, rawRowCheck19809]

def rawRow19810 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1606, 24), (key1528, 24), (key1636, 24)]

theorem rawRowCheck19810 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form3 = rawRow19810 := by decide +kernel

def row19810 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19810 : row19810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19810 := by decide +kernel

theorem rowEval19810 (x : Key → ℝ) : Integer.Sparse.eval row19810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19810, Integer.Sparse.eval_collectBalanced, rawRowCheck19810]

def rawRow19811 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1606, 24), (key1636, 24), (key1528, 24)]

theorem rawRowCheck19811 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form3 = rawRow19811 := by decide +kernel

def row19811 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19811 : row19811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19811 := by decide +kernel

theorem rowEval19811 (x : Key → ℝ) : Integer.Sparse.eval row19811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19811, Integer.Sparse.eval_collectBalanced, rawRowCheck19811]

def rawRow19812 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1636, 24), (key1528, 24), (key1606, 24)]

theorem rawRowCheck19812 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form3 = rawRow19812 := by decide +kernel

def row19812 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19812 : row19812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19812 := by decide +kernel

theorem rowEval19812 (x : Key → ℝ) : Integer.Sparse.eval row19812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19812, Integer.Sparse.eval_collectBalanced, rawRowCheck19812]

def rawRow19813 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1636, 24), (key1606, 24), (key1528, 24)]

theorem rawRowCheck19813 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form3 = rawRow19813 := by decide +kernel

def row19813 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19813 : row19813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19813 := by decide +kernel

theorem rowEval19813 (x : Key → ℝ) : Integer.Sparse.eval row19813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19813, Integer.Sparse.eval_collectBalanced, rawRowCheck19813]

def rawRow19814 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1253, 24), (key1606, 24), (key1636, 24)]

theorem rawRowCheck19814 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form3 = rawRow19814 := by decide +kernel

def row19814 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19814 : row19814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19814 := by decide +kernel

theorem rowEval19814 (x : Key → ℝ) : Integer.Sparse.eval row19814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19814, Integer.Sparse.eval_collectBalanced, rawRowCheck19814]

def rawRow19815 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1253, 24), (key1636, 24), (key1606, 24)]

theorem rawRowCheck19815 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form3 = rawRow19815 := by decide +kernel

def row19815 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19815 : row19815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19815 := by decide +kernel

theorem rowEval19815 (x : Key → ℝ) : Integer.Sparse.eval row19815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19815, Integer.Sparse.eval_collectBalanced, rawRowCheck19815]

def rawRow19816 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1606, 24), (key1253, 24), (key1636, 24)]

theorem rawRowCheck19816 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form3 = rawRow19816 := by decide +kernel

def row19816 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19816 : row19816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19816 := by decide +kernel

theorem rowEval19816 (x : Key → ℝ) : Integer.Sparse.eval row19816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19816, Integer.Sparse.eval_collectBalanced, rawRowCheck19816]

def rawRow19817 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1606, 24), (key1636, 24), (key1253, 24)]

theorem rawRowCheck19817 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form3 = rawRow19817 := by decide +kernel

def row19817 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19817 : row19817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19817 := by decide +kernel

theorem rowEval19817 (x : Key → ℝ) : Integer.Sparse.eval row19817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19817, Integer.Sparse.eval_collectBalanced, rawRowCheck19817]

def rawRow19818 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1636, 24), (key1253, 24), (key1606, 24)]

theorem rawRowCheck19818 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form3 = rawRow19818 := by decide +kernel

def row19818 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19818 : row19818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19818 := by decide +kernel

theorem rowEval19818 (x : Key → ℝ) : Integer.Sparse.eval row19818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19818, Integer.Sparse.eval_collectBalanced, rawRowCheck19818]

def rawRow19819 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1636, 24), (key1606, 24), (key1253, 24)]

theorem rawRowCheck19819 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form3 = rawRow19819 := by decide +kernel

def row19819 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19819 : row19819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19819 := by decide +kernel

theorem rowEval19819 (x : Key → ℝ) : Integer.Sparse.eval row19819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19819, Integer.Sparse.eval_collectBalanced, rawRowCheck19819]

def rawRow19820 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1253, 24), (key1528, 24), (key1636, 24)]

theorem rawRowCheck19820 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form3 = rawRow19820 := by decide +kernel

def row19820 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19820 : row19820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19820 := by decide +kernel

theorem rowEval19820 (x : Key → ℝ) : Integer.Sparse.eval row19820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19820, Integer.Sparse.eval_collectBalanced, rawRowCheck19820]

def rawRow19821 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1253, 24), (key1636, 24), (key1528, 24)]

theorem rawRowCheck19821 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form3 = rawRow19821 := by decide +kernel

def row19821 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19821 : row19821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19821 := by decide +kernel

theorem rowEval19821 (x : Key → ℝ) : Integer.Sparse.eval row19821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19821, Integer.Sparse.eval_collectBalanced, rawRowCheck19821]

def rawRow19822 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1528, 24), (key1253, 24), (key1636, 24)]

theorem rawRowCheck19822 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form3 = rawRow19822 := by decide +kernel

def row19822 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19822 : row19822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19822 := by decide +kernel

theorem rowEval19822 (x : Key → ℝ) : Integer.Sparse.eval row19822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19822, Integer.Sparse.eval_collectBalanced, rawRowCheck19822]

def rawRow19823 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1528, 24), (key1636, 24), (key1253, 24)]

theorem rawRowCheck19823 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form3 = rawRow19823 := by decide +kernel

def row19823 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19823 : row19823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19823 := by decide +kernel

theorem rowEval19823 (x : Key → ℝ) : Integer.Sparse.eval row19823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19823, Integer.Sparse.eval_collectBalanced, rawRowCheck19823]

def rawRow19824 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1636, 24), (key1253, 24), (key1528, 24)]

theorem rawRowCheck19824 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form3 = rawRow19824 := by decide +kernel

def row19824 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19824 : row19824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19824 := by decide +kernel

theorem rowEval19824 (x : Key → ℝ) : Integer.Sparse.eval row19824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19824, Integer.Sparse.eval_collectBalanced, rawRowCheck19824]

def rawRow19825 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1636, 24), (key1528, 24), (key1253, 24)]

theorem rawRowCheck19825 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form3 = rawRow19825 := by decide +kernel

def row19825 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19825 : row19825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19825 := by decide +kernel

theorem rowEval19825 (x : Key → ℝ) : Integer.Sparse.eval row19825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19825, Integer.Sparse.eval_collectBalanced, rawRowCheck19825]

def rawRow19826 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1253, 24), (key1528, 24), (key1606, 24)]

theorem rawRowCheck19826 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form3 = rawRow19826 := by decide +kernel

def row19826 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19826 : row19826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19826 := by decide +kernel

theorem rowEval19826 (x : Key → ℝ) : Integer.Sparse.eval row19826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19826, Integer.Sparse.eval_collectBalanced, rawRowCheck19826]

def rawRow19827 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1253, 24), (key1606, 24), (key1528, 24)]

theorem rawRowCheck19827 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form3 = rawRow19827 := by decide +kernel

def row19827 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19827 : row19827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19827 := by decide +kernel

theorem rowEval19827 (x : Key → ℝ) : Integer.Sparse.eval row19827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19827, Integer.Sparse.eval_collectBalanced, rawRowCheck19827]

def rawRow19828 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1528, 24), (key1253, 24), (key1606, 24)]

theorem rawRowCheck19828 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form3 = rawRow19828 := by decide +kernel

def row19828 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19828 : row19828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19828 := by decide +kernel

theorem rowEval19828 (x : Key → ℝ) : Integer.Sparse.eval row19828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19828, Integer.Sparse.eval_collectBalanced, rawRowCheck19828]

def rawRow19829 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1528, 24), (key1606, 24), (key1253, 24)]

theorem rawRowCheck19829 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form3 = rawRow19829 := by decide +kernel

def row19829 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19829 : row19829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19829 := by decide +kernel

theorem rowEval19829 (x : Key → ℝ) : Integer.Sparse.eval row19829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19829, Integer.Sparse.eval_collectBalanced, rawRowCheck19829]

def rawRow19830 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1606, 24), (key1253, 24), (key1528, 24)]

theorem rawRowCheck19830 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form3 = rawRow19830 := by decide +kernel

def row19830 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19830 : row19830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19830 := by decide +kernel

theorem rowEval19830 (x : Key → ℝ) : Integer.Sparse.eval row19830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19830, Integer.Sparse.eval_collectBalanced, rawRowCheck19830]

def rawRow19831 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1606, 24), (key1528, 24), (key1253, 24)]

theorem rawRowCheck19831 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form3 = rawRow19831 := by decide +kernel

def row19831 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19831 : row19831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19831 := by decide +kernel

theorem rowEval19831 (x : Key → ℝ) : Integer.Sparse.eval row19831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19831, Integer.Sparse.eval_collectBalanced, rawRowCheck19831]

def rawRow19832 : Integer.Sparse Key := [(key1636, 24), (key1253, 24), (key1528, 24), (key1606, 24), (key1606, 24)]

theorem rawRowCheck19832 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form3 = rawRow19832 := by decide +kernel

def row19832 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19832 : row19832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19832 := by decide +kernel

theorem rowEval19832 (x : Key → ℝ) : Integer.Sparse.eval row19832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19832, Integer.Sparse.eval_collectBalanced, rawRowCheck19832]

def rawRow19833 : Integer.Sparse Key := [(key1636, 24), (key1253, 24), (key1606, 24), (key1528, 24), (key1606, 24)]

theorem rawRowCheck19833 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form3 = rawRow19833 := by decide +kernel

def row19833 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19833 : row19833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19833 := by decide +kernel

theorem rowEval19833 (x : Key → ℝ) : Integer.Sparse.eval row19833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19833, Integer.Sparse.eval_collectBalanced, rawRowCheck19833]

def rawRow19834 : Integer.Sparse Key := [(key1636, 24), (key1253, 24), (key1606, 24), (key1606, 24), (key1528, 24)]

theorem rawRowCheck19834 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form3 = rawRow19834 := by decide +kernel

def row19834 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19834 : row19834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19834 := by decide +kernel

theorem rowEval19834 (x : Key → ℝ) : Integer.Sparse.eval row19834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19834, Integer.Sparse.eval_collectBalanced, rawRowCheck19834]

def rawRow19835 : Integer.Sparse Key := [(key1636, 24), (key1528, 24), (key1253, 24), (key1606, 24), (key1606, 24)]

theorem rawRowCheck19835 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form3 = rawRow19835 := by decide +kernel

def row19835 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19835 : row19835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19835 := by decide +kernel

theorem rowEval19835 (x : Key → ℝ) : Integer.Sparse.eval row19835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19835, Integer.Sparse.eval_collectBalanced, rawRowCheck19835]

def rawRow19836 : Integer.Sparse Key := [(key1636, 24), (key1528, 24), (key1606, 24), (key1253, 24), (key1606, 24)]

theorem rawRowCheck19836 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form3 = rawRow19836 := by decide +kernel

def row19836 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19836 : row19836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19836 := by decide +kernel

theorem rowEval19836 (x : Key → ℝ) : Integer.Sparse.eval row19836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19836, Integer.Sparse.eval_collectBalanced, rawRowCheck19836]

def rawRow19837 : Integer.Sparse Key := [(key1636, 24), (key1528, 24), (key1606, 24), (key1606, 24), (key1253, 24)]

theorem rawRowCheck19837 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form3 = rawRow19837 := by decide +kernel

def row19837 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19837 : row19837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19837 := by decide +kernel

theorem rowEval19837 (x : Key → ℝ) : Integer.Sparse.eval row19837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19837, Integer.Sparse.eval_collectBalanced, rawRowCheck19837]

def rawRow19838 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1253, 24), (key1528, 24), (key1606, 24)]

theorem rawRowCheck19838 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form3 = rawRow19838 := by decide +kernel

def row19838 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19838 : row19838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19838 := by decide +kernel

theorem rowEval19838 (x : Key → ℝ) : Integer.Sparse.eval row19838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19838, Integer.Sparse.eval_collectBalanced, rawRowCheck19838]

def rawRow19839 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1253, 24), (key1606, 24), (key1528, 24)]

theorem rawRowCheck19839 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form3 = rawRow19839 := by decide +kernel

def row19839 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19839 : row19839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19839 := by decide +kernel

theorem rowEval19839 (x : Key → ℝ) : Integer.Sparse.eval row19839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19839, Integer.Sparse.eval_collectBalanced, rawRowCheck19839]

end MUB6.Certificate.GramRows

end OAI
