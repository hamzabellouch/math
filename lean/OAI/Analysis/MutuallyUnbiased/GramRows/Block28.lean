import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow992 : Integer.Sparse Key := [(key1690, -2), (key1927, -2), (key1634, -2), (key1690, 1), (key1927, 1), (key1481, 1), (key1912, 1), (key1445, 1), (key1594, 1), (key1684, 2), (key1921, 2), (key1625, 2), (key1684, -1), (key1921, -1), (key1355, -1), (key1900, -1), (key1327, -1), (key1557, -1), (key1682, -1), (key1919, -1), (key1473, -1), (key1904, -1), (key1427, -1), (key1576, -1), (key1682, 1), (key1919, 1), (key1352, 1), (key1897, 1), (key1319, 1), (key1549, 1)]

theorem rawRowCheck992 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form2 = rawRow992 := by decide +kernel

def row992 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck992 : row992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow992 := by decide +kernel

theorem rowEval992 (x : Key → ℝ) : Integer.Sparse.eval row992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck992, Integer.Sparse.eval_collectBalanced, rawRowCheck992]

def rawRow993 : Integer.Sparse Key := [(key1927, -2), (key1690, -2), (key1634, -2), (key1927, 1), (key1690, 1), (key1912, 1), (key1481, 1), (key1594, 1), (key1445, 1), (key1921, 2), (key1684, 2), (key1625, 2), (key1921, -1), (key1684, -1), (key1900, -1), (key1355, -1), (key1557, -1), (key1327, -1), (key1919, -1), (key1682, -1), (key1904, -1), (key1473, -1), (key1576, -1), (key1427, -1), (key1919, 1), (key1682, 1), (key1897, 1), (key1352, 1), (key1549, 1), (key1319, 1)]

theorem rawRowCheck993 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form2 = rawRow993 := by decide +kernel

def row993 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck993 : row993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow993 := by decide +kernel

theorem rowEval993 (x : Key → ℝ) : Integer.Sparse.eval row993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck993, Integer.Sparse.eval_collectBalanced, rawRowCheck993]

def rawRow994 : Integer.Sparse Key := [(key43, -2), (key48, -2), (key74, -2), (key48, 6), (key426, 2), (key432, 2), (key659, 2), (key212, -2), (key432, -2), (key460, -2), (key486, -6), (key218, 2), (key486, 2), (key490, 2)]

theorem rawRowCheck994 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form3 = rawRow994 := by decide +kernel

def row994 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

theorem rowCheck994 : row994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow994 := by decide +kernel

theorem rowEval994 (x : Key → ℝ) : Integer.Sparse.eval row994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck994, Integer.Sparse.eval_collectBalanced, rawRowCheck994]

def rawRow995 : Integer.Sparse Key := [(key48, -2), (key43, -2), (key74, -2), (key48, 6), (key432, 2), (key426, 2), (key659, 2), (key212, -2), (key460, -2), (key432, -2), (key486, -6), (key218, 2), (key490, 2), (key486, 2)]

theorem rawRowCheck995 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form3 = rawRow995 := by decide +kernel

def row995 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

theorem rowCheck995 : row995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow995 := by decide +kernel

theorem rowEval995 (x : Key → ℝ) : Integer.Sparse.eval row995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck995, Integer.Sparse.eval_collectBalanced, rawRowCheck995]

def rawRow996 : Integer.Sparse Key := [(key43, -2), (key74, -2), (key48, -2), (key48, 6), (key426, 2), (key659, 2), (key432, 2), (key432, -2), (key212, -2), (key460, -2), (key486, -6), (key486, 2), (key218, 2), (key490, 2)]

theorem rawRowCheck996 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form3 = rawRow996 := by decide +kernel

def row996 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

theorem rowCheck996 : row996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow996 := by decide +kernel

theorem rowEval996 (x : Key → ℝ) : Integer.Sparse.eval row996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck996, Integer.Sparse.eval_collectBalanced, rawRowCheck996]

def rawRow997 : Integer.Sparse Key := [(key74, -2), (key43, -2), (key48, -2), (key48, 6), (key659, 2), (key426, 2), (key432, 2), (key432, -2), (key460, -2), (key212, -2), (key486, -6), (key486, 2), (key490, 2), (key218, 2)]

theorem rawRowCheck997 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form3 = rawRow997 := by decide +kernel

def row997 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

theorem rowCheck997 : row997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow997 := by decide +kernel

theorem rowEval997 (x : Key → ℝ) : Integer.Sparse.eval row997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck997, Integer.Sparse.eval_collectBalanced, rawRowCheck997]

def rawRow998 : Integer.Sparse Key := [(key48, -2), (key74, -2), (key43, -2), (key48, 6), (key432, 2), (key659, 2), (key426, 2), (key460, -2), (key212, -2), (key432, -2), (key486, -6), (key490, 2), (key218, 2), (key486, 2)]

theorem rawRowCheck998 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form3 = rawRow998 := by decide +kernel

def row998 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

theorem rowCheck998 : row998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow998 := by decide +kernel

theorem rowEval998 (x : Key → ℝ) : Integer.Sparse.eval row998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck998, Integer.Sparse.eval_collectBalanced, rawRowCheck998]

def rawRow999 : Integer.Sparse Key := [(key74, -2), (key48, -2), (key43, -2), (key48, 6), (key659, 2), (key432, 2), (key426, 2), (key460, -2), (key432, -2), (key212, -2), (key486, -6), (key490, 2), (key486, 2), (key218, 2)]

theorem rawRowCheck999 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form3 = rawRow999 := by decide +kernel

def row999 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

theorem rowCheck999 : row999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow999 := by decide +kernel

theorem rowEval999 (x : Key → ℝ) : Integer.Sparse.eval row999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck999, Integer.Sparse.eval_collectBalanced, rawRowCheck999]

def rawRow1000 : Integer.Sparse Key := [(key48, -2), (key48, -2), (key74, -2), (key43, 6), (key460, 2), (key460, 2), (key663, 2), (key206, -2), (key426, -2), (key426, -2), (key490, -6), (key218, 2), (key486, 2), (key486, 2)]

theorem rawRowCheck1000 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form3 = rawRow1000 := by decide +kernel

def row1000 : Integer.Sparse Key := [(key43, 6), (key48, -4), (key74, -2), (key206, -2), (key218, 2), (key426, -4), (key460, 4), (key486, 4), (key490, -6), (key663, 2)]

theorem rowCheck1000 : row1000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1000 := by decide +kernel

theorem rowEval1000 (x : Key → ℝ) : Integer.Sparse.eval row1000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1000, Integer.Sparse.eval_collectBalanced, rawRowCheck1000]

def rawRow1001 : Integer.Sparse Key := [(key48, -2), (key74, -2), (key48, -2), (key43, 6), (key460, 2), (key663, 2), (key460, 2), (key426, -2), (key206, -2), (key426, -2), (key490, -6), (key486, 2), (key218, 2), (key486, 2)]

theorem rawRowCheck1001 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form3 = rawRow1001 := by decide +kernel

def row1001 : Integer.Sparse Key := [(key43, 6), (key48, -4), (key74, -2), (key206, -2), (key218, 2), (key426, -4), (key460, 4), (key486, 4), (key490, -6), (key663, 2)]

theorem rowCheck1001 : row1001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1001 := by decide +kernel

theorem rowEval1001 (x : Key → ℝ) : Integer.Sparse.eval row1001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1001, Integer.Sparse.eval_collectBalanced, rawRowCheck1001]

def rawRow1002 : Integer.Sparse Key := [(key74, -2), (key48, -2), (key48, -2), (key43, 6), (key663, 2), (key460, 2), (key460, 2), (key426, -2), (key426, -2), (key206, -2), (key490, -6), (key486, 2), (key486, 2), (key218, 2)]

theorem rawRowCheck1002 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form3 = rawRow1002 := by decide +kernel

def row1002 : Integer.Sparse Key := [(key43, 6), (key48, -4), (key74, -2), (key206, -2), (key218, 2), (key426, -4), (key460, 4), (key486, 4), (key490, -6), (key663, 2)]

theorem rowCheck1002 : row1002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1002 := by decide +kernel

theorem rowEval1002 (x : Key → ℝ) : Integer.Sparse.eval row1002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1002, Integer.Sparse.eval_collectBalanced, rawRowCheck1002]

def rawRow1003 : Integer.Sparse Key := [(key100, -2), (key105, -2), (key137, -2), (key115, 6), (key43, 2), (key48, 2), (key74, 2), (key218, -2), (key486, -2), (key490, -2), (key381, -6), (key212, 2), (key432, 2), (key460, 2)]

theorem rawRowCheck1003 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form3 = rawRow1003 := by decide +kernel

def row1003 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

theorem rowCheck1003 : row1003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1003 := by decide +kernel

theorem rowEval1003 (x : Key → ℝ) : Integer.Sparse.eval row1003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1003, Integer.Sparse.eval_collectBalanced, rawRowCheck1003]

def rawRow1004 : Integer.Sparse Key := [(key105, -2), (key100, -2), (key137, -2), (key115, 6), (key48, 2), (key43, 2), (key74, 2), (key218, -2), (key490, -2), (key486, -2), (key381, -6), (key212, 2), (key460, 2), (key432, 2)]

theorem rawRowCheck1004 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form3 = rawRow1004 := by decide +kernel

def row1004 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

theorem rowCheck1004 : row1004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1004 := by decide +kernel

theorem rowEval1004 (x : Key → ℝ) : Integer.Sparse.eval row1004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1004, Integer.Sparse.eval_collectBalanced, rawRowCheck1004]

def rawRow1005 : Integer.Sparse Key := [(key100, -2), (key137, -2), (key105, -2), (key115, 6), (key43, 2), (key74, 2), (key48, 2), (key486, -2), (key218, -2), (key490, -2), (key381, -6), (key432, 2), (key212, 2), (key460, 2)]

theorem rawRowCheck1005 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form3 = rawRow1005 := by decide +kernel

def row1005 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

theorem rowCheck1005 : row1005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1005 := by decide +kernel

theorem rowEval1005 (x : Key → ℝ) : Integer.Sparse.eval row1005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1005, Integer.Sparse.eval_collectBalanced, rawRowCheck1005]

def rawRow1006 : Integer.Sparse Key := [(key137, -2), (key100, -2), (key105, -2), (key115, 6), (key74, 2), (key43, 2), (key48, 2), (key486, -2), (key490, -2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key212, 2)]

theorem rawRowCheck1006 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form3 = rawRow1006 := by decide +kernel

def row1006 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

theorem rowCheck1006 : row1006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1006 := by decide +kernel

theorem rowEval1006 (x : Key → ℝ) : Integer.Sparse.eval row1006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1006, Integer.Sparse.eval_collectBalanced, rawRowCheck1006]

def rawRow1007 : Integer.Sparse Key := [(key105, -2), (key137, -2), (key100, -2), (key115, 6), (key48, 2), (key74, 2), (key43, 2), (key490, -2), (key218, -2), (key486, -2), (key381, -6), (key460, 2), (key212, 2), (key432, 2)]

theorem rawRowCheck1007 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form3 = rawRow1007 := by decide +kernel

def row1007 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

theorem rowCheck1007 : row1007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1007 := by decide +kernel

theorem rowEval1007 (x : Key → ℝ) : Integer.Sparse.eval row1007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1007, Integer.Sparse.eval_collectBalanced, rawRowCheck1007]

def rawRow1008 : Integer.Sparse Key := [(key137, -2), (key105, -2), (key100, -2), (key115, 6), (key74, 2), (key48, 2), (key43, 2), (key490, -2), (key486, -2), (key218, -2), (key381, -6), (key460, 2), (key432, 2), (key212, 2)]

theorem rawRowCheck1008 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form3 = rawRow1008 := by decide +kernel

def row1008 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

theorem rowCheck1008 : row1008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1008 := by decide +kernel

theorem rowEval1008 (x : Key → ℝ) : Integer.Sparse.eval row1008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1008, Integer.Sparse.eval_collectBalanced, rawRowCheck1008]

def rawRow1009 : Integer.Sparse Key := [(key105, -2), (key115, -2), (key137, -2), (key100, 6), (key195, 2), (key196, 2), (key200, 2), (key18, -2), (key375, -2), (key426, -2), (key460, -6), (key212, 2), (key381, 2), (key432, 2)]

theorem rawRowCheck1009 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form3 = rawRow1009 := by decide +kernel

def row1009 : Integer.Sparse Key := [(key18, -2), (key100, 6), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key212, 2), (key375, -2), (key381, 2), (key426, -2), (key432, 2), (key460, -6)]

theorem rowCheck1009 : row1009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1009 := by decide +kernel

theorem rowEval1009 (x : Key → ℝ) : Integer.Sparse.eval row1009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1009, Integer.Sparse.eval_collectBalanced, rawRowCheck1009]

def rawRow1010 : Integer.Sparse Key := [(key115, -2), (key105, -2), (key137, -2), (key100, 6), (key196, 2), (key195, 2), (key200, 2), (key18, -2), (key426, -2), (key375, -2), (key460, -6), (key212, 2), (key432, 2), (key381, 2)]

theorem rawRowCheck1010 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form3 = rawRow1010 := by decide +kernel

def row1010 : Integer.Sparse Key := [(key18, -2), (key100, 6), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key212, 2), (key375, -2), (key381, 2), (key426, -2), (key432, 2), (key460, -6)]

theorem rowCheck1010 : row1010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1010 := by decide +kernel

theorem rowEval1010 (x : Key → ℝ) : Integer.Sparse.eval row1010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1010, Integer.Sparse.eval_collectBalanced, rawRowCheck1010]

def rawRow1011 : Integer.Sparse Key := [(key105, -2), (key137, -2), (key115, -2), (key100, 6), (key195, 2), (key200, 2), (key196, 2), (key43, -2), (key206, -2), (key426, -2), (key460, -6), (key381, 2), (key212, 2), (key432, 2)]

theorem rawRowCheck1011 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form3 = rawRow1011 := by decide +kernel

def row1011 : Integer.Sparse Key := [(key43, -2), (key100, 6), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key206, -2), (key212, 2), (key381, 2), (key426, -2), (key432, 2), (key460, -6)]

theorem rowCheck1011 : row1011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1011 := by decide +kernel

theorem rowEval1011 (x : Key → ℝ) : Integer.Sparse.eval row1011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1011, Integer.Sparse.eval_collectBalanced, rawRowCheck1011]

def rawRow1012 : Integer.Sparse Key := [(key137, -2), (key105, -2), (key115, -2), (key100, 6), (key200, 2), (key195, 2), (key196, 2), (key43, -2), (key426, -2), (key206, -2), (key460, -6), (key381, 2), (key432, 2), (key212, 2)]

theorem rawRowCheck1012 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form3 = rawRow1012 := by decide +kernel

def row1012 : Integer.Sparse Key := [(key43, -2), (key100, 6), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key206, -2), (key212, 2), (key381, 2), (key426, -2), (key432, 2), (key460, -6)]

theorem rowCheck1012 : row1012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1012 := by decide +kernel

theorem rowEval1012 (x : Key → ℝ) : Integer.Sparse.eval row1012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1012, Integer.Sparse.eval_collectBalanced, rawRowCheck1012]

def rawRow1013 : Integer.Sparse Key := [(key115, -2), (key137, -2), (key105, -2), (key100, 6), (key196, 2), (key200, 2), (key195, 2), (key100, -2), (key18, -2), (key375, -2), (key460, -6), (key432, 2), (key212, 2), (key381, 2)]

theorem rawRowCheck1013 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form3 = rawRow1013 := by decide +kernel

def row1013 : Integer.Sparse Key := [(key18, -2), (key100, 4), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key212, 2), (key375, -2), (key381, 2), (key432, 2), (key460, -6)]

theorem rowCheck1013 : row1013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1013 := by decide +kernel

theorem rowEval1013 (x : Key → ℝ) : Integer.Sparse.eval row1013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1013, Integer.Sparse.eval_collectBalanced, rawRowCheck1013]

def rawRow1014 : Integer.Sparse Key := [(key137, -2), (key115, -2), (key105, -2), (key100, 6), (key200, 2), (key196, 2), (key195, 2), (key100, -2), (key43, -2), (key206, -2), (key460, -6), (key432, 2), (key381, 2), (key212, 2)]

theorem rawRowCheck1014 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form3 = rawRow1014 := by decide +kernel

def row1014 : Integer.Sparse Key := [(key43, -2), (key100, 4), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key206, -2), (key212, 2), (key381, 2), (key432, 2), (key460, -6)]

theorem rowCheck1014 : row1014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1014 := by decide +kernel

theorem rowEval1014 (x : Key → ℝ) : Integer.Sparse.eval row1014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1014, Integer.Sparse.eval_collectBalanced, rawRowCheck1014]

def rawRow1015 : Integer.Sparse Key := [(key195, -2), (key195, -2), (key200, -2), (key196, 6), (key48, 2), (key48, 2), (key74, 2), (key35, -2), (key115, -2), (key115, -2), (key43, -6), (key206, 2), (key426, 2), (key426, 2)]

theorem rawRowCheck1015 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow1015 := by decide +kernel

def row1015 : Integer.Sparse Key := [(key35, -2), (key43, -6), (key48, 4), (key74, 2), (key115, -4), (key195, -4), (key196, 6), (key200, -2), (key206, 2), (key426, 4)]

theorem rowCheck1015 : row1015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1015 := by decide +kernel

theorem rowEval1015 (x : Key → ℝ) : Integer.Sparse.eval row1015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1015, Integer.Sparse.eval_collectBalanced, rawRowCheck1015]

def rawRow1016 : Integer.Sparse Key := [(key195, -2), (key200, -2), (key195, -2), (key196, 6), (key48, 2), (key74, 2), (key48, 2), (key115, -2), (key35, -2), (key115, -2), (key43, -6), (key426, 2), (key206, 2), (key426, 2)]

theorem rawRowCheck1016 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow1016 := by decide +kernel

def row1016 : Integer.Sparse Key := [(key35, -2), (key43, -6), (key48, 4), (key74, 2), (key115, -4), (key195, -4), (key196, 6), (key200, -2), (key206, 2), (key426, 4)]

theorem rowCheck1016 : row1016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1016 := by decide +kernel

theorem rowEval1016 (x : Key → ℝ) : Integer.Sparse.eval row1016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1016, Integer.Sparse.eval_collectBalanced, rawRowCheck1016]

def rawRow1017 : Integer.Sparse Key := [(key200, -2), (key195, -2), (key195, -2), (key196, 6), (key74, 2), (key48, 2), (key48, 2), (key115, -2), (key115, -2), (key35, -2), (key43, -6), (key426, 2), (key426, 2), (key206, 2)]

theorem rawRowCheck1017 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow1017 := by decide +kernel

def row1017 : Integer.Sparse Key := [(key35, -2), (key43, -6), (key48, 4), (key74, 2), (key115, -4), (key195, -4), (key196, 6), (key200, -2), (key206, 2), (key426, 4)]

theorem rowCheck1017 : row1017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1017 := by decide +kernel

theorem rowEval1017 (x : Key → ℝ) : Integer.Sparse.eval row1017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1017, Integer.Sparse.eval_collectBalanced, rawRowCheck1017]

def rawRow1018 : Integer.Sparse Key := [(key195, -2), (key196, -2), (key200, -2), (key195, 6), (key105, 2), (key115, 2), (key137, 2), (key23, -2), (key48, -2), (key105, -2), (key100, -6), (key18, 2), (key375, 2), (key426, 2)]

theorem rawRowCheck1018 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form3 = rawRow1018 := by decide +kernel

def row1018 : Integer.Sparse Key := [(key18, 2), (key23, -2), (key48, -2), (key100, -6), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key375, 2), (key426, 2)]

theorem rowCheck1018 : row1018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1018 := by decide +kernel

theorem rowEval1018 (x : Key → ℝ) : Integer.Sparse.eval row1018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1018, Integer.Sparse.eval_collectBalanced, rawRowCheck1018]

def rawRow1019 : Integer.Sparse Key := [(key196, -2), (key195, -2), (key200, -2), (key195, 6), (key115, 2), (key105, 2), (key137, 2), (key23, -2), (key105, -2), (key48, -2), (key100, -6), (key18, 2), (key426, 2), (key375, 2)]

theorem rawRowCheck1019 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form3 = rawRow1019 := by decide +kernel

def row1019 : Integer.Sparse Key := [(key18, 2), (key23, -2), (key48, -2), (key100, -6), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key375, 2), (key426, 2)]

theorem rowCheck1019 : row1019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1019 := by decide +kernel

theorem rowEval1019 (x : Key → ℝ) : Integer.Sparse.eval row1019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1019, Integer.Sparse.eval_collectBalanced, rawRowCheck1019]

def rawRow1020 : Integer.Sparse Key := [(key195, -2), (key200, -2), (key196, -2), (key195, 6), (key105, 2), (key137, 2), (key115, 2), (key48, -2), (key23, -2), (key105, -2), (key100, -6), (key43, 2), (key206, 2), (key426, 2)]

theorem rawRowCheck1020 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form3 = rawRow1020 := by decide +kernel

def row1020 : Integer.Sparse Key := [(key23, -2), (key43, 2), (key48, -2), (key100, -6), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key206, 2), (key426, 2)]

theorem rowCheck1020 : row1020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1020 := by decide +kernel

theorem rowEval1020 (x : Key → ℝ) : Integer.Sparse.eval row1020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1020, Integer.Sparse.eval_collectBalanced, rawRowCheck1020]

def rawRow1021 : Integer.Sparse Key := [(key200, -2), (key195, -2), (key196, -2), (key195, 6), (key137, 2), (key105, 2), (key115, 2), (key48, -2), (key105, -2), (key23, -2), (key100, -6), (key43, 2), (key426, 2), (key206, 2)]

theorem rawRowCheck1021 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form3 = rawRow1021 := by decide +kernel

def row1021 : Integer.Sparse Key := [(key23, -2), (key43, 2), (key48, -2), (key100, -6), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key206, 2), (key426, 2)]

theorem rowCheck1021 : row1021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1021 := by decide +kernel

theorem rowEval1021 (x : Key → ℝ) : Integer.Sparse.eval row1021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1021, Integer.Sparse.eval_collectBalanced, rawRowCheck1021]

def rawRow1022 : Integer.Sparse Key := [(key196, -2), (key200, -2), (key195, -2), (key195, 6), (key115, 2), (key137, 2), (key105, 2), (key105, -2), (key23, -2), (key48, -2), (key100, -6), (key100, 2), (key18, 2), (key375, 2)]

theorem rawRowCheck1022 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form3 = rawRow1022 := by decide +kernel

def row1022 : Integer.Sparse Key := [(key18, 2), (key23, -2), (key48, -2), (key100, -4), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key375, 2)]

theorem rowCheck1022 : row1022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1022 := by decide +kernel

theorem rowEval1022 (x : Key → ℝ) : Integer.Sparse.eval row1022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1022, Integer.Sparse.eval_collectBalanced, rawRowCheck1022]

def rawRow1023 : Integer.Sparse Key := [(key200, -2), (key196, -2), (key195, -2), (key195, 6), (key137, 2), (key115, 2), (key105, 2), (key105, -2), (key48, -2), (key23, -2), (key100, -6), (key100, 2), (key43, 2), (key206, 2)]

theorem rawRowCheck1023 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form3 = rawRow1023 := by decide +kernel

def row1023 : Integer.Sparse Key := [(key23, -2), (key43, 2), (key48, -2), (key100, -4), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key206, 2)]

theorem rowCheck1023 : row1023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1023 := by decide +kernel

theorem rowEval1023 (x : Key → ℝ) : Integer.Sparse.eval row1023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1023, Integer.Sparse.eval_collectBalanced, rawRowCheck1023]

end MUB6.Certificate.GramRows

end OAI
