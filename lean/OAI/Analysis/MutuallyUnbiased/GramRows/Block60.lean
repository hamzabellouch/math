import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4608 : Integer.Sparse Key := [(key175, -2), (key175, -2), (key175, -2), (key185, 6), (key33, 2), (key33, 2), (key33, 2), (key149, -2), (key149, -2), (key149, -2), (key223, -6), (key495, 2), (key495, 2), (key495, 2)]

theorem rawRowCheck4608 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form3 = rawRow4608 := by decide +kernel

def row4608 : Integer.Sparse Key := [(key33, 6), (key149, -6), (key175, -6), (key185, 6), (key223, -6), (key495, 6)]

theorem rowCheck4608 : row4608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4608 := by decide +kernel

theorem rowEval4608 (x : Key → ℝ) : Integer.Sparse.eval row4608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4608, Integer.Sparse.eval_collectBalanced, rawRowCheck4608]

def rawRow4609 : Integer.Sparse Key := [(key175, -2), (key175, -2), (key185, -2), (key175, 6), (key113, 2), (key113, 2), (key149, 2), (key33, -2), (key113, -2), (key113, -2), (key495, -6), (key223, 2), (key495, 2), (key495, 2)]

theorem rawRowCheck4609 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form3 = rawRow4609 := by decide +kernel

def row4609 : Integer.Sparse Key := [(key33, -2), (key149, 2), (key175, 2), (key185, -2), (key223, 2), (key495, -2)]

theorem rowCheck4609 : row4609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4609 := by decide +kernel

theorem rowEval4609 (x : Key → ℝ) : Integer.Sparse.eval row4609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4609, Integer.Sparse.eval_collectBalanced, rawRowCheck4609]

def rawRow4610 : Integer.Sparse Key := [(key175, -2), (key185, -2), (key175, -2), (key175, 6), (key113, 2), (key149, 2), (key113, 2), (key113, -2), (key33, -2), (key113, -2), (key495, -6), (key495, 2), (key223, 2), (key495, 2)]

theorem rawRowCheck4610 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form3 = rawRow4610 := by decide +kernel

def row4610 : Integer.Sparse Key := [(key33, -2), (key149, 2), (key175, 2), (key185, -2), (key223, 2), (key495, -2)]

theorem rowCheck4610 : row4610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4610 := by decide +kernel

theorem rowEval4610 (x : Key → ℝ) : Integer.Sparse.eval row4610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4610, Integer.Sparse.eval_collectBalanced, rawRowCheck4610]

def rawRow4611 : Integer.Sparse Key := [(key185, -2), (key175, -2), (key175, -2), (key175, 6), (key149, 2), (key113, 2), (key113, 2), (key113, -2), (key113, -2), (key33, -2), (key495, -6), (key495, 2), (key495, 2), (key223, 2)]

theorem rawRowCheck4611 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form3 = rawRow4611 := by decide +kernel

def row4611 : Integer.Sparse Key := [(key33, -2), (key149, 2), (key175, 2), (key185, -2), (key223, 2), (key495, -2)]

theorem rowCheck4611 : row4611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4611 := by decide +kernel

theorem rowEval4611 (x : Key → ℝ) : Integer.Sparse.eval row4611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4611, Integer.Sparse.eval_collectBalanced, rawRowCheck4611]

def rawRow4612 : Integer.Sparse Key := [(key1361, -6), (key1361, 2), (key1361, 2), (key1373, 2), (key1487, 6), (key1487, -2), (key1487, -2), (key1512, -2), (key1713, -2), (key1713, -2), (key1722, -2), (key1713, 2), (key1713, 2), (key1740, 2)]

theorem rawRowCheck4612 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form4 = rawRow4612 := by decide +kernel

def row4612 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

theorem rowCheck4612 : row4612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4612 := by decide +kernel

theorem rowEval4612 (x : Key → ℝ) : Integer.Sparse.eval row4612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4612, Integer.Sparse.eval_collectBalanced, rawRowCheck4612]

def rawRow4613 : Integer.Sparse Key := [(key1361, -6), (key1361, 2), (key1373, 2), (key1361, 2), (key1487, 6), (key1487, -2), (key1512, -2), (key1487, -2), (key1713, -2), (key1722, -2), (key1713, -2), (key1713, 2), (key1740, 2), (key1713, 2)]

theorem rawRowCheck4613 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form4 = rawRow4613 := by decide +kernel

def row4613 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

theorem rowCheck4613 : row4613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4613 := by decide +kernel

theorem rowEval4613 (x : Key → ℝ) : Integer.Sparse.eval row4613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4613, Integer.Sparse.eval_collectBalanced, rawRowCheck4613]

def rawRow4614 : Integer.Sparse Key := [(key1361, -6), (key1373, 2), (key1361, 2), (key1361, 2), (key1487, 6), (key1512, -2), (key1487, -2), (key1487, -2), (key1722, -2), (key1713, -2), (key1713, -2), (key1740, 2), (key1713, 2), (key1713, 2)]

theorem rawRowCheck4614 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form4 = rawRow4614 := by decide +kernel

def row4614 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

theorem rowCheck4614 : row4614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4614 := by decide +kernel

theorem rowEval4614 (x : Key → ℝ) : Integer.Sparse.eval row4614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4614, Integer.Sparse.eval_collectBalanced, rawRowCheck4614]

def rawRow4615 : Integer.Sparse Key := [(key1373, -6), (key1361, 2), (key1361, 2), (key1361, 2), (key1512, 6), (key1487, -2), (key1487, -2), (key1487, -2), (key1740, -2), (key1740, -2), (key1740, -2), (key1722, 2), (key1722, 2), (key1722, 2)]

theorem rawRowCheck4615 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form4 = rawRow4615 := by decide +kernel

def row4615 : Integer.Sparse Key := [(key1361, 6), (key1373, -6), (key1487, -6), (key1512, 6), (key1722, 6), (key1740, -6)]

theorem rowCheck4615 : row4615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4615 := by decide +kernel

theorem rowEval4615 (x : Key → ℝ) : Integer.Sparse.eval row4615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4615, Integer.Sparse.eval_collectBalanced, rawRowCheck4615]

def rawRow4616 : Integer.Sparse Key := [(key1487, -6), (key1713, 2), (key1713, 2), (key1722, 2), (key1361, 6), (key1713, -2), (key1713, -2), (key1740, -2), (key1361, -2), (key1361, -2), (key1373, -2), (key1487, 2), (key1487, 2), (key1512, 2)]

theorem rawRowCheck4616 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form4 = rawRow4616 := by decide +kernel

def row4616 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

theorem rowCheck4616 : row4616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4616 := by decide +kernel

theorem rowEval4616 (x : Key → ℝ) : Integer.Sparse.eval row4616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4616, Integer.Sparse.eval_collectBalanced, rawRowCheck4616]

def rawRow4617 : Integer.Sparse Key := [(key1487, -6), (key1713, 2), (key1722, 2), (key1713, 2), (key1361, 6), (key1713, -2), (key1740, -2), (key1713, -2), (key1361, -2), (key1373, -2), (key1361, -2), (key1487, 2), (key1512, 2), (key1487, 2)]

theorem rawRowCheck4617 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form4 = rawRow4617 := by decide +kernel

def row4617 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

theorem rowCheck4617 : row4617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4617 := by decide +kernel

theorem rowEval4617 (x : Key → ℝ) : Integer.Sparse.eval row4617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4617, Integer.Sparse.eval_collectBalanced, rawRowCheck4617]

def rawRow4618 : Integer.Sparse Key := [(key1487, -6), (key1722, 2), (key1713, 2), (key1713, 2), (key1361, 6), (key1740, -2), (key1713, -2), (key1713, -2), (key1373, -2), (key1361, -2), (key1361, -2), (key1512, 2), (key1487, 2), (key1487, 2)]

theorem rawRowCheck4618 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form4 = rawRow4618 := by decide +kernel

def row4618 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

theorem rowCheck4618 : row4618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4618 := by decide +kernel

theorem rowEval4618 (x : Key → ℝ) : Integer.Sparse.eval row4618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4618, Integer.Sparse.eval_collectBalanced, rawRowCheck4618]

def rawRow4619 : Integer.Sparse Key := [(key1722, -6), (key1487, 2), (key1713, 2), (key1713, 2), (key1740, 6), (key1361, -2), (key1713, -2), (key1713, -2), (key1512, -2), (key1740, -2), (key1740, -2), (key1373, 2), (key1722, 2), (key1722, 2)]

theorem rawRowCheck4619 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form4 = rawRow4619 := by decide +kernel

def row4619 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

theorem rowCheck4619 : row4619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4619 := by decide +kernel

theorem rowEval4619 (x : Key → ℝ) : Integer.Sparse.eval row4619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4619, Integer.Sparse.eval_collectBalanced, rawRowCheck4619]

def rawRow4620 : Integer.Sparse Key := [(key1722, -6), (key1713, 2), (key1487, 2), (key1713, 2), (key1740, 6), (key1713, -2), (key1361, -2), (key1713, -2), (key1740, -2), (key1512, -2), (key1740, -2), (key1722, 2), (key1373, 2), (key1722, 2)]

theorem rawRowCheck4620 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form4 = rawRow4620 := by decide +kernel

def row4620 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

theorem rowCheck4620 : row4620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4620 := by decide +kernel

theorem rowEval4620 (x : Key → ℝ) : Integer.Sparse.eval row4620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4620, Integer.Sparse.eval_collectBalanced, rawRowCheck4620]

def rawRow4621 : Integer.Sparse Key := [(key1722, -6), (key1713, 2), (key1713, 2), (key1487, 2), (key1740, 6), (key1713, -2), (key1713, -2), (key1361, -2), (key1740, -2), (key1740, -2), (key1512, -2), (key1722, 2), (key1722, 2), (key1373, 2)]

theorem rawRowCheck4621 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form4 = rawRow4621 := by decide +kernel

def row4621 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

theorem rowCheck4621 : row4621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4621 := by decide +kernel

theorem rowEval4621 (x : Key → ℝ) : Integer.Sparse.eval row4621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4621, Integer.Sparse.eval_collectBalanced, rawRowCheck4621]

def rawRow4622 : Integer.Sparse Key := [(key1512, -6), (key1740, 2), (key1740, 2), (key1740, 2), (key1373, 6), (key1722, -2), (key1722, -2), (key1722, -2), (key1361, -2), (key1361, -2), (key1361, -2), (key1487, 2), (key1487, 2), (key1487, 2)]

theorem rawRowCheck4622 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form4 = rawRow4622 := by decide +kernel

def row4622 : Integer.Sparse Key := [(key1361, -6), (key1373, 6), (key1487, 6), (key1512, -6), (key1722, -6), (key1740, 6)]

theorem rowCheck4622 : row4622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4622 := by decide +kernel

theorem rowEval4622 (x : Key → ℝ) : Integer.Sparse.eval row4622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4622, Integer.Sparse.eval_collectBalanced, rawRowCheck4622]

def rawRow4623 : Integer.Sparse Key := [(key1740, -6), (key1512, 2), (key1740, 2), (key1740, 2), (key1722, 6), (key1373, -2), (key1722, -2), (key1722, -2), (key1487, -2), (key1713, -2), (key1713, -2), (key1361, 2), (key1713, 2), (key1713, 2)]

theorem rawRowCheck4623 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form4 = rawRow4623 := by decide +kernel

def row4623 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

theorem rowCheck4623 : row4623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4623 := by decide +kernel

theorem rowEval4623 (x : Key → ℝ) : Integer.Sparse.eval row4623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4623, Integer.Sparse.eval_collectBalanced, rawRowCheck4623]

def rawRow4624 : Integer.Sparse Key := [(key1740, -6), (key1740, 2), (key1512, 2), (key1740, 2), (key1722, 6), (key1722, -2), (key1373, -2), (key1722, -2), (key1713, -2), (key1487, -2), (key1713, -2), (key1713, 2), (key1361, 2), (key1713, 2)]

theorem rawRowCheck4624 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form4 = rawRow4624 := by decide +kernel

def row4624 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

theorem rowCheck4624 : row4624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4624 := by decide +kernel

theorem rowEval4624 (x : Key → ℝ) : Integer.Sparse.eval row4624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4624, Integer.Sparse.eval_collectBalanced, rawRowCheck4624]

def rawRow4625 : Integer.Sparse Key := [(key1740, -6), (key1740, 2), (key1740, 2), (key1512, 2), (key1722, 6), (key1722, -2), (key1722, -2), (key1373, -2), (key1713, -2), (key1713, -2), (key1487, -2), (key1713, 2), (key1713, 2), (key1361, 2)]

theorem rawRowCheck4625 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form4 = rawRow4625 := by decide +kernel

def row4625 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

theorem rowCheck4625 : row4625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4625 := by decide +kernel

theorem rowEval4625 (x : Key → ℝ) : Integer.Sparse.eval row4625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4625, Integer.Sparse.eval_collectBalanced, rawRowCheck4625]

def rawRow4626 : Integer.Sparse Key := [(key351, -1), (key354, -1), (key351, -1), (key371, -1), (key354, -1), (key371, -1), (key354, 2), (key354, 2), (key371, 2), (key508, 1), (key511, 1), (key508, 1), (key543, 1), (key511, 1), (key543, 1), (key511, -1), (key523, -1), (key511, -1), (key543, -1), (key523, -1), (key543, -1), (key668, -2), (key668, -2), (key678, -2), (key668, 1), (key672, 1), (key668, 1), (key678, 1), (key672, 1), (key678, 1)]

theorem rawRowCheck4626 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form5 = rawRow4626 := by decide +kernel

def row4626 : Integer.Sparse Key := [(key351, -2), (key354, 2), (key508, 2), (key523, -2), (key668, -2), (key672, 2)]

theorem rowCheck4626 : row4626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4626 := by decide +kernel

theorem rowEval4626 (x : Key → ℝ) : Integer.Sparse.eval row4626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4626, Integer.Sparse.eval_collectBalanced, rawRowCheck4626]

def rawRow4627 : Integer.Sparse Key := [(key354, -1), (key351, -1), (key371, -1), (key351, -1), (key371, -1), (key354, -1), (key354, 2), (key371, 2), (key354, 2), (key511, 1), (key508, 1), (key543, 1), (key508, 1), (key543, 1), (key511, 1), (key523, -1), (key511, -1), (key543, -1), (key511, -1), (key543, -1), (key523, -1), (key668, -2), (key678, -2), (key668, -2), (key672, 1), (key668, 1), (key678, 1), (key668, 1), (key678, 1), (key672, 1)]

theorem rawRowCheck4627 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form5 = rawRow4627 := by decide +kernel

def row4627 : Integer.Sparse Key := [(key351, -2), (key354, 2), (key508, 2), (key523, -2), (key668, -2), (key672, 2)]

theorem rowCheck4627 : row4627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4627 := by decide +kernel

theorem rowEval4627 (x : Key → ℝ) : Integer.Sparse.eval row4627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4627, Integer.Sparse.eval_collectBalanced, rawRowCheck4627]

def rawRow4628 : Integer.Sparse Key := [(key371, -1), (key371, -1), (key354, -1), (key354, -1), (key351, -1), (key351, -1), (key371, 2), (key354, 2), (key354, 2), (key543, 1), (key543, 1), (key511, 1), (key511, 1), (key508, 1), (key508, 1), (key543, -1), (key543, -1), (key523, -1), (key523, -1), (key511, -1), (key511, -1), (key678, -2), (key668, -2), (key668, -2), (key678, 1), (key678, 1), (key672, 1), (key672, 1), (key668, 1), (key668, 1)]

theorem rawRowCheck4628 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form5 = rawRow4628 := by decide +kernel

def row4628 : Integer.Sparse Key := [(key351, -2), (key354, 2), (key508, 2), (key523, -2), (key668, -2), (key672, 2)]

theorem rowCheck4628 : row4628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4628 := by decide +kernel

theorem rowEval4628 (x : Key → ℝ) : Integer.Sparse.eval row4628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4628, Integer.Sparse.eval_collectBalanced, rawRowCheck4628]

def rawRow4629 : Integer.Sparse Key := [(key354, -1), (key354, -1), (key354, -1), (key354, -1), (key354, -1), (key354, -1), (key351, 2), (key351, 2), (key351, 2), (key523, 1), (key523, 1), (key523, 1), (key523, 1), (key523, 1), (key523, 1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key672, -2), (key672, -2), (key672, -2), (key668, 1), (key668, 1), (key668, 1), (key668, 1), (key668, 1), (key668, 1)]

theorem rawRowCheck4629 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form5 = rawRow4629 := by decide +kernel

def row4629 : Integer.Sparse Key := [(key351, 6), (key354, -6), (key508, -6), (key523, 6), (key668, 6), (key672, -6)]

theorem rowCheck4629 : row4629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4629 := by decide +kernel

theorem rowEval4629 (x : Key → ℝ) : Integer.Sparse.eval row4629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4629, Integer.Sparse.eval_collectBalanced, rawRowCheck4629]

def rawRow4630 : Integer.Sparse Key := [(key439, -1), (key443, -1), (key439, -1), (key596, -1), (key443, -1), (key596, -1), (key458, 2), (key458, 2), (key607, 2), (key351, 1), (key354, 1), (key351, 1), (key371, 1), (key354, 1), (key371, 1), (key668, -1), (key672, -1), (key668, -1), (key678, -1), (key672, -1), (key678, -1), (key354, -2), (key354, -2), (key371, -2), (key511, 1), (key523, 1), (key511, 1), (key543, 1), (key523, 1), (key543, 1)]

theorem rawRowCheck4630 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form5 = rawRow4630 := by decide +kernel

def row4630 : Integer.Sparse Key := [(key351, 2), (key354, -2), (key439, -2), (key443, -2), (key458, 4), (key511, 2), (key523, 2), (key543, 2), (key596, -2), (key607, 2), (key668, -2), (key672, -2), (key678, -2)]

theorem rowCheck4630 : row4630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4630 := by decide +kernel

theorem rowEval4630 (x : Key → ℝ) : Integer.Sparse.eval row4630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4630, Integer.Sparse.eval_collectBalanced, rawRowCheck4630]

def rawRow4631 : Integer.Sparse Key := [(key443, -1), (key439, -1), (key596, -1), (key439, -1), (key596, -1), (key443, -1), (key458, 2), (key607, 2), (key458, 2), (key354, 1), (key351, 1), (key371, 1), (key351, 1), (key371, 1), (key354, 1), (key672, -1), (key668, -1), (key678, -1), (key668, -1), (key678, -1), (key672, -1), (key354, -2), (key371, -2), (key354, -2), (key523, 1), (key511, 1), (key543, 1), (key511, 1), (key543, 1), (key523, 1)]

theorem rawRowCheck4631 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form5 = rawRow4631 := by decide +kernel

def row4631 : Integer.Sparse Key := [(key351, 2), (key354, -2), (key439, -2), (key443, -2), (key458, 4), (key511, 2), (key523, 2), (key543, 2), (key596, -2), (key607, 2), (key668, -2), (key672, -2), (key678, -2)]

theorem rowCheck4631 : row4631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4631 := by decide +kernel

theorem rowEval4631 (x : Key → ℝ) : Integer.Sparse.eval row4631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4631, Integer.Sparse.eval_collectBalanced, rawRowCheck4631]

def rawRow4632 : Integer.Sparse Key := [(key596, -1), (key596, -1), (key443, -1), (key443, -1), (key439, -1), (key439, -1), (key607, 2), (key458, 2), (key458, 2), (key371, 1), (key371, 1), (key354, 1), (key354, 1), (key351, 1), (key351, 1), (key678, -1), (key678, -1), (key672, -1), (key672, -1), (key668, -1), (key668, -1), (key371, -2), (key354, -2), (key354, -2), (key543, 1), (key543, 1), (key523, 1), (key523, 1), (key511, 1), (key511, 1)]

theorem rawRowCheck4632 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form5 = rawRow4632 := by decide +kernel

def row4632 : Integer.Sparse Key := [(key351, 2), (key354, -2), (key439, -2), (key443, -2), (key458, 4), (key511, 2), (key523, 2), (key543, 2), (key596, -2), (key607, 2), (key668, -2), (key672, -2), (key678, -2)]

theorem rowCheck4632 : row4632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4632 := by decide +kernel

theorem rowEval4632 (x : Key → ℝ) : Integer.Sparse.eval row4632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4632, Integer.Sparse.eval_collectBalanced, rawRowCheck4632]

def rawRow4633 : Integer.Sparse Key := [(key261, -1), (key261, -1), (key443, -1), (key443, -1), (key458, -1), (key458, -1), (key257, 2), (key439, 2), (key439, 2), (key272, 1), (key272, 1), (key470, 1), (key470, 1), (key481, 1), (key481, 1), (key282, -1), (key282, -1), (key351, -1), (key351, -1), (key508, -1), (key508, -1), (key295, -2), (key523, -2), (key523, -2), (key285, 1), (key285, 1), (key354, 1), (key354, 1), (key511, 1), (key511, 1)]

theorem rawRowCheck4633 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form5 = rawRow4633 := by decide +kernel

def row4633 : Integer.Sparse Key := [(key257, 2), (key261, -2), (key272, 2), (key282, -2), (key285, 2), (key295, -2), (key351, -2), (key354, 2), (key439, 4), (key443, -2), (key458, -2), (key470, 2), (key481, 2), (key508, -2), (key511, 2), (key523, -4)]

theorem rowCheck4633 : row4633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4633 := by decide +kernel

theorem rowEval4633 (x : Key → ℝ) : Integer.Sparse.eval row4633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4633, Integer.Sparse.eval_collectBalanced, rawRowCheck4633]

def rawRow4634 : Integer.Sparse Key := [(key443, -1), (key458, -1), (key261, -1), (key458, -1), (key261, -1), (key443, -1), (key439, 2), (key257, 2), (key439, 2), (key470, 1), (key481, 1), (key272, 1), (key481, 1), (key272, 1), (key470, 1), (key351, -1), (key508, -1), (key282, -1), (key508, -1), (key282, -1), (key351, -1), (key523, -2), (key295, -2), (key523, -2), (key354, 1), (key511, 1), (key285, 1), (key511, 1), (key285, 1), (key354, 1)]

theorem rawRowCheck4634 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form5 = rawRow4634 := by decide +kernel

def row4634 : Integer.Sparse Key := [(key257, 2), (key261, -2), (key272, 2), (key282, -2), (key285, 2), (key295, -2), (key351, -2), (key354, 2), (key439, 4), (key443, -2), (key458, -2), (key470, 2), (key481, 2), (key508, -2), (key511, 2), (key523, -4)]

theorem rowCheck4634 : row4634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4634 := by decide +kernel

theorem rowEval4634 (x : Key → ℝ) : Integer.Sparse.eval row4634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4634, Integer.Sparse.eval_collectBalanced, rawRowCheck4634]

def rawRow4635 : Integer.Sparse Key := [(key458, -1), (key443, -1), (key458, -1), (key261, -1), (key443, -1), (key261, -1), (key439, 2), (key439, 2), (key257, 2), (key481, 1), (key470, 1), (key481, 1), (key272, 1), (key470, 1), (key272, 1), (key508, -1), (key351, -1), (key508, -1), (key282, -1), (key351, -1), (key282, -1), (key523, -2), (key523, -2), (key295, -2), (key511, 1), (key354, 1), (key511, 1), (key285, 1), (key354, 1), (key285, 1)]

theorem rawRowCheck4635 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form5 = rawRow4635 := by decide +kernel

def row4635 : Integer.Sparse Key := [(key257, 2), (key261, -2), (key272, 2), (key282, -2), (key285, 2), (key295, -2), (key351, -2), (key354, 2), (key439, 4), (key443, -2), (key458, -2), (key470, 2), (key481, 2), (key508, -2), (key511, 2), (key523, -4)]

theorem rowCheck4635 : row4635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4635 := by decide +kernel

theorem rowEval4635 (x : Key → ℝ) : Integer.Sparse.eval row4635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck4635, Integer.Sparse.eval_collectBalanced, rawRowCheck4635]

def rawRow4636 : Integer.Sparse Key := [(key470, -1), (key470, -1), (key470, -1), (key470, -1), (key470, -1), (key470, -1), (key481, 2), (key481, 2), (key481, 2), (key398, 1), (key398, 1), (key398, 1), (key398, 1), (key398, 1), (key398, 1), (key458, -1), (key458, -1), (key458, -1), (key458, -1), (key458, -1), (key458, -1), (key351, -2), (key351, -2), (key351, -2), (key508, 1), (key508, 1), (key508, 1), (key508, 1), (key508, 1), (key508, 1)]

theorem rawRowCheck4636 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form5 = rawRow4636 := by decide +kernel

def row4636 : Integer.Sparse Key := [(key351, -6), (key398, 6), (key458, -6), (key470, -6), (key481, 6), (key508, 6)]

theorem rowCheck4636 : row4636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4636 := by decide +kernel

theorem rowEval4636 (x : Key → ℝ) : Integer.Sparse.eval row4636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4636, Integer.Sparse.eval_collectBalanced, rawRowCheck4636]

def rawRow4637 : Integer.Sparse Key := [(key272, -1), (key272, -1), (key470, -1), (key470, -1), (key481, -1), (key481, -1), (key272, 2), (key470, 2), (key470, 2), (key261, 1), (key261, 1), (key443, 1), (key443, 1), (key458, 1), (key458, 1), (key261, -1), (key261, -1), (key398, -1), (key398, -1), (key443, -1), (key443, -1), (key282, -2), (key508, -2), (key508, -2), (key282, 1), (key282, 1), (key351, 1), (key351, 1), (key508, 1), (key508, 1)]

theorem rawRowCheck4637 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form5 = rawRow4637 := by decide +kernel

def row4637 : Integer.Sparse Key := [(key351, 2), (key398, -2), (key458, 2), (key470, 2), (key481, -2), (key508, -2)]

theorem rowCheck4637 : row4637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4637 := by decide +kernel

theorem rowEval4637 (x : Key → ℝ) : Integer.Sparse.eval row4637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4637, Integer.Sparse.eval_collectBalanced, rawRowCheck4637]

def rawRow4638 : Integer.Sparse Key := [(key470, -1), (key481, -1), (key272, -1), (key481, -1), (key272, -1), (key470, -1), (key470, 2), (key272, 2), (key470, 2), (key443, 1), (key458, 1), (key261, 1), (key458, 1), (key261, 1), (key443, 1), (key398, -1), (key443, -1), (key261, -1), (key443, -1), (key261, -1), (key398, -1), (key508, -2), (key282, -2), (key508, -2), (key351, 1), (key508, 1), (key282, 1), (key508, 1), (key282, 1), (key351, 1)]

theorem rawRowCheck4638 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form5 = rawRow4638 := by decide +kernel

def row4638 : Integer.Sparse Key := [(key351, 2), (key398, -2), (key458, 2), (key470, 2), (key481, -2), (key508, -2)]

theorem rowCheck4638 : row4638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4638 := by decide +kernel

theorem rowEval4638 (x : Key → ℝ) : Integer.Sparse.eval row4638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4638, Integer.Sparse.eval_collectBalanced, rawRowCheck4638]

def rawRow4639 : Integer.Sparse Key := [(key481, -1), (key470, -1), (key481, -1), (key272, -1), (key470, -1), (key272, -1), (key470, 2), (key470, 2), (key272, 2), (key458, 1), (key443, 1), (key458, 1), (key261, 1), (key443, 1), (key261, 1), (key443, -1), (key398, -1), (key443, -1), (key261, -1), (key398, -1), (key261, -1), (key508, -2), (key508, -2), (key282, -2), (key508, 1), (key351, 1), (key508, 1), (key282, 1), (key351, 1), (key282, 1)]

theorem rawRowCheck4639 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form5 = rawRow4639 := by decide +kernel

def row4639 : Integer.Sparse Key := [(key351, 2), (key398, -2), (key458, 2), (key470, 2), (key481, -2), (key508, -2)]

theorem rowCheck4639 : row4639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4639 := by decide +kernel

theorem rowEval4639 (x : Key → ℝ) : Integer.Sparse.eval row4639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck4639, Integer.Sparse.eval_collectBalanced, rawRowCheck4639]

def rawRow4640 : Integer.Sparse Key := [(key1502, -2), (key1508, -2), (key1508, -2), (key1504, 2), (key1508, 2), (key1508, 2), (key1734, 2), (key1737, 2), (key1737, 2), (key1737, -6), (key1945, -2), (key1947, -2), (key1947, -2), (key1947, 6)]

theorem rawRowCheck4640 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form6 = rawRow4640 := by decide +kernel

def row4640 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

theorem rowCheck4640 : row4640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4640 := by decide +kernel

theorem rowEval4640 (x : Key → ℝ) : Integer.Sparse.eval row4640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4640, Integer.Sparse.eval_collectBalanced, rawRowCheck4640]

def rawRow4641 : Integer.Sparse Key := [(key1508, -2), (key1502, -2), (key1508, -2), (key1508, 2), (key1504, 2), (key1508, 2), (key1737, 2), (key1734, 2), (key1737, 2), (key1737, -6), (key1947, -2), (key1945, -2), (key1947, -2), (key1947, 6)]

theorem rawRowCheck4641 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form6 = rawRow4641 := by decide +kernel

def row4641 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

theorem rowCheck4641 : row4641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4641 := by decide +kernel

theorem rowEval4641 (x : Key → ℝ) : Integer.Sparse.eval row4641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4641, Integer.Sparse.eval_collectBalanced, rawRowCheck4641]

def rawRow4642 : Integer.Sparse Key := [(key1508, -2), (key1508, -2), (key1502, -2), (key1508, 2), (key1508, 2), (key1504, 2), (key1737, 2), (key1737, 2), (key1734, 2), (key1737, -6), (key1947, -2), (key1947, -2), (key1945, -2), (key1947, 6)]

theorem rawRowCheck4642 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form6 = rawRow4642 := by decide +kernel

def row4642 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

theorem rowCheck4642 : row4642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4642 := by decide +kernel

theorem rowEval4642 (x : Key → ℝ) : Integer.Sparse.eval row4642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4642, Integer.Sparse.eval_collectBalanced, rawRowCheck4642]

def rawRow4643 : Integer.Sparse Key := [(key1504, -2), (key1504, -2), (key1504, -2), (key1502, 2), (key1502, 2), (key1502, 2), (key1737, 2), (key1737, 2), (key1737, 2), (key1734, -6), (key1947, -2), (key1947, -2), (key1947, -2), (key1945, 6)]

theorem rawRowCheck4643 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form6 = rawRow4643 := by decide +kernel

def row4643 : Integer.Sparse Key := [(key1502, 6), (key1504, -6), (key1734, -6), (key1737, 6), (key1945, 6), (key1947, -6)]

theorem rowCheck4643 : row4643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4643 := by decide +kernel

theorem rowEval4643 (x : Key → ℝ) : Integer.Sparse.eval row4643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4643, Integer.Sparse.eval_collectBalanced, rawRowCheck4643]

def rawRow4644 : Integer.Sparse Key := [(key1734, -2), (key1737, -2), (key1737, -2), (key1945, 2), (key1947, 2), (key1947, 2), (key1502, 2), (key1508, 2), (key1508, 2), (key1947, -6), (key1504, -2), (key1508, -2), (key1508, -2), (key1737, 6)]

theorem rawRowCheck4644 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form6 = rawRow4644 := by decide +kernel

def row4644 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

theorem rowCheck4644 : row4644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4644 := by decide +kernel

theorem rowEval4644 (x : Key → ℝ) : Integer.Sparse.eval row4644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4644, Integer.Sparse.eval_collectBalanced, rawRowCheck4644]

def rawRow4645 : Integer.Sparse Key := [(key1737, -2), (key1734, -2), (key1737, -2), (key1947, 2), (key1945, 2), (key1947, 2), (key1508, 2), (key1502, 2), (key1508, 2), (key1947, -6), (key1508, -2), (key1504, -2), (key1508, -2), (key1737, 6)]

theorem rawRowCheck4645 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form6 = rawRow4645 := by decide +kernel

def row4645 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

theorem rowCheck4645 : row4645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4645 := by decide +kernel

theorem rowEval4645 (x : Key → ℝ) : Integer.Sparse.eval row4645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4645, Integer.Sparse.eval_collectBalanced, rawRowCheck4645]

def rawRow4646 : Integer.Sparse Key := [(key1737, -2), (key1737, -2), (key1734, -2), (key1947, 2), (key1947, 2), (key1945, 2), (key1508, 2), (key1508, 2), (key1502, 2), (key1947, -6), (key1508, -2), (key1508, -2), (key1504, -2), (key1737, 6)]

theorem rawRowCheck4646 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form6 = rawRow4646 := by decide +kernel

def row4646 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

theorem rowCheck4646 : row4646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4646 := by decide +kernel

theorem rowEval4646 (x : Key → ℝ) : Integer.Sparse.eval row4646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4646, Integer.Sparse.eval_collectBalanced, rawRowCheck4646]

def rawRow4647 : Integer.Sparse Key := [(key1504, -2), (key1504, -2), (key1945, -2), (key1502, 2), (key1502, 2), (key1734, 2), (key1508, 2), (key1508, 2), (key1947, 2), (key1502, -6), (key1508, -2), (key1508, -2), (key1737, -2), (key1504, 6)]

theorem rawRowCheck4647 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form6 = rawRow4647 := by decide +kernel

def row4647 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

theorem rowCheck4647 : row4647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4647 := by decide +kernel

theorem rowEval4647 (x : Key → ℝ) : Integer.Sparse.eval row4647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4647, Integer.Sparse.eval_collectBalanced, rawRowCheck4647]

def rawRow4648 : Integer.Sparse Key := [(key1504, -2), (key1945, -2), (key1504, -2), (key1502, 2), (key1734, 2), (key1502, 2), (key1508, 2), (key1947, 2), (key1508, 2), (key1502, -6), (key1508, -2), (key1737, -2), (key1508, -2), (key1504, 6)]

theorem rawRowCheck4648 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form6 = rawRow4648 := by decide +kernel

def row4648 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

theorem rowCheck4648 : row4648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4648 := by decide +kernel

theorem rowEval4648 (x : Key → ℝ) : Integer.Sparse.eval row4648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4648, Integer.Sparse.eval_collectBalanced, rawRowCheck4648]

def rawRow4649 : Integer.Sparse Key := [(key1945, -2), (key1504, -2), (key1504, -2), (key1734, 2), (key1502, 2), (key1502, 2), (key1947, 2), (key1508, 2), (key1508, 2), (key1502, -6), (key1737, -2), (key1508, -2), (key1508, -2), (key1504, 6)]

theorem rawRowCheck4649 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form6 = rawRow4649 := by decide +kernel

def row4649 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

theorem rowCheck4649 : row4649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4649 := by decide +kernel

theorem rowEval4649 (x : Key → ℝ) : Integer.Sparse.eval row4649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4649, Integer.Sparse.eval_collectBalanced, rawRowCheck4649]

def rawRow4650 : Integer.Sparse Key := [(key1737, -2), (key1737, -2), (key1737, -2), (key1947, 2), (key1947, 2), (key1947, 2), (key1504, 2), (key1504, 2), (key1504, 2), (key1945, -6), (key1502, -2), (key1502, -2), (key1502, -2), (key1734, 6)]

theorem rawRowCheck4650 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form6 = rawRow4650 := by decide +kernel

def row4650 : Integer.Sparse Key := [(key1502, -6), (key1504, 6), (key1734, 6), (key1737, -6), (key1945, -6), (key1947, 6)]

theorem rowCheck4650 : row4650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4650 := by decide +kernel

theorem rowEval4650 (x : Key → ℝ) : Integer.Sparse.eval row4650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4650, Integer.Sparse.eval_collectBalanced, rawRowCheck4650]

def rawRow4651 : Integer.Sparse Key := [(key1508, -2), (key1508, -2), (key1947, -2), (key1508, 2), (key1508, 2), (key1737, 2), (key1504, 2), (key1504, 2), (key1945, 2), (key1504, -6), (key1502, -2), (key1502, -2), (key1734, -2), (key1502, 6)]

theorem rawRowCheck4651 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form6 = rawRow4651 := by decide +kernel

def row4651 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

theorem rowCheck4651 : row4651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4651 := by decide +kernel

theorem rowEval4651 (x : Key → ℝ) : Integer.Sparse.eval row4651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4651, Integer.Sparse.eval_collectBalanced, rawRowCheck4651]

def rawRow4652 : Integer.Sparse Key := [(key1508, -2), (key1947, -2), (key1508, -2), (key1508, 2), (key1737, 2), (key1508, 2), (key1504, 2), (key1945, 2), (key1504, 2), (key1504, -6), (key1502, -2), (key1734, -2), (key1502, -2), (key1502, 6)]

theorem rawRowCheck4652 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form6 = rawRow4652 := by decide +kernel

def row4652 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

theorem rowCheck4652 : row4652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4652 := by decide +kernel

theorem rowEval4652 (x : Key → ℝ) : Integer.Sparse.eval row4652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4652, Integer.Sparse.eval_collectBalanced, rawRowCheck4652]

def rawRow4653 : Integer.Sparse Key := [(key1947, -2), (key1508, -2), (key1508, -2), (key1737, 2), (key1508, 2), (key1508, 2), (key1945, 2), (key1504, 2), (key1504, 2), (key1504, -6), (key1734, -2), (key1502, -2), (key1502, -2), (key1502, 6)]

theorem rawRowCheck4653 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form6 = rawRow4653 := by decide +kernel

def row4653 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

theorem rowCheck4653 : row4653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4653 := by decide +kernel

theorem rowEval4653 (x : Key → ℝ) : Integer.Sparse.eval row4653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4653, Integer.Sparse.eval_collectBalanced, rawRowCheck4653]

def rawRow4654 : Integer.Sparse Key := [(key257, -2), (key261, -2), (key261, -2), (key257, 1), (key261, 1), (key257, 1), (key295, 1), (key285, 1), (key295, 1), (key351, 2), (key354, 2), (key354, 2), (key351, -1), (key354, -1), (key351, -1), (key371, -1), (key354, -1), (key371, -1), (key508, -1), (key511, -1), (key508, -1), (key523, -1), (key511, -1), (key523, -1), (key508, 1), (key511, 1), (key508, 1), (key543, 1), (key511, 1), (key543, 1)]

theorem rawRowCheck4654 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form7 = rawRow4654 := by decide +kernel

def row4654 : Integer.Sparse Key := [(key261, -3), (key285, 1), (key295, 2), (key354, 2), (key371, -2), (key523, -2), (key543, 2)]

theorem rowCheck4654 : row4654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4654 := by decide +kernel

theorem rowEval4654 (x : Key → ℝ) : Integer.Sparse.eval row4654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4654, Integer.Sparse.eval_collectBalanced, rawRowCheck4654]

def rawRow4655 : Integer.Sparse Key := [(key261, -2), (key257, -2), (key261, -2), (key261, 1), (key257, 1), (key272, 1), (key282, 1), (key295, 1), (key285, 1), (key354, 2), (key351, 2), (key354, 2), (key354, -1), (key351, -1), (key371, -1), (key351, -1), (key371, -1), (key354, -1), (key511, -1), (key508, -1), (key523, -1), (key508, -1), (key523, -1), (key511, -1), (key511, 1), (key508, 1), (key543, 1), (key508, 1), (key543, 1), (key511, 1)]

theorem rawRowCheck4655 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form7 = rawRow4655 := by decide +kernel

def row4655 : Integer.Sparse Key := [(key257, -1), (key261, -3), (key272, 1), (key282, 1), (key285, 1), (key295, 1), (key354, 2), (key371, -2), (key523, -2), (key543, 2)]

theorem rowCheck4655 : row4655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4655 := by decide +kernel

theorem rowEval4655 (x : Key → ℝ) : Integer.Sparse.eval row4655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4655, Integer.Sparse.eval_collectBalanced, rawRowCheck4655]

def rawRow4656 : Integer.Sparse Key := [(key261, -2), (key261, -2), (key257, -2), (key272, 1), (key272, 1), (key261, 1), (key261, 1), (key282, 1), (key282, 1), (key354, 2), (key354, 2), (key351, 2), (key371, -1), (key371, -1), (key354, -1), (key354, -1), (key351, -1), (key351, -1), (key523, -1), (key523, -1), (key511, -1), (key511, -1), (key508, -1), (key508, -1), (key543, 1), (key543, 1), (key511, 1), (key511, 1), (key508, 1), (key508, 1)]

theorem rawRowCheck4656 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form7 = rawRow4656 := by decide +kernel

def row4656 : Integer.Sparse Key := [(key257, -2), (key261, -2), (key272, 2), (key282, 2), (key354, 2), (key371, -2), (key523, -2), (key543, 2)]

theorem rowCheck4656 : row4656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4656 := by decide +kernel

theorem rowEval4656 (x : Key → ℝ) : Integer.Sparse.eval row4656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4656, Integer.Sparse.eval_collectBalanced, rawRowCheck4656]

def rawRow4657 : Integer.Sparse Key := [(key272, -2), (key272, -2), (key272, -2), (key261, 1), (key261, 1), (key261, 1), (key261, 1), (key261, 1), (key261, 1), (key371, 2), (key371, 2), (key371, 2), (key354, -1), (key354, -1), (key354, -1), (key354, -1), (key354, -1), (key354, -1), (key543, -1), (key543, -1), (key543, -1), (key543, -1), (key543, -1), (key543, -1), (key523, 1), (key523, 1), (key523, 1), (key523, 1), (key523, 1), (key523, 1)]

theorem rawRowCheck4657 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form7 = rawRow4657 := by decide +kernel

def row4657 : Integer.Sparse Key := [(key261, 6), (key272, -6), (key354, -6), (key371, 6), (key523, 6), (key543, -6)]

theorem rowCheck4657 : row4657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4657 := by decide +kernel

theorem rowEval4657 (x : Key → ℝ) : Integer.Sparse.eval row4657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4657, Integer.Sparse.eval_collectBalanced, rawRowCheck4657]

def rawRow4658 : Integer.Sparse Key := [(key394, -2), (key398, -2), (key398, -2), (key439, 1), (key443, 1), (key439, 1), (key470, 1), (key443, 1), (key470, 1), (key257, 2), (key261, 2), (key261, 2), (key439, -1), (key443, -1), (key439, -1), (key596, -1), (key443, -1), (key596, -1), (key257, -1), (key261, -1), (key257, -1), (key295, -1), (key285, -1), (key295, -1), (key351, 1), (key354, 1), (key351, 1), (key371, 1), (key354, 1), (key371, 1)]

theorem rawRowCheck4658 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form7 = rawRow4658 := by decide +kernel

def row4658 : Integer.Sparse Key := [(key261, 3), (key285, -1), (key295, -2), (key351, 2), (key354, 2), (key371, 2), (key394, -2), (key398, -4), (key470, 2), (key596, -2)]

theorem rowCheck4658 : row4658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4658 := by decide +kernel

theorem rowEval4658 (x : Key → ℝ) : Integer.Sparse.eval row4658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4658, Integer.Sparse.eval_collectBalanced, rawRowCheck4658]

def rawRow4659 : Integer.Sparse Key := [(key398, -2), (key394, -2), (key398, -2), (key443, 1), (key439, 1), (key470, 1), (key439, 1), (key470, 1), (key443, 1), (key261, 2), (key257, 2), (key261, 2), (key443, -1), (key439, -1), (key596, -1), (key439, -1), (key596, -1), (key443, -1), (key261, -1), (key257, -1), (key272, -1), (key282, -1), (key295, -1), (key285, -1), (key354, 1), (key351, 1), (key371, 1), (key351, 1), (key371, 1), (key354, 1)]

theorem rawRowCheck4659 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form7 = rawRow4659 := by decide +kernel

def row4659 : Integer.Sparse Key := [(key257, 1), (key261, 3), (key272, -1), (key282, -1), (key285, -1), (key295, -1), (key351, 2), (key354, 2), (key371, 2), (key394, -2), (key398, -4), (key470, 2), (key596, -2)]

theorem rowCheck4659 : row4659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4659 := by decide +kernel

theorem rowEval4659 (x : Key → ℝ) : Integer.Sparse.eval row4659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4659, Integer.Sparse.eval_collectBalanced, rawRowCheck4659]

def rawRow4660 : Integer.Sparse Key := [(key398, -2), (key398, -2), (key394, -2), (key470, 1), (key470, 1), (key443, 1), (key443, 1), (key439, 1), (key439, 1), (key261, 2), (key261, 2), (key257, 2), (key596, -1), (key596, -1), (key443, -1), (key443, -1), (key439, -1), (key439, -1), (key272, -1), (key272, -1), (key261, -1), (key261, -1), (key282, -1), (key282, -1), (key371, 1), (key371, 1), (key354, 1), (key354, 1), (key351, 1), (key351, 1)]

theorem rawRowCheck4660 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form7 = rawRow4660 := by decide +kernel

def row4660 : Integer.Sparse Key := [(key257, 2), (key261, 2), (key272, -2), (key282, -2), (key351, 2), (key354, 2), (key371, 2), (key394, -2), (key398, -4), (key470, 2), (key596, -2)]

theorem rowCheck4660 : row4660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4660 := by decide +kernel

theorem rowEval4660 (x : Key → ℝ) : Integer.Sparse.eval row4660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4660, Integer.Sparse.eval_collectBalanced, rawRowCheck4660]

def rawRow4661 : Integer.Sparse Key := [(key470, -2), (key470, -2), (key481, -2), (key398, 1), (key398, 1), (key443, 1), (key443, 1), (key458, 1), (key458, 1), (key596, 2), (key596, 2), (key607, 2), (key261, -1), (key261, -1), (key443, -1), (key443, -1), (key458, -1), (key458, -1), (key573, -1), (key573, -1), (key596, -1), (key596, -1), (key607, -1), (key607, -1), (key272, 1), (key272, 1), (key470, 1), (key470, 1), (key481, 1), (key481, 1)]

theorem rawRowCheck4661 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form7 = rawRow4661 := by decide +kernel

def row4661 : Integer.Sparse Key := [(key261, -2), (key272, 2), (key398, 2), (key470, -2), (key573, -2), (key596, 2)]

theorem rowCheck4661 : row4661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4661 := by decide +kernel

theorem rowEval4661 (x : Key → ℝ) : Integer.Sparse.eval row4661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4661, Integer.Sparse.eval_collectBalanced, rawRowCheck4661]

def rawRow4662 : Integer.Sparse Key := [(key470, -2), (key481, -2), (key470, -2), (key443, 1), (key458, 1), (key398, 1), (key458, 1), (key398, 1), (key443, 1), (key596, 2), (key607, 2), (key596, 2), (key443, -1), (key458, -1), (key261, -1), (key458, -1), (key261, -1), (key443, -1), (key596, -1), (key607, -1), (key573, -1), (key607, -1), (key573, -1), (key596, -1), (key470, 1), (key481, 1), (key272, 1), (key481, 1), (key272, 1), (key470, 1)]

theorem rawRowCheck4662 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form7 = rawRow4662 := by decide +kernel

def row4662 : Integer.Sparse Key := [(key261, -2), (key272, 2), (key398, 2), (key470, -2), (key573, -2), (key596, 2)]

theorem rowCheck4662 : row4662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4662 := by decide +kernel

theorem rowEval4662 (x : Key → ℝ) : Integer.Sparse.eval row4662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4662, Integer.Sparse.eval_collectBalanced, rawRowCheck4662]

def rawRow4663 : Integer.Sparse Key := [(key481, -2), (key470, -2), (key470, -2), (key458, 1), (key443, 1), (key458, 1), (key398, 1), (key443, 1), (key398, 1), (key607, 2), (key596, 2), (key596, 2), (key458, -1), (key443, -1), (key458, -1), (key261, -1), (key443, -1), (key261, -1), (key607, -1), (key596, -1), (key607, -1), (key573, -1), (key596, -1), (key573, -1), (key481, 1), (key470, 1), (key481, 1), (key272, 1), (key470, 1), (key272, 1)]

theorem rawRowCheck4663 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form7 = rawRow4663 := by decide +kernel

def row4663 : Integer.Sparse Key := [(key261, -2), (key272, 2), (key398, 2), (key470, -2), (key573, -2), (key596, 2)]

theorem rowCheck4663 : row4663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4663 := by decide +kernel

theorem rowEval4663 (x : Key → ℝ) : Integer.Sparse.eval row4663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4663, Integer.Sparse.eval_collectBalanced, rawRowCheck4663]

def rawRow4664 : Integer.Sparse Key := [(key573, -2), (key573, -2), (key573, -2), (key596, 1), (key596, 1), (key596, 1), (key596, 1), (key596, 1), (key596, 1), (key272, 2), (key272, 2), (key272, 2), (key470, -1), (key470, -1), (key470, -1), (key470, -1), (key470, -1), (key470, -1), (key261, -1), (key261, -1), (key261, -1), (key261, -1), (key261, -1), (key261, -1), (key398, 1), (key398, 1), (key398, 1), (key398, 1), (key398, 1), (key398, 1)]

theorem rawRowCheck4664 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form7 = rawRow4664 := by decide +kernel

def row4664 : Integer.Sparse Key := [(key261, -6), (key272, 6), (key398, 6), (key470, -6), (key573, -6), (key596, 6)]

theorem rowCheck4664 : row4664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4664 := by decide +kernel

theorem rowEval4664 (x : Key → ℝ) : Integer.Sparse.eval row4664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4664, Integer.Sparse.eval_collectBalanced, rawRowCheck4664]

def rawRow4665 : Integer.Sparse Key := [(key596, -2), (key596, -2), (key607, -2), (key573, 1), (key573, 1), (key596, 1), (key596, 1), (key607, 1), (key607, 1), (key470, 2), (key470, 2), (key481, 2), (key272, -1), (key272, -1), (key470, -1), (key470, -1), (key481, -1), (key481, -1), (key398, -1), (key398, -1), (key443, -1), (key443, -1), (key458, -1), (key458, -1), (key261, 1), (key261, 1), (key443, 1), (key443, 1), (key458, 1), (key458, 1)]

theorem rawRowCheck4665 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form7 = rawRow4665 := by decide +kernel

def row4665 : Integer.Sparse Key := [(key261, 2), (key272, -2), (key398, -2), (key470, 2), (key573, 2), (key596, -2)]

theorem rowCheck4665 : row4665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4665 := by decide +kernel

theorem rowEval4665 (x : Key → ℝ) : Integer.Sparse.eval row4665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4665, Integer.Sparse.eval_collectBalanced, rawRowCheck4665]

def rawRow4666 : Integer.Sparse Key := [(key596, -2), (key607, -2), (key596, -2), (key596, 1), (key607, 1), (key573, 1), (key607, 1), (key573, 1), (key596, 1), (key470, 2), (key481, 2), (key470, 2), (key470, -1), (key481, -1), (key272, -1), (key481, -1), (key272, -1), (key470, -1), (key443, -1), (key458, -1), (key398, -1), (key458, -1), (key398, -1), (key443, -1), (key443, 1), (key458, 1), (key261, 1), (key458, 1), (key261, 1), (key443, 1)]

theorem rawRowCheck4666 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form7 = rawRow4666 := by decide +kernel

def row4666 : Integer.Sparse Key := [(key261, 2), (key272, -2), (key398, -2), (key470, 2), (key573, 2), (key596, -2)]

theorem rowCheck4666 : row4666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4666 := by decide +kernel

theorem rowEval4666 (x : Key → ℝ) : Integer.Sparse.eval row4666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4666, Integer.Sparse.eval_collectBalanced, rawRowCheck4666]

def rawRow4667 : Integer.Sparse Key := [(key607, -2), (key596, -2), (key596, -2), (key607, 1), (key596, 1), (key607, 1), (key573, 1), (key596, 1), (key573, 1), (key481, 2), (key470, 2), (key470, 2), (key481, -1), (key470, -1), (key481, -1), (key272, -1), (key470, -1), (key272, -1), (key458, -1), (key443, -1), (key458, -1), (key398, -1), (key443, -1), (key398, -1), (key458, 1), (key443, 1), (key458, 1), (key261, 1), (key443, 1), (key261, 1)]

theorem rawRowCheck4667 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form7 = rawRow4667 := by decide +kernel

def row4667 : Integer.Sparse Key := [(key261, 2), (key272, -2), (key398, -2), (key470, 2), (key573, 2), (key596, -2)]

theorem rowCheck4667 : row4667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4667 := by decide +kernel

theorem rowEval4667 (x : Key → ℝ) : Integer.Sparse.eval row4667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4667, Integer.Sparse.eval_collectBalanced, rawRowCheck4667]

def rawRow4668 : Integer.Sparse Key := [(key223, -2), (key226, -2), (key226, -2), (key226, 6), (key495, 2), (key498, 2), (key498, 2), (key498, -2), (key498, -2), (key552, -2), (key620, -6), (key620, 2), (key620, 2), (key646, 2)]

theorem rawRowCheck4668 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form8 = rawRow4668 := by decide +kernel

def row4668 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

theorem rowCheck4668 : row4668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4668 := by decide +kernel

theorem rowEval4668 (x : Key → ℝ) : Integer.Sparse.eval row4668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4668, Integer.Sparse.eval_collectBalanced, rawRowCheck4668]

def rawRow4669 : Integer.Sparse Key := [(key226, -2), (key223, -2), (key226, -2), (key226, 6), (key498, 2), (key495, 2), (key498, 2), (key498, -2), (key552, -2), (key498, -2), (key620, -6), (key620, 2), (key646, 2), (key620, 2)]

theorem rawRowCheck4669 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form8 = rawRow4669 := by decide +kernel

def row4669 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

theorem rowCheck4669 : row4669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4669 := by decide +kernel

theorem rowEval4669 (x : Key → ℝ) : Integer.Sparse.eval row4669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4669, Integer.Sparse.eval_collectBalanced, rawRowCheck4669]

def rawRow4670 : Integer.Sparse Key := [(key226, -2), (key226, -2), (key223, -2), (key226, 6), (key498, 2), (key498, 2), (key495, 2), (key552, -2), (key498, -2), (key498, -2), (key620, -6), (key646, 2), (key620, 2), (key620, 2)]

theorem rawRowCheck4670 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form8 = rawRow4670 := by decide +kernel

def row4670 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

theorem rowCheck4670 : row4670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4670 := by decide +kernel

theorem rowEval4670 (x : Key → ℝ) : Integer.Sparse.eval row4670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4670, Integer.Sparse.eval_collectBalanced, rawRowCheck4670]

def rawRow4671 : Integer.Sparse Key := [(key226, -2), (key226, -2), (key226, -2), (key223, 6), (key552, 2), (key552, 2), (key552, 2), (key495, -2), (key495, -2), (key495, -2), (key646, -6), (key620, 2), (key620, 2), (key620, 2)]

theorem rawRowCheck4671 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form8 = rawRow4671 := by decide +kernel

def row4671 : Integer.Sparse Key := [(key223, 6), (key226, -6), (key495, -6), (key552, 6), (key620, 6), (key646, -6)]

theorem rowCheck4671 : row4671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4671 := by decide +kernel

theorem rowEval4671 (x : Key → ℝ) : Integer.Sparse.eval row4671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4671, Integer.Sparse.eval_collectBalanced, rawRowCheck4671]

def rawRow4672 : Integer.Sparse Key := [(key495, -2), (key498, -2), (key498, -2), (key620, 6), (key223, 2), (key226, 2), (key226, 2), (key620, -2), (key620, -2), (key646, -2), (key226, -6), (key498, 2), (key498, 2), (key552, 2)]

theorem rawRowCheck4672 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form8 = rawRow4672 := by decide +kernel

def row4672 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

theorem rowCheck4672 : row4672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4672 := by decide +kernel

theorem rowEval4672 (x : Key → ℝ) : Integer.Sparse.eval row4672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4672, Integer.Sparse.eval_collectBalanced, rawRowCheck4672]

def rawRow4673 : Integer.Sparse Key := [(key498, -2), (key495, -2), (key498, -2), (key620, 6), (key226, 2), (key223, 2), (key226, 2), (key620, -2), (key646, -2), (key620, -2), (key226, -6), (key498, 2), (key552, 2), (key498, 2)]

theorem rawRowCheck4673 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form8 = rawRow4673 := by decide +kernel

def row4673 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

theorem rowCheck4673 : row4673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4673 := by decide +kernel

theorem rowEval4673 (x : Key → ℝ) : Integer.Sparse.eval row4673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4673, Integer.Sparse.eval_collectBalanced, rawRowCheck4673]

def rawRow4674 : Integer.Sparse Key := [(key498, -2), (key498, -2), (key495, -2), (key620, 6), (key226, 2), (key226, 2), (key223, 2), (key646, -2), (key620, -2), (key620, -2), (key226, -6), (key552, 2), (key498, 2), (key498, 2)]

theorem rawRowCheck4674 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form8 = rawRow4674 := by decide +kernel

def row4674 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

theorem rowCheck4674 : row4674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4674 := by decide +kernel

theorem rowEval4674 (x : Key → ℝ) : Integer.Sparse.eval row4674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4674, Integer.Sparse.eval_collectBalanced, rawRowCheck4674]

def rawRow4675 : Integer.Sparse Key := [(key498, -2), (key498, -2), (key620, -2), (key495, 6), (key552, 2), (key552, 2), (key646, 2), (key223, -2), (key495, -2), (key495, -2), (key552, -6), (key226, 2), (key498, 2), (key498, 2)]

theorem rawRowCheck4675 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form8 = rawRow4675 := by decide +kernel

def row4675 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

theorem rowCheck4675 : row4675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4675 := by decide +kernel

theorem rowEval4675 (x : Key → ℝ) : Integer.Sparse.eval row4675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4675, Integer.Sparse.eval_collectBalanced, rawRowCheck4675]

def rawRow4676 : Integer.Sparse Key := [(key498, -2), (key620, -2), (key498, -2), (key495, 6), (key552, 2), (key646, 2), (key552, 2), (key495, -2), (key223, -2), (key495, -2), (key552, -6), (key498, 2), (key226, 2), (key498, 2)]

theorem rawRowCheck4676 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form8 = rawRow4676 := by decide +kernel

def row4676 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

theorem rowCheck4676 : row4676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4676 := by decide +kernel

theorem rowEval4676 (x : Key → ℝ) : Integer.Sparse.eval row4676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4676, Integer.Sparse.eval_collectBalanced, rawRowCheck4676]

def rawRow4677 : Integer.Sparse Key := [(key620, -2), (key498, -2), (key498, -2), (key495, 6), (key646, 2), (key552, 2), (key552, 2), (key495, -2), (key495, -2), (key223, -2), (key552, -6), (key498, 2), (key498, 2), (key226, 2)]

theorem rawRowCheck4677 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form8 = rawRow4677 := by decide +kernel

def row4677 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

theorem rowCheck4677 : row4677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4677 := by decide +kernel

theorem rowEval4677 (x : Key → ℝ) : Integer.Sparse.eval row4677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4677, Integer.Sparse.eval_collectBalanced, rawRowCheck4677]

def rawRow4678 : Integer.Sparse Key := [(key552, -2), (key552, -2), (key552, -2), (key646, 6), (key226, 2), (key226, 2), (key226, 2), (key620, -2), (key620, -2), (key620, -2), (key223, -6), (key495, 2), (key495, 2), (key495, 2)]

theorem rawRowCheck4678 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form8 = rawRow4678 := by decide +kernel

def row4678 : Integer.Sparse Key := [(key223, -6), (key226, 6), (key495, 6), (key552, -6), (key620, -6), (key646, 6)]

theorem rowCheck4678 : row4678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4678 := by decide +kernel

theorem rowEval4678 (x : Key → ℝ) : Integer.Sparse.eval row4678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4678, Integer.Sparse.eval_collectBalanced, rawRowCheck4678]

def rawRow4679 : Integer.Sparse Key := [(key552, -2), (key552, -2), (key646, -2), (key552, 6), (key498, 2), (key498, 2), (key620, 2), (key226, -2), (key498, -2), (key498, -2), (key495, -6), (key223, 2), (key495, 2), (key495, 2)]

theorem rawRowCheck4679 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form8 = rawRow4679 := by decide +kernel

def row4679 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

theorem rowCheck4679 : row4679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4679 := by decide +kernel

theorem rowEval4679 (x : Key → ℝ) : Integer.Sparse.eval row4679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4679, Integer.Sparse.eval_collectBalanced, rawRowCheck4679]

def rawRow4680 : Integer.Sparse Key := [(key552, -2), (key646, -2), (key552, -2), (key552, 6), (key498, 2), (key620, 2), (key498, 2), (key498, -2), (key226, -2), (key498, -2), (key495, -6), (key495, 2), (key223, 2), (key495, 2)]

theorem rawRowCheck4680 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form8 = rawRow4680 := by decide +kernel

def row4680 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

theorem rowCheck4680 : row4680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4680 := by decide +kernel

theorem rowEval4680 (x : Key → ℝ) : Integer.Sparse.eval row4680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4680, Integer.Sparse.eval_collectBalanced, rawRowCheck4680]

def rawRow4681 : Integer.Sparse Key := [(key646, -2), (key552, -2), (key552, -2), (key552, 6), (key620, 2), (key498, 2), (key498, 2), (key498, -2), (key498, -2), (key226, -2), (key495, -6), (key495, 2), (key495, 2), (key223, 2)]

theorem rawRowCheck4681 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form8 = rawRow4681 := by decide +kernel

def row4681 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

theorem rowCheck4681 : row4681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4681 := by decide +kernel

theorem rowEval4681 (x : Key → ℝ) : Integer.Sparse.eval row4681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4681, Integer.Sparse.eval_collectBalanced, rawRowCheck4681]

def rawRow4682 : Integer.Sparse Key := [(key1366, -2), (key1366, -2), (key1379, -2), (key1366, 1), (key1370, 1), (key1366, 1), (key1379, 1), (key1370, 1), (key1379, 1), (key1718, 2), (key1718, 2), (key1728, 2), (key1718, -1), (key1728, -1), (key1718, -1), (key1747, -1), (key1728, -1), (key1747, -1), (key1863, -1), (key1865, -1), (key1863, -1), (key1870, -1), (key1865, -1), (key1870, -1), (key1863, 1), (key1870, 1), (key1863, 1), (key1880, 1), (key1870, 1), (key1880, 1)]

theorem rawRowCheck4682 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form9 = rawRow4682 := by decide +kernel

def row4682 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

theorem rowCheck4682 : row4682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4682 := by decide +kernel

theorem rowEval4682 (x : Key → ℝ) : Integer.Sparse.eval row4682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4682, Integer.Sparse.eval_collectBalanced, rawRowCheck4682]

def rawRow4683 : Integer.Sparse Key := [(key1366, -2), (key1379, -2), (key1366, -2), (key1370, 1), (key1366, 1), (key1379, 1), (key1366, 1), (key1379, 1), (key1370, 1), (key1718, 2), (key1728, 2), (key1718, 2), (key1728, -1), (key1718, -1), (key1747, -1), (key1718, -1), (key1747, -1), (key1728, -1), (key1865, -1), (key1863, -1), (key1870, -1), (key1863, -1), (key1870, -1), (key1865, -1), (key1870, 1), (key1863, 1), (key1880, 1), (key1863, 1), (key1880, 1), (key1870, 1)]

theorem rawRowCheck4683 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form9 = rawRow4683 := by decide +kernel

def row4683 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

theorem rowCheck4683 : row4683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4683 := by decide +kernel

theorem rowEval4683 (x : Key → ℝ) : Integer.Sparse.eval row4683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4683, Integer.Sparse.eval_collectBalanced, rawRowCheck4683]

def rawRow4684 : Integer.Sparse Key := [(key1379, -2), (key1366, -2), (key1366, -2), (key1379, 1), (key1379, 1), (key1370, 1), (key1370, 1), (key1366, 1), (key1366, 1), (key1728, 2), (key1718, 2), (key1718, 2), (key1747, -1), (key1747, -1), (key1728, -1), (key1728, -1), (key1718, -1), (key1718, -1), (key1870, -1), (key1870, -1), (key1865, -1), (key1865, -1), (key1863, -1), (key1863, -1), (key1880, 1), (key1880, 1), (key1870, 1), (key1870, 1), (key1863, 1), (key1863, 1)]

theorem rawRowCheck4684 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form9 = rawRow4684 := by decide +kernel

def row4684 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

theorem rowCheck4684 : row4684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4684 := by decide +kernel

theorem rowEval4684 (x : Key → ℝ) : Integer.Sparse.eval row4684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4684, Integer.Sparse.eval_collectBalanced, rawRowCheck4684]

def rawRow4685 : Integer.Sparse Key := [(key1370, -2), (key1370, -2), (key1370, -2), (key1366, 1), (key1366, 1), (key1366, 1), (key1366, 1), (key1366, 1), (key1366, 1), (key1747, 2), (key1747, 2), (key1747, 2), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1880, -1), (key1880, -1), (key1880, -1), (key1880, -1), (key1880, -1), (key1880, -1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1)]

theorem rawRowCheck4685 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form9 = rawRow4685 := by decide +kernel

def row4685 : Integer.Sparse Key := [(key1366, 6), (key1370, -6), (key1718, -6), (key1747, 6), (key1865, 6), (key1880, -6)]

theorem rowCheck4685 : row4685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4685 := by decide +kernel

theorem rowEval4685 (x : Key → ℝ) : Integer.Sparse.eval row4685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4685, Integer.Sparse.eval_collectBalanced, rawRowCheck4685]

def rawRow4686 : Integer.Sparse Key := [(key1718, -2), (key1718, -2), (key1728, -2), (key1863, 1), (key1865, 1), (key1863, 1), (key1870, 1), (key1865, 1), (key1870, 1), (key1366, 2), (key1366, 2), (key1379, 2), (key1863, -1), (key1870, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1880, -1), (key1366, -1), (key1370, -1), (key1366, -1), (key1379, -1), (key1370, -1), (key1379, -1), (key1718, 1), (key1728, 1), (key1718, 1), (key1747, 1), (key1728, 1), (key1747, 1)]

theorem rawRowCheck4686 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form9 = rawRow4686 := by decide +kernel

def row4686 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

theorem rowCheck4686 : row4686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4686 := by decide +kernel

theorem rowEval4686 (x : Key → ℝ) : Integer.Sparse.eval row4686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4686, Integer.Sparse.eval_collectBalanced, rawRowCheck4686]

def rawRow4687 : Integer.Sparse Key := [(key1718, -2), (key1728, -2), (key1718, -2), (key1865, 1), (key1863, 1), (key1870, 1), (key1863, 1), (key1870, 1), (key1865, 1), (key1366, 2), (key1379, 2), (key1366, 2), (key1870, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1370, -1), (key1366, -1), (key1379, -1), (key1366, -1), (key1379, -1), (key1370, -1), (key1728, 1), (key1718, 1), (key1747, 1), (key1718, 1), (key1747, 1), (key1728, 1)]

theorem rawRowCheck4687 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form9 = rawRow4687 := by decide +kernel

def row4687 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

theorem rowCheck4687 : row4687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4687 := by decide +kernel

theorem rowEval4687 (x : Key → ℝ) : Integer.Sparse.eval row4687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4687, Integer.Sparse.eval_collectBalanced, rawRowCheck4687]

def rawRow4688 : Integer.Sparse Key := [(key1728, -2), (key1718, -2), (key1718, -2), (key1870, 1), (key1870, 1), (key1865, 1), (key1865, 1), (key1863, 1), (key1863, 1), (key1379, 2), (key1366, 2), (key1366, 2), (key1880, -1), (key1880, -1), (key1870, -1), (key1870, -1), (key1863, -1), (key1863, -1), (key1379, -1), (key1379, -1), (key1370, -1), (key1370, -1), (key1366, -1), (key1366, -1), (key1747, 1), (key1747, 1), (key1728, 1), (key1728, 1), (key1718, 1), (key1718, 1)]

theorem rawRowCheck4688 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form9 = rawRow4688 := by decide +kernel

def row4688 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

theorem rowCheck4688 : row4688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4688 := by decide +kernel

theorem rowEval4688 (x : Key → ℝ) : Integer.Sparse.eval row4688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4688, Integer.Sparse.eval_collectBalanced, rawRowCheck4688]

def rawRow4689 : Integer.Sparse Key := [(key1496, -2), (key1865, -2), (key1865, -2), (key1492, 1), (key1492, 1), (key1718, 1), (key1718, 1), (key1863, 1), (key1863, 1), (key1519, 2), (key1880, 2), (key1880, 2), (key1366, -1), (key1366, -1), (key1492, -1), (key1492, -1), (key1863, -1), (key1863, -1), (key1519, -1), (key1519, -1), (key1747, -1), (key1747, -1), (key1880, -1), (key1880, -1), (key1370, 1), (key1370, 1), (key1496, 1), (key1496, 1), (key1865, 1), (key1865, 1)]

theorem rawRowCheck4689 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form9 = rawRow4689 := by decide +kernel

def row4689 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

theorem rowCheck4689 : row4689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4689 := by decide +kernel

theorem rowEval4689 (x : Key → ℝ) : Integer.Sparse.eval row4689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4689, Integer.Sparse.eval_collectBalanced, rawRowCheck4689]

def rawRow4690 : Integer.Sparse Key := [(key1865, -2), (key1496, -2), (key1865, -2), (key1718, 1), (key1863, 1), (key1492, 1), (key1863, 1), (key1492, 1), (key1718, 1), (key1880, 2), (key1519, 2), (key1880, 2), (key1492, -1), (key1863, -1), (key1366, -1), (key1863, -1), (key1366, -1), (key1492, -1), (key1747, -1), (key1880, -1), (key1519, -1), (key1880, -1), (key1519, -1), (key1747, -1), (key1496, 1), (key1865, 1), (key1370, 1), (key1865, 1), (key1370, 1), (key1496, 1)]

theorem rawRowCheck4690 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form9 = rawRow4690 := by decide +kernel

def row4690 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

theorem rowCheck4690 : row4690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4690 := by decide +kernel

theorem rowEval4690 (x : Key → ℝ) : Integer.Sparse.eval row4690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4690, Integer.Sparse.eval_collectBalanced, rawRowCheck4690]

def rawRow4691 : Integer.Sparse Key := [(key1865, -2), (key1865, -2), (key1496, -2), (key1863, 1), (key1718, 1), (key1863, 1), (key1492, 1), (key1718, 1), (key1492, 1), (key1880, 2), (key1880, 2), (key1519, 2), (key1863, -1), (key1492, -1), (key1863, -1), (key1366, -1), (key1492, -1), (key1366, -1), (key1880, -1), (key1747, -1), (key1880, -1), (key1519, -1), (key1747, -1), (key1519, -1), (key1865, 1), (key1496, 1), (key1865, 1), (key1370, 1), (key1496, 1), (key1370, 1)]

theorem rawRowCheck4691 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form9 = rawRow4691 := by decide +kernel

def row4691 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

theorem rowCheck4691 : row4691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4691 := by decide +kernel

theorem rowEval4691 (x : Key → ℝ) : Integer.Sparse.eval row4691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4691, Integer.Sparse.eval_collectBalanced, rawRowCheck4691]

def rawRow4692 : Integer.Sparse Key := [(key1747, -2), (key1747, -2), (key1747, -2), (key1880, 1), (key1880, 1), (key1880, 1), (key1880, 1), (key1880, 1), (key1880, 1), (key1370, 2), (key1370, 2), (key1370, 2), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1366, -1), (key1366, -1), (key1366, -1), (key1366, -1), (key1366, -1), (key1366, -1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1)]

theorem rawRowCheck4692 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form9 = rawRow4692 := by decide +kernel

def row4692 : Integer.Sparse Key := [(key1366, -6), (key1370, 6), (key1718, 6), (key1747, -6), (key1865, -6), (key1880, 6)]

theorem rowCheck4692 : row4692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4692 := by decide +kernel

theorem rowEval4692 (x : Key → ℝ) : Integer.Sparse.eval row4692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4692, Integer.Sparse.eval_collectBalanced, rawRowCheck4692]

def rawRow4693 : Integer.Sparse Key := [(key1519, -2), (key1880, -2), (key1880, -2), (key1519, 1), (key1519, 1), (key1747, 1), (key1747, 1), (key1880, 1), (key1880, 1), (key1496, 2), (key1865, 2), (key1865, 2), (key1370, -1), (key1370, -1), (key1496, -1), (key1496, -1), (key1865, -1), (key1865, -1), (key1492, -1), (key1492, -1), (key1718, -1), (key1718, -1), (key1863, -1), (key1863, -1), (key1366, 1), (key1366, 1), (key1492, 1), (key1492, 1), (key1863, 1), (key1863, 1)]

theorem rawRowCheck4693 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form9 = rawRow4693 := by decide +kernel

def row4693 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

theorem rowCheck4693 : row4693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4693 := by decide +kernel

theorem rowEval4693 (x : Key → ℝ) : Integer.Sparse.eval row4693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4693, Integer.Sparse.eval_collectBalanced, rawRowCheck4693]

def rawRow4694 : Integer.Sparse Key := [(key1880, -2), (key1519, -2), (key1880, -2), (key1747, 1), (key1880, 1), (key1519, 1), (key1880, 1), (key1519, 1), (key1747, 1), (key1865, 2), (key1496, 2), (key1865, 2), (key1496, -1), (key1865, -1), (key1370, -1), (key1865, -1), (key1370, -1), (key1496, -1), (key1718, -1), (key1863, -1), (key1492, -1), (key1863, -1), (key1492, -1), (key1718, -1), (key1492, 1), (key1863, 1), (key1366, 1), (key1863, 1), (key1366, 1), (key1492, 1)]

theorem rawRowCheck4694 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form9 = rawRow4694 := by decide +kernel

def row4694 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

theorem rowCheck4694 : row4694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4694 := by decide +kernel

theorem rowEval4694 (x : Key → ℝ) : Integer.Sparse.eval row4694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4694, Integer.Sparse.eval_collectBalanced, rawRowCheck4694]

def rawRow4695 : Integer.Sparse Key := [(key1880, -2), (key1880, -2), (key1519, -2), (key1880, 1), (key1747, 1), (key1880, 1), (key1519, 1), (key1747, 1), (key1519, 1), (key1865, 2), (key1865, 2), (key1496, 2), (key1865, -1), (key1496, -1), (key1865, -1), (key1370, -1), (key1496, -1), (key1370, -1), (key1863, -1), (key1718, -1), (key1863, -1), (key1492, -1), (key1718, -1), (key1492, -1), (key1863, 1), (key1492, 1), (key1863, 1), (key1366, 1), (key1492, 1), (key1366, 1)]

theorem rawRowCheck4695 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form9 = rawRow4695 := by decide +kernel

def row4695 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

theorem rowCheck4695 : row4695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4695 := by decide +kernel

theorem rowEval4695 (x : Key → ℝ) : Integer.Sparse.eval row4695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4695, Integer.Sparse.eval_collectBalanced, rawRowCheck4695]

def rawRow4696 : Integer.Sparse Key := [(key1276, -2), (key1281, -2), (key1281, -2), (key1281, 6), (key1699, 2), (key1704, 2), (key1704, 2), (key1704, -2), (key1704, -2), (key1753, -2), (key1934, -6), (key1934, 2), (key1934, 2), (key1954, 2)]

theorem rawRowCheck4696 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form10 = rawRow4696 := by decide +kernel

def row4696 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

theorem rowCheck4696 : row4696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4696 := by decide +kernel

theorem rowEval4696 (x : Key → ℝ) : Integer.Sparse.eval row4696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4696, Integer.Sparse.eval_collectBalanced, rawRowCheck4696]

def rawRow4697 : Integer.Sparse Key := [(key1281, -2), (key1276, -2), (key1281, -2), (key1281, 6), (key1704, 2), (key1699, 2), (key1704, 2), (key1704, -2), (key1753, -2), (key1704, -2), (key1934, -6), (key1934, 2), (key1954, 2), (key1934, 2)]

theorem rawRowCheck4697 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form10 = rawRow4697 := by decide +kernel

def row4697 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

theorem rowCheck4697 : row4697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4697 := by decide +kernel

theorem rowEval4697 (x : Key → ℝ) : Integer.Sparse.eval row4697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4697, Integer.Sparse.eval_collectBalanced, rawRowCheck4697]

def rawRow4698 : Integer.Sparse Key := [(key1281, -2), (key1281, -2), (key1276, -2), (key1281, 6), (key1704, 2), (key1704, 2), (key1699, 2), (key1753, -2), (key1704, -2), (key1704, -2), (key1934, -6), (key1954, 2), (key1934, 2), (key1934, 2)]

theorem rawRowCheck4698 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form10 = rawRow4698 := by decide +kernel

def row4698 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

theorem rowCheck4698 : row4698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4698 := by decide +kernel

theorem rowEval4698 (x : Key → ℝ) : Integer.Sparse.eval row4698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4698, Integer.Sparse.eval_collectBalanced, rawRowCheck4698]

def rawRow4699 : Integer.Sparse Key := [(key1281, -2), (key1281, -2), (key1281, -2), (key1276, 6), (key1753, 2), (key1753, 2), (key1753, 2), (key1699, -2), (key1699, -2), (key1699, -2), (key1954, -6), (key1934, 2), (key1934, 2), (key1934, 2)]

theorem rawRowCheck4699 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form10 = rawRow4699 := by decide +kernel

def row4699 : Integer.Sparse Key := [(key1276, 6), (key1281, -6), (key1699, -6), (key1753, 6), (key1934, 6), (key1954, -6)]

theorem rowCheck4699 : row4699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4699 := by decide +kernel

theorem rowEval4699 (x : Key → ℝ) : Integer.Sparse.eval row4699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4699, Integer.Sparse.eval_collectBalanced, rawRowCheck4699]

def rawRow4700 : Integer.Sparse Key := [(key1699, -2), (key1704, -2), (key1704, -2), (key1934, 6), (key1276, 2), (key1281, 2), (key1281, 2), (key1934, -2), (key1934, -2), (key1954, -2), (key1281, -6), (key1704, 2), (key1704, 2), (key1753, 2)]

theorem rawRowCheck4700 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form10 = rawRow4700 := by decide +kernel

def row4700 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

theorem rowCheck4700 : row4700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4700 := by decide +kernel

theorem rowEval4700 (x : Key → ℝ) : Integer.Sparse.eval row4700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4700, Integer.Sparse.eval_collectBalanced, rawRowCheck4700]

def rawRow4701 : Integer.Sparse Key := [(key1704, -2), (key1699, -2), (key1704, -2), (key1934, 6), (key1281, 2), (key1276, 2), (key1281, 2), (key1934, -2), (key1954, -2), (key1934, -2), (key1281, -6), (key1704, 2), (key1753, 2), (key1704, 2)]

theorem rawRowCheck4701 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form10 = rawRow4701 := by decide +kernel

def row4701 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

theorem rowCheck4701 : row4701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4701 := by decide +kernel

theorem rowEval4701 (x : Key → ℝ) : Integer.Sparse.eval row4701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4701, Integer.Sparse.eval_collectBalanced, rawRowCheck4701]

def rawRow4702 : Integer.Sparse Key := [(key1704, -2), (key1704, -2), (key1699, -2), (key1934, 6), (key1281, 2), (key1281, 2), (key1276, 2), (key1954, -2), (key1934, -2), (key1934, -2), (key1281, -6), (key1753, 2), (key1704, 2), (key1704, 2)]

theorem rawRowCheck4702 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form10 = rawRow4702 := by decide +kernel

def row4702 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

theorem rowCheck4702 : row4702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4702 := by decide +kernel

theorem rowEval4702 (x : Key → ℝ) : Integer.Sparse.eval row4702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4702, Integer.Sparse.eval_collectBalanced, rawRowCheck4702]

def rawRow4703 : Integer.Sparse Key := [(key1704, -2), (key1704, -2), (key1934, -2), (key1699, 6), (key1753, 2), (key1753, 2), (key1954, 2), (key1276, -2), (key1699, -2), (key1699, -2), (key1753, -6), (key1281, 2), (key1704, 2), (key1704, 2)]

theorem rawRowCheck4703 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form10 = rawRow4703 := by decide +kernel

def row4703 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

theorem rowCheck4703 : row4703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4703 := by decide +kernel

theorem rowEval4703 (x : Key → ℝ) : Integer.Sparse.eval row4703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4703, Integer.Sparse.eval_collectBalanced, rawRowCheck4703]

def rawRow4704 : Integer.Sparse Key := [(key1704, -2), (key1934, -2), (key1704, -2), (key1699, 6), (key1753, 2), (key1954, 2), (key1753, 2), (key1699, -2), (key1276, -2), (key1699, -2), (key1753, -6), (key1704, 2), (key1281, 2), (key1704, 2)]

theorem rawRowCheck4704 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form10 = rawRow4704 := by decide +kernel

def row4704 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

theorem rowCheck4704 : row4704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4704 := by decide +kernel

theorem rowEval4704 (x : Key → ℝ) : Integer.Sparse.eval row4704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4704, Integer.Sparse.eval_collectBalanced, rawRowCheck4704]

def rawRow4705 : Integer.Sparse Key := [(key1934, -2), (key1704, -2), (key1704, -2), (key1699, 6), (key1954, 2), (key1753, 2), (key1753, 2), (key1699, -2), (key1699, -2), (key1276, -2), (key1753, -6), (key1704, 2), (key1704, 2), (key1281, 2)]

theorem rawRowCheck4705 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form10 = rawRow4705 := by decide +kernel

def row4705 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

theorem rowCheck4705 : row4705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4705 := by decide +kernel

theorem rowEval4705 (x : Key → ℝ) : Integer.Sparse.eval row4705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4705, Integer.Sparse.eval_collectBalanced, rawRowCheck4705]

def rawRow4706 : Integer.Sparse Key := [(key1753, -2), (key1753, -2), (key1753, -2), (key1954, 6), (key1281, 2), (key1281, 2), (key1281, 2), (key1934, -2), (key1934, -2), (key1934, -2), (key1276, -6), (key1699, 2), (key1699, 2), (key1699, 2)]

theorem rawRowCheck4706 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form10 = rawRow4706 := by decide +kernel

def row4706 : Integer.Sparse Key := [(key1276, -6), (key1281, 6), (key1699, 6), (key1753, -6), (key1934, -6), (key1954, 6)]

theorem rowCheck4706 : row4706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4706 := by decide +kernel

theorem rowEval4706 (x : Key → ℝ) : Integer.Sparse.eval row4706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4706, Integer.Sparse.eval_collectBalanced, rawRowCheck4706]

def rawRow4707 : Integer.Sparse Key := [(key1753, -2), (key1753, -2), (key1954, -2), (key1753, 6), (key1704, 2), (key1704, 2), (key1934, 2), (key1281, -2), (key1704, -2), (key1704, -2), (key1699, -6), (key1276, 2), (key1699, 2), (key1699, 2)]

theorem rawRowCheck4707 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form10 = rawRow4707 := by decide +kernel

def row4707 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

theorem rowCheck4707 : row4707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4707 := by decide +kernel

theorem rowEval4707 (x : Key → ℝ) : Integer.Sparse.eval row4707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4707, Integer.Sparse.eval_collectBalanced, rawRowCheck4707]

def rawRow4708 : Integer.Sparse Key := [(key1753, -2), (key1954, -2), (key1753, -2), (key1753, 6), (key1704, 2), (key1934, 2), (key1704, 2), (key1704, -2), (key1281, -2), (key1704, -2), (key1699, -6), (key1699, 2), (key1276, 2), (key1699, 2)]

theorem rawRowCheck4708 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form10 = rawRow4708 := by decide +kernel

def row4708 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

theorem rowCheck4708 : row4708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4708 := by decide +kernel

theorem rowEval4708 (x : Key → ℝ) : Integer.Sparse.eval row4708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4708, Integer.Sparse.eval_collectBalanced, rawRowCheck4708]

def rawRow4709 : Integer.Sparse Key := [(key1954, -2), (key1753, -2), (key1753, -2), (key1753, 6), (key1934, 2), (key1704, 2), (key1704, 2), (key1704, -2), (key1704, -2), (key1281, -2), (key1699, -6), (key1699, 2), (key1699, 2), (key1276, 2)]

theorem rawRowCheck4709 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form10 = rawRow4709 := by decide +kernel

def row4709 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

theorem rowCheck4709 : row4709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4709 := by decide +kernel

theorem rowEval4709 (x : Key → ℝ) : Integer.Sparse.eval row4709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4709, Integer.Sparse.eval_collectBalanced, rawRowCheck4709]

def rawRow4710 : Integer.Sparse Key := [(key1276, -2), (key1279, -2), (key1279, -2), (key1279, 6), (key1699, 2), (key1702, 2), (key1702, 2), (key1702, -2), (key1702, -2), (key1752, -2), (key1853, -6), (key1853, 2), (key1853, 2), (key1885, 2)]

theorem rawRowCheck4710 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form11 = rawRow4710 := by decide +kernel

def row4710 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

theorem rowCheck4710 : row4710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4710 := by decide +kernel

theorem rowEval4710 (x : Key → ℝ) : Integer.Sparse.eval row4710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4710, Integer.Sparse.eval_collectBalanced, rawRowCheck4710]

def rawRow4711 : Integer.Sparse Key := [(key1279, -2), (key1276, -2), (key1279, -2), (key1279, 6), (key1702, 2), (key1699, 2), (key1702, 2), (key1702, -2), (key1752, -2), (key1702, -2), (key1853, -6), (key1853, 2), (key1885, 2), (key1853, 2)]

theorem rawRowCheck4711 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form11 = rawRow4711 := by decide +kernel

def row4711 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

theorem rowCheck4711 : row4711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4711 := by decide +kernel

theorem rowEval4711 (x : Key → ℝ) : Integer.Sparse.eval row4711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4711, Integer.Sparse.eval_collectBalanced, rawRowCheck4711]

def rawRow4712 : Integer.Sparse Key := [(key1279, -2), (key1279, -2), (key1276, -2), (key1279, 6), (key1702, 2), (key1702, 2), (key1699, 2), (key1752, -2), (key1702, -2), (key1702, -2), (key1853, -6), (key1885, 2), (key1853, 2), (key1853, 2)]

theorem rawRowCheck4712 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form11 = rawRow4712 := by decide +kernel

def row4712 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

theorem rowCheck4712 : row4712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4712 := by decide +kernel

theorem rowEval4712 (x : Key → ℝ) : Integer.Sparse.eval row4712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4712, Integer.Sparse.eval_collectBalanced, rawRowCheck4712]

def rawRow4713 : Integer.Sparse Key := [(key1279, -2), (key1279, -2), (key1279, -2), (key1276, 6), (key1752, 2), (key1752, 2), (key1752, 2), (key1699, -2), (key1699, -2), (key1699, -2), (key1885, -6), (key1853, 2), (key1853, 2), (key1853, 2)]

theorem rawRowCheck4713 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form11 = rawRow4713 := by decide +kernel

def row4713 : Integer.Sparse Key := [(key1276, 6), (key1279, -6), (key1699, -6), (key1752, 6), (key1853, 6), (key1885, -6)]

theorem rowCheck4713 : row4713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4713 := by decide +kernel

theorem rowEval4713 (x : Key → ℝ) : Integer.Sparse.eval row4713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4713, Integer.Sparse.eval_collectBalanced, rawRowCheck4713]

def rawRow4714 : Integer.Sparse Key := [(key1699, -2), (key1702, -2), (key1702, -2), (key1853, 6), (key1276, 2), (key1279, 2), (key1279, 2), (key1853, -2), (key1853, -2), (key1885, -2), (key1279, -6), (key1702, 2), (key1702, 2), (key1752, 2)]

theorem rawRowCheck4714 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form11 = rawRow4714 := by decide +kernel

def row4714 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

theorem rowCheck4714 : row4714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4714 := by decide +kernel

theorem rowEval4714 (x : Key → ℝ) : Integer.Sparse.eval row4714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4714, Integer.Sparse.eval_collectBalanced, rawRowCheck4714]

def rawRow4715 : Integer.Sparse Key := [(key1702, -2), (key1699, -2), (key1702, -2), (key1853, 6), (key1279, 2), (key1276, 2), (key1279, 2), (key1853, -2), (key1885, -2), (key1853, -2), (key1279, -6), (key1702, 2), (key1752, 2), (key1702, 2)]

theorem rawRowCheck4715 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form11 = rawRow4715 := by decide +kernel

def row4715 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

theorem rowCheck4715 : row4715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4715 := by decide +kernel

theorem rowEval4715 (x : Key → ℝ) : Integer.Sparse.eval row4715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4715, Integer.Sparse.eval_collectBalanced, rawRowCheck4715]

def rawRow4716 : Integer.Sparse Key := [(key1702, -2), (key1702, -2), (key1699, -2), (key1853, 6), (key1279, 2), (key1279, 2), (key1276, 2), (key1885, -2), (key1853, -2), (key1853, -2), (key1279, -6), (key1752, 2), (key1702, 2), (key1702, 2)]

theorem rawRowCheck4716 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form11 = rawRow4716 := by decide +kernel

def row4716 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

theorem rowCheck4716 : row4716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4716 := by decide +kernel

theorem rowEval4716 (x : Key → ℝ) : Integer.Sparse.eval row4716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4716, Integer.Sparse.eval_collectBalanced, rawRowCheck4716]

def rawRow4717 : Integer.Sparse Key := [(key1702, -2), (key1702, -2), (key1853, -2), (key1699, 6), (key1752, 2), (key1752, 2), (key1885, 2), (key1276, -2), (key1699, -2), (key1699, -2), (key1752, -6), (key1279, 2), (key1702, 2), (key1702, 2)]

theorem rawRowCheck4717 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form11 = rawRow4717 := by decide +kernel

def row4717 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

theorem rowCheck4717 : row4717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4717 := by decide +kernel

theorem rowEval4717 (x : Key → ℝ) : Integer.Sparse.eval row4717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4717, Integer.Sparse.eval_collectBalanced, rawRowCheck4717]

def rawRow4718 : Integer.Sparse Key := [(key1702, -2), (key1853, -2), (key1702, -2), (key1699, 6), (key1752, 2), (key1885, 2), (key1752, 2), (key1699, -2), (key1276, -2), (key1699, -2), (key1752, -6), (key1702, 2), (key1279, 2), (key1702, 2)]

theorem rawRowCheck4718 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form11 = rawRow4718 := by decide +kernel

def row4718 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

theorem rowCheck4718 : row4718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4718 := by decide +kernel

theorem rowEval4718 (x : Key → ℝ) : Integer.Sparse.eval row4718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4718, Integer.Sparse.eval_collectBalanced, rawRowCheck4718]

def rawRow4719 : Integer.Sparse Key := [(key1853, -2), (key1702, -2), (key1702, -2), (key1699, 6), (key1885, 2), (key1752, 2), (key1752, 2), (key1699, -2), (key1699, -2), (key1276, -2), (key1752, -6), (key1702, 2), (key1702, 2), (key1279, 2)]

theorem rawRowCheck4719 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form11 = rawRow4719 := by decide +kernel

def row4719 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

theorem rowCheck4719 : row4719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4719 := by decide +kernel

theorem rowEval4719 (x : Key → ℝ) : Integer.Sparse.eval row4719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4719, Integer.Sparse.eval_collectBalanced, rawRowCheck4719]

def rawRow4720 : Integer.Sparse Key := [(key1752, -2), (key1752, -2), (key1752, -2), (key1885, 6), (key1279, 2), (key1279, 2), (key1279, 2), (key1853, -2), (key1853, -2), (key1853, -2), (key1276, -6), (key1699, 2), (key1699, 2), (key1699, 2)]

theorem rawRowCheck4720 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form11 = rawRow4720 := by decide +kernel

def row4720 : Integer.Sparse Key := [(key1276, -6), (key1279, 6), (key1699, 6), (key1752, -6), (key1853, -6), (key1885, 6)]

theorem rowCheck4720 : row4720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4720 := by decide +kernel

theorem rowEval4720 (x : Key → ℝ) : Integer.Sparse.eval row4720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4720, Integer.Sparse.eval_collectBalanced, rawRowCheck4720]

def rawRow4721 : Integer.Sparse Key := [(key1752, -2), (key1752, -2), (key1885, -2), (key1752, 6), (key1702, 2), (key1702, 2), (key1853, 2), (key1279, -2), (key1702, -2), (key1702, -2), (key1699, -6), (key1276, 2), (key1699, 2), (key1699, 2)]

theorem rawRowCheck4721 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form11 = rawRow4721 := by decide +kernel

def row4721 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

theorem rowCheck4721 : row4721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4721 := by decide +kernel

theorem rowEval4721 (x : Key → ℝ) : Integer.Sparse.eval row4721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4721, Integer.Sparse.eval_collectBalanced, rawRowCheck4721]

def rawRow4722 : Integer.Sparse Key := [(key1752, -2), (key1885, -2), (key1752, -2), (key1752, 6), (key1702, 2), (key1853, 2), (key1702, 2), (key1702, -2), (key1279, -2), (key1702, -2), (key1699, -6), (key1699, 2), (key1276, 2), (key1699, 2)]

theorem rawRowCheck4722 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form11 = rawRow4722 := by decide +kernel

def row4722 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

theorem rowCheck4722 : row4722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4722 := by decide +kernel

theorem rowEval4722 (x : Key → ℝ) : Integer.Sparse.eval row4722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4722, Integer.Sparse.eval_collectBalanced, rawRowCheck4722]

def rawRow4723 : Integer.Sparse Key := [(key1885, -2), (key1752, -2), (key1752, -2), (key1752, 6), (key1853, 2), (key1702, 2), (key1702, 2), (key1702, -2), (key1702, -2), (key1279, -2), (key1699, -6), (key1699, 2), (key1699, 2), (key1276, 2)]

theorem rawRowCheck4723 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form11 = rawRow4723 := by decide +kernel

def row4723 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

theorem rowCheck4723 : row4723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4723 := by decide +kernel

theorem rowEval4723 (x : Key → ℝ) : Integer.Sparse.eval row4723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4723, Integer.Sparse.eval_collectBalanced, rawRowCheck4723]

def rawRow4724 : Integer.Sparse Key := [(key1362, -2), (key1365, -2), (key1365, -2), (key1362, 1), (key1365, 1), (key1362, 1), (key1375, 1), (key1365, 1), (key1375, 1), (key1488, 2), (key1491, 2), (key1491, 2), (key1488, -1), (key1491, -1), (key1488, -1), (key1514, -1), (key1491, -1), (key1514, -1), (key1714, -1), (key1717, -1), (key1714, -1), (key1724, -1), (key1717, -1), (key1724, -1), (key1714, 1), (key1717, 1), (key1714, 1), (key1742, 1), (key1717, 1), (key1742, 1)]

theorem rawRowCheck4724 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form12 = rawRow4724 := by decide +kernel

def row4724 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

theorem rowCheck4724 : row4724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4724 := by decide +kernel

theorem rowEval4724 (x : Key → ℝ) : Integer.Sparse.eval row4724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4724, Integer.Sparse.eval_collectBalanced, rawRowCheck4724]

def rawRow4725 : Integer.Sparse Key := [(key1365, -2), (key1362, -2), (key1365, -2), (key1365, 1), (key1362, 1), (key1375, 1), (key1362, 1), (key1375, 1), (key1365, 1), (key1491, 2), (key1488, 2), (key1491, 2), (key1491, -1), (key1488, -1), (key1514, -1), (key1488, -1), (key1514, -1), (key1491, -1), (key1717, -1), (key1714, -1), (key1724, -1), (key1714, -1), (key1724, -1), (key1717, -1), (key1717, 1), (key1714, 1), (key1742, 1), (key1714, 1), (key1742, 1), (key1717, 1)]

theorem rawRowCheck4725 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form12 = rawRow4725 := by decide +kernel

def row4725 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

theorem rowCheck4725 : row4725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4725 := by decide +kernel

theorem rowEval4725 (x : Key → ℝ) : Integer.Sparse.eval row4725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4725, Integer.Sparse.eval_collectBalanced, rawRowCheck4725]

def rawRow4726 : Integer.Sparse Key := [(key1365, -2), (key1365, -2), (key1362, -2), (key1375, 1), (key1375, 1), (key1365, 1), (key1365, 1), (key1362, 1), (key1362, 1), (key1491, 2), (key1491, 2), (key1488, 2), (key1514, -1), (key1514, -1), (key1491, -1), (key1491, -1), (key1488, -1), (key1488, -1), (key1724, -1), (key1724, -1), (key1717, -1), (key1717, -1), (key1714, -1), (key1714, -1), (key1742, 1), (key1742, 1), (key1717, 1), (key1717, 1), (key1714, 1), (key1714, 1)]

theorem rawRowCheck4726 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form12 = rawRow4726 := by decide +kernel

def row4726 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

theorem rowCheck4726 : row4726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4726 := by decide +kernel

theorem rowEval4726 (x : Key → ℝ) : Integer.Sparse.eval row4726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4726, Integer.Sparse.eval_collectBalanced, rawRowCheck4726]

def rawRow4727 : Integer.Sparse Key := [(key1375, -2), (key1375, -2), (key1375, -2), (key1365, 1), (key1365, 1), (key1365, 1), (key1365, 1), (key1365, 1), (key1365, 1), (key1514, 2), (key1514, 2), (key1514, 2), (key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1742, -1), (key1742, -1), (key1742, -1), (key1742, -1), (key1742, -1), (key1742, -1), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1)]

theorem rawRowCheck4727 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form12 = rawRow4727 := by decide +kernel

def row4727 : Integer.Sparse Key := [(key1365, 6), (key1375, -6), (key1491, -6), (key1514, 6), (key1724, 6), (key1742, -6)]

theorem rowCheck4727 : row4727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4727 := by decide +kernel

theorem rowEval4727 (x : Key → ℝ) : Integer.Sparse.eval row4727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4727, Integer.Sparse.eval_collectBalanced, rawRowCheck4727]

def rawRow4728 : Integer.Sparse Key := [(key1488, -2), (key1491, -2), (key1491, -2), (key1714, 1), (key1717, 1), (key1714, 1), (key1724, 1), (key1717, 1), (key1724, 1), (key1362, 2), (key1365, 2), (key1365, 2), (key1714, -1), (key1717, -1), (key1714, -1), (key1742, -1), (key1717, -1), (key1742, -1), (key1362, -1), (key1365, -1), (key1362, -1), (key1375, -1), (key1365, -1), (key1375, -1), (key1488, 1), (key1491, 1), (key1488, 1), (key1514, 1), (key1491, 1), (key1514, 1)]

theorem rawRowCheck4728 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form12 = rawRow4728 := by decide +kernel

def row4728 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

theorem rowCheck4728 : row4728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4728 := by decide +kernel

theorem rowEval4728 (x : Key → ℝ) : Integer.Sparse.eval row4728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4728, Integer.Sparse.eval_collectBalanced, rawRowCheck4728]

def rawRow4729 : Integer.Sparse Key := [(key1491, -2), (key1488, -2), (key1491, -2), (key1717, 1), (key1714, 1), (key1724, 1), (key1714, 1), (key1724, 1), (key1717, 1), (key1365, 2), (key1362, 2), (key1365, 2), (key1717, -1), (key1714, -1), (key1742, -1), (key1714, -1), (key1742, -1), (key1717, -1), (key1365, -1), (key1362, -1), (key1375, -1), (key1362, -1), (key1375, -1), (key1365, -1), (key1491, 1), (key1488, 1), (key1514, 1), (key1488, 1), (key1514, 1), (key1491, 1)]

theorem rawRowCheck4729 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form12 = rawRow4729 := by decide +kernel

def row4729 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

theorem rowCheck4729 : row4729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4729 := by decide +kernel

theorem rowEval4729 (x : Key → ℝ) : Integer.Sparse.eval row4729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4729, Integer.Sparse.eval_collectBalanced, rawRowCheck4729]

def rawRow4730 : Integer.Sparse Key := [(key1491, -2), (key1491, -2), (key1488, -2), (key1724, 1), (key1724, 1), (key1717, 1), (key1717, 1), (key1714, 1), (key1714, 1), (key1365, 2), (key1365, 2), (key1362, 2), (key1742, -1), (key1742, -1), (key1717, -1), (key1717, -1), (key1714, -1), (key1714, -1), (key1375, -1), (key1375, -1), (key1365, -1), (key1365, -1), (key1362, -1), (key1362, -1), (key1514, 1), (key1514, 1), (key1491, 1), (key1491, 1), (key1488, 1), (key1488, 1)]

theorem rawRowCheck4730 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form12 = rawRow4730 := by decide +kernel

def row4730 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

theorem rowCheck4730 : row4730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4730 := by decide +kernel

theorem rowEval4730 (x : Key → ℝ) : Integer.Sparse.eval row4730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4730, Integer.Sparse.eval_collectBalanced, rawRowCheck4730]

def rawRow4731 : Integer.Sparse Key := [(key1724, -2), (key1724, -2), (key1868, -2), (key1491, 1), (key1491, 1), (key1717, 1), (key1717, 1), (key1862, 1), (key1862, 1), (key1742, 2), (key1742, 2), (key1878, 2), (key1365, -1), (key1365, -1), (key1717, -1), (key1717, -1), (key1862, -1), (key1862, -1), (key1514, -1), (key1514, -1), (key1742, -1), (key1742, -1), (key1878, -1), (key1878, -1), (key1375, 1), (key1375, 1), (key1724, 1), (key1724, 1), (key1868, 1), (key1868, 1)]

theorem rawRowCheck4731 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form12 = rawRow4731 := by decide +kernel

def row4731 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

theorem rowCheck4731 : row4731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4731 := by decide +kernel

theorem rowEval4731 (x : Key → ℝ) : Integer.Sparse.eval row4731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4731, Integer.Sparse.eval_collectBalanced, rawRowCheck4731]

def rawRow4732 : Integer.Sparse Key := [(key1724, -2), (key1868, -2), (key1724, -2), (key1717, 1), (key1862, 1), (key1491, 1), (key1862, 1), (key1491, 1), (key1717, 1), (key1742, 2), (key1878, 2), (key1742, 2), (key1717, -1), (key1862, -1), (key1365, -1), (key1862, -1), (key1365, -1), (key1717, -1), (key1742, -1), (key1878, -1), (key1514, -1), (key1878, -1), (key1514, -1), (key1742, -1), (key1724, 1), (key1868, 1), (key1375, 1), (key1868, 1), (key1375, 1), (key1724, 1)]

theorem rawRowCheck4732 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form12 = rawRow4732 := by decide +kernel

def row4732 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

theorem rowCheck4732 : row4732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4732 := by decide +kernel

theorem rowEval4732 (x : Key → ℝ) : Integer.Sparse.eval row4732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4732, Integer.Sparse.eval_collectBalanced, rawRowCheck4732]

def rawRow4733 : Integer.Sparse Key := [(key1868, -2), (key1724, -2), (key1724, -2), (key1862, 1), (key1717, 1), (key1862, 1), (key1491, 1), (key1717, 1), (key1491, 1), (key1878, 2), (key1742, 2), (key1742, 2), (key1862, -1), (key1717, -1), (key1862, -1), (key1365, -1), (key1717, -1), (key1365, -1), (key1878, -1), (key1742, -1), (key1878, -1), (key1514, -1), (key1742, -1), (key1514, -1), (key1868, 1), (key1724, 1), (key1868, 1), (key1375, 1), (key1724, 1), (key1375, 1)]

theorem rawRowCheck4733 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form12 = rawRow4733 := by decide +kernel

def row4733 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

theorem rowCheck4733 : row4733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4733 := by decide +kernel

theorem rowEval4733 (x : Key → ℝ) : Integer.Sparse.eval row4733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4733, Integer.Sparse.eval_collectBalanced, rawRowCheck4733]

def rawRow4734 : Integer.Sparse Key := [(key1514, -2), (key1514, -2), (key1514, -2), (key1742, 1), (key1742, 1), (key1742, 1), (key1742, 1), (key1742, 1), (key1742, 1), (key1375, 2), (key1375, 2), (key1375, 2), (key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1365, -1), (key1365, -1), (key1365, -1), (key1365, -1), (key1365, -1), (key1365, -1), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1)]

theorem rawRowCheck4734 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form12 = rawRow4734 := by decide +kernel

def row4734 : Integer.Sparse Key := [(key1365, -6), (key1375, 6), (key1491, 6), (key1514, -6), (key1724, -6), (key1742, 6)]

theorem rowCheck4734 : row4734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4734 := by decide +kernel

theorem rowEval4734 (x : Key → ℝ) : Integer.Sparse.eval row4734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4734, Integer.Sparse.eval_collectBalanced, rawRowCheck4734]

def rawRow4735 : Integer.Sparse Key := [(key1742, -2), (key1742, -2), (key1878, -2), (key1514, 1), (key1514, 1), (key1742, 1), (key1742, 1), (key1878, 1), (key1878, 1), (key1724, 2), (key1724, 2), (key1868, 2), (key1375, -1), (key1375, -1), (key1724, -1), (key1724, -1), (key1868, -1), (key1868, -1), (key1491, -1), (key1491, -1), (key1717, -1), (key1717, -1), (key1862, -1), (key1862, -1), (key1365, 1), (key1365, 1), (key1717, 1), (key1717, 1), (key1862, 1), (key1862, 1)]

theorem rawRowCheck4735 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form12 = rawRow4735 := by decide +kernel

def row4735 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

theorem rowCheck4735 : row4735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4735 := by decide +kernel

theorem rowEval4735 (x : Key → ℝ) : Integer.Sparse.eval row4735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4735, Integer.Sparse.eval_collectBalanced, rawRowCheck4735]

end MUB6.Certificate.GramRows

end OAI
