import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10624 : Integer.Sparse Key := [(key1859, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1861, -2), (key1859, -2), (key1867, -2), (key1861, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1867, -2), (key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, 2)]

theorem rawRowCheck10624 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form7 = rawRow10624 := by decide +kernel

def row10624 : Integer.Sparse Key := [(key1867, -6), (key1877, 6)]

theorem rowCheck10624 : row10624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10624 := by decide +kernel

theorem rowEval10624 (x : Key → ℝ) : Integer.Sparse.eval row10624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck10624, Integer.Sparse.eval_collectBalanced, rawRowCheck10624]

def rawRow10625 : Integer.Sparse Key := [(key1861, -2), (key1859, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1867, -2), (key1859, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1867, -2), (key1861, -2), (key1861, 2), (key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, 2)]

theorem rawRowCheck10625 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form7 = rawRow10625 := by decide +kernel

def row10625 : Integer.Sparse Key := [(key1867, -6), (key1877, 6)]

theorem rowCheck10625 : row10625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10625 := by decide +kernel

theorem rowEval10625 (x : Key → ℝ) : Integer.Sparse.eval row10625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10625, Integer.Sparse.eval_collectBalanced, rawRowCheck10625]

def rawRow10626 : Integer.Sparse Key := [(key1861, -2), (key1861, -2), (key1859, -2), (key1867, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1859, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1861, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1861, 2)]

theorem rawRowCheck10626 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form7 = rawRow10626 := by decide +kernel

def row10626 : Integer.Sparse Key := [(key1867, -6), (key1877, 6)]

theorem rowCheck10626 : row10626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10626 := by decide +kernel

theorem rowEval10626 (x : Key → ℝ) : Integer.Sparse.eval row10626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10626, Integer.Sparse.eval_collectBalanced, rawRowCheck10626]

def rawRow10627 : Integer.Sparse Key := [(key1867, -2), (key1867, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1877, 2), (key1877, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1859, 2)]

theorem rawRowCheck10627 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow10627 := by decide +kernel

def row10627 : Integer.Sparse Key := [(key1867, -6), (key1877, 6)]

theorem rowCheck10627 : row10627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10627 := by decide +kernel

theorem rowEval10627 (x : Key → ℝ) : Integer.Sparse.eval row10627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10627, Integer.Sparse.eval_collectBalanced, rawRowCheck10627]

def rawRow10628 : Integer.Sparse Key := [(key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2)]

theorem rawRowCheck10628 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form7 = rawRow10628 := by decide +kernel

def row10628 : Integer.Sparse Key := [(key1867, 24), (key1877, -24)]

theorem rowCheck10628 : row10628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10628 := by decide +kernel

theorem rowEval10628 (x : Key → ℝ) : Integer.Sparse.eval row10628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10628, Integer.Sparse.eval_collectBalanced, rawRowCheck10628]

def rawRow10629 : Integer.Sparse Key := [(key626, -2), (key627, -2), (key627, -2), (key626, -2), (key627, -2), (key626, -2), (key640, -2), (key627, -2), (key640, -2), (key627, -2), (key627, -2), (key640, -2), (key626, 1), (key627, 1), (key626, 1), (key629, 1), (key627, 1), (key629, 1), (key626, 1), (key627, 1), (key626, 1), (key640, 1), (key627, 1), (key640, 1), (key626, 1), (key629, 1), (key626, 1), (key640, 1), (key629, 1), (key640, 1), (key627, 1), (key629, 1), (key627, 1), (key640, 1), (key629, 1), (key640, 1)]

theorem rawRowCheck10629 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form8 = rawRow10629 := by decide +kernel

def row10629 : Integer.Sparse Key := [(key627, -6), (key629, 6)]

theorem rowCheck10629 : row10629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10629 := by decide +kernel

theorem rowEval10629 (x : Key → ℝ) : Integer.Sparse.eval row10629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck10629, Integer.Sparse.eval_collectBalanced, rawRowCheck10629]

def rawRow10630 : Integer.Sparse Key := [(key627, -2), (key626, -2), (key627, -2), (key627, -2), (key626, -2), (key640, -2), (key626, -2), (key640, -2), (key627, -2), (key627, -2), (key640, -2), (key627, -2), (key627, 1), (key626, 1), (key629, 1), (key626, 1), (key629, 1), (key627, 1), (key627, 1), (key626, 1), (key640, 1), (key626, 1), (key640, 1), (key627, 1), (key629, 1), (key626, 1), (key640, 1), (key626, 1), (key640, 1), (key629, 1), (key629, 1), (key627, 1), (key640, 1), (key627, 1), (key640, 1), (key629, 1)]

theorem rawRowCheck10630 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form8 = rawRow10630 := by decide +kernel

def row10630 : Integer.Sparse Key := [(key627, -6), (key629, 6)]

theorem rowCheck10630 : row10630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10630 := by decide +kernel

theorem rowEval10630 (x : Key → ℝ) : Integer.Sparse.eval row10630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10630, Integer.Sparse.eval_collectBalanced, rawRowCheck10630]

def rawRow10631 : Integer.Sparse Key := [(key627, -2), (key627, -2), (key626, -2), (key640, -2), (key640, -2), (key627, -2), (key627, -2), (key626, -2), (key626, -2), (key640, -2), (key627, -2), (key627, -2), (key629, 1), (key629, 1), (key627, 1), (key627, 1), (key626, 1), (key626, 1), (key640, 1), (key640, 1), (key627, 1), (key627, 1), (key626, 1), (key626, 1), (key640, 1), (key640, 1), (key629, 1), (key629, 1), (key626, 1), (key626, 1), (key640, 1), (key640, 1), (key629, 1), (key629, 1), (key627, 1), (key627, 1)]

theorem rawRowCheck10631 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form8 = rawRow10631 := by decide +kernel

def row10631 : Integer.Sparse Key := [(key627, -6), (key629, 6)]

theorem rowCheck10631 : row10631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10631 := by decide +kernel

theorem rowEval10631 (x : Key → ℝ) : Integer.Sparse.eval row10631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10631, Integer.Sparse.eval_collectBalanced, rawRowCheck10631]

def rawRow10632 : Integer.Sparse Key := [(key640, -2), (key640, -2), (key640, -2), (key627, -2), (key627, -2), (key627, -2), (key627, -2), (key627, -2), (key627, -2), (key626, -2), (key626, -2), (key626, -2), (key640, 1), (key640, 1), (key640, 1), (key640, 1), (key640, 1), (key640, 1), (key629, 1), (key629, 1), (key629, 1), (key629, 1), (key629, 1), (key629, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key626, 1), (key626, 1), (key626, 1), (key626, 1), (key626, 1), (key626, 1)]

theorem rawRowCheck10632 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form8 = rawRow10632 := by decide +kernel

def row10632 : Integer.Sparse Key := [(key627, -6), (key629, 6)]

theorem rowCheck10632 : row10632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10632 := by decide +kernel

theorem rowEval10632 (x : Key → ℝ) : Integer.Sparse.eval row10632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10632, Integer.Sparse.eval_collectBalanced, rawRowCheck10632]

def rawRow10633 : Integer.Sparse Key := [(key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1)]

theorem rawRowCheck10633 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form8 = rawRow10633 := by decide +kernel

def row10633 : Integer.Sparse Key := [(key627, 24), (key629, -24)]

theorem rowCheck10633 : row10633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10633 := by decide +kernel

theorem rowEval10633 (x : Key → ℝ) : Integer.Sparse.eval row10633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10633, Integer.Sparse.eval_collectBalanced, rawRowCheck10633]

def rawRow10634 : Integer.Sparse Key := [(key1859, 1), (key1861, 1), (key1859, 1), (key1867, 1), (key1861, 1), (key1867, 1), (key1859, 1), (key1861, 1), (key1859, 1), (key1877, 1), (key1861, 1), (key1877, 1), (key1859, 1), (key1867, 1), (key1859, 1), (key1877, 1), (key1867, 1), (key1877, 1), (key1861, 1), (key1867, 1), (key1861, 1), (key1877, 1), (key1867, 1), (key1877, 1), (key1861, -2), (key1861, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1877, -2), (key1861, -2), (key1867, -2), (key1861, -2), (key1877, -2), (key1867, -2), (key1877, -2)]

theorem rawRowCheck10634 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form9 = rawRow10634 := by decide +kernel

def row10634 : Integer.Sparse Key := [(key1859, 6), (key1861, -6)]

theorem rowCheck10634 : row10634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10634 := by decide +kernel

theorem rowEval10634 (x : Key → ℝ) : Integer.Sparse.eval row10634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck10634, Integer.Sparse.eval_collectBalanced, rawRowCheck10634]

def rawRow10635 : Integer.Sparse Key := [(key1861, 1), (key1859, 1), (key1867, 1), (key1859, 1), (key1867, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1877, 1), (key1859, 1), (key1877, 1), (key1861, 1), (key1867, 1), (key1859, 1), (key1877, 1), (key1859, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1861, 1), (key1877, 1), (key1861, 1), (key1877, 1), (key1867, 1), (key1861, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1877, -2), (key1861, -2), (key1867, -2), (key1861, -2), (key1877, -2), (key1861, -2), (key1877, -2), (key1867, -2)]

theorem rawRowCheck10635 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form9 = rawRow10635 := by decide +kernel

def row10635 : Integer.Sparse Key := [(key1859, 6), (key1861, -6)]

theorem rowCheck10635 : row10635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10635 := by decide +kernel

theorem rowEval10635 (x : Key → ℝ) : Integer.Sparse.eval row10635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10635, Integer.Sparse.eval_collectBalanced, rawRowCheck10635]

def rawRow10636 : Integer.Sparse Key := [(key1867, 1), (key1867, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1859, 1), (key1877, 1), (key1877, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1859, 1), (key1877, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1859, 1), (key1859, 1), (key1877, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1861, 1), (key1861, 1), (key1867, -2), (key1861, -2), (key1861, -2), (key1877, -2), (key1861, -2), (key1861, -2), (key1877, -2), (key1877, -2), (key1867, -2), (key1867, -2), (key1861, -2), (key1861, -2)]

theorem rawRowCheck10636 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form9 = rawRow10636 := by decide +kernel

def row10636 : Integer.Sparse Key := [(key1859, 6), (key1861, -6)]

theorem rowCheck10636 : row10636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10636 := by decide +kernel

theorem rowEval10636 (x : Key → ℝ) : Integer.Sparse.eval row10636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10636, Integer.Sparse.eval_collectBalanced, rawRowCheck10636]

def rawRow10637 : Integer.Sparse Key := [(key1877, 1), (key1877, 1), (key1877, 1), (key1877, 1), (key1877, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1877, -2), (key1877, -2), (key1877, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2)]

theorem rawRowCheck10637 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form9 = rawRow10637 := by decide +kernel

def row10637 : Integer.Sparse Key := [(key1859, 6), (key1861, -6)]

theorem rowCheck10637 : row10637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10637 := by decide +kernel

theorem rowEval10637 (x : Key → ℝ) : Integer.Sparse.eval row10637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10637, Integer.Sparse.eval_collectBalanced, rawRowCheck10637]

def rawRow10638 : Integer.Sparse Key := [(key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2)]

theorem rawRowCheck10638 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form9 = rawRow10638 := by decide +kernel

def row10638 : Integer.Sparse Key := [(key1859, -24), (key1861, 24)]

theorem rowCheck10638 : row10638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10638 := by decide +kernel

theorem rowEval10638 (x : Key → ℝ) : Integer.Sparse.eval row10638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10638, Integer.Sparse.eval_collectBalanced, rawRowCheck10638]

def rawRow10639 : Integer.Sparse Key := [(key686, -6), (key686, -6), (key686, -6), (key690, -6), (key686, 2), (key686, 2), (key687, 2), (key686, 2), (key686, 2), (key690, 2), (key686, 2), (key687, 2), (key686, 2), (key690, 2), (key687, 2), (key690, 2)]

theorem rawRowCheck10639 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form10 = rawRow10639 := by decide +kernel

def row10639 : Integer.Sparse Key := [(key686, -6), (key687, 6)]

theorem rowCheck10639 : row10639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10639 := by decide +kernel

theorem rowEval10639 (x : Key → ℝ) : Integer.Sparse.eval row10639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck10639, Integer.Sparse.eval_collectBalanced, rawRowCheck10639]

def rawRow10640 : Integer.Sparse Key := [(key686, -6), (key686, -6), (key690, -6), (key686, -6), (key686, 2), (key687, 2), (key686, 2), (key686, 2), (key690, 2), (key686, 2), (key687, 2), (key686, 2), (key690, 2), (key686, 2), (key690, 2), (key687, 2)]

theorem rawRowCheck10640 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form10 = rawRow10640 := by decide +kernel

def row10640 : Integer.Sparse Key := [(key686, -6), (key687, 6)]

theorem rowCheck10640 : row10640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10640 := by decide +kernel

theorem rowEval10640 (x : Key → ℝ) : Integer.Sparse.eval row10640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10640, Integer.Sparse.eval_collectBalanced, rawRowCheck10640]

def rawRow10641 : Integer.Sparse Key := [(key686, -6), (key690, -6), (key686, -6), (key686, -6), (key687, 2), (key686, 2), (key686, 2), (key690, 2), (key686, 2), (key686, 2), (key690, 2), (key690, 2), (key687, 2), (key687, 2), (key686, 2), (key686, 2)]

theorem rawRowCheck10641 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form10 = rawRow10641 := by decide +kernel

def row10641 : Integer.Sparse Key := [(key686, -6), (key687, 6)]

theorem rowCheck10641 : row10641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10641 := by decide +kernel

theorem rowEval10641 (x : Key → ℝ) : Integer.Sparse.eval row10641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10641, Integer.Sparse.eval_collectBalanced, rawRowCheck10641]

def rawRow10642 : Integer.Sparse Key := [(key690, -6), (key686, -6), (key686, -6), (key686, -6), (key690, 2), (key690, 2), (key690, 2), (key687, 2), (key687, 2), (key687, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2)]

theorem rawRowCheck10642 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow10642 := by decide +kernel

def row10642 : Integer.Sparse Key := [(key686, -6), (key687, 6)]

theorem rowCheck10642 : row10642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10642 := by decide +kernel

theorem rowEval10642 (x : Key → ℝ) : Integer.Sparse.eval row10642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10642, Integer.Sparse.eval_collectBalanced, rawRowCheck10642]

def rawRow10643 : Integer.Sparse Key := [(key687, -6), (key687, -6), (key687, -6), (key687, -6), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2)]

theorem rawRowCheck10643 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form10 = rawRow10643 := by decide +kernel

def row10643 : Integer.Sparse Key := [(key686, 24), (key687, -24)]

theorem rowCheck10643 : row10643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10643 := by decide +kernel

theorem rowEval10643 (x : Key → ℝ) : Integer.Sparse.eval row10643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10643, Integer.Sparse.eval_collectBalanced, rawRowCheck10643]

def rawRow10644 : Integer.Sparse Key := [(key1932, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, -6), (key1933, -6), (key1933, -6), (key1953, -6)]

theorem rawRowCheck10644 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form11 = rawRow10644 := by decide +kernel

def row10644 : Integer.Sparse Key := [(key1932, 6), (key1953, -6)]

theorem rowCheck10644 : row10644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10644 := by decide +kernel

theorem rowEval10644 (x : Key → ℝ) : Integer.Sparse.eval row10644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck10644, Integer.Sparse.eval_collectBalanced, rawRowCheck10644]

def rawRow10645 : Integer.Sparse Key := [(key1933, 6), (key1932, 6), (key1933, 6), (key1933, 6), (key1933, -6), (key1933, -6), (key1953, -6), (key1933, -6)]

theorem rawRowCheck10645 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form11 = rawRow10645 := by decide +kernel

def row10645 : Integer.Sparse Key := [(key1932, 6), (key1953, -6)]

theorem rowCheck10645 : row10645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10645 := by decide +kernel

theorem rowEval10645 (x : Key → ℝ) : Integer.Sparse.eval row10645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10645, Integer.Sparse.eval_collectBalanced, rawRowCheck10645]

def rawRow10646 : Integer.Sparse Key := [(key1933, 6), (key1933, 6), (key1932, 6), (key1933, 6), (key1933, -6), (key1953, -6), (key1933, -6), (key1933, -6)]

theorem rawRowCheck10646 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form11 = rawRow10646 := by decide +kernel

def row10646 : Integer.Sparse Key := [(key1932, 6), (key1953, -6)]

theorem rowCheck10646 : row10646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10646 := by decide +kernel

theorem rowEval10646 (x : Key → ℝ) : Integer.Sparse.eval row10646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10646, Integer.Sparse.eval_collectBalanced, rawRowCheck10646]

def rawRow10647 : Integer.Sparse Key := [(key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1953, -6), (key1933, -6), (key1933, -6), (key1933, -6)]

theorem rawRowCheck10647 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form11 = rawRow10647 := by decide +kernel

def row10647 : Integer.Sparse Key := [(key1932, 6), (key1953, -6)]

theorem rowCheck10647 : row10647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10647 := by decide +kernel

theorem rowEval10647 (x : Key → ℝ) : Integer.Sparse.eval row10647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10647, Integer.Sparse.eval_collectBalanced, rawRowCheck10647]

def rawRow10648 : Integer.Sparse Key := [(key1953, 6), (key1953, 6), (key1953, 6), (key1953, 6), (key1932, -6), (key1932, -6), (key1932, -6), (key1932, -6)]

theorem rawRowCheck10648 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form11 = rawRow10648 := by decide +kernel

def row10648 : Integer.Sparse Key := [(key1932, -24), (key1953, 24)]

theorem rowCheck10648 : row10648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10648 := by decide +kernel

theorem rowEval10648 (x : Key → ℝ) : Integer.Sparse.eval row10648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10648, Integer.Sparse.eval_collectBalanced, rawRowCheck10648]

def rawRow10649 : Integer.Sparse Key := [(key1850, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, -6), (key1852, -6), (key1852, -6), (key1884, -6)]

theorem rawRowCheck10649 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form12 = rawRow10649 := by decide +kernel

def row10649 : Integer.Sparse Key := [(key1850, 6), (key1884, -6)]

theorem rowCheck10649 : row10649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10649 := by decide +kernel

theorem rowEval10649 (x : Key → ℝ) : Integer.Sparse.eval row10649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck10649, Integer.Sparse.eval_collectBalanced, rawRowCheck10649]

def rawRow10650 : Integer.Sparse Key := [(key1852, 6), (key1850, 6), (key1852, 6), (key1852, 6), (key1852, -6), (key1852, -6), (key1884, -6), (key1852, -6)]

theorem rawRowCheck10650 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form12 = rawRow10650 := by decide +kernel

def row10650 : Integer.Sparse Key := [(key1850, 6), (key1884, -6)]

theorem rowCheck10650 : row10650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10650 := by decide +kernel

theorem rowEval10650 (x : Key → ℝ) : Integer.Sparse.eval row10650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10650, Integer.Sparse.eval_collectBalanced, rawRowCheck10650]

def rawRow10651 : Integer.Sparse Key := [(key1852, 6), (key1852, 6), (key1850, 6), (key1852, 6), (key1852, -6), (key1884, -6), (key1852, -6), (key1852, -6)]

theorem rawRowCheck10651 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form12 = rawRow10651 := by decide +kernel

def row10651 : Integer.Sparse Key := [(key1850, 6), (key1884, -6)]

theorem rowCheck10651 : row10651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10651 := by decide +kernel

theorem rowEval10651 (x : Key → ℝ) : Integer.Sparse.eval row10651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10651, Integer.Sparse.eval_collectBalanced, rawRowCheck10651]

def rawRow10652 : Integer.Sparse Key := [(key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1884, -6), (key1852, -6), (key1852, -6), (key1852, -6)]

theorem rawRowCheck10652 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form12 = rawRow10652 := by decide +kernel

def row10652 : Integer.Sparse Key := [(key1850, 6), (key1884, -6)]

theorem rowCheck10652 : row10652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10652 := by decide +kernel

theorem rowEval10652 (x : Key → ℝ) : Integer.Sparse.eval row10652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10652, Integer.Sparse.eval_collectBalanced, rawRowCheck10652]

def rawRow10653 : Integer.Sparse Key := [(key1884, 6), (key1884, 6), (key1884, 6), (key1884, 6), (key1850, -6), (key1850, -6), (key1850, -6), (key1850, -6)]

theorem rawRowCheck10653 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form12 = rawRow10653 := by decide +kernel

def row10653 : Integer.Sparse Key := [(key1850, -24), (key1884, 24)]

theorem rowCheck10653 : row10653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10653 := by decide +kernel

theorem rowEval10653 (x : Key → ℝ) : Integer.Sparse.eval row10653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10653, Integer.Sparse.eval_collectBalanced, rawRowCheck10653]

def rawRow10654 : Integer.Sparse Key := [(key360, -6), (key362, -6), (key362, -6), (key362, -6), (key360, 2), (key362, 2), (key362, 2), (key360, 2), (key362, 2), (key360, 2), (key366, 2), (key362, 2), (key366, 2), (key362, 2), (key362, 2), (key366, 2)]

theorem rawRowCheck10654 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form13 = rawRow10654 := by decide +kernel

def row10654 : Integer.Sparse Key := [(key362, -6), (key366, 6)]

theorem rowCheck10654 : row10654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10654 := by decide +kernel

theorem rowEval10654 (x : Key → ℝ) : Integer.Sparse.eval row10654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form13) x := by
  rw [rowCheck10654, Integer.Sparse.eval_collectBalanced, rawRowCheck10654]

def rawRow10655 : Integer.Sparse Key := [(key362, -6), (key360, -6), (key362, -6), (key362, -6), (key362, 2), (key360, 2), (key362, 2), (key362, 2), (key360, 2), (key366, 2), (key360, 2), (key366, 2), (key362, 2), (key362, 2), (key366, 2), (key362, 2)]

theorem rawRowCheck10655 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form13 = rawRow10655 := by decide +kernel

def row10655 : Integer.Sparse Key := [(key362, -6), (key366, 6)]

theorem rowCheck10655 : row10655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10655 := by decide +kernel

theorem rowEval10655 (x : Key → ℝ) : Integer.Sparse.eval row10655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10655, Integer.Sparse.eval_collectBalanced, rawRowCheck10655]

def rawRow10656 : Integer.Sparse Key := [(key362, -6), (key362, -6), (key360, -6), (key362, -6), (key362, 2), (key362, 2), (key360, 2), (key366, 2), (key366, 2), (key362, 2), (key362, 2), (key360, 2), (key360, 2), (key366, 2), (key362, 2), (key362, 2)]

theorem rawRowCheck10656 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form13 = rawRow10656 := by decide +kernel

def row10656 : Integer.Sparse Key := [(key362, -6), (key366, 6)]

theorem rowCheck10656 : row10656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10656 := by decide +kernel

theorem rowEval10656 (x : Key → ℝ) : Integer.Sparse.eval row10656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10656, Integer.Sparse.eval_collectBalanced, rawRowCheck10656]

def rawRow10657 : Integer.Sparse Key := [(key362, -6), (key362, -6), (key362, -6), (key360, -6), (key366, 2), (key366, 2), (key366, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key360, 2), (key360, 2), (key360, 2)]

theorem rawRowCheck10657 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form13 = rawRow10657 := by decide +kernel

def row10657 : Integer.Sparse Key := [(key362, -6), (key366, 6)]

theorem rowCheck10657 : row10657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10657 := by decide +kernel

theorem rowEval10657 (x : Key → ℝ) : Integer.Sparse.eval row10657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10657, Integer.Sparse.eval_collectBalanced, rawRowCheck10657]

def rawRow10658 : Integer.Sparse Key := [(key366, -6), (key366, -6), (key366, -6), (key366, -6), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2)]

theorem rawRowCheck10658 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form13 = rawRow10658 := by decide +kernel

def row10658 : Integer.Sparse Key := [(key362, 24), (key366, -24)]

theorem rowCheck10658 : row10658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10658 := by decide +kernel

theorem rowEval10658 (x : Key → ℝ) : Integer.Sparse.eval row10658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10658, Integer.Sparse.eval_collectBalanced, rawRowCheck10658]

def rawRow10659 : Integer.Sparse Key := [(key617, 6), (key619, 6), (key619, 6), (key619, 6), (key619, -6), (key619, -6), (key619, -6), (key645, -6)]

theorem rawRowCheck10659 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form14 = rawRow10659 := by decide +kernel

def row10659 : Integer.Sparse Key := [(key617, 6), (key645, -6)]

theorem rowCheck10659 : row10659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10659 := by decide +kernel

theorem rowEval10659 (x : Key → ℝ) : Integer.Sparse.eval row10659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form14) x := by
  rw [rowCheck10659, Integer.Sparse.eval_collectBalanced, rawRowCheck10659]

def rawRow10660 : Integer.Sparse Key := [(key619, 6), (key617, 6), (key619, 6), (key619, 6), (key619, -6), (key619, -6), (key645, -6), (key619, -6)]

theorem rawRowCheck10660 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form14 = rawRow10660 := by decide +kernel

def row10660 : Integer.Sparse Key := [(key617, 6), (key645, -6)]

theorem rowCheck10660 : row10660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10660 := by decide +kernel

theorem rowEval10660 (x : Key → ℝ) : Integer.Sparse.eval row10660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10660, Integer.Sparse.eval_collectBalanced, rawRowCheck10660]

def rawRow10661 : Integer.Sparse Key := [(key619, 6), (key619, 6), (key617, 6), (key619, 6), (key619, -6), (key645, -6), (key619, -6), (key619, -6)]

theorem rawRowCheck10661 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form14 = rawRow10661 := by decide +kernel

def row10661 : Integer.Sparse Key := [(key617, 6), (key645, -6)]

theorem rowCheck10661 : row10661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10661 := by decide +kernel

theorem rowEval10661 (x : Key → ℝ) : Integer.Sparse.eval row10661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10661, Integer.Sparse.eval_collectBalanced, rawRowCheck10661]

def rawRow10662 : Integer.Sparse Key := [(key619, 6), (key619, 6), (key619, 6), (key617, 6), (key645, -6), (key619, -6), (key619, -6), (key619, -6)]

theorem rawRowCheck10662 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form14 = rawRow10662 := by decide +kernel

def row10662 : Integer.Sparse Key := [(key617, 6), (key645, -6)]

theorem rowCheck10662 : row10662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10662 := by decide +kernel

theorem rowEval10662 (x : Key → ℝ) : Integer.Sparse.eval row10662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10662, Integer.Sparse.eval_collectBalanced, rawRowCheck10662]

def rawRow10663 : Integer.Sparse Key := [(key645, 6), (key645, 6), (key645, 6), (key645, 6), (key617, -6), (key617, -6), (key617, -6), (key617, -6)]

theorem rawRowCheck10663 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form14 = rawRow10663 := by decide +kernel

def row10663 : Integer.Sparse Key := [(key617, -24), (key645, 24)]

theorem rowCheck10663 : row10663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10663 := by decide +kernel

theorem rowEval10663 (x : Key → ℝ) : Integer.Sparse.eval row10663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10663, Integer.Sparse.eval_collectBalanced, rawRowCheck10663]

def rawRow10664 : Integer.Sparse Key := [(key1932, -6), (key1933, -6), (key1933, -6), (key1933, -6), (key1932, 2), (key1933, 2), (key1933, 2), (key1932, 2), (key1933, 2), (key1932, 2), (key1953, 2), (key1933, 2), (key1953, 2), (key1933, 2), (key1933, 2), (key1953, 2)]

theorem rawRowCheck10664 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form15 = rawRow10664 := by decide +kernel

def row10664 : Integer.Sparse Key := [(key1933, -6), (key1953, 6)]

theorem rowCheck10664 : row10664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10664 := by decide +kernel

theorem rowEval10664 (x : Key → ℝ) : Integer.Sparse.eval row10664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form15) x := by
  rw [rowCheck10664, Integer.Sparse.eval_collectBalanced, rawRowCheck10664]

def rawRow10665 : Integer.Sparse Key := [(key1933, -6), (key1932, -6), (key1933, -6), (key1933, -6), (key1933, 2), (key1932, 2), (key1933, 2), (key1933, 2), (key1932, 2), (key1953, 2), (key1932, 2), (key1953, 2), (key1933, 2), (key1933, 2), (key1953, 2), (key1933, 2)]

theorem rawRowCheck10665 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form15 = rawRow10665 := by decide +kernel

def row10665 : Integer.Sparse Key := [(key1933, -6), (key1953, 6)]

theorem rowCheck10665 : row10665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10665 := by decide +kernel

theorem rowEval10665 (x : Key → ℝ) : Integer.Sparse.eval row10665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10665, Integer.Sparse.eval_collectBalanced, rawRowCheck10665]

def rawRow10666 : Integer.Sparse Key := [(key1933, -6), (key1933, -6), (key1932, -6), (key1933, -6), (key1933, 2), (key1933, 2), (key1932, 2), (key1953, 2), (key1953, 2), (key1933, 2), (key1933, 2), (key1932, 2), (key1932, 2), (key1953, 2), (key1933, 2), (key1933, 2)]

theorem rawRowCheck10666 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form15 = rawRow10666 := by decide +kernel

def row10666 : Integer.Sparse Key := [(key1933, -6), (key1953, 6)]

theorem rowCheck10666 : row10666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10666 := by decide +kernel

theorem rowEval10666 (x : Key → ℝ) : Integer.Sparse.eval row10666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10666, Integer.Sparse.eval_collectBalanced, rawRowCheck10666]

def rawRow10667 : Integer.Sparse Key := [(key1933, -6), (key1933, -6), (key1933, -6), (key1932, -6), (key1953, 2), (key1953, 2), (key1953, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1932, 2), (key1932, 2), (key1932, 2)]

theorem rawRowCheck10667 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form15 = rawRow10667 := by decide +kernel

def row10667 : Integer.Sparse Key := [(key1933, -6), (key1953, 6)]

theorem rowCheck10667 : row10667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10667 := by decide +kernel

theorem rowEval10667 (x : Key → ℝ) : Integer.Sparse.eval row10667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10667, Integer.Sparse.eval_collectBalanced, rawRowCheck10667]

def rawRow10668 : Integer.Sparse Key := [(key1953, -6), (key1953, -6), (key1953, -6), (key1953, -6), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2)]

theorem rawRowCheck10668 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form15 = rawRow10668 := by decide +kernel

def row10668 : Integer.Sparse Key := [(key1933, 24), (key1953, -24)]

theorem rowCheck10668 : row10668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10668 := by decide +kernel

theorem rowEval10668 (x : Key → ℝ) : Integer.Sparse.eval row10668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10668, Integer.Sparse.eval_collectBalanced, rawRowCheck10668]

def rawRow10669 : Integer.Sparse Key := [(key1958, -6), (key1958, -6), (key1958, -6), (key1960, -6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6)]

theorem rawRowCheck10669 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form16 = rawRow10669 := by decide +kernel

def row10669 : Integer.Sparse Key := [(key1960, -6), (key1966, 6)]

theorem rowCheck10669 : row10669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10669 := by decide +kernel

theorem rowEval10669 (x : Key → ℝ) : Integer.Sparse.eval row10669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form16) x := by
  rw [rowCheck10669, Integer.Sparse.eval_collectBalanced, rawRowCheck10669]

def rawRow10670 : Integer.Sparse Key := [(key1958, -6), (key1958, -6), (key1960, -6), (key1958, -6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6)]

theorem rawRowCheck10670 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form16 = rawRow10670 := by decide +kernel

def row10670 : Integer.Sparse Key := [(key1960, -6), (key1966, 6)]

theorem rowCheck10670 : row10670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10670 := by decide +kernel

theorem rowEval10670 (x : Key → ℝ) : Integer.Sparse.eval row10670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10670, Integer.Sparse.eval_collectBalanced, rawRowCheck10670]

def rawRow10671 : Integer.Sparse Key := [(key1958, -6), (key1960, -6), (key1958, -6), (key1958, -6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6)]

theorem rawRowCheck10671 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form16 = rawRow10671 := by decide +kernel

def row10671 : Integer.Sparse Key := [(key1960, -6), (key1966, 6)]

theorem rowCheck10671 : row10671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10671 := by decide +kernel

theorem rowEval10671 (x : Key → ℝ) : Integer.Sparse.eval row10671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10671, Integer.Sparse.eval_collectBalanced, rawRowCheck10671]

def rawRow10672 : Integer.Sparse Key := [(key1960, -6), (key1958, -6), (key1958, -6), (key1958, -6), (key1966, 6), (key1958, 6), (key1958, 6), (key1958, 6)]

theorem rawRowCheck10672 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form16 = rawRow10672 := by decide +kernel

def row10672 : Integer.Sparse Key := [(key1960, -6), (key1966, 6)]

theorem rowCheck10672 : row10672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10672 := by decide +kernel

theorem rowEval10672 (x : Key → ℝ) : Integer.Sparse.eval row10672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10672, Integer.Sparse.eval_collectBalanced, rawRowCheck10672]

def rawRow10673 : Integer.Sparse Key := [(key1966, -6), (key1966, -6), (key1966, -6), (key1966, -6), (key1960, 6), (key1960, 6), (key1960, 6), (key1960, 6)]

theorem rawRowCheck10673 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form16 = rawRow10673 := by decide +kernel

def row10673 : Integer.Sparse Key := [(key1960, 24), (key1966, -24)]

theorem rowCheck10673 : row10673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10673 := by decide +kernel

theorem rowEval10673 (x : Key → ℝ) : Integer.Sparse.eval row10673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10673, Integer.Sparse.eval_collectBalanced, rawRowCheck10673]

def rawRow10674 : Integer.Sparse Key := [(key1860, -2), (key1860, -2), (key1864, -2), (key1860, -2), (key1860, -2), (key1879, -2), (key1860, -2), (key1864, -2), (key1860, -2), (key1879, -2), (key1864, -2), (key1879, -2), (key1860, 2), (key1860, 2), (key1869, 2), (key1860, 2), (key1860, 2), (key1879, 2), (key1860, 2), (key1869, 2), (key1860, 2), (key1879, 2), (key1869, 2), (key1879, 2)]

theorem rawRowCheck10674 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form17 = rawRow10674 := by decide +kernel

def row10674 : Integer.Sparse Key := [(key1864, -6), (key1869, 6)]

theorem rowCheck10674 : row10674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10674 := by decide +kernel

theorem rowEval10674 (x : Key → ℝ) : Integer.Sparse.eval row10674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form17) x := by
  rw [rowCheck10674, Integer.Sparse.eval_collectBalanced, rawRowCheck10674]

def rawRow10675 : Integer.Sparse Key := [(key1860, -2), (key1864, -2), (key1860, -2), (key1860, -2), (key1879, -2), (key1860, -2), (key1864, -2), (key1860, -2), (key1879, -2), (key1860, -2), (key1879, -2), (key1864, -2), (key1860, 2), (key1869, 2), (key1860, 2), (key1860, 2), (key1879, 2), (key1860, 2), (key1869, 2), (key1860, 2), (key1879, 2), (key1860, 2), (key1879, 2), (key1869, 2)]

theorem rawRowCheck10675 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form17 = rawRow10675 := by decide +kernel

def row10675 : Integer.Sparse Key := [(key1864, -6), (key1869, 6)]

theorem rowCheck10675 : row10675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10675 := by decide +kernel

theorem rowEval10675 (x : Key → ℝ) : Integer.Sparse.eval row10675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10675, Integer.Sparse.eval_collectBalanced, rawRowCheck10675]

def rawRow10676 : Integer.Sparse Key := [(key1864, -2), (key1860, -2), (key1860, -2), (key1879, -2), (key1860, -2), (key1860, -2), (key1879, -2), (key1879, -2), (key1864, -2), (key1864, -2), (key1860, -2), (key1860, -2), (key1869, 2), (key1860, 2), (key1860, 2), (key1879, 2), (key1860, 2), (key1860, 2), (key1879, 2), (key1879, 2), (key1869, 2), (key1869, 2), (key1860, 2), (key1860, 2)]

theorem rawRowCheck10676 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form17 = rawRow10676 := by decide +kernel

def row10676 : Integer.Sparse Key := [(key1864, -6), (key1869, 6)]

theorem rowCheck10676 : row10676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10676 := by decide +kernel

theorem rowEval10676 (x : Key → ℝ) : Integer.Sparse.eval row10676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10676, Integer.Sparse.eval_collectBalanced, rawRowCheck10676]

def rawRow10677 : Integer.Sparse Key := [(key1879, -2), (key1879, -2), (key1879, -2), (key1864, -2), (key1864, -2), (key1864, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1879, 2), (key1879, 2), (key1879, 2), (key1869, 2), (key1869, 2), (key1869, 2), (key1860, 2), (key1860, 2), (key1860, 2), (key1860, 2), (key1860, 2), (key1860, 2)]

theorem rawRowCheck10677 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form17 = rawRow10677 := by decide +kernel

def row10677 : Integer.Sparse Key := [(key1864, -6), (key1869, 6)]

theorem rowCheck10677 : row10677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10677 := by decide +kernel

theorem rowEval10677 (x : Key → ℝ) : Integer.Sparse.eval row10677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10677, Integer.Sparse.eval_collectBalanced, rawRowCheck10677]

def rawRow10678 : Integer.Sparse Key := [(key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2)]

theorem rawRowCheck10678 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form17 = rawRow10678 := by decide +kernel

def row10678 : Integer.Sparse Key := [(key1864, 24), (key1869, -24)]

theorem rowCheck10678 : row10678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10678 := by decide +kernel

theorem rowEval10678 (x : Key → ℝ) : Integer.Sparse.eval row10678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10678, Integer.Sparse.eval_collectBalanced, rawRowCheck10678]

def rawRow10679 : Integer.Sparse Key := [(key618, 2), (key618, 2), (key622, 2), (key618, 2), (key618, 2), (key648, 2), (key618, 2), (key622, 2), (key618, 2), (key648, 2), (key622, 2), (key648, 2), (key618, -2), (key622, -2), (key622, -2), (key618, -2), (key622, -2), (key618, -2), (key648, -2), (key622, -2), (key648, -2), (key622, -2), (key622, -2), (key648, -2)]

theorem rawRowCheck10679 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form18 = rawRow10679 := by decide +kernel

def row10679 : Integer.Sparse Key := [(key618, 6), (key622, -6)]

theorem rowCheck10679 : row10679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10679 := by decide +kernel

theorem rowEval10679 (x : Key → ℝ) : Integer.Sparse.eval row10679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form18) x := by
  rw [rowCheck10679, Integer.Sparse.eval_collectBalanced, rawRowCheck10679]

def rawRow10680 : Integer.Sparse Key := [(key618, 2), (key622, 2), (key618, 2), (key618, 2), (key648, 2), (key618, 2), (key622, 2), (key618, 2), (key648, 2), (key618, 2), (key648, 2), (key622, 2), (key622, -2), (key618, -2), (key622, -2), (key622, -2), (key618, -2), (key648, -2), (key618, -2), (key648, -2), (key622, -2), (key622, -2), (key648, -2), (key622, -2)]

theorem rawRowCheck10680 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form18 = rawRow10680 := by decide +kernel

def row10680 : Integer.Sparse Key := [(key618, 6), (key622, -6)]

theorem rowCheck10680 : row10680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10680 := by decide +kernel

theorem rowEval10680 (x : Key → ℝ) : Integer.Sparse.eval row10680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10680, Integer.Sparse.eval_collectBalanced, rawRowCheck10680]

def rawRow10681 : Integer.Sparse Key := [(key622, 2), (key618, 2), (key618, 2), (key648, 2), (key618, 2), (key618, 2), (key648, 2), (key648, 2), (key622, 2), (key622, 2), (key618, 2), (key618, 2), (key622, -2), (key622, -2), (key618, -2), (key648, -2), (key648, -2), (key622, -2), (key622, -2), (key618, -2), (key618, -2), (key648, -2), (key622, -2), (key622, -2)]

theorem rawRowCheck10681 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form18 = rawRow10681 := by decide +kernel

def row10681 : Integer.Sparse Key := [(key618, 6), (key622, -6)]

theorem rowCheck10681 : row10681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10681 := by decide +kernel

theorem rowEval10681 (x : Key → ℝ) : Integer.Sparse.eval row10681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10681, Integer.Sparse.eval_collectBalanced, rawRowCheck10681]

def rawRow10682 : Integer.Sparse Key := [(key648, 2), (key648, 2), (key648, 2), (key622, 2), (key622, 2), (key622, 2), (key618, 2), (key618, 2), (key618, 2), (key618, 2), (key618, 2), (key618, 2), (key648, -2), (key648, -2), (key648, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key618, -2), (key618, -2), (key618, -2)]

theorem rawRowCheck10682 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form18 = rawRow10682 := by decide +kernel

def row10682 : Integer.Sparse Key := [(key618, 6), (key622, -6)]

theorem rowCheck10682 : row10682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10682 := by decide +kernel

theorem rowEval10682 (x : Key → ℝ) : Integer.Sparse.eval row10682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10682, Integer.Sparse.eval_collectBalanced, rawRowCheck10682]

def rawRow10683 : Integer.Sparse Key := [(key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2)]

theorem rawRowCheck10683 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form18 = rawRow10683 := by decide +kernel

def row10683 : Integer.Sparse Key := [(key618, -24), (key622, 24)]

theorem rowCheck10683 : row10683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10683 := by decide +kernel

theorem rowEval10683 (x : Key → ℝ) : Integer.Sparse.eval row10683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10683, Integer.Sparse.eval_collectBalanced, rawRowCheck10683]

def rawRow10684 : Integer.Sparse Key := [(key1962, -4), (key1962, -4), (key1964, -4), (key1962, -4), (key1964, -4), (key1964, -4), (key1962, 6), (key1964, 6), (key1964, 6), (key1964, 6)]

theorem rawRowCheck10684 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form19 = rawRow10684 := by decide +kernel

def row10684 : Integer.Sparse Key := [(key1962, -6), (key1964, 6)]

theorem rowCheck10684 : row10684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10684 := by decide +kernel

theorem rowEval10684 (x : Key → ℝ) : Integer.Sparse.eval row10684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form19) x := by
  rw [rowCheck10684, Integer.Sparse.eval_collectBalanced, rawRowCheck10684]

def rawRow10685 : Integer.Sparse Key := [(key1962, -4), (key1964, -4), (key1962, -4), (key1964, -4), (key1962, -4), (key1964, -4), (key1964, 6), (key1962, 6), (key1964, 6), (key1964, 6)]

theorem rawRowCheck10685 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form19 = rawRow10685 := by decide +kernel

def row10685 : Integer.Sparse Key := [(key1962, -6), (key1964, 6)]

theorem rowCheck10685 : row10685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10685 := by decide +kernel

theorem rowEval10685 (x : Key → ℝ) : Integer.Sparse.eval row10685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10685, Integer.Sparse.eval_collectBalanced, rawRowCheck10685]

def rawRow10686 : Integer.Sparse Key := [(key1964, -4), (key1962, -4), (key1962, -4), (key1964, -4), (key1964, -4), (key1962, -4), (key1964, 6), (key1964, 6), (key1962, 6), (key1964, 6)]

theorem rawRowCheck10686 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form19 = rawRow10686 := by decide +kernel

def row10686 : Integer.Sparse Key := [(key1962, -6), (key1964, 6)]

theorem rowCheck10686 : row10686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10686 := by decide +kernel

theorem rowEval10686 (x : Key → ℝ) : Integer.Sparse.eval row10686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10686, Integer.Sparse.eval_collectBalanced, rawRowCheck10686]

def rawRow10687 : Integer.Sparse Key := [(key1964, -4), (key1964, -4), (key1964, -4), (key1962, -4), (key1962, -4), (key1962, -4), (key1964, 6), (key1964, 6), (key1964, 6), (key1962, 6)]

theorem rawRowCheck10687 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form19 = rawRow10687 := by decide +kernel

def row10687 : Integer.Sparse Key := [(key1962, -6), (key1964, 6)]

theorem rowCheck10687 : row10687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10687 := by decide +kernel

theorem rowEval10687 (x : Key → ℝ) : Integer.Sparse.eval row10687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10687, Integer.Sparse.eval_collectBalanced, rawRowCheck10687]

def rawRow10688 : Integer.Sparse Key := [(key1964, -4), (key1964, -4), (key1964, -4), (key1964, -4), (key1964, -4), (key1964, -4), (key1962, 6), (key1962, 6), (key1962, 6), (key1962, 6)]

theorem rawRowCheck10688 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form19 = rawRow10688 := by decide +kernel

def row10688 : Integer.Sparse Key := [(key1962, 24), (key1964, -24)]

theorem rowCheck10688 : row10688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10688 := by decide +kernel

theorem rowEval10688 (x : Key → ℝ) : Integer.Sparse.eval row10688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10688, Integer.Sparse.eval_collectBalanced, rawRowCheck10688]

def rawRow10689 : Integer.Sparse Key := [(key288, 6), (key289, 6), (key289, 6), (key289, 6), (key289, -24)]

theorem rawRowCheck10689 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form20 = rawRow10689 := by decide +kernel

def row10689 : Integer.Sparse Key := [(key288, 6), (key289, -6)]

theorem rowCheck10689 : row10689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10689 := by decide +kernel

theorem rowEval10689 (x : Key → ℝ) : Integer.Sparse.eval row10689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form20) x := by
  rw [rowCheck10689, Integer.Sparse.eval_collectBalanced, rawRowCheck10689]

def rawRow10690 : Integer.Sparse Key := [(key289, 6), (key288, 6), (key289, 6), (key289, 6), (key289, -24)]

theorem rawRowCheck10690 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form20 = rawRow10690 := by decide +kernel

def row10690 : Integer.Sparse Key := [(key288, 6), (key289, -6)]

theorem rowCheck10690 : row10690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10690 := by decide +kernel

theorem rowEval10690 (x : Key → ℝ) : Integer.Sparse.eval row10690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck10690, Integer.Sparse.eval_collectBalanced, rawRowCheck10690]

def rawRow10691 : Integer.Sparse Key := [(key289, 6), (key289, 6), (key288, 6), (key289, 6), (key289, -24)]

theorem rawRowCheck10691 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form20 = rawRow10691 := by decide +kernel

def row10691 : Integer.Sparse Key := [(key288, 6), (key289, -6)]

theorem rowCheck10691 : row10691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10691 := by decide +kernel

theorem rowEval10691 (x : Key → ℝ) : Integer.Sparse.eval row10691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck10691, Integer.Sparse.eval_collectBalanced, rawRowCheck10691]

def rawRow10692 : Integer.Sparse Key := [(key289, 6), (key289, 6), (key289, 6), (key288, 6), (key289, -24)]

theorem rawRowCheck10692 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form20 = rawRow10692 := by decide +kernel

def row10692 : Integer.Sparse Key := [(key288, 6), (key289, -6)]

theorem rowCheck10692 : row10692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10692 := by decide +kernel

theorem rowEval10692 (x : Key → ℝ) : Integer.Sparse.eval row10692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck10692, Integer.Sparse.eval_collectBalanced, rawRowCheck10692]

def rawRow10693 : Integer.Sparse Key := [(key289, 6), (key289, 6), (key289, 6), (key289, 6), (key288, -24)]

theorem rawRowCheck10693 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form20 = rawRow10693 := by decide +kernel

def row10693 : Integer.Sparse Key := [(key288, -24), (key289, 24)]

theorem rowCheck10693 : row10693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10693 := by decide +kernel

theorem rowEval10693 (x : Key → ℝ) : Integer.Sparse.eval row10693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck10693, Integer.Sparse.eval_collectBalanced, rawRowCheck10693]

def rawRow10694 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2392, 2), (key2406, 2), (key2480, 2), (key2543, 2), (key2437, 2), (key2440, 2), (key2503, 2), (key2554, 2), (key2522, 2), (key2563, 2), (key2378, -2), (key2381, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2472, -2), (key2538, -2), (key2482, -2), (key2543, -2), (key2440, -2), (key2506, -2), (key2554, -2)]

theorem rawRowCheck10694 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form0 = rawRow10694 := by decide +kernel

def row10694 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10694 : row10694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10694 := by decide +kernel

theorem rowEval10694 (x : Key → ℝ) : Integer.Sparse.eval row10694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10694, Integer.Sparse.eval_collectBalanced, rawRowCheck10694]

def rawRow10695 : Integer.Sparse Key := [(key2378, 2), (key2392, 2), (key2390, 2), (key2406, 2), (key2543, 2), (key2480, 2), (key2440, 2), (key2437, 2), (key2554, 2), (key2503, 2), (key2563, 2), (key2522, 2), (key2381, -2), (key2378, -2), (key2392, -2), (key2409, -2), (key2406, -2), (key2538, -2), (key2472, -2), (key2543, -2), (key2482, -2), (key2440, -2), (key2554, -2), (key2506, -2)]

theorem rawRowCheck10695 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form0 = rawRow10695 := by decide +kernel

def row10695 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10695 : row10695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10695 := by decide +kernel

theorem rowEval10695 (x : Key → ℝ) : Integer.Sparse.eval row10695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10695, Integer.Sparse.eval_collectBalanced, rawRowCheck10695]

def rawRow10696 : Integer.Sparse Key := [(key2390, 2), (key2378, 2), (key2392, 2), (key2480, 2), (key2406, 2), (key2543, 2), (key2503, 2), (key2522, 2), (key2437, 2), (key2563, 2), (key2440, 2), (key2554, 2), (key2378, -2), (key2392, -2), (key2381, -2), (key2472, -2), (key2482, -2), (key2406, -2), (key2543, -2), (key2409, -2), (key2538, -2), (key2506, -2), (key2440, -2), (key2554, -2)]

theorem rawRowCheck10696 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form0 = rawRow10696 := by decide +kernel

def row10696 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10696 : row10696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10696 := by decide +kernel

theorem rowEval10696 (x : Key → ℝ) : Integer.Sparse.eval row10696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10696, Integer.Sparse.eval_collectBalanced, rawRowCheck10696]

def rawRow10697 : Integer.Sparse Key := [(key2390, 2), (key2392, 2), (key2378, 2), (key2480, 2), (key2543, 2), (key2406, 2), (key2522, 2), (key2503, 2), (key2563, 2), (key2437, 2), (key2554, 2), (key2440, 2), (key2392, -2), (key2378, -2), (key2381, -2), (key2482, -2), (key2472, -2), (key2543, -2), (key2406, -2), (key2538, -2), (key2409, -2), (key2506, -2), (key2554, -2), (key2440, -2)]

theorem rawRowCheck10697 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form0 = rawRow10697 := by decide +kernel

def row10697 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10697 : row10697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10697 := by decide +kernel

theorem rowEval10697 (x : Key → ℝ) : Integer.Sparse.eval row10697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10697, Integer.Sparse.eval_collectBalanced, rawRowCheck10697]

def rawRow10698 : Integer.Sparse Key := [(key2392, 2), (key2378, 2), (key2390, 2), (key2543, 2), (key2406, 2), (key2480, 2), (key2554, 2), (key2563, 2), (key2440, 2), (key2522, 2), (key2437, 2), (key2503, 2), (key2381, -2), (key2392, -2), (key2378, -2), (key2538, -2), (key2543, -2), (key2409, -2), (key2482, -2), (key2406, -2), (key2472, -2), (key2554, -2), (key2440, -2), (key2506, -2)]

theorem rawRowCheck10698 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form0 = rawRow10698 := by decide +kernel

def row10698 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10698 : row10698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10698 := by decide +kernel

theorem rowEval10698 (x : Key → ℝ) : Integer.Sparse.eval row10698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10698, Integer.Sparse.eval_collectBalanced, rawRowCheck10698]

def rawRow10699 : Integer.Sparse Key := [(key2392, 2), (key2390, 2), (key2378, 2), (key2543, 2), (key2480, 2), (key2406, 2), (key2563, 2), (key2554, 2), (key2522, 2), (key2440, 2), (key2503, 2), (key2437, 2), (key2392, -2), (key2381, -2), (key2378, -2), (key2543, -2), (key2538, -2), (key2482, -2), (key2409, -2), (key2472, -2), (key2406, -2), (key2554, -2), (key2506, -2), (key2440, -2)]

theorem rawRowCheck10699 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form0 = rawRow10699 := by decide +kernel

def row10699 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10699 : row10699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10699 := by decide +kernel

theorem rowEval10699 (x : Key → ℝ) : Integer.Sparse.eval row10699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10699, Integer.Sparse.eval_collectBalanced, rawRowCheck10699]

def rawRow10700 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2440, 2), (key2378, 2), (key2503, 2), (key2554, 2), (key2390, 2), (key2392, 2), (key2480, 2), (key2543, 2), (key2522, 2), (key2563, 2), (key2406, -2), (key2409, -2), (key2440, -2), (key2378, -2), (key2381, -2), (key2472, -2), (key2538, -2), (key2506, -2), (key2554, -2), (key2392, -2), (key2482, -2), (key2543, -2)]

theorem rawRowCheck10700 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form0 = rawRow10700 := by decide +kernel

def row10700 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10700 : row10700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10700 := by decide +kernel

theorem rowEval10700 (x : Key → ℝ) : Integer.Sparse.eval row10700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10700, Integer.Sparse.eval_collectBalanced, rawRowCheck10700]

def rawRow10701 : Integer.Sparse Key := [(key2406, 2), (key2440, 2), (key2437, 2), (key2378, 2), (key2554, 2), (key2503, 2), (key2392, 2), (key2390, 2), (key2543, 2), (key2480, 2), (key2563, 2), (key2522, 2), (key2409, -2), (key2406, -2), (key2440, -2), (key2381, -2), (key2378, -2), (key2538, -2), (key2472, -2), (key2554, -2), (key2506, -2), (key2392, -2), (key2543, -2), (key2482, -2)]

theorem rawRowCheck10701 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form0 = rawRow10701 := by decide +kernel

def row10701 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10701 : row10701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10701 := by decide +kernel

theorem rowEval10701 (x : Key → ℝ) : Integer.Sparse.eval row10701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10701, Integer.Sparse.eval_collectBalanced, rawRowCheck10701]

def rawRow10702 : Integer.Sparse Key := [(key2437, 2), (key2406, 2), (key2440, 2), (key2503, 2), (key2378, 2), (key2554, 2), (key2480, 2), (key2522, 2), (key2390, 2), (key2563, 2), (key2392, 2), (key2543, 2), (key2406, -2), (key2440, -2), (key2409, -2), (key2472, -2), (key2506, -2), (key2378, -2), (key2554, -2), (key2381, -2), (key2538, -2), (key2482, -2), (key2392, -2), (key2543, -2)]

theorem rawRowCheck10702 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form0 = rawRow10702 := by decide +kernel

def row10702 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10702 : row10702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10702 := by decide +kernel

theorem rowEval10702 (x : Key → ℝ) : Integer.Sparse.eval row10702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10702, Integer.Sparse.eval_collectBalanced, rawRowCheck10702]

def rawRow10703 : Integer.Sparse Key := [(key2437, 2), (key2440, 2), (key2406, 2), (key2503, 2), (key2554, 2), (key2378, 2), (key2522, 2), (key2480, 2), (key2563, 2), (key2390, 2), (key2543, 2), (key2392, 2), (key2440, -2), (key2406, -2), (key2409, -2), (key2506, -2), (key2472, -2), (key2554, -2), (key2378, -2), (key2538, -2), (key2381, -2), (key2482, -2), (key2543, -2), (key2392, -2)]

theorem rawRowCheck10703 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form0 = rawRow10703 := by decide +kernel

def row10703 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10703 : row10703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10703 := by decide +kernel

theorem rowEval10703 (x : Key → ℝ) : Integer.Sparse.eval row10703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck10703, Integer.Sparse.eval_collectBalanced, rawRowCheck10703]

def rawRow10704 : Integer.Sparse Key := [(key2440, 2), (key2406, 2), (key2437, 2), (key2554, 2), (key2378, 2), (key2503, 2), (key2543, 2), (key2563, 2), (key2392, 2), (key2522, 2), (key2390, 2), (key2480, 2), (key2409, -2), (key2440, -2), (key2406, -2), (key2538, -2), (key2554, -2), (key2381, -2), (key2506, -2), (key2378, -2), (key2472, -2), (key2543, -2), (key2392, -2), (key2482, -2)]

theorem rawRowCheck10704 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form0 = rawRow10704 := by decide +kernel

def row10704 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10704 : row10704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10704 := by decide +kernel

theorem rowEval10704 (x : Key → ℝ) : Integer.Sparse.eval row10704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10704, Integer.Sparse.eval_collectBalanced, rawRowCheck10704]

def rawRow10705 : Integer.Sparse Key := [(key2440, 2), (key2437, 2), (key2406, 2), (key2554, 2), (key2503, 2), (key2378, 2), (key2563, 2), (key2543, 2), (key2522, 2), (key2392, 2), (key2480, 2), (key2390, 2), (key2440, -2), (key2409, -2), (key2406, -2), (key2554, -2), (key2538, -2), (key2506, -2), (key2381, -2), (key2472, -2), (key2378, -2), (key2543, -2), (key2482, -2), (key2392, -2)]

theorem rawRowCheck10705 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form0 = rawRow10705 := by decide +kernel

def row10705 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10705 : row10705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10705 := by decide +kernel

theorem rowEval10705 (x : Key → ℝ) : Integer.Sparse.eval row10705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck10705, Integer.Sparse.eval_collectBalanced, rawRowCheck10705]

def rawRow10706 : Integer.Sparse Key := [(key2480, 2), (key2503, 2), (key2522, 2), (key2390, 2), (key2437, 2), (key2563, 2), (key2378, 2), (key2392, 2), (key2406, 2), (key2543, 2), (key2440, 2), (key2554, 2), (key2472, -2), (key2482, -2), (key2506, -2), (key2378, -2), (key2392, -2), (key2406, -2), (key2543, -2), (key2440, -2), (key2554, -2), (key2381, -2), (key2409, -2), (key2538, -2)]

theorem rawRowCheck10706 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form0 = rawRow10706 := by decide +kernel

def row10706 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10706 : row10706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10706 := by decide +kernel

theorem rowEval10706 (x : Key → ℝ) : Integer.Sparse.eval row10706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10706, Integer.Sparse.eval_collectBalanced, rawRowCheck10706]

def rawRow10707 : Integer.Sparse Key := [(key2480, 2), (key2522, 2), (key2503, 2), (key2390, 2), (key2563, 2), (key2437, 2), (key2392, 2), (key2378, 2), (key2543, 2), (key2406, 2), (key2554, 2), (key2440, 2), (key2482, -2), (key2472, -2), (key2506, -2), (key2392, -2), (key2378, -2), (key2543, -2), (key2406, -2), (key2554, -2), (key2440, -2), (key2381, -2), (key2538, -2), (key2409, -2)]

theorem rawRowCheck10707 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form0 = rawRow10707 := by decide +kernel

def row10707 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10707 : row10707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10707 := by decide +kernel

theorem rowEval10707 (x : Key → ℝ) : Integer.Sparse.eval row10707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10707, Integer.Sparse.eval_collectBalanced, rawRowCheck10707]

def rawRow10708 : Integer.Sparse Key := [(key2503, 2), (key2480, 2), (key2522, 2), (key2437, 2), (key2390, 2), (key2563, 2), (key2406, 2), (key2440, 2), (key2378, 2), (key2554, 2), (key2392, 2), (key2543, 2), (key2472, -2), (key2506, -2), (key2482, -2), (key2406, -2), (key2440, -2), (key2378, -2), (key2554, -2), (key2392, -2), (key2543, -2), (key2409, -2), (key2381, -2), (key2538, -2)]

theorem rawRowCheck10708 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form0 = rawRow10708 := by decide +kernel

def row10708 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10708 : row10708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10708 := by decide +kernel

theorem rowEval10708 (x : Key → ℝ) : Integer.Sparse.eval row10708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10708, Integer.Sparse.eval_collectBalanced, rawRowCheck10708]

def rawRow10709 : Integer.Sparse Key := [(key2503, 2), (key2522, 2), (key2480, 2), (key2437, 2), (key2563, 2), (key2390, 2), (key2440, 2), (key2406, 2), (key2554, 2), (key2378, 2), (key2543, 2), (key2392, 2), (key2506, -2), (key2472, -2), (key2482, -2), (key2440, -2), (key2406, -2), (key2554, -2), (key2378, -2), (key2543, -2), (key2392, -2), (key2409, -2), (key2538, -2), (key2381, -2)]

theorem rawRowCheck10709 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form0 = rawRow10709 := by decide +kernel

def row10709 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10709 : row10709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10709 := by decide +kernel

theorem rowEval10709 (x : Key → ℝ) : Integer.Sparse.eval row10709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck10709, Integer.Sparse.eval_collectBalanced, rawRowCheck10709]

def rawRow10710 : Integer.Sparse Key := [(key2522, 2), (key2480, 2), (key2503, 2), (key2563, 2), (key2390, 2), (key2437, 2), (key2543, 2), (key2554, 2), (key2392, 2), (key2440, 2), (key2378, 2), (key2406, 2), (key2482, -2), (key2506, -2), (key2472, -2), (key2543, -2), (key2554, -2), (key2392, -2), (key2440, -2), (key2378, -2), (key2406, -2), (key2538, -2), (key2381, -2), (key2409, -2)]

theorem rawRowCheck10710 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form0 = rawRow10710 := by decide +kernel

def row10710 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10710 : row10710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10710 := by decide +kernel

theorem rowEval10710 (x : Key → ℝ) : Integer.Sparse.eval row10710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10710, Integer.Sparse.eval_collectBalanced, rawRowCheck10710]

def rawRow10711 : Integer.Sparse Key := [(key2522, 2), (key2503, 2), (key2480, 2), (key2563, 2), (key2437, 2), (key2390, 2), (key2554, 2), (key2543, 2), (key2440, 2), (key2392, 2), (key2406, 2), (key2378, 2), (key2506, -2), (key2482, -2), (key2472, -2), (key2554, -2), (key2543, -2), (key2440, -2), (key2392, -2), (key2406, -2), (key2378, -2), (key2538, -2), (key2409, -2), (key2381, -2)]

theorem rawRowCheck10711 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form0 = rawRow10711 := by decide +kernel

def row10711 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10711 : row10711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10711 := by decide +kernel

theorem rowEval10711 (x : Key → ℝ) : Integer.Sparse.eval row10711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck10711, Integer.Sparse.eval_collectBalanced, rawRowCheck10711]

def rawRow10712 : Integer.Sparse Key := [(key2543, 2), (key2554, 2), (key2563, 2), (key2392, 2), (key2440, 2), (key2522, 2), (key2378, 2), (key2390, 2), (key2406, 2), (key2480, 2), (key2437, 2), (key2503, 2), (key2538, -2), (key2543, -2), (key2554, -2), (key2381, -2), (key2392, -2), (key2409, -2), (key2482, -2), (key2440, -2), (key2506, -2), (key2378, -2), (key2406, -2), (key2472, -2)]

theorem rawRowCheck10712 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form0 = rawRow10712 := by decide +kernel

def row10712 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10712 : row10712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10712 := by decide +kernel

theorem rowEval10712 (x : Key → ℝ) : Integer.Sparse.eval row10712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10712, Integer.Sparse.eval_collectBalanced, rawRowCheck10712]

def rawRow10713 : Integer.Sparse Key := [(key2543, 2), (key2563, 2), (key2554, 2), (key2392, 2), (key2522, 2), (key2440, 2), (key2390, 2), (key2378, 2), (key2480, 2), (key2406, 2), (key2503, 2), (key2437, 2), (key2543, -2), (key2538, -2), (key2554, -2), (key2392, -2), (key2381, -2), (key2482, -2), (key2409, -2), (key2506, -2), (key2440, -2), (key2378, -2), (key2472, -2), (key2406, -2)]

theorem rawRowCheck10713 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form0 = rawRow10713 := by decide +kernel

def row10713 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10713 : row10713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10713 := by decide +kernel

theorem rowEval10713 (x : Key → ℝ) : Integer.Sparse.eval row10713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10713, Integer.Sparse.eval_collectBalanced, rawRowCheck10713]

def rawRow10714 : Integer.Sparse Key := [(key2554, 2), (key2543, 2), (key2563, 2), (key2440, 2), (key2392, 2), (key2522, 2), (key2406, 2), (key2437, 2), (key2378, 2), (key2503, 2), (key2390, 2), (key2480, 2), (key2538, -2), (key2554, -2), (key2543, -2), (key2409, -2), (key2440, -2), (key2381, -2), (key2506, -2), (key2392, -2), (key2482, -2), (key2406, -2), (key2378, -2), (key2472, -2)]

theorem rawRowCheck10714 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form0 = rawRow10714 := by decide +kernel

def row10714 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10714 : row10714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10714 := by decide +kernel

theorem rowEval10714 (x : Key → ℝ) : Integer.Sparse.eval row10714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10714, Integer.Sparse.eval_collectBalanced, rawRowCheck10714]

def rawRow10715 : Integer.Sparse Key := [(key2554, 2), (key2563, 2), (key2543, 2), (key2440, 2), (key2522, 2), (key2392, 2), (key2437, 2), (key2406, 2), (key2503, 2), (key2378, 2), (key2480, 2), (key2390, 2), (key2554, -2), (key2538, -2), (key2543, -2), (key2440, -2), (key2409, -2), (key2506, -2), (key2381, -2), (key2482, -2), (key2392, -2), (key2406, -2), (key2472, -2), (key2378, -2)]

theorem rawRowCheck10715 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form0 = rawRow10715 := by decide +kernel

def row10715 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10715 : row10715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10715 := by decide +kernel

theorem rowEval10715 (x : Key → ℝ) : Integer.Sparse.eval row10715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck10715, Integer.Sparse.eval_collectBalanced, rawRowCheck10715]

def rawRow10716 : Integer.Sparse Key := [(key2563, 2), (key2543, 2), (key2554, 2), (key2522, 2), (key2392, 2), (key2440, 2), (key2480, 2), (key2503, 2), (key2390, 2), (key2437, 2), (key2378, 2), (key2406, 2), (key2543, -2), (key2554, -2), (key2538, -2), (key2482, -2), (key2506, -2), (key2392, -2), (key2440, -2), (key2381, -2), (key2409, -2), (key2472, -2), (key2378, -2), (key2406, -2)]

theorem rawRowCheck10716 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form0 = rawRow10716 := by decide +kernel

def row10716 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10716 : row10716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10716 := by decide +kernel

theorem rowEval10716 (x : Key → ℝ) : Integer.Sparse.eval row10716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10716, Integer.Sparse.eval_collectBalanced, rawRowCheck10716]

def rawRow10717 : Integer.Sparse Key := [(key2563, 2), (key2554, 2), (key2543, 2), (key2522, 2), (key2440, 2), (key2392, 2), (key2503, 2), (key2480, 2), (key2437, 2), (key2390, 2), (key2406, 2), (key2378, 2), (key2554, -2), (key2543, -2), (key2538, -2), (key2506, -2), (key2482, -2), (key2440, -2), (key2392, -2), (key2409, -2), (key2381, -2), (key2472, -2), (key2406, -2), (key2378, -2)]

theorem rawRowCheck10717 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form0 = rawRow10717 := by decide +kernel

def row10717 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

theorem rowCheck10717 : row10717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10717 := by decide +kernel

theorem rowEval10717 (x : Key → ℝ) : Integer.Sparse.eval row10717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck10717, Integer.Sparse.eval_collectBalanced, rawRowCheck10717]

def rawRow10718 : Integer.Sparse Key := [(key2381, 2), (key2392, 2), (key2392, 2), (key2409, 2), (key2482, 2), (key2482, 2), (key2440, 2), (key2440, 2), (key2506, 2), (key2506, 2), (key2522, 2), (key2522, 2), (key2378, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2406, -2), (key2472, -2), (key2472, -2), (key2480, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2503, -2)]

theorem rawRowCheck10718 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form0 = rawRow10718 := by decide +kernel

def row10718 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

theorem rowCheck10718 : row10718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10718 := by decide +kernel

theorem rowEval10718 (x : Key → ℝ) : Integer.Sparse.eval row10718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10718, Integer.Sparse.eval_collectBalanced, rawRowCheck10718]

def rawRow10719 : Integer.Sparse Key := [(key2392, 2), (key2381, 2), (key2392, 2), (key2482, 2), (key2409, 2), (key2482, 2), (key2506, 2), (key2522, 2), (key2440, 2), (key2522, 2), (key2440, 2), (key2506, 2), (key2378, -2), (key2390, -2), (key2378, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2503, -2), (key2437, -2), (key2503, -2)]

theorem rawRowCheck10719 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form0 = rawRow10719 := by decide +kernel

def row10719 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

theorem rowCheck10719 : row10719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10719 := by decide +kernel

theorem rowEval10719 (x : Key → ℝ) : Integer.Sparse.eval row10719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10719, Integer.Sparse.eval_collectBalanced, rawRowCheck10719]

def rawRow10720 : Integer.Sparse Key := [(key2392, 2), (key2392, 2), (key2381, 2), (key2482, 2), (key2482, 2), (key2409, 2), (key2522, 2), (key2506, 2), (key2522, 2), (key2440, 2), (key2506, 2), (key2440, 2), (key2390, -2), (key2378, -2), (key2378, -2), (key2480, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2406, -2), (key2503, -2), (key2503, -2), (key2437, -2)]

theorem rawRowCheck10720 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form0 = rawRow10720 := by decide +kernel

def row10720 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

theorem rowCheck10720 : row10720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10720 := by decide +kernel

theorem rowEval10720 (x : Key → ℝ) : Integer.Sparse.eval row10720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10720, Integer.Sparse.eval_collectBalanced, rawRowCheck10720]

def rawRow10721 : Integer.Sparse Key := [(key2409, 2), (key2440, 2), (key2440, 2), (key2381, 2), (key2506, 2), (key2506, 2), (key2392, 2), (key2392, 2), (key2482, 2), (key2482, 2), (key2522, 2), (key2522, 2), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2378, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2480, -2)]

theorem rawRowCheck10721 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form0 = rawRow10721 := by decide +kernel

def row10721 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

theorem rowCheck10721 : row10721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10721 := by decide +kernel

theorem rowEval10721 (x : Key → ℝ) : Integer.Sparse.eval row10721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10721, Integer.Sparse.eval_collectBalanced, rawRowCheck10721]

def rawRow10722 : Integer.Sparse Key := [(key2440, 2), (key2409, 2), (key2440, 2), (key2506, 2), (key2381, 2), (key2506, 2), (key2482, 2), (key2522, 2), (key2392, 2), (key2522, 2), (key2392, 2), (key2482, 2), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2480, -2), (key2390, -2), (key2480, -2)]

theorem rawRowCheck10722 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form0 = rawRow10722 := by decide +kernel

def row10722 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

theorem rowCheck10722 : row10722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10722 := by decide +kernel

theorem rowEval10722 (x : Key → ℝ) : Integer.Sparse.eval row10722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10722, Integer.Sparse.eval_collectBalanced, rawRowCheck10722]

def rawRow10723 : Integer.Sparse Key := [(key2440, 2), (key2440, 2), (key2409, 2), (key2506, 2), (key2506, 2), (key2381, 2), (key2522, 2), (key2482, 2), (key2522, 2), (key2392, 2), (key2482, 2), (key2392, 2), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2378, -2), (key2480, -2), (key2480, -2), (key2390, -2)]

theorem rawRowCheck10723 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form0 = rawRow10723 := by decide +kernel

def row10723 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

theorem rowCheck10723 : row10723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10723 := by decide +kernel

theorem rowEval10723 (x : Key → ℝ) : Integer.Sparse.eval row10723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck10723, Integer.Sparse.eval_collectBalanced, rawRowCheck10723]

def rawRow10724 : Integer.Sparse Key := [(key2482, 2), (key2506, 2), (key2522, 2), (key2392, 2), (key2440, 2), (key2522, 2), (key2381, 2), (key2392, 2), (key2409, 2), (key2482, 2), (key2440, 2), (key2506, 2), (key2472, -2), (key2480, -2), (key2503, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2378, -2), (key2406, -2), (key2472, -2)]

theorem rawRowCheck10724 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form0 = rawRow10724 := by decide +kernel

def row10724 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

theorem rowCheck10724 : row10724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10724 := by decide +kernel

theorem rowEval10724 (x : Key → ℝ) : Integer.Sparse.eval row10724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10724, Integer.Sparse.eval_collectBalanced, rawRowCheck10724]

def rawRow10725 : Integer.Sparse Key := [(key2482, 2), (key2522, 2), (key2506, 2), (key2392, 2), (key2522, 2), (key2440, 2), (key2392, 2), (key2381, 2), (key2482, 2), (key2409, 2), (key2506, 2), (key2440, 2), (key2480, -2), (key2472, -2), (key2503, -2), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2378, -2), (key2472, -2), (key2406, -2)]

theorem rawRowCheck10725 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form0 = rawRow10725 := by decide +kernel

def row10725 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

theorem rowCheck10725 : row10725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10725 := by decide +kernel

theorem rowEval10725 (x : Key → ℝ) : Integer.Sparse.eval row10725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10725, Integer.Sparse.eval_collectBalanced, rawRowCheck10725]

def rawRow10726 : Integer.Sparse Key := [(key2506, 2), (key2482, 2), (key2522, 2), (key2440, 2), (key2392, 2), (key2522, 2), (key2409, 2), (key2440, 2), (key2381, 2), (key2506, 2), (key2392, 2), (key2482, 2), (key2472, -2), (key2503, -2), (key2480, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2406, -2), (key2378, -2), (key2472, -2)]

theorem rawRowCheck10726 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form0 = rawRow10726 := by decide +kernel

def row10726 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

theorem rowCheck10726 : row10726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10726 := by decide +kernel

theorem rowEval10726 (x : Key → ℝ) : Integer.Sparse.eval row10726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10726, Integer.Sparse.eval_collectBalanced, rawRowCheck10726]

def rawRow10727 : Integer.Sparse Key := [(key2506, 2), (key2522, 2), (key2482, 2), (key2440, 2), (key2522, 2), (key2392, 2), (key2440, 2), (key2409, 2), (key2506, 2), (key2381, 2), (key2482, 2), (key2392, 2), (key2503, -2), (key2472, -2), (key2480, -2), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2406, -2), (key2472, -2), (key2378, -2)]

theorem rawRowCheck10727 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form0 = rawRow10727 := by decide +kernel

def row10727 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

theorem rowCheck10727 : row10727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10727 := by decide +kernel

theorem rowEval10727 (x : Key → ℝ) : Integer.Sparse.eval row10727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck10727, Integer.Sparse.eval_collectBalanced, rawRowCheck10727]

def rawRow10728 : Integer.Sparse Key := [(key2522, 2), (key2482, 2), (key2506, 2), (key2522, 2), (key2392, 2), (key2440, 2), (key2482, 2), (key2506, 2), (key2392, 2), (key2440, 2), (key2381, 2), (key2409, 2), (key2480, -2), (key2503, -2), (key2472, -2), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2472, -2), (key2378, -2), (key2406, -2)]

theorem rawRowCheck10728 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form0 = rawRow10728 := by decide +kernel

def row10728 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

theorem rowCheck10728 : row10728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10728 := by decide +kernel

theorem rowEval10728 (x : Key → ℝ) : Integer.Sparse.eval row10728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10728, Integer.Sparse.eval_collectBalanced, rawRowCheck10728]

def rawRow10729 : Integer.Sparse Key := [(key2522, 2), (key2506, 2), (key2482, 2), (key2522, 2), (key2440, 2), (key2392, 2), (key2506, 2), (key2482, 2), (key2440, 2), (key2392, 2), (key2409, 2), (key2381, 2), (key2503, -2), (key2480, -2), (key2472, -2), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2472, -2), (key2406, -2), (key2378, -2)]

theorem rawRowCheck10729 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form0 = rawRow10729 := by decide +kernel

def row10729 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

theorem rowCheck10729 : row10729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10729 := by decide +kernel

theorem rowEval10729 (x : Key → ℝ) : Integer.Sparse.eval row10729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck10729, Integer.Sparse.eval_collectBalanced, rawRowCheck10729]

def rawRow10730 : Integer.Sparse Key := [(key1103, -24), (key990, 6), (key1025, 6), (key1103, 6), (key1187, 6)]

theorem rawRowCheck10730 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form1 = rawRow10730 := by decide +kernel

def row10730 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10730 : row10730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10730 := by decide +kernel

theorem rowEval10730 (x : Key → ℝ) : Integer.Sparse.eval row10730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10730, Integer.Sparse.eval_collectBalanced, rawRowCheck10730]

def rawRow10731 : Integer.Sparse Key := [(key1103, -24), (key990, 6), (key1025, 6), (key1187, 6), (key1103, 6)]

theorem rawRowCheck10731 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form1 = rawRow10731 := by decide +kernel

def row10731 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10731 : row10731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10731 := by decide +kernel

theorem rowEval10731 (x : Key → ℝ) : Integer.Sparse.eval row10731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10731, Integer.Sparse.eval_collectBalanced, rawRowCheck10731]

def rawRow10732 : Integer.Sparse Key := [(key1103, -24), (key990, 6), (key1103, 6), (key1025, 6), (key1187, 6)]

theorem rawRowCheck10732 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form1 = rawRow10732 := by decide +kernel

def row10732 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10732 : row10732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10732 := by decide +kernel

theorem rowEval10732 (x : Key → ℝ) : Integer.Sparse.eval row10732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10732, Integer.Sparse.eval_collectBalanced, rawRowCheck10732]

def rawRow10733 : Integer.Sparse Key := [(key1103, -24), (key990, 6), (key1103, 6), (key1187, 6), (key1025, 6)]

theorem rawRowCheck10733 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form1 = rawRow10733 := by decide +kernel

def row10733 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10733 : row10733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10733 := by decide +kernel

theorem rowEval10733 (x : Key → ℝ) : Integer.Sparse.eval row10733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10733, Integer.Sparse.eval_collectBalanced, rawRowCheck10733]

def rawRow10734 : Integer.Sparse Key := [(key1103, -24), (key990, 6), (key1187, 6), (key1025, 6), (key1103, 6)]

theorem rawRowCheck10734 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form1 = rawRow10734 := by decide +kernel

def row10734 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10734 : row10734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10734 := by decide +kernel

theorem rowEval10734 (x : Key → ℝ) : Integer.Sparse.eval row10734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10734, Integer.Sparse.eval_collectBalanced, rawRowCheck10734]

def rawRow10735 : Integer.Sparse Key := [(key1103, -24), (key990, 6), (key1187, 6), (key1103, 6), (key1025, 6)]

theorem rawRowCheck10735 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form1 = rawRow10735 := by decide +kernel

def row10735 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10735 : row10735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10735 := by decide +kernel

theorem rowEval10735 (x : Key → ℝ) : Integer.Sparse.eval row10735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10735, Integer.Sparse.eval_collectBalanced, rawRowCheck10735]

def rawRow10736 : Integer.Sparse Key := [(key1103, -24), (key1025, 6), (key990, 6), (key1103, 6), (key1187, 6)]

theorem rawRowCheck10736 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form1 = rawRow10736 := by decide +kernel

def row10736 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10736 : row10736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10736 := by decide +kernel

theorem rowEval10736 (x : Key → ℝ) : Integer.Sparse.eval row10736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10736, Integer.Sparse.eval_collectBalanced, rawRowCheck10736]

def rawRow10737 : Integer.Sparse Key := [(key1103, -24), (key1025, 6), (key990, 6), (key1187, 6), (key1103, 6)]

theorem rawRowCheck10737 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form1 = rawRow10737 := by decide +kernel

def row10737 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10737 : row10737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10737 := by decide +kernel

theorem rowEval10737 (x : Key → ℝ) : Integer.Sparse.eval row10737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10737, Integer.Sparse.eval_collectBalanced, rawRowCheck10737]

def rawRow10738 : Integer.Sparse Key := [(key1103, -24), (key1025, 6), (key1103, 6), (key990, 6), (key1187, 6)]

theorem rawRowCheck10738 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form1 = rawRow10738 := by decide +kernel

def row10738 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10738 : row10738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10738 := by decide +kernel

theorem rowEval10738 (x : Key → ℝ) : Integer.Sparse.eval row10738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10738, Integer.Sparse.eval_collectBalanced, rawRowCheck10738]

def rawRow10739 : Integer.Sparse Key := [(key1103, -24), (key1025, 6), (key1103, 6), (key1187, 6), (key990, 6)]

theorem rawRowCheck10739 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form1 = rawRow10739 := by decide +kernel

def row10739 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10739 : row10739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10739 := by decide +kernel

theorem rowEval10739 (x : Key → ℝ) : Integer.Sparse.eval row10739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10739, Integer.Sparse.eval_collectBalanced, rawRowCheck10739]

def rawRow10740 : Integer.Sparse Key := [(key1103, -24), (key1025, 6), (key1187, 6), (key990, 6), (key1103, 6)]

theorem rawRowCheck10740 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form1 = rawRow10740 := by decide +kernel

def row10740 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10740 : row10740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10740 := by decide +kernel

theorem rowEval10740 (x : Key → ℝ) : Integer.Sparse.eval row10740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10740, Integer.Sparse.eval_collectBalanced, rawRowCheck10740]

def rawRow10741 : Integer.Sparse Key := [(key1103, -24), (key1025, 6), (key1187, 6), (key1103, 6), (key990, 6)]

theorem rawRowCheck10741 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form1 = rawRow10741 := by decide +kernel

def row10741 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10741 : row10741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10741 := by decide +kernel

theorem rowEval10741 (x : Key → ℝ) : Integer.Sparse.eval row10741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10741, Integer.Sparse.eval_collectBalanced, rawRowCheck10741]

def rawRow10742 : Integer.Sparse Key := [(key1103, -24), (key1103, 6), (key990, 6), (key1025, 6), (key1187, 6)]

theorem rawRowCheck10742 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form1 = rawRow10742 := by decide +kernel

def row10742 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10742 : row10742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10742 := by decide +kernel

theorem rowEval10742 (x : Key → ℝ) : Integer.Sparse.eval row10742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10742, Integer.Sparse.eval_collectBalanced, rawRowCheck10742]

def rawRow10743 : Integer.Sparse Key := [(key1103, -24), (key1103, 6), (key990, 6), (key1187, 6), (key1025, 6)]

theorem rawRowCheck10743 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form1 = rawRow10743 := by decide +kernel

def row10743 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10743 : row10743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10743 := by decide +kernel

theorem rowEval10743 (x : Key → ℝ) : Integer.Sparse.eval row10743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10743, Integer.Sparse.eval_collectBalanced, rawRowCheck10743]

def rawRow10744 : Integer.Sparse Key := [(key1103, -24), (key1103, 6), (key1025, 6), (key990, 6), (key1187, 6)]

theorem rawRowCheck10744 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form1 = rawRow10744 := by decide +kernel

def row10744 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10744 : row10744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10744 := by decide +kernel

theorem rowEval10744 (x : Key → ℝ) : Integer.Sparse.eval row10744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10744, Integer.Sparse.eval_collectBalanced, rawRowCheck10744]

def rawRow10745 : Integer.Sparse Key := [(key1103, -24), (key1103, 6), (key1025, 6), (key1187, 6), (key990, 6)]

theorem rawRowCheck10745 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form1 = rawRow10745 := by decide +kernel

def row10745 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10745 : row10745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10745 := by decide +kernel

theorem rowEval10745 (x : Key → ℝ) : Integer.Sparse.eval row10745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10745, Integer.Sparse.eval_collectBalanced, rawRowCheck10745]

def rawRow10746 : Integer.Sparse Key := [(key1103, -24), (key1103, 6), (key1187, 6), (key990, 6), (key1025, 6)]

theorem rawRowCheck10746 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form1 = rawRow10746 := by decide +kernel

def row10746 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10746 : row10746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10746 := by decide +kernel

theorem rowEval10746 (x : Key → ℝ) : Integer.Sparse.eval row10746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10746, Integer.Sparse.eval_collectBalanced, rawRowCheck10746]

def rawRow10747 : Integer.Sparse Key := [(key1103, -24), (key1103, 6), (key1187, 6), (key1025, 6), (key990, 6)]

theorem rawRowCheck10747 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form1 = rawRow10747 := by decide +kernel

def row10747 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10747 : row10747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10747 := by decide +kernel

theorem rowEval10747 (x : Key → ℝ) : Integer.Sparse.eval row10747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10747, Integer.Sparse.eval_collectBalanced, rawRowCheck10747]

def rawRow10748 : Integer.Sparse Key := [(key1103, -24), (key1187, 6), (key990, 6), (key1025, 6), (key1103, 6)]

theorem rawRowCheck10748 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form1 = rawRow10748 := by decide +kernel

def row10748 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10748 : row10748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10748 := by decide +kernel

theorem rowEval10748 (x : Key → ℝ) : Integer.Sparse.eval row10748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10748, Integer.Sparse.eval_collectBalanced, rawRowCheck10748]

def rawRow10749 : Integer.Sparse Key := [(key1103, -24), (key1187, 6), (key990, 6), (key1103, 6), (key1025, 6)]

theorem rawRowCheck10749 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form1 = rawRow10749 := by decide +kernel

def row10749 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10749 : row10749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10749 := by decide +kernel

theorem rowEval10749 (x : Key → ℝ) : Integer.Sparse.eval row10749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10749, Integer.Sparse.eval_collectBalanced, rawRowCheck10749]

def rawRow10750 : Integer.Sparse Key := [(key1103, -24), (key1187, 6), (key1025, 6), (key990, 6), (key1103, 6)]

theorem rawRowCheck10750 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form1 = rawRow10750 := by decide +kernel

def row10750 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10750 : row10750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10750 := by decide +kernel

theorem rowEval10750 (x : Key → ℝ) : Integer.Sparse.eval row10750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10750, Integer.Sparse.eval_collectBalanced, rawRowCheck10750]

def rawRow10751 : Integer.Sparse Key := [(key1103, -24), (key1187, 6), (key1025, 6), (key1103, 6), (key990, 6)]

theorem rawRowCheck10751 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form1 = rawRow10751 := by decide +kernel

def row10751 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10751 : row10751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10751 := by decide +kernel

theorem rowEval10751 (x : Key → ℝ) : Integer.Sparse.eval row10751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10751, Integer.Sparse.eval_collectBalanced, rawRowCheck10751]

end MUB6.Certificate.GramRows

end OAI
