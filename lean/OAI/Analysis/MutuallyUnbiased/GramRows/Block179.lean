import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19840 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1528, 24), (key1253, 24), (key1606, 24)]

theorem rawRowCheck19840 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form3 = rawRow19840 := by decide +kernel

def row19840 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19840 : row19840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19840 := by decide +kernel

theorem rowEval19840 (x : Key → ℝ) : Integer.Sparse.eval row19840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19840, Integer.Sparse.eval_collectBalanced, rawRowCheck19840]

def rawRow19841 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1528, 24), (key1606, 24), (key1253, 24)]

theorem rawRowCheck19841 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form3 = rawRow19841 := by decide +kernel

def row19841 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19841 : row19841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19841 := by decide +kernel

theorem rowEval19841 (x : Key → ℝ) : Integer.Sparse.eval row19841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19841, Integer.Sparse.eval_collectBalanced, rawRowCheck19841]

def rawRow19842 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1606, 24), (key1253, 24), (key1528, 24)]

theorem rawRowCheck19842 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form3 = rawRow19842 := by decide +kernel

def row19842 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19842 : row19842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19842 := by decide +kernel

theorem rowEval19842 (x : Key → ℝ) : Integer.Sparse.eval row19842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19842, Integer.Sparse.eval_collectBalanced, rawRowCheck19842]

def rawRow19843 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1606, 24), (key1528, 24), (key1253, 24)]

theorem rawRowCheck19843 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form3 = rawRow19843 := by decide +kernel

def row19843 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

theorem rowCheck19843 : row19843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19843 := by decide +kernel

theorem rowEval19843 (x : Key → ℝ) : Integer.Sparse.eval row19843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19843, Integer.Sparse.eval_collectBalanced, rawRowCheck19843]

def rawRow19844 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key23, 6), (key35, 6), (key375, 6), (key381, 6), (key381, 6), (key426, 6), (key432, 6), (key426, 6), (key460, 6), (key432, 6), (key460, 6), (key486, 6), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key659, 6), (key663, 6)]

theorem rawRowCheck19844 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form4 = rawRow19844 := by decide +kernel

def row19844 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

theorem rowCheck19844 : row19844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19844 := by decide +kernel

theorem rowEval19844 (x : Key → ℝ) : Integer.Sparse.eval row19844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19844, Integer.Sparse.eval_collectBalanced, rawRowCheck19844]

def rawRow19845 : Integer.Sparse Key := [(key23, 6), (key18, 6), (key23, 6), (key35, 6), (key381, 6), (key375, 6), (key381, 6), (key432, 6), (key426, 6), (key460, 6), (key426, 6), (key460, 6), (key432, 6), (key486, 6), (key490, 6), (key486, 6), (key654, 6), (key659, 6), (key663, 6), (key659, 6)]

theorem rawRowCheck19845 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form4 = rawRow19845 := by decide +kernel

def row19845 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

theorem rowCheck19845 : row19845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19845 := by decide +kernel

theorem rowEval19845 (x : Key → ℝ) : Integer.Sparse.eval row19845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19845, Integer.Sparse.eval_collectBalanced, rawRowCheck19845]

def rawRow19846 : Integer.Sparse Key := [(key23, 6), (key23, 6), (key18, 6), (key35, 6), (key381, 6), (key381, 6), (key375, 6), (key460, 6), (key460, 6), (key432, 6), (key432, 6), (key426, 6), (key426, 6), (key490, 6), (key486, 6), (key486, 6), (key654, 6), (key663, 6), (key659, 6), (key659, 6)]

theorem rawRowCheck19846 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form4 = rawRow19846 := by decide +kernel

def row19846 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

theorem rowCheck19846 : row19846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19846 := by decide +kernel

theorem rowEval19846 (x : Key → ℝ) : Integer.Sparse.eval row19846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19846, Integer.Sparse.eval_collectBalanced, rawRowCheck19846]

def rawRow19847 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key23, 6), (key426, 6), (key432, 6), (key486, 6), (key375, 6), (key381, 6), (key426, 6), (key460, 6), (key486, 6), (key490, 6), (key381, 6), (key432, 6), (key460, 6), (key659, 6), (key654, 6), (key659, 6), (key663, 6)]

theorem rawRowCheck19847 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form4 = rawRow19847 := by decide +kernel

def row19847 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

theorem rowCheck19847 : row19847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19847 := by decide +kernel

theorem rowEval19847 (x : Key → ℝ) : Integer.Sparse.eval row19847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19847, Integer.Sparse.eval_collectBalanced, rawRowCheck19847]

def rawRow19848 : Integer.Sparse Key := [(key23, 6), (key18, 6), (key35, 6), (key23, 6), (key432, 6), (key426, 6), (key486, 6), (key381, 6), (key375, 6), (key460, 6), (key426, 6), (key490, 6), (key486, 6), (key381, 6), (key460, 6), (key432, 6), (key659, 6), (key654, 6), (key663, 6), (key659, 6)]

theorem rawRowCheck19848 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form4 = rawRow19848 := by decide +kernel

def row19848 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

theorem rowCheck19848 : row19848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19848 := by decide +kernel

theorem rowEval19848 (x : Key → ℝ) : Integer.Sparse.eval row19848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19848, Integer.Sparse.eval_collectBalanced, rawRowCheck19848]

def rawRow19849 : Integer.Sparse Key := [(key18, 6), (key35, 6), (key23, 6), (key23, 6), (key426, 6), (key486, 6), (key432, 6), (key426, 6), (key486, 6), (key375, 6), (key490, 6), (key381, 6), (key460, 6), (key432, 6), (key381, 6), (key460, 6), (key659, 6), (key659, 6), (key654, 6), (key663, 6)]

theorem rawRowCheck19849 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form4 = rawRow19849 := by decide +kernel

def row19849 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

theorem rowCheck19849 : row19849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19849 := by decide +kernel

theorem rowEval19849 (x : Key → ℝ) : Integer.Sparse.eval row19849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19849, Integer.Sparse.eval_collectBalanced, rawRowCheck19849]

def rawRow19850 : Integer.Sparse Key := [(key35, 6), (key18, 6), (key23, 6), (key23, 6), (key486, 6), (key426, 6), (key432, 6), (key486, 6), (key426, 6), (key490, 6), (key375, 6), (key460, 6), (key381, 6), (key432, 6), (key460, 6), (key381, 6), (key659, 6), (key659, 6), (key663, 6), (key654, 6)]

theorem rawRowCheck19850 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form4 = rawRow19850 := by decide +kernel

def row19850 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

theorem rowCheck19850 : row19850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19850 := by decide +kernel

theorem rowEval19850 (x : Key → ℝ) : Integer.Sparse.eval row19850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19850, Integer.Sparse.eval_collectBalanced, rawRowCheck19850]

def rawRow19851 : Integer.Sparse Key := [(key23, 6), (key35, 6), (key18, 6), (key23, 6), (key432, 6), (key486, 6), (key426, 6), (key460, 6), (key490, 6), (key381, 6), (key486, 6), (key375, 6), (key426, 6), (key460, 6), (key381, 6), (key432, 6), (key659, 6), (key663, 6), (key654, 6), (key659, 6)]

theorem rawRowCheck19851 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form4 = rawRow19851 := by decide +kernel

def row19851 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

theorem rowCheck19851 : row19851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19851 := by decide +kernel

theorem rowEval19851 (x : Key → ℝ) : Integer.Sparse.eval row19851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19851, Integer.Sparse.eval_collectBalanced, rawRowCheck19851]

def rawRow19852 : Integer.Sparse Key := [(key35, 6), (key23, 6), (key18, 6), (key23, 6), (key486, 6), (key432, 6), (key426, 6), (key490, 6), (key460, 6), (key486, 6), (key381, 6), (key426, 6), (key375, 6), (key460, 6), (key432, 6), (key381, 6), (key659, 6), (key663, 6), (key659, 6), (key654, 6)]

theorem rawRowCheck19852 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form4 = rawRow19852 := by decide +kernel

def row19852 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

theorem rowCheck19852 : row19852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19852 := by decide +kernel

theorem rowEval19852 (x : Key → ℝ) : Integer.Sparse.eval row19852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19852, Integer.Sparse.eval_collectBalanced, rawRowCheck19852]

def rawRow19853 : Integer.Sparse Key := [(key23, 6), (key23, 6), (key35, 6), (key18, 6), (key460, 6), (key460, 6), (key490, 6), (key381, 6), (key381, 6), (key432, 6), (key432, 6), (key486, 6), (key486, 6), (key375, 6), (key426, 6), (key426, 6), (key663, 6), (key654, 6), (key659, 6), (key659, 6)]

theorem rawRowCheck19853 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form4 = rawRow19853 := by decide +kernel

def row19853 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

theorem rowCheck19853 : row19853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19853 := by decide +kernel

theorem rowEval19853 (x : Key → ℝ) : Integer.Sparse.eval row19853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19853, Integer.Sparse.eval_collectBalanced, rawRowCheck19853]

def rawRow19854 : Integer.Sparse Key := [(key23, 6), (key35, 6), (key23, 6), (key18, 6), (key460, 6), (key490, 6), (key460, 6), (key432, 6), (key486, 6), (key381, 6), (key486, 6), (key381, 6), (key432, 6), (key426, 6), (key375, 6), (key426, 6), (key663, 6), (key659, 6), (key654, 6), (key659, 6)]

theorem rawRowCheck19854 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form4 = rawRow19854 := by decide +kernel

def row19854 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

theorem rowCheck19854 : row19854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19854 := by decide +kernel

theorem rowEval19854 (x : Key → ℝ) : Integer.Sparse.eval row19854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19854, Integer.Sparse.eval_collectBalanced, rawRowCheck19854]

def rawRow19855 : Integer.Sparse Key := [(key35, 6), (key23, 6), (key23, 6), (key18, 6), (key490, 6), (key460, 6), (key460, 6), (key486, 6), (key432, 6), (key486, 6), (key381, 6), (key432, 6), (key381, 6), (key426, 6), (key426, 6), (key375, 6), (key663, 6), (key659, 6), (key659, 6), (key654, 6)]

theorem rawRowCheck19855 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form4 = rawRow19855 := by decide +kernel

def row19855 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

theorem rowCheck19855 : row19855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19855 := by decide +kernel

theorem rowEval19855 (x : Key → ℝ) : Integer.Sparse.eval row19855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19855, Integer.Sparse.eval_collectBalanced, rawRowCheck19855]

def rawRow19856 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key48, 6), (key74, 6), (key206, 6), (key212, 6), (key212, 6), (key426, 6), (key432, 6), (key426, 6), (key460, 6), (key432, 6), (key460, 6), (key659, 6), (key659, 6), (key663, 6), (key218, 6), (key486, 6), (key486, 6), (key490, 6)]

theorem rawRowCheck19856 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form4 = rawRow19856 := by decide +kernel

def row19856 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

theorem rowCheck19856 : row19856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19856 := by decide +kernel

theorem rowEval19856 (x : Key → ℝ) : Integer.Sparse.eval row19856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19856, Integer.Sparse.eval_collectBalanced, rawRowCheck19856]

def rawRow19857 : Integer.Sparse Key := [(key48, 6), (key43, 6), (key48, 6), (key74, 6), (key212, 6), (key206, 6), (key212, 6), (key432, 6), (key426, 6), (key460, 6), (key426, 6), (key460, 6), (key432, 6), (key659, 6), (key663, 6), (key659, 6), (key218, 6), (key486, 6), (key490, 6), (key486, 6)]

theorem rawRowCheck19857 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form4 = rawRow19857 := by decide +kernel

def row19857 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

theorem rowCheck19857 : row19857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19857 := by decide +kernel

theorem rowEval19857 (x : Key → ℝ) : Integer.Sparse.eval row19857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19857, Integer.Sparse.eval_collectBalanced, rawRowCheck19857]

def rawRow19858 : Integer.Sparse Key := [(key48, 6), (key48, 6), (key43, 6), (key74, 6), (key212, 6), (key212, 6), (key206, 6), (key460, 6), (key460, 6), (key432, 6), (key432, 6), (key426, 6), (key426, 6), (key663, 6), (key659, 6), (key659, 6), (key218, 6), (key490, 6), (key486, 6), (key486, 6)]

theorem rawRowCheck19858 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form4 = rawRow19858 := by decide +kernel

def row19858 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

theorem rowCheck19858 : row19858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19858 := by decide +kernel

theorem rowEval19858 (x : Key → ℝ) : Integer.Sparse.eval row19858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19858, Integer.Sparse.eval_collectBalanced, rawRowCheck19858]

def rawRow19859 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key48, 6), (key426, 6), (key432, 6), (key659, 6), (key206, 6), (key212, 6), (key426, 6), (key460, 6), (key659, 6), (key663, 6), (key212, 6), (key432, 6), (key460, 6), (key486, 6), (key218, 6), (key486, 6), (key490, 6)]

theorem rawRowCheck19859 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form4 = rawRow19859 := by decide +kernel

def row19859 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

theorem rowCheck19859 : row19859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19859 := by decide +kernel

theorem rowEval19859 (x : Key → ℝ) : Integer.Sparse.eval row19859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19859, Integer.Sparse.eval_collectBalanced, rawRowCheck19859]

def rawRow19860 : Integer.Sparse Key := [(key48, 6), (key43, 6), (key74, 6), (key48, 6), (key432, 6), (key426, 6), (key659, 6), (key212, 6), (key206, 6), (key460, 6), (key426, 6), (key663, 6), (key659, 6), (key212, 6), (key460, 6), (key432, 6), (key486, 6), (key218, 6), (key490, 6), (key486, 6)]

theorem rawRowCheck19860 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form4 = rawRow19860 := by decide +kernel

def row19860 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

theorem rowCheck19860 : row19860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19860 := by decide +kernel

theorem rowEval19860 (x : Key → ℝ) : Integer.Sparse.eval row19860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19860, Integer.Sparse.eval_collectBalanced, rawRowCheck19860]

def rawRow19861 : Integer.Sparse Key := [(key43, 6), (key74, 6), (key48, 6), (key48, 6), (key426, 6), (key659, 6), (key432, 6), (key426, 6), (key659, 6), (key206, 6), (key663, 6), (key212, 6), (key460, 6), (key432, 6), (key212, 6), (key460, 6), (key486, 6), (key486, 6), (key218, 6), (key490, 6)]

theorem rawRowCheck19861 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form4 = rawRow19861 := by decide +kernel

def row19861 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

theorem rowCheck19861 : row19861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19861 := by decide +kernel

theorem rowEval19861 (x : Key → ℝ) : Integer.Sparse.eval row19861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19861, Integer.Sparse.eval_collectBalanced, rawRowCheck19861]

def rawRow19862 : Integer.Sparse Key := [(key74, 6), (key43, 6), (key48, 6), (key48, 6), (key659, 6), (key426, 6), (key432, 6), (key659, 6), (key426, 6), (key663, 6), (key206, 6), (key460, 6), (key212, 6), (key432, 6), (key460, 6), (key212, 6), (key486, 6), (key486, 6), (key490, 6), (key218, 6)]

theorem rawRowCheck19862 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form4 = rawRow19862 := by decide +kernel

def row19862 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

theorem rowCheck19862 : row19862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19862 := by decide +kernel

theorem rowEval19862 (x : Key → ℝ) : Integer.Sparse.eval row19862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19862, Integer.Sparse.eval_collectBalanced, rawRowCheck19862]

def rawRow19863 : Integer.Sparse Key := [(key48, 6), (key74, 6), (key43, 6), (key48, 6), (key432, 6), (key659, 6), (key426, 6), (key460, 6), (key663, 6), (key212, 6), (key659, 6), (key206, 6), (key426, 6), (key460, 6), (key212, 6), (key432, 6), (key486, 6), (key490, 6), (key218, 6), (key486, 6)]

theorem rawRowCheck19863 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form4 = rawRow19863 := by decide +kernel

def row19863 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

theorem rowCheck19863 : row19863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19863 := by decide +kernel

theorem rowEval19863 (x : Key → ℝ) : Integer.Sparse.eval row19863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19863, Integer.Sparse.eval_collectBalanced, rawRowCheck19863]

def rawRow19864 : Integer.Sparse Key := [(key74, 6), (key48, 6), (key43, 6), (key48, 6), (key659, 6), (key432, 6), (key426, 6), (key663, 6), (key460, 6), (key659, 6), (key212, 6), (key426, 6), (key206, 6), (key460, 6), (key432, 6), (key212, 6), (key486, 6), (key490, 6), (key486, 6), (key218, 6)]

theorem rawRowCheck19864 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form4 = rawRow19864 := by decide +kernel

def row19864 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

theorem rowCheck19864 : row19864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19864 := by decide +kernel

theorem rowEval19864 (x : Key → ℝ) : Integer.Sparse.eval row19864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19864, Integer.Sparse.eval_collectBalanced, rawRowCheck19864]

def rawRow19865 : Integer.Sparse Key := [(key48, 6), (key48, 6), (key74, 6), (key43, 6), (key460, 6), (key460, 6), (key663, 6), (key212, 6), (key212, 6), (key432, 6), (key432, 6), (key659, 6), (key659, 6), (key206, 6), (key426, 6), (key426, 6), (key490, 6), (key218, 6), (key486, 6), (key486, 6)]

theorem rawRowCheck19865 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form4 = rawRow19865 := by decide +kernel

def row19865 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

theorem rowCheck19865 : row19865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19865 := by decide +kernel

theorem rowEval19865 (x : Key → ℝ) : Integer.Sparse.eval row19865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19865, Integer.Sparse.eval_collectBalanced, rawRowCheck19865]

def rawRow19866 : Integer.Sparse Key := [(key48, 6), (key74, 6), (key48, 6), (key43, 6), (key460, 6), (key663, 6), (key460, 6), (key432, 6), (key659, 6), (key212, 6), (key659, 6), (key212, 6), (key432, 6), (key426, 6), (key206, 6), (key426, 6), (key490, 6), (key486, 6), (key218, 6), (key486, 6)]

theorem rawRowCheck19866 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form4 = rawRow19866 := by decide +kernel

def row19866 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

theorem rowCheck19866 : row19866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19866 := by decide +kernel

theorem rowEval19866 (x : Key → ℝ) : Integer.Sparse.eval row19866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19866, Integer.Sparse.eval_collectBalanced, rawRowCheck19866]

def rawRow19867 : Integer.Sparse Key := [(key74, 6), (key48, 6), (key48, 6), (key43, 6), (key663, 6), (key460, 6), (key460, 6), (key659, 6), (key432, 6), (key659, 6), (key212, 6), (key432, 6), (key212, 6), (key426, 6), (key426, 6), (key206, 6), (key490, 6), (key486, 6), (key486, 6), (key218, 6)]

theorem rawRowCheck19867 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form4 = rawRow19867 := by decide +kernel

def row19867 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

theorem rowCheck19867 : row19867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19867 := by decide +kernel

theorem rowEval19867 (x : Key → ℝ) : Integer.Sparse.eval row19867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19867, Integer.Sparse.eval_collectBalanced, rawRowCheck19867]

def rawRow19868 : Integer.Sparse Key := [(key100, 6), (key105, 6), (key115, 6), (key137, 6), (key18, 6), (key23, 6), (key35, 6), (key375, 6), (key381, 6), (key426, 6), (key460, 6), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6), (key212, 6), (key381, 6), (key432, 6), (key460, 6)]

theorem rawRowCheck19868 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form4 = rawRow19868 := by decide +kernel

def row19868 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

theorem rowCheck19868 : row19868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19868 := by decide +kernel

theorem rowEval19868 (x : Key → ℝ) : Integer.Sparse.eval row19868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19868, Integer.Sparse.eval_collectBalanced, rawRowCheck19868]

def rawRow19869 : Integer.Sparse Key := [(key105, 6), (key100, 6), (key115, 6), (key137, 6), (key23, 6), (key18, 6), (key35, 6), (key381, 6), (key375, 6), (key460, 6), (key426, 6), (key490, 6), (key486, 6), (key654, 6), (key663, 6), (key659, 6), (key212, 6), (key381, 6), (key460, 6), (key432, 6)]

theorem rawRowCheck19869 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form4 = rawRow19869 := by decide +kernel

def row19869 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

theorem rowCheck19869 : row19869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19869 := by decide +kernel

theorem rowEval19869 (x : Key → ℝ) : Integer.Sparse.eval row19869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19869, Integer.Sparse.eval_collectBalanced, rawRowCheck19869]

def rawRow19870 : Integer.Sparse Key := [(key100, 6), (key115, 6), (key105, 6), (key137, 6), (key18, 6), (key35, 6), (key23, 6), (key426, 6), (key486, 6), (key375, 6), (key490, 6), (key381, 6), (key460, 6), (key659, 6), (key654, 6), (key663, 6), (key212, 6), (key432, 6), (key381, 6), (key460, 6)]

theorem rawRowCheck19870 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form4 = rawRow19870 := by decide +kernel

def row19870 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

theorem rowCheck19870 : row19870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19870 := by decide +kernel

theorem rowEval19870 (x : Key → ℝ) : Integer.Sparse.eval row19870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19870, Integer.Sparse.eval_collectBalanced, rawRowCheck19870]

def rawRow19871 : Integer.Sparse Key := [(key115, 6), (key100, 6), (key105, 6), (key137, 6), (key35, 6), (key18, 6), (key23, 6), (key486, 6), (key426, 6), (key490, 6), (key375, 6), (key460, 6), (key381, 6), (key659, 6), (key663, 6), (key654, 6), (key212, 6), (key432, 6), (key460, 6), (key381, 6)]

theorem rawRowCheck19871 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form4 = rawRow19871 := by decide +kernel

def row19871 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

theorem rowCheck19871 : row19871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19871 := by decide +kernel

theorem rowEval19871 (x : Key → ℝ) : Integer.Sparse.eval row19871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19871, Integer.Sparse.eval_collectBalanced, rawRowCheck19871]

def rawRow19872 : Integer.Sparse Key := [(key105, 6), (key115, 6), (key100, 6), (key137, 6), (key23, 6), (key35, 6), (key18, 6), (key460, 6), (key490, 6), (key381, 6), (key486, 6), (key375, 6), (key426, 6), (key663, 6), (key654, 6), (key659, 6), (key212, 6), (key460, 6), (key381, 6), (key432, 6)]

theorem rawRowCheck19872 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form4 = rawRow19872 := by decide +kernel

def row19872 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

theorem rowCheck19872 : row19872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19872 := by decide +kernel

theorem rowEval19872 (x : Key → ℝ) : Integer.Sparse.eval row19872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19872, Integer.Sparse.eval_collectBalanced, rawRowCheck19872]

def rawRow19873 : Integer.Sparse Key := [(key115, 6), (key105, 6), (key100, 6), (key137, 6), (key35, 6), (key23, 6), (key18, 6), (key490, 6), (key460, 6), (key486, 6), (key381, 6), (key426, 6), (key375, 6), (key663, 6), (key659, 6), (key654, 6), (key212, 6), (key460, 6), (key432, 6), (key381, 6)]

theorem rawRowCheck19873 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form4 = rawRow19873 := by decide +kernel

def row19873 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

theorem rowCheck19873 : row19873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19873 := by decide +kernel

theorem rowEval19873 (x : Key → ℝ) : Integer.Sparse.eval row19873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19873, Integer.Sparse.eval_collectBalanced, rawRowCheck19873]

def rawRow19874 : Integer.Sparse Key := [(key100, 6), (key105, 6), (key137, 6), (key115, 6), (key43, 6), (key48, 6), (key74, 6), (key206, 6), (key212, 6), (key426, 6), (key460, 6), (key659, 6), (key663, 6), (key218, 6), (key486, 6), (key490, 6), (key381, 6), (key212, 6), (key432, 6), (key460, 6)]

theorem rawRowCheck19874 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form4 = rawRow19874 := by decide +kernel

def row19874 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

theorem rowCheck19874 : row19874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19874 := by decide +kernel

theorem rowEval19874 (x : Key → ℝ) : Integer.Sparse.eval row19874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19874, Integer.Sparse.eval_collectBalanced, rawRowCheck19874]

def rawRow19875 : Integer.Sparse Key := [(key105, 6), (key100, 6), (key137, 6), (key115, 6), (key48, 6), (key43, 6), (key74, 6), (key212, 6), (key206, 6), (key460, 6), (key426, 6), (key663, 6), (key659, 6), (key218, 6), (key490, 6), (key486, 6), (key381, 6), (key212, 6), (key460, 6), (key432, 6)]

theorem rawRowCheck19875 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form4 = rawRow19875 := by decide +kernel

def row19875 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

theorem rowCheck19875 : row19875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19875 := by decide +kernel

theorem rowEval19875 (x : Key → ℝ) : Integer.Sparse.eval row19875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19875, Integer.Sparse.eval_collectBalanced, rawRowCheck19875]

def rawRow19876 : Integer.Sparse Key := [(key100, 6), (key137, 6), (key105, 6), (key115, 6), (key43, 6), (key74, 6), (key48, 6), (key426, 6), (key659, 6), (key206, 6), (key663, 6), (key212, 6), (key460, 6), (key486, 6), (key218, 6), (key490, 6), (key381, 6), (key432, 6), (key212, 6), (key460, 6)]

theorem rawRowCheck19876 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form4 = rawRow19876 := by decide +kernel

def row19876 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

theorem rowCheck19876 : row19876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19876 := by decide +kernel

theorem rowEval19876 (x : Key → ℝ) : Integer.Sparse.eval row19876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19876, Integer.Sparse.eval_collectBalanced, rawRowCheck19876]

def rawRow19877 : Integer.Sparse Key := [(key137, 6), (key100, 6), (key105, 6), (key115, 6), (key74, 6), (key43, 6), (key48, 6), (key659, 6), (key426, 6), (key663, 6), (key206, 6), (key460, 6), (key212, 6), (key486, 6), (key490, 6), (key218, 6), (key381, 6), (key432, 6), (key460, 6), (key212, 6)]

theorem rawRowCheck19877 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form4 = rawRow19877 := by decide +kernel

def row19877 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

theorem rowCheck19877 : row19877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19877 := by decide +kernel

theorem rowEval19877 (x : Key → ℝ) : Integer.Sparse.eval row19877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19877, Integer.Sparse.eval_collectBalanced, rawRowCheck19877]

def rawRow19878 : Integer.Sparse Key := [(key105, 6), (key137, 6), (key100, 6), (key115, 6), (key48, 6), (key74, 6), (key43, 6), (key460, 6), (key663, 6), (key212, 6), (key659, 6), (key206, 6), (key426, 6), (key490, 6), (key218, 6), (key486, 6), (key381, 6), (key460, 6), (key212, 6), (key432, 6)]

theorem rawRowCheck19878 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form4 = rawRow19878 := by decide +kernel

def row19878 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

theorem rowCheck19878 : row19878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19878 := by decide +kernel

theorem rowEval19878 (x : Key → ℝ) : Integer.Sparse.eval row19878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19878, Integer.Sparse.eval_collectBalanced, rawRowCheck19878]

def rawRow19879 : Integer.Sparse Key := [(key137, 6), (key105, 6), (key100, 6), (key115, 6), (key74, 6), (key48, 6), (key43, 6), (key663, 6), (key460, 6), (key659, 6), (key212, 6), (key426, 6), (key206, 6), (key490, 6), (key486, 6), (key218, 6), (key381, 6), (key460, 6), (key432, 6), (key212, 6)]

theorem rawRowCheck19879 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form4 = rawRow19879 := by decide +kernel

def row19879 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

theorem rowCheck19879 : row19879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19879 := by decide +kernel

theorem rowEval19879 (x : Key → ℝ) : Integer.Sparse.eval row19879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19879, Integer.Sparse.eval_collectBalanced, rawRowCheck19879]

def rawRow19880 : Integer.Sparse Key := [(key100, 6), (key115, 6), (key137, 6), (key105, 6), (key100, 6), (key115, 6), (key137, 6), (key18, 6), (key35, 6), (key375, 6), (key490, 6), (key654, 6), (key663, 6), (key212, 6), (key381, 6), (key460, 6), (key432, 6), (key212, 6), (key381, 6), (key460, 6)]

theorem rawRowCheck19880 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form4 = rawRow19880 := by decide +kernel

def row19880 : Integer.Sparse Key := [(key18, 6), (key35, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key212, 12), (key375, 6), (key381, 12), (key432, 6), (key460, 12), (key490, 6), (key654, 6), (key663, 6)]

theorem rowCheck19880 : row19880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19880 := by decide +kernel

theorem rowEval19880 (x : Key → ℝ) : Integer.Sparse.eval row19880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19880, Integer.Sparse.eval_collectBalanced, rawRowCheck19880]

def rawRow19881 : Integer.Sparse Key := [(key115, 6), (key100, 6), (key137, 6), (key105, 6), (key115, 6), (key100, 6), (key137, 6), (key35, 6), (key18, 6), (key490, 6), (key375, 6), (key663, 6), (key654, 6), (key212, 6), (key460, 6), (key381, 6), (key432, 6), (key212, 6), (key460, 6), (key381, 6)]

theorem rawRowCheck19881 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form4 = rawRow19881 := by decide +kernel

def row19881 : Integer.Sparse Key := [(key18, 6), (key35, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key212, 12), (key375, 6), (key381, 12), (key432, 6), (key460, 12), (key490, 6), (key654, 6), (key663, 6)]

theorem rowCheck19881 : row19881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19881 := by decide +kernel

theorem rowEval19881 (x : Key → ℝ) : Integer.Sparse.eval row19881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19881, Integer.Sparse.eval_collectBalanced, rawRowCheck19881]

def rawRow19882 : Integer.Sparse Key := [(key100, 6), (key137, 6), (key115, 6), (key105, 6), (key100, 6), (key137, 6), (key115, 6), (key43, 6), (key74, 6), (key206, 6), (key663, 6), (key218, 6), (key490, 6), (key381, 6), (key212, 6), (key460, 6), (key432, 6), (key381, 6), (key212, 6), (key460, 6)]

theorem rawRowCheck19882 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form4 = rawRow19882 := by decide +kernel

def row19882 : Integer.Sparse Key := [(key43, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key206, 6), (key212, 12), (key218, 6), (key381, 12), (key432, 6), (key460, 12), (key490, 6), (key663, 6)]

theorem rowCheck19882 : row19882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19882 := by decide +kernel

theorem rowEval19882 (x : Key → ℝ) : Integer.Sparse.eval row19882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19882, Integer.Sparse.eval_collectBalanced, rawRowCheck19882]

def rawRow19883 : Integer.Sparse Key := [(key137, 6), (key100, 6), (key115, 6), (key105, 6), (key137, 6), (key100, 6), (key115, 6), (key74, 6), (key43, 6), (key663, 6), (key206, 6), (key490, 6), (key218, 6), (key381, 6), (key460, 6), (key212, 6), (key432, 6), (key381, 6), (key460, 6), (key212, 6)]

theorem rawRowCheck19883 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form4 = rawRow19883 := by decide +kernel

def row19883 : Integer.Sparse Key := [(key43, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key206, 6), (key212, 12), (key218, 6), (key381, 12), (key432, 6), (key460, 12), (key490, 6), (key663, 6)]

theorem rowCheck19883 : row19883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19883 := by decide +kernel

theorem rowEval19883 (x : Key → ℝ) : Integer.Sparse.eval row19883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19883, Integer.Sparse.eval_collectBalanced, rawRowCheck19883]

def rawRow19884 : Integer.Sparse Key := [(key115, 6), (key137, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key100, 6), (key196, 6), (key200, 6), (key35, 6), (key74, 6), (key18, 6), (key375, 6), (key460, 6), (key212, 6), (key381, 6), (key432, 6), (key460, 6), (key212, 6), (key381, 6)]

theorem rawRowCheck19884 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form4 = rawRow19884 := by decide +kernel

def row19884 : Integer.Sparse Key := [(key18, 6), (key35, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key196, 6), (key200, 6), (key212, 12), (key375, 6), (key381, 12), (key432, 6), (key460, 12)]

theorem rowCheck19884 : row19884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19884 := by decide +kernel

theorem rowEval19884 (x : Key → ℝ) : Integer.Sparse.eval row19884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19884, Integer.Sparse.eval_collectBalanced, rawRowCheck19884]

def rawRow19885 : Integer.Sparse Key := [(key137, 6), (key115, 6), (key100, 6), (key105, 6), (key137, 6), (key115, 6), (key100, 6), (key200, 6), (key196, 6), (key74, 6), (key35, 6), (key43, 6), (key206, 6), (key460, 6), (key381, 6), (key212, 6), (key432, 6), (key460, 6), (key381, 6), (key212, 6)]

theorem rawRowCheck19885 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form4 = rawRow19885 := by decide +kernel

def row19885 : Integer.Sparse Key := [(key35, 6), (key43, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key196, 6), (key200, 6), (key206, 6), (key212, 12), (key381, 12), (key432, 6), (key460, 12)]

theorem rowCheck19885 : row19885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19885 := by decide +kernel

theorem rowEval19885 (x : Key → ℝ) : Integer.Sparse.eval row19885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19885, Integer.Sparse.eval_collectBalanced, rawRowCheck19885]

def rawRow19886 : Integer.Sparse Key := [(key105, 6), (key115, 6), (key137, 6), (key100, 6), (key195, 6), (key196, 6), (key200, 6), (key23, 6), (key35, 6), (key48, 6), (key115, 6), (key74, 6), (key137, 6), (key18, 6), (key375, 6), (key426, 6), (key460, 6), (key212, 6), (key381, 6), (key432, 6)]

theorem rawRowCheck19886 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form4 = rawRow19886 := by decide +kernel

def row19886 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key212, 6), (key375, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 6)]

theorem rowCheck19886 : row19886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19886 := by decide +kernel

theorem rowEval19886 (x : Key → ℝ) : Integer.Sparse.eval row19886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19886, Integer.Sparse.eval_collectBalanced, rawRowCheck19886]

def rawRow19887 : Integer.Sparse Key := [(key115, 6), (key105, 6), (key137, 6), (key100, 6), (key196, 6), (key195, 6), (key200, 6), (key35, 6), (key23, 6), (key115, 6), (key48, 6), (key137, 6), (key74, 6), (key18, 6), (key426, 6), (key375, 6), (key460, 6), (key212, 6), (key432, 6), (key381, 6)]

theorem rawRowCheck19887 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form4 = rawRow19887 := by decide +kernel

def row19887 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key212, 6), (key375, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 6)]

theorem rowCheck19887 : row19887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19887 := by decide +kernel

theorem rowEval19887 (x : Key → ℝ) : Integer.Sparse.eval row19887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19887, Integer.Sparse.eval_collectBalanced, rawRowCheck19887]

def rawRow19888 : Integer.Sparse Key := [(key105, 6), (key137, 6), (key115, 6), (key100, 6), (key195, 6), (key200, 6), (key196, 6), (key48, 6), (key74, 6), (key23, 6), (key137, 6), (key35, 6), (key115, 6), (key43, 6), (key206, 6), (key426, 6), (key460, 6), (key381, 6), (key212, 6), (key432, 6)]

theorem rawRowCheck19888 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form4 = rawRow19888 := by decide +kernel

def row19888 : Integer.Sparse Key := [(key23, 6), (key35, 6), (key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key206, 6), (key212, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 6)]

theorem rowCheck19888 : row19888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19888 := by decide +kernel

theorem rowEval19888 (x : Key → ℝ) : Integer.Sparse.eval row19888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19888, Integer.Sparse.eval_collectBalanced, rawRowCheck19888]

def rawRow19889 : Integer.Sparse Key := [(key137, 6), (key105, 6), (key115, 6), (key100, 6), (key200, 6), (key195, 6), (key196, 6), (key74, 6), (key48, 6), (key137, 6), (key23, 6), (key115, 6), (key35, 6), (key43, 6), (key426, 6), (key206, 6), (key460, 6), (key381, 6), (key432, 6), (key212, 6)]

theorem rawRowCheck19889 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form4 = rawRow19889 := by decide +kernel

def row19889 : Integer.Sparse Key := [(key23, 6), (key35, 6), (key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key206, 6), (key212, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 6)]

theorem rowCheck19889 : row19889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19889 := by decide +kernel

theorem rowEval19889 (x : Key → ℝ) : Integer.Sparse.eval row19889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19889, Integer.Sparse.eval_collectBalanced, rawRowCheck19889]

def rawRow19890 : Integer.Sparse Key := [(key115, 6), (key137, 6), (key105, 6), (key100, 6), (key196, 6), (key200, 6), (key195, 6), (key115, 6), (key137, 6), (key35, 6), (key74, 6), (key23, 6), (key48, 6), (key100, 6), (key18, 6), (key375, 6), (key460, 6), (key432, 6), (key212, 6), (key381, 6)]

theorem rawRowCheck19890 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form4 = rawRow19890 := by decide +kernel

def row19890 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key48, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key212, 6), (key375, 6), (key381, 6), (key432, 6), (key460, 6)]

theorem rowCheck19890 : row19890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19890 := by decide +kernel

theorem rowEval19890 (x : Key → ℝ) : Integer.Sparse.eval row19890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19890, Integer.Sparse.eval_collectBalanced, rawRowCheck19890]

def rawRow19891 : Integer.Sparse Key := [(key137, 6), (key115, 6), (key105, 6), (key100, 6), (key200, 6), (key196, 6), (key195, 6), (key137, 6), (key115, 6), (key74, 6), (key35, 6), (key48, 6), (key23, 6), (key100, 6), (key43, 6), (key206, 6), (key460, 6), (key432, 6), (key381, 6), (key212, 6)]

theorem rawRowCheck19891 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form4 = rawRow19891 := by decide +kernel

def row19891 : Integer.Sparse Key := [(key23, 6), (key35, 6), (key43, 6), (key48, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key206, 6), (key212, 6), (key381, 6), (key432, 6), (key460, 6)]

theorem rowCheck19891 : row19891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19891 := by decide +kernel

theorem rowEval19891 (x : Key → ℝ) : Integer.Sparse.eval row19891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19891, Integer.Sparse.eval_collectBalanced, rawRowCheck19891]

def rawRow19892 : Integer.Sparse Key := [(key195, 6), (key195, 6), (key196, 6), (key200, 6), (key23, 6), (key23, 6), (key35, 6), (key48, 6), (key48, 6), (key105, 6), (key105, 6), (key115, 6), (key115, 6), (key74, 6), (key137, 6), (key137, 6), (key18, 6), (key375, 6), (key426, 6), (key426, 6)]

theorem rawRowCheck19892 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form4 = rawRow19892 := by decide +kernel

def row19892 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6), (key426, 12)]

theorem rowCheck19892 : row19892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19892 := by decide +kernel

theorem rowEval19892 (x : Key → ℝ) : Integer.Sparse.eval row19892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19892, Integer.Sparse.eval_collectBalanced, rawRowCheck19892]

def rawRow19893 : Integer.Sparse Key := [(key195, 6), (key196, 6), (key195, 6), (key200, 6), (key23, 6), (key35, 6), (key23, 6), (key105, 6), (key115, 6), (key48, 6), (key115, 6), (key48, 6), (key105, 6), (key137, 6), (key74, 6), (key137, 6), (key18, 6), (key426, 6), (key375, 6), (key426, 6)]

theorem rawRowCheck19893 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form4 = rawRow19893 := by decide +kernel

def row19893 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6), (key426, 12)]

theorem rowCheck19893 : row19893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19893 := by decide +kernel

theorem rowEval19893 (x : Key → ℝ) : Integer.Sparse.eval row19893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19893, Integer.Sparse.eval_collectBalanced, rawRowCheck19893]

def rawRow19894 : Integer.Sparse Key := [(key196, 6), (key195, 6), (key195, 6), (key200, 6), (key35, 6), (key23, 6), (key23, 6), (key115, 6), (key105, 6), (key115, 6), (key48, 6), (key105, 6), (key48, 6), (key137, 6), (key137, 6), (key74, 6), (key18, 6), (key426, 6), (key426, 6), (key375, 6)]

theorem rawRowCheck19894 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form4 = rawRow19894 := by decide +kernel

def row19894 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6), (key426, 12)]

theorem rowCheck19894 : row19894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19894 := by decide +kernel

theorem rowEval19894 (x : Key → ℝ) : Integer.Sparse.eval row19894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19894, Integer.Sparse.eval_collectBalanced, rawRowCheck19894]

def rawRow19895 : Integer.Sparse Key := [(key195, 6), (key195, 6), (key200, 6), (key196, 6), (key48, 6), (key48, 6), (key74, 6), (key23, 6), (key23, 6), (key105, 6), (key105, 6), (key137, 6), (key137, 6), (key35, 6), (key115, 6), (key115, 6), (key43, 6), (key206, 6), (key426, 6), (key426, 6)]

theorem rawRowCheck19895 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form4 = rawRow19895 := by decide +kernel

def row19895 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6), (key426, 12)]

theorem rowCheck19895 : row19895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19895 := by decide +kernel

theorem rowEval19895 (x : Key → ℝ) : Integer.Sparse.eval row19895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19895, Integer.Sparse.eval_collectBalanced, rawRowCheck19895]

def rawRow19896 : Integer.Sparse Key := [(key195, 6), (key200, 6), (key195, 6), (key196, 6), (key48, 6), (key74, 6), (key48, 6), (key105, 6), (key137, 6), (key23, 6), (key137, 6), (key23, 6), (key105, 6), (key115, 6), (key35, 6), (key115, 6), (key43, 6), (key426, 6), (key206, 6), (key426, 6)]

theorem rawRowCheck19896 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form4 = rawRow19896 := by decide +kernel

def row19896 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6), (key426, 12)]

theorem rowCheck19896 : row19896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19896 := by decide +kernel

theorem rowEval19896 (x : Key → ℝ) : Integer.Sparse.eval row19896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19896, Integer.Sparse.eval_collectBalanced, rawRowCheck19896]

def rawRow19897 : Integer.Sparse Key := [(key200, 6), (key195, 6), (key195, 6), (key196, 6), (key74, 6), (key48, 6), (key48, 6), (key137, 6), (key105, 6), (key137, 6), (key23, 6), (key105, 6), (key23, 6), (key115, 6), (key115, 6), (key35, 6), (key43, 6), (key426, 6), (key426, 6), (key206, 6)]

theorem rawRowCheck19897 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form4 = rawRow19897 := by decide +kernel

def row19897 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6), (key426, 12)]

theorem rowCheck19897 : row19897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19897 := by decide +kernel

theorem rowEval19897 (x : Key → ℝ) : Integer.Sparse.eval row19897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19897, Integer.Sparse.eval_collectBalanced, rawRowCheck19897]

def rawRow19898 : Integer.Sparse Key := [(key195, 6), (key196, 6), (key200, 6), (key195, 6), (key105, 6), (key115, 6), (key137, 6), (key23, 6), (key35, 6), (key48, 6), (key115, 6), (key74, 6), (key137, 6), (key23, 6), (key48, 6), (key105, 6), (key100, 6), (key18, 6), (key375, 6), (key426, 6)]

theorem rawRowCheck19898 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form4 = rawRow19898 := by decide +kernel

def row19898 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key100, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6), (key426, 6)]

theorem rowCheck19898 : row19898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19898 := by decide +kernel

theorem rowEval19898 (x : Key → ℝ) : Integer.Sparse.eval row19898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19898, Integer.Sparse.eval_collectBalanced, rawRowCheck19898]

def rawRow19899 : Integer.Sparse Key := [(key196, 6), (key195, 6), (key200, 6), (key195, 6), (key115, 6), (key105, 6), (key137, 6), (key35, 6), (key23, 6), (key115, 6), (key48, 6), (key137, 6), (key74, 6), (key23, 6), (key105, 6), (key48, 6), (key100, 6), (key18, 6), (key426, 6), (key375, 6)]

theorem rawRowCheck19899 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form4 = rawRow19899 := by decide +kernel

def row19899 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key100, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6), (key426, 6)]

theorem rowCheck19899 : row19899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19899 := by decide +kernel

theorem rowEval19899 (x : Key → ℝ) : Integer.Sparse.eval row19899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19899, Integer.Sparse.eval_collectBalanced, rawRowCheck19899]

def rawRow19900 : Integer.Sparse Key := [(key195, 6), (key200, 6), (key196, 6), (key195, 6), (key105, 6), (key137, 6), (key115, 6), (key48, 6), (key74, 6), (key23, 6), (key137, 6), (key35, 6), (key115, 6), (key48, 6), (key23, 6), (key105, 6), (key100, 6), (key43, 6), (key206, 6), (key426, 6)]

theorem rawRowCheck19900 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form4 = rawRow19900 := by decide +kernel

def row19900 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key100, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6), (key426, 6)]

theorem rowCheck19900 : row19900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19900 := by decide +kernel

theorem rowEval19900 (x : Key → ℝ) : Integer.Sparse.eval row19900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19900, Integer.Sparse.eval_collectBalanced, rawRowCheck19900]

def rawRow19901 : Integer.Sparse Key := [(key200, 6), (key195, 6), (key196, 6), (key195, 6), (key137, 6), (key105, 6), (key115, 6), (key74, 6), (key48, 6), (key137, 6), (key23, 6), (key115, 6), (key35, 6), (key48, 6), (key105, 6), (key23, 6), (key100, 6), (key43, 6), (key426, 6), (key206, 6)]

theorem rawRowCheck19901 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form4 = rawRow19901 := by decide +kernel

def row19901 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key100, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6), (key426, 6)]

theorem rowCheck19901 : row19901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19901 := by decide +kernel

theorem rowEval19901 (x : Key → ℝ) : Integer.Sparse.eval row19901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19901, Integer.Sparse.eval_collectBalanced, rawRowCheck19901]

def rawRow19902 : Integer.Sparse Key := [(key196, 6), (key200, 6), (key195, 6), (key195, 6), (key115, 6), (key137, 6), (key105, 6), (key115, 6), (key137, 6), (key35, 6), (key74, 6), (key23, 6), (key48, 6), (key105, 6), (key23, 6), (key48, 6), (key100, 6), (key100, 6), (key18, 6), (key375, 6)]

theorem rawRowCheck19902 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form4 = rawRow19902 := by decide +kernel

def row19902 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key100, 12), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6)]

theorem rowCheck19902 : row19902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19902 := by decide +kernel

theorem rowEval19902 (x : Key → ℝ) : Integer.Sparse.eval row19902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19902, Integer.Sparse.eval_collectBalanced, rawRowCheck19902]

def rawRow19903 : Integer.Sparse Key := [(key200, 6), (key196, 6), (key195, 6), (key195, 6), (key137, 6), (key115, 6), (key105, 6), (key137, 6), (key115, 6), (key74, 6), (key35, 6), (key48, 6), (key23, 6), (key105, 6), (key48, 6), (key23, 6), (key100, 6), (key100, 6), (key43, 6), (key206, 6)]

theorem rawRowCheck19903 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form4 = rawRow19903 := by decide +kernel

def row19903 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key100, 12), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6)]

theorem rowCheck19903 : row19903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19903 := by decide +kernel

theorem rowEval19903 (x : Key → ℝ) : Integer.Sparse.eval row19903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19903, Integer.Sparse.eval_collectBalanced, rawRowCheck19903]

def rawRow19904 : Integer.Sparse Key := [(key1256, 4), (key1256, 4), (key1261, 4), (key1265, 4), (key1268, 4), (key1268, 4), (key1531, 4), (key1531, 4), (key1536, 4), (key1609, 4), (key1609, 4), (key1642, 4), (key1648, 4), (key1651, 4), (key1648, 4), (key1674, 4), (key1651, 4), (key1674, 4), (key1765, 4), (key1768, 4), (key1768, 4), (key1806, 4), (key1809, 4), (key1806, 4), (key1832, 4), (key1809, 4), (key1832, 4), (key1837, 4), (key1837, 4), (key1848, 4)]

theorem rawRowCheck19904 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form5 = rawRow19904 := by decide +kernel

def row19904 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19904 : row19904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19904 := by decide +kernel

theorem rowEval19904 (x : Key → ℝ) : Integer.Sparse.eval row19904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19904, Integer.Sparse.eval_collectBalanced, rawRowCheck19904]

def rawRow19905 : Integer.Sparse Key := [(key1256, 4), (key1261, 4), (key1256, 4), (key1268, 4), (key1265, 4), (key1268, 4), (key1531, 4), (key1536, 4), (key1531, 4), (key1609, 4), (key1642, 4), (key1609, 4), (key1651, 4), (key1648, 4), (key1674, 4), (key1648, 4), (key1674, 4), (key1651, 4), (key1768, 4), (key1765, 4), (key1768, 4), (key1809, 4), (key1806, 4), (key1832, 4), (key1806, 4), (key1832, 4), (key1809, 4), (key1837, 4), (key1848, 4), (key1837, 4)]

theorem rawRowCheck19905 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form5 = rawRow19905 := by decide +kernel

def row19905 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19905 : row19905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19905 := by decide +kernel

theorem rowEval19905 (x : Key → ℝ) : Integer.Sparse.eval row19905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19905, Integer.Sparse.eval_collectBalanced, rawRowCheck19905]

def rawRow19906 : Integer.Sparse Key := [(key1261, 4), (key1256, 4), (key1256, 4), (key1268, 4), (key1268, 4), (key1265, 4), (key1536, 4), (key1531, 4), (key1531, 4), (key1642, 4), (key1609, 4), (key1609, 4), (key1674, 4), (key1674, 4), (key1651, 4), (key1651, 4), (key1648, 4), (key1648, 4), (key1768, 4), (key1768, 4), (key1765, 4), (key1832, 4), (key1832, 4), (key1809, 4), (key1809, 4), (key1806, 4), (key1806, 4), (key1848, 4), (key1837, 4), (key1837, 4)]

theorem rawRowCheck19906 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form5 = rawRow19906 := by decide +kernel

def row19906 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19906 : row19906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19906 := by decide +kernel

theorem rowEval19906 (x : Key → ℝ) : Integer.Sparse.eval row19906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19906, Integer.Sparse.eval_collectBalanced, rawRowCheck19906]

def rawRow19907 : Integer.Sparse Key := [(key1256, 4), (key1265, 4), (key1268, 4), (key1256, 4), (key1261, 4), (key1268, 4), (key1609, 4), (key1648, 4), (key1651, 4), (key1531, 4), (key1648, 4), (key1674, 4), (key1531, 4), (key1536, 4), (key1609, 4), (key1642, 4), (key1651, 4), (key1674, 4), (key1806, 4), (key1809, 4), (key1837, 4), (key1765, 4), (key1768, 4), (key1806, 4), (key1832, 4), (key1837, 4), (key1848, 4), (key1768, 4), (key1809, 4), (key1832, 4)]

theorem rawRowCheck19907 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form5 = rawRow19907 := by decide +kernel

def row19907 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19907 : row19907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19907 := by decide +kernel

theorem rowEval19907 (x : Key → ℝ) : Integer.Sparse.eval row19907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19907, Integer.Sparse.eval_collectBalanced, rawRowCheck19907]

def rawRow19908 : Integer.Sparse Key := [(key1256, 4), (key1268, 4), (key1265, 4), (key1261, 4), (key1256, 4), (key1268, 4), (key1609, 4), (key1651, 4), (key1648, 4), (key1531, 4), (key1674, 4), (key1648, 4), (key1536, 4), (key1531, 4), (key1642, 4), (key1609, 4), (key1674, 4), (key1651, 4), (key1809, 4), (key1806, 4), (key1837, 4), (key1768, 4), (key1765, 4), (key1832, 4), (key1806, 4), (key1848, 4), (key1837, 4), (key1768, 4), (key1832, 4), (key1809, 4)]

theorem rawRowCheck19908 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form5 = rawRow19908 := by decide +kernel

def row19908 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19908 : row19908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19908 := by decide +kernel

theorem rowEval19908 (x : Key → ℝ) : Integer.Sparse.eval row19908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19908, Integer.Sparse.eval_collectBalanced, rawRowCheck19908]

def rawRow19909 : Integer.Sparse Key := [(key1265, 4), (key1256, 4), (key1268, 4), (key1256, 4), (key1268, 4), (key1261, 4), (key1648, 4), (key1609, 4), (key1651, 4), (key1648, 4), (key1531, 4), (key1674, 4), (key1609, 4), (key1651, 4), (key1531, 4), (key1674, 4), (key1536, 4), (key1642, 4), (key1806, 4), (key1837, 4), (key1809, 4), (key1806, 4), (key1837, 4), (key1765, 4), (key1848, 4), (key1768, 4), (key1832, 4), (key1809, 4), (key1768, 4), (key1832, 4)]

theorem rawRowCheck19909 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form5 = rawRow19909 := by decide +kernel

def row19909 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19909 : row19909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19909 := by decide +kernel

theorem rowEval19909 (x : Key → ℝ) : Integer.Sparse.eval row19909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19909, Integer.Sparse.eval_collectBalanced, rawRowCheck19909]

def rawRow19910 : Integer.Sparse Key := [(key1265, 4), (key1268, 4), (key1256, 4), (key1268, 4), (key1256, 4), (key1261, 4), (key1648, 4), (key1651, 4), (key1609, 4), (key1648, 4), (key1674, 4), (key1531, 4), (key1651, 4), (key1609, 4), (key1674, 4), (key1531, 4), (key1642, 4), (key1536, 4), (key1837, 4), (key1806, 4), (key1809, 4), (key1837, 4), (key1806, 4), (key1848, 4), (key1765, 4), (key1832, 4), (key1768, 4), (key1809, 4), (key1832, 4), (key1768, 4)]

theorem rawRowCheck19910 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form5 = rawRow19910 := by decide +kernel

def row19910 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19910 : row19910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19910 := by decide +kernel

theorem rowEval19910 (x : Key → ℝ) : Integer.Sparse.eval row19910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19910, Integer.Sparse.eval_collectBalanced, rawRowCheck19910]

def rawRow19911 : Integer.Sparse Key := [(key1268, 4), (key1256, 4), (key1265, 4), (key1261, 4), (key1268, 4), (key1256, 4), (key1651, 4), (key1609, 4), (key1648, 4), (key1674, 4), (key1531, 4), (key1648, 4), (key1642, 4), (key1674, 4), (key1536, 4), (key1651, 4), (key1531, 4), (key1609, 4), (key1809, 4), (key1837, 4), (key1806, 4), (key1832, 4), (key1848, 4), (key1768, 4), (key1837, 4), (key1765, 4), (key1806, 4), (key1832, 4), (key1768, 4), (key1809, 4)]

theorem rawRowCheck19911 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form5 = rawRow19911 := by decide +kernel

def row19911 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19911 : row19911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19911 := by decide +kernel

theorem rowEval19911 (x : Key → ℝ) : Integer.Sparse.eval row19911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19911, Integer.Sparse.eval_collectBalanced, rawRowCheck19911]

def rawRow19912 : Integer.Sparse Key := [(key1268, 4), (key1265, 4), (key1256, 4), (key1268, 4), (key1261, 4), (key1256, 4), (key1651, 4), (key1648, 4), (key1609, 4), (key1674, 4), (key1648, 4), (key1531, 4), (key1674, 4), (key1642, 4), (key1651, 4), (key1536, 4), (key1609, 4), (key1531, 4), (key1837, 4), (key1809, 4), (key1806, 4), (key1848, 4), (key1832, 4), (key1837, 4), (key1768, 4), (key1806, 4), (key1765, 4), (key1832, 4), (key1809, 4), (key1768, 4)]

theorem rawRowCheck19912 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form5 = rawRow19912 := by decide +kernel

def row19912 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19912 : row19912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19912 := by decide +kernel

theorem rowEval19912 (x : Key → ℝ) : Integer.Sparse.eval row19912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19912, Integer.Sparse.eval_collectBalanced, rawRowCheck19912]

def rawRow19913 : Integer.Sparse Key := [(key1261, 4), (key1268, 4), (key1268, 4), (key1256, 4), (key1256, 4), (key1265, 4), (key1642, 4), (key1674, 4), (key1674, 4), (key1536, 4), (key1651, 4), (key1651, 4), (key1531, 4), (key1531, 4), (key1609, 4), (key1609, 4), (key1648, 4), (key1648, 4), (key1832, 4), (key1832, 4), (key1848, 4), (key1768, 4), (key1768, 4), (key1809, 4), (key1809, 4), (key1837, 4), (key1837, 4), (key1765, 4), (key1806, 4), (key1806, 4)]

theorem rawRowCheck19913 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form5 = rawRow19913 := by decide +kernel

def row19913 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19913 : row19913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19913 := by decide +kernel

theorem rowEval19913 (x : Key → ℝ) : Integer.Sparse.eval row19913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19913, Integer.Sparse.eval_collectBalanced, rawRowCheck19913]

def rawRow19914 : Integer.Sparse Key := [(key1268, 4), (key1261, 4), (key1268, 4), (key1256, 4), (key1265, 4), (key1256, 4), (key1674, 4), (key1642, 4), (key1674, 4), (key1651, 4), (key1536, 4), (key1651, 4), (key1609, 4), (key1648, 4), (key1531, 4), (key1648, 4), (key1531, 4), (key1609, 4), (key1832, 4), (key1848, 4), (key1832, 4), (key1809, 4), (key1837, 4), (key1768, 4), (key1837, 4), (key1768, 4), (key1809, 4), (key1806, 4), (key1765, 4), (key1806, 4)]

theorem rawRowCheck19914 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form5 = rawRow19914 := by decide +kernel

def row19914 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19914 : row19914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19914 := by decide +kernel

theorem rowEval19914 (x : Key → ℝ) : Integer.Sparse.eval row19914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19914, Integer.Sparse.eval_collectBalanced, rawRowCheck19914]

def rawRow19915 : Integer.Sparse Key := [(key1268, 4), (key1268, 4), (key1261, 4), (key1265, 4), (key1256, 4), (key1256, 4), (key1674, 4), (key1674, 4), (key1642, 4), (key1651, 4), (key1651, 4), (key1536, 4), (key1648, 4), (key1609, 4), (key1648, 4), (key1531, 4), (key1609, 4), (key1531, 4), (key1848, 4), (key1832, 4), (key1832, 4), (key1837, 4), (key1809, 4), (key1837, 4), (key1768, 4), (key1809, 4), (key1768, 4), (key1806, 4), (key1806, 4), (key1765, 4)]

theorem rawRowCheck19915 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form5 = rawRow19915 := by decide +kernel

def row19915 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19915 : row19915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19915 := by decide +kernel

theorem rowEval19915 (x : Key → ℝ) : Integer.Sparse.eval row19915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19915, Integer.Sparse.eval_collectBalanced, rawRowCheck19915]

def rawRow19916 : Integer.Sparse Key := [(key1531, 4), (key1531, 4), (key1536, 4), (key1765, 4), (key1768, 4), (key1768, 4), (key1256, 4), (key1256, 4), (key1261, 4), (key1609, 4), (key1609, 4), (key1642, 4), (key1806, 4), (key1809, 4), (key1806, 4), (key1832, 4), (key1809, 4), (key1832, 4), (key1265, 4), (key1268, 4), (key1268, 4), (key1648, 4), (key1651, 4), (key1648, 4), (key1674, 4), (key1651, 4), (key1674, 4), (key1837, 4), (key1837, 4), (key1848, 4)]

theorem rawRowCheck19916 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form5 = rawRow19916 := by decide +kernel

def row19916 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19916 : row19916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19916 := by decide +kernel

theorem rowEval19916 (x : Key → ℝ) : Integer.Sparse.eval row19916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19916, Integer.Sparse.eval_collectBalanced, rawRowCheck19916]

def rawRow19917 : Integer.Sparse Key := [(key1531, 4), (key1536, 4), (key1531, 4), (key1768, 4), (key1765, 4), (key1768, 4), (key1256, 4), (key1261, 4), (key1256, 4), (key1609, 4), (key1642, 4), (key1609, 4), (key1809, 4), (key1806, 4), (key1832, 4), (key1806, 4), (key1832, 4), (key1809, 4), (key1268, 4), (key1265, 4), (key1268, 4), (key1651, 4), (key1648, 4), (key1674, 4), (key1648, 4), (key1674, 4), (key1651, 4), (key1837, 4), (key1848, 4), (key1837, 4)]

theorem rawRowCheck19917 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form5 = rawRow19917 := by decide +kernel

def row19917 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19917 : row19917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19917 := by decide +kernel

theorem rowEval19917 (x : Key → ℝ) : Integer.Sparse.eval row19917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19917, Integer.Sparse.eval_collectBalanced, rawRowCheck19917]

def rawRow19918 : Integer.Sparse Key := [(key1536, 4), (key1531, 4), (key1531, 4), (key1768, 4), (key1768, 4), (key1765, 4), (key1261, 4), (key1256, 4), (key1256, 4), (key1642, 4), (key1609, 4), (key1609, 4), (key1832, 4), (key1832, 4), (key1809, 4), (key1809, 4), (key1806, 4), (key1806, 4), (key1268, 4), (key1268, 4), (key1265, 4), (key1674, 4), (key1674, 4), (key1651, 4), (key1651, 4), (key1648, 4), (key1648, 4), (key1848, 4), (key1837, 4), (key1837, 4)]

theorem rawRowCheck19918 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form5 = rawRow19918 := by decide +kernel

def row19918 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19918 : row19918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19918 := by decide +kernel

theorem rowEval19918 (x : Key → ℝ) : Integer.Sparse.eval row19918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19918, Integer.Sparse.eval_collectBalanced, rawRowCheck19918]

def rawRow19919 : Integer.Sparse Key := [(key1531, 4), (key1765, 4), (key1768, 4), (key1531, 4), (key1536, 4), (key1768, 4), (key1609, 4), (key1806, 4), (key1809, 4), (key1256, 4), (key1806, 4), (key1832, 4), (key1256, 4), (key1261, 4), (key1609, 4), (key1642, 4), (key1809, 4), (key1832, 4), (key1648, 4), (key1651, 4), (key1837, 4), (key1265, 4), (key1268, 4), (key1648, 4), (key1674, 4), (key1837, 4), (key1848, 4), (key1268, 4), (key1651, 4), (key1674, 4)]

theorem rawRowCheck19919 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form5 = rawRow19919 := by decide +kernel

def row19919 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19919 : row19919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19919 := by decide +kernel

theorem rowEval19919 (x : Key → ℝ) : Integer.Sparse.eval row19919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19919, Integer.Sparse.eval_collectBalanced, rawRowCheck19919]

def rawRow19920 : Integer.Sparse Key := [(key1531, 4), (key1768, 4), (key1765, 4), (key1536, 4), (key1531, 4), (key1768, 4), (key1609, 4), (key1809, 4), (key1806, 4), (key1256, 4), (key1832, 4), (key1806, 4), (key1261, 4), (key1256, 4), (key1642, 4), (key1609, 4), (key1832, 4), (key1809, 4), (key1651, 4), (key1648, 4), (key1837, 4), (key1268, 4), (key1265, 4), (key1674, 4), (key1648, 4), (key1848, 4), (key1837, 4), (key1268, 4), (key1674, 4), (key1651, 4)]

theorem rawRowCheck19920 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form5 = rawRow19920 := by decide +kernel

def row19920 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19920 : row19920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19920 := by decide +kernel

theorem rowEval19920 (x : Key → ℝ) : Integer.Sparse.eval row19920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19920, Integer.Sparse.eval_collectBalanced, rawRowCheck19920]

def rawRow19921 : Integer.Sparse Key := [(key1765, 4), (key1531, 4), (key1768, 4), (key1531, 4), (key1768, 4), (key1536, 4), (key1806, 4), (key1609, 4), (key1809, 4), (key1806, 4), (key1256, 4), (key1832, 4), (key1609, 4), (key1809, 4), (key1256, 4), (key1832, 4), (key1261, 4), (key1642, 4), (key1648, 4), (key1837, 4), (key1651, 4), (key1648, 4), (key1837, 4), (key1265, 4), (key1848, 4), (key1268, 4), (key1674, 4), (key1651, 4), (key1268, 4), (key1674, 4)]

theorem rawRowCheck19921 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form5 = rawRow19921 := by decide +kernel

def row19921 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19921 : row19921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19921 := by decide +kernel

theorem rowEval19921 (x : Key → ℝ) : Integer.Sparse.eval row19921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19921, Integer.Sparse.eval_collectBalanced, rawRowCheck19921]

def rawRow19922 : Integer.Sparse Key := [(key1765, 4), (key1768, 4), (key1531, 4), (key1768, 4), (key1531, 4), (key1536, 4), (key1806, 4), (key1809, 4), (key1609, 4), (key1806, 4), (key1832, 4), (key1256, 4), (key1809, 4), (key1609, 4), (key1832, 4), (key1256, 4), (key1642, 4), (key1261, 4), (key1837, 4), (key1648, 4), (key1651, 4), (key1837, 4), (key1648, 4), (key1848, 4), (key1265, 4), (key1674, 4), (key1268, 4), (key1651, 4), (key1674, 4), (key1268, 4)]

theorem rawRowCheck19922 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form5 = rawRow19922 := by decide +kernel

def row19922 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19922 : row19922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19922 := by decide +kernel

theorem rowEval19922 (x : Key → ℝ) : Integer.Sparse.eval row19922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19922, Integer.Sparse.eval_collectBalanced, rawRowCheck19922]

def rawRow19923 : Integer.Sparse Key := [(key1768, 4), (key1531, 4), (key1765, 4), (key1536, 4), (key1768, 4), (key1531, 4), (key1809, 4), (key1609, 4), (key1806, 4), (key1832, 4), (key1256, 4), (key1806, 4), (key1642, 4), (key1832, 4), (key1261, 4), (key1809, 4), (key1256, 4), (key1609, 4), (key1651, 4), (key1837, 4), (key1648, 4), (key1674, 4), (key1848, 4), (key1268, 4), (key1837, 4), (key1265, 4), (key1648, 4), (key1674, 4), (key1268, 4), (key1651, 4)]

theorem rawRowCheck19923 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form5 = rawRow19923 := by decide +kernel

def row19923 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19923 : row19923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19923 := by decide +kernel

theorem rowEval19923 (x : Key → ℝ) : Integer.Sparse.eval row19923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19923, Integer.Sparse.eval_collectBalanced, rawRowCheck19923]

def rawRow19924 : Integer.Sparse Key := [(key1768, 4), (key1765, 4), (key1531, 4), (key1768, 4), (key1536, 4), (key1531, 4), (key1809, 4), (key1806, 4), (key1609, 4), (key1832, 4), (key1806, 4), (key1256, 4), (key1832, 4), (key1642, 4), (key1809, 4), (key1261, 4), (key1609, 4), (key1256, 4), (key1837, 4), (key1651, 4), (key1648, 4), (key1848, 4), (key1674, 4), (key1837, 4), (key1268, 4), (key1648, 4), (key1265, 4), (key1674, 4), (key1651, 4), (key1268, 4)]

theorem rawRowCheck19924 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form5 = rawRow19924 := by decide +kernel

def row19924 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19924 : row19924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19924 := by decide +kernel

theorem rowEval19924 (x : Key → ℝ) : Integer.Sparse.eval row19924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19924, Integer.Sparse.eval_collectBalanced, rawRowCheck19924]

def rawRow19925 : Integer.Sparse Key := [(key1536, 4), (key1768, 4), (key1768, 4), (key1531, 4), (key1531, 4), (key1765, 4), (key1642, 4), (key1832, 4), (key1832, 4), (key1261, 4), (key1809, 4), (key1809, 4), (key1256, 4), (key1256, 4), (key1609, 4), (key1609, 4), (key1806, 4), (key1806, 4), (key1674, 4), (key1674, 4), (key1848, 4), (key1268, 4), (key1268, 4), (key1651, 4), (key1651, 4), (key1837, 4), (key1837, 4), (key1265, 4), (key1648, 4), (key1648, 4)]

theorem rawRowCheck19925 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form5 = rawRow19925 := by decide +kernel

def row19925 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19925 : row19925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19925 := by decide +kernel

theorem rowEval19925 (x : Key → ℝ) : Integer.Sparse.eval row19925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19925, Integer.Sparse.eval_collectBalanced, rawRowCheck19925]

def rawRow19926 : Integer.Sparse Key := [(key1768, 4), (key1536, 4), (key1768, 4), (key1531, 4), (key1765, 4), (key1531, 4), (key1832, 4), (key1642, 4), (key1832, 4), (key1809, 4), (key1261, 4), (key1809, 4), (key1609, 4), (key1806, 4), (key1256, 4), (key1806, 4), (key1256, 4), (key1609, 4), (key1674, 4), (key1848, 4), (key1674, 4), (key1651, 4), (key1837, 4), (key1268, 4), (key1837, 4), (key1268, 4), (key1651, 4), (key1648, 4), (key1265, 4), (key1648, 4)]

theorem rawRowCheck19926 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form5 = rawRow19926 := by decide +kernel

def row19926 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19926 : row19926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19926 := by decide +kernel

theorem rowEval19926 (x : Key → ℝ) : Integer.Sparse.eval row19926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19926, Integer.Sparse.eval_collectBalanced, rawRowCheck19926]

def rawRow19927 : Integer.Sparse Key := [(key1768, 4), (key1768, 4), (key1536, 4), (key1765, 4), (key1531, 4), (key1531, 4), (key1832, 4), (key1832, 4), (key1642, 4), (key1809, 4), (key1809, 4), (key1261, 4), (key1806, 4), (key1609, 4), (key1806, 4), (key1256, 4), (key1609, 4), (key1256, 4), (key1848, 4), (key1674, 4), (key1674, 4), (key1837, 4), (key1651, 4), (key1837, 4), (key1268, 4), (key1651, 4), (key1268, 4), (key1648, 4), (key1648, 4), (key1265, 4)]

theorem rawRowCheck19927 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form5 = rawRow19927 := by decide +kernel

def row19927 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19927 : row19927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19927 := by decide +kernel

theorem rowEval19927 (x : Key → ℝ) : Integer.Sparse.eval row19927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19927, Integer.Sparse.eval_collectBalanced, rawRowCheck19927]

def rawRow19928 : Integer.Sparse Key := [(key1609, 4), (key1648, 4), (key1651, 4), (key1806, 4), (key1809, 4), (key1837, 4), (key1256, 4), (key1265, 4), (key1268, 4), (key1531, 4), (key1648, 4), (key1674, 4), (key1765, 4), (key1768, 4), (key1806, 4), (key1832, 4), (key1837, 4), (key1848, 4), (key1256, 4), (key1261, 4), (key1268, 4), (key1531, 4), (key1536, 4), (key1609, 4), (key1642, 4), (key1651, 4), (key1674, 4), (key1768, 4), (key1809, 4), (key1832, 4)]

theorem rawRowCheck19928 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form5 = rawRow19928 := by decide +kernel

def row19928 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19928 : row19928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19928 := by decide +kernel

theorem rowEval19928 (x : Key → ℝ) : Integer.Sparse.eval row19928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19928, Integer.Sparse.eval_collectBalanced, rawRowCheck19928]

def rawRow19929 : Integer.Sparse Key := [(key1609, 4), (key1651, 4), (key1648, 4), (key1809, 4), (key1806, 4), (key1837, 4), (key1256, 4), (key1268, 4), (key1265, 4), (key1531, 4), (key1674, 4), (key1648, 4), (key1768, 4), (key1765, 4), (key1832, 4), (key1806, 4), (key1848, 4), (key1837, 4), (key1261, 4), (key1256, 4), (key1268, 4), (key1536, 4), (key1531, 4), (key1642, 4), (key1609, 4), (key1674, 4), (key1651, 4), (key1768, 4), (key1832, 4), (key1809, 4)]

theorem rawRowCheck19929 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form5 = rawRow19929 := by decide +kernel

def row19929 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19929 : row19929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19929 := by decide +kernel

theorem rowEval19929 (x : Key → ℝ) : Integer.Sparse.eval row19929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19929, Integer.Sparse.eval_collectBalanced, rawRowCheck19929]

def rawRow19930 : Integer.Sparse Key := [(key1648, 4), (key1609, 4), (key1651, 4), (key1806, 4), (key1837, 4), (key1809, 4), (key1265, 4), (key1256, 4), (key1268, 4), (key1648, 4), (key1531, 4), (key1674, 4), (key1806, 4), (key1837, 4), (key1765, 4), (key1848, 4), (key1768, 4), (key1832, 4), (key1256, 4), (key1268, 4), (key1261, 4), (key1609, 4), (key1651, 4), (key1531, 4), (key1674, 4), (key1536, 4), (key1642, 4), (key1809, 4), (key1768, 4), (key1832, 4)]

theorem rawRowCheck19930 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form5 = rawRow19930 := by decide +kernel

def row19930 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19930 : row19930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19930 := by decide +kernel

theorem rowEval19930 (x : Key → ℝ) : Integer.Sparse.eval row19930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19930, Integer.Sparse.eval_collectBalanced, rawRowCheck19930]

def rawRow19931 : Integer.Sparse Key := [(key1648, 4), (key1651, 4), (key1609, 4), (key1837, 4), (key1806, 4), (key1809, 4), (key1265, 4), (key1268, 4), (key1256, 4), (key1648, 4), (key1674, 4), (key1531, 4), (key1837, 4), (key1806, 4), (key1848, 4), (key1765, 4), (key1832, 4), (key1768, 4), (key1268, 4), (key1256, 4), (key1261, 4), (key1651, 4), (key1609, 4), (key1674, 4), (key1531, 4), (key1642, 4), (key1536, 4), (key1809, 4), (key1832, 4), (key1768, 4)]

theorem rawRowCheck19931 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form5 = rawRow19931 := by decide +kernel

def row19931 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19931 : row19931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19931 := by decide +kernel

theorem rowEval19931 (x : Key → ℝ) : Integer.Sparse.eval row19931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19931, Integer.Sparse.eval_collectBalanced, rawRowCheck19931]

def rawRow19932 : Integer.Sparse Key := [(key1651, 4), (key1609, 4), (key1648, 4), (key1809, 4), (key1837, 4), (key1806, 4), (key1268, 4), (key1256, 4), (key1265, 4), (key1674, 4), (key1531, 4), (key1648, 4), (key1832, 4), (key1848, 4), (key1768, 4), (key1837, 4), (key1765, 4), (key1806, 4), (key1261, 4), (key1268, 4), (key1256, 4), (key1642, 4), (key1674, 4), (key1536, 4), (key1651, 4), (key1531, 4), (key1609, 4), (key1832, 4), (key1768, 4), (key1809, 4)]

theorem rawRowCheck19932 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form5 = rawRow19932 := by decide +kernel

def row19932 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19932 : row19932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19932 := by decide +kernel

theorem rowEval19932 (x : Key → ℝ) : Integer.Sparse.eval row19932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19932, Integer.Sparse.eval_collectBalanced, rawRowCheck19932]

def rawRow19933 : Integer.Sparse Key := [(key1651, 4), (key1648, 4), (key1609, 4), (key1837, 4), (key1809, 4), (key1806, 4), (key1268, 4), (key1265, 4), (key1256, 4), (key1674, 4), (key1648, 4), (key1531, 4), (key1848, 4), (key1832, 4), (key1837, 4), (key1768, 4), (key1806, 4), (key1765, 4), (key1268, 4), (key1261, 4), (key1256, 4), (key1674, 4), (key1642, 4), (key1651, 4), (key1536, 4), (key1609, 4), (key1531, 4), (key1832, 4), (key1809, 4), (key1768, 4)]

theorem rawRowCheck19933 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form5 = rawRow19933 := by decide +kernel

def row19933 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19933 : row19933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19933 := by decide +kernel

theorem rowEval19933 (x : Key → ℝ) : Integer.Sparse.eval row19933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19933, Integer.Sparse.eval_collectBalanced, rawRowCheck19933]

def rawRow19934 : Integer.Sparse Key := [(key1609, 4), (key1806, 4), (key1809, 4), (key1648, 4), (key1651, 4), (key1837, 4), (key1531, 4), (key1765, 4), (key1768, 4), (key1256, 4), (key1806, 4), (key1832, 4), (key1265, 4), (key1268, 4), (key1648, 4), (key1674, 4), (key1837, 4), (key1848, 4), (key1531, 4), (key1536, 4), (key1768, 4), (key1256, 4), (key1261, 4), (key1609, 4), (key1642, 4), (key1809, 4), (key1832, 4), (key1268, 4), (key1651, 4), (key1674, 4)]

theorem rawRowCheck19934 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form5 = rawRow19934 := by decide +kernel

def row19934 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19934 : row19934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19934 := by decide +kernel

theorem rowEval19934 (x : Key → ℝ) : Integer.Sparse.eval row19934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19934, Integer.Sparse.eval_collectBalanced, rawRowCheck19934]

def rawRow19935 : Integer.Sparse Key := [(key1609, 4), (key1809, 4), (key1806, 4), (key1651, 4), (key1648, 4), (key1837, 4), (key1531, 4), (key1768, 4), (key1765, 4), (key1256, 4), (key1832, 4), (key1806, 4), (key1268, 4), (key1265, 4), (key1674, 4), (key1648, 4), (key1848, 4), (key1837, 4), (key1536, 4), (key1531, 4), (key1768, 4), (key1261, 4), (key1256, 4), (key1642, 4), (key1609, 4), (key1832, 4), (key1809, 4), (key1268, 4), (key1674, 4), (key1651, 4)]

theorem rawRowCheck19935 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form5 = rawRow19935 := by decide +kernel

def row19935 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19935 : row19935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19935 := by decide +kernel

theorem rowEval19935 (x : Key → ℝ) : Integer.Sparse.eval row19935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19935, Integer.Sparse.eval_collectBalanced, rawRowCheck19935]

def rawRow19936 : Integer.Sparse Key := [(key1806, 4), (key1609, 4), (key1809, 4), (key1648, 4), (key1837, 4), (key1651, 4), (key1765, 4), (key1531, 4), (key1768, 4), (key1806, 4), (key1256, 4), (key1832, 4), (key1648, 4), (key1837, 4), (key1265, 4), (key1848, 4), (key1268, 4), (key1674, 4), (key1531, 4), (key1768, 4), (key1536, 4), (key1609, 4), (key1809, 4), (key1256, 4), (key1832, 4), (key1261, 4), (key1642, 4), (key1651, 4), (key1268, 4), (key1674, 4)]

theorem rawRowCheck19936 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form5 = rawRow19936 := by decide +kernel

def row19936 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19936 : row19936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19936 := by decide +kernel

theorem rowEval19936 (x : Key → ℝ) : Integer.Sparse.eval row19936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19936, Integer.Sparse.eval_collectBalanced, rawRowCheck19936]

def rawRow19937 : Integer.Sparse Key := [(key1806, 4), (key1809, 4), (key1609, 4), (key1837, 4), (key1648, 4), (key1651, 4), (key1765, 4), (key1768, 4), (key1531, 4), (key1806, 4), (key1832, 4), (key1256, 4), (key1837, 4), (key1648, 4), (key1848, 4), (key1265, 4), (key1674, 4), (key1268, 4), (key1768, 4), (key1531, 4), (key1536, 4), (key1809, 4), (key1609, 4), (key1832, 4), (key1256, 4), (key1642, 4), (key1261, 4), (key1651, 4), (key1674, 4), (key1268, 4)]

theorem rawRowCheck19937 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form5 = rawRow19937 := by decide +kernel

def row19937 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19937 : row19937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19937 := by decide +kernel

theorem rowEval19937 (x : Key → ℝ) : Integer.Sparse.eval row19937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19937, Integer.Sparse.eval_collectBalanced, rawRowCheck19937]

def rawRow19938 : Integer.Sparse Key := [(key1809, 4), (key1609, 4), (key1806, 4), (key1651, 4), (key1837, 4), (key1648, 4), (key1768, 4), (key1531, 4), (key1765, 4), (key1832, 4), (key1256, 4), (key1806, 4), (key1674, 4), (key1848, 4), (key1268, 4), (key1837, 4), (key1265, 4), (key1648, 4), (key1536, 4), (key1768, 4), (key1531, 4), (key1642, 4), (key1832, 4), (key1261, 4), (key1809, 4), (key1256, 4), (key1609, 4), (key1674, 4), (key1268, 4), (key1651, 4)]

theorem rawRowCheck19938 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form5 = rawRow19938 := by decide +kernel

def row19938 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19938 : row19938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19938 := by decide +kernel

theorem rowEval19938 (x : Key → ℝ) : Integer.Sparse.eval row19938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19938, Integer.Sparse.eval_collectBalanced, rawRowCheck19938]

def rawRow19939 : Integer.Sparse Key := [(key1809, 4), (key1806, 4), (key1609, 4), (key1837, 4), (key1651, 4), (key1648, 4), (key1768, 4), (key1765, 4), (key1531, 4), (key1832, 4), (key1806, 4), (key1256, 4), (key1848, 4), (key1674, 4), (key1837, 4), (key1268, 4), (key1648, 4), (key1265, 4), (key1768, 4), (key1536, 4), (key1531, 4), (key1832, 4), (key1642, 4), (key1809, 4), (key1261, 4), (key1609, 4), (key1256, 4), (key1674, 4), (key1651, 4), (key1268, 4)]

theorem rawRowCheck19939 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form5 = rawRow19939 := by decide +kernel

def row19939 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19939 : row19939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19939 := by decide +kernel

theorem rowEval19939 (x : Key → ℝ) : Integer.Sparse.eval row19939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19939, Integer.Sparse.eval_collectBalanced, rawRowCheck19939]

def rawRow19940 : Integer.Sparse Key := [(key1648, 4), (key1806, 4), (key1837, 4), (key1609, 4), (key1651, 4), (key1809, 4), (key1648, 4), (key1806, 4), (key1837, 4), (key1265, 4), (key1765, 4), (key1848, 4), (key1256, 4), (key1268, 4), (key1531, 4), (key1674, 4), (key1768, 4), (key1832, 4), (key1609, 4), (key1651, 4), (key1809, 4), (key1256, 4), (key1268, 4), (key1531, 4), (key1674, 4), (key1768, 4), (key1832, 4), (key1261, 4), (key1536, 4), (key1642, 4)]

theorem rawRowCheck19940 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form5 = rawRow19940 := by decide +kernel

def row19940 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19940 : row19940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19940 := by decide +kernel

theorem rowEval19940 (x : Key → ℝ) : Integer.Sparse.eval row19940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19940, Integer.Sparse.eval_collectBalanced, rawRowCheck19940]

def rawRow19941 : Integer.Sparse Key := [(key1648, 4), (key1837, 4), (key1806, 4), (key1651, 4), (key1609, 4), (key1809, 4), (key1648, 4), (key1837, 4), (key1806, 4), (key1265, 4), (key1848, 4), (key1765, 4), (key1268, 4), (key1256, 4), (key1674, 4), (key1531, 4), (key1832, 4), (key1768, 4), (key1651, 4), (key1609, 4), (key1809, 4), (key1268, 4), (key1256, 4), (key1674, 4), (key1531, 4), (key1832, 4), (key1768, 4), (key1261, 4), (key1642, 4), (key1536, 4)]

theorem rawRowCheck19941 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form5 = rawRow19941 := by decide +kernel

def row19941 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19941 : row19941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19941 := by decide +kernel

theorem rowEval19941 (x : Key → ℝ) : Integer.Sparse.eval row19941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19941, Integer.Sparse.eval_collectBalanced, rawRowCheck19941]

def rawRow19942 : Integer.Sparse Key := [(key1806, 4), (key1648, 4), (key1837, 4), (key1609, 4), (key1809, 4), (key1651, 4), (key1806, 4), (key1648, 4), (key1837, 4), (key1765, 4), (key1265, 4), (key1848, 4), (key1531, 4), (key1768, 4), (key1256, 4), (key1832, 4), (key1268, 4), (key1674, 4), (key1609, 4), (key1809, 4), (key1651, 4), (key1531, 4), (key1768, 4), (key1256, 4), (key1832, 4), (key1268, 4), (key1674, 4), (key1536, 4), (key1261, 4), (key1642, 4)]

theorem rawRowCheck19942 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form5 = rawRow19942 := by decide +kernel

def row19942 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19942 : row19942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19942 := by decide +kernel

theorem rowEval19942 (x : Key → ℝ) : Integer.Sparse.eval row19942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19942, Integer.Sparse.eval_collectBalanced, rawRowCheck19942]

def rawRow19943 : Integer.Sparse Key := [(key1806, 4), (key1837, 4), (key1648, 4), (key1809, 4), (key1609, 4), (key1651, 4), (key1806, 4), (key1837, 4), (key1648, 4), (key1765, 4), (key1848, 4), (key1265, 4), (key1768, 4), (key1531, 4), (key1832, 4), (key1256, 4), (key1674, 4), (key1268, 4), (key1809, 4), (key1609, 4), (key1651, 4), (key1768, 4), (key1531, 4), (key1832, 4), (key1256, 4), (key1674, 4), (key1268, 4), (key1536, 4), (key1642, 4), (key1261, 4)]

theorem rawRowCheck19943 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form5 = rawRow19943 := by decide +kernel

def row19943 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19943 : row19943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19943 := by decide +kernel

theorem rowEval19943 (x : Key → ℝ) : Integer.Sparse.eval row19943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19943, Integer.Sparse.eval_collectBalanced, rawRowCheck19943]

def rawRow19944 : Integer.Sparse Key := [(key1837, 4), (key1648, 4), (key1806, 4), (key1651, 4), (key1809, 4), (key1609, 4), (key1837, 4), (key1648, 4), (key1806, 4), (key1848, 4), (key1265, 4), (key1765, 4), (key1674, 4), (key1832, 4), (key1268, 4), (key1768, 4), (key1256, 4), (key1531, 4), (key1651, 4), (key1809, 4), (key1609, 4), (key1674, 4), (key1832, 4), (key1268, 4), (key1768, 4), (key1256, 4), (key1531, 4), (key1642, 4), (key1261, 4), (key1536, 4)]

theorem rawRowCheck19944 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form5 = rawRow19944 := by decide +kernel

def row19944 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19944 : row19944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19944 := by decide +kernel

theorem rowEval19944 (x : Key → ℝ) : Integer.Sparse.eval row19944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19944, Integer.Sparse.eval_collectBalanced, rawRowCheck19944]

def rawRow19945 : Integer.Sparse Key := [(key1837, 4), (key1806, 4), (key1648, 4), (key1809, 4), (key1651, 4), (key1609, 4), (key1837, 4), (key1806, 4), (key1648, 4), (key1848, 4), (key1765, 4), (key1265, 4), (key1832, 4), (key1674, 4), (key1768, 4), (key1268, 4), (key1531, 4), (key1256, 4), (key1809, 4), (key1651, 4), (key1609, 4), (key1832, 4), (key1674, 4), (key1768, 4), (key1268, 4), (key1531, 4), (key1256, 4), (key1642, 4), (key1536, 4), (key1261, 4)]

theorem rawRowCheck19945 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form5 = rawRow19945 := by decide +kernel

def row19945 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19945 : row19945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19945 := by decide +kernel

theorem rowEval19945 (x : Key → ℝ) : Integer.Sparse.eval row19945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19945, Integer.Sparse.eval_collectBalanced, rawRowCheck19945]

def rawRow19946 : Integer.Sparse Key := [(key1651, 4), (key1809, 4), (key1837, 4), (key1609, 4), (key1648, 4), (key1806, 4), (key1674, 4), (key1832, 4), (key1848, 4), (key1268, 4), (key1768, 4), (key1837, 4), (key1256, 4), (key1265, 4), (key1531, 4), (key1648, 4), (key1765, 4), (key1806, 4), (key1642, 4), (key1674, 4), (key1832, 4), (key1261, 4), (key1268, 4), (key1536, 4), (key1651, 4), (key1768, 4), (key1809, 4), (key1256, 4), (key1531, 4), (key1609, 4)]

theorem rawRowCheck19946 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form5 = rawRow19946 := by decide +kernel

def row19946 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19946 : row19946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19946 := by decide +kernel

theorem rowEval19946 (x : Key → ℝ) : Integer.Sparse.eval row19946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19946, Integer.Sparse.eval_collectBalanced, rawRowCheck19946]

def rawRow19947 : Integer.Sparse Key := [(key1651, 4), (key1837, 4), (key1809, 4), (key1648, 4), (key1609, 4), (key1806, 4), (key1674, 4), (key1848, 4), (key1832, 4), (key1268, 4), (key1837, 4), (key1768, 4), (key1265, 4), (key1256, 4), (key1648, 4), (key1531, 4), (key1806, 4), (key1765, 4), (key1674, 4), (key1642, 4), (key1832, 4), (key1268, 4), (key1261, 4), (key1651, 4), (key1536, 4), (key1809, 4), (key1768, 4), (key1256, 4), (key1609, 4), (key1531, 4)]

theorem rawRowCheck19947 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form5 = rawRow19947 := by decide +kernel

def row19947 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19947 : row19947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19947 := by decide +kernel

theorem rowEval19947 (x : Key → ℝ) : Integer.Sparse.eval row19947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19947, Integer.Sparse.eval_collectBalanced, rawRowCheck19947]

def rawRow19948 : Integer.Sparse Key := [(key1809, 4), (key1651, 4), (key1837, 4), (key1609, 4), (key1806, 4), (key1648, 4), (key1832, 4), (key1674, 4), (key1848, 4), (key1768, 4), (key1268, 4), (key1837, 4), (key1531, 4), (key1765, 4), (key1256, 4), (key1806, 4), (key1265, 4), (key1648, 4), (key1642, 4), (key1832, 4), (key1674, 4), (key1536, 4), (key1768, 4), (key1261, 4), (key1809, 4), (key1268, 4), (key1651, 4), (key1531, 4), (key1256, 4), (key1609, 4)]

theorem rawRowCheck19948 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form5 = rawRow19948 := by decide +kernel

def row19948 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19948 : row19948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19948 := by decide +kernel

theorem rowEval19948 (x : Key → ℝ) : Integer.Sparse.eval row19948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19948, Integer.Sparse.eval_collectBalanced, rawRowCheck19948]

def rawRow19949 : Integer.Sparse Key := [(key1809, 4), (key1837, 4), (key1651, 4), (key1806, 4), (key1609, 4), (key1648, 4), (key1832, 4), (key1848, 4), (key1674, 4), (key1768, 4), (key1837, 4), (key1268, 4), (key1765, 4), (key1531, 4), (key1806, 4), (key1256, 4), (key1648, 4), (key1265, 4), (key1832, 4), (key1642, 4), (key1674, 4), (key1768, 4), (key1536, 4), (key1809, 4), (key1261, 4), (key1651, 4), (key1268, 4), (key1531, 4), (key1609, 4), (key1256, 4)]

theorem rawRowCheck19949 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form5 = rawRow19949 := by decide +kernel

def row19949 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19949 : row19949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19949 := by decide +kernel

theorem rowEval19949 (x : Key → ℝ) : Integer.Sparse.eval row19949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19949, Integer.Sparse.eval_collectBalanced, rawRowCheck19949]

def rawRow19950 : Integer.Sparse Key := [(key1837, 4), (key1651, 4), (key1809, 4), (key1648, 4), (key1806, 4), (key1609, 4), (key1848, 4), (key1674, 4), (key1832, 4), (key1837, 4), (key1268, 4), (key1768, 4), (key1648, 4), (key1806, 4), (key1265, 4), (key1765, 4), (key1256, 4), (key1531, 4), (key1674, 4), (key1832, 4), (key1642, 4), (key1651, 4), (key1809, 4), (key1268, 4), (key1768, 4), (key1261, 4), (key1536, 4), (key1609, 4), (key1256, 4), (key1531, 4)]

theorem rawRowCheck19950 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form5 = rawRow19950 := by decide +kernel

def row19950 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19950 : row19950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19950 := by decide +kernel

theorem rowEval19950 (x : Key → ℝ) : Integer.Sparse.eval row19950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19950, Integer.Sparse.eval_collectBalanced, rawRowCheck19950]

def rawRow19951 : Integer.Sparse Key := [(key1837, 4), (key1809, 4), (key1651, 4), (key1806, 4), (key1648, 4), (key1609, 4), (key1848, 4), (key1832, 4), (key1674, 4), (key1837, 4), (key1768, 4), (key1268, 4), (key1806, 4), (key1648, 4), (key1765, 4), (key1265, 4), (key1531, 4), (key1256, 4), (key1832, 4), (key1674, 4), (key1642, 4), (key1809, 4), (key1651, 4), (key1768, 4), (key1268, 4), (key1536, 4), (key1261, 4), (key1609, 4), (key1531, 4), (key1256, 4)]

theorem rawRowCheck19951 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form5 = rawRow19951 := by decide +kernel

def row19951 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19951 : row19951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19951 := by decide +kernel

theorem rowEval19951 (x : Key → ℝ) : Integer.Sparse.eval row19951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19951, Integer.Sparse.eval_collectBalanced, rawRowCheck19951]

def rawRow19952 : Integer.Sparse Key := [(key1642, 4), (key1674, 4), (key1674, 4), (key1832, 4), (key1832, 4), (key1848, 4), (key1261, 4), (key1268, 4), (key1268, 4), (key1536, 4), (key1651, 4), (key1651, 4), (key1768, 4), (key1768, 4), (key1809, 4), (key1809, 4), (key1837, 4), (key1837, 4), (key1256, 4), (key1256, 4), (key1265, 4), (key1531, 4), (key1531, 4), (key1609, 4), (key1609, 4), (key1648, 4), (key1648, 4), (key1765, 4), (key1806, 4), (key1806, 4)]

theorem rawRowCheck19952 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form5 = rawRow19952 := by decide +kernel

def row19952 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19952 : row19952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19952 := by decide +kernel

theorem rowEval19952 (x : Key → ℝ) : Integer.Sparse.eval row19952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19952, Integer.Sparse.eval_collectBalanced, rawRowCheck19952]

def rawRow19953 : Integer.Sparse Key := [(key1674, 4), (key1642, 4), (key1674, 4), (key1832, 4), (key1848, 4), (key1832, 4), (key1268, 4), (key1261, 4), (key1268, 4), (key1651, 4), (key1536, 4), (key1651, 4), (key1809, 4), (key1837, 4), (key1768, 4), (key1837, 4), (key1768, 4), (key1809, 4), (key1256, 4), (key1265, 4), (key1256, 4), (key1609, 4), (key1648, 4), (key1531, 4), (key1648, 4), (key1531, 4), (key1609, 4), (key1806, 4), (key1765, 4), (key1806, 4)]

theorem rawRowCheck19953 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form5 = rawRow19953 := by decide +kernel

def row19953 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19953 : row19953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19953 := by decide +kernel

theorem rowEval19953 (x : Key → ℝ) : Integer.Sparse.eval row19953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19953, Integer.Sparse.eval_collectBalanced, rawRowCheck19953]

def rawRow19954 : Integer.Sparse Key := [(key1674, 4), (key1674, 4), (key1642, 4), (key1848, 4), (key1832, 4), (key1832, 4), (key1268, 4), (key1268, 4), (key1261, 4), (key1651, 4), (key1651, 4), (key1536, 4), (key1837, 4), (key1809, 4), (key1837, 4), (key1768, 4), (key1809, 4), (key1768, 4), (key1265, 4), (key1256, 4), (key1256, 4), (key1648, 4), (key1609, 4), (key1648, 4), (key1531, 4), (key1609, 4), (key1531, 4), (key1806, 4), (key1806, 4), (key1765, 4)]

theorem rawRowCheck19954 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form5 = rawRow19954 := by decide +kernel

def row19954 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19954 : row19954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19954 := by decide +kernel

theorem rowEval19954 (x : Key → ℝ) : Integer.Sparse.eval row19954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19954, Integer.Sparse.eval_collectBalanced, rawRowCheck19954]

def rawRow19955 : Integer.Sparse Key := [(key1642, 4), (key1832, 4), (key1832, 4), (key1674, 4), (key1674, 4), (key1848, 4), (key1536, 4), (key1768, 4), (key1768, 4), (key1261, 4), (key1809, 4), (key1809, 4), (key1268, 4), (key1268, 4), (key1651, 4), (key1651, 4), (key1837, 4), (key1837, 4), (key1531, 4), (key1531, 4), (key1765, 4), (key1256, 4), (key1256, 4), (key1609, 4), (key1609, 4), (key1806, 4), (key1806, 4), (key1265, 4), (key1648, 4), (key1648, 4)]

theorem rawRowCheck19955 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form5 = rawRow19955 := by decide +kernel

def row19955 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19955 : row19955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19955 := by decide +kernel

theorem rowEval19955 (x : Key → ℝ) : Integer.Sparse.eval row19955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19955, Integer.Sparse.eval_collectBalanced, rawRowCheck19955]

def rawRow19956 : Integer.Sparse Key := [(key1832, 4), (key1642, 4), (key1832, 4), (key1674, 4), (key1848, 4), (key1674, 4), (key1768, 4), (key1536, 4), (key1768, 4), (key1809, 4), (key1261, 4), (key1809, 4), (key1651, 4), (key1837, 4), (key1268, 4), (key1837, 4), (key1268, 4), (key1651, 4), (key1531, 4), (key1765, 4), (key1531, 4), (key1609, 4), (key1806, 4), (key1256, 4), (key1806, 4), (key1256, 4), (key1609, 4), (key1648, 4), (key1265, 4), (key1648, 4)]

theorem rawRowCheck19956 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form5 = rawRow19956 := by decide +kernel

def row19956 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19956 : row19956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19956 := by decide +kernel

theorem rowEval19956 (x : Key → ℝ) : Integer.Sparse.eval row19956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19956, Integer.Sparse.eval_collectBalanced, rawRowCheck19956]

def rawRow19957 : Integer.Sparse Key := [(key1832, 4), (key1832, 4), (key1642, 4), (key1848, 4), (key1674, 4), (key1674, 4), (key1768, 4), (key1768, 4), (key1536, 4), (key1809, 4), (key1809, 4), (key1261, 4), (key1837, 4), (key1651, 4), (key1837, 4), (key1268, 4), (key1651, 4), (key1268, 4), (key1765, 4), (key1531, 4), (key1531, 4), (key1806, 4), (key1609, 4), (key1806, 4), (key1256, 4), (key1609, 4), (key1256, 4), (key1648, 4), (key1648, 4), (key1265, 4)]

theorem rawRowCheck19957 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form5 = rawRow19957 := by decide +kernel

def row19957 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19957 : row19957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19957 := by decide +kernel

theorem rowEval19957 (x : Key → ℝ) : Integer.Sparse.eval row19957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19957, Integer.Sparse.eval_collectBalanced, rawRowCheck19957]

def rawRow19958 : Integer.Sparse Key := [(key1674, 4), (key1832, 4), (key1848, 4), (key1642, 4), (key1674, 4), (key1832, 4), (key1651, 4), (key1809, 4), (key1837, 4), (key1268, 4), (key1768, 4), (key1837, 4), (key1261, 4), (key1268, 4), (key1536, 4), (key1651, 4), (key1768, 4), (key1809, 4), (key1609, 4), (key1648, 4), (key1806, 4), (key1256, 4), (key1265, 4), (key1531, 4), (key1648, 4), (key1765, 4), (key1806, 4), (key1256, 4), (key1531, 4), (key1609, 4)]

theorem rawRowCheck19958 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form5 = rawRow19958 := by decide +kernel

def row19958 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19958 : row19958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19958 := by decide +kernel

theorem rowEval19958 (x : Key → ℝ) : Integer.Sparse.eval row19958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19958, Integer.Sparse.eval_collectBalanced, rawRowCheck19958]

def rawRow19959 : Integer.Sparse Key := [(key1674, 4), (key1848, 4), (key1832, 4), (key1674, 4), (key1642, 4), (key1832, 4), (key1651, 4), (key1837, 4), (key1809, 4), (key1268, 4), (key1837, 4), (key1768, 4), (key1268, 4), (key1261, 4), (key1651, 4), (key1536, 4), (key1809, 4), (key1768, 4), (key1648, 4), (key1609, 4), (key1806, 4), (key1265, 4), (key1256, 4), (key1648, 4), (key1531, 4), (key1806, 4), (key1765, 4), (key1256, 4), (key1609, 4), (key1531, 4)]

theorem rawRowCheck19959 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form5 = rawRow19959 := by decide +kernel

def row19959 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19959 : row19959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19959 := by decide +kernel

theorem rowEval19959 (x : Key → ℝ) : Integer.Sparse.eval row19959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19959, Integer.Sparse.eval_collectBalanced, rawRowCheck19959]

def rawRow19960 : Integer.Sparse Key := [(key1832, 4), (key1674, 4), (key1848, 4), (key1642, 4), (key1832, 4), (key1674, 4), (key1809, 4), (key1651, 4), (key1837, 4), (key1768, 4), (key1268, 4), (key1837, 4), (key1536, 4), (key1768, 4), (key1261, 4), (key1809, 4), (key1268, 4), (key1651, 4), (key1609, 4), (key1806, 4), (key1648, 4), (key1531, 4), (key1765, 4), (key1256, 4), (key1806, 4), (key1265, 4), (key1648, 4), (key1531, 4), (key1256, 4), (key1609, 4)]

theorem rawRowCheck19960 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form5 = rawRow19960 := by decide +kernel

def row19960 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19960 : row19960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19960 := by decide +kernel

theorem rowEval19960 (x : Key → ℝ) : Integer.Sparse.eval row19960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19960, Integer.Sparse.eval_collectBalanced, rawRowCheck19960]

def rawRow19961 : Integer.Sparse Key := [(key1832, 4), (key1848, 4), (key1674, 4), (key1832, 4), (key1642, 4), (key1674, 4), (key1809, 4), (key1837, 4), (key1651, 4), (key1768, 4), (key1837, 4), (key1268, 4), (key1768, 4), (key1536, 4), (key1809, 4), (key1261, 4), (key1651, 4), (key1268, 4), (key1806, 4), (key1609, 4), (key1648, 4), (key1765, 4), (key1531, 4), (key1806, 4), (key1256, 4), (key1648, 4), (key1265, 4), (key1531, 4), (key1609, 4), (key1256, 4)]

theorem rawRowCheck19961 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form5 = rawRow19961 := by decide +kernel

def row19961 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19961 : row19961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19961 := by decide +kernel

theorem rowEval19961 (x : Key → ℝ) : Integer.Sparse.eval row19961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19961, Integer.Sparse.eval_collectBalanced, rawRowCheck19961]

def rawRow19962 : Integer.Sparse Key := [(key1848, 4), (key1674, 4), (key1832, 4), (key1674, 4), (key1832, 4), (key1642, 4), (key1837, 4), (key1651, 4), (key1809, 4), (key1837, 4), (key1268, 4), (key1768, 4), (key1651, 4), (key1809, 4), (key1268, 4), (key1768, 4), (key1261, 4), (key1536, 4), (key1648, 4), (key1806, 4), (key1609, 4), (key1648, 4), (key1806, 4), (key1265, 4), (key1765, 4), (key1256, 4), (key1531, 4), (key1609, 4), (key1256, 4), (key1531, 4)]

theorem rawRowCheck19962 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form5 = rawRow19962 := by decide +kernel

def row19962 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19962 : row19962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19962 := by decide +kernel

theorem rowEval19962 (x : Key → ℝ) : Integer.Sparse.eval row19962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19962, Integer.Sparse.eval_collectBalanced, rawRowCheck19962]

def rawRow19963 : Integer.Sparse Key := [(key1848, 4), (key1832, 4), (key1674, 4), (key1832, 4), (key1674, 4), (key1642, 4), (key1837, 4), (key1809, 4), (key1651, 4), (key1837, 4), (key1768, 4), (key1268, 4), (key1809, 4), (key1651, 4), (key1768, 4), (key1268, 4), (key1536, 4), (key1261, 4), (key1806, 4), (key1648, 4), (key1609, 4), (key1806, 4), (key1648, 4), (key1765, 4), (key1265, 4), (key1531, 4), (key1256, 4), (key1609, 4), (key1531, 4), (key1256, 4)]

theorem rawRowCheck19963 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form5 = rawRow19963 := by decide +kernel

def row19963 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

theorem rowCheck19963 : row19963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19963 := by decide +kernel

theorem rowEval19963 (x : Key → ℝ) : Integer.Sparse.eval row19963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19963, Integer.Sparse.eval_collectBalanced, rawRowCheck19963]

def rawRow19964 : Integer.Sparse Key := [(key1252, 6), (key1257, 6), (key1257, 6), (key1266, 6), (key1527, 6), (key1532, 6), (key1532, 6), (key1605, 6), (key1610, 6), (key1605, 6), (key1638, 6), (key1610, 6), (key1638, 6), (key1649, 6), (key1649, 6), (key1672, 6), (key1766, 6), (key1807, 6), (key1807, 6), (key1830, 6)]

theorem rawRowCheck19964 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form6 = rawRow19964 := by decide +kernel

def row19964 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19964 : row19964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19964 := by decide +kernel

theorem rowEval19964 (x : Key → ℝ) : Integer.Sparse.eval row19964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19964, Integer.Sparse.eval_collectBalanced, rawRowCheck19964]

def rawRow19965 : Integer.Sparse Key := [(key1257, 6), (key1252, 6), (key1257, 6), (key1266, 6), (key1532, 6), (key1527, 6), (key1532, 6), (key1610, 6), (key1605, 6), (key1638, 6), (key1605, 6), (key1638, 6), (key1610, 6), (key1649, 6), (key1672, 6), (key1649, 6), (key1766, 6), (key1807, 6), (key1830, 6), (key1807, 6)]

theorem rawRowCheck19965 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form6 = rawRow19965 := by decide +kernel

def row19965 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19965 : row19965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19965 := by decide +kernel

theorem rowEval19965 (x : Key → ℝ) : Integer.Sparse.eval row19965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19965, Integer.Sparse.eval_collectBalanced, rawRowCheck19965]

def rawRow19966 : Integer.Sparse Key := [(key1257, 6), (key1257, 6), (key1252, 6), (key1266, 6), (key1532, 6), (key1532, 6), (key1527, 6), (key1638, 6), (key1638, 6), (key1610, 6), (key1610, 6), (key1605, 6), (key1605, 6), (key1672, 6), (key1649, 6), (key1649, 6), (key1766, 6), (key1830, 6), (key1807, 6), (key1807, 6)]

theorem rawRowCheck19966 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form6 = rawRow19966 := by decide +kernel

def row19966 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19966 : row19966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19966 := by decide +kernel

theorem rowEval19966 (x : Key → ℝ) : Integer.Sparse.eval row19966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19966, Integer.Sparse.eval_collectBalanced, rawRowCheck19966]

def rawRow19967 : Integer.Sparse Key := [(key1252, 6), (key1257, 6), (key1266, 6), (key1257, 6), (key1605, 6), (key1610, 6), (key1649, 6), (key1527, 6), (key1532, 6), (key1605, 6), (key1638, 6), (key1649, 6), (key1672, 6), (key1532, 6), (key1610, 6), (key1638, 6), (key1807, 6), (key1766, 6), (key1807, 6), (key1830, 6)]

theorem rawRowCheck19967 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form6 = rawRow19967 := by decide +kernel

def row19967 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19967 : row19967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19967 := by decide +kernel

theorem rowEval19967 (x : Key → ℝ) : Integer.Sparse.eval row19967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19967, Integer.Sparse.eval_collectBalanced, rawRowCheck19967]

end MUB6.Certificate.GramRows

end OAI
