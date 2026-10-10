import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow6912 : Integer.Sparse Key := [(key794, -1), (key819, -1), (key795, 2), (key864, -1), (key899, -1), (key794, 2), (key903, 2), (key795, -1), (key869, -1), (key899, 2), (key819, -1), (key903, -1), (key728, 1), (key739, 1), (key729, -2), (key864, 1), (key899, 1), (key728, -2), (key909, -2), (key729, 1), (key878, 1), (key899, -2), (key739, 1), (key909, 1), (key725, -1), (key744, -1), (key726, 1), (key735, 1), (key725, 1), (key826, 1), (key726, -1), (key813, -1), (key794, -1), (key903, -1), (key728, 1), (key909, 1), (key819, 1), (key903, 1), (key739, -1), (key909, -1)]

theorem rawRowCheck6912 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form6 = rawRow6912 := by decide +kernel

def row6912 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6912 : row6912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6912 := by decide +kernel

theorem rowEval6912 (x : Key → ℝ) : Integer.Sparse.eval row6912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6912, Integer.Sparse.eval_collectBalanced, rawRowCheck6912]

def rawRow6913 : Integer.Sparse Key := [(key819, -1), (key794, -1), (key795, 2), (key899, -1), (key864, -1), (key903, 2), (key794, 2), (key869, -1), (key795, -1), (key899, 2), (key903, -1), (key819, -1), (key739, 1), (key728, 1), (key729, -2), (key899, 1), (key864, 1), (key909, -2), (key728, -2), (key878, 1), (key729, 1), (key899, -2), (key909, 1), (key739, 1), (key744, -1), (key725, -1), (key735, 1), (key726, 1), (key826, 1), (key725, 1), (key813, -1), (key726, -1), (key903, -1), (key794, -1), (key909, 1), (key728, 1), (key903, 1), (key819, 1), (key909, -1), (key739, -1)]

theorem rawRowCheck6913 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form6 = rawRow6913 := by decide +kernel

def row6913 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6913 : row6913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6913 := by decide +kernel

theorem rowEval6913 (x : Key → ℝ) : Integer.Sparse.eval row6913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6913, Integer.Sparse.eval_collectBalanced, rawRowCheck6913]

def rawRow6914 : Integer.Sparse Key := [(key795, -1), (key819, -1), (key794, 2), (key869, -1), (key903, -1), (key795, 2), (key899, 2), (key794, -1), (key864, -1), (key903, 2), (key819, -1), (key899, -1), (key729, 1), (key739, 1), (key728, -2), (key878, 1), (key909, 1), (key729, -2), (key899, -2), (key728, 1), (key864, 1), (key909, -2), (key739, 1), (key899, 1), (key726, -1), (key739, -1), (key725, 1), (key728, 1), (key726, 1), (key819, 1), (key725, -1), (key794, -1), (key813, -1), (key909, -1), (key735, 1), (key903, 1), (key826, 1), (key909, 1), (key744, -1), (key903, -1)]

theorem rawRowCheck6914 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form6 = rawRow6914 := by decide +kernel

def row6914 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6914 : row6914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6914 := by decide +kernel

theorem rowEval6914 (x : Key → ℝ) : Integer.Sparse.eval row6914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6914, Integer.Sparse.eval_collectBalanced, rawRowCheck6914]

def rawRow6915 : Integer.Sparse Key := [(key819, -1), (key795, -1), (key794, 2), (key903, -1), (key869, -1), (key899, 2), (key795, 2), (key864, -1), (key794, -1), (key903, 2), (key899, -1), (key819, -1), (key739, 1), (key729, 1), (key728, -2), (key909, 1), (key878, 1), (key899, -2), (key729, -2), (key864, 1), (key728, 1), (key909, -2), (key899, 1), (key739, 1), (key739, -1), (key726, -1), (key728, 1), (key725, 1), (key819, 1), (key726, 1), (key794, -1), (key725, -1), (key909, -1), (key813, -1), (key903, 1), (key735, 1), (key909, 1), (key826, 1), (key903, -1), (key744, -1)]

theorem rawRowCheck6915 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form6 = rawRow6915 := by decide +kernel

def row6915 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6915 : row6915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6915 := by decide +kernel

theorem rowEval6915 (x : Key → ℝ) : Integer.Sparse.eval row6915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6915, Integer.Sparse.eval_collectBalanced, rawRowCheck6915]

def rawRow6916 : Integer.Sparse Key := [(key864, -1), (key899, -1), (key899, 2), (key794, -1), (key819, -1), (key794, 2), (key903, 2), (key819, -1), (key903, -1), (key795, 2), (key795, -1), (key869, -1), (key864, 1), (key899, 1), (key899, -2), (key728, 1), (key739, 1), (key728, -2), (key909, -2), (key739, 1), (key909, 1), (key729, -2), (key729, 1), (key878, 1), (key794, -1), (key903, -1), (key819, 1), (key903, 1), (key728, 1), (key909, 1), (key739, -1), (key909, -1), (key725, -1), (key744, -1), (key725, 1), (key826, 1), (key726, 1), (key735, 1), (key726, -1), (key813, -1)]

theorem rawRowCheck6916 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form6 = rawRow6916 := by decide +kernel

def row6916 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6916 : row6916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6916 := by decide +kernel

theorem rowEval6916 (x : Key → ℝ) : Integer.Sparse.eval row6916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6916, Integer.Sparse.eval_collectBalanced, rawRowCheck6916]

def rawRow6917 : Integer.Sparse Key := [(key899, -1), (key864, -1), (key899, 2), (key819, -1), (key794, -1), (key903, 2), (key794, 2), (key903, -1), (key819, -1), (key795, 2), (key869, -1), (key795, -1), (key899, 1), (key864, 1), (key899, -2), (key739, 1), (key728, 1), (key909, -2), (key728, -2), (key909, 1), (key739, 1), (key729, -2), (key878, 1), (key729, 1), (key903, -1), (key794, -1), (key903, 1), (key819, 1), (key909, 1), (key728, 1), (key909, -1), (key739, -1), (key744, -1), (key725, -1), (key826, 1), (key725, 1), (key735, 1), (key726, 1), (key813, -1), (key726, -1)]

theorem rawRowCheck6917 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form6 = rawRow6917 := by decide +kernel

def row6917 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6917 : row6917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6917 := by decide +kernel

theorem rowEval6917 (x : Key → ℝ) : Integer.Sparse.eval row6917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6917, Integer.Sparse.eval_collectBalanced, rawRowCheck6917]

def rawRow6918 : Integer.Sparse Key := [(key899, -1), (key899, -1), (key864, 2), (key903, -1), (key903, -1), (key819, 2), (key819, 2), (key794, -1), (key794, -1), (key869, 2), (key795, -1), (key795, -1), (key899, 1), (key899, 1), (key864, -2), (key909, 1), (key909, 1), (key739, -2), (key739, -2), (key728, 1), (key728, 1), (key878, -2), (key729, 1), (key729, 1), (key819, -1), (key819, -1), (key794, 1), (key794, 1), (key739, 1), (key739, 1), (key728, -1), (key728, -1), (key826, -1), (key826, -1), (key744, 1), (key744, 1), (key813, 1), (key813, 1), (key735, -1), (key735, -1)]

theorem rawRowCheck6918 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form6 = rawRow6918 := by decide +kernel

def row6918 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

theorem rowCheck6918 : row6918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6918 := by decide +kernel

theorem rowEval6918 (x : Key → ℝ) : Integer.Sparse.eval row6918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6918, Integer.Sparse.eval_collectBalanced, rawRowCheck6918]

def rawRow6919 : Integer.Sparse Key := [(key869, -1), (key903, -1), (key903, 2), (key795, -1), (key819, -1), (key795, 2), (key899, 2), (key819, -1), (key899, -1), (key794, 2), (key794, -1), (key864, -1), (key878, 1), (key909, 1), (key909, -2), (key729, 1), (key739, 1), (key729, -2), (key899, -2), (key739, 1), (key899, 1), (key728, -2), (key728, 1), (key864, 1), (key813, -1), (key909, -1), (key826, 1), (key909, 1), (key735, 1), (key903, 1), (key744, -1), (key903, -1), (key726, -1), (key739, -1), (key726, 1), (key819, 1), (key725, 1), (key728, 1), (key725, -1), (key794, -1)]

theorem rawRowCheck6919 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form6 = rawRow6919 := by decide +kernel

def row6919 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6919 : row6919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6919 := by decide +kernel

theorem rowEval6919 (x : Key → ℝ) : Integer.Sparse.eval row6919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6919, Integer.Sparse.eval_collectBalanced, rawRowCheck6919]

def rawRow6920 : Integer.Sparse Key := [(key903, -1), (key869, -1), (key903, 2), (key819, -1), (key795, -1), (key899, 2), (key795, 2), (key899, -1), (key819, -1), (key794, 2), (key864, -1), (key794, -1), (key909, 1), (key878, 1), (key909, -2), (key739, 1), (key729, 1), (key899, -2), (key729, -2), (key899, 1), (key739, 1), (key728, -2), (key864, 1), (key728, 1), (key909, -1), (key813, -1), (key909, 1), (key826, 1), (key903, 1), (key735, 1), (key903, -1), (key744, -1), (key739, -1), (key726, -1), (key819, 1), (key726, 1), (key728, 1), (key725, 1), (key794, -1), (key725, -1)]

theorem rawRowCheck6920 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form6 = rawRow6920 := by decide +kernel

def row6920 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6920 : row6920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6920 := by decide +kernel

theorem rowEval6920 (x : Key → ℝ) : Integer.Sparse.eval row6920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6920, Integer.Sparse.eval_collectBalanced, rawRowCheck6920]

def rawRow6921 : Integer.Sparse Key := [(key903, -1), (key903, -1), (key869, 2), (key899, -1), (key899, -1), (key819, 2), (key819, 2), (key795, -1), (key795, -1), (key864, 2), (key794, -1), (key794, -1), (key909, 1), (key909, 1), (key878, -2), (key899, 1), (key899, 1), (key739, -2), (key739, -2), (key729, 1), (key729, 1), (key864, -2), (key728, 1), (key728, 1), (key826, -1), (key826, -1), (key813, 1), (key813, 1), (key744, 1), (key744, 1), (key735, -1), (key735, -1), (key819, -1), (key819, -1), (key739, 1), (key739, 1), (key794, 1), (key794, 1), (key728, -1), (key728, -1)]

theorem rawRowCheck6921 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form6 = rawRow6921 := by decide +kernel

def row6921 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

theorem rowCheck6921 : row6921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6921 := by decide +kernel

theorem rowEval6921 (x : Key → ℝ) : Integer.Sparse.eval row6921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6921, Integer.Sparse.eval_collectBalanced, rawRowCheck6921]

def rawRow6922 : Integer.Sparse Key := [(key813, -1), (key813, -1), (key826, 2), (key813, -1), (key813, -1), (key878, 2), (key878, 2), (key909, -1), (key909, -1), (key826, 2), (key909, -1), (key909, -1), (key735, 1), (key735, 1), (key744, -2), (key735, 1), (key735, 1), (key869, -2), (key869, -2), (key903, 1), (key903, 1), (key744, -2), (key903, 1), (key903, 1), (key729, -1), (key729, -1), (key739, 1), (key739, 1), (key795, 1), (key795, 1), (key819, -1), (key819, -1), (key729, -1), (key729, -1), (key795, 1), (key795, 1), (key739, 1), (key739, 1), (key819, -1), (key819, -1)]

theorem rawRowCheck6922 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form6 = rawRow6922 := by decide +kernel

def row6922 : Integer.Sparse Key := [(key729, -4), (key735, 4), (key739, 4), (key744, -4), (key795, 4), (key813, -4), (key819, -4), (key826, 4), (key869, -4), (key878, 4), (key903, 4), (key909, -4)]

theorem rowCheck6922 : row6922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6922 := by decide +kernel

theorem rowEval6922 (x : Key → ℝ) : Integer.Sparse.eval row6922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6922, Integer.Sparse.eval_collectBalanced, rawRowCheck6922]

def rawRow6923 : Integer.Sparse Key := [(key813, -1), (key826, -1), (key813, 2), (key878, -1), (key909, -1), (key813, 2), (key909, 2), (key813, -1), (key878, -1), (key909, 2), (key826, -1), (key909, -1), (key735, 1), (key744, 1), (key735, -2), (key869, 1), (key903, 1), (key735, -2), (key903, -2), (key735, 1), (key869, 1), (key903, -2), (key744, 1), (key903, 1), (key726, -1), (key739, -1), (key726, 1), (key729, 1), (key726, 1), (key819, 1), (key726, -1), (key795, -1), (key795, -1), (key899, -1), (key729, 1), (key899, 1), (key819, 1), (key899, 1), (key739, -1), (key899, -1)]

theorem rawRowCheck6923 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form6 = rawRow6923 := by decide +kernel

def row6923 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

theorem rowCheck6923 : row6923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6923 := by decide +kernel

theorem rowEval6923 (x : Key → ℝ) : Integer.Sparse.eval row6923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6923, Integer.Sparse.eval_collectBalanced, rawRowCheck6923]

def rawRow6924 : Integer.Sparse Key := [(key826, -1), (key813, -1), (key813, 2), (key909, -1), (key878, -1), (key909, 2), (key813, 2), (key878, -1), (key813, -1), (key909, 2), (key909, -1), (key826, -1), (key744, 1), (key735, 1), (key735, -2), (key903, 1), (key869, 1), (key903, -2), (key735, -2), (key869, 1), (key735, 1), (key903, -2), (key903, 1), (key744, 1), (key739, -1), (key726, -1), (key729, 1), (key726, 1), (key819, 1), (key726, 1), (key795, -1), (key726, -1), (key899, -1), (key795, -1), (key899, 1), (key729, 1), (key899, 1), (key819, 1), (key899, -1), (key739, -1)]

theorem rawRowCheck6924 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form6 = rawRow6924 := by decide +kernel

def row6924 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

theorem rowCheck6924 : row6924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6924 := by decide +kernel

theorem rowEval6924 (x : Key → ℝ) : Integer.Sparse.eval row6924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6924, Integer.Sparse.eval_collectBalanced, rawRowCheck6924]

def rawRow6925 : Integer.Sparse Key := [(key878, -1), (key909, -1), (key909, 2), (key813, -1), (key826, -1), (key813, 2), (key909, 2), (key826, -1), (key909, -1), (key813, 2), (key813, -1), (key878, -1), (key869, 1), (key903, 1), (key903, -2), (key735, 1), (key744, 1), (key735, -2), (key903, -2), (key744, 1), (key903, 1), (key735, -2), (key735, 1), (key869, 1), (key795, -1), (key899, -1), (key819, 1), (key899, 1), (key729, 1), (key899, 1), (key739, -1), (key899, -1), (key726, -1), (key739, -1), (key726, 1), (key819, 1), (key726, 1), (key729, 1), (key726, -1), (key795, -1)]

theorem rawRowCheck6925 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form6 = rawRow6925 := by decide +kernel

def row6925 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

theorem rowCheck6925 : row6925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6925 := by decide +kernel

theorem rowEval6925 (x : Key → ℝ) : Integer.Sparse.eval row6925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6925, Integer.Sparse.eval_collectBalanced, rawRowCheck6925]

def rawRow6926 : Integer.Sparse Key := [(key909, -1), (key878, -1), (key909, 2), (key826, -1), (key813, -1), (key909, 2), (key813, 2), (key909, -1), (key826, -1), (key813, 2), (key878, -1), (key813, -1), (key903, 1), (key869, 1), (key903, -2), (key744, 1), (key735, 1), (key903, -2), (key735, -2), (key903, 1), (key744, 1), (key735, -2), (key869, 1), (key735, 1), (key899, -1), (key795, -1), (key899, 1), (key819, 1), (key899, 1), (key729, 1), (key899, -1), (key739, -1), (key739, -1), (key726, -1), (key819, 1), (key726, 1), (key729, 1), (key726, 1), (key795, -1), (key726, -1)]

theorem rawRowCheck6926 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form6 = rawRow6926 := by decide +kernel

def row6926 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

theorem rowCheck6926 : row6926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6926 := by decide +kernel

theorem rowEval6926 (x : Key → ℝ) : Integer.Sparse.eval row6926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6926, Integer.Sparse.eval_collectBalanced, rawRowCheck6926]

def rawRow6927 : Integer.Sparse Key := [(key909, -1), (key909, -1), (key878, 2), (key909, -1), (key909, -1), (key826, 2), (key826, 2), (key813, -1), (key813, -1), (key878, 2), (key813, -1), (key813, -1), (key903, 1), (key903, 1), (key869, -2), (key903, 1), (key903, 1), (key744, -2), (key744, -2), (key735, 1), (key735, 1), (key869, -2), (key735, 1), (key735, 1), (key819, -1), (key819, -1), (key795, 1), (key795, 1), (key739, 1), (key739, 1), (key729, -1), (key729, -1), (key819, -1), (key819, -1), (key739, 1), (key739, 1), (key795, 1), (key795, 1), (key729, -1), (key729, -1)]

theorem rawRowCheck6927 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form6 = rawRow6927 := by decide +kernel

def row6927 : Integer.Sparse Key := [(key729, -4), (key735, 4), (key739, 4), (key744, -4), (key795, 4), (key813, -4), (key819, -4), (key826, 4), (key869, -4), (key878, 4), (key903, 4), (key909, -4)]

theorem rowCheck6927 : row6927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6927 := by decide +kernel

theorem rowEval6927 (x : Key → ℝ) : Integer.Sparse.eval row6927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6927, Integer.Sparse.eval_collectBalanced, rawRowCheck6927]

def rawRow6928 : Integer.Sparse Key := [(key2031, 1), (key2036, 1), (key2036, -2), (key2150, 1), (key2155, 1), (key2150, -2), (key2168, -2), (key2155, 1), (key2168, 1), (key2195, -2), (key2195, 1), (key2201, 1), (key2061, -1), (key2066, -1), (key2066, 1), (key2071, 1), (key2150, -1), (key2155, -1), (key2150, 1), (key2168, 1), (key2243, 1), (key2255, 1), (key2248, -1), (key2255, -1), (key2304, 1), (key2306, 1), (key2306, -1), (key2311, -1), (key2093, 2), (key2093, -1), (key2096, -1), (key2195, 2), (key2195, -1), (key2201, -1), (key2304, -1), (key2306, -1), (key2304, -1), (key2311, -1), (key2306, 2), (key2311, 2)]

theorem rawRowCheck6928 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form7 = rawRow6928 := by decide +kernel

def row6928 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6928 : row6928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6928 := by decide +kernel

theorem rowEval6928 (x : Key → ℝ) : Integer.Sparse.eval row6928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6928, Integer.Sparse.eval_collectBalanced, rawRowCheck6928]

def rawRow6929 : Integer.Sparse Key := [(key2036, 1), (key2031, 1), (key2036, -2), (key2155, 1), (key2150, 1), (key2168, -2), (key2150, -2), (key2168, 1), (key2155, 1), (key2195, -2), (key2201, 1), (key2195, 1), (key2066, -1), (key2061, -1), (key2071, 1), (key2066, 1), (key2155, -1), (key2150, -1), (key2168, 1), (key2150, 1), (key2255, 1), (key2243, 1), (key2255, -1), (key2248, -1), (key2306, 1), (key2304, 1), (key2311, -1), (key2306, -1), (key2093, 2), (key2096, -1), (key2093, -1), (key2195, 2), (key2201, -1), (key2195, -1), (key2306, -1), (key2304, -1), (key2311, -1), (key2304, -1), (key2311, 2), (key2306, 2)]

theorem rawRowCheck6929 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form7 = rawRow6929 := by decide +kernel

def row6929 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6929 : row6929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6929 := by decide +kernel

theorem rowEval6929 (x : Key → ℝ) : Integer.Sparse.eval row6929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6929, Integer.Sparse.eval_collectBalanced, rawRowCheck6929]

def rawRow6930 : Integer.Sparse Key := [(key2036, 1), (key2036, 1), (key2031, -2), (key2168, 1), (key2168, 1), (key2155, -2), (key2155, -2), (key2150, 1), (key2150, 1), (key2201, -2), (key2195, 1), (key2195, 1), (key2071, -1), (key2071, -1), (key2061, 1), (key2061, 1), (key2168, -1), (key2168, -1), (key2155, 1), (key2155, 1), (key2248, 1), (key2248, 1), (key2243, -1), (key2243, -1), (key2311, 1), (key2311, 1), (key2304, -1), (key2304, -1), (key2096, 2), (key2093, -1), (key2093, -1), (key2201, 2), (key2195, -1), (key2195, -1), (key2311, -1), (key2311, -1), (key2306, -1), (key2306, -1), (key2304, 2), (key2304, 2)]

theorem rawRowCheck6930 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form7 = rawRow6930 := by decide +kernel

def row6930 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

theorem rowCheck6930 : row6930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6930 := by decide +kernel

theorem rowEval6930 (x : Key → ℝ) : Integer.Sparse.eval row6930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6930, Integer.Sparse.eval_collectBalanced, rawRowCheck6930]

def rawRow6931 : Integer.Sparse Key := [(key2150, 1), (key2155, 1), (key2195, -2), (key2031, 1), (key2036, 1), (key2150, -2), (key2168, -2), (key2195, 1), (key2201, 1), (key2036, -2), (key2155, 1), (key2168, 1), (key2150, -1), (key2155, -1), (key2304, 1), (key2306, 1), (key2061, -1), (key2066, -1), (key2243, 1), (key2255, 1), (key2150, 1), (key2168, 1), (key2306, -1), (key2311, -1), (key2066, 1), (key2071, 1), (key2248, -1), (key2255, -1), (key2195, 2), (key2304, -1), (key2306, -1), (key2093, 2), (key2304, -1), (key2311, -1), (key2093, -1), (key2096, -1), (key2195, -1), (key2201, -1), (key2306, 2), (key2311, 2)]

theorem rawRowCheck6931 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form7 = rawRow6931 := by decide +kernel

def row6931 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6931 : row6931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6931 := by decide +kernel

theorem rowEval6931 (x : Key → ℝ) : Integer.Sparse.eval row6931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6931, Integer.Sparse.eval_collectBalanced, rawRowCheck6931]

def rawRow6932 : Integer.Sparse Key := [(key2155, 1), (key2150, 1), (key2195, -2), (key2036, 1), (key2031, 1), (key2168, -2), (key2150, -2), (key2201, 1), (key2195, 1), (key2036, -2), (key2168, 1), (key2155, 1), (key2155, -1), (key2150, -1), (key2306, 1), (key2304, 1), (key2066, -1), (key2061, -1), (key2255, 1), (key2243, 1), (key2168, 1), (key2150, 1), (key2311, -1), (key2306, -1), (key2071, 1), (key2066, 1), (key2255, -1), (key2248, -1), (key2195, 2), (key2306, -1), (key2304, -1), (key2093, 2), (key2311, -1), (key2304, -1), (key2096, -1), (key2093, -1), (key2201, -1), (key2195, -1), (key2311, 2), (key2306, 2)]

theorem rawRowCheck6932 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form7 = rawRow6932 := by decide +kernel

def row6932 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6932 : row6932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6932 := by decide +kernel

theorem rowEval6932 (x : Key → ℝ) : Integer.Sparse.eval row6932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6932, Integer.Sparse.eval_collectBalanced, rawRowCheck6932]

def rawRow6933 : Integer.Sparse Key := [(key2150, 1), (key2195, 1), (key2155, -2), (key2150, 1), (key2195, 1), (key2031, -2), (key2201, -2), (key2036, 1), (key2168, 1), (key2155, -2), (key2036, 1), (key2168, 1), (key2243, -1), (key2304, -1), (key2155, 1), (key2248, 1), (key2243, -1), (key2304, -1), (key2061, 1), (key2311, 1), (key2061, 1), (key2311, 1), (key2071, -1), (key2168, -1), (key2155, 1), (key2248, 1), (key2071, -1), (key2168, -1), (key2304, 2), (key2195, -1), (key2306, -1), (key2304, 2), (key2093, -1), (key2311, -1), (key2195, -1), (key2306, -1), (key2093, -1), (key2311, -1), (key2096, 2), (key2201, 2)]

theorem rawRowCheck6933 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form7 = rawRow6933 := by decide +kernel

def row6933 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

theorem rowCheck6933 : row6933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6933 := by decide +kernel

theorem rowEval6933 (x : Key → ℝ) : Integer.Sparse.eval row6933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6933, Integer.Sparse.eval_collectBalanced, rawRowCheck6933]

def rawRow6934 : Integer.Sparse Key := [(key2195, 1), (key2150, 1), (key2155, -2), (key2195, 1), (key2150, 1), (key2201, -2), (key2031, -2), (key2168, 1), (key2036, 1), (key2155, -2), (key2168, 1), (key2036, 1), (key2304, -1), (key2243, -1), (key2248, 1), (key2155, 1), (key2304, -1), (key2243, -1), (key2311, 1), (key2061, 1), (key2311, 1), (key2061, 1), (key2168, -1), (key2071, -1), (key2248, 1), (key2155, 1), (key2168, -1), (key2071, -1), (key2304, 2), (key2306, -1), (key2195, -1), (key2304, 2), (key2311, -1), (key2093, -1), (key2306, -1), (key2195, -1), (key2311, -1), (key2093, -1), (key2201, 2), (key2096, 2)]

theorem rawRowCheck6934 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form7 = rawRow6934 := by decide +kernel

def row6934 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

theorem rowCheck6934 : row6934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6934 := by decide +kernel

theorem rowEval6934 (x : Key → ℝ) : Integer.Sparse.eval row6934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6934, Integer.Sparse.eval_collectBalanced, rawRowCheck6934]

def rawRow6935 : Integer.Sparse Key := [(key2155, 1), (key2195, 1), (key2150, -2), (key2168, 1), (key2201, 1), (key2036, -2), (key2195, -2), (key2031, 1), (key2150, 1), (key2168, -2), (key2036, 1), (key2155, 1), (key2248, -1), (key2306, -1), (key2150, 1), (key2243, 1), (key2255, -1), (key2311, -1), (key2066, 1), (key2304, 1), (key2071, 1), (key2306, 1), (key2061, -1), (key2150, -1), (key2168, 1), (key2255, 1), (key2066, -1), (key2155, -1), (key2306, 2), (key2195, -1), (key2304, -1), (key2311, 2), (key2093, -1), (key2304, -1), (key2201, -1), (key2311, -1), (key2096, -1), (key2306, -1), (key2093, 2), (key2195, 2)]

theorem rawRowCheck6935 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form7 = rawRow6935 := by decide +kernel

def row6935 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6935 : row6935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6935 := by decide +kernel

theorem rowEval6935 (x : Key → ℝ) : Integer.Sparse.eval row6935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6935, Integer.Sparse.eval_collectBalanced, rawRowCheck6935]

def rawRow6936 : Integer.Sparse Key := [(key2195, 1), (key2155, 1), (key2150, -2), (key2201, 1), (key2168, 1), (key2195, -2), (key2036, -2), (key2150, 1), (key2031, 1), (key2168, -2), (key2155, 1), (key2036, 1), (key2306, -1), (key2248, -1), (key2243, 1), (key2150, 1), (key2311, -1), (key2255, -1), (key2304, 1), (key2066, 1), (key2306, 1), (key2071, 1), (key2150, -1), (key2061, -1), (key2255, 1), (key2168, 1), (key2155, -1), (key2066, -1), (key2306, 2), (key2304, -1), (key2195, -1), (key2311, 2), (key2304, -1), (key2093, -1), (key2311, -1), (key2201, -1), (key2306, -1), (key2096, -1), (key2195, 2), (key2093, 2)]

theorem rawRowCheck6936 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form7 = rawRow6936 := by decide +kernel

def row6936 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6936 : row6936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6936 := by decide +kernel

theorem rowEval6936 (x : Key → ℝ) : Integer.Sparse.eval row6936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6936, Integer.Sparse.eval_collectBalanced, rawRowCheck6936]

def rawRow6937 : Integer.Sparse Key := [(key2168, 1), (key2168, 1), (key2201, -2), (key2036, 1), (key2036, 1), (key2155, -2), (key2155, -2), (key2195, 1), (key2195, 1), (key2031, -2), (key2150, 1), (key2150, 1), (key2168, -1), (key2168, -1), (key2311, 1), (key2311, 1), (key2071, -1), (key2071, -1), (key2248, 1), (key2248, 1), (key2155, 1), (key2155, 1), (key2304, -1), (key2304, -1), (key2061, 1), (key2061, 1), (key2243, -1), (key2243, -1), (key2201, 2), (key2311, -1), (key2311, -1), (key2096, 2), (key2306, -1), (key2306, -1), (key2093, -1), (key2093, -1), (key2195, -1), (key2195, -1), (key2304, 2), (key2304, 2)]

theorem rawRowCheck6937 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form7 = rawRow6937 := by decide +kernel

def row6937 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

theorem rowCheck6937 : row6937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6937 := by decide +kernel

theorem rowEval6937 (x : Key → ℝ) : Integer.Sparse.eval row6937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6937, Integer.Sparse.eval_collectBalanced, rawRowCheck6937]

def rawRow6938 : Integer.Sparse Key := [(key2168, 1), (key2201, 1), (key2168, -2), (key2155, 1), (key2195, 1), (key2036, -2), (key2195, -2), (key2036, 1), (key2155, 1), (key2150, -2), (key2031, 1), (key2150, 1), (key2255, -1), (key2311, -1), (key2168, 1), (key2255, 1), (key2248, -1), (key2306, -1), (key2071, 1), (key2306, 1), (key2066, 1), (key2304, 1), (key2066, -1), (key2155, -1), (key2150, 1), (key2243, 1), (key2061, -1), (key2150, -1), (key2311, 2), (key2201, -1), (key2311, -1), (key2306, 2), (key2096, -1), (key2306, -1), (key2195, -1), (key2304, -1), (key2093, -1), (key2304, -1), (key2093, 2), (key2195, 2)]

theorem rawRowCheck6938 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form7 = rawRow6938 := by decide +kernel

def row6938 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6938 : row6938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6938 := by decide +kernel

theorem rowEval6938 (x : Key → ℝ) : Integer.Sparse.eval row6938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6938, Integer.Sparse.eval_collectBalanced, rawRowCheck6938]

def rawRow6939 : Integer.Sparse Key := [(key2201, 1), (key2168, 1), (key2168, -2), (key2195, 1), (key2155, 1), (key2195, -2), (key2036, -2), (key2155, 1), (key2036, 1), (key2150, -2), (key2150, 1), (key2031, 1), (key2311, -1), (key2255, -1), (key2255, 1), (key2168, 1), (key2306, -1), (key2248, -1), (key2306, 1), (key2071, 1), (key2304, 1), (key2066, 1), (key2155, -1), (key2066, -1), (key2243, 1), (key2150, 1), (key2150, -1), (key2061, -1), (key2311, 2), (key2311, -1), (key2201, -1), (key2306, 2), (key2306, -1), (key2096, -1), (key2304, -1), (key2195, -1), (key2304, -1), (key2093, -1), (key2195, 2), (key2093, 2)]

theorem rawRowCheck6939 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form7 = rawRow6939 := by decide +kernel

def row6939 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6939 : row6939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6939 := by decide +kernel

theorem rowEval6939 (x : Key → ℝ) : Integer.Sparse.eval row6939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6939, Integer.Sparse.eval_collectBalanced, rawRowCheck6939]

def rawRow6940 : Integer.Sparse Key := [(key2061, 1), (key2066, 1), (key2093, -2), (key2061, 1), (key2066, 1), (key2243, -2), (key2255, -2), (key2304, 1), (key2311, 1), (key2093, -2), (key2304, 1), (key2311, 1), (key2031, -1), (key2036, -1), (key2093, 1), (key2096, 1), (key2031, -1), (key2036, -1), (key2150, 1), (key2168, 1), (key2150, 1), (key2168, 1), (key2306, -1), (key2311, -1), (key2093, 1), (key2096, 1), (key2306, -1), (key2311, -1), (key2036, 2), (key2066, -1), (key2071, -1), (key2036, 2), (key2155, -1), (key2168, -1), (key2066, -1), (key2071, -1), (key2155, -1), (key2168, -1), (key2248, 2), (key2255, 2)]

theorem rawRowCheck6940 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form7 = rawRow6940 := by decide +kernel

def row6940 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

theorem rowCheck6940 : row6940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6940 := by decide +kernel

theorem rowEval6940 (x : Key → ℝ) : Integer.Sparse.eval row6940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6940, Integer.Sparse.eval_collectBalanced, rawRowCheck6940]

def rawRow6941 : Integer.Sparse Key := [(key2066, 1), (key2061, 1), (key2093, -2), (key2066, 1), (key2061, 1), (key2255, -2), (key2243, -2), (key2311, 1), (key2304, 1), (key2093, -2), (key2311, 1), (key2304, 1), (key2036, -1), (key2031, -1), (key2096, 1), (key2093, 1), (key2036, -1), (key2031, -1), (key2168, 1), (key2150, 1), (key2168, 1), (key2150, 1), (key2311, -1), (key2306, -1), (key2096, 1), (key2093, 1), (key2311, -1), (key2306, -1), (key2036, 2), (key2071, -1), (key2066, -1), (key2036, 2), (key2168, -1), (key2155, -1), (key2071, -1), (key2066, -1), (key2168, -1), (key2155, -1), (key2255, 2), (key2248, 2)]

theorem rawRowCheck6941 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form7 = rawRow6941 := by decide +kernel

def row6941 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

theorem rowCheck6941 : row6941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6941 := by decide +kernel

theorem rowEval6941 (x : Key → ℝ) : Integer.Sparse.eval row6941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6941, Integer.Sparse.eval_collectBalanced, rawRowCheck6941]

def rawRow6942 : Integer.Sparse Key := [(key2061, 1), (key2093, 1), (key2066, -2), (key2243, 1), (key2304, 1), (key2061, -2), (key2311, -2), (key2066, 1), (key2255, 1), (key2304, -2), (key2093, 1), (key2311, 1), (key2061, -1), (key2093, -1), (key2036, 1), (key2071, 1), (key2150, -1), (key2195, -1), (key2031, 1), (key2201, 1), (key2061, 1), (key2311, 1), (key2071, -1), (key2168, -1), (key2195, 1), (key2306, 1), (key2096, -1), (key2201, -1), (key2066, 2), (key2036, -1), (key2071, -1), (key2155, 2), (key2036, -1), (key2168, -1), (key2155, -1), (key2248, -1), (key2066, -1), (key2255, -1), (key2071, 2), (key2168, 2)]

theorem rawRowCheck6942 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form7 = rawRow6942 := by decide +kernel

def row6942 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6942 : row6942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6942 := by decide +kernel

theorem rowEval6942 (x : Key → ℝ) : Integer.Sparse.eval row6942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6942, Integer.Sparse.eval_collectBalanced, rawRowCheck6942]

def rawRow6943 : Integer.Sparse Key := [(key2093, 1), (key2061, 1), (key2066, -2), (key2304, 1), (key2243, 1), (key2311, -2), (key2061, -2), (key2255, 1), (key2066, 1), (key2304, -2), (key2311, 1), (key2093, 1), (key2093, -1), (key2061, -1), (key2071, 1), (key2036, 1), (key2195, -1), (key2150, -1), (key2201, 1), (key2031, 1), (key2311, 1), (key2061, 1), (key2168, -1), (key2071, -1), (key2306, 1), (key2195, 1), (key2201, -1), (key2096, -1), (key2066, 2), (key2071, -1), (key2036, -1), (key2155, 2), (key2168, -1), (key2036, -1), (key2248, -1), (key2155, -1), (key2255, -1), (key2066, -1), (key2168, 2), (key2071, 2)]

theorem rawRowCheck6943 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form7 = rawRow6943 := by decide +kernel

def row6943 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6943 : row6943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6943 := by decide +kernel

theorem rowEval6943 (x : Key → ℝ) : Integer.Sparse.eval row6943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6943, Integer.Sparse.eval_collectBalanced, rawRowCheck6943]

def rawRow6944 : Integer.Sparse Key := [(key2066, 1), (key2093, 1), (key2061, -2), (key2255, 1), (key2311, 1), (key2066, -2), (key2304, -2), (key2061, 1), (key2243, 1), (key2311, -2), (key2093, 1), (key2304, 1), (key2071, -1), (key2096, -1), (key2031, 1), (key2061, 1), (key2168, -1), (key2201, -1), (key2036, 1), (key2195, 1), (key2071, 1), (key2306, 1), (key2061, -1), (key2150, -1), (key2201, 1), (key2311, 1), (key2093, -1), (key2195, -1), (key2071, 2), (key2036, -1), (key2066, -1), (key2168, 2), (key2036, -1), (key2155, -1), (key2168, -1), (key2255, -1), (key2071, -1), (key2248, -1), (key2066, 2), (key2155, 2)]

theorem rawRowCheck6944 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form7 = rawRow6944 := by decide +kernel

def row6944 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6944 : row6944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6944 := by decide +kernel

theorem rowEval6944 (x : Key → ℝ) : Integer.Sparse.eval row6944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6944, Integer.Sparse.eval_collectBalanced, rawRowCheck6944]

def rawRow6945 : Integer.Sparse Key := [(key2093, 1), (key2066, 1), (key2061, -2), (key2311, 1), (key2255, 1), (key2304, -2), (key2066, -2), (key2243, 1), (key2061, 1), (key2311, -2), (key2304, 1), (key2093, 1), (key2096, -1), (key2071, -1), (key2061, 1), (key2031, 1), (key2201, -1), (key2168, -1), (key2195, 1), (key2036, 1), (key2306, 1), (key2071, 1), (key2150, -1), (key2061, -1), (key2311, 1), (key2201, 1), (key2195, -1), (key2093, -1), (key2071, 2), (key2066, -1), (key2036, -1), (key2168, 2), (key2155, -1), (key2036, -1), (key2255, -1), (key2168, -1), (key2248, -1), (key2071, -1), (key2155, 2), (key2066, 2)]

theorem rawRowCheck6945 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form7 = rawRow6945 := by decide +kernel

def row6945 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6945 : row6945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6945 := by decide +kernel

theorem rowEval6945 (x : Key → ℝ) : Integer.Sparse.eval row6945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6945, Integer.Sparse.eval_collectBalanced, rawRowCheck6945]

def rawRow6946 : Integer.Sparse Key := [(key2243, 1), (key2304, 1), (key2304, -2), (key2061, 1), (key2093, 1), (key2061, -2), (key2311, -2), (key2093, 1), (key2311, 1), (key2066, -2), (key2066, 1), (key2255, 1), (key2150, -1), (key2195, -1), (key2195, 1), (key2306, 1), (key2061, -1), (key2093, -1), (key2061, 1), (key2311, 1), (key2031, 1), (key2201, 1), (key2096, -1), (key2201, -1), (key2036, 1), (key2071, 1), (key2071, -1), (key2168, -1), (key2155, 2), (key2155, -1), (key2248, -1), (key2066, 2), (key2066, -1), (key2255, -1), (key2036, -1), (key2071, -1), (key2036, -1), (key2168, -1), (key2071, 2), (key2168, 2)]

theorem rawRowCheck6946 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form7 = rawRow6946 := by decide +kernel

def row6946 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6946 : row6946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6946 := by decide +kernel

theorem rowEval6946 (x : Key → ℝ) : Integer.Sparse.eval row6946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6946, Integer.Sparse.eval_collectBalanced, rawRowCheck6946]

def rawRow6947 : Integer.Sparse Key := [(key2304, 1), (key2243, 1), (key2304, -2), (key2093, 1), (key2061, 1), (key2311, -2), (key2061, -2), (key2311, 1), (key2093, 1), (key2066, -2), (key2255, 1), (key2066, 1), (key2195, -1), (key2150, -1), (key2306, 1), (key2195, 1), (key2093, -1), (key2061, -1), (key2311, 1), (key2061, 1), (key2201, 1), (key2031, 1), (key2201, -1), (key2096, -1), (key2071, 1), (key2036, 1), (key2168, -1), (key2071, -1), (key2155, 2), (key2248, -1), (key2155, -1), (key2066, 2), (key2255, -1), (key2066, -1), (key2071, -1), (key2036, -1), (key2168, -1), (key2036, -1), (key2168, 2), (key2071, 2)]

theorem rawRowCheck6947 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form7 = rawRow6947 := by decide +kernel

def row6947 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6947 : row6947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6947 := by decide +kernel

theorem rowEval6947 (x : Key → ℝ) : Integer.Sparse.eval row6947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6947, Integer.Sparse.eval_collectBalanced, rawRowCheck6947]

def rawRow6948 : Integer.Sparse Key := [(key2304, 1), (key2304, 1), (key2243, -2), (key2311, 1), (key2311, 1), (key2093, -2), (key2093, -2), (key2061, 1), (key2061, 1), (key2255, -2), (key2066, 1), (key2066, 1), (key2306, -1), (key2306, -1), (key2150, 1), (key2150, 1), (key2311, -1), (key2311, -1), (key2093, 1), (key2093, 1), (key2096, 1), (key2096, 1), (key2031, -1), (key2031, -1), (key2168, 1), (key2168, 1), (key2036, -1), (key2036, -1), (key2248, 2), (key2155, -1), (key2155, -1), (key2255, 2), (key2066, -1), (key2066, -1), (key2168, -1), (key2168, -1), (key2071, -1), (key2071, -1), (key2036, 2), (key2036, 2)]

theorem rawRowCheck6948 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form7 = rawRow6948 := by decide +kernel

def row6948 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

theorem rowCheck6948 : row6948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6948 := by decide +kernel

theorem rowEval6948 (x : Key → ℝ) : Integer.Sparse.eval row6948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6948, Integer.Sparse.eval_collectBalanced, rawRowCheck6948]

def rawRow6949 : Integer.Sparse Key := [(key2255, 1), (key2311, 1), (key2311, -2), (key2066, 1), (key2093, 1), (key2066, -2), (key2304, -2), (key2093, 1), (key2304, 1), (key2061, -2), (key2061, 1), (key2243, 1), (key2168, -1), (key2201, -1), (key2201, 1), (key2311, 1), (key2071, -1), (key2096, -1), (key2071, 1), (key2306, 1), (key2036, 1), (key2195, 1), (key2093, -1), (key2195, -1), (key2031, 1), (key2061, 1), (key2061, -1), (key2150, -1), (key2168, 2), (key2168, -1), (key2255, -1), (key2071, 2), (key2071, -1), (key2248, -1), (key2036, -1), (key2066, -1), (key2036, -1), (key2155, -1), (key2066, 2), (key2155, 2)]

theorem rawRowCheck6949 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form7 = rawRow6949 := by decide +kernel

def row6949 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6949 : row6949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6949 := by decide +kernel

theorem rowEval6949 (x : Key → ℝ) : Integer.Sparse.eval row6949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6949, Integer.Sparse.eval_collectBalanced, rawRowCheck6949]

def rawRow6950 : Integer.Sparse Key := [(key2311, 1), (key2255, 1), (key2311, -2), (key2093, 1), (key2066, 1), (key2304, -2), (key2066, -2), (key2304, 1), (key2093, 1), (key2061, -2), (key2243, 1), (key2061, 1), (key2201, -1), (key2168, -1), (key2311, 1), (key2201, 1), (key2096, -1), (key2071, -1), (key2306, 1), (key2071, 1), (key2195, 1), (key2036, 1), (key2195, -1), (key2093, -1), (key2061, 1), (key2031, 1), (key2150, -1), (key2061, -1), (key2168, 2), (key2255, -1), (key2168, -1), (key2071, 2), (key2248, -1), (key2071, -1), (key2066, -1), (key2036, -1), (key2155, -1), (key2036, -1), (key2155, 2), (key2066, 2)]

theorem rawRowCheck6950 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form7 = rawRow6950 := by decide +kernel

def row6950 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

theorem rowCheck6950 : row6950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6950 := by decide +kernel

theorem rowEval6950 (x : Key → ℝ) : Integer.Sparse.eval row6950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6950, Integer.Sparse.eval_collectBalanced, rawRowCheck6950]

def rawRow6951 : Integer.Sparse Key := [(key2311, 1), (key2311, 1), (key2255, -2), (key2304, 1), (key2304, 1), (key2093, -2), (key2093, -2), (key2066, 1), (key2066, 1), (key2243, -2), (key2061, 1), (key2061, 1), (key2311, -1), (key2311, -1), (key2168, 1), (key2168, 1), (key2306, -1), (key2306, -1), (key2096, 1), (key2096, 1), (key2093, 1), (key2093, 1), (key2036, -1), (key2036, -1), (key2150, 1), (key2150, 1), (key2031, -1), (key2031, -1), (key2255, 2), (key2168, -1), (key2168, -1), (key2248, 2), (key2071, -1), (key2071, -1), (key2155, -1), (key2155, -1), (key2066, -1), (key2066, -1), (key2036, 2), (key2036, 2)]

theorem rawRowCheck6951 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form7 = rawRow6951 := by decide +kernel

def row6951 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

theorem rowCheck6951 : row6951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6951 := by decide +kernel

theorem rowEval6951 (x : Key → ℝ) : Integer.Sparse.eval row6951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6951, Integer.Sparse.eval_collectBalanced, rawRowCheck6951]

def rawRow6952 : Integer.Sparse Key := [(key2071, 1), (key2071, 1), (key2096, -2), (key2071, 1), (key2071, 1), (key2248, -2), (key2248, -2), (key2306, 1), (key2306, 1), (key2096, -2), (key2306, 1), (key2306, 1), (key2036, -1), (key2036, -1), (key2093, 1), (key2093, 1), (key2036, -1), (key2036, -1), (key2155, 1), (key2155, 1), (key2155, 1), (key2155, 1), (key2304, -1), (key2304, -1), (key2093, 1), (key2093, 1), (key2304, -1), (key2304, -1), (key2031, 2), (key2061, -1), (key2061, -1), (key2031, 2), (key2150, -1), (key2150, -1), (key2061, -1), (key2061, -1), (key2150, -1), (key2150, -1), (key2243, 2), (key2243, 2)]

theorem rawRowCheck6952 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form7 = rawRow6952 := by decide +kernel

def row6952 : Integer.Sparse Key := [(key2031, 4), (key2036, -4), (key2061, -4), (key2071, 4), (key2093, 4), (key2096, -4), (key2150, -4), (key2155, 4), (key2243, 4), (key2248, -4), (key2304, -4), (key2306, 4)]

theorem rowCheck6952 : row6952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6952 := by decide +kernel

theorem rowEval6952 (x : Key → ℝ) : Integer.Sparse.eval row6952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6952, Integer.Sparse.eval_collectBalanced, rawRowCheck6952]

def rawRow6953 : Integer.Sparse Key := [(key2071, 1), (key2096, 1), (key2071, -2), (key2248, 1), (key2306, 1), (key2071, -2), (key2306, -2), (key2071, 1), (key2248, 1), (key2306, -2), (key2096, 1), (key2306, 1), (key2066, -1), (key2093, -1), (key2036, 1), (key2066, 1), (key2155, -1), (key2195, -1), (key2036, 1), (key2195, 1), (key2066, 1), (key2304, 1), (key2066, -1), (key2155, -1), (key2195, 1), (key2304, 1), (key2093, -1), (key2195, -1), (key2061, 2), (key2031, -1), (key2061, -1), (key2150, 2), (key2031, -1), (key2150, -1), (key2150, -1), (key2243, -1), (key2061, -1), (key2243, -1), (key2061, 2), (key2150, 2)]

theorem rawRowCheck6953 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form7 = rawRow6953 := by decide +kernel

def row6953 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

theorem rowCheck6953 : row6953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6953 := by decide +kernel

theorem rowEval6953 (x : Key → ℝ) : Integer.Sparse.eval row6953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6953, Integer.Sparse.eval_collectBalanced, rawRowCheck6953]

def rawRow6954 : Integer.Sparse Key := [(key2096, 1), (key2071, 1), (key2071, -2), (key2306, 1), (key2248, 1), (key2306, -2), (key2071, -2), (key2248, 1), (key2071, 1), (key2306, -2), (key2306, 1), (key2096, 1), (key2093, -1), (key2066, -1), (key2066, 1), (key2036, 1), (key2195, -1), (key2155, -1), (key2195, 1), (key2036, 1), (key2304, 1), (key2066, 1), (key2155, -1), (key2066, -1), (key2304, 1), (key2195, 1), (key2195, -1), (key2093, -1), (key2061, 2), (key2061, -1), (key2031, -1), (key2150, 2), (key2150, -1), (key2031, -1), (key2243, -1), (key2150, -1), (key2243, -1), (key2061, -1), (key2150, 2), (key2061, 2)]

theorem rawRowCheck6954 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form7 = rawRow6954 := by decide +kernel

def row6954 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

theorem rowCheck6954 : row6954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6954 := by decide +kernel

theorem rowEval6954 (x : Key → ℝ) : Integer.Sparse.eval row6954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6954, Integer.Sparse.eval_collectBalanced, rawRowCheck6954]

def rawRow6955 : Integer.Sparse Key := [(key2248, 1), (key2306, 1), (key2306, -2), (key2071, 1), (key2096, 1), (key2071, -2), (key2306, -2), (key2096, 1), (key2306, 1), (key2071, -2), (key2071, 1), (key2248, 1), (key2155, -1), (key2195, -1), (key2195, 1), (key2304, 1), (key2066, -1), (key2093, -1), (key2066, 1), (key2304, 1), (key2036, 1), (key2195, 1), (key2093, -1), (key2195, -1), (key2036, 1), (key2066, 1), (key2066, -1), (key2155, -1), (key2150, 2), (key2150, -1), (key2243, -1), (key2061, 2), (key2061, -1), (key2243, -1), (key2031, -1), (key2061, -1), (key2031, -1), (key2150, -1), (key2061, 2), (key2150, 2)]

theorem rawRowCheck6955 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form7 = rawRow6955 := by decide +kernel

def row6955 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

theorem rowCheck6955 : row6955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6955 := by decide +kernel

theorem rowEval6955 (x : Key → ℝ) : Integer.Sparse.eval row6955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6955, Integer.Sparse.eval_collectBalanced, rawRowCheck6955]

def rawRow6956 : Integer.Sparse Key := [(key2306, 1), (key2248, 1), (key2306, -2), (key2096, 1), (key2071, 1), (key2306, -2), (key2071, -2), (key2306, 1), (key2096, 1), (key2071, -2), (key2248, 1), (key2071, 1), (key2195, -1), (key2155, -1), (key2304, 1), (key2195, 1), (key2093, -1), (key2066, -1), (key2304, 1), (key2066, 1), (key2195, 1), (key2036, 1), (key2195, -1), (key2093, -1), (key2066, 1), (key2036, 1), (key2155, -1), (key2066, -1), (key2150, 2), (key2243, -1), (key2150, -1), (key2061, 2), (key2243, -1), (key2061, -1), (key2061, -1), (key2031, -1), (key2150, -1), (key2031, -1), (key2150, 2), (key2061, 2)]

theorem rawRowCheck6956 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form7 = rawRow6956 := by decide +kernel

def row6956 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

theorem rowCheck6956 : row6956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6956 := by decide +kernel

theorem rowEval6956 (x : Key → ℝ) : Integer.Sparse.eval row6956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6956, Integer.Sparse.eval_collectBalanced, rawRowCheck6956]

def rawRow6957 : Integer.Sparse Key := [(key2306, 1), (key2306, 1), (key2248, -2), (key2306, 1), (key2306, 1), (key2096, -2), (key2096, -2), (key2071, 1), (key2071, 1), (key2248, -2), (key2071, 1), (key2071, 1), (key2304, -1), (key2304, -1), (key2155, 1), (key2155, 1), (key2304, -1), (key2304, -1), (key2093, 1), (key2093, 1), (key2093, 1), (key2093, 1), (key2036, -1), (key2036, -1), (key2155, 1), (key2155, 1), (key2036, -1), (key2036, -1), (key2243, 2), (key2150, -1), (key2150, -1), (key2243, 2), (key2061, -1), (key2061, -1), (key2150, -1), (key2150, -1), (key2061, -1), (key2061, -1), (key2031, 2), (key2031, 2)]

theorem rawRowCheck6957 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form7 = rawRow6957 := by decide +kernel

def row6957 : Integer.Sparse Key := [(key2031, 4), (key2036, -4), (key2061, -4), (key2071, 4), (key2093, 4), (key2096, -4), (key2150, -4), (key2155, 4), (key2243, 4), (key2248, -4), (key2304, -4), (key2306, 4)]

theorem rowCheck6957 : row6957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6957 := by decide +kernel

theorem rowEval6957 (x : Key → ℝ) : Integer.Sparse.eval row6957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6957, Integer.Sparse.eval_collectBalanced, rawRowCheck6957]

def rawRow6958 : Integer.Sparse Key := [(key2035, -2), (key2035, 1), (key2038, 1), (key2065, -2), (key2065, 1), (key2073, 1), (key2081, 1), (key2083, 1), (key2081, 1), (key2088, 1), (key2083, -2), (key2088, -2), (key2065, 2), (key2065, -1), (key2073, -1), (key2154, 2), (key2154, -1), (key2170, -1), (key2278, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2282, 2), (key2290, 2), (key2081, -1), (key2083, -1), (key2083, 1), (key2088, 1), (key2178, -1), (key2180, -1), (key2178, 1), (key2190, 1), (key2278, 1), (key2290, 1), (key2282, -1), (key2290, -1), (key2329, 1), (key2331, 1), (key2331, -1), (key2334, -1)]

theorem rawRowCheck6958 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form8 = rawRow6958 := by decide +kernel

def row6958 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6958 : row6958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6958 := by decide +kernel

theorem rowEval6958 (x : Key → ℝ) : Integer.Sparse.eval row6958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6958, Integer.Sparse.eval_collectBalanced, rawRowCheck6958]

def rawRow6959 : Integer.Sparse Key := [(key2035, -2), (key2038, 1), (key2035, 1), (key2065, -2), (key2073, 1), (key2065, 1), (key2083, 1), (key2081, 1), (key2088, 1), (key2081, 1), (key2088, -2), (key2083, -2), (key2065, 2), (key2073, -1), (key2065, -1), (key2154, 2), (key2170, -1), (key2154, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2278, -1), (key2290, 2), (key2282, 2), (key2083, -1), (key2081, -1), (key2088, 1), (key2083, 1), (key2180, -1), (key2178, -1), (key2190, 1), (key2178, 1), (key2290, 1), (key2278, 1), (key2290, -1), (key2282, -1), (key2331, 1), (key2329, 1), (key2334, -1), (key2331, -1)]

theorem rawRowCheck6959 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form8 = rawRow6959 := by decide +kernel

def row6959 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6959 : row6959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6959 := by decide +kernel

theorem rowEval6959 (x : Key → ℝ) : Integer.Sparse.eval row6959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6959, Integer.Sparse.eval_collectBalanced, rawRowCheck6959]

def rawRow6960 : Integer.Sparse Key := [(key2038, -2), (key2035, 1), (key2035, 1), (key2073, -2), (key2065, 1), (key2065, 1), (key2088, 1), (key2088, 1), (key2083, 1), (key2083, 1), (key2081, -2), (key2081, -2), (key2073, 2), (key2065, -1), (key2065, -1), (key2170, 2), (key2154, -1), (key2154, -1), (key2290, -1), (key2290, -1), (key2282, -1), (key2282, -1), (key2278, 2), (key2278, 2), (key2088, -1), (key2088, -1), (key2081, 1), (key2081, 1), (key2190, -1), (key2190, -1), (key2180, 1), (key2180, 1), (key2282, 1), (key2282, 1), (key2278, -1), (key2278, -1), (key2334, 1), (key2334, 1), (key2329, -1), (key2329, -1)]

theorem rawRowCheck6960 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form8 = rawRow6960 := by decide +kernel

def row6960 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

theorem rowCheck6960 : row6960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6960 := by decide +kernel

theorem rowEval6960 (x : Key → ℝ) : Integer.Sparse.eval row6960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6960, Integer.Sparse.eval_collectBalanced, rawRowCheck6960]

def rawRow6961 : Integer.Sparse Key := [(key2065, -2), (key2081, 1), (key2083, 1), (key2035, -2), (key2081, 1), (key2088, 1), (key2035, 1), (key2038, 1), (key2065, 1), (key2073, 1), (key2083, -2), (key2088, -2), (key2154, 2), (key2278, -1), (key2282, -1), (key2065, 2), (key2278, -1), (key2290, -1), (key2065, -1), (key2073, -1), (key2154, -1), (key2170, -1), (key2282, 2), (key2290, 2), (key2178, -1), (key2180, -1), (key2329, 1), (key2331, 1), (key2081, -1), (key2083, -1), (key2278, 1), (key2290, 1), (key2178, 1), (key2190, 1), (key2331, -1), (key2334, -1), (key2083, 1), (key2088, 1), (key2282, -1), (key2290, -1)]

theorem rawRowCheck6961 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form8 = rawRow6961 := by decide +kernel

def row6961 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6961 : row6961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6961 := by decide +kernel

theorem rowEval6961 (x : Key → ℝ) : Integer.Sparse.eval row6961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6961, Integer.Sparse.eval_collectBalanced, rawRowCheck6961]

def rawRow6962 : Integer.Sparse Key := [(key2065, -2), (key2083, 1), (key2081, 1), (key2035, -2), (key2088, 1), (key2081, 1), (key2038, 1), (key2035, 1), (key2073, 1), (key2065, 1), (key2088, -2), (key2083, -2), (key2154, 2), (key2282, -1), (key2278, -1), (key2065, 2), (key2290, -1), (key2278, -1), (key2073, -1), (key2065, -1), (key2170, -1), (key2154, -1), (key2290, 2), (key2282, 2), (key2180, -1), (key2178, -1), (key2331, 1), (key2329, 1), (key2083, -1), (key2081, -1), (key2290, 1), (key2278, 1), (key2190, 1), (key2178, 1), (key2334, -1), (key2331, -1), (key2088, 1), (key2083, 1), (key2290, -1), (key2282, -1)]

theorem rawRowCheck6962 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form8 = rawRow6962 := by decide +kernel

def row6962 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6962 : row6962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6962 := by decide +kernel

theorem rowEval6962 (x : Key → ℝ) : Integer.Sparse.eval row6962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6962, Integer.Sparse.eval_collectBalanced, rawRowCheck6962]

def rawRow6963 : Integer.Sparse Key := [(key2081, -2), (key2065, 1), (key2083, 1), (key2081, -2), (key2035, 1), (key2088, 1), (key2065, 1), (key2083, 1), (key2035, 1), (key2088, 1), (key2038, -2), (key2073, -2), (key2278, 2), (key2154, -1), (key2282, -1), (key2278, 2), (key2065, -1), (key2290, -1), (key2154, -1), (key2282, -1), (key2065, -1), (key2290, -1), (key2073, 2), (key2170, 2), (key2278, -1), (key2329, -1), (key2180, 1), (key2282, 1), (key2278, -1), (key2329, -1), (key2081, 1), (key2334, 1), (key2081, 1), (key2334, 1), (key2088, -1), (key2190, -1), (key2180, 1), (key2282, 1), (key2088, -1), (key2190, -1)]

theorem rawRowCheck6963 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form8 = rawRow6963 := by decide +kernel

def row6963 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

theorem rowCheck6963 : row6963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6963 := by decide +kernel

theorem rowEval6963 (x : Key → ℝ) : Integer.Sparse.eval row6963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6963, Integer.Sparse.eval_collectBalanced, rawRowCheck6963]

def rawRow6964 : Integer.Sparse Key := [(key2081, -2), (key2083, 1), (key2065, 1), (key2081, -2), (key2088, 1), (key2035, 1), (key2083, 1), (key2065, 1), (key2088, 1), (key2035, 1), (key2073, -2), (key2038, -2), (key2278, 2), (key2282, -1), (key2154, -1), (key2278, 2), (key2290, -1), (key2065, -1), (key2282, -1), (key2154, -1), (key2290, -1), (key2065, -1), (key2170, 2), (key2073, 2), (key2329, -1), (key2278, -1), (key2282, 1), (key2180, 1), (key2329, -1), (key2278, -1), (key2334, 1), (key2081, 1), (key2334, 1), (key2081, 1), (key2190, -1), (key2088, -1), (key2282, 1), (key2180, 1), (key2190, -1), (key2088, -1)]

theorem rawRowCheck6964 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form8 = rawRow6964 := by decide +kernel

def row6964 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

theorem rowCheck6964 : row6964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6964 := by decide +kernel

theorem rowEval6964 (x : Key → ℝ) : Integer.Sparse.eval row6964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6964, Integer.Sparse.eval_collectBalanced, rawRowCheck6964]

def rawRow6965 : Integer.Sparse Key := [(key2083, -2), (key2065, 1), (key2081, 1), (key2088, -2), (key2035, 1), (key2081, 1), (key2073, 1), (key2088, 1), (key2038, 1), (key2083, 1), (key2035, -2), (key2065, -2), (key2282, 2), (key2154, -1), (key2278, -1), (key2290, 2), (key2065, -1), (key2278, -1), (key2170, -1), (key2290, -1), (key2073, -1), (key2282, -1), (key2065, 2), (key2154, 2), (key2282, -1), (key2331, -1), (key2178, 1), (key2278, 1), (key2290, -1), (key2334, -1), (key2083, 1), (key2329, 1), (key2088, 1), (key2331, 1), (key2081, -1), (key2178, -1), (key2190, 1), (key2290, 1), (key2083, -1), (key2180, -1)]

theorem rawRowCheck6965 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form8 = rawRow6965 := by decide +kernel

def row6965 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6965 : row6965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6965 := by decide +kernel

theorem rowEval6965 (x : Key → ℝ) : Integer.Sparse.eval row6965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6965, Integer.Sparse.eval_collectBalanced, rawRowCheck6965]

def rawRow6966 : Integer.Sparse Key := [(key2083, -2), (key2081, 1), (key2065, 1), (key2088, -2), (key2081, 1), (key2035, 1), (key2088, 1), (key2073, 1), (key2083, 1), (key2038, 1), (key2065, -2), (key2035, -2), (key2282, 2), (key2278, -1), (key2154, -1), (key2290, 2), (key2278, -1), (key2065, -1), (key2290, -1), (key2170, -1), (key2282, -1), (key2073, -1), (key2154, 2), (key2065, 2), (key2331, -1), (key2282, -1), (key2278, 1), (key2178, 1), (key2334, -1), (key2290, -1), (key2329, 1), (key2083, 1), (key2331, 1), (key2088, 1), (key2178, -1), (key2081, -1), (key2290, 1), (key2190, 1), (key2180, -1), (key2083, -1)]

theorem rawRowCheck6966 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form8 = rawRow6966 := by decide +kernel

def row6966 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6966 : row6966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6966 := by decide +kernel

theorem rowEval6966 (x : Key → ℝ) : Integer.Sparse.eval row6966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6966, Integer.Sparse.eval_collectBalanced, rawRowCheck6966]

def rawRow6967 : Integer.Sparse Key := [(key2073, -2), (key2088, 1), (key2088, 1), (key2038, -2), (key2083, 1), (key2083, 1), (key2035, 1), (key2035, 1), (key2065, 1), (key2065, 1), (key2081, -2), (key2081, -2), (key2170, 2), (key2290, -1), (key2290, -1), (key2073, 2), (key2282, -1), (key2282, -1), (key2065, -1), (key2065, -1), (key2154, -1), (key2154, -1), (key2278, 2), (key2278, 2), (key2190, -1), (key2190, -1), (key2334, 1), (key2334, 1), (key2088, -1), (key2088, -1), (key2282, 1), (key2282, 1), (key2180, 1), (key2180, 1), (key2329, -1), (key2329, -1), (key2081, 1), (key2081, 1), (key2278, -1), (key2278, -1)]

theorem rawRowCheck6967 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form8 = rawRow6967 := by decide +kernel

def row6967 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

theorem rowCheck6967 : row6967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6967 := by decide +kernel

theorem rowEval6967 (x : Key → ℝ) : Integer.Sparse.eval row6967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6967, Integer.Sparse.eval_collectBalanced, rawRowCheck6967]

def rawRow6968 : Integer.Sparse Key := [(key2088, -2), (key2073, 1), (key2088, 1), (key2083, -2), (key2038, 1), (key2083, 1), (key2065, 1), (key2081, 1), (key2035, 1), (key2081, 1), (key2035, -2), (key2065, -2), (key2290, 2), (key2170, -1), (key2290, -1), (key2282, 2), (key2073, -1), (key2282, -1), (key2154, -1), (key2278, -1), (key2065, -1), (key2278, -1), (key2065, 2), (key2154, 2), (key2290, -1), (key2334, -1), (key2190, 1), (key2290, 1), (key2282, -1), (key2331, -1), (key2088, 1), (key2331, 1), (key2083, 1), (key2329, 1), (key2083, -1), (key2180, -1), (key2178, 1), (key2278, 1), (key2081, -1), (key2178, -1)]

theorem rawRowCheck6968 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form8 = rawRow6968 := by decide +kernel

def row6968 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6968 : row6968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6968 := by decide +kernel

theorem rowEval6968 (x : Key → ℝ) : Integer.Sparse.eval row6968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6968, Integer.Sparse.eval_collectBalanced, rawRowCheck6968]

def rawRow6969 : Integer.Sparse Key := [(key2088, -2), (key2088, 1), (key2073, 1), (key2083, -2), (key2083, 1), (key2038, 1), (key2081, 1), (key2065, 1), (key2081, 1), (key2035, 1), (key2065, -2), (key2035, -2), (key2290, 2), (key2290, -1), (key2170, -1), (key2282, 2), (key2282, -1), (key2073, -1), (key2278, -1), (key2154, -1), (key2278, -1), (key2065, -1), (key2154, 2), (key2065, 2), (key2334, -1), (key2290, -1), (key2290, 1), (key2190, 1), (key2331, -1), (key2282, -1), (key2331, 1), (key2088, 1), (key2329, 1), (key2083, 1), (key2180, -1), (key2083, -1), (key2278, 1), (key2178, 1), (key2178, -1), (key2081, -1)]

theorem rawRowCheck6969 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form8 = rawRow6969 := by decide +kernel

def row6969 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6969 : row6969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6969 := by decide +kernel

theorem rowEval6969 (x : Key → ℝ) : Integer.Sparse.eval row6969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6969, Integer.Sparse.eval_collectBalanced, rawRowCheck6969]

def rawRow6970 : Integer.Sparse Key := [(key2154, -2), (key2178, 1), (key2180, 1), (key2154, -2), (key2278, 1), (key2282, 1), (key2178, 1), (key2180, 1), (key2278, 1), (key2282, 1), (key2329, -2), (key2331, -2), (key2035, 2), (key2081, -1), (key2088, -1), (key2035, 2), (key2178, -1), (key2190, -1), (key2081, -1), (key2088, -1), (key2178, -1), (key2190, -1), (key2331, 2), (key2334, 2), (key2035, -1), (key2038, -1), (key2083, 1), (key2088, 1), (key2035, -1), (key2038, -1), (key2154, 1), (key2170, 1), (key2154, 1), (key2170, 1), (key2282, -1), (key2290, -1), (key2083, 1), (key2088, 1), (key2282, -1), (key2290, -1)]

theorem rawRowCheck6970 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form8 = rawRow6970 := by decide +kernel

def row6970 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

theorem rowCheck6970 : row6970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6970 := by decide +kernel

theorem rowEval6970 (x : Key → ℝ) : Integer.Sparse.eval row6970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6970, Integer.Sparse.eval_collectBalanced, rawRowCheck6970]

def rawRow6971 : Integer.Sparse Key := [(key2154, -2), (key2180, 1), (key2178, 1), (key2154, -2), (key2282, 1), (key2278, 1), (key2180, 1), (key2178, 1), (key2282, 1), (key2278, 1), (key2331, -2), (key2329, -2), (key2035, 2), (key2088, -1), (key2081, -1), (key2035, 2), (key2190, -1), (key2178, -1), (key2088, -1), (key2081, -1), (key2190, -1), (key2178, -1), (key2334, 2), (key2331, 2), (key2038, -1), (key2035, -1), (key2088, 1), (key2083, 1), (key2038, -1), (key2035, -1), (key2170, 1), (key2154, 1), (key2170, 1), (key2154, 1), (key2290, -1), (key2282, -1), (key2088, 1), (key2083, 1), (key2290, -1), (key2282, -1)]

theorem rawRowCheck6971 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form8 = rawRow6971 := by decide +kernel

def row6971 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

theorem rowCheck6971 : row6971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6971 := by decide +kernel

theorem rowEval6971 (x : Key → ℝ) : Integer.Sparse.eval row6971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6971, Integer.Sparse.eval_collectBalanced, rawRowCheck6971]

def rawRow6972 : Integer.Sparse Key := [(key2178, -2), (key2154, 1), (key2180, 1), (key2278, -2), (key2154, 1), (key2282, 1), (key2278, 1), (key2329, 1), (key2178, 1), (key2331, 1), (key2180, -2), (key2282, -2), (key2081, 2), (key2035, -1), (key2088, -1), (key2178, 2), (key2035, -1), (key2190, -1), (key2178, -1), (key2331, -1), (key2081, -1), (key2334, -1), (key2088, 2), (key2190, 2), (key2065, -1), (key2083, -1), (key2038, 1), (key2073, 1), (key2154, -1), (key2180, -1), (key2035, 1), (key2190, 1), (key2065, 1), (key2290, 1), (key2073, -1), (key2170, -1), (key2180, 1), (key2282, 1), (key2088, -1), (key2190, -1)]

theorem rawRowCheck6972 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form8 = rawRow6972 := by decide +kernel

def row6972 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6972 : row6972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6972 := by decide +kernel

theorem rowEval6972 (x : Key → ℝ) : Integer.Sparse.eval row6972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6972, Integer.Sparse.eval_collectBalanced, rawRowCheck6972]

def rawRow6973 : Integer.Sparse Key := [(key2178, -2), (key2180, 1), (key2154, 1), (key2278, -2), (key2282, 1), (key2154, 1), (key2329, 1), (key2278, 1), (key2331, 1), (key2178, 1), (key2282, -2), (key2180, -2), (key2081, 2), (key2088, -1), (key2035, -1), (key2178, 2), (key2190, -1), (key2035, -1), (key2331, -1), (key2178, -1), (key2334, -1), (key2081, -1), (key2190, 2), (key2088, 2), (key2083, -1), (key2065, -1), (key2073, 1), (key2038, 1), (key2180, -1), (key2154, -1), (key2190, 1), (key2035, 1), (key2290, 1), (key2065, 1), (key2170, -1), (key2073, -1), (key2282, 1), (key2180, 1), (key2190, -1), (key2088, -1)]

theorem rawRowCheck6973 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form8 = rawRow6973 := by decide +kernel

def row6973 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6973 : row6973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6973 := by decide +kernel

theorem rowEval6973 (x : Key → ℝ) : Integer.Sparse.eval row6973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6973, Integer.Sparse.eval_collectBalanced, rawRowCheck6973]

def rawRow6974 : Integer.Sparse Key := [(key2180, -2), (key2154, 1), (key2178, 1), (key2282, -2), (key2154, 1), (key2278, 1), (key2282, 1), (key2331, 1), (key2180, 1), (key2329, 1), (key2178, -2), (key2278, -2), (key2088, 2), (key2035, -1), (key2081, -1), (key2190, 2), (key2035, -1), (key2178, -1), (key2190, -1), (key2334, -1), (key2088, -1), (key2331, -1), (key2081, 2), (key2178, 2), (key2073, -1), (key2088, -1), (key2035, 1), (key2065, 1), (key2170, -1), (key2190, -1), (key2038, 1), (key2180, 1), (key2073, 1), (key2282, 1), (key2065, -1), (key2154, -1), (key2190, 1), (key2290, 1), (key2083, -1), (key2180, -1)]

theorem rawRowCheck6974 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form8 = rawRow6974 := by decide +kernel

def row6974 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6974 : row6974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6974 := by decide +kernel

theorem rowEval6974 (x : Key → ℝ) : Integer.Sparse.eval row6974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6974, Integer.Sparse.eval_collectBalanced, rawRowCheck6974]

def rawRow6975 : Integer.Sparse Key := [(key2180, -2), (key2178, 1), (key2154, 1), (key2282, -2), (key2278, 1), (key2154, 1), (key2331, 1), (key2282, 1), (key2329, 1), (key2180, 1), (key2278, -2), (key2178, -2), (key2088, 2), (key2081, -1), (key2035, -1), (key2190, 2), (key2178, -1), (key2035, -1), (key2334, -1), (key2190, -1), (key2331, -1), (key2088, -1), (key2178, 2), (key2081, 2), (key2088, -1), (key2073, -1), (key2065, 1), (key2035, 1), (key2190, -1), (key2170, -1), (key2180, 1), (key2038, 1), (key2282, 1), (key2073, 1), (key2154, -1), (key2065, -1), (key2290, 1), (key2190, 1), (key2180, -1), (key2083, -1)]

theorem rawRowCheck6975 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form8 = rawRow6975 := by decide +kernel

def row6975 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6975 : row6975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6975 := by decide +kernel

theorem rowEval6975 (x : Key → ℝ) : Integer.Sparse.eval row6975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6975, Integer.Sparse.eval_collectBalanced, rawRowCheck6975]

def rawRow6976 : Integer.Sparse Key := [(key2278, -2), (key2278, 1), (key2329, 1), (key2178, -2), (key2178, 1), (key2331, 1), (key2154, 1), (key2180, 1), (key2154, 1), (key2282, 1), (key2180, -2), (key2282, -2), (key2178, 2), (key2178, -1), (key2331, -1), (key2081, 2), (key2081, -1), (key2334, -1), (key2035, -1), (key2088, -1), (key2035, -1), (key2190, -1), (key2088, 2), (key2190, 2), (key2154, -1), (key2180, -1), (key2180, 1), (key2282, 1), (key2065, -1), (key2083, -1), (key2065, 1), (key2290, 1), (key2035, 1), (key2190, 1), (key2088, -1), (key2190, -1), (key2038, 1), (key2073, 1), (key2073, -1), (key2170, -1)]

theorem rawRowCheck6976 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form8 = rawRow6976 := by decide +kernel

def row6976 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6976 : row6976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6976 := by decide +kernel

theorem rowEval6976 (x : Key → ℝ) : Integer.Sparse.eval row6976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6976, Integer.Sparse.eval_collectBalanced, rawRowCheck6976]

def rawRow6977 : Integer.Sparse Key := [(key2278, -2), (key2329, 1), (key2278, 1), (key2178, -2), (key2331, 1), (key2178, 1), (key2180, 1), (key2154, 1), (key2282, 1), (key2154, 1), (key2282, -2), (key2180, -2), (key2178, 2), (key2331, -1), (key2178, -1), (key2081, 2), (key2334, -1), (key2081, -1), (key2088, -1), (key2035, -1), (key2190, -1), (key2035, -1), (key2190, 2), (key2088, 2), (key2180, -1), (key2154, -1), (key2282, 1), (key2180, 1), (key2083, -1), (key2065, -1), (key2290, 1), (key2065, 1), (key2190, 1), (key2035, 1), (key2190, -1), (key2088, -1), (key2073, 1), (key2038, 1), (key2170, -1), (key2073, -1)]

theorem rawRowCheck6977 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form8 = rawRow6977 := by decide +kernel

def row6977 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6977 : row6977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6977 := by decide +kernel

theorem rowEval6977 (x : Key → ℝ) : Integer.Sparse.eval row6977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6977, Integer.Sparse.eval_collectBalanced, rawRowCheck6977]

def rawRow6978 : Integer.Sparse Key := [(key2329, -2), (key2278, 1), (key2278, 1), (key2331, -2), (key2178, 1), (key2178, 1), (key2282, 1), (key2282, 1), (key2180, 1), (key2180, 1), (key2154, -2), (key2154, -2), (key2331, 2), (key2178, -1), (key2178, -1), (key2334, 2), (key2081, -1), (key2081, -1), (key2190, -1), (key2190, -1), (key2088, -1), (key2088, -1), (key2035, 2), (key2035, 2), (key2282, -1), (key2282, -1), (key2154, 1), (key2154, 1), (key2290, -1), (key2290, -1), (key2083, 1), (key2083, 1), (key2088, 1), (key2088, 1), (key2035, -1), (key2035, -1), (key2170, 1), (key2170, 1), (key2038, -1), (key2038, -1)]

theorem rawRowCheck6978 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form8 = rawRow6978 := by decide +kernel

def row6978 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

theorem rowCheck6978 : row6978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6978 := by decide +kernel

theorem rowEval6978 (x : Key → ℝ) : Integer.Sparse.eval row6978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6978, Integer.Sparse.eval_collectBalanced, rawRowCheck6978]

def rawRow6979 : Integer.Sparse Key := [(key2282, -2), (key2282, 1), (key2331, 1), (key2180, -2), (key2180, 1), (key2329, 1), (key2154, 1), (key2178, 1), (key2154, 1), (key2278, 1), (key2178, -2), (key2278, -2), (key2190, 2), (key2190, -1), (key2334, -1), (key2088, 2), (key2088, -1), (key2331, -1), (key2035, -1), (key2081, -1), (key2035, -1), (key2178, -1), (key2081, 2), (key2178, 2), (key2170, -1), (key2190, -1), (key2190, 1), (key2290, 1), (key2073, -1), (key2088, -1), (key2073, 1), (key2282, 1), (key2038, 1), (key2180, 1), (key2083, -1), (key2180, -1), (key2035, 1), (key2065, 1), (key2065, -1), (key2154, -1)]

theorem rawRowCheck6979 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form8 = rawRow6979 := by decide +kernel

def row6979 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6979 : row6979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6979 := by decide +kernel

theorem rowEval6979 (x : Key → ℝ) : Integer.Sparse.eval row6979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6979, Integer.Sparse.eval_collectBalanced, rawRowCheck6979]

def rawRow6980 : Integer.Sparse Key := [(key2282, -2), (key2331, 1), (key2282, 1), (key2180, -2), (key2329, 1), (key2180, 1), (key2178, 1), (key2154, 1), (key2278, 1), (key2154, 1), (key2278, -2), (key2178, -2), (key2190, 2), (key2334, -1), (key2190, -1), (key2088, 2), (key2331, -1), (key2088, -1), (key2081, -1), (key2035, -1), (key2178, -1), (key2035, -1), (key2178, 2), (key2081, 2), (key2190, -1), (key2170, -1), (key2290, 1), (key2190, 1), (key2088, -1), (key2073, -1), (key2282, 1), (key2073, 1), (key2180, 1), (key2038, 1), (key2180, -1), (key2083, -1), (key2065, 1), (key2035, 1), (key2154, -1), (key2065, -1)]

theorem rawRowCheck6980 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form8 = rawRow6980 := by decide +kernel

def row6980 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

theorem rowCheck6980 : row6980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6980 := by decide +kernel

theorem rowEval6980 (x : Key → ℝ) : Integer.Sparse.eval row6980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6980, Integer.Sparse.eval_collectBalanced, rawRowCheck6980]

def rawRow6981 : Integer.Sparse Key := [(key2331, -2), (key2282, 1), (key2282, 1), (key2329, -2), (key2180, 1), (key2180, 1), (key2278, 1), (key2278, 1), (key2178, 1), (key2178, 1), (key2154, -2), (key2154, -2), (key2334, 2), (key2190, -1), (key2190, -1), (key2331, 2), (key2088, -1), (key2088, -1), (key2178, -1), (key2178, -1), (key2081, -1), (key2081, -1), (key2035, 2), (key2035, 2), (key2290, -1), (key2290, -1), (key2170, 1), (key2170, 1), (key2282, -1), (key2282, -1), (key2088, 1), (key2088, 1), (key2083, 1), (key2083, 1), (key2038, -1), (key2038, -1), (key2154, 1), (key2154, 1), (key2035, -1), (key2035, -1)]

theorem rawRowCheck6981 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form8 = rawRow6981 := by decide +kernel

def row6981 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

theorem rowCheck6981 : row6981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6981 := by decide +kernel

theorem rowEval6981 (x : Key → ℝ) : Integer.Sparse.eval row6981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6981, Integer.Sparse.eval_collectBalanced, rawRowCheck6981]

def rawRow6982 : Integer.Sparse Key := [(key2170, -2), (key2190, 1), (key2190, 1), (key2170, -2), (key2290, 1), (key2290, 1), (key2190, 1), (key2190, 1), (key2290, 1), (key2290, 1), (key2334, -2), (key2334, -2), (key2038, 2), (key2083, -1), (key2083, -1), (key2038, 2), (key2180, -1), (key2180, -1), (key2083, -1), (key2083, -1), (key2180, -1), (key2180, -1), (key2329, 2), (key2329, 2), (key2035, -1), (key2035, -1), (key2081, 1), (key2081, 1), (key2035, -1), (key2035, -1), (key2154, 1), (key2154, 1), (key2154, 1), (key2154, 1), (key2278, -1), (key2278, -1), (key2081, 1), (key2081, 1), (key2278, -1), (key2278, -1)]

theorem rawRowCheck6982 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form8 = rawRow6982 := by decide +kernel

def row6982 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2081, 4), (key2083, -4), (key2154, 4), (key2170, -4), (key2180, -4), (key2190, 4), (key2278, -4), (key2290, 4), (key2329, 4), (key2334, -4)]

theorem rowCheck6982 : row6982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6982 := by decide +kernel

theorem rowEval6982 (x : Key → ℝ) : Integer.Sparse.eval row6982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6982, Integer.Sparse.eval_collectBalanced, rawRowCheck6982]

def rawRow6983 : Integer.Sparse Key := [(key2190, -2), (key2170, 1), (key2190, 1), (key2290, -2), (key2170, 1), (key2290, 1), (key2290, 1), (key2334, 1), (key2190, 1), (key2334, 1), (key2190, -2), (key2290, -2), (key2083, 2), (key2038, -1), (key2083, -1), (key2180, 2), (key2038, -1), (key2180, -1), (key2180, -1), (key2329, -1), (key2083, -1), (key2329, -1), (key2083, 2), (key2180, 2), (key2065, -1), (key2081, -1), (key2035, 1), (key2065, 1), (key2154, -1), (key2178, -1), (key2035, 1), (key2178, 1), (key2065, 1), (key2278, 1), (key2065, -1), (key2154, -1), (key2178, 1), (key2278, 1), (key2081, -1), (key2178, -1)]

theorem rawRowCheck6983 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form8 = rawRow6983 := by decide +kernel

def row6983 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

theorem rowCheck6983 : row6983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6983 := by decide +kernel

theorem rowEval6983 (x : Key → ℝ) : Integer.Sparse.eval row6983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6983, Integer.Sparse.eval_collectBalanced, rawRowCheck6983]

def rawRow6984 : Integer.Sparse Key := [(key2190, -2), (key2190, 1), (key2170, 1), (key2290, -2), (key2290, 1), (key2170, 1), (key2334, 1), (key2290, 1), (key2334, 1), (key2190, 1), (key2290, -2), (key2190, -2), (key2083, 2), (key2083, -1), (key2038, -1), (key2180, 2), (key2180, -1), (key2038, -1), (key2329, -1), (key2180, -1), (key2329, -1), (key2083, -1), (key2180, 2), (key2083, 2), (key2081, -1), (key2065, -1), (key2065, 1), (key2035, 1), (key2178, -1), (key2154, -1), (key2178, 1), (key2035, 1), (key2278, 1), (key2065, 1), (key2154, -1), (key2065, -1), (key2278, 1), (key2178, 1), (key2178, -1), (key2081, -1)]

theorem rawRowCheck6984 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form8 = rawRow6984 := by decide +kernel

def row6984 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

theorem rowCheck6984 : row6984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6984 := by decide +kernel

theorem rowEval6984 (x : Key → ℝ) : Integer.Sparse.eval row6984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6984, Integer.Sparse.eval_collectBalanced, rawRowCheck6984]

def rawRow6985 : Integer.Sparse Key := [(key2290, -2), (key2290, 1), (key2334, 1), (key2190, -2), (key2190, 1), (key2334, 1), (key2170, 1), (key2190, 1), (key2170, 1), (key2290, 1), (key2190, -2), (key2290, -2), (key2180, 2), (key2180, -1), (key2329, -1), (key2083, 2), (key2083, -1), (key2329, -1), (key2038, -1), (key2083, -1), (key2038, -1), (key2180, -1), (key2083, 2), (key2180, 2), (key2154, -1), (key2178, -1), (key2178, 1), (key2278, 1), (key2065, -1), (key2081, -1), (key2065, 1), (key2278, 1), (key2035, 1), (key2178, 1), (key2081, -1), (key2178, -1), (key2035, 1), (key2065, 1), (key2065, -1), (key2154, -1)]

theorem rawRowCheck6985 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form8 = rawRow6985 := by decide +kernel

def row6985 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

theorem rowCheck6985 : row6985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6985 := by decide +kernel

theorem rowEval6985 (x : Key → ℝ) : Integer.Sparse.eval row6985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6985, Integer.Sparse.eval_collectBalanced, rawRowCheck6985]

def rawRow6986 : Integer.Sparse Key := [(key2290, -2), (key2334, 1), (key2290, 1), (key2190, -2), (key2334, 1), (key2190, 1), (key2190, 1), (key2170, 1), (key2290, 1), (key2170, 1), (key2290, -2), (key2190, -2), (key2180, 2), (key2329, -1), (key2180, -1), (key2083, 2), (key2329, -1), (key2083, -1), (key2083, -1), (key2038, -1), (key2180, -1), (key2038, -1), (key2180, 2), (key2083, 2), (key2178, -1), (key2154, -1), (key2278, 1), (key2178, 1), (key2081, -1), (key2065, -1), (key2278, 1), (key2065, 1), (key2178, 1), (key2035, 1), (key2178, -1), (key2081, -1), (key2065, 1), (key2035, 1), (key2154, -1), (key2065, -1)]

theorem rawRowCheck6986 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form8 = rawRow6986 := by decide +kernel

def row6986 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

theorem rowCheck6986 : row6986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6986 := by decide +kernel

theorem rowEval6986 (x : Key → ℝ) : Integer.Sparse.eval row6986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6986, Integer.Sparse.eval_collectBalanced, rawRowCheck6986]

def rawRow6987 : Integer.Sparse Key := [(key2334, -2), (key2290, 1), (key2290, 1), (key2334, -2), (key2190, 1), (key2190, 1), (key2290, 1), (key2290, 1), (key2190, 1), (key2190, 1), (key2170, -2), (key2170, -2), (key2329, 2), (key2180, -1), (key2180, -1), (key2329, 2), (key2083, -1), (key2083, -1), (key2180, -1), (key2180, -1), (key2083, -1), (key2083, -1), (key2038, 2), (key2038, 2), (key2278, -1), (key2278, -1), (key2154, 1), (key2154, 1), (key2278, -1), (key2278, -1), (key2081, 1), (key2081, 1), (key2081, 1), (key2081, 1), (key2035, -1), (key2035, -1), (key2154, 1), (key2154, 1), (key2035, -1), (key2035, -1)]

theorem rawRowCheck6987 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form8 = rawRow6987 := by decide +kernel

def row6987 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2081, 4), (key2083, -4), (key2154, 4), (key2170, -4), (key2180, -4), (key2190, 4), (key2278, -4), (key2290, 4), (key2329, 4), (key2334, -4)]

theorem rowCheck6987 : row6987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6987 := by decide +kernel

theorem rowEval6987 (x : Key → ℝ) : Integer.Sparse.eval row6987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6987, Integer.Sparse.eval_collectBalanced, rawRowCheck6987]

def rawRow6988 : Integer.Sparse Key := [(key781, 1), (key784, 1), (key784, -2), (key806, 1), (key809, 1), (key806, -2), (key814, -2), (key809, 1), (key814, 1), (key822, -2), (key822, 1), (key827, 1), (key806, -2), (key809, -2), (key806, 1), (key814, 1), (key809, 1), (key814, 1), (key875, 1), (key879, 1), (key879, -2), (key906, 1), (key910, 1), (key910, -2), (key822, 4), (key822, -2), (key827, -2), (key906, -2), (key910, -2), (key910, 4)]

theorem rawRowCheck6988 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form9 = rawRow6988 := by decide +kernel

def row6988 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

theorem rowCheck6988 : row6988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6988 := by decide +kernel

theorem rowEval6988 (x : Key → ℝ) : Integer.Sparse.eval row6988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck6988, Integer.Sparse.eval_collectBalanced, rawRowCheck6988]

def rawRow6989 : Integer.Sparse Key := [(key784, 1), (key781, 1), (key784, -2), (key809, 1), (key806, 1), (key814, -2), (key806, -2), (key814, 1), (key809, 1), (key822, -2), (key827, 1), (key822, 1), (key809, -2), (key806, -2), (key814, 1), (key806, 1), (key814, 1), (key809, 1), (key879, 1), (key875, 1), (key879, -2), (key910, 1), (key906, 1), (key910, -2), (key822, 4), (key827, -2), (key822, -2), (key910, -2), (key906, -2), (key910, 4)]

theorem rawRowCheck6989 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form9 = rawRow6989 := by decide +kernel

def row6989 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

theorem rowCheck6989 : row6989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6989 := by decide +kernel

theorem rowEval6989 (x : Key → ℝ) : Integer.Sparse.eval row6989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck6989, Integer.Sparse.eval_collectBalanced, rawRowCheck6989]

def rawRow6990 : Integer.Sparse Key := [(key784, 1), (key784, 1), (key781, -2), (key814, 1), (key814, 1), (key809, -2), (key809, -2), (key806, 1), (key806, 1), (key827, -2), (key822, 1), (key822, 1), (key814, -2), (key814, -2), (key809, 1), (key809, 1), (key806, 1), (key806, 1), (key879, 1), (key879, 1), (key875, -2), (key910, 1), (key910, 1), (key906, -2), (key827, 4), (key822, -2), (key822, -2), (key910, -2), (key910, -2), (key906, 4)]

theorem rawRowCheck6990 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form9 = rawRow6990 := by decide +kernel

def row6990 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

theorem rowCheck6990 : row6990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6990 := by decide +kernel

theorem rowEval6990 (x : Key → ℝ) : Integer.Sparse.eval row6990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck6990, Integer.Sparse.eval_collectBalanced, rawRowCheck6990]

def rawRow6991 : Integer.Sparse Key := [(key806, 1), (key809, 1), (key814, -2), (key781, 1), (key784, 1), (key806, -2), (key814, -2), (key822, 1), (key827, 1), (key784, -2), (key809, 1), (key814, 1), (key806, -2), (key809, -2), (key875, 1), (key879, 1), (key906, 1), (key910, 1), (key806, 1), (key814, 1), (key910, -2), (key809, 1), (key814, 1), (key879, -2), (key822, 4), (key906, -2), (key910, -2), (key822, -2), (key827, -2), (key910, 4)]

theorem rawRowCheck6991 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form9 = rawRow6991 := by decide +kernel

def row6991 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, -1), (key822, 3), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

theorem rowCheck6991 : row6991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6991 := by decide +kernel

theorem rowEval6991 (x : Key → ℝ) : Integer.Sparse.eval row6991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck6991, Integer.Sparse.eval_collectBalanced, rawRowCheck6991]

def rawRow6992 : Integer.Sparse Key := [(key809, 1), (key806, 1), (key814, -2), (key784, 1), (key781, 1), (key814, -2), (key806, -2), (key827, 1), (key822, 1), (key784, -2), (key814, 1), (key809, 1), (key809, -2), (key806, -2), (key879, 1), (key875, 1), (key910, 1), (key906, 1), (key814, 1), (key806, 1), (key910, -2), (key814, 1), (key809, 1), (key879, -2), (key822, 4), (key910, -2), (key906, -2), (key827, -2), (key822, -2), (key910, 4)]

theorem rawRowCheck6992 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form9 = rawRow6992 := by decide +kernel

def row6992 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, -1), (key822, 3), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

theorem rowCheck6992 : row6992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6992 := by decide +kernel

theorem rowEval6992 (x : Key → ℝ) : Integer.Sparse.eval row6992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck6992, Integer.Sparse.eval_collectBalanced, rawRowCheck6992]

def rawRow6993 : Integer.Sparse Key := [(key806, 1), (key814, 1), (key809, -2), (key806, 1), (key814, 1), (key781, -2), (key827, -2), (key784, 1), (key814, 1), (key809, -2), (key784, 1), (key814, 1), (key875, -2), (key906, -2), (key806, 1), (key910, 1), (key809, 1), (key879, 1), (key806, 1), (key910, 1), (key814, -2), (key809, 1), (key879, 1), (key814, -2), (key906, 4), (key822, -2), (key910, -2), (key822, -2), (key910, -2), (key827, 4)]

theorem rawRowCheck6993 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form9 = rawRow6993 := by decide +kernel

def row6993 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key822, -4), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

theorem rowCheck6993 : row6993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6993 := by decide +kernel

theorem rowEval6993 (x : Key → ℝ) : Integer.Sparse.eval row6993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck6993, Integer.Sparse.eval_collectBalanced, rawRowCheck6993]

def rawRow6994 : Integer.Sparse Key := [(key814, 1), (key806, 1), (key809, -2), (key814, 1), (key806, 1), (key827, -2), (key781, -2), (key814, 1), (key784, 1), (key809, -2), (key814, 1), (key784, 1), (key906, -2), (key875, -2), (key910, 1), (key806, 1), (key879, 1), (key809, 1), (key910, 1), (key806, 1), (key814, -2), (key879, 1), (key809, 1), (key814, -2), (key906, 4), (key910, -2), (key822, -2), (key910, -2), (key822, -2), (key827, 4)]

theorem rawRowCheck6994 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form9 = rawRow6994 := by decide +kernel

def row6994 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key822, -4), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

theorem rowCheck6994 : row6994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6994 := by decide +kernel

theorem rowEval6994 (x : Key → ℝ) : Integer.Sparse.eval row6994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck6994, Integer.Sparse.eval_collectBalanced, rawRowCheck6994]

def rawRow6995 : Integer.Sparse Key := [(key809, 1), (key814, 1), (key806, -2), (key822, 1), (key827, 1), (key784, -2), (key814, -2), (key781, 1), (key806, 1), (key814, -2), (key784, 1), (key809, 1), (key879, -2), (key910, -2), (key809, 1), (key906, 1), (key806, 1), (key875, 1), (key814, 1), (key910, 1), (key806, -2), (key814, 1), (key879, 1), (key809, -2), (key910, 4), (key822, -2), (key906, -2), (key827, -2), (key910, -2), (key822, 4)]

theorem rawRowCheck6995 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form9 = rawRow6995 := by decide +kernel

def row6995 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, -1), (key822, 3), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

theorem rowCheck6995 : row6995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6995 := by decide +kernel

theorem rowEval6995 (x : Key → ℝ) : Integer.Sparse.eval row6995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck6995, Integer.Sparse.eval_collectBalanced, rawRowCheck6995]

def rawRow6996 : Integer.Sparse Key := [(key814, 1), (key809, 1), (key806, -2), (key827, 1), (key822, 1), (key814, -2), (key784, -2), (key806, 1), (key781, 1), (key814, -2), (key809, 1), (key784, 1), (key910, -2), (key879, -2), (key906, 1), (key809, 1), (key875, 1), (key806, 1), (key910, 1), (key814, 1), (key806, -2), (key879, 1), (key814, 1), (key809, -2), (key910, 4), (key906, -2), (key822, -2), (key910, -2), (key827, -2), (key822, 4)]

theorem rawRowCheck6996 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form9 = rawRow6996 := by decide +kernel

def row6996 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, -1), (key822, 3), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

theorem rowCheck6996 : row6996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6996 := by decide +kernel

theorem rowEval6996 (x : Key → ℝ) : Integer.Sparse.eval row6996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck6996, Integer.Sparse.eval_collectBalanced, rawRowCheck6996]

def rawRow6997 : Integer.Sparse Key := [(key822, 1), (key822, 1), (key827, -2), (key784, 1), (key784, 1), (key809, -2), (key809, -2), (key814, 1), (key814, 1), (key781, -2), (key806, 1), (key806, 1), (key814, -2), (key814, -2), (key879, 1), (key879, 1), (key910, 1), (key910, 1), (key809, 1), (key809, 1), (key906, -2), (key806, 1), (key806, 1), (key875, -2), (key827, 4), (key910, -2), (key910, -2), (key822, -2), (key822, -2), (key906, 4)]

theorem rawRowCheck6997 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form9 = rawRow6997 := by decide +kernel

def row6997 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

theorem rowCheck6997 : row6997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6997 := by decide +kernel

theorem rowEval6997 (x : Key → ℝ) : Integer.Sparse.eval row6997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck6997, Integer.Sparse.eval_collectBalanced, rawRowCheck6997]

def rawRow6998 : Integer.Sparse Key := [(key822, 1), (key827, 1), (key822, -2), (key809, 1), (key814, 1), (key784, -2), (key814, -2), (key784, 1), (key809, 1), (key806, -2), (key781, 1), (key806, 1), (key879, -2), (key910, -2), (key814, 1), (key910, 1), (key814, 1), (key879, 1), (key809, 1), (key906, 1), (key809, -2), (key806, 1), (key875, 1), (key806, -2), (key910, 4), (key827, -2), (key910, -2), (key822, -2), (key906, -2), (key822, 4)]

theorem rawRowCheck6998 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form9 = rawRow6998 := by decide +kernel

def row6998 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

theorem rowCheck6998 : row6998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6998 := by decide +kernel

theorem rowEval6998 (x : Key → ℝ) : Integer.Sparse.eval row6998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck6998, Integer.Sparse.eval_collectBalanced, rawRowCheck6998]

def rawRow6999 : Integer.Sparse Key := [(key827, 1), (key822, 1), (key822, -2), (key814, 1), (key809, 1), (key814, -2), (key784, -2), (key809, 1), (key784, 1), (key806, -2), (key806, 1), (key781, 1), (key910, -2), (key879, -2), (key910, 1), (key814, 1), (key879, 1), (key814, 1), (key906, 1), (key809, 1), (key809, -2), (key875, 1), (key806, 1), (key806, -2), (key910, 4), (key910, -2), (key827, -2), (key906, -2), (key822, -2), (key822, 4)]

theorem rawRowCheck6999 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form9 = rawRow6999 := by decide +kernel

def row6999 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

theorem rowCheck6999 : row6999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6999 := by decide +kernel

theorem rowEval6999 (x : Key → ℝ) : Integer.Sparse.eval row6999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck6999, Integer.Sparse.eval_collectBalanced, rawRowCheck6999]

def rawRow7000 : Integer.Sparse Key := [(key806, 1), (key809, 1), (key814, -2), (key806, 1), (key809, 1), (key875, -2), (key906, -2), (key879, 1), (key910, 1), (key814, -2), (key879, 1), (key910, 1), (key781, -2), (key784, -2), (key806, 1), (key814, 1), (key822, 1), (key827, 1), (key806, 1), (key814, 1), (key910, -2), (key822, 1), (key827, 1), (key910, -2), (key784, 4), (key809, -2), (key814, -2), (key809, -2), (key814, -2), (key879, 4)]

theorem rawRowCheck7000 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form9 = rawRow7000 := by decide +kernel

def row7000 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -6), (key822, 2), (key827, 2), (key875, -2), (key879, 6), (key906, -2), (key910, -2)]

theorem rowCheck7000 : row7000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7000 := by decide +kernel

theorem rowEval7000 (x : Key → ℝ) : Integer.Sparse.eval row7000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7000, Integer.Sparse.eval_collectBalanced, rawRowCheck7000]

def rawRow7001 : Integer.Sparse Key := [(key809, 1), (key806, 1), (key814, -2), (key809, 1), (key806, 1), (key906, -2), (key875, -2), (key910, 1), (key879, 1), (key814, -2), (key910, 1), (key879, 1), (key784, -2), (key781, -2), (key814, 1), (key806, 1), (key827, 1), (key822, 1), (key814, 1), (key806, 1), (key910, -2), (key827, 1), (key822, 1), (key910, -2), (key784, 4), (key814, -2), (key809, -2), (key814, -2), (key809, -2), (key879, 4)]

theorem rawRowCheck7001 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form9 = rawRow7001 := by decide +kernel

def row7001 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -6), (key822, 2), (key827, 2), (key875, -2), (key879, 6), (key906, -2), (key910, -2)]

theorem rowCheck7001 : row7001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7001 := by decide +kernel

theorem rowEval7001 (x : Key → ℝ) : Integer.Sparse.eval row7001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7001, Integer.Sparse.eval_collectBalanced, rawRowCheck7001]

def rawRow7002 : Integer.Sparse Key := [(key806, 1), (key814, 1), (key809, -2), (key875, 1), (key879, 1), (key806, -2), (key910, -2), (key809, 1), (key906, 1), (key879, -2), (key814, 1), (key910, 1), (key806, -2), (key814, -2), (key781, 1), (key827, 1), (key784, 1), (key814, 1), (key806, 1), (key910, 1), (key814, -2), (key822, 1), (key910, 1), (key827, -2), (key809, 4), (key784, -2), (key814, -2), (key809, -2), (key879, -2), (key814, 4)]

theorem rawRowCheck7002 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form9 = rawRow7002 := by decide +kernel

def row7002 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

theorem rowCheck7002 : row7002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7002 := by decide +kernel

theorem rowEval7002 (x : Key → ℝ) : Integer.Sparse.eval row7002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7002, Integer.Sparse.eval_collectBalanced, rawRowCheck7002]

def rawRow7003 : Integer.Sparse Key := [(key814, 1), (key806, 1), (key809, -2), (key879, 1), (key875, 1), (key910, -2), (key806, -2), (key906, 1), (key809, 1), (key879, -2), (key910, 1), (key814, 1), (key814, -2), (key806, -2), (key827, 1), (key781, 1), (key814, 1), (key784, 1), (key910, 1), (key806, 1), (key814, -2), (key910, 1), (key822, 1), (key827, -2), (key809, 4), (key814, -2), (key784, -2), (key879, -2), (key809, -2), (key814, 4)]

theorem rawRowCheck7003 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form9 = rawRow7003 := by decide +kernel

def row7003 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

theorem rowCheck7003 : row7003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7003 := by decide +kernel

theorem rowEval7003 (x : Key → ℝ) : Integer.Sparse.eval row7003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7003, Integer.Sparse.eval_collectBalanced, rawRowCheck7003]

def rawRow7004 : Integer.Sparse Key := [(key809, 1), (key814, 1), (key806, -2), (key906, 1), (key910, 1), (key809, -2), (key879, -2), (key806, 1), (key875, 1), (key910, -2), (key814, 1), (key879, 1), (key822, -2), (key827, -2), (key784, 1), (key814, 1), (key781, 1), (key806, 1), (key814, 1), (key910, 1), (key806, -2), (key827, 1), (key910, 1), (key822, -2), (key814, 4), (key784, -2), (key809, -2), (key814, -2), (key879, -2), (key809, 4)]

theorem rawRowCheck7004 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form9 = rawRow7004 := by decide +kernel

def row7004 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 6), (key822, -4), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

theorem rowCheck7004 : row7004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7004 := by decide +kernel

theorem rowEval7004 (x : Key → ℝ) : Integer.Sparse.eval row7004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7004, Integer.Sparse.eval_collectBalanced, rawRowCheck7004]

def rawRow7005 : Integer.Sparse Key := [(key814, 1), (key809, 1), (key806, -2), (key910, 1), (key906, 1), (key879, -2), (key809, -2), (key875, 1), (key806, 1), (key910, -2), (key879, 1), (key814, 1), (key827, -2), (key822, -2), (key814, 1), (key784, 1), (key806, 1), (key781, 1), (key910, 1), (key814, 1), (key806, -2), (key910, 1), (key827, 1), (key822, -2), (key814, 4), (key809, -2), (key784, -2), (key879, -2), (key814, -2), (key809, 4)]

theorem rawRowCheck7005 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form9 = rawRow7005 := by decide +kernel

def row7005 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 6), (key822, -4), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

theorem rowCheck7005 : row7005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7005 := by decide +kernel

theorem rowEval7005 (x : Key → ℝ) : Integer.Sparse.eval row7005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7005, Integer.Sparse.eval_collectBalanced, rawRowCheck7005]

def rawRow7006 : Integer.Sparse Key := [(key875, 1), (key879, 1), (key879, -2), (key806, 1), (key814, 1), (key806, -2), (key910, -2), (key814, 1), (key910, 1), (key809, -2), (key809, 1), (key906, 1), (key806, -2), (key814, -2), (key806, 1), (key910, 1), (key814, 1), (key910, 1), (key781, 1), (key827, 1), (key827, -2), (key784, 1), (key814, 1), (key814, -2), (key809, 4), (key809, -2), (key879, -2), (key784, -2), (key814, -2), (key814, 4)]

theorem rawRowCheck7006 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form9 = rawRow7006 := by decide +kernel

def row7006 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 2), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

theorem rowCheck7006 : row7006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7006 := by decide +kernel

theorem rowEval7006 (x : Key → ℝ) : Integer.Sparse.eval row7006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7006, Integer.Sparse.eval_collectBalanced, rawRowCheck7006]

def rawRow7007 : Integer.Sparse Key := [(key879, 1), (key875, 1), (key879, -2), (key814, 1), (key806, 1), (key910, -2), (key806, -2), (key910, 1), (key814, 1), (key809, -2), (key906, 1), (key809, 1), (key814, -2), (key806, -2), (key910, 1), (key806, 1), (key910, 1), (key814, 1), (key827, 1), (key781, 1), (key827, -2), (key814, 1), (key784, 1), (key814, -2), (key809, 4), (key879, -2), (key809, -2), (key814, -2), (key784, -2), (key814, 4)]

theorem rawRowCheck7007 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form9 = rawRow7007 := by decide +kernel

def row7007 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 2), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

theorem rowCheck7007 : row7007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7007 := by decide +kernel

theorem rowEval7007 (x : Key → ℝ) : Integer.Sparse.eval row7007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7007, Integer.Sparse.eval_collectBalanced, rawRowCheck7007]

def rawRow7008 : Integer.Sparse Key := [(key879, 1), (key879, 1), (key875, -2), (key910, 1), (key910, 1), (key814, -2), (key814, -2), (key806, 1), (key806, 1), (key906, -2), (key809, 1), (key809, 1), (key910, -2), (key910, -2), (key814, 1), (key814, 1), (key806, 1), (key806, 1), (key827, 1), (key827, 1), (key781, -2), (key814, 1), (key814, 1), (key784, -2), (key879, 4), (key809, -2), (key809, -2), (key814, -2), (key814, -2), (key784, 4)]

theorem rawRowCheck7008 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form9 = rawRow7008 := by decide +kernel

def row7008 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -4), (key827, 2), (key875, -2), (key879, 6), (key906, -2), (key910, -2)]

theorem rowCheck7008 : row7008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7008 := by decide +kernel

theorem rowEval7008 (x : Key → ℝ) : Integer.Sparse.eval row7008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7008, Integer.Sparse.eval_collectBalanced, rawRowCheck7008]

def rawRow7009 : Integer.Sparse Key := [(key906, 1), (key910, 1), (key910, -2), (key809, 1), (key814, 1), (key809, -2), (key879, -2), (key814, 1), (key879, 1), (key806, -2), (key806, 1), (key875, 1), (key822, -2), (key827, -2), (key822, 1), (key910, 1), (key827, 1), (key910, 1), (key784, 1), (key814, 1), (key814, -2), (key781, 1), (key806, 1), (key806, -2), (key814, 4), (key814, -2), (key879, -2), (key784, -2), (key809, -2), (key809, 4)]

theorem rawRowCheck7009 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form9 = rawRow7009 := by decide +kernel

def row7009 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 3), (key822, -1), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

theorem rowCheck7009 : row7009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7009 := by decide +kernel

theorem rowEval7009 (x : Key → ℝ) : Integer.Sparse.eval row7009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7009, Integer.Sparse.eval_collectBalanced, rawRowCheck7009]

def rawRow7010 : Integer.Sparse Key := [(key910, 1), (key906, 1), (key910, -2), (key814, 1), (key809, 1), (key879, -2), (key809, -2), (key879, 1), (key814, 1), (key806, -2), (key875, 1), (key806, 1), (key827, -2), (key822, -2), (key910, 1), (key822, 1), (key910, 1), (key827, 1), (key814, 1), (key784, 1), (key814, -2), (key806, 1), (key781, 1), (key806, -2), (key814, 4), (key879, -2), (key814, -2), (key809, -2), (key784, -2), (key809, 4)]

theorem rawRowCheck7010 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form9 = rawRow7010 := by decide +kernel

def row7010 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 3), (key822, -1), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

theorem rowCheck7010 : row7010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7010 := by decide +kernel

theorem rowEval7010 (x : Key → ℝ) : Integer.Sparse.eval row7010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7010, Integer.Sparse.eval_collectBalanced, rawRowCheck7010]

def rawRow7011 : Integer.Sparse Key := [(key910, 1), (key910, 1), (key906, -2), (key879, 1), (key879, 1), (key814, -2), (key814, -2), (key809, 1), (key809, 1), (key875, -2), (key806, 1), (key806, 1), (key910, -2), (key910, -2), (key827, 1), (key827, 1), (key822, 1), (key822, 1), (key814, 1), (key814, 1), (key784, -2), (key806, 1), (key806, 1), (key781, -2), (key879, 4), (key814, -2), (key814, -2), (key809, -2), (key809, -2), (key784, 4)]

theorem rawRowCheck7011 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form9 = rawRow7011 := by decide +kernel

def row7011 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -6), (key822, 2), (key827, 2), (key875, -2), (key879, 6), (key906, -2), (key910, -2)]

theorem rowCheck7011 : row7011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7011 := by decide +kernel

theorem rowEval7011 (x : Key → ℝ) : Integer.Sparse.eval row7011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7011, Integer.Sparse.eval_collectBalanced, rawRowCheck7011]

def rawRow7012 : Integer.Sparse Key := [(key822, 1), (key822, 1), (key827, -2), (key822, 1), (key822, 1), (key906, -2), (key906, -2), (key910, 1), (key910, 1), (key827, -2), (key910, 1), (key910, 1), (key784, -2), (key784, -2), (key809, 1), (key809, 1), (key814, 1), (key814, 1), (key809, 1), (key809, 1), (key879, -2), (key814, 1), (key814, 1), (key879, -2), (key781, 4), (key806, -2), (key806, -2), (key806, -2), (key806, -2), (key875, 4)]

theorem rawRowCheck7012 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form9 = rawRow7012 := by decide +kernel

def row7012 : Integer.Sparse Key := [(key781, 4), (key784, -4), (key806, -8), (key809, 4), (key814, 4), (key822, 4), (key827, -4), (key875, 4), (key879, -4), (key906, -4), (key910, 4)]

theorem rowCheck7012 : row7012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7012 := by decide +kernel

theorem rowEval7012 (x : Key → ℝ) : Integer.Sparse.eval row7012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7012, Integer.Sparse.eval_collectBalanced, rawRowCheck7012]

def rawRow7013 : Integer.Sparse Key := [(key822, 1), (key827, 1), (key822, -2), (key906, 1), (key910, 1), (key822, -2), (key910, -2), (key822, 1), (key906, 1), (key910, -2), (key827, 1), (key910, 1), (key809, -2), (key814, -2), (key784, 1), (key814, 1), (key784, 1), (key809, 1), (key809, 1), (key879, 1), (key809, -2), (key814, 1), (key879, 1), (key814, -2), (key806, 4), (key781, -2), (key806, -2), (key806, -2), (key875, -2), (key806, 4)]

theorem rawRowCheck7013 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form9 = rawRow7013 := by decide +kernel

def row7013 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

theorem rowCheck7013 : row7013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7013 := by decide +kernel

theorem rowEval7013 (x : Key → ℝ) : Integer.Sparse.eval row7013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7013, Integer.Sparse.eval_collectBalanced, rawRowCheck7013]

def rawRow7014 : Integer.Sparse Key := [(key827, 1), (key822, 1), (key822, -2), (key910, 1), (key906, 1), (key910, -2), (key822, -2), (key906, 1), (key822, 1), (key910, -2), (key910, 1), (key827, 1), (key814, -2), (key809, -2), (key814, 1), (key784, 1), (key809, 1), (key784, 1), (key879, 1), (key809, 1), (key809, -2), (key879, 1), (key814, 1), (key814, -2), (key806, 4), (key806, -2), (key781, -2), (key875, -2), (key806, -2), (key806, 4)]

theorem rawRowCheck7014 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form9 = rawRow7014 := by decide +kernel

def row7014 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

theorem rowCheck7014 : row7014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7014 := by decide +kernel

theorem rowEval7014 (x : Key → ℝ) : Integer.Sparse.eval row7014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7014, Integer.Sparse.eval_collectBalanced, rawRowCheck7014]

def rawRow7015 : Integer.Sparse Key := [(key906, 1), (key910, 1), (key910, -2), (key822, 1), (key827, 1), (key822, -2), (key910, -2), (key827, 1), (key910, 1), (key822, -2), (key822, 1), (key906, 1), (key809, -2), (key814, -2), (key809, 1), (key879, 1), (key814, 1), (key879, 1), (key784, 1), (key814, 1), (key814, -2), (key784, 1), (key809, 1), (key809, -2), (key806, 4), (key806, -2), (key875, -2), (key781, -2), (key806, -2), (key806, 4)]

theorem rawRowCheck7015 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form9 = rawRow7015 := by decide +kernel

def row7015 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

theorem rowCheck7015 : row7015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7015 := by decide +kernel

theorem rowEval7015 (x : Key → ℝ) : Integer.Sparse.eval row7015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7015, Integer.Sparse.eval_collectBalanced, rawRowCheck7015]

def rawRow7016 : Integer.Sparse Key := [(key910, 1), (key906, 1), (key910, -2), (key827, 1), (key822, 1), (key910, -2), (key822, -2), (key910, 1), (key827, 1), (key822, -2), (key906, 1), (key822, 1), (key814, -2), (key809, -2), (key879, 1), (key809, 1), (key879, 1), (key814, 1), (key814, 1), (key784, 1), (key814, -2), (key809, 1), (key784, 1), (key809, -2), (key806, 4), (key875, -2), (key806, -2), (key806, -2), (key781, -2), (key806, 4)]

theorem rawRowCheck7016 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form9 = rawRow7016 := by decide +kernel

def row7016 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

theorem rowCheck7016 : row7016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7016 := by decide +kernel

theorem rowEval7016 (x : Key → ℝ) : Integer.Sparse.eval row7016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7016, Integer.Sparse.eval_collectBalanced, rawRowCheck7016]

def rawRow7017 : Integer.Sparse Key := [(key910, 1), (key910, 1), (key906, -2), (key910, 1), (key910, 1), (key827, -2), (key827, -2), (key822, 1), (key822, 1), (key906, -2), (key822, 1), (key822, 1), (key879, -2), (key879, -2), (key814, 1), (key814, 1), (key809, 1), (key809, 1), (key814, 1), (key814, 1), (key784, -2), (key809, 1), (key809, 1), (key784, -2), (key875, 4), (key806, -2), (key806, -2), (key806, -2), (key806, -2), (key781, 4)]

theorem rawRowCheck7017 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form9 = rawRow7017 := by decide +kernel

def row7017 : Integer.Sparse Key := [(key781, 4), (key784, -4), (key806, -8), (key809, 4), (key814, 4), (key822, 4), (key827, -4), (key875, 4), (key879, -4), (key906, -4), (key910, 4)]

theorem rowCheck7017 : row7017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7017 := by decide +kernel

theorem rowEval7017 (x : Key → ℝ) : Integer.Sparse.eval row7017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7017, Integer.Sparse.eval_collectBalanced, rawRowCheck7017]

def rawRow7018 : Integer.Sparse Key := [(key2080, -1), (key2080, -1), (key2084, 2), (key2080, -1), (key2080, -1), (key2086, 2), (key2086, 2), (key2089, -1), (key2089, -1), (key2084, 2), (key2089, -1), (key2089, -1), (key2177, 1), (key2177, 1), (key2181, -2), (key2177, 1), (key2177, 1), (key2188, -2), (key2188, -2), (key2191, 1), (key2191, 1), (key2181, -2), (key2191, 1), (key2191, 1), (key2280, -1), (key2280, -1), (key2283, 1), (key2283, 1), (key2288, 1), (key2288, 1), (key2291, -1), (key2291, -1), (key2280, -1), (key2280, -1), (key2288, 1), (key2288, 1), (key2283, 1), (key2283, 1), (key2291, -1), (key2291, -1)]

theorem rawRowCheck7018 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form0 = rawRow7018 := by decide +kernel

def row7018 : Integer.Sparse Key := [(key2080, -4), (key2084, 4), (key2086, 4), (key2089, -4), (key2177, 4), (key2181, -4), (key2188, -4), (key2191, 4), (key2280, -4), (key2283, 4), (key2288, 4), (key2291, -4)]

theorem rowCheck7018 : row7018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7018 := by decide +kernel

theorem rowEval7018 (x : Key → ℝ) : Integer.Sparse.eval row7018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7018, Integer.Sparse.eval_collectBalanced, rawRowCheck7018]

def rawRow7019 : Integer.Sparse Key := [(key2080, -1), (key2084, -1), (key2080, 2), (key2086, -1), (key2089, -1), (key2080, 2), (key2089, 2), (key2080, -1), (key2086, -1), (key2089, 2), (key2084, -1), (key2089, -1), (key2177, 1), (key2181, 1), (key2177, -2), (key2188, 1), (key2191, 1), (key2177, -2), (key2191, -2), (key2177, 1), (key2188, 1), (key2191, -2), (key2181, 1), (key2191, 1), (key2277, -1), (key2283, -1), (key2277, 1), (key2280, 1), (key2277, 1), (key2291, 1), (key2277, -1), (key2288, -1), (key2288, -1), (key2296, -1), (key2280, 1), (key2296, 1), (key2291, 1), (key2296, 1), (key2283, -1), (key2296, -1)]

theorem rawRowCheck7019 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form0 = rawRow7019 := by decide +kernel

def row7019 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

theorem rowCheck7019 : row7019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7019 := by decide +kernel

theorem rowEval7019 (x : Key → ℝ) : Integer.Sparse.eval row7019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7019, Integer.Sparse.eval_collectBalanced, rawRowCheck7019]

def rawRow7020 : Integer.Sparse Key := [(key2084, -1), (key2080, -1), (key2080, 2), (key2089, -1), (key2086, -1), (key2089, 2), (key2080, 2), (key2086, -1), (key2080, -1), (key2089, 2), (key2089, -1), (key2084, -1), (key2181, 1), (key2177, 1), (key2177, -2), (key2191, 1), (key2188, 1), (key2191, -2), (key2177, -2), (key2188, 1), (key2177, 1), (key2191, -2), (key2191, 1), (key2181, 1), (key2283, -1), (key2277, -1), (key2280, 1), (key2277, 1), (key2291, 1), (key2277, 1), (key2288, -1), (key2277, -1), (key2296, -1), (key2288, -1), (key2296, 1), (key2280, 1), (key2296, 1), (key2291, 1), (key2296, -1), (key2283, -1)]

theorem rawRowCheck7020 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form0 = rawRow7020 := by decide +kernel

def row7020 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

theorem rowCheck7020 : row7020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7020 := by decide +kernel

theorem rowEval7020 (x : Key → ℝ) : Integer.Sparse.eval row7020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7020, Integer.Sparse.eval_collectBalanced, rawRowCheck7020]

def rawRow7021 : Integer.Sparse Key := [(key2086, -1), (key2089, -1), (key2089, 2), (key2080, -1), (key2084, -1), (key2080, 2), (key2089, 2), (key2084, -1), (key2089, -1), (key2080, 2), (key2080, -1), (key2086, -1), (key2188, 1), (key2191, 1), (key2191, -2), (key2177, 1), (key2181, 1), (key2177, -2), (key2191, -2), (key2181, 1), (key2191, 1), (key2177, -2), (key2177, 1), (key2188, 1), (key2288, -1), (key2296, -1), (key2291, 1), (key2296, 1), (key2280, 1), (key2296, 1), (key2283, -1), (key2296, -1), (key2277, -1), (key2283, -1), (key2277, 1), (key2291, 1), (key2277, 1), (key2280, 1), (key2277, -1), (key2288, -1)]

theorem rawRowCheck7021 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form0 = rawRow7021 := by decide +kernel

def row7021 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

theorem rowCheck7021 : row7021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7021 := by decide +kernel

theorem rowEval7021 (x : Key → ℝ) : Integer.Sparse.eval row7021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7021, Integer.Sparse.eval_collectBalanced, rawRowCheck7021]

def rawRow7022 : Integer.Sparse Key := [(key2089, -1), (key2086, -1), (key2089, 2), (key2084, -1), (key2080, -1), (key2089, 2), (key2080, 2), (key2089, -1), (key2084, -1), (key2080, 2), (key2086, -1), (key2080, -1), (key2191, 1), (key2188, 1), (key2191, -2), (key2181, 1), (key2177, 1), (key2191, -2), (key2177, -2), (key2191, 1), (key2181, 1), (key2177, -2), (key2188, 1), (key2177, 1), (key2296, -1), (key2288, -1), (key2296, 1), (key2291, 1), (key2296, 1), (key2280, 1), (key2296, -1), (key2283, -1), (key2283, -1), (key2277, -1), (key2291, 1), (key2277, 1), (key2280, 1), (key2277, 1), (key2288, -1), (key2277, -1)]

theorem rawRowCheck7022 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form0 = rawRow7022 := by decide +kernel

def row7022 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

theorem rowCheck7022 : row7022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7022 := by decide +kernel

theorem rowEval7022 (x : Key → ℝ) : Integer.Sparse.eval row7022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7022, Integer.Sparse.eval_collectBalanced, rawRowCheck7022]

def rawRow7023 : Integer.Sparse Key := [(key2089, -1), (key2089, -1), (key2086, 2), (key2089, -1), (key2089, -1), (key2084, 2), (key2084, 2), (key2080, -1), (key2080, -1), (key2086, 2), (key2080, -1), (key2080, -1), (key2191, 1), (key2191, 1), (key2188, -2), (key2191, 1), (key2191, 1), (key2181, -2), (key2181, -2), (key2177, 1), (key2177, 1), (key2188, -2), (key2177, 1), (key2177, 1), (key2291, -1), (key2291, -1), (key2288, 1), (key2288, 1), (key2283, 1), (key2283, 1), (key2280, -1), (key2280, -1), (key2291, -1), (key2291, -1), (key2283, 1), (key2283, 1), (key2288, 1), (key2288, 1), (key2280, -1), (key2280, -1)]

theorem rawRowCheck7023 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form0 = rawRow7023 := by decide +kernel

def row7023 : Integer.Sparse Key := [(key2080, -4), (key2084, 4), (key2086, 4), (key2089, -4), (key2177, 4), (key2181, -4), (key2188, -4), (key2191, 4), (key2280, -4), (key2283, 4), (key2288, 4), (key2291, -4)]

theorem rowCheck7023 : row7023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7023 := by decide +kernel

theorem rowEval7023 (x : Key → ℝ) : Integer.Sparse.eval row7023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7023, Integer.Sparse.eval_collectBalanced, rawRowCheck7023]

def rawRow7024 : Integer.Sparse Key := [(key2177, -1), (key2177, -1), (key2181, 2), (key2277, -1), (key2277, -1), (key2280, 2), (key2280, 2), (key2283, -1), (key2283, -1), (key2342, 2), (key2344, -1), (key2344, -1), (key2080, 1), (key2080, 1), (key2084, -2), (key2277, 1), (key2277, 1), (key2288, -2), (key2288, -2), (key2291, 1), (key2291, 1), (key2342, -2), (key2348, 1), (key2348, 1), (key2086, -1), (key2086, -1), (key2089, 1), (key2089, 1), (key2188, 1), (key2188, 1), (key2191, -1), (key2191, -1), (key2280, -1), (key2280, -1), (key2288, 1), (key2288, 1), (key2344, 1), (key2344, 1), (key2348, -1), (key2348, -1)]

theorem rawRowCheck7024 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form0 = rawRow7024 := by decide +kernel

def row7024 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

theorem rowCheck7024 : row7024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7024 := by decide +kernel

theorem rowEval7024 (x : Key → ℝ) : Integer.Sparse.eval row7024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7024, Integer.Sparse.eval_collectBalanced, rawRowCheck7024]

def rawRow7025 : Integer.Sparse Key := [(key2177, -1), (key2181, -1), (key2177, 2), (key2280, -1), (key2283, -1), (key2277, 2), (key2283, 2), (key2277, -1), (key2280, -1), (key2344, 2), (key2342, -1), (key2344, -1), (key2080, 1), (key2084, 1), (key2080, -2), (key2288, 1), (key2291, 1), (key2277, -2), (key2291, -2), (key2277, 1), (key2288, 1), (key2348, -2), (key2342, 1), (key2348, 1), (key2080, -1), (key2089, -1), (key2080, 1), (key2086, 1), (key2177, 1), (key2191, 1), (key2177, -1), (key2188, -1), (key2288, -1), (key2296, -1), (key2280, 1), (key2296, 1), (key2348, 1), (key2350, 1), (key2344, -1), (key2350, -1)]

theorem rawRowCheck7025 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form0 = rawRow7025 := by decide +kernel

def row7025 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7025 : row7025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7025 := by decide +kernel

theorem rowEval7025 (x : Key → ℝ) : Integer.Sparse.eval row7025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7025, Integer.Sparse.eval_collectBalanced, rawRowCheck7025]

def rawRow7026 : Integer.Sparse Key := [(key2181, -1), (key2177, -1), (key2177, 2), (key2283, -1), (key2280, -1), (key2283, 2), (key2277, 2), (key2280, -1), (key2277, -1), (key2344, 2), (key2344, -1), (key2342, -1), (key2084, 1), (key2080, 1), (key2080, -2), (key2291, 1), (key2288, 1), (key2291, -2), (key2277, -2), (key2288, 1), (key2277, 1), (key2348, -2), (key2348, 1), (key2342, 1), (key2089, -1), (key2080, -1), (key2086, 1), (key2080, 1), (key2191, 1), (key2177, 1), (key2188, -1), (key2177, -1), (key2296, -1), (key2288, -1), (key2296, 1), (key2280, 1), (key2350, 1), (key2348, 1), (key2350, -1), (key2344, -1)]

theorem rawRowCheck7026 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form0 = rawRow7026 := by decide +kernel

def row7026 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7026 : row7026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7026 := by decide +kernel

theorem rowEval7026 (x : Key → ℝ) : Integer.Sparse.eval row7026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7026, Integer.Sparse.eval_collectBalanced, rawRowCheck7026]

def rawRow7027 : Integer.Sparse Key := [(key2277, -1), (key2277, -1), (key2342, 2), (key2177, -1), (key2177, -1), (key2280, 2), (key2280, 2), (key2344, -1), (key2344, -1), (key2181, 2), (key2283, -1), (key2283, -1), (key2277, 1), (key2277, 1), (key2342, -2), (key2080, 1), (key2080, 1), (key2288, -2), (key2288, -2), (key2348, 1), (key2348, 1), (key2084, -2), (key2291, 1), (key2291, 1), (key2280, -1), (key2280, -1), (key2344, 1), (key2344, 1), (key2288, 1), (key2288, 1), (key2348, -1), (key2348, -1), (key2086, -1), (key2086, -1), (key2188, 1), (key2188, 1), (key2089, 1), (key2089, 1), (key2191, -1), (key2191, -1)]

theorem rawRowCheck7027 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form0 = rawRow7027 := by decide +kernel

def row7027 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

theorem rowCheck7027 : row7027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7027 := by decide +kernel

theorem rowEval7027 (x : Key → ℝ) : Integer.Sparse.eval row7027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7027, Integer.Sparse.eval_collectBalanced, rawRowCheck7027]

def rawRow7028 : Integer.Sparse Key := [(key2277, -1), (key2342, -1), (key2277, 2), (key2280, -1), (key2344, -1), (key2177, 2), (key2344, 2), (key2177, -1), (key2280, -1), (key2283, 2), (key2181, -1), (key2283, -1), (key2277, 1), (key2342, 1), (key2277, -2), (key2288, 1), (key2348, 1), (key2080, -2), (key2348, -2), (key2080, 1), (key2288, 1), (key2291, -2), (key2084, 1), (key2291, 1), (key2177, -1), (key2344, -1), (key2177, 1), (key2280, 1), (key2080, 1), (key2348, 1), (key2080, -1), (key2288, -1), (key2188, -1), (key2350, -1), (key2086, 1), (key2350, 1), (key2191, 1), (key2296, 1), (key2089, -1), (key2296, -1)]

theorem rawRowCheck7028 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form0 = rawRow7028 := by decide +kernel

def row7028 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7028 : row7028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7028 := by decide +kernel

theorem rowEval7028 (x : Key → ℝ) : Integer.Sparse.eval row7028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7028, Integer.Sparse.eval_collectBalanced, rawRowCheck7028]

def rawRow7029 : Integer.Sparse Key := [(key2342, -1), (key2277, -1), (key2277, 2), (key2344, -1), (key2280, -1), (key2344, 2), (key2177, 2), (key2280, -1), (key2177, -1), (key2283, 2), (key2283, -1), (key2181, -1), (key2342, 1), (key2277, 1), (key2277, -2), (key2348, 1), (key2288, 1), (key2348, -2), (key2080, -2), (key2288, 1), (key2080, 1), (key2291, -2), (key2291, 1), (key2084, 1), (key2344, -1), (key2177, -1), (key2280, 1), (key2177, 1), (key2348, 1), (key2080, 1), (key2288, -1), (key2080, -1), (key2350, -1), (key2188, -1), (key2350, 1), (key2086, 1), (key2296, 1), (key2191, 1), (key2296, -1), (key2089, -1)]

theorem rawRowCheck7029 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form0 = rawRow7029 := by decide +kernel

def row7029 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7029 : row7029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7029 := by decide +kernel

theorem rowEval7029 (x : Key → ℝ) : Integer.Sparse.eval row7029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7029, Integer.Sparse.eval_collectBalanced, rawRowCheck7029]

def rawRow7030 : Integer.Sparse Key := [(key2280, -1), (key2283, -1), (key2344, 2), (key2177, -1), (key2181, -1), (key2277, 2), (key2283, 2), (key2342, -1), (key2344, -1), (key2177, 2), (key2277, -1), (key2280, -1), (key2288, 1), (key2291, 1), (key2348, -2), (key2080, 1), (key2084, 1), (key2277, -2), (key2291, -2), (key2342, 1), (key2348, 1), (key2080, -2), (key2277, 1), (key2288, 1), (key2288, -1), (key2296, -1), (key2348, 1), (key2350, 1), (key2280, 1), (key2296, 1), (key2344, -1), (key2350, -1), (key2080, -1), (key2089, -1), (key2177, 1), (key2191, 1), (key2080, 1), (key2086, 1), (key2177, -1), (key2188, -1)]

theorem rawRowCheck7030 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form0 = rawRow7030 := by decide +kernel

def row7030 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7030 : row7030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7030 := by decide +kernel

theorem rowEval7030 (x : Key → ℝ) : Integer.Sparse.eval row7030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7030, Integer.Sparse.eval_collectBalanced, rawRowCheck7030]

def rawRow7031 : Integer.Sparse Key := [(key2283, -1), (key2280, -1), (key2344, 2), (key2181, -1), (key2177, -1), (key2283, 2), (key2277, 2), (key2344, -1), (key2342, -1), (key2177, 2), (key2280, -1), (key2277, -1), (key2291, 1), (key2288, 1), (key2348, -2), (key2084, 1), (key2080, 1), (key2291, -2), (key2277, -2), (key2348, 1), (key2342, 1), (key2080, -2), (key2288, 1), (key2277, 1), (key2296, -1), (key2288, -1), (key2350, 1), (key2348, 1), (key2296, 1), (key2280, 1), (key2350, -1), (key2344, -1), (key2089, -1), (key2080, -1), (key2191, 1), (key2177, 1), (key2086, 1), (key2080, 1), (key2188, -1), (key2177, -1)]

theorem rawRowCheck7031 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form0 = rawRow7031 := by decide +kernel

def row7031 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7031 : row7031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7031 := by decide +kernel

theorem rowEval7031 (x : Key → ℝ) : Integer.Sparse.eval row7031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7031, Integer.Sparse.eval_collectBalanced, rawRowCheck7031]

def rawRow7032 : Integer.Sparse Key := [(key2280, -1), (key2344, -1), (key2283, 2), (key2277, -1), (key2342, -1), (key2177, 2), (key2344, 2), (key2181, -1), (key2283, -1), (key2277, 2), (key2177, -1), (key2280, -1), (key2288, 1), (key2348, 1), (key2291, -2), (key2277, 1), (key2342, 1), (key2080, -2), (key2348, -2), (key2084, 1), (key2291, 1), (key2277, -2), (key2080, 1), (key2288, 1), (key2188, -1), (key2350, -1), (key2191, 1), (key2296, 1), (key2086, 1), (key2350, 1), (key2089, -1), (key2296, -1), (key2177, -1), (key2344, -1), (key2080, 1), (key2348, 1), (key2177, 1), (key2280, 1), (key2080, -1), (key2288, -1)]

theorem rawRowCheck7032 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form0 = rawRow7032 := by decide +kernel

def row7032 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7032 : row7032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7032 := by decide +kernel

theorem rowEval7032 (x : Key → ℝ) : Integer.Sparse.eval row7032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7032, Integer.Sparse.eval_collectBalanced, rawRowCheck7032]

def rawRow7033 : Integer.Sparse Key := [(key2344, -1), (key2280, -1), (key2283, 2), (key2342, -1), (key2277, -1), (key2344, 2), (key2177, 2), (key2283, -1), (key2181, -1), (key2277, 2), (key2280, -1), (key2177, -1), (key2348, 1), (key2288, 1), (key2291, -2), (key2342, 1), (key2277, 1), (key2348, -2), (key2080, -2), (key2291, 1), (key2084, 1), (key2277, -2), (key2288, 1), (key2080, 1), (key2350, -1), (key2188, -1), (key2296, 1), (key2191, 1), (key2350, 1), (key2086, 1), (key2296, -1), (key2089, -1), (key2344, -1), (key2177, -1), (key2348, 1), (key2080, 1), (key2280, 1), (key2177, 1), (key2288, -1), (key2080, -1)]

theorem rawRowCheck7033 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form0 = rawRow7033 := by decide +kernel

def row7033 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7033 : row7033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7033 := by decide +kernel

theorem rowEval7033 (x : Key → ℝ) : Integer.Sparse.eval row7033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7033, Integer.Sparse.eval_collectBalanced, rawRowCheck7033]

def rawRow7034 : Integer.Sparse Key := [(key2283, -1), (key2344, -1), (key2280, 2), (key2283, -1), (key2344, -1), (key2181, 2), (key2342, 2), (key2177, -1), (key2277, -1), (key2280, 2), (key2177, -1), (key2277, -1), (key2291, 1), (key2348, 1), (key2288, -2), (key2291, 1), (key2348, 1), (key2084, -2), (key2342, -2), (key2080, 1), (key2277, 1), (key2288, -2), (key2080, 1), (key2277, 1), (key2191, -1), (key2348, -1), (key2188, 1), (key2288, 1), (key2089, 1), (key2344, 1), (key2086, -1), (key2280, -1), (key2191, -1), (key2348, -1), (key2089, 1), (key2344, 1), (key2188, 1), (key2288, 1), (key2086, -1), (key2280, -1)]

theorem rawRowCheck7034 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form0 = rawRow7034 := by decide +kernel

def row7034 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

theorem rowCheck7034 : row7034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7034 := by decide +kernel

theorem rowEval7034 (x : Key → ℝ) : Integer.Sparse.eval row7034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7034, Integer.Sparse.eval_collectBalanced, rawRowCheck7034]

def rawRow7035 : Integer.Sparse Key := [(key2344, -1), (key2283, -1), (key2280, 2), (key2344, -1), (key2283, -1), (key2342, 2), (key2181, 2), (key2277, -1), (key2177, -1), (key2280, 2), (key2277, -1), (key2177, -1), (key2348, 1), (key2291, 1), (key2288, -2), (key2348, 1), (key2291, 1), (key2342, -2), (key2084, -2), (key2277, 1), (key2080, 1), (key2288, -2), (key2277, 1), (key2080, 1), (key2348, -1), (key2191, -1), (key2288, 1), (key2188, 1), (key2344, 1), (key2089, 1), (key2280, -1), (key2086, -1), (key2348, -1), (key2191, -1), (key2344, 1), (key2089, 1), (key2288, 1), (key2188, 1), (key2280, -1), (key2086, -1)]

theorem rawRowCheck7035 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form0 = rawRow7035 := by decide +kernel

def row7035 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

theorem rowCheck7035 : row7035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7035 := by decide +kernel

theorem rowEval7035 (x : Key → ℝ) : Integer.Sparse.eval row7035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7035, Integer.Sparse.eval_collectBalanced, rawRowCheck7035]

def rawRow7036 : Integer.Sparse Key := [(key2188, -1), (key2191, -1), (key2191, 2), (key2288, -1), (key2291, -1), (key2288, 2), (key2296, 2), (key2291, -1), (key2296, -1), (key2348, 2), (key2348, -1), (key2350, -1), (key2086, 1), (key2089, 1), (key2089, -2), (key2280, 1), (key2283, 1), (key2280, -2), (key2296, -2), (key2283, 1), (key2296, 1), (key2344, -2), (key2344, 1), (key2350, 1), (key2080, -1), (key2089, -1), (key2084, 1), (key2089, 1), (key2177, 1), (key2191, 1), (key2181, -1), (key2191, -1), (key2277, -1), (key2283, -1), (key2277, 1), (key2291, 1), (key2342, 1), (key2344, 1), (key2342, -1), (key2348, -1)]

theorem rawRowCheck7036 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form0 = rawRow7036 := by decide +kernel

def row7036 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7036 : row7036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7036 := by decide +kernel

theorem rowEval7036 (x : Key → ℝ) : Integer.Sparse.eval row7036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7036, Integer.Sparse.eval_collectBalanced, rawRowCheck7036]

def rawRow7037 : Integer.Sparse Key := [(key2191, -1), (key2188, -1), (key2191, 2), (key2291, -1), (key2288, -1), (key2296, 2), (key2288, 2), (key2296, -1), (key2291, -1), (key2348, 2), (key2350, -1), (key2348, -1), (key2089, 1), (key2086, 1), (key2089, -2), (key2283, 1), (key2280, 1), (key2296, -2), (key2280, -2), (key2296, 1), (key2283, 1), (key2344, -2), (key2350, 1), (key2344, 1), (key2089, -1), (key2080, -1), (key2089, 1), (key2084, 1), (key2191, 1), (key2177, 1), (key2191, -1), (key2181, -1), (key2283, -1), (key2277, -1), (key2291, 1), (key2277, 1), (key2344, 1), (key2342, 1), (key2348, -1), (key2342, -1)]

theorem rawRowCheck7037 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form0 = rawRow7037 := by decide +kernel

def row7037 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7037 : row7037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7037 := by decide +kernel

theorem rowEval7037 (x : Key → ℝ) : Integer.Sparse.eval row7037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7037, Integer.Sparse.eval_collectBalanced, rawRowCheck7037]

def rawRow7038 : Integer.Sparse Key := [(key2191, -1), (key2191, -1), (key2188, 2), (key2296, -1), (key2296, -1), (key2291, 2), (key2291, 2), (key2288, -1), (key2288, -1), (key2350, 2), (key2348, -1), (key2348, -1), (key2089, 1), (key2089, 1), (key2086, -2), (key2296, 1), (key2296, 1), (key2283, -2), (key2283, -2), (key2280, 1), (key2280, 1), (key2350, -2), (key2344, 1), (key2344, 1), (key2084, -1), (key2084, -1), (key2080, 1), (key2080, 1), (key2181, 1), (key2181, 1), (key2177, -1), (key2177, -1), (key2291, -1), (key2291, -1), (key2283, 1), (key2283, 1), (key2348, 1), (key2348, 1), (key2344, -1), (key2344, -1)]

theorem rawRowCheck7038 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form0 = rawRow7038 := by decide +kernel

def row7038 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

theorem rowCheck7038 : row7038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7038 := by decide +kernel

theorem rowEval7038 (x : Key → ℝ) : Integer.Sparse.eval row7038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7038, Integer.Sparse.eval_collectBalanced, rawRowCheck7038]

def rawRow7039 : Integer.Sparse Key := [(key2288, -1), (key2291, -1), (key2348, 2), (key2188, -1), (key2191, -1), (key2288, 2), (key2296, 2), (key2348, -1), (key2350, -1), (key2191, 2), (key2291, -1), (key2296, -1), (key2280, 1), (key2283, 1), (key2344, -2), (key2086, 1), (key2089, 1), (key2280, -2), (key2296, -2), (key2344, 1), (key2350, 1), (key2089, -2), (key2283, 1), (key2296, 1), (key2277, -1), (key2283, -1), (key2342, 1), (key2344, 1), (key2277, 1), (key2291, 1), (key2342, -1), (key2348, -1), (key2080, -1), (key2089, -1), (key2177, 1), (key2191, 1), (key2084, 1), (key2089, 1), (key2181, -1), (key2191, -1)]

theorem rawRowCheck7039 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form0 = rawRow7039 := by decide +kernel

def row7039 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7039 : row7039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7039 := by decide +kernel

theorem rowEval7039 (x : Key → ℝ) : Integer.Sparse.eval row7039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7039, Integer.Sparse.eval_collectBalanced, rawRowCheck7039]

end MUB6.Certificate.GramRows

end OAI
