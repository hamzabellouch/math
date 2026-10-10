import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9856 : Integer.Sparse Key := [(key1127, 6), (key1111, 6), (key1155, 6), (key1111, 6), (key1193, -6), (key1006, -6), (key1193, -6), (key1041, -6)]

theorem rawRowCheck9856 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form14 = rawRow9856 := by decide +kernel

def row9856 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

theorem rowCheck9856 : row9856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9856 := by decide +kernel

theorem rowEval9856 (x : Key → ℝ) : Integer.Sparse.eval row9856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9856, Integer.Sparse.eval_collectBalanced, rawRowCheck9856]

def rawRow9857 : Integer.Sparse Key := [(key1111, 6), (key1155, 6), (key1127, 6), (key1111, 6), (key1193, -6), (key1041, -6), (key1006, -6), (key1193, -6)]

theorem rawRowCheck9857 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form14 = rawRow9857 := by decide +kernel

def row9857 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

theorem rowCheck9857 : row9857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9857 := by decide +kernel

theorem rowEval9857 (x : Key → ℝ) : Integer.Sparse.eval row9857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9857, Integer.Sparse.eval_collectBalanced, rawRowCheck9857]

def rawRow9858 : Integer.Sparse Key := [(key1155, 6), (key1111, 6), (key1127, 6), (key1111, 6), (key1193, -6), (key1041, -6), (key1193, -6), (key1006, -6)]

theorem rawRowCheck9858 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form14 = rawRow9858 := by decide +kernel

def row9858 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

theorem rowCheck9858 : row9858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9858 := by decide +kernel

theorem rowEval9858 (x : Key → ℝ) : Integer.Sparse.eval row9858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9858, Integer.Sparse.eval_collectBalanced, rawRowCheck9858]

def rawRow9859 : Integer.Sparse Key := [(key1127, 6), (key1155, 6), (key1111, 6), (key1111, 6), (key1193, -6), (key1193, -6), (key1006, -6), (key1041, -6)]

theorem rawRowCheck9859 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form14 = rawRow9859 := by decide +kernel

def row9859 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

theorem rowCheck9859 : row9859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9859 := by decide +kernel

theorem rowEval9859 (x : Key → ℝ) : Integer.Sparse.eval row9859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9859, Integer.Sparse.eval_collectBalanced, rawRowCheck9859]

def rawRow9860 : Integer.Sparse Key := [(key1155, 6), (key1127, 6), (key1111, 6), (key1111, 6), (key1193, -6), (key1193, -6), (key1041, -6), (key1006, -6)]

theorem rawRowCheck9860 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form14 = rawRow9860 := by decide +kernel

def row9860 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

theorem rowCheck9860 : row9860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9860 := by decide +kernel

theorem rowEval9860 (x : Key → ℝ) : Integer.Sparse.eval row9860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9860, Integer.Sparse.eval_collectBalanced, rawRowCheck9860]

def rawRow9861 : Integer.Sparse Key := [(key2770, -6), (key2770, -6), (key2773, -6), (key2932, -6), (key2591, 2), (key2591, 2), (key2594, 2), (key2847, 2), (key2847, 2), (key2878, 2), (key2878, 2), (key2881, 2), (key2881, 2), (key2969, 2), (key2990, 2), (key2990, 2)]

theorem rawRowCheck9861 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form15 = rawRow9861 := by decide +kernel

def row9861 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

theorem rowCheck9861 : row9861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9861 := by decide +kernel

theorem rowEval9861 (x : Key → ℝ) : Integer.Sparse.eval row9861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9861, Integer.Sparse.eval_collectBalanced, rawRowCheck9861]

def rawRow9862 : Integer.Sparse Key := [(key2770, -6), (key2773, -6), (key2770, -6), (key2932, -6), (key2591, 2), (key2594, 2), (key2591, 2), (key2878, 2), (key2881, 2), (key2847, 2), (key2881, 2), (key2847, 2), (key2878, 2), (key2990, 2), (key2969, 2), (key2990, 2)]

theorem rawRowCheck9862 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form15 = rawRow9862 := by decide +kernel

def row9862 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

theorem rowCheck9862 : row9862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9862 := by decide +kernel

theorem rowEval9862 (x : Key → ℝ) : Integer.Sparse.eval row9862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9862, Integer.Sparse.eval_collectBalanced, rawRowCheck9862]

def rawRow9863 : Integer.Sparse Key := [(key2773, -6), (key2770, -6), (key2770, -6), (key2932, -6), (key2594, 2), (key2591, 2), (key2591, 2), (key2881, 2), (key2878, 2), (key2881, 2), (key2847, 2), (key2878, 2), (key2847, 2), (key2990, 2), (key2990, 2), (key2969, 2)]

theorem rawRowCheck9863 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form15 = rawRow9863 := by decide +kernel

def row9863 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

theorem rowCheck9863 : row9863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9863 := by decide +kernel

theorem rowEval9863 (x : Key → ℝ) : Integer.Sparse.eval row9863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9863, Integer.Sparse.eval_collectBalanced, rawRowCheck9863]

def rawRow9864 : Integer.Sparse Key := [(key2770, -6), (key2770, -6), (key2932, -6), (key2773, -6), (key2847, 2), (key2847, 2), (key2969, 2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key2990, 2), (key2990, 2), (key2594, 2), (key2881, 2), (key2881, 2)]

theorem rawRowCheck9864 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form15 = rawRow9864 := by decide +kernel

def row9864 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

theorem rowCheck9864 : row9864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9864 := by decide +kernel

theorem rowEval9864 (x : Key → ℝ) : Integer.Sparse.eval row9864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9864, Integer.Sparse.eval_collectBalanced, rawRowCheck9864]

def rawRow9865 : Integer.Sparse Key := [(key2770, -6), (key2932, -6), (key2770, -6), (key2773, -6), (key2847, 2), (key2969, 2), (key2847, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2881, 2), (key2594, 2), (key2881, 2)]

theorem rawRowCheck9865 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form15 = rawRow9865 := by decide +kernel

def row9865 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

theorem rowCheck9865 : row9865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9865 := by decide +kernel

theorem rowEval9865 (x : Key → ℝ) : Integer.Sparse.eval row9865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9865, Integer.Sparse.eval_collectBalanced, rawRowCheck9865]

def rawRow9866 : Integer.Sparse Key := [(key2932, -6), (key2770, -6), (key2770, -6), (key2773, -6), (key2969, 2), (key2847, 2), (key2847, 2), (key2990, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2881, 2), (key2881, 2), (key2594, 2)]

theorem rawRowCheck9866 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form15 = rawRow9866 := by decide +kernel

def row9866 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

theorem rowCheck9866 : row9866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9866 := by decide +kernel

theorem rowEval9866 (x : Key → ℝ) : Integer.Sparse.eval row9866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck9866, Integer.Sparse.eval_collectBalanced, rawRowCheck9866]

def rawRow9867 : Integer.Sparse Key := [(key2770, -6), (key2773, -6), (key2932, -6), (key2770, -6), (key2878, 2), (key2881, 2), (key2990, 2), (key2591, 2), (key2594, 2), (key2847, 2), (key2881, 2), (key2969, 2), (key2990, 2), (key2591, 2), (key2847, 2), (key2878, 2)]

theorem rawRowCheck9867 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form15 = rawRow9867 := by decide +kernel

def row9867 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

theorem rowCheck9867 : row9867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9867 := by decide +kernel

theorem rowEval9867 (x : Key → ℝ) : Integer.Sparse.eval row9867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9867, Integer.Sparse.eval_collectBalanced, rawRowCheck9867]

def rawRow9868 : Integer.Sparse Key := [(key2773, -6), (key2770, -6), (key2932, -6), (key2770, -6), (key2881, 2), (key2878, 2), (key2990, 2), (key2594, 2), (key2591, 2), (key2881, 2), (key2847, 2), (key2990, 2), (key2969, 2), (key2591, 2), (key2878, 2), (key2847, 2)]

theorem rawRowCheck9868 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form15 = rawRow9868 := by decide +kernel

def row9868 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

theorem rowCheck9868 : row9868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9868 := by decide +kernel

theorem rowEval9868 (x : Key → ℝ) : Integer.Sparse.eval row9868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9868, Integer.Sparse.eval_collectBalanced, rawRowCheck9868]

def rawRow9869 : Integer.Sparse Key := [(key2770, -6), (key2932, -6), (key2773, -6), (key2770, -6), (key2878, 2), (key2990, 2), (key2881, 2), (key2847, 2), (key2969, 2), (key2591, 2), (key2990, 2), (key2594, 2), (key2881, 2), (key2847, 2), (key2591, 2), (key2878, 2)]

theorem rawRowCheck9869 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form15 = rawRow9869 := by decide +kernel

def row9869 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

theorem rowCheck9869 : row9869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9869 := by decide +kernel

theorem rowEval9869 (x : Key → ℝ) : Integer.Sparse.eval row9869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9869, Integer.Sparse.eval_collectBalanced, rawRowCheck9869]

def rawRow9870 : Integer.Sparse Key := [(key2932, -6), (key2770, -6), (key2773, -6), (key2770, -6), (key2990, 2), (key2878, 2), (key2881, 2), (key2969, 2), (key2847, 2), (key2990, 2), (key2591, 2), (key2881, 2), (key2594, 2), (key2847, 2), (key2878, 2), (key2591, 2)]

theorem rawRowCheck9870 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form15 = rawRow9870 := by decide +kernel

def row9870 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

theorem rowCheck9870 : row9870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9870 := by decide +kernel

theorem rowEval9870 (x : Key → ℝ) : Integer.Sparse.eval row9870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck9870, Integer.Sparse.eval_collectBalanced, rawRowCheck9870]

def rawRow9871 : Integer.Sparse Key := [(key2773, -6), (key2932, -6), (key2770, -6), (key2770, -6), (key2881, 2), (key2990, 2), (key2878, 2), (key2881, 2), (key2990, 2), (key2594, 2), (key2969, 2), (key2591, 2), (key2847, 2), (key2878, 2), (key2591, 2), (key2847, 2)]

theorem rawRowCheck9871 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form15 = rawRow9871 := by decide +kernel

def row9871 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

theorem rowCheck9871 : row9871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9871 := by decide +kernel

theorem rowEval9871 (x : Key → ℝ) : Integer.Sparse.eval row9871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9871, Integer.Sparse.eval_collectBalanced, rawRowCheck9871]

def rawRow9872 : Integer.Sparse Key := [(key2932, -6), (key2773, -6), (key2770, -6), (key2770, -6), (key2990, 2), (key2881, 2), (key2878, 2), (key2990, 2), (key2881, 2), (key2969, 2), (key2594, 2), (key2847, 2), (key2591, 2), (key2878, 2), (key2847, 2), (key2591, 2)]

theorem rawRowCheck9872 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form15 = rawRow9872 := by decide +kernel

def row9872 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

theorem rowCheck9872 : row9872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9872 := by decide +kernel

theorem rowEval9872 (x : Key → ℝ) : Integer.Sparse.eval row9872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck9872, Integer.Sparse.eval_collectBalanced, rawRowCheck9872]

def rawRow9873 : Integer.Sparse Key := [(key2847, -6), (key2847, -6), (key2890, -6), (key2969, -6), (key2591, 2), (key2591, 2), (key2601, 2), (key2770, 2), (key2770, 2), (key2878, 2), (key2878, 2), (key2911, 2), (key2911, 2), (key2932, 2), (key2990, 2), (key2990, 2)]

theorem rawRowCheck9873 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form15 = rawRow9873 := by decide +kernel

def row9873 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

theorem rowCheck9873 : row9873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9873 := by decide +kernel

theorem rowEval9873 (x : Key → ℝ) : Integer.Sparse.eval row9873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9873, Integer.Sparse.eval_collectBalanced, rawRowCheck9873]

def rawRow9874 : Integer.Sparse Key := [(key2847, -6), (key2890, -6), (key2847, -6), (key2969, -6), (key2591, 2), (key2601, 2), (key2591, 2), (key2878, 2), (key2911, 2), (key2770, 2), (key2911, 2), (key2770, 2), (key2878, 2), (key2990, 2), (key2932, 2), (key2990, 2)]

theorem rawRowCheck9874 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form15 = rawRow9874 := by decide +kernel

def row9874 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

theorem rowCheck9874 : row9874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9874 := by decide +kernel

theorem rowEval9874 (x : Key → ℝ) : Integer.Sparse.eval row9874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9874, Integer.Sparse.eval_collectBalanced, rawRowCheck9874]

def rawRow9875 : Integer.Sparse Key := [(key2890, -6), (key2847, -6), (key2847, -6), (key2969, -6), (key2601, 2), (key2591, 2), (key2591, 2), (key2911, 2), (key2878, 2), (key2911, 2), (key2770, 2), (key2878, 2), (key2770, 2), (key2990, 2), (key2990, 2), (key2932, 2)]

theorem rawRowCheck9875 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form15 = rawRow9875 := by decide +kernel

def row9875 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

theorem rowCheck9875 : row9875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9875 := by decide +kernel

theorem rowEval9875 (x : Key → ℝ) : Integer.Sparse.eval row9875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9875, Integer.Sparse.eval_collectBalanced, rawRowCheck9875]

def rawRow9876 : Integer.Sparse Key := [(key2847, -6), (key2847, -6), (key2969, -6), (key2890, -6), (key2770, 2), (key2770, 2), (key2932, 2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key2990, 2), (key2990, 2), (key2601, 2), (key2911, 2), (key2911, 2)]

theorem rawRowCheck9876 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form15 = rawRow9876 := by decide +kernel

def row9876 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

theorem rowCheck9876 : row9876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9876 := by decide +kernel

theorem rowEval9876 (x : Key → ℝ) : Integer.Sparse.eval row9876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9876, Integer.Sparse.eval_collectBalanced, rawRowCheck9876]

def rawRow9877 : Integer.Sparse Key := [(key2847, -6), (key2969, -6), (key2847, -6), (key2890, -6), (key2770, 2), (key2932, 2), (key2770, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2911, 2), (key2601, 2), (key2911, 2)]

theorem rawRowCheck9877 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form15 = rawRow9877 := by decide +kernel

def row9877 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

theorem rowCheck9877 : row9877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9877 := by decide +kernel

theorem rowEval9877 (x : Key → ℝ) : Integer.Sparse.eval row9877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9877, Integer.Sparse.eval_collectBalanced, rawRowCheck9877]

def rawRow9878 : Integer.Sparse Key := [(key2969, -6), (key2847, -6), (key2847, -6), (key2890, -6), (key2932, 2), (key2770, 2), (key2770, 2), (key2990, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2911, 2), (key2911, 2), (key2601, 2)]

theorem rawRowCheck9878 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form15 = rawRow9878 := by decide +kernel

def row9878 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

theorem rowCheck9878 : row9878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9878 := by decide +kernel

theorem rowEval9878 (x : Key → ℝ) : Integer.Sparse.eval row9878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck9878, Integer.Sparse.eval_collectBalanced, rawRowCheck9878]

def rawRow9879 : Integer.Sparse Key := [(key2847, -6), (key2890, -6), (key2969, -6), (key2847, -6), (key2878, 2), (key2911, 2), (key2990, 2), (key2591, 2), (key2601, 2), (key2770, 2), (key2911, 2), (key2932, 2), (key2990, 2), (key2591, 2), (key2770, 2), (key2878, 2)]

theorem rawRowCheck9879 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form15 = rawRow9879 := by decide +kernel

def row9879 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

theorem rowCheck9879 : row9879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9879 := by decide +kernel

theorem rowEval9879 (x : Key → ℝ) : Integer.Sparse.eval row9879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9879, Integer.Sparse.eval_collectBalanced, rawRowCheck9879]

def rawRow9880 : Integer.Sparse Key := [(key2890, -6), (key2847, -6), (key2969, -6), (key2847, -6), (key2911, 2), (key2878, 2), (key2990, 2), (key2601, 2), (key2591, 2), (key2911, 2), (key2770, 2), (key2990, 2), (key2932, 2), (key2591, 2), (key2878, 2), (key2770, 2)]

theorem rawRowCheck9880 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form15 = rawRow9880 := by decide +kernel

def row9880 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

theorem rowCheck9880 : row9880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9880 := by decide +kernel

theorem rowEval9880 (x : Key → ℝ) : Integer.Sparse.eval row9880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9880, Integer.Sparse.eval_collectBalanced, rawRowCheck9880]

def rawRow9881 : Integer.Sparse Key := [(key2847, -6), (key2969, -6), (key2890, -6), (key2847, -6), (key2878, 2), (key2990, 2), (key2911, 2), (key2770, 2), (key2932, 2), (key2591, 2), (key2990, 2), (key2601, 2), (key2911, 2), (key2770, 2), (key2591, 2), (key2878, 2)]

theorem rawRowCheck9881 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form15 = rawRow9881 := by decide +kernel

def row9881 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

theorem rowCheck9881 : row9881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9881 := by decide +kernel

theorem rowEval9881 (x : Key → ℝ) : Integer.Sparse.eval row9881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9881, Integer.Sparse.eval_collectBalanced, rawRowCheck9881]

def rawRow9882 : Integer.Sparse Key := [(key2969, -6), (key2847, -6), (key2890, -6), (key2847, -6), (key2990, 2), (key2878, 2), (key2911, 2), (key2932, 2), (key2770, 2), (key2990, 2), (key2591, 2), (key2911, 2), (key2601, 2), (key2770, 2), (key2878, 2), (key2591, 2)]

theorem rawRowCheck9882 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form15 = rawRow9882 := by decide +kernel

def row9882 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

theorem rowCheck9882 : row9882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9882 := by decide +kernel

theorem rowEval9882 (x : Key → ℝ) : Integer.Sparse.eval row9882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck9882, Integer.Sparse.eval_collectBalanced, rawRowCheck9882]

def rawRow9883 : Integer.Sparse Key := [(key2890, -6), (key2969, -6), (key2847, -6), (key2847, -6), (key2911, 2), (key2990, 2), (key2878, 2), (key2911, 2), (key2990, 2), (key2601, 2), (key2932, 2), (key2591, 2), (key2770, 2), (key2878, 2), (key2591, 2), (key2770, 2)]

theorem rawRowCheck9883 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form15 = rawRow9883 := by decide +kernel

def row9883 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

theorem rowCheck9883 : row9883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9883 := by decide +kernel

theorem rowEval9883 (x : Key → ℝ) : Integer.Sparse.eval row9883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9883, Integer.Sparse.eval_collectBalanced, rawRowCheck9883]

def rawRow9884 : Integer.Sparse Key := [(key2969, -6), (key2890, -6), (key2847, -6), (key2847, -6), (key2990, 2), (key2911, 2), (key2878, 2), (key2990, 2), (key2911, 2), (key2932, 2), (key2601, 2), (key2770, 2), (key2591, 2), (key2878, 2), (key2770, 2), (key2591, 2)]

theorem rawRowCheck9884 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form15 = rawRow9884 := by decide +kernel

def row9884 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

theorem rowCheck9884 : row9884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9884 := by decide +kernel

theorem rowEval9884 (x : Key → ℝ) : Integer.Sparse.eval row9884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck9884, Integer.Sparse.eval_collectBalanced, rawRowCheck9884]

def rawRow9885 : Integer.Sparse Key := [(key2670, -6), (key2785, -6), (key2793, -6), (key2793, -6), (key2615, 6), (key2808, 6), (key2828, 6), (key2828, 6)]

theorem rawRowCheck9885 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form16 = rawRow9885 := by decide +kernel

def row9885 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

theorem rowCheck9885 : row9885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9885 := by decide +kernel

theorem rowEval9885 (x : Key → ℝ) : Integer.Sparse.eval row9885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9885, Integer.Sparse.eval_collectBalanced, rawRowCheck9885]

def rawRow9886 : Integer.Sparse Key := [(key2670, -6), (key2793, -6), (key2785, -6), (key2793, -6), (key2615, 6), (key2828, 6), (key2808, 6), (key2828, 6)]

theorem rawRowCheck9886 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form16 = rawRow9886 := by decide +kernel

def row9886 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

theorem rowCheck9886 : row9886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9886 := by decide +kernel

theorem rowEval9886 (x : Key → ℝ) : Integer.Sparse.eval row9886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9886, Integer.Sparse.eval_collectBalanced, rawRowCheck9886]

def rawRow9887 : Integer.Sparse Key := [(key2670, -6), (key2793, -6), (key2793, -6), (key2785, -6), (key2615, 6), (key2828, 6), (key2828, 6), (key2808, 6)]

theorem rawRowCheck9887 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form16 = rawRow9887 := by decide +kernel

def row9887 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

theorem rowCheck9887 : row9887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9887 := by decide +kernel

theorem rowEval9887 (x : Key → ℝ) : Integer.Sparse.eval row9887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9887, Integer.Sparse.eval_collectBalanced, rawRowCheck9887]

def rawRow9888 : Integer.Sparse Key := [(key2785, -6), (key2670, -6), (key2793, -6), (key2793, -6), (key2808, 6), (key2615, 6), (key2828, 6), (key2828, 6)]

theorem rawRowCheck9888 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form16 = rawRow9888 := by decide +kernel

def row9888 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

theorem rowCheck9888 : row9888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9888 := by decide +kernel

theorem rowEval9888 (x : Key → ℝ) : Integer.Sparse.eval row9888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9888, Integer.Sparse.eval_collectBalanced, rawRowCheck9888]

def rawRow9889 : Integer.Sparse Key := [(key2785, -6), (key2793, -6), (key2670, -6), (key2793, -6), (key2808, 6), (key2828, 6), (key2615, 6), (key2828, 6)]

theorem rawRowCheck9889 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form16 = rawRow9889 := by decide +kernel

def row9889 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

theorem rowCheck9889 : row9889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9889 := by decide +kernel

theorem rowEval9889 (x : Key → ℝ) : Integer.Sparse.eval row9889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9889, Integer.Sparse.eval_collectBalanced, rawRowCheck9889]

def rawRow9890 : Integer.Sparse Key := [(key2785, -6), (key2793, -6), (key2793, -6), (key2670, -6), (key2808, 6), (key2828, 6), (key2828, 6), (key2615, 6)]

theorem rawRowCheck9890 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form16 = rawRow9890 := by decide +kernel

def row9890 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

theorem rowCheck9890 : row9890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9890 := by decide +kernel

theorem rowEval9890 (x : Key → ℝ) : Integer.Sparse.eval row9890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck9890, Integer.Sparse.eval_collectBalanced, rawRowCheck9890]

def rawRow9891 : Integer.Sparse Key := [(key2793, -6), (key2670, -6), (key2785, -6), (key2793, -6), (key2828, 6), (key2615, 6), (key2808, 6), (key2828, 6)]

theorem rawRowCheck9891 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form16 = rawRow9891 := by decide +kernel

def row9891 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

theorem rowCheck9891 : row9891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9891 := by decide +kernel

theorem rowEval9891 (x : Key → ℝ) : Integer.Sparse.eval row9891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9891, Integer.Sparse.eval_collectBalanced, rawRowCheck9891]

def rawRow9892 : Integer.Sparse Key := [(key2793, -6), (key2670, -6), (key2793, -6), (key2785, -6), (key2828, 6), (key2615, 6), (key2828, 6), (key2808, 6)]

theorem rawRowCheck9892 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form16 = rawRow9892 := by decide +kernel

def row9892 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

theorem rowCheck9892 : row9892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9892 := by decide +kernel

theorem rowEval9892 (x : Key → ℝ) : Integer.Sparse.eval row9892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9892, Integer.Sparse.eval_collectBalanced, rawRowCheck9892]

def rawRow9893 : Integer.Sparse Key := [(key2793, -6), (key2785, -6), (key2670, -6), (key2793, -6), (key2828, 6), (key2808, 6), (key2615, 6), (key2828, 6)]

theorem rawRowCheck9893 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form16 = rawRow9893 := by decide +kernel

def row9893 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

theorem rowCheck9893 : row9893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9893 := by decide +kernel

theorem rowEval9893 (x : Key → ℝ) : Integer.Sparse.eval row9893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9893, Integer.Sparse.eval_collectBalanced, rawRowCheck9893]

def rawRow9894 : Integer.Sparse Key := [(key2793, -6), (key2785, -6), (key2793, -6), (key2670, -6), (key2828, 6), (key2808, 6), (key2828, 6), (key2615, 6)]

theorem rawRowCheck9894 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form16 = rawRow9894 := by decide +kernel

def row9894 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

theorem rowCheck9894 : row9894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9894 := by decide +kernel

theorem rowEval9894 (x : Key → ℝ) : Integer.Sparse.eval row9894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck9894, Integer.Sparse.eval_collectBalanced, rawRowCheck9894]

def rawRow9895 : Integer.Sparse Key := [(key2793, -6), (key2793, -6), (key2670, -6), (key2785, -6), (key2828, 6), (key2828, 6), (key2615, 6), (key2808, 6)]

theorem rawRowCheck9895 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form16 = rawRow9895 := by decide +kernel

def row9895 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

theorem rowCheck9895 : row9895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9895 := by decide +kernel

theorem rowEval9895 (x : Key → ℝ) : Integer.Sparse.eval row9895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9895, Integer.Sparse.eval_collectBalanced, rawRowCheck9895]

def rawRow9896 : Integer.Sparse Key := [(key2793, -6), (key2793, -6), (key2785, -6), (key2670, -6), (key2828, 6), (key2828, 6), (key2808, 6), (key2615, 6)]

theorem rawRowCheck9896 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form16 = rawRow9896 := by decide +kernel

def row9896 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

theorem rowCheck9896 : row9896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9896 := by decide +kernel

theorem rowEval9896 (x : Key → ℝ) : Integer.Sparse.eval row9896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck9896, Integer.Sparse.eval_collectBalanced, rawRowCheck9896]

def rawRow9897 : Integer.Sparse Key := [(key2705, -6), (key2808, -6), (key2859, -6), (key2859, -6), (key2631, 6), (key2785, 6), (key2869, 6), (key2869, 6)]

theorem rawRowCheck9897 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form16 = rawRow9897 := by decide +kernel

def row9897 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

theorem rowCheck9897 : row9897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9897 := by decide +kernel

theorem rowEval9897 (x : Key → ℝ) : Integer.Sparse.eval row9897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9897, Integer.Sparse.eval_collectBalanced, rawRowCheck9897]

def rawRow9898 : Integer.Sparse Key := [(key2705, -6), (key2859, -6), (key2808, -6), (key2859, -6), (key2631, 6), (key2869, 6), (key2785, 6), (key2869, 6)]

theorem rawRowCheck9898 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form16 = rawRow9898 := by decide +kernel

def row9898 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

theorem rowCheck9898 : row9898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9898 := by decide +kernel

theorem rowEval9898 (x : Key → ℝ) : Integer.Sparse.eval row9898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9898, Integer.Sparse.eval_collectBalanced, rawRowCheck9898]

def rawRow9899 : Integer.Sparse Key := [(key2705, -6), (key2859, -6), (key2859, -6), (key2808, -6), (key2631, 6), (key2869, 6), (key2869, 6), (key2785, 6)]

theorem rawRowCheck9899 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form16 = rawRow9899 := by decide +kernel

def row9899 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

theorem rowCheck9899 : row9899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9899 := by decide +kernel

theorem rowEval9899 (x : Key → ℝ) : Integer.Sparse.eval row9899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9899, Integer.Sparse.eval_collectBalanced, rawRowCheck9899]

def rawRow9900 : Integer.Sparse Key := [(key2808, -6), (key2705, -6), (key2859, -6), (key2859, -6), (key2785, 6), (key2631, 6), (key2869, 6), (key2869, 6)]

theorem rawRowCheck9900 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form16 = rawRow9900 := by decide +kernel

def row9900 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

theorem rowCheck9900 : row9900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9900 := by decide +kernel

theorem rowEval9900 (x : Key → ℝ) : Integer.Sparse.eval row9900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9900, Integer.Sparse.eval_collectBalanced, rawRowCheck9900]

def rawRow9901 : Integer.Sparse Key := [(key2808, -6), (key2859, -6), (key2705, -6), (key2859, -6), (key2785, 6), (key2869, 6), (key2631, 6), (key2869, 6)]

theorem rawRowCheck9901 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form16 = rawRow9901 := by decide +kernel

def row9901 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

theorem rowCheck9901 : row9901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9901 := by decide +kernel

theorem rowEval9901 (x : Key → ℝ) : Integer.Sparse.eval row9901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9901, Integer.Sparse.eval_collectBalanced, rawRowCheck9901]

def rawRow9902 : Integer.Sparse Key := [(key2808, -6), (key2859, -6), (key2859, -6), (key2705, -6), (key2785, 6), (key2869, 6), (key2869, 6), (key2631, 6)]

theorem rawRowCheck9902 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form16 = rawRow9902 := by decide +kernel

def row9902 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

theorem rowCheck9902 : row9902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9902 := by decide +kernel

theorem rowEval9902 (x : Key → ℝ) : Integer.Sparse.eval row9902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck9902, Integer.Sparse.eval_collectBalanced, rawRowCheck9902]

def rawRow9903 : Integer.Sparse Key := [(key2859, -6), (key2705, -6), (key2808, -6), (key2859, -6), (key2869, 6), (key2631, 6), (key2785, 6), (key2869, 6)]

theorem rawRowCheck9903 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form16 = rawRow9903 := by decide +kernel

def row9903 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

theorem rowCheck9903 : row9903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9903 := by decide +kernel

theorem rowEval9903 (x : Key → ℝ) : Integer.Sparse.eval row9903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9903, Integer.Sparse.eval_collectBalanced, rawRowCheck9903]

def rawRow9904 : Integer.Sparse Key := [(key2859, -6), (key2705, -6), (key2859, -6), (key2808, -6), (key2869, 6), (key2631, 6), (key2869, 6), (key2785, 6)]

theorem rawRowCheck9904 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form16 = rawRow9904 := by decide +kernel

def row9904 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

theorem rowCheck9904 : row9904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9904 := by decide +kernel

theorem rowEval9904 (x : Key → ℝ) : Integer.Sparse.eval row9904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9904, Integer.Sparse.eval_collectBalanced, rawRowCheck9904]

def rawRow9905 : Integer.Sparse Key := [(key2859, -6), (key2808, -6), (key2705, -6), (key2859, -6), (key2869, 6), (key2785, 6), (key2631, 6), (key2869, 6)]

theorem rawRowCheck9905 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form16 = rawRow9905 := by decide +kernel

def row9905 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

theorem rowCheck9905 : row9905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9905 := by decide +kernel

theorem rowEval9905 (x : Key → ℝ) : Integer.Sparse.eval row9905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9905, Integer.Sparse.eval_collectBalanced, rawRowCheck9905]

def rawRow9906 : Integer.Sparse Key := [(key2859, -6), (key2808, -6), (key2859, -6), (key2705, -6), (key2869, 6), (key2785, 6), (key2869, 6), (key2631, 6)]

theorem rawRowCheck9906 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form16 = rawRow9906 := by decide +kernel

def row9906 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

theorem rowCheck9906 : row9906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9906 := by decide +kernel

theorem rowEval9906 (x : Key → ℝ) : Integer.Sparse.eval row9906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck9906, Integer.Sparse.eval_collectBalanced, rawRowCheck9906]

def rawRow9907 : Integer.Sparse Key := [(key2859, -6), (key2859, -6), (key2705, -6), (key2808, -6), (key2869, 6), (key2869, 6), (key2631, 6), (key2785, 6)]

theorem rawRowCheck9907 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form16 = rawRow9907 := by decide +kernel

def row9907 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

theorem rowCheck9907 : row9907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9907 := by decide +kernel

theorem rowEval9907 (x : Key → ℝ) : Integer.Sparse.eval row9907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9907, Integer.Sparse.eval_collectBalanced, rawRowCheck9907]

def rawRow9908 : Integer.Sparse Key := [(key2859, -6), (key2859, -6), (key2808, -6), (key2705, -6), (key2869, 6), (key2869, 6), (key2785, 6), (key2631, 6)]

theorem rawRowCheck9908 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form16 = rawRow9908 := by decide +kernel

def row9908 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

theorem rowCheck9908 : row9908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9908 := by decide +kernel

theorem rowEval9908 (x : Key → ℝ) : Integer.Sparse.eval row9908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck9908, Integer.Sparse.eval_collectBalanced, rawRowCheck9908]

def rawRow9909 : Integer.Sparse Key := [(key2617, -2), (key2620, -2), (key2620, -2), (key2810, -2), (key2833, -2), (key2833, -2), (key2952, -2), (key2952, -2), (key2962, -2), (key2962, -2), (key2964, -2), (key2964, -2), (key2633, 2), (key2643, 2), (key2643, 2), (key2707, 2), (key2730, 2), (key2730, 2), (key2978, 2), (key2978, 2), (key2985, 2), (key2985, 2), (key2994, 2), (key2994, 2)]

theorem rawRowCheck9909 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form17 = rawRow9909 := by decide +kernel

def row9909 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

theorem rowCheck9909 : row9909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9909 := by decide +kernel

theorem rowEval9909 (x : Key → ℝ) : Integer.Sparse.eval row9909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9909, Integer.Sparse.eval_collectBalanced, rawRowCheck9909]

def rawRow9910 : Integer.Sparse Key := [(key2620, -2), (key2617, -2), (key2620, -2), (key2833, -2), (key2810, -2), (key2833, -2), (key2962, -2), (key2964, -2), (key2952, -2), (key2964, -2), (key2952, -2), (key2962, -2), (key2643, 2), (key2633, 2), (key2643, 2), (key2730, 2), (key2707, 2), (key2730, 2), (key2985, 2), (key2994, 2), (key2978, 2), (key2994, 2), (key2978, 2), (key2985, 2)]

theorem rawRowCheck9910 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form17 = rawRow9910 := by decide +kernel

def row9910 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

theorem rowCheck9910 : row9910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9910 := by decide +kernel

theorem rowEval9910 (x : Key → ℝ) : Integer.Sparse.eval row9910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9910, Integer.Sparse.eval_collectBalanced, rawRowCheck9910]

def rawRow9911 : Integer.Sparse Key := [(key2620, -2), (key2620, -2), (key2617, -2), (key2833, -2), (key2833, -2), (key2810, -2), (key2964, -2), (key2962, -2), (key2964, -2), (key2952, -2), (key2962, -2), (key2952, -2), (key2643, 2), (key2643, 2), (key2633, 2), (key2730, 2), (key2730, 2), (key2707, 2), (key2994, 2), (key2985, 2), (key2994, 2), (key2978, 2), (key2985, 2), (key2978, 2)]

theorem rawRowCheck9911 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form17 = rawRow9911 := by decide +kernel

def row9911 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

theorem rowCheck9911 : row9911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9911 := by decide +kernel

theorem rowEval9911 (x : Key → ℝ) : Integer.Sparse.eval row9911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck9911, Integer.Sparse.eval_collectBalanced, rawRowCheck9911]

def rawRow9912 : Integer.Sparse Key := [(key2810, -2), (key2833, -2), (key2833, -2), (key2617, -2), (key2962, -2), (key2962, -2), (key2620, -2), (key2620, -2), (key2833, -2), (key2833, -2), (key2964, -2), (key2964, -2), (key2707, 2), (key2978, 2), (key2978, 2), (key2633, 2), (key2985, 2), (key2985, 2), (key2643, 2), (key2643, 2), (key2730, 2), (key2730, 2), (key2994, 2), (key2994, 2)]

theorem rawRowCheck9912 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form17 = rawRow9912 := by decide +kernel

def row9912 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -8), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

theorem rowCheck9912 : row9912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9912 := by decide +kernel

theorem rowEval9912 (x : Key → ℝ) : Integer.Sparse.eval row9912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9912, Integer.Sparse.eval_collectBalanced, rawRowCheck9912]

def rawRow9913 : Integer.Sparse Key := [(key2833, -2), (key2810, -2), (key2833, -2), (key2962, -2), (key2617, -2), (key2962, -2), (key2833, -2), (key2964, -2), (key2620, -2), (key2964, -2), (key2620, -2), (key2833, -2), (key2978, 2), (key2707, 2), (key2978, 2), (key2985, 2), (key2633, 2), (key2985, 2), (key2730, 2), (key2994, 2), (key2643, 2), (key2994, 2), (key2643, 2), (key2730, 2)]

theorem rawRowCheck9913 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form17 = rawRow9913 := by decide +kernel

def row9913 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -8), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

theorem rowCheck9913 : row9913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9913 := by decide +kernel

theorem rowEval9913 (x : Key → ℝ) : Integer.Sparse.eval row9913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9913, Integer.Sparse.eval_collectBalanced, rawRowCheck9913]

def rawRow9914 : Integer.Sparse Key := [(key2833, -2), (key2833, -2), (key2810, -2), (key2962, -2), (key2962, -2), (key2617, -2), (key2964, -2), (key2833, -2), (key2964, -2), (key2620, -2), (key2833, -2), (key2620, -2), (key2978, 2), (key2978, 2), (key2707, 2), (key2985, 2), (key2985, 2), (key2633, 2), (key2994, 2), (key2730, 2), (key2994, 2), (key2643, 2), (key2730, 2), (key2643, 2)]

theorem rawRowCheck9914 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form17 = rawRow9914 := by decide +kernel

def row9914 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -8), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

theorem rowCheck9914 : row9914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9914 := by decide +kernel

theorem rowEval9914 (x : Key → ℝ) : Integer.Sparse.eval row9914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck9914, Integer.Sparse.eval_collectBalanced, rawRowCheck9914]

def rawRow9915 : Integer.Sparse Key := [(key2952, -2), (key2962, -2), (key2964, -2), (key2620, -2), (key2833, -2), (key2964, -2), (key2617, -2), (key2620, -2), (key2810, -2), (key2833, -2), (key2952, -2), (key2962, -2), (key2730, 2), (key2985, 2), (key2994, 2), (key2643, 2), (key2978, 2), (key2994, 2), (key2633, 2), (key2643, 2), (key2707, 2), (key2730, 2), (key2978, 2), (key2985, 2)]

theorem rawRowCheck9915 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form17 = rawRow9915 := by decide +kernel

def row9915 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

theorem rowCheck9915 : row9915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9915 := by decide +kernel

theorem rowEval9915 (x : Key → ℝ) : Integer.Sparse.eval row9915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9915, Integer.Sparse.eval_collectBalanced, rawRowCheck9915]

def rawRow9916 : Integer.Sparse Key := [(key2952, -2), (key2964, -2), (key2962, -2), (key2620, -2), (key2964, -2), (key2833, -2), (key2620, -2), (key2617, -2), (key2833, -2), (key2810, -2), (key2962, -2), (key2952, -2), (key2730, 2), (key2994, 2), (key2985, 2), (key2643, 2), (key2994, 2), (key2978, 2), (key2643, 2), (key2633, 2), (key2730, 2), (key2707, 2), (key2985, 2), (key2978, 2)]

theorem rawRowCheck9916 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form17 = rawRow9916 := by decide +kernel

def row9916 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

theorem rowCheck9916 : row9916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9916 := by decide +kernel

theorem rowEval9916 (x : Key → ℝ) : Integer.Sparse.eval row9916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck9916, Integer.Sparse.eval_collectBalanced, rawRowCheck9916]

def rawRow9917 : Integer.Sparse Key := [(key2962, -2), (key2952, -2), (key2964, -2), (key2833, -2), (key2620, -2), (key2964, -2), (key2810, -2), (key2833, -2), (key2617, -2), (key2962, -2), (key2620, -2), (key2833, -2), (key2985, 2), (key2730, 2), (key2994, 2), (key2978, 2), (key2643, 2), (key2994, 2), (key2707, 2), (key2978, 2), (key2633, 2), (key2985, 2), (key2643, 2), (key2730, 2)]

theorem rawRowCheck9917 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form17 = rawRow9917 := by decide +kernel

def row9917 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -6), (key2952, -2), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

theorem rowCheck9917 : row9917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9917 := by decide +kernel

theorem rowEval9917 (x : Key → ℝ) : Integer.Sparse.eval row9917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9917, Integer.Sparse.eval_collectBalanced, rawRowCheck9917]

def rawRow9918 : Integer.Sparse Key := [(key2962, -2), (key2964, -2), (key2952, -2), (key2833, -2), (key2964, -2), (key2620, -2), (key2833, -2), (key2810, -2), (key2962, -2), (key2617, -2), (key2833, -2), (key2620, -2), (key2985, 2), (key2994, 2), (key2730, 2), (key2978, 2), (key2994, 2), (key2643, 2), (key2978, 2), (key2707, 2), (key2985, 2), (key2633, 2), (key2730, 2), (key2643, 2)]

theorem rawRowCheck9918 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form17 = rawRow9918 := by decide +kernel

def row9918 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -6), (key2952, -2), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

theorem rowCheck9918 : row9918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9918 := by decide +kernel

theorem rowEval9918 (x : Key → ℝ) : Integer.Sparse.eval row9918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck9918, Integer.Sparse.eval_collectBalanced, rawRowCheck9918]

def rawRow9919 : Integer.Sparse Key := [(key2964, -2), (key2952, -2), (key2962, -2), (key2964, -2), (key2620, -2), (key2833, -2), (key2952, -2), (key2962, -2), (key2620, -2), (key2833, -2), (key2617, -2), (key2810, -2), (key2994, 2), (key2730, 2), (key2985, 2), (key2994, 2), (key2643, 2), (key2978, 2), (key2730, 2), (key2985, 2), (key2643, 2), (key2978, 2), (key2633, 2), (key2707, 2)]

theorem rawRowCheck9919 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form17 = rawRow9919 := by decide +kernel

def row9919 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

theorem rowCheck9919 : row9919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9919 := by decide +kernel

theorem rowEval9919 (x : Key → ℝ) : Integer.Sparse.eval row9919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck9919, Integer.Sparse.eval_collectBalanced, rawRowCheck9919]

def rawRow9920 : Integer.Sparse Key := [(key2964, -2), (key2962, -2), (key2952, -2), (key2964, -2), (key2833, -2), (key2620, -2), (key2962, -2), (key2952, -2), (key2833, -2), (key2620, -2), (key2810, -2), (key2617, -2), (key2994, 2), (key2985, 2), (key2730, 2), (key2994, 2), (key2978, 2), (key2643, 2), (key2985, 2), (key2730, 2), (key2978, 2), (key2643, 2), (key2707, 2), (key2633, 2)]

theorem rawRowCheck9920 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form17 = rawRow9920 := by decide +kernel

def row9920 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

theorem rowCheck9920 : row9920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9920 := by decide +kernel

theorem rowEval9920 (x : Key → ℝ) : Integer.Sparse.eval row9920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck9920, Integer.Sparse.eval_collectBalanced, rawRowCheck9920]

def rawRow9921 : Integer.Sparse Key := [(key2633, -2), (key2643, -2), (key2643, -2), (key2707, -2), (key2978, -2), (key2978, -2), (key2730, -2), (key2730, -2), (key2985, -2), (key2985, -2), (key2994, -2), (key2994, -2), (key2617, 2), (key2655, 2), (key2655, 2), (key2672, 2), (key2749, 2), (key2749, 2), (key2945, 2), (key2945, 2), (key2962, 2), (key2962, 2), (key3004, 2), (key3004, 2)]

theorem rawRowCheck9921 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form17 = rawRow9921 := by decide +kernel

def row9921 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

theorem rowCheck9921 : row9921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9921 := by decide +kernel

theorem rowEval9921 (x : Key → ℝ) : Integer.Sparse.eval row9921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9921, Integer.Sparse.eval_collectBalanced, rawRowCheck9921]

def rawRow9922 : Integer.Sparse Key := [(key2643, -2), (key2633, -2), (key2643, -2), (key2978, -2), (key2707, -2), (key2978, -2), (key2985, -2), (key2994, -2), (key2730, -2), (key2994, -2), (key2730, -2), (key2985, -2), (key2655, 2), (key2617, 2), (key2655, 2), (key2749, 2), (key2672, 2), (key2749, 2), (key2962, 2), (key3004, 2), (key2945, 2), (key3004, 2), (key2945, 2), (key2962, 2)]

theorem rawRowCheck9922 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form17 = rawRow9922 := by decide +kernel

def row9922 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

theorem rowCheck9922 : row9922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9922 := by decide +kernel

theorem rowEval9922 (x : Key → ℝ) : Integer.Sparse.eval row9922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9922, Integer.Sparse.eval_collectBalanced, rawRowCheck9922]

def rawRow9923 : Integer.Sparse Key := [(key2643, -2), (key2643, -2), (key2633, -2), (key2978, -2), (key2978, -2), (key2707, -2), (key2994, -2), (key2985, -2), (key2994, -2), (key2730, -2), (key2985, -2), (key2730, -2), (key2655, 2), (key2655, 2), (key2617, 2), (key2749, 2), (key2749, 2), (key2672, 2), (key3004, 2), (key2962, 2), (key3004, 2), (key2945, 2), (key2962, 2), (key2945, 2)]

theorem rawRowCheck9923 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form17 = rawRow9923 := by decide +kernel

def row9923 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

theorem rowCheck9923 : row9923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9923 := by decide +kernel

theorem rowEval9923 (x : Key → ℝ) : Integer.Sparse.eval row9923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9923, Integer.Sparse.eval_collectBalanced, rawRowCheck9923]

def rawRow9924 : Integer.Sparse Key := [(key2707, -2), (key2730, -2), (key2730, -2), (key2633, -2), (key2985, -2), (key2985, -2), (key2643, -2), (key2643, -2), (key2978, -2), (key2978, -2), (key2994, -2), (key2994, -2), (key2672, 2), (key2749, 2), (key2749, 2), (key2617, 2), (key2962, 2), (key2962, 2), (key2655, 2), (key2655, 2), (key2749, 2), (key2749, 2), (key3004, 2), (key3004, 2)]

theorem rawRowCheck9924 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form17 = rawRow9924 := by decide +kernel

def row9924 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 8), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

theorem rowCheck9924 : row9924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9924 := by decide +kernel

theorem rowEval9924 (x : Key → ℝ) : Integer.Sparse.eval row9924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9924, Integer.Sparse.eval_collectBalanced, rawRowCheck9924]

def rawRow9925 : Integer.Sparse Key := [(key2730, -2), (key2707, -2), (key2730, -2), (key2985, -2), (key2633, -2), (key2985, -2), (key2978, -2), (key2994, -2), (key2643, -2), (key2994, -2), (key2643, -2), (key2978, -2), (key2749, 2), (key2672, 2), (key2749, 2), (key2962, 2), (key2617, 2), (key2962, 2), (key2749, 2), (key3004, 2), (key2655, 2), (key3004, 2), (key2655, 2), (key2749, 2)]

theorem rawRowCheck9925 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form17 = rawRow9925 := by decide +kernel

def row9925 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 8), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

theorem rowCheck9925 : row9925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9925 := by decide +kernel

theorem rowEval9925 (x : Key → ℝ) : Integer.Sparse.eval row9925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9925, Integer.Sparse.eval_collectBalanced, rawRowCheck9925]

def rawRow9926 : Integer.Sparse Key := [(key2730, -2), (key2730, -2), (key2707, -2), (key2985, -2), (key2985, -2), (key2633, -2), (key2994, -2), (key2978, -2), (key2994, -2), (key2643, -2), (key2978, -2), (key2643, -2), (key2749, 2), (key2749, 2), (key2672, 2), (key2962, 2), (key2962, 2), (key2617, 2), (key3004, 2), (key2749, 2), (key3004, 2), (key2655, 2), (key2749, 2), (key2655, 2)]

theorem rawRowCheck9926 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form17 = rawRow9926 := by decide +kernel

def row9926 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 8), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

theorem rowCheck9926 : row9926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9926 := by decide +kernel

theorem rowEval9926 (x : Key → ℝ) : Integer.Sparse.eval row9926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck9926, Integer.Sparse.eval_collectBalanced, rawRowCheck9926]

def rawRow9927 : Integer.Sparse Key := [(key2978, -2), (key2985, -2), (key2994, -2), (key2643, -2), (key2730, -2), (key2994, -2), (key2633, -2), (key2643, -2), (key2707, -2), (key2978, -2), (key2730, -2), (key2985, -2), (key2945, 2), (key2962, 2), (key3004, 2), (key2655, 2), (key2749, 2), (key3004, 2), (key2617, 2), (key2655, 2), (key2672, 2), (key2749, 2), (key2945, 2), (key2962, 2)]

theorem rawRowCheck9927 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form17 = rawRow9927 := by decide +kernel

def row9927 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

theorem rowCheck9927 : row9927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9927 := by decide +kernel

theorem rowEval9927 (x : Key → ℝ) : Integer.Sparse.eval row9927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9927, Integer.Sparse.eval_collectBalanced, rawRowCheck9927]

def rawRow9928 : Integer.Sparse Key := [(key2978, -2), (key2994, -2), (key2985, -2), (key2643, -2), (key2994, -2), (key2730, -2), (key2643, -2), (key2633, -2), (key2978, -2), (key2707, -2), (key2985, -2), (key2730, -2), (key2945, 2), (key3004, 2), (key2962, 2), (key2655, 2), (key3004, 2), (key2749, 2), (key2655, 2), (key2617, 2), (key2749, 2), (key2672, 2), (key2962, 2), (key2945, 2)]

theorem rawRowCheck9928 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form17 = rawRow9928 := by decide +kernel

def row9928 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

theorem rowCheck9928 : row9928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9928 := by decide +kernel

theorem rowEval9928 (x : Key → ℝ) : Integer.Sparse.eval row9928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9928, Integer.Sparse.eval_collectBalanced, rawRowCheck9928]

def rawRow9929 : Integer.Sparse Key := [(key2985, -2), (key2978, -2), (key2994, -2), (key2730, -2), (key2643, -2), (key2994, -2), (key2707, -2), (key2730, -2), (key2633, -2), (key2985, -2), (key2643, -2), (key2978, -2), (key2962, 2), (key2945, 2), (key3004, 2), (key2749, 2), (key2655, 2), (key3004, 2), (key2672, 2), (key2749, 2), (key2617, 2), (key2962, 2), (key2655, 2), (key2749, 2)]

theorem rawRowCheck9929 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form17 = rawRow9929 := by decide +kernel

def row9929 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 6), (key2945, 2), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

theorem rowCheck9929 : row9929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9929 := by decide +kernel

theorem rowEval9929 (x : Key → ℝ) : Integer.Sparse.eval row9929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9929, Integer.Sparse.eval_collectBalanced, rawRowCheck9929]

def rawRow9930 : Integer.Sparse Key := [(key2985, -2), (key2994, -2), (key2978, -2), (key2730, -2), (key2994, -2), (key2643, -2), (key2730, -2), (key2707, -2), (key2985, -2), (key2633, -2), (key2978, -2), (key2643, -2), (key2962, 2), (key3004, 2), (key2945, 2), (key2749, 2), (key3004, 2), (key2655, 2), (key2749, 2), (key2672, 2), (key2962, 2), (key2617, 2), (key2749, 2), (key2655, 2)]

theorem rawRowCheck9930 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form17 = rawRow9930 := by decide +kernel

def row9930 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 6), (key2945, 2), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

theorem rowCheck9930 : row9930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9930 := by decide +kernel

theorem rowEval9930 (x : Key → ℝ) : Integer.Sparse.eval row9930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck9930, Integer.Sparse.eval_collectBalanced, rawRowCheck9930]

def rawRow9931 : Integer.Sparse Key := [(key2994, -2), (key2978, -2), (key2985, -2), (key2994, -2), (key2643, -2), (key2730, -2), (key2978, -2), (key2985, -2), (key2643, -2), (key2730, -2), (key2633, -2), (key2707, -2), (key3004, 2), (key2945, 2), (key2962, 2), (key3004, 2), (key2655, 2), (key2749, 2), (key2945, 2), (key2962, 2), (key2655, 2), (key2749, 2), (key2617, 2), (key2672, 2)]

theorem rawRowCheck9931 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form17 = rawRow9931 := by decide +kernel

def row9931 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

theorem rowCheck9931 : row9931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9931 := by decide +kernel

theorem rowEval9931 (x : Key → ℝ) : Integer.Sparse.eval row9931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9931, Integer.Sparse.eval_collectBalanced, rawRowCheck9931]

def rawRow9932 : Integer.Sparse Key := [(key2994, -2), (key2985, -2), (key2978, -2), (key2994, -2), (key2730, -2), (key2643, -2), (key2985, -2), (key2978, -2), (key2730, -2), (key2643, -2), (key2707, -2), (key2633, -2), (key3004, 2), (key2962, 2), (key2945, 2), (key3004, 2), (key2749, 2), (key2655, 2), (key2962, 2), (key2945, 2), (key2749, 2), (key2655, 2), (key2672, 2), (key2617, 2)]

theorem rawRowCheck9932 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form17 = rawRow9932 := by decide +kernel

def row9932 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

theorem rowCheck9932 : row9932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9932 := by decide +kernel

theorem rowEval9932 (x : Key → ℝ) : Integer.Sparse.eval row9932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck9932, Integer.Sparse.eval_collectBalanced, rawRowCheck9932]

def rawRow9933 : Integer.Sparse Key := [(key982, 2), (key986, 2), (key986, 2), (key1096, 2), (key1171, 2), (key1171, 2), (key1185, 2), (key1185, 2), (key1222, 2), (key1222, 2), (key1224, 2), (key1224, 2), (key986, -2), (key986, -2), (key988, -2), (key1100, -2), (key1100, -2), (key1171, -2), (key1171, -2), (key1175, -2), (key1175, -2), (key1186, -2), (key1224, -2), (key1224, -2)]

theorem rawRowCheck9933 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form0 = rawRow9933 := by decide +kernel

def row9933 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

theorem rowCheck9933 : row9933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9933 := by decide +kernel

theorem rowEval9933 (x : Key → ℝ) : Integer.Sparse.eval row9933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9933, Integer.Sparse.eval_collectBalanced, rawRowCheck9933]

def rawRow9934 : Integer.Sparse Key := [(key986, 2), (key982, 2), (key986, 2), (key1171, 2), (key1096, 2), (key1171, 2), (key1222, 2), (key1224, 2), (key1185, 2), (key1224, 2), (key1185, 2), (key1222, 2), (key986, -2), (key988, -2), (key986, -2), (key1171, -2), (key1175, -2), (key1100, -2), (key1175, -2), (key1100, -2), (key1171, -2), (key1224, -2), (key1186, -2), (key1224, -2)]

theorem rawRowCheck9934 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form0 = rawRow9934 := by decide +kernel

def row9934 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

theorem rowCheck9934 : row9934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9934 := by decide +kernel

theorem rowEval9934 (x : Key → ℝ) : Integer.Sparse.eval row9934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9934, Integer.Sparse.eval_collectBalanced, rawRowCheck9934]

def rawRow9935 : Integer.Sparse Key := [(key986, 2), (key986, 2), (key982, 2), (key1171, 2), (key1171, 2), (key1096, 2), (key1224, 2), (key1222, 2), (key1224, 2), (key1185, 2), (key1222, 2), (key1185, 2), (key988, -2), (key986, -2), (key986, -2), (key1175, -2), (key1171, -2), (key1175, -2), (key1100, -2), (key1171, -2), (key1100, -2), (key1224, -2), (key1224, -2), (key1186, -2)]

theorem rawRowCheck9935 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form0 = rawRow9935 := by decide +kernel

def row9935 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

theorem rowCheck9935 : row9935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9935 := by decide +kernel

theorem rowEval9935 (x : Key → ℝ) : Integer.Sparse.eval row9935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9935, Integer.Sparse.eval_collectBalanced, rawRowCheck9935]

def rawRow9936 : Integer.Sparse Key := [(key1096, 2), (key1185, 2), (key1185, 2), (key982, 2), (key1222, 2), (key1222, 2), (key986, 2), (key986, 2), (key1171, 2), (key1171, 2), (key1224, 2), (key1224, 2), (key1100, -2), (key1100, -2), (key1186, -2), (key986, -2), (key986, -2), (key1171, -2), (key1171, -2), (key1224, -2), (key1224, -2), (key988, -2), (key1175, -2), (key1175, -2)]

theorem rawRowCheck9936 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form0 = rawRow9936 := by decide +kernel

def row9936 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

theorem rowCheck9936 : row9936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9936 := by decide +kernel

theorem rowEval9936 (x : Key → ℝ) : Integer.Sparse.eval row9936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9936, Integer.Sparse.eval_collectBalanced, rawRowCheck9936]

def rawRow9937 : Integer.Sparse Key := [(key1185, 2), (key1096, 2), (key1185, 2), (key1222, 2), (key982, 2), (key1222, 2), (key1171, 2), (key1224, 2), (key986, 2), (key1224, 2), (key986, 2), (key1171, 2), (key1100, -2), (key1186, -2), (key1100, -2), (key1171, -2), (key1224, -2), (key986, -2), (key1224, -2), (key986, -2), (key1171, -2), (key1175, -2), (key988, -2), (key1175, -2)]

theorem rawRowCheck9937 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form0 = rawRow9937 := by decide +kernel

def row9937 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

theorem rowCheck9937 : row9937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9937 := by decide +kernel

theorem rowEval9937 (x : Key → ℝ) : Integer.Sparse.eval row9937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9937, Integer.Sparse.eval_collectBalanced, rawRowCheck9937]

def rawRow9938 : Integer.Sparse Key := [(key1185, 2), (key1185, 2), (key1096, 2), (key1222, 2), (key1222, 2), (key982, 2), (key1224, 2), (key1171, 2), (key1224, 2), (key986, 2), (key1171, 2), (key986, 2), (key1186, -2), (key1100, -2), (key1100, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key986, -2), (key1171, -2), (key986, -2), (key1175, -2), (key1175, -2), (key988, -2)]

theorem rawRowCheck9938 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form0 = rawRow9938 := by decide +kernel

def row9938 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

theorem rowCheck9938 : row9938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9938 := by decide +kernel

theorem rowEval9938 (x : Key → ℝ) : Integer.Sparse.eval row9938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9938, Integer.Sparse.eval_collectBalanced, rawRowCheck9938]

def rawRow9939 : Integer.Sparse Key := [(key1171, 2), (key1222, 2), (key1224, 2), (key986, 2), (key1185, 2), (key1224, 2), (key982, 2), (key986, 2), (key1096, 2), (key1171, 2), (key1185, 2), (key1222, 2), (key1171, -2), (key1175, -2), (key1224, -2), (key986, -2), (key988, -2), (key1100, -2), (key1175, -2), (key1186, -2), (key1224, -2), (key986, -2), (key1100, -2), (key1171, -2)]

theorem rawRowCheck9939 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form0 = rawRow9939 := by decide +kernel

def row9939 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

theorem rowCheck9939 : row9939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9939 := by decide +kernel

theorem rowEval9939 (x : Key → ℝ) : Integer.Sparse.eval row9939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9939, Integer.Sparse.eval_collectBalanced, rawRowCheck9939]

def rawRow9940 : Integer.Sparse Key := [(key1171, 2), (key1224, 2), (key1222, 2), (key986, 2), (key1224, 2), (key1185, 2), (key986, 2), (key982, 2), (key1171, 2), (key1096, 2), (key1222, 2), (key1185, 2), (key1175, -2), (key1171, -2), (key1224, -2), (key988, -2), (key986, -2), (key1175, -2), (key1100, -2), (key1224, -2), (key1186, -2), (key986, -2), (key1171, -2), (key1100, -2)]

theorem rawRowCheck9940 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form0 = rawRow9940 := by decide +kernel

def row9940 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

theorem rowCheck9940 : row9940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9940 := by decide +kernel

theorem rowEval9940 (x : Key → ℝ) : Integer.Sparse.eval row9940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9940, Integer.Sparse.eval_collectBalanced, rawRowCheck9940]

def rawRow9941 : Integer.Sparse Key := [(key1222, 2), (key1171, 2), (key1224, 2), (key1185, 2), (key986, 2), (key1224, 2), (key1096, 2), (key1185, 2), (key982, 2), (key1222, 2), (key986, 2), (key1171, 2), (key1171, -2), (key1224, -2), (key1175, -2), (key1100, -2), (key1186, -2), (key986, -2), (key1224, -2), (key988, -2), (key1175, -2), (key1100, -2), (key986, -2), (key1171, -2)]

theorem rawRowCheck9941 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form0 = rawRow9941 := by decide +kernel

def row9941 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

theorem rowCheck9941 : row9941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9941 := by decide +kernel

theorem rowEval9941 (x : Key → ℝ) : Integer.Sparse.eval row9941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9941, Integer.Sparse.eval_collectBalanced, rawRowCheck9941]

def rawRow9942 : Integer.Sparse Key := [(key1222, 2), (key1224, 2), (key1171, 2), (key1185, 2), (key1224, 2), (key986, 2), (key1185, 2), (key1096, 2), (key1222, 2), (key982, 2), (key1171, 2), (key986, 2), (key1224, -2), (key1171, -2), (key1175, -2), (key1186, -2), (key1100, -2), (key1224, -2), (key986, -2), (key1175, -2), (key988, -2), (key1100, -2), (key1171, -2), (key986, -2)]

theorem rawRowCheck9942 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form0 = rawRow9942 := by decide +kernel

def row9942 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

theorem rowCheck9942 : row9942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9942 := by decide +kernel

theorem rowEval9942 (x : Key → ℝ) : Integer.Sparse.eval row9942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9942, Integer.Sparse.eval_collectBalanced, rawRowCheck9942]

def rawRow9943 : Integer.Sparse Key := [(key1224, 2), (key1171, 2), (key1222, 2), (key1224, 2), (key986, 2), (key1185, 2), (key1171, 2), (key1222, 2), (key986, 2), (key1185, 2), (key982, 2), (key1096, 2), (key1175, -2), (key1224, -2), (key1171, -2), (key1175, -2), (key1224, -2), (key988, -2), (key1186, -2), (key986, -2), (key1100, -2), (key1171, -2), (key986, -2), (key1100, -2)]

theorem rawRowCheck9943 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form0 = rawRow9943 := by decide +kernel

def row9943 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

theorem rowCheck9943 : row9943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9943 := by decide +kernel

theorem rowEval9943 (x : Key → ℝ) : Integer.Sparse.eval row9943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9943, Integer.Sparse.eval_collectBalanced, rawRowCheck9943]

def rawRow9944 : Integer.Sparse Key := [(key1224, 2), (key1222, 2), (key1171, 2), (key1224, 2), (key1185, 2), (key986, 2), (key1222, 2), (key1171, 2), (key1185, 2), (key986, 2), (key1096, 2), (key982, 2), (key1224, -2), (key1175, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1186, -2), (key988, -2), (key1100, -2), (key986, -2), (key1171, -2), (key1100, -2), (key986, -2)]

theorem rawRowCheck9944 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form0 = rawRow9944 := by decide +kernel

def row9944 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

theorem rowCheck9944 : row9944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9944 := by decide +kernel

theorem rowEval9944 (x : Key → ℝ) : Integer.Sparse.eval row9944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9944, Integer.Sparse.eval_collectBalanced, rawRowCheck9944]

def rawRow9945 : Integer.Sparse Key := [(key986, 2), (key986, 2), (key988, 2), (key1100, 2), (key1100, 2), (key1175, 2), (key1185, 2), (key1186, 2), (key1185, 2), (key1224, 2), (key1186, 2), (key1224, 2), (key982, -2), (key986, -2), (key986, -2), (key1096, -2), (key1100, -2), (key1096, -2), (key1171, -2), (key1100, -2), (key1171, -2), (key1185, -2), (key1185, -2), (key1222, -2)]

theorem rawRowCheck9945 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form0 = rawRow9945 := by decide +kernel

def row9945 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

theorem rowCheck9945 : row9945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9945 := by decide +kernel

theorem rowEval9945 (x : Key → ℝ) : Integer.Sparse.eval row9945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9945, Integer.Sparse.eval_collectBalanced, rawRowCheck9945]

def rawRow9946 : Integer.Sparse Key := [(key986, 2), (key988, 2), (key986, 2), (key1100, 2), (key1175, 2), (key1100, 2), (key1186, 2), (key1185, 2), (key1224, 2), (key1185, 2), (key1224, 2), (key1186, 2), (key986, -2), (key982, -2), (key986, -2), (key1100, -2), (key1096, -2), (key1171, -2), (key1096, -2), (key1171, -2), (key1100, -2), (key1185, -2), (key1222, -2), (key1185, -2)]

theorem rawRowCheck9946 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form0 = rawRow9946 := by decide +kernel

def row9946 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

theorem rowCheck9946 : row9946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9946 := by decide +kernel

theorem rowEval9946 (x : Key → ℝ) : Integer.Sparse.eval row9946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9946, Integer.Sparse.eval_collectBalanced, rawRowCheck9946]

def rawRow9947 : Integer.Sparse Key := [(key988, 2), (key986, 2), (key986, 2), (key1175, 2), (key1100, 2), (key1100, 2), (key1224, 2), (key1224, 2), (key1186, 2), (key1186, 2), (key1185, 2), (key1185, 2), (key986, -2), (key986, -2), (key982, -2), (key1171, -2), (key1171, -2), (key1100, -2), (key1100, -2), (key1096, -2), (key1096, -2), (key1222, -2), (key1185, -2), (key1185, -2)]

theorem rawRowCheck9947 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form0 = rawRow9947 := by decide +kernel

def row9947 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

theorem rowCheck9947 : row9947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9947 := by decide +kernel

theorem rowEval9947 (x : Key → ℝ) : Integer.Sparse.eval row9947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9947, Integer.Sparse.eval_collectBalanced, rawRowCheck9947]

def rawRow9948 : Integer.Sparse Key := [(key1100, 2), (key1185, 2), (key1186, 2), (key986, 2), (key1185, 2), (key1224, 2), (key986, 2), (key988, 2), (key1100, 2), (key1175, 2), (key1186, 2), (key1224, 2), (key1096, -2), (key1100, -2), (key1185, -2), (key982, -2), (key986, -2), (key1096, -2), (key1171, -2), (key1185, -2), (key1222, -2), (key986, -2), (key1100, -2), (key1171, -2)]

theorem rawRowCheck9948 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form0 = rawRow9948 := by decide +kernel

def row9948 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

theorem rowCheck9948 : row9948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9948 := by decide +kernel

theorem rowEval9948 (x : Key → ℝ) : Integer.Sparse.eval row9948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9948, Integer.Sparse.eval_collectBalanced, rawRowCheck9948]

def rawRow9949 : Integer.Sparse Key := [(key1100, 2), (key1186, 2), (key1185, 2), (key986, 2), (key1224, 2), (key1185, 2), (key988, 2), (key986, 2), (key1175, 2), (key1100, 2), (key1224, 2), (key1186, 2), (key1100, -2), (key1096, -2), (key1185, -2), (key986, -2), (key982, -2), (key1171, -2), (key1096, -2), (key1222, -2), (key1185, -2), (key986, -2), (key1171, -2), (key1100, -2)]

theorem rawRowCheck9949 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form0 = rawRow9949 := by decide +kernel

def row9949 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

theorem rowCheck9949 : row9949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9949 := by decide +kernel

theorem rowEval9949 (x : Key → ℝ) : Integer.Sparse.eval row9949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9949, Integer.Sparse.eval_collectBalanced, rawRowCheck9949]

def rawRow9950 : Integer.Sparse Key := [(key1185, 2), (key1100, 2), (key1186, 2), (key1185, 2), (key986, 2), (key1224, 2), (key1100, 2), (key1186, 2), (key986, 2), (key1224, 2), (key988, 2), (key1175, 2), (key1096, -2), (key1185, -2), (key1100, -2), (key1096, -2), (key1185, -2), (key982, -2), (key1222, -2), (key986, -2), (key1171, -2), (key1100, -2), (key986, -2), (key1171, -2)]

theorem rawRowCheck9950 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form0 = rawRow9950 := by decide +kernel

def row9950 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

theorem rowCheck9950 : row9950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9950 := by decide +kernel

theorem rowEval9950 (x : Key → ℝ) : Integer.Sparse.eval row9950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9950, Integer.Sparse.eval_collectBalanced, rawRowCheck9950]

def rawRow9951 : Integer.Sparse Key := [(key1185, 2), (key1186, 2), (key1100, 2), (key1185, 2), (key1224, 2), (key986, 2), (key1186, 2), (key1100, 2), (key1224, 2), (key986, 2), (key1175, 2), (key988, 2), (key1185, -2), (key1096, -2), (key1100, -2), (key1185, -2), (key1096, -2), (key1222, -2), (key982, -2), (key1171, -2), (key986, -2), (key1100, -2), (key1171, -2), (key986, -2)]

theorem rawRowCheck9951 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form0 = rawRow9951 := by decide +kernel

def row9951 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

theorem rowCheck9951 : row9951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9951 := by decide +kernel

theorem rowEval9951 (x : Key → ℝ) : Integer.Sparse.eval row9951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9951, Integer.Sparse.eval_collectBalanced, rawRowCheck9951]

def rawRow9952 : Integer.Sparse Key := [(key1186, 2), (key1100, 2), (key1185, 2), (key1224, 2), (key986, 2), (key1185, 2), (key1175, 2), (key1224, 2), (key988, 2), (key1186, 2), (key986, 2), (key1100, 2), (key1100, -2), (key1185, -2), (key1096, -2), (key1171, -2), (key1222, -2), (key986, -2), (key1185, -2), (key982, -2), (key1096, -2), (key1171, -2), (key986, -2), (key1100, -2)]

theorem rawRowCheck9952 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form0 = rawRow9952 := by decide +kernel

def row9952 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

theorem rowCheck9952 : row9952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9952 := by decide +kernel

theorem rowEval9952 (x : Key → ℝ) : Integer.Sparse.eval row9952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9952, Integer.Sparse.eval_collectBalanced, rawRowCheck9952]

def rawRow9953 : Integer.Sparse Key := [(key1186, 2), (key1185, 2), (key1100, 2), (key1224, 2), (key1185, 2), (key986, 2), (key1224, 2), (key1175, 2), (key1186, 2), (key988, 2), (key1100, 2), (key986, 2), (key1185, -2), (key1100, -2), (key1096, -2), (key1222, -2), (key1171, -2), (key1185, -2), (key986, -2), (key1096, -2), (key982, -2), (key1171, -2), (key1100, -2), (key986, -2)]

theorem rawRowCheck9953 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form0 = rawRow9953 := by decide +kernel

def row9953 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

theorem rowCheck9953 : row9953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9953 := by decide +kernel

theorem rowEval9953 (x : Key → ℝ) : Integer.Sparse.eval row9953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9953, Integer.Sparse.eval_collectBalanced, rawRowCheck9953]

def rawRow9954 : Integer.Sparse Key := [(key1175, 2), (key1224, 2), (key1224, 2), (key988, 2), (key1186, 2), (key1186, 2), (key986, 2), (key986, 2), (key1100, 2), (key1100, 2), (key1185, 2), (key1185, 2), (key1171, -2), (key1171, -2), (key1222, -2), (key986, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1185, -2), (key1185, -2), (key982, -2), (key1096, -2), (key1096, -2)]

theorem rawRowCheck9954 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form0 = rawRow9954 := by decide +kernel

def row9954 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

theorem rowCheck9954 : row9954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9954 := by decide +kernel

theorem rowEval9954 (x : Key → ℝ) : Integer.Sparse.eval row9954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9954, Integer.Sparse.eval_collectBalanced, rawRowCheck9954]

def rawRow9955 : Integer.Sparse Key := [(key1224, 2), (key1175, 2), (key1224, 2), (key1186, 2), (key988, 2), (key1186, 2), (key1100, 2), (key1185, 2), (key986, 2), (key1185, 2), (key986, 2), (key1100, 2), (key1171, -2), (key1222, -2), (key1171, -2), (key1100, -2), (key1185, -2), (key986, -2), (key1185, -2), (key986, -2), (key1100, -2), (key1096, -2), (key982, -2), (key1096, -2)]

theorem rawRowCheck9955 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form0 = rawRow9955 := by decide +kernel

def row9955 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

theorem rowCheck9955 : row9955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9955 := by decide +kernel

theorem rowEval9955 (x : Key → ℝ) : Integer.Sparse.eval row9955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9955, Integer.Sparse.eval_collectBalanced, rawRowCheck9955]

def rawRow9956 : Integer.Sparse Key := [(key1224, 2), (key1224, 2), (key1175, 2), (key1186, 2), (key1186, 2), (key988, 2), (key1185, 2), (key1100, 2), (key1185, 2), (key986, 2), (key1100, 2), (key986, 2), (key1222, -2), (key1171, -2), (key1171, -2), (key1185, -2), (key1100, -2), (key1185, -2), (key986, -2), (key1100, -2), (key986, -2), (key1096, -2), (key1096, -2), (key982, -2)]

theorem rawRowCheck9956 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form0 = rawRow9956 := by decide +kernel

def row9956 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

theorem rowCheck9956 : row9956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9956 := by decide +kernel

theorem rowEval9956 (x : Key → ℝ) : Integer.Sparse.eval row9956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9956, Integer.Sparse.eval_collectBalanced, rawRowCheck9956]

def rawRow9957 : Integer.Sparse Key := [(key91, -24), (key8, 6), (key91, 6), (key152, 6), (key152, 6)]

theorem rawRowCheck9957 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form1 = rawRow9957 := by decide +kernel

def row9957 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

theorem rowCheck9957 : row9957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9957 := by decide +kernel

theorem rowEval9957 (x : Key → ℝ) : Integer.Sparse.eval row9957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9957, Integer.Sparse.eval_collectBalanced, rawRowCheck9957]

def rawRow9958 : Integer.Sparse Key := [(key91, -24), (key8, 6), (key152, 6), (key91, 6), (key152, 6)]

theorem rawRowCheck9958 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form1 = rawRow9958 := by decide +kernel

def row9958 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

theorem rowCheck9958 : row9958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9958 := by decide +kernel

theorem rowEval9958 (x : Key → ℝ) : Integer.Sparse.eval row9958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9958, Integer.Sparse.eval_collectBalanced, rawRowCheck9958]

def rawRow9959 : Integer.Sparse Key := [(key91, -24), (key8, 6), (key152, 6), (key152, 6), (key91, 6)]

theorem rawRowCheck9959 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form1 = rawRow9959 := by decide +kernel

def row9959 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

theorem rowCheck9959 : row9959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9959 := by decide +kernel

theorem rowEval9959 (x : Key → ℝ) : Integer.Sparse.eval row9959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9959, Integer.Sparse.eval_collectBalanced, rawRowCheck9959]

def rawRow9960 : Integer.Sparse Key := [(key91, -24), (key91, 6), (key8, 6), (key152, 6), (key152, 6)]

theorem rawRowCheck9960 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form1 = rawRow9960 := by decide +kernel

def row9960 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

theorem rowCheck9960 : row9960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9960 := by decide +kernel

theorem rowEval9960 (x : Key → ℝ) : Integer.Sparse.eval row9960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9960, Integer.Sparse.eval_collectBalanced, rawRowCheck9960]

def rawRow9961 : Integer.Sparse Key := [(key91, -24), (key91, 6), (key152, 6), (key8, 6), (key152, 6)]

theorem rawRowCheck9961 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form1 = rawRow9961 := by decide +kernel

def row9961 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

theorem rowCheck9961 : row9961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9961 := by decide +kernel

theorem rowEval9961 (x : Key → ℝ) : Integer.Sparse.eval row9961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9961, Integer.Sparse.eval_collectBalanced, rawRowCheck9961]

def rawRow9962 : Integer.Sparse Key := [(key91, -24), (key91, 6), (key152, 6), (key152, 6), (key8, 6)]

theorem rawRowCheck9962 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form1 = rawRow9962 := by decide +kernel

def row9962 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

theorem rowCheck9962 : row9962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9962 := by decide +kernel

theorem rowEval9962 (x : Key → ℝ) : Integer.Sparse.eval row9962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9962, Integer.Sparse.eval_collectBalanced, rawRowCheck9962]

def rawRow9963 : Integer.Sparse Key := [(key91, -24), (key152, 6), (key8, 6), (key91, 6), (key152, 6)]

theorem rawRowCheck9963 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form1 = rawRow9963 := by decide +kernel

def row9963 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

theorem rowCheck9963 : row9963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9963 := by decide +kernel

theorem rowEval9963 (x : Key → ℝ) : Integer.Sparse.eval row9963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9963, Integer.Sparse.eval_collectBalanced, rawRowCheck9963]

def rawRow9964 : Integer.Sparse Key := [(key91, -24), (key152, 6), (key8, 6), (key152, 6), (key91, 6)]

theorem rawRowCheck9964 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form1 = rawRow9964 := by decide +kernel

def row9964 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

theorem rowCheck9964 : row9964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9964 := by decide +kernel

theorem rowEval9964 (x : Key → ℝ) : Integer.Sparse.eval row9964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9964, Integer.Sparse.eval_collectBalanced, rawRowCheck9964]

def rawRow9965 : Integer.Sparse Key := [(key91, -24), (key152, 6), (key91, 6), (key8, 6), (key152, 6)]

theorem rawRowCheck9965 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form1 = rawRow9965 := by decide +kernel

def row9965 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

theorem rowCheck9965 : row9965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9965 := by decide +kernel

theorem rowEval9965 (x : Key → ℝ) : Integer.Sparse.eval row9965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9965, Integer.Sparse.eval_collectBalanced, rawRowCheck9965]

def rawRow9966 : Integer.Sparse Key := [(key91, -24), (key152, 6), (key91, 6), (key152, 6), (key8, 6)]

theorem rawRowCheck9966 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form1 = rawRow9966 := by decide +kernel

def row9966 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

theorem rowCheck9966 : row9966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9966 := by decide +kernel

theorem rowEval9966 (x : Key → ℝ) : Integer.Sparse.eval row9966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9966, Integer.Sparse.eval_collectBalanced, rawRowCheck9966]

def rawRow9967 : Integer.Sparse Key := [(key91, -24), (key152, 6), (key152, 6), (key8, 6), (key91, 6)]

theorem rawRowCheck9967 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form1 = rawRow9967 := by decide +kernel

def row9967 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

theorem rowCheck9967 : row9967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9967 := by decide +kernel

theorem rowEval9967 (x : Key → ℝ) : Integer.Sparse.eval row9967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9967, Integer.Sparse.eval_collectBalanced, rawRowCheck9967]

def rawRow9968 : Integer.Sparse Key := [(key91, -24), (key152, 6), (key152, 6), (key91, 6), (key8, 6)]

theorem rawRowCheck9968 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form1 = rawRow9968 := by decide +kernel

def row9968 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

theorem rowCheck9968 : row9968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9968 := by decide +kernel

theorem rowEval9968 (x : Key → ℝ) : Integer.Sparse.eval row9968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9968, Integer.Sparse.eval_collectBalanced, rawRowCheck9968]

def rawRow9969 : Integer.Sparse Key := [(key152, -24), (key8, 6), (key91, 6), (key91, 6), (key152, 6)]

theorem rawRowCheck9969 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form1 = rawRow9969 := by decide +kernel

def row9969 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

theorem rowCheck9969 : row9969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9969 := by decide +kernel

theorem rowEval9969 (x : Key → ℝ) : Integer.Sparse.eval row9969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9969, Integer.Sparse.eval_collectBalanced, rawRowCheck9969]

def rawRow9970 : Integer.Sparse Key := [(key152, -24), (key8, 6), (key91, 6), (key152, 6), (key91, 6)]

theorem rawRowCheck9970 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form1 = rawRow9970 := by decide +kernel

def row9970 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

theorem rowCheck9970 : row9970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9970 := by decide +kernel

theorem rowEval9970 (x : Key → ℝ) : Integer.Sparse.eval row9970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9970, Integer.Sparse.eval_collectBalanced, rawRowCheck9970]

def rawRow9971 : Integer.Sparse Key := [(key152, -24), (key8, 6), (key152, 6), (key91, 6), (key91, 6)]

theorem rawRowCheck9971 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form1 = rawRow9971 := by decide +kernel

def row9971 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

theorem rowCheck9971 : row9971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9971 := by decide +kernel

theorem rowEval9971 (x : Key → ℝ) : Integer.Sparse.eval row9971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9971, Integer.Sparse.eval_collectBalanced, rawRowCheck9971]

def rawRow9972 : Integer.Sparse Key := [(key152, -24), (key91, 6), (key8, 6), (key91, 6), (key152, 6)]

theorem rawRowCheck9972 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form1 = rawRow9972 := by decide +kernel

def row9972 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

theorem rowCheck9972 : row9972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9972 := by decide +kernel

theorem rowEval9972 (x : Key → ℝ) : Integer.Sparse.eval row9972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9972, Integer.Sparse.eval_collectBalanced, rawRowCheck9972]

def rawRow9973 : Integer.Sparse Key := [(key152, -24), (key91, 6), (key8, 6), (key152, 6), (key91, 6)]

theorem rawRowCheck9973 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form1 = rawRow9973 := by decide +kernel

def row9973 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

theorem rowCheck9973 : row9973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9973 := by decide +kernel

theorem rowEval9973 (x : Key → ℝ) : Integer.Sparse.eval row9973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9973, Integer.Sparse.eval_collectBalanced, rawRowCheck9973]

def rawRow9974 : Integer.Sparse Key := [(key152, -24), (key91, 6), (key91, 6), (key8, 6), (key152, 6)]

theorem rawRowCheck9974 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form1 = rawRow9974 := by decide +kernel

def row9974 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

theorem rowCheck9974 : row9974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9974 := by decide +kernel

theorem rowEval9974 (x : Key → ℝ) : Integer.Sparse.eval row9974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9974, Integer.Sparse.eval_collectBalanced, rawRowCheck9974]

def rawRow9975 : Integer.Sparse Key := [(key152, -24), (key91, 6), (key91, 6), (key152, 6), (key8, 6)]

theorem rawRowCheck9975 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form1 = rawRow9975 := by decide +kernel

def row9975 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

theorem rowCheck9975 : row9975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9975 := by decide +kernel

theorem rowEval9975 (x : Key → ℝ) : Integer.Sparse.eval row9975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9975, Integer.Sparse.eval_collectBalanced, rawRowCheck9975]

def rawRow9976 : Integer.Sparse Key := [(key152, -24), (key91, 6), (key152, 6), (key8, 6), (key91, 6)]

theorem rawRowCheck9976 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form1 = rawRow9976 := by decide +kernel

def row9976 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

theorem rowCheck9976 : row9976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9976 := by decide +kernel

theorem rowEval9976 (x : Key → ℝ) : Integer.Sparse.eval row9976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9976, Integer.Sparse.eval_collectBalanced, rawRowCheck9976]

def rawRow9977 : Integer.Sparse Key := [(key152, -24), (key91, 6), (key152, 6), (key91, 6), (key8, 6)]

theorem rawRowCheck9977 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form1 = rawRow9977 := by decide +kernel

def row9977 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

theorem rowCheck9977 : row9977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9977 := by decide +kernel

theorem rowEval9977 (x : Key → ℝ) : Integer.Sparse.eval row9977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9977, Integer.Sparse.eval_collectBalanced, rawRowCheck9977]

def rawRow9978 : Integer.Sparse Key := [(key152, -24), (key152, 6), (key8, 6), (key91, 6), (key91, 6)]

theorem rawRowCheck9978 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form1 = rawRow9978 := by decide +kernel

def row9978 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

theorem rowCheck9978 : row9978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9978 := by decide +kernel

theorem rowEval9978 (x : Key → ℝ) : Integer.Sparse.eval row9978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9978, Integer.Sparse.eval_collectBalanced, rawRowCheck9978]

def rawRow9979 : Integer.Sparse Key := [(key152, -24), (key152, 6), (key91, 6), (key8, 6), (key91, 6)]

theorem rawRowCheck9979 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form1 = rawRow9979 := by decide +kernel

def row9979 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

theorem rowCheck9979 : row9979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9979 := by decide +kernel

theorem rowEval9979 (x : Key → ℝ) : Integer.Sparse.eval row9979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9979, Integer.Sparse.eval_collectBalanced, rawRowCheck9979]

def rawRow9980 : Integer.Sparse Key := [(key152, -24), (key152, 6), (key91, 6), (key91, 6), (key8, 6)]

theorem rawRowCheck9980 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form1 = rawRow9980 := by decide +kernel

def row9980 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

theorem rowCheck9980 : row9980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9980 := by decide +kernel

theorem rowEval9980 (x : Key → ℝ) : Integer.Sparse.eval row9980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9980, Integer.Sparse.eval_collectBalanced, rawRowCheck9980]

def rawRow9981 : Integer.Sparse Key := [(key88, -6), (key88, -6), (key94, -6), (key156, -6), (key5, 2), (key9, 2), (key14, 2), (key92, 2), (key92, 2), (key153, 2), (key153, 2), (key161, 2), (key161, 2), (key194, 2), (key203, 2), (key203, 2)]

theorem rawRowCheck9981 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form2 = rawRow9981 := by decide +kernel

def row9981 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, 2), (key88, -12), (key92, 4), (key94, -6), (key153, 4), (key156, -6), (key161, 4), (key194, 2), (key203, 4)]

theorem rowCheck9981 : row9981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9981 := by decide +kernel

theorem rowEval9981 (x : Key → ℝ) : Integer.Sparse.eval row9981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9981, Integer.Sparse.eval_collectBalanced, rawRowCheck9981]

def rawRow9982 : Integer.Sparse Key := [(key88, -6), (key94, -6), (key88, -6), (key156, -6), (key5, 2), (key11, 2), (key9, 2), (key153, 2), (key161, 2), (key92, 2), (key161, 2), (key92, 2), (key153, 2), (key203, 2), (key194, 2), (key203, 2)]

theorem rawRowCheck9982 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form2 = rawRow9982 := by decide +kernel

def row9982 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -12), (key92, 4), (key94, -6), (key153, 4), (key156, -6), (key161, 4), (key194, 2), (key203, 4)]

theorem rowCheck9982 : row9982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9982 := by decide +kernel

theorem rowEval9982 (x : Key → ℝ) : Integer.Sparse.eval row9982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9982, Integer.Sparse.eval_collectBalanced, rawRowCheck9982]

def rawRow9983 : Integer.Sparse Key := [(key94, -6), (key88, -6), (key88, -6), (key156, -6), (key11, 2), (key5, 2), (key9, 2), (key161, 2), (key153, 2), (key161, 2), (key92, 2), (key153, 2), (key92, 2), (key203, 2), (key203, 2), (key194, 2)]

theorem rawRowCheck9983 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form2 = rawRow9983 := by decide +kernel

def row9983 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -12), (key92, 4), (key94, -6), (key153, 4), (key156, -6), (key161, 4), (key194, 2), (key203, 4)]

theorem rowCheck9983 : row9983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9983 := by decide +kernel

theorem rowEval9983 (x : Key → ℝ) : Integer.Sparse.eval row9983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9983, Integer.Sparse.eval_collectBalanced, rawRowCheck9983]

end MUB6.Certificate.GramRows

end OAI
