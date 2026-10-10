import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
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

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8704 : Integer.Sparse Key := [(key2930, -2), (key2930, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2767, -2), (key2767, -2), (key2767, -2), (key2767, -2), (key2763, -2), (key2763, -2), (key2763, -2), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1)]

theorem rawRowCheck8704 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form5 = rawRow8704 := by decide +kernel

def row8704 : Integer.Sparse Key := [(key2763, -6), (key2767, -12), (key2840, 6), (key2844, 6), (key2888, 6), (key2930, -6), (key2967, 6)]

theorem rowCheck8704 : row8704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8704 := by decide +kernel

theorem rowEval8704 (x : Key → ℝ) : Integer.Sparse.eval row8704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8704, Integer.Sparse.eval_collectBalanced, rawRowCheck8704]

def rawRow8705 : Integer.Sparse Key := [(key2599, -2), (key2599, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2888, -2), (key2888, -2), (key2888, -2), (key2888, -2), (key2909, -2), (key2909, -2), (key2909, -2), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1)]

theorem rawRowCheck8705 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form5 = rawRow8705 := by decide +kernel

def row8705 : Integer.Sparse Key := [(key2588, 6), (key2599, -6), (key2767, 6), (key2844, 6), (key2875, 6), (key2888, -12), (key2909, -6)]

theorem rowCheck8705 : row8705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8705 := by decide +kernel

theorem rowEval8705 (x : Key → ℝ) : Integer.Sparse.eval row8705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8705, Integer.Sparse.eval_collectBalanced, rawRowCheck8705]

def rawRow8706 : Integer.Sparse Key := [(key2888, -2), (key2888, -2), (key2909, -2), (key2599, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2909, -2), (key2909, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1)]

theorem rawRowCheck8706 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form5 = rawRow8706 := by decide +kernel

def row8706 : Integer.Sparse Key := [(key2588, 6), (key2599, -6), (key2767, 6), (key2844, 6), (key2875, 6), (key2888, -12), (key2909, -6)]

theorem rowCheck8706 : row8706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8706 := by decide +kernel

theorem rowEval8706 (x : Key → ℝ) : Integer.Sparse.eval row8706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8706, Integer.Sparse.eval_collectBalanced, rawRowCheck8706]

def rawRow8707 : Integer.Sparse Key := [(key2888, -2), (key2909, -2), (key2888, -2), (key2888, -2), (key2909, -2), (key2599, -2), (key2909, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2599, -2), (key2888, -2), (key2844, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2844, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2588, 1), (key2844, 1), (key2588, 1), (key2767, 1)]

theorem rawRowCheck8707 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form5 = rawRow8707 := by decide +kernel

def row8707 : Integer.Sparse Key := [(key2588, 6), (key2599, -6), (key2767, 6), (key2844, 6), (key2875, 6), (key2888, -12), (key2909, -6)]

theorem rowCheck8707 : row8707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8707 := by decide +kernel

theorem rowEval8707 (x : Key → ℝ) : Integer.Sparse.eval row8707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8707, Integer.Sparse.eval_collectBalanced, rawRowCheck8707]

def rawRow8708 : Integer.Sparse Key := [(key2909, -2), (key2888, -2), (key2888, -2), (key2909, -2), (key2888, -2), (key2909, -2), (key2599, -2), (key2888, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2599, -2), (key2875, 1), (key2844, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2767, 1), (key2875, 1), (key2844, 1), (key2875, 1), (key2588, 1), (key2844, 1), (key2588, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2588, 1), (key2844, 1), (key2767, 1), (key2844, 1), (key2588, 1), (key2767, 1), (key2588, 1)]

theorem rawRowCheck8708 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form5 = rawRow8708 := by decide +kernel

def row8708 : Integer.Sparse Key := [(key2588, 6), (key2599, -6), (key2767, 6), (key2844, 6), (key2875, 6), (key2888, -12), (key2909, -6)]

theorem rowCheck8708 : row8708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8708 := by decide +kernel

theorem rowEval8708 (x : Key → ℝ) : Integer.Sparse.eval row8708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck8708, Integer.Sparse.eval_collectBalanced, rawRowCheck8708]

def rawRow8709 : Integer.Sparse Key := [(key2352, -24), (key2447, 6), (key2447, 6), (key2447, 6), (key2511, 6)]

theorem rawRowCheck8709 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form6 = rawRow8709 := by decide +kernel

def row8709 : Integer.Sparse Key := [(key2352, -24), (key2447, 18), (key2511, 6)]

theorem rowCheck8709 : row8709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8709 := by decide +kernel

theorem rowEval8709 (x : Key → ℝ) : Integer.Sparse.eval row8709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8709, Integer.Sparse.eval_collectBalanced, rawRowCheck8709]

def rawRow8710 : Integer.Sparse Key := [(key2352, -24), (key2447, 6), (key2447, 6), (key2511, 6), (key2447, 6)]

theorem rawRowCheck8710 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form6 = rawRow8710 := by decide +kernel

def row8710 : Integer.Sparse Key := [(key2352, -24), (key2447, 18), (key2511, 6)]

theorem rowCheck8710 : row8710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8710 := by decide +kernel

theorem rowEval8710 (x : Key → ℝ) : Integer.Sparse.eval row8710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8710, Integer.Sparse.eval_collectBalanced, rawRowCheck8710]

def rawRow8711 : Integer.Sparse Key := [(key2352, -24), (key2447, 6), (key2511, 6), (key2447, 6), (key2447, 6)]

theorem rawRowCheck8711 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form6 = rawRow8711 := by decide +kernel

def row8711 : Integer.Sparse Key := [(key2352, -24), (key2447, 18), (key2511, 6)]

theorem rowCheck8711 : row8711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8711 := by decide +kernel

theorem rowEval8711 (x : Key → ℝ) : Integer.Sparse.eval row8711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8711, Integer.Sparse.eval_collectBalanced, rawRowCheck8711]

def rawRow8712 : Integer.Sparse Key := [(key2352, -24), (key2511, 6), (key2447, 6), (key2447, 6), (key2447, 6)]

theorem rawRowCheck8712 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form6 = rawRow8712 := by decide +kernel

def row8712 : Integer.Sparse Key := [(key2352, -24), (key2447, 18), (key2511, 6)]

theorem rowCheck8712 : row8712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8712 := by decide +kernel

theorem rowEval8712 (x : Key → ℝ) : Integer.Sparse.eval row8712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8712, Integer.Sparse.eval_collectBalanced, rawRowCheck8712]

def rawRow8713 : Integer.Sparse Key := [(key2511, -24), (key2352, 6), (key2447, 6), (key2447, 6), (key2447, 6)]

theorem rawRowCheck8713 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form6 = rawRow8713 := by decide +kernel

def row8713 : Integer.Sparse Key := [(key2352, 6), (key2447, 18), (key2511, -24)]

theorem rowCheck8713 : row8713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8713 := by decide +kernel

theorem rowEval8713 (x : Key → ℝ) : Integer.Sparse.eval row8713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8713, Integer.Sparse.eval_collectBalanced, rawRowCheck8713]

def rawRow8714 : Integer.Sparse Key := [(key2511, -24), (key2447, 6), (key2352, 6), (key2447, 6), (key2447, 6)]

theorem rawRowCheck8714 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form6 = rawRow8714 := by decide +kernel

def row8714 : Integer.Sparse Key := [(key2352, 6), (key2447, 18), (key2511, -24)]

theorem rowCheck8714 : row8714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8714 := by decide +kernel

theorem rowEval8714 (x : Key → ℝ) : Integer.Sparse.eval row8714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8714, Integer.Sparse.eval_collectBalanced, rawRowCheck8714]

def rawRow8715 : Integer.Sparse Key := [(key2511, -24), (key2447, 6), (key2447, 6), (key2352, 6), (key2447, 6)]

theorem rawRowCheck8715 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form6 = rawRow8715 := by decide +kernel

def row8715 : Integer.Sparse Key := [(key2352, 6), (key2447, 18), (key2511, -24)]

theorem rowCheck8715 : row8715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8715 := by decide +kernel

theorem rowEval8715 (x : Key → ℝ) : Integer.Sparse.eval row8715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8715, Integer.Sparse.eval_collectBalanced, rawRowCheck8715]

def rawRow8716 : Integer.Sparse Key := [(key2511, -24), (key2447, 6), (key2447, 6), (key2447, 6), (key2352, 6)]

theorem rawRowCheck8716 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form6 = rawRow8716 := by decide +kernel

def row8716 : Integer.Sparse Key := [(key2352, 6), (key2447, 18), (key2511, -24)]

theorem rowCheck8716 : row8716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8716 := by decide +kernel

theorem rowEval8716 (x : Key → ℝ) : Integer.Sparse.eval row8716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck8716, Integer.Sparse.eval_collectBalanced, rawRowCheck8716]

def rawRow8717 : Integer.Sparse Key := [(key2584, -2), (key2588, -2), (key2588, -2), (key2584, -2), (key2588, -2), (key2584, -2), (key2599, -2), (key2588, -2), (key2599, -2), (key2588, -2), (key2588, -2), (key2599, -2), (key2763, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2930, 2)]

theorem rawRowCheck8717 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form7 = rawRow8717 := by decide +kernel

def row8717 : Integer.Sparse Key := [(key2584, -6), (key2588, -12), (key2599, -6), (key2763, 6), (key2767, 12), (key2930, 6)]

theorem rowCheck8717 : row8717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8717 := by decide +kernel

theorem rowEval8717 (x : Key → ℝ) : Integer.Sparse.eval row8717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8717, Integer.Sparse.eval_collectBalanced, rawRowCheck8717]

def rawRow8718 : Integer.Sparse Key := [(key2588, -2), (key2584, -2), (key2588, -2), (key2588, -2), (key2584, -2), (key2599, -2), (key2584, -2), (key2599, -2), (key2588, -2), (key2588, -2), (key2599, -2), (key2588, -2), (key2767, 2), (key2763, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2930, 2), (key2767, 2)]

theorem rawRowCheck8718 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form7 = rawRow8718 := by decide +kernel

def row8718 : Integer.Sparse Key := [(key2584, -6), (key2588, -12), (key2599, -6), (key2763, 6), (key2767, 12), (key2930, 6)]

theorem rowCheck8718 : row8718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8718 := by decide +kernel

theorem rowEval8718 (x : Key → ℝ) : Integer.Sparse.eval row8718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8718, Integer.Sparse.eval_collectBalanced, rawRowCheck8718]

def rawRow8719 : Integer.Sparse Key := [(key2588, -2), (key2588, -2), (key2584, -2), (key2599, -2), (key2599, -2), (key2588, -2), (key2588, -2), (key2584, -2), (key2584, -2), (key2599, -2), (key2588, -2), (key2588, -2), (key2767, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2767, 2)]

theorem rawRowCheck8719 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form7 = rawRow8719 := by decide +kernel

def row8719 : Integer.Sparse Key := [(key2584, -6), (key2588, -12), (key2599, -6), (key2763, 6), (key2767, 12), (key2930, 6)]

theorem rowCheck8719 : row8719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8719 := by decide +kernel

theorem rowEval8719 (x : Key → ℝ) : Integer.Sparse.eval row8719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8719, Integer.Sparse.eval_collectBalanced, rawRowCheck8719]

def rawRow8720 : Integer.Sparse Key := [(key2599, -2), (key2599, -2), (key2599, -2), (key2588, -2), (key2588, -2), (key2588, -2), (key2588, -2), (key2588, -2), (key2588, -2), (key2584, -2), (key2584, -2), (key2584, -2), (key2930, 2), (key2930, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2763, 2), (key2763, 2)]

theorem rawRowCheck8720 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8720 := by decide +kernel

def row8720 : Integer.Sparse Key := [(key2584, -6), (key2588, -12), (key2599, -6), (key2763, 6), (key2767, 12), (key2930, 6)]

theorem rowCheck8720 : row8720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8720 := by decide +kernel

theorem rowEval8720 (x : Key → ℝ) : Integer.Sparse.eval row8720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8720, Integer.Sparse.eval_collectBalanced, rawRowCheck8720]

def rawRow8721 : Integer.Sparse Key := [(key2930, -2), (key2930, -2), (key2930, -2), (key2967, -2), (key2967, -2), (key2967, -2), (key2967, -2), (key2967, -2), (key2967, -2), (key2988, -2), (key2988, -2), (key2988, -2), (key2599, 2), (key2599, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2909, 2), (key2909, 2)]

theorem rawRowCheck8721 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8721 := by decide +kernel

def row8721 : Integer.Sparse Key := [(key2599, 6), (key2888, 12), (key2909, 6), (key2930, -6), (key2967, -12), (key2988, -6)]

theorem rowCheck8721 : row8721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8721 := by decide +kernel

theorem rowEval8721 (x : Key → ℝ) : Integer.Sparse.eval row8721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8721, Integer.Sparse.eval_collectBalanced, rawRowCheck8721]

def rawRow8722 : Integer.Sparse Key := [(key2967, -2), (key2967, -2), (key2988, -2), (key2930, -2), (key2930, -2), (key2967, -2), (key2967, -2), (key2988, -2), (key2988, -2), (key2930, -2), (key2967, -2), (key2967, -2), (key2888, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2888, 2)]

theorem rawRowCheck8722 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form7 = rawRow8722 := by decide +kernel

def row8722 : Integer.Sparse Key := [(key2599, 6), (key2888, 12), (key2909, 6), (key2930, -6), (key2967, -12), (key2988, -6)]

theorem rowCheck8722 : row8722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8722 := by decide +kernel

theorem rowEval8722 (x : Key → ℝ) : Integer.Sparse.eval row8722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8722, Integer.Sparse.eval_collectBalanced, rawRowCheck8722]

def rawRow8723 : Integer.Sparse Key := [(key2967, -2), (key2988, -2), (key2967, -2), (key2967, -2), (key2988, -2), (key2930, -2), (key2988, -2), (key2930, -2), (key2967, -2), (key2967, -2), (key2930, -2), (key2967, -2), (key2888, 2), (key2909, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2599, 2), (key2888, 2)]

theorem rawRowCheck8723 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form7 = rawRow8723 := by decide +kernel

def row8723 : Integer.Sparse Key := [(key2599, 6), (key2888, 12), (key2909, 6), (key2930, -6), (key2967, -12), (key2988, -6)]

theorem rowCheck8723 : row8723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8723 := by decide +kernel

theorem rowEval8723 (x : Key → ℝ) : Integer.Sparse.eval row8723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8723, Integer.Sparse.eval_collectBalanced, rawRowCheck8723]

def rawRow8724 : Integer.Sparse Key := [(key2988, -2), (key2967, -2), (key2967, -2), (key2988, -2), (key2967, -2), (key2988, -2), (key2930, -2), (key2967, -2), (key2930, -2), (key2967, -2), (key2967, -2), (key2930, -2), (key2909, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2599, 2)]

theorem rawRowCheck8724 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form7 = rawRow8724 := by decide +kernel

def row8724 : Integer.Sparse Key := [(key2599, 6), (key2888, 12), (key2909, 6), (key2930, -6), (key2967, -12), (key2988, -6)]

theorem rowCheck8724 : row8724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8724 := by decide +kernel

theorem rowEval8724 (x : Key → ℝ) : Integer.Sparse.eval row8724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck8724, Integer.Sparse.eval_collectBalanced, rawRowCheck8724]

def rawRow8725 : Integer.Sparse Key := [(key1527, -2), (key1532, -2), (key1532, -2), (key1527, -2), (key1532, -2), (key1527, -2), (key1766, -2), (key1532, -2), (key1766, -2), (key1532, -2), (key1532, -2), (key1766, -2), (key1605, 1), (key1610, 1), (key1605, 1), (key1649, 1), (key1610, 1), (key1649, 1), (key1605, 1), (key1610, 1), (key1605, 1), (key1807, 1), (key1610, 1), (key1807, 1), (key1605, 1), (key1649, 1), (key1605, 1), (key1807, 1), (key1649, 1), (key1807, 1), (key1610, 1), (key1649, 1), (key1610, 1), (key1807, 1), (key1649, 1), (key1807, 1)]

theorem rawRowCheck8725 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form8 = rawRow8725 := by decide +kernel

def row8725 : Integer.Sparse Key := [(key1527, -6), (key1532, -12), (key1605, 6), (key1610, 6), (key1649, 6), (key1766, -6), (key1807, 6)]

theorem rowCheck8725 : row8725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8725 := by decide +kernel

theorem rowEval8725 (x : Key → ℝ) : Integer.Sparse.eval row8725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8725, Integer.Sparse.eval_collectBalanced, rawRowCheck8725]

def rawRow8726 : Integer.Sparse Key := [(key1532, -2), (key1527, -2), (key1532, -2), (key1532, -2), (key1527, -2), (key1766, -2), (key1527, -2), (key1766, -2), (key1532, -2), (key1532, -2), (key1766, -2), (key1532, -2), (key1610, 1), (key1605, 1), (key1649, 1), (key1605, 1), (key1649, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1807, 1), (key1605, 1), (key1807, 1), (key1610, 1), (key1649, 1), (key1605, 1), (key1807, 1), (key1605, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1610, 1), (key1807, 1), (key1610, 1), (key1807, 1), (key1649, 1)]

theorem rawRowCheck8726 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form8 = rawRow8726 := by decide +kernel

def row8726 : Integer.Sparse Key := [(key1527, -6), (key1532, -12), (key1605, 6), (key1610, 6), (key1649, 6), (key1766, -6), (key1807, 6)]

theorem rowCheck8726 : row8726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8726 := by decide +kernel

theorem rowEval8726 (x : Key → ℝ) : Integer.Sparse.eval row8726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8726, Integer.Sparse.eval_collectBalanced, rawRowCheck8726]

def rawRow8727 : Integer.Sparse Key := [(key1532, -2), (key1532, -2), (key1527, -2), (key1766, -2), (key1766, -2), (key1532, -2), (key1532, -2), (key1527, -2), (key1527, -2), (key1766, -2), (key1532, -2), (key1532, -2), (key1649, 1), (key1649, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1), (key1807, 1), (key1807, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1), (key1807, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1605, 1), (key1605, 1), (key1807, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1610, 1), (key1610, 1)]

theorem rawRowCheck8727 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form8 = rawRow8727 := by decide +kernel

def row8727 : Integer.Sparse Key := [(key1527, -6), (key1532, -12), (key1605, 6), (key1610, 6), (key1649, 6), (key1766, -6), (key1807, 6)]

theorem rowCheck8727 : row8727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8727 := by decide +kernel

theorem rowEval8727 (x : Key → ℝ) : Integer.Sparse.eval row8727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8727, Integer.Sparse.eval_collectBalanced, rawRowCheck8727]

def rawRow8728 : Integer.Sparse Key := [(key1766, -2), (key1766, -2), (key1766, -2), (key1532, -2), (key1532, -2), (key1532, -2), (key1532, -2), (key1532, -2), (key1532, -2), (key1527, -2), (key1527, -2), (key1527, -2), (key1807, 1), (key1807, 1), (key1807, 1), (key1807, 1), (key1807, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1), (key1605, 1), (key1605, 1), (key1605, 1), (key1605, 1)]

theorem rawRowCheck8728 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form8 = rawRow8728 := by decide +kernel

def row8728 : Integer.Sparse Key := [(key1527, -6), (key1532, -12), (key1605, 6), (key1610, 6), (key1649, 6), (key1766, -6), (key1807, 6)]

theorem rowCheck8728 : row8728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8728 := by decide +kernel

theorem rowEval8728 (x : Key → ℝ) : Integer.Sparse.eval row8728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8728, Integer.Sparse.eval_collectBalanced, rawRowCheck8728]

def rawRow8729 : Integer.Sparse Key := [(key1266, -2), (key1266, -2), (key1266, -2), (key1649, -2), (key1649, -2), (key1649, -2), (key1649, -2), (key1649, -2), (key1649, -2), (key1672, -2), (key1672, -2), (key1672, -2), (key1257, 1), (key1257, 1), (key1257, 1), (key1257, 1), (key1257, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1), (key1638, 1), (key1638, 1), (key1638, 1), (key1638, 1)]

theorem rawRowCheck8729 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form8 = rawRow8729 := by decide +kernel

def row8729 : Integer.Sparse Key := [(key1257, 6), (key1266, -6), (key1532, 6), (key1610, 6), (key1638, 6), (key1649, -12), (key1672, -6)]

theorem rowCheck8729 : row8729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8729 := by decide +kernel

theorem rowEval8729 (x : Key → ℝ) : Integer.Sparse.eval row8729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8729, Integer.Sparse.eval_collectBalanced, rawRowCheck8729]

def rawRow8730 : Integer.Sparse Key := [(key1649, -2), (key1649, -2), (key1672, -2), (key1266, -2), (key1266, -2), (key1649, -2), (key1649, -2), (key1672, -2), (key1672, -2), (key1266, -2), (key1649, -2), (key1649, -2), (key1532, 1), (key1532, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1), (key1257, 1), (key1257, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1), (key1257, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1638, 1), (key1638, 1), (key1257, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1610, 1), (key1610, 1)]

theorem rawRowCheck8730 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form8 = rawRow8730 := by decide +kernel

def row8730 : Integer.Sparse Key := [(key1257, 6), (key1266, -6), (key1532, 6), (key1610, 6), (key1638, 6), (key1649, -12), (key1672, -6)]

theorem rowCheck8730 : row8730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8730 := by decide +kernel

theorem rowEval8730 (x : Key → ℝ) : Integer.Sparse.eval row8730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8730, Integer.Sparse.eval_collectBalanced, rawRowCheck8730]

def rawRow8731 : Integer.Sparse Key := [(key1649, -2), (key1672, -2), (key1649, -2), (key1649, -2), (key1672, -2), (key1266, -2), (key1672, -2), (key1266, -2), (key1649, -2), (key1649, -2), (key1266, -2), (key1649, -2), (key1610, 1), (key1638, 1), (key1532, 1), (key1638, 1), (key1532, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1257, 1), (key1638, 1), (key1257, 1), (key1610, 1), (key1532, 1), (key1638, 1), (key1257, 1), (key1638, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1610, 1), (key1257, 1), (key1610, 1), (key1257, 1), (key1532, 1)]

theorem rawRowCheck8731 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form8 = rawRow8731 := by decide +kernel

def row8731 : Integer.Sparse Key := [(key1257, 6), (key1266, -6), (key1532, 6), (key1610, 6), (key1638, 6), (key1649, -12), (key1672, -6)]

theorem rowCheck8731 : row8731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8731 := by decide +kernel

theorem rowEval8731 (x : Key → ℝ) : Integer.Sparse.eval row8731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8731, Integer.Sparse.eval_collectBalanced, rawRowCheck8731]

def rawRow8732 : Integer.Sparse Key := [(key1672, -2), (key1649, -2), (key1649, -2), (key1672, -2), (key1649, -2), (key1672, -2), (key1266, -2), (key1649, -2), (key1266, -2), (key1649, -2), (key1649, -2), (key1266, -2), (key1638, 1), (key1610, 1), (key1638, 1), (key1532, 1), (key1610, 1), (key1532, 1), (key1638, 1), (key1610, 1), (key1638, 1), (key1257, 1), (key1610, 1), (key1257, 1), (key1638, 1), (key1532, 1), (key1638, 1), (key1257, 1), (key1532, 1), (key1257, 1), (key1610, 1), (key1532, 1), (key1610, 1), (key1257, 1), (key1532, 1), (key1257, 1)]

theorem rawRowCheck8732 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form8 = rawRow8732 := by decide +kernel

def row8732 : Integer.Sparse Key := [(key1257, 6), (key1266, -6), (key1532, 6), (key1610, 6), (key1638, 6), (key1649, -12), (key1672, -6)]

theorem rowCheck8732 : row8732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8732 := by decide +kernel

theorem rowEval8732 (x : Key → ℝ) : Integer.Sparse.eval row8732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck8732, Integer.Sparse.eval_collectBalanced, rawRowCheck8732]

def rawRow8733 : Integer.Sparse Key := [(key2840, 1), (key2844, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2888, 1), (key2840, 1), (key2844, 1), (key2840, 1), (key2967, 1), (key2844, 1), (key2967, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2967, 1), (key2844, 1), (key2888, 1), (key2844, 1), (key2967, 1), (key2888, 1), (key2967, 1), (key2875, -2), (key2875, -2), (key2909, -2), (key2875, -2), (key2875, -2), (key2988, -2), (key2875, -2), (key2909, -2), (key2875, -2), (key2988, -2), (key2909, -2), (key2988, -2)]

theorem rawRowCheck8733 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form9 = rawRow8733 := by decide +kernel

def row8733 : Integer.Sparse Key := [(key2840, 6), (key2844, 6), (key2875, -12), (key2888, 6), (key2909, -6), (key2967, 6), (key2988, -6)]

theorem rowCheck8733 : row8733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8733 := by decide +kernel

theorem rowEval8733 (x : Key → ℝ) : Integer.Sparse.eval row8733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8733, Integer.Sparse.eval_collectBalanced, rawRowCheck8733]

def rawRow8734 : Integer.Sparse Key := [(key2844, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2844, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2967, 1), (key2844, 1), (key2967, 1), (key2888, 1), (key2875, -2), (key2909, -2), (key2875, -2), (key2875, -2), (key2988, -2), (key2875, -2), (key2909, -2), (key2875, -2), (key2988, -2), (key2875, -2), (key2988, -2), (key2909, -2)]

theorem rawRowCheck8734 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form9 = rawRow8734 := by decide +kernel

def row8734 : Integer.Sparse Key := [(key2840, 6), (key2844, 6), (key2875, -12), (key2888, 6), (key2909, -6), (key2967, 6), (key2988, -6)]

theorem rowCheck8734 : row8734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8734 := by decide +kernel

theorem rowEval8734 (x : Key → ℝ) : Integer.Sparse.eval row8734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8734, Integer.Sparse.eval_collectBalanced, rawRowCheck8734]

def rawRow8735 : Integer.Sparse Key := [(key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2909, -2), (key2875, -2), (key2875, -2), (key2988, -2), (key2875, -2), (key2875, -2), (key2988, -2), (key2988, -2), (key2909, -2), (key2909, -2), (key2875, -2), (key2875, -2)]

theorem rawRowCheck8735 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form9 = rawRow8735 := by decide +kernel

def row8735 : Integer.Sparse Key := [(key2840, 6), (key2844, 6), (key2875, -12), (key2888, 6), (key2909, -6), (key2967, 6), (key2988, -6)]

theorem rowCheck8735 : row8735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8735 := by decide +kernel

theorem rowEval8735 (x : Key → ℝ) : Integer.Sparse.eval row8735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8735, Integer.Sparse.eval_collectBalanced, rawRowCheck8735]

def rawRow8736 : Integer.Sparse Key := [(key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2988, -2), (key2988, -2), (key2988, -2), (key2909, -2), (key2909, -2), (key2909, -2), (key2875, -2), (key2875, -2), (key2875, -2), (key2875, -2), (key2875, -2), (key2875, -2)]

theorem rawRowCheck8736 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form9 = rawRow8736 := by decide +kernel

def row8736 : Integer.Sparse Key := [(key2840, 6), (key2844, 6), (key2875, -12), (key2888, 6), (key2909, -6), (key2967, 6), (key2988, -6)]

theorem rowCheck8736 : row8736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8736 := by decide +kernel

theorem rowEval8736 (x : Key → ℝ) : Integer.Sparse.eval row8736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8736, Integer.Sparse.eval_collectBalanced, rawRowCheck8736]

def rawRow8737 : Integer.Sparse Key := [(key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2584, -2), (key2584, -2), (key2584, -2), (key2763, -2), (key2763, -2), (key2763, -2), (key2840, -2), (key2840, -2), (key2840, -2), (key2840, -2), (key2840, -2), (key2840, -2)]

theorem rawRowCheck8737 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form9 = rawRow8737 := by decide +kernel

def row8737 : Integer.Sparse Key := [(key2584, -6), (key2588, 6), (key2763, -6), (key2767, 6), (key2840, -12), (key2844, 6), (key2875, 6)]

theorem rowCheck8737 : row8737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8737 := by decide +kernel

theorem rowEval8737 (x : Key → ℝ) : Integer.Sparse.eval row8737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8737, Integer.Sparse.eval_collectBalanced, rawRowCheck8737]

def rawRow8738 : Integer.Sparse Key := [(key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2763, -2), (key2840, -2), (key2840, -2), (key2584, -2), (key2840, -2), (key2840, -2), (key2584, -2), (key2584, -2), (key2763, -2), (key2763, -2), (key2840, -2), (key2840, -2)]

theorem rawRowCheck8738 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form9 = rawRow8738 := by decide +kernel

def row8738 : Integer.Sparse Key := [(key2584, -6), (key2588, 6), (key2763, -6), (key2767, 6), (key2840, -12), (key2844, 6), (key2875, 6)]

theorem rowCheck8738 : row8738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8738 := by decide +kernel

theorem rowEval8738 (x : Key → ℝ) : Integer.Sparse.eval row8738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8738, Integer.Sparse.eval_collectBalanced, rawRowCheck8738]

def rawRow8739 : Integer.Sparse Key := [(key2844, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2844, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2588, 1), (key2844, 1), (key2588, 1), (key2767, 1), (key2840, -2), (key2763, -2), (key2840, -2), (key2840, -2), (key2584, -2), (key2840, -2), (key2763, -2), (key2840, -2), (key2584, -2), (key2840, -2), (key2584, -2), (key2763, -2)]

theorem rawRowCheck8739 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form9 = rawRow8739 := by decide +kernel

def row8739 : Integer.Sparse Key := [(key2584, -6), (key2588, 6), (key2763, -6), (key2767, 6), (key2840, -12), (key2844, 6), (key2875, 6)]

theorem rowCheck8739 : row8739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8739 := by decide +kernel

theorem rowEval8739 (x : Key → ℝ) : Integer.Sparse.eval row8739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8739, Integer.Sparse.eval_collectBalanced, rawRowCheck8739]

def rawRow8740 : Integer.Sparse Key := [(key2875, 1), (key2844, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2767, 1), (key2875, 1), (key2844, 1), (key2875, 1), (key2588, 1), (key2844, 1), (key2588, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2588, 1), (key2844, 1), (key2767, 1), (key2844, 1), (key2588, 1), (key2767, 1), (key2588, 1), (key2840, -2), (key2840, -2), (key2763, -2), (key2840, -2), (key2840, -2), (key2584, -2), (key2840, -2), (key2763, -2), (key2840, -2), (key2584, -2), (key2763, -2), (key2584, -2)]

theorem rawRowCheck8740 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form9 = rawRow8740 := by decide +kernel

def row8740 : Integer.Sparse Key := [(key2584, -6), (key2588, 6), (key2763, -6), (key2767, 6), (key2840, -12), (key2844, 6), (key2875, 6)]

theorem rowCheck8740 : row8740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8740 := by decide +kernel

theorem rowEval8740 (x : Key → ℝ) : Integer.Sparse.eval row8740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck8740, Integer.Sparse.eval_collectBalanced, rawRowCheck8740]

def rawRow8741 : Integer.Sparse Key := [(key1524, -6), (key1524, -6), (key1524, -6), (key1762, -6), (key1602, 2), (key1602, 2), (key1645, 2), (key1602, 2), (key1602, 2), (key1803, 2), (key1602, 2), (key1645, 2), (key1602, 2), (key1803, 2), (key1645, 2), (key1803, 2)]

theorem rawRowCheck8741 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form10 = rawRow8741 := by decide +kernel

def row8741 : Integer.Sparse Key := [(key1524, -18), (key1602, 12), (key1645, 6), (key1762, -6), (key1803, 6)]

theorem rowCheck8741 : row8741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8741 := by decide +kernel

theorem rowEval8741 (x : Key → ℝ) : Integer.Sparse.eval row8741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck8741, Integer.Sparse.eval_collectBalanced, rawRowCheck8741]

def rawRow8742 : Integer.Sparse Key := [(key1524, -6), (key1524, -6), (key1762, -6), (key1524, -6), (key1602, 2), (key1645, 2), (key1602, 2), (key1602, 2), (key1803, 2), (key1602, 2), (key1645, 2), (key1602, 2), (key1803, 2), (key1602, 2), (key1803, 2), (key1645, 2)]

theorem rawRowCheck8742 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form10 = rawRow8742 := by decide +kernel

def row8742 : Integer.Sparse Key := [(key1524, -18), (key1602, 12), (key1645, 6), (key1762, -6), (key1803, 6)]

theorem rowCheck8742 : row8742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8742 := by decide +kernel

theorem rowEval8742 (x : Key → ℝ) : Integer.Sparse.eval row8742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8742, Integer.Sparse.eval_collectBalanced, rawRowCheck8742]

def rawRow8743 : Integer.Sparse Key := [(key1524, -6), (key1762, -6), (key1524, -6), (key1524, -6), (key1645, 2), (key1602, 2), (key1602, 2), (key1803, 2), (key1602, 2), (key1602, 2), (key1803, 2), (key1803, 2), (key1645, 2), (key1645, 2), (key1602, 2), (key1602, 2)]

theorem rawRowCheck8743 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form10 = rawRow8743 := by decide +kernel

def row8743 : Integer.Sparse Key := [(key1524, -18), (key1602, 12), (key1645, 6), (key1762, -6), (key1803, 6)]

theorem rowCheck8743 : row8743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8743 := by decide +kernel

theorem rowEval8743 (x : Key → ℝ) : Integer.Sparse.eval row8743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8743, Integer.Sparse.eval_collectBalanced, rawRowCheck8743]

def rawRow8744 : Integer.Sparse Key := [(key1762, -6), (key1524, -6), (key1524, -6), (key1524, -6), (key1803, 2), (key1803, 2), (key1803, 2), (key1645, 2), (key1645, 2), (key1645, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2)]

theorem rawRowCheck8744 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form10 = rawRow8744 := by decide +kernel

def row8744 : Integer.Sparse Key := [(key1524, -18), (key1602, 12), (key1645, 6), (key1762, -6), (key1803, 6)]

theorem rowCheck8744 : row8744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8744 := by decide +kernel

theorem rowEval8744 (x : Key → ℝ) : Integer.Sparse.eval row8744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8744, Integer.Sparse.eval_collectBalanced, rawRowCheck8744]

def rawRow8745 : Integer.Sparse Key := [(key1262, -6), (key1645, -6), (key1645, -6), (key1645, -6), (key1249, 2), (key1249, 2), (key1249, 2), (key1524, 2), (key1524, 2), (key1524, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2)]

theorem rawRowCheck8745 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form10 = rawRow8745 := by decide +kernel

def row8745 : Integer.Sparse Key := [(key1249, 6), (key1262, -6), (key1524, 6), (key1602, 12), (key1645, -18)]

theorem rowCheck8745 : row8745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8745 := by decide +kernel

theorem rowEval8745 (x : Key → ℝ) : Integer.Sparse.eval row8745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8745, Integer.Sparse.eval_collectBalanced, rawRowCheck8745]

def rawRow8746 : Integer.Sparse Key := [(key1645, -6), (key1262, -6), (key1645, -6), (key1645, -6), (key1524, 2), (key1602, 2), (key1602, 2), (key1249, 2), (key1602, 2), (key1602, 2), (key1249, 2), (key1249, 2), (key1524, 2), (key1524, 2), (key1602, 2), (key1602, 2)]

theorem rawRowCheck8746 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form10 = rawRow8746 := by decide +kernel

def row8746 : Integer.Sparse Key := [(key1249, 6), (key1262, -6), (key1524, 6), (key1602, 12), (key1645, -18)]

theorem rowCheck8746 : row8746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8746 := by decide +kernel

theorem rowEval8746 (x : Key → ℝ) : Integer.Sparse.eval row8746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8746, Integer.Sparse.eval_collectBalanced, rawRowCheck8746]

def rawRow8747 : Integer.Sparse Key := [(key1645, -6), (key1645, -6), (key1262, -6), (key1645, -6), (key1602, 2), (key1524, 2), (key1602, 2), (key1602, 2), (key1249, 2), (key1602, 2), (key1524, 2), (key1602, 2), (key1249, 2), (key1602, 2), (key1249, 2), (key1524, 2)]

theorem rawRowCheck8747 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form10 = rawRow8747 := by decide +kernel

def row8747 : Integer.Sparse Key := [(key1249, 6), (key1262, -6), (key1524, 6), (key1602, 12), (key1645, -18)]

theorem rowCheck8747 : row8747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8747 := by decide +kernel

theorem rowEval8747 (x : Key → ℝ) : Integer.Sparse.eval row8747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8747, Integer.Sparse.eval_collectBalanced, rawRowCheck8747]

def rawRow8748 : Integer.Sparse Key := [(key1645, -6), (key1645, -6), (key1645, -6), (key1262, -6), (key1602, 2), (key1602, 2), (key1524, 2), (key1602, 2), (key1602, 2), (key1249, 2), (key1602, 2), (key1524, 2), (key1602, 2), (key1249, 2), (key1524, 2), (key1249, 2)]

theorem rawRowCheck8748 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form10 = rawRow8748 := by decide +kernel

def row8748 : Integer.Sparse Key := [(key1249, 6), (key1262, -6), (key1524, 6), (key1602, 12), (key1645, -18)]

theorem rowCheck8748 : row8748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8748 := by decide +kernel

theorem rowEval8748 (x : Key → ℝ) : Integer.Sparse.eval row8748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck8748, Integer.Sparse.eval_collectBalanced, rawRowCheck8748]

def rawRow8749 : Integer.Sparse Key := [(key2353, 6), (key2356, 6), (key2356, 6), (key2356, 6), (key2527, -6), (key2527, -6), (key2527, -6), (key2558, -6)]

theorem rawRowCheck8749 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form11 = rawRow8749 := by decide +kernel

def row8749 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2527, -18), (key2558, -6)]

theorem rowCheck8749 : row8749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8749 := by decide +kernel

theorem rowEval8749 (x : Key → ℝ) : Integer.Sparse.eval row8749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck8749, Integer.Sparse.eval_collectBalanced, rawRowCheck8749]

def rawRow8750 : Integer.Sparse Key := [(key2356, 6), (key2353, 6), (key2356, 6), (key2356, 6), (key2527, -6), (key2527, -6), (key2558, -6), (key2527, -6)]

theorem rawRowCheck8750 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form11 = rawRow8750 := by decide +kernel

def row8750 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2527, -18), (key2558, -6)]

theorem rowCheck8750 : row8750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8750 := by decide +kernel

theorem rowEval8750 (x : Key → ℝ) : Integer.Sparse.eval row8750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8750, Integer.Sparse.eval_collectBalanced, rawRowCheck8750]

def rawRow8751 : Integer.Sparse Key := [(key2356, 6), (key2356, 6), (key2353, 6), (key2356, 6), (key2527, -6), (key2558, -6), (key2527, -6), (key2527, -6)]

theorem rawRowCheck8751 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form11 = rawRow8751 := by decide +kernel

def row8751 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2527, -18), (key2558, -6)]

theorem rowCheck8751 : row8751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8751 := by decide +kernel

theorem rowEval8751 (x : Key → ℝ) : Integer.Sparse.eval row8751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8751, Integer.Sparse.eval_collectBalanced, rawRowCheck8751]

def rawRow8752 : Integer.Sparse Key := [(key2356, 6), (key2356, 6), (key2356, 6), (key2353, 6), (key2558, -6), (key2527, -6), (key2527, -6), (key2527, -6)]

theorem rawRowCheck8752 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form11 = rawRow8752 := by decide +kernel

def row8752 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2527, -18), (key2558, -6)]

theorem rowCheck8752 : row8752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8752 := by decide +kernel

theorem rowEval8752 (x : Key → ℝ) : Integer.Sparse.eval row8752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8752, Integer.Sparse.eval_collectBalanced, rawRowCheck8752]

def rawRow8753 : Integer.Sparse Key := [(key2527, 6), (key2527, 6), (key2527, 6), (key2558, 6), (key2353, -6), (key2448, -6), (key2448, -6), (key2448, -6)]

theorem rawRowCheck8753 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form11 = rawRow8753 := by decide +kernel

def row8753 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2527, 18), (key2558, 6)]

theorem rowCheck8753 : row8753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8753 := by decide +kernel

theorem rowEval8753 (x : Key → ℝ) : Integer.Sparse.eval row8753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8753, Integer.Sparse.eval_collectBalanced, rawRowCheck8753]

def rawRow8754 : Integer.Sparse Key := [(key2527, 6), (key2527, 6), (key2558, 6), (key2527, 6), (key2448, -6), (key2353, -6), (key2448, -6), (key2448, -6)]

theorem rawRowCheck8754 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form11 = rawRow8754 := by decide +kernel

def row8754 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2527, 18), (key2558, 6)]

theorem rowCheck8754 : row8754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8754 := by decide +kernel

theorem rowEval8754 (x : Key → ℝ) : Integer.Sparse.eval row8754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8754, Integer.Sparse.eval_collectBalanced, rawRowCheck8754]

def rawRow8755 : Integer.Sparse Key := [(key2527, 6), (key2558, 6), (key2527, 6), (key2527, 6), (key2448, -6), (key2448, -6), (key2353, -6), (key2448, -6)]

theorem rawRowCheck8755 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form11 = rawRow8755 := by decide +kernel

def row8755 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2527, 18), (key2558, 6)]

theorem rowCheck8755 : row8755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8755 := by decide +kernel

theorem rowEval8755 (x : Key → ℝ) : Integer.Sparse.eval row8755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8755, Integer.Sparse.eval_collectBalanced, rawRowCheck8755]

def rawRow8756 : Integer.Sparse Key := [(key2558, 6), (key2527, 6), (key2527, 6), (key2527, 6), (key2448, -6), (key2448, -6), (key2448, -6), (key2353, -6)]

theorem rawRowCheck8756 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form11 = rawRow8756 := by decide +kernel

def row8756 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2527, 18), (key2558, 6)]

theorem rowCheck8756 : row8756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8756 := by decide +kernel

theorem rowEval8756 (x : Key → ℝ) : Integer.Sparse.eval row8756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck8756, Integer.Sparse.eval_collectBalanced, rawRowCheck8756]

def rawRow8757 : Integer.Sparse Key := [(key2366, 2), (key2366, 2), (key2366, 2), (key2461, 2), (key2461, 2), (key2461, 2), (key2523, 2), (key2523, 2), (key2523, 2), (key2523, 2), (key2523, 2), (key2523, 2), (key2361, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2517, -2)]

theorem rawRowCheck8757 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form0 = rawRow8757 := by decide +kernel

def row8757 : Integer.Sparse Key := [(key2361, -6), (key2366, 6), (key2456, -12), (key2461, 6), (key2517, -6), (key2523, 12)]

theorem rowCheck8757 : row8757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8757 := by decide +kernel

theorem rowEval8757 (x : Key → ℝ) : Integer.Sparse.eval row8757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8757, Integer.Sparse.eval_collectBalanced, rawRowCheck8757]

def rawRow8758 : Integer.Sparse Key := [(key2461, 2), (key2523, 2), (key2523, 2), (key2366, 2), (key2523, 2), (key2523, 2), (key2366, 2), (key2366, 2), (key2461, 2), (key2461, 2), (key2523, 2), (key2523, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, -2)]

theorem rawRowCheck8758 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form0 = rawRow8758 := by decide +kernel

def row8758 : Integer.Sparse Key := [(key2361, -6), (key2366, 6), (key2456, -12), (key2461, 6), (key2517, -6), (key2523, 12)]

theorem rowCheck8758 : row8758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8758 := by decide +kernel

theorem rowEval8758 (x : Key → ℝ) : Integer.Sparse.eval row8758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8758, Integer.Sparse.eval_collectBalanced, rawRowCheck8758]

def rawRow8759 : Integer.Sparse Key := [(key2523, 2), (key2461, 2), (key2523, 2), (key2523, 2), (key2366, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2366, 2), (key2523, 2), (key2366, 2), (key2461, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2361, -2), (key2456, -2)]

theorem rawRowCheck8759 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form0 = rawRow8759 := by decide +kernel

def row8759 : Integer.Sparse Key := [(key2361, -6), (key2366, 6), (key2456, -12), (key2461, 6), (key2517, -6), (key2523, 12)]

theorem rowCheck8759 : row8759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8759 := by decide +kernel

theorem rowEval8759 (x : Key → ℝ) : Integer.Sparse.eval row8759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8759, Integer.Sparse.eval_collectBalanced, rawRowCheck8759]

def rawRow8760 : Integer.Sparse Key := [(key2523, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2523, 2), (key2366, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2366, 2), (key2461, 2), (key2366, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2361, -2)]

theorem rawRowCheck8760 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form0 = rawRow8760 := by decide +kernel

def row8760 : Integer.Sparse Key := [(key2361, -6), (key2366, 6), (key2456, -12), (key2461, 6), (key2517, -6), (key2523, 12)]

theorem rowCheck8760 : row8760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8760 := by decide +kernel

theorem rowEval8760 (x : Key → ℝ) : Integer.Sparse.eval row8760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck8760, Integer.Sparse.eval_collectBalanced, rawRowCheck8760]

def rawRow8761 : Integer.Sparse Key := [(key1226, -24), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6)]

theorem rawRowCheck8761 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form1 = rawRow8761 := by decide +kernel

def row8761 : Integer.Sparse Key := [(key970, 6), (key1084, 18), (key1226, -24)]

theorem rowCheck8761 : row8761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8761 := by decide +kernel

theorem rowEval8761 (x : Key → ℝ) : Integer.Sparse.eval row8761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8761, Integer.Sparse.eval_collectBalanced, rawRowCheck8761]

def rawRow8762 : Integer.Sparse Key := [(key1226, -24), (key1084, 6), (key970, 6), (key1084, 6), (key1084, 6)]

theorem rawRowCheck8762 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form1 = rawRow8762 := by decide +kernel

def row8762 : Integer.Sparse Key := [(key970, 6), (key1084, 18), (key1226, -24)]

theorem rowCheck8762 : row8762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8762 := by decide +kernel

theorem rowEval8762 (x : Key → ℝ) : Integer.Sparse.eval row8762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8762, Integer.Sparse.eval_collectBalanced, rawRowCheck8762]

def rawRow8763 : Integer.Sparse Key := [(key1226, -24), (key1084, 6), (key1084, 6), (key970, 6), (key1084, 6)]

theorem rawRowCheck8763 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form1 = rawRow8763 := by decide +kernel

def row8763 : Integer.Sparse Key := [(key970, 6), (key1084, 18), (key1226, -24)]

theorem rowCheck8763 : row8763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8763 := by decide +kernel

theorem rowEval8763 (x : Key → ℝ) : Integer.Sparse.eval row8763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8763, Integer.Sparse.eval_collectBalanced, rawRowCheck8763]

def rawRow8764 : Integer.Sparse Key := [(key1226, -24), (key1084, 6), (key1084, 6), (key1084, 6), (key970, 6)]

theorem rawRowCheck8764 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form1 = rawRow8764 := by decide +kernel

def row8764 : Integer.Sparse Key := [(key970, 6), (key1084, 18), (key1226, -24)]

theorem rowCheck8764 : row8764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8764 := by decide +kernel

theorem rowEval8764 (x : Key → ℝ) : Integer.Sparse.eval row8764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck8764, Integer.Sparse.eval_collectBalanced, rawRowCheck8764]

def rawRow8765 : Integer.Sparse Key := [(key1228, -6), (key1228, -6), (key1228, -6), (key1245, -6), (key979, 2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1164, 2), (key1164, 2)]

theorem rawRowCheck8765 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form2 = rawRow8765 := by decide +kernel

def row8765 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, 6), (key1228, -18), (key1245, -6)]

theorem rowCheck8765 : row8765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8765 := by decide +kernel

theorem rowEval8765 (x : Key → ℝ) : Integer.Sparse.eval row8765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8765, Integer.Sparse.eval_collectBalanced, rawRowCheck8765]

def rawRow8766 : Integer.Sparse Key := [(key1228, -6), (key1228, -6), (key1245, -6), (key1228, -6), (key1093, 2), (key1093, 2), (key1164, 2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1164, 2), (key979, 2), (key1093, 2), (key1093, 2)]

theorem rawRowCheck8766 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form2 = rawRow8766 := by decide +kernel

def row8766 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, 6), (key1228, -18), (key1245, -6)]

theorem rowCheck8766 : row8766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8766 := by decide +kernel

theorem rowEval8766 (x : Key → ℝ) : Integer.Sparse.eval row8766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8766, Integer.Sparse.eval_collectBalanced, rawRowCheck8766]

def rawRow8767 : Integer.Sparse Key := [(key1228, -6), (key1245, -6), (key1228, -6), (key1228, -6), (key1093, 2), (key1164, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1164, 2), (key979, 2), (key1093, 2), (key1093, 2), (key979, 2), (key1093, 2)]

theorem rawRowCheck8767 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form2 = rawRow8767 := by decide +kernel

def row8767 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, 6), (key1228, -18), (key1245, -6)]

theorem rowCheck8767 : row8767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8767 := by decide +kernel

theorem rowEval8767 (x : Key → ℝ) : Integer.Sparse.eval row8767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8767, Integer.Sparse.eval_collectBalanced, rawRowCheck8767]

def rawRow8768 : Integer.Sparse Key := [(key1245, -6), (key1228, -6), (key1228, -6), (key1228, -6), (key1164, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1093, 2), (key979, 2), (key1093, 2), (key1093, 2), (key979, 2)]

theorem rawRowCheck8768 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form2 = rawRow8768 := by decide +kernel

def row8768 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, 6), (key1228, -18), (key1245, -6)]

theorem rowCheck8768 : row8768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8768 := by decide +kernel

theorem rowEval8768 (x : Key → ℝ) : Integer.Sparse.eval row8768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck8768, Integer.Sparse.eval_collectBalanced, rawRowCheck8768]

def rawRow8769 : Integer.Sparse Key := [(key2385, -6), (key2475, -6), (key2475, -6), (key2475, -6), (key2372, 2), (key2372, 2), (key2372, 2), (key2400, 2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2)]

theorem rawRowCheck8769 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form3 = rawRow8769 := by decide +kernel

def row8769 : Integer.Sparse Key := [(key2372, 6), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, -18)]

theorem rowCheck8769 : row8769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8769 := by decide +kernel

theorem rowEval8769 (x : Key → ℝ) : Integer.Sparse.eval row8769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8769, Integer.Sparse.eval_collectBalanced, rawRowCheck8769]

def rawRow8770 : Integer.Sparse Key := [(key2475, -6), (key2385, -6), (key2475, -6), (key2475, -6), (key2400, 2), (key2466, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2466, 2), (key2372, 2), (key2372, 2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2)]

theorem rawRowCheck8770 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form3 = rawRow8770 := by decide +kernel

def row8770 : Integer.Sparse Key := [(key2372, 6), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, -18)]

theorem rowCheck8770 : row8770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8770 := by decide +kernel

theorem rowEval8770 (x : Key → ℝ) : Integer.Sparse.eval row8770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8770, Integer.Sparse.eval_collectBalanced, rawRowCheck8770]

def rawRow8771 : Integer.Sparse Key := [(key2475, -6), (key2475, -6), (key2385, -6), (key2475, -6), (key2466, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2400, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2372, 2), (key2400, 2)]

theorem rawRowCheck8771 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form3 = rawRow8771 := by decide +kernel

def row8771 : Integer.Sparse Key := [(key2372, 6), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, -18)]

theorem rowCheck8771 : row8771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8771 := by decide +kernel

theorem rowEval8771 (x : Key → ℝ) : Integer.Sparse.eval row8771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8771, Integer.Sparse.eval_collectBalanced, rawRowCheck8771]

def rawRow8772 : Integer.Sparse Key := [(key2475, -6), (key2475, -6), (key2475, -6), (key2385, -6), (key2466, 2), (key2466, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2400, 2), (key2466, 2), (key2372, 2), (key2400, 2), (key2372, 2)]

theorem rawRowCheck8772 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form3 = rawRow8772 := by decide +kernel

def row8772 : Integer.Sparse Key := [(key2372, 6), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, -18)]

theorem rowCheck8772 : row8772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8772 := by decide +kernel

theorem rowEval8772 (x : Key → ℝ) : Integer.Sparse.eval row8772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck8772, Integer.Sparse.eval_collectBalanced, rawRowCheck8772]

def rawRow8773 : Integer.Sparse Key := [(key2566, -6), (key2566, -6), (key2566, -6), (key2578, -6), (key2359, 2), (key2359, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2515, 2), (key2515, 2)]

theorem rawRowCheck8773 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form4 = rawRow8773 := by decide +kernel

def row8773 : Integer.Sparse Key := [(key2359, 6), (key2454, 12), (key2515, 6), (key2566, -18), (key2578, -6)]

theorem rowCheck8773 : row8773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8773 := by decide +kernel

theorem rowEval8773 (x : Key → ℝ) : Integer.Sparse.eval row8773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8773, Integer.Sparse.eval_collectBalanced, rawRowCheck8773]

def rawRow8774 : Integer.Sparse Key := [(key2566, -6), (key2566, -6), (key2578, -6), (key2566, -6), (key2454, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2454, 2)]

theorem rawRowCheck8774 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form4 = rawRow8774 := by decide +kernel

def row8774 : Integer.Sparse Key := [(key2359, 6), (key2454, 12), (key2515, 6), (key2566, -18), (key2578, -6)]

theorem rowCheck8774 : row8774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8774 := by decide +kernel

theorem rowEval8774 (x : Key → ℝ) : Integer.Sparse.eval row8774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8774, Integer.Sparse.eval_collectBalanced, rawRowCheck8774]

def rawRow8775 : Integer.Sparse Key := [(key2566, -6), (key2578, -6), (key2566, -6), (key2566, -6), (key2454, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2359, 2), (key2454, 2)]

theorem rawRowCheck8775 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form4 = rawRow8775 := by decide +kernel

def row8775 : Integer.Sparse Key := [(key2359, 6), (key2454, 12), (key2515, 6), (key2566, -18), (key2578, -6)]

theorem rowCheck8775 : row8775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8775 := by decide +kernel

theorem rowEval8775 (x : Key → ℝ) : Integer.Sparse.eval row8775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8775, Integer.Sparse.eval_collectBalanced, rawRowCheck8775]

def rawRow8776 : Integer.Sparse Key := [(key2578, -6), (key2566, -6), (key2566, -6), (key2566, -6), (key2515, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2359, 2)]

theorem rawRowCheck8776 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form4 = rawRow8776 := by decide +kernel

def row8776 : Integer.Sparse Key := [(key2359, 6), (key2454, 12), (key2515, 6), (key2566, -18), (key2578, -6)]

theorem rowCheck8776 : row8776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8776 := by decide +kernel

theorem rowEval8776 (x : Key → ℝ) : Integer.Sparse.eval row8776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck8776, Integer.Sparse.eval_collectBalanced, rawRowCheck8776]

def rawRow8777 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2404, -2), (key2398, -2), (key2404, -2), (key2398, -2), (key2435, -2), (key2404, -2), (key2435, -2), (key2404, -2), (key2404, -2), (key2435, -2), (key2464, 1), (key2470, 1), (key2464, 1), (key2478, 1), (key2470, 1), (key2478, 1), (key2464, 1), (key2470, 1), (key2464, 1), (key2501, 1), (key2470, 1), (key2501, 1), (key2464, 1), (key2478, 1), (key2464, 1), (key2501, 1), (key2478, 1), (key2501, 1), (key2470, 1), (key2478, 1), (key2470, 1), (key2501, 1), (key2478, 1), (key2501, 1)]

theorem rawRowCheck8777 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form5 = rawRow8777 := by decide +kernel

def row8777 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6)]

theorem rowCheck8777 : row8777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8777 := by decide +kernel

theorem rowEval8777 (x : Key → ℝ) : Integer.Sparse.eval row8777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8777, Integer.Sparse.eval_collectBalanced, rawRowCheck8777]

def rawRow8778 : Integer.Sparse Key := [(key2404, -2), (key2398, -2), (key2404, -2), (key2404, -2), (key2398, -2), (key2435, -2), (key2398, -2), (key2435, -2), (key2404, -2), (key2404, -2), (key2435, -2), (key2404, -2), (key2470, 1), (key2464, 1), (key2478, 1), (key2464, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2501, 1), (key2464, 1), (key2501, 1), (key2470, 1), (key2478, 1), (key2464, 1), (key2501, 1), (key2464, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2501, 1), (key2470, 1), (key2501, 1), (key2478, 1)]

theorem rawRowCheck8778 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form5 = rawRow8778 := by decide +kernel

def row8778 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6)]

theorem rowCheck8778 : row8778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8778 := by decide +kernel

theorem rowEval8778 (x : Key → ℝ) : Integer.Sparse.eval row8778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8778, Integer.Sparse.eval_collectBalanced, rawRowCheck8778]

def rawRow8779 : Integer.Sparse Key := [(key2404, -2), (key2404, -2), (key2398, -2), (key2435, -2), (key2435, -2), (key2404, -2), (key2404, -2), (key2398, -2), (key2398, -2), (key2435, -2), (key2404, -2), (key2404, -2), (key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1)]

theorem rawRowCheck8779 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form5 = rawRow8779 := by decide +kernel

def row8779 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6)]

theorem rowCheck8779 : row8779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8779 := by decide +kernel

theorem rowEval8779 (x : Key → ℝ) : Integer.Sparse.eval row8779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8779, Integer.Sparse.eval_collectBalanced, rawRowCheck8779]

def rawRow8780 : Integer.Sparse Key := [(key2435, -2), (key2435, -2), (key2435, -2), (key2404, -2), (key2404, -2), (key2404, -2), (key2404, -2), (key2404, -2), (key2404, -2), (key2398, -2), (key2398, -2), (key2398, -2), (key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1)]

theorem rawRowCheck8780 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form5 = rawRow8780 := by decide +kernel

def row8780 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6)]

theorem rowCheck8780 : row8780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8780 := by decide +kernel

theorem rowEval8780 (x : Key → ℝ) : Integer.Sparse.eval row8780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8780, Integer.Sparse.eval_collectBalanced, rawRowCheck8780]

def rawRow8781 : Integer.Sparse Key := [(key2604, -2), (key2604, -2), (key2604, -2), (key2916, -2), (key2916, -2), (key2916, -2), (key2916, -2), (key2916, -2), (key2916, -2), (key2925, -2), (key2925, -2), (key2925, -2), (key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1)]

theorem rawRowCheck8781 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form5 = rawRow8781 := by decide +kernel

def row8781 : Integer.Sparse Key := [(key2589, 6), (key2604, -6), (key2768, 6), (key2845, 6), (key2876, 6), (key2916, -12), (key2925, -6)]

theorem rowCheck8781 : row8781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8781 := by decide +kernel

theorem rowEval8781 (x : Key → ℝ) : Integer.Sparse.eval row8781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8781, Integer.Sparse.eval_collectBalanced, rawRowCheck8781]

def rawRow8782 : Integer.Sparse Key := [(key2916, -2), (key2916, -2), (key2925, -2), (key2604, -2), (key2604, -2), (key2916, -2), (key2916, -2), (key2925, -2), (key2925, -2), (key2604, -2), (key2916, -2), (key2916, -2), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1)]

theorem rawRowCheck8782 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form5 = rawRow8782 := by decide +kernel

def row8782 : Integer.Sparse Key := [(key2589, 6), (key2604, -6), (key2768, 6), (key2845, 6), (key2876, 6), (key2916, -12), (key2925, -6)]

theorem rowCheck8782 : row8782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8782 := by decide +kernel

theorem rowEval8782 (x : Key → ℝ) : Integer.Sparse.eval row8782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8782, Integer.Sparse.eval_collectBalanced, rawRowCheck8782]

def rawRow8783 : Integer.Sparse Key := [(key2916, -2), (key2925, -2), (key2916, -2), (key2916, -2), (key2925, -2), (key2604, -2), (key2925, -2), (key2604, -2), (key2916, -2), (key2916, -2), (key2604, -2), (key2916, -2), (key2845, 1), (key2876, 1), (key2768, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2589, 1), (key2876, 1), (key2589, 1), (key2845, 1), (key2768, 1), (key2876, 1), (key2589, 1), (key2876, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2589, 1), (key2845, 1), (key2589, 1), (key2768, 1)]

theorem rawRowCheck8783 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form5 = rawRow8783 := by decide +kernel

def row8783 : Integer.Sparse Key := [(key2589, 6), (key2604, -6), (key2768, 6), (key2845, 6), (key2876, 6), (key2916, -12), (key2925, -6)]

theorem rowCheck8783 : row8783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8783 := by decide +kernel

theorem rowEval8783 (x : Key → ℝ) : Integer.Sparse.eval row8783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8783, Integer.Sparse.eval_collectBalanced, rawRowCheck8783]

def rawRow8784 : Integer.Sparse Key := [(key2925, -2), (key2916, -2), (key2916, -2), (key2925, -2), (key2916, -2), (key2925, -2), (key2604, -2), (key2916, -2), (key2604, -2), (key2916, -2), (key2916, -2), (key2604, -2), (key2876, 1), (key2845, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key2768, 1), (key2876, 1), (key2845, 1), (key2876, 1), (key2589, 1), (key2845, 1), (key2589, 1), (key2876, 1), (key2768, 1), (key2876, 1), (key2589, 1), (key2768, 1), (key2589, 1), (key2845, 1), (key2768, 1), (key2845, 1), (key2589, 1), (key2768, 1), (key2589, 1)]

theorem rawRowCheck8784 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form5 = rawRow8784 := by decide +kernel

def row8784 : Integer.Sparse Key := [(key2589, 6), (key2604, -6), (key2768, 6), (key2845, 6), (key2876, 6), (key2916, -12), (key2925, -6)]

theorem rowCheck8784 : row8784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8784 := by decide +kernel

theorem rowEval8784 (x : Key → ℝ) : Integer.Sparse.eval row8784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck8784, Integer.Sparse.eval_collectBalanced, rawRowCheck8784]

def rawRow8785 : Integer.Sparse Key := [(key2355, -24), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6)]

theorem rawRowCheck8785 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form6 = rawRow8785 := by decide +kernel

def row8785 : Integer.Sparse Key := [(key2355, -24), (key2450, 18), (key2512, 6)]

theorem rowCheck8785 : row8785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8785 := by decide +kernel

theorem rowEval8785 (x : Key → ℝ) : Integer.Sparse.eval row8785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8785, Integer.Sparse.eval_collectBalanced, rawRowCheck8785]

def rawRow8786 : Integer.Sparse Key := [(key2355, -24), (key2450, 6), (key2450, 6), (key2512, 6), (key2450, 6)]

theorem rawRowCheck8786 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form6 = rawRow8786 := by decide +kernel

def row8786 : Integer.Sparse Key := [(key2355, -24), (key2450, 18), (key2512, 6)]

theorem rowCheck8786 : row8786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8786 := by decide +kernel

theorem rowEval8786 (x : Key → ℝ) : Integer.Sparse.eval row8786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8786, Integer.Sparse.eval_collectBalanced, rawRowCheck8786]

def rawRow8787 : Integer.Sparse Key := [(key2355, -24), (key2450, 6), (key2512, 6), (key2450, 6), (key2450, 6)]

theorem rawRowCheck8787 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form6 = rawRow8787 := by decide +kernel

def row8787 : Integer.Sparse Key := [(key2355, -24), (key2450, 18), (key2512, 6)]

theorem rowCheck8787 : row8787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8787 := by decide +kernel

theorem rowEval8787 (x : Key → ℝ) : Integer.Sparse.eval row8787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8787, Integer.Sparse.eval_collectBalanced, rawRowCheck8787]

def rawRow8788 : Integer.Sparse Key := [(key2355, -24), (key2512, 6), (key2450, 6), (key2450, 6), (key2450, 6)]

theorem rawRowCheck8788 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow8788 := by decide +kernel

def row8788 : Integer.Sparse Key := [(key2355, -24), (key2450, 18), (key2512, 6)]

theorem rowCheck8788 : row8788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8788 := by decide +kernel

theorem rowEval8788 (x : Key → ℝ) : Integer.Sparse.eval row8788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8788, Integer.Sparse.eval_collectBalanced, rawRowCheck8788]

def rawRow8789 : Integer.Sparse Key := [(key2512, -24), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6)]

theorem rawRowCheck8789 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form6 = rawRow8789 := by decide +kernel

def row8789 : Integer.Sparse Key := [(key2355, 6), (key2450, 18), (key2512, -24)]

theorem rowCheck8789 : row8789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8789 := by decide +kernel

theorem rowEval8789 (x : Key → ℝ) : Integer.Sparse.eval row8789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8789, Integer.Sparse.eval_collectBalanced, rawRowCheck8789]

def rawRow8790 : Integer.Sparse Key := [(key2512, -24), (key2450, 6), (key2355, 6), (key2450, 6), (key2450, 6)]

theorem rawRowCheck8790 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form6 = rawRow8790 := by decide +kernel

def row8790 : Integer.Sparse Key := [(key2355, 6), (key2450, 18), (key2512, -24)]

theorem rowCheck8790 : row8790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8790 := by decide +kernel

theorem rowEval8790 (x : Key → ℝ) : Integer.Sparse.eval row8790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8790, Integer.Sparse.eval_collectBalanced, rawRowCheck8790]

def rawRow8791 : Integer.Sparse Key := [(key2512, -24), (key2450, 6), (key2450, 6), (key2355, 6), (key2450, 6)]

theorem rawRowCheck8791 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form6 = rawRow8791 := by decide +kernel

def row8791 : Integer.Sparse Key := [(key2355, 6), (key2450, 18), (key2512, -24)]

theorem rowCheck8791 : row8791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8791 := by decide +kernel

theorem rowEval8791 (x : Key → ℝ) : Integer.Sparse.eval row8791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8791, Integer.Sparse.eval_collectBalanced, rawRowCheck8791]

def rawRow8792 : Integer.Sparse Key := [(key2512, -24), (key2450, 6), (key2450, 6), (key2450, 6), (key2355, 6)]

theorem rawRowCheck8792 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form6 = rawRow8792 := by decide +kernel

def row8792 : Integer.Sparse Key := [(key2355, 6), (key2450, 18), (key2512, -24)]

theorem rowCheck8792 : row8792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8792 := by decide +kernel

theorem rowEval8792 (x : Key → ℝ) : Integer.Sparse.eval row8792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck8792, Integer.Sparse.eval_collectBalanced, rawRowCheck8792]

def rawRow8793 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2376, -2), (key2370, -2), (key2376, -2), (key2370, -2), (key2388, -2), (key2376, -2), (key2388, -2), (key2376, -2), (key2376, -2), (key2388, -2), (key2398, 2), (key2404, 2), (key2404, 2), (key2398, 2), (key2404, 2), (key2398, 2), (key2435, 2), (key2404, 2), (key2435, 2), (key2404, 2), (key2404, 2), (key2435, 2)]

theorem rawRowCheck8793 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form7 = rawRow8793 := by decide +kernel

def row8793 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2398, 6), (key2404, 12), (key2435, 6)]

theorem rowCheck8793 : row8793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8793 := by decide +kernel

theorem rowEval8793 (x : Key → ℝ) : Integer.Sparse.eval row8793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8793, Integer.Sparse.eval_collectBalanced, rawRowCheck8793]

def rawRow8794 : Integer.Sparse Key := [(key2376, -2), (key2370, -2), (key2376, -2), (key2376, -2), (key2370, -2), (key2388, -2), (key2370, -2), (key2388, -2), (key2376, -2), (key2376, -2), (key2388, -2), (key2376, -2), (key2404, 2), (key2398, 2), (key2404, 2), (key2404, 2), (key2398, 2), (key2435, 2), (key2398, 2), (key2435, 2), (key2404, 2), (key2404, 2), (key2435, 2), (key2404, 2)]

theorem rawRowCheck8794 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form7 = rawRow8794 := by decide +kernel

def row8794 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2398, 6), (key2404, 12), (key2435, 6)]

theorem rowCheck8794 : row8794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8794 := by decide +kernel

theorem rowEval8794 (x : Key → ℝ) : Integer.Sparse.eval row8794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8794, Integer.Sparse.eval_collectBalanced, rawRowCheck8794]

def rawRow8795 : Integer.Sparse Key := [(key2376, -2), (key2376, -2), (key2370, -2), (key2388, -2), (key2388, -2), (key2376, -2), (key2376, -2), (key2370, -2), (key2370, -2), (key2388, -2), (key2376, -2), (key2376, -2), (key2404, 2), (key2404, 2), (key2398, 2), (key2435, 2), (key2435, 2), (key2404, 2), (key2404, 2), (key2398, 2), (key2398, 2), (key2435, 2), (key2404, 2), (key2404, 2)]

theorem rawRowCheck8795 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form7 = rawRow8795 := by decide +kernel

def row8795 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2398, 6), (key2404, 12), (key2435, 6)]

theorem rowCheck8795 : row8795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8795 := by decide +kernel

theorem rowEval8795 (x : Key → ℝ) : Integer.Sparse.eval row8795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8795, Integer.Sparse.eval_collectBalanced, rawRowCheck8795]

def rawRow8796 : Integer.Sparse Key := [(key2388, -2), (key2388, -2), (key2388, -2), (key2376, -2), (key2376, -2), (key2376, -2), (key2376, -2), (key2376, -2), (key2376, -2), (key2370, -2), (key2370, -2), (key2370, -2), (key2435, 2), (key2435, 2), (key2435, 2), (key2404, 2), (key2404, 2), (key2404, 2), (key2404, 2), (key2404, 2), (key2404, 2), (key2398, 2), (key2398, 2), (key2398, 2)]

theorem rawRowCheck8796 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8796 := by decide +kernel

def row8796 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2398, 6), (key2404, 12), (key2435, 6)]

theorem rowCheck8796 : row8796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8796 := by decide +kernel

theorem rowEval8796 (x : Key → ℝ) : Integer.Sparse.eval row8796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8796, Integer.Sparse.eval_collectBalanced, rawRowCheck8796]

def rawRow8797 : Integer.Sparse Key := [(key3005, -2), (key3005, -2), (key3005, -2), (key3019, -2), (key3019, -2), (key3019, -2), (key3019, -2), (key3019, -2), (key3019, -2), (key3028, -2), (key3028, -2), (key3028, -2), (key2604, 2), (key2604, 2), (key2604, 2), (key2916, 2), (key2916, 2), (key2916, 2), (key2916, 2), (key2916, 2), (key2916, 2), (key2925, 2), (key2925, 2), (key2925, 2)]

theorem rawRowCheck8797 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8797 := by decide +kernel

def row8797 : Integer.Sparse Key := [(key2604, 6), (key2916, 12), (key2925, 6), (key3005, -6), (key3019, -12), (key3028, -6)]

theorem rowCheck8797 : row8797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8797 := by decide +kernel

theorem rowEval8797 (x : Key → ℝ) : Integer.Sparse.eval row8797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8797, Integer.Sparse.eval_collectBalanced, rawRowCheck8797]

def rawRow8798 : Integer.Sparse Key := [(key3019, -2), (key3019, -2), (key3028, -2), (key3005, -2), (key3005, -2), (key3019, -2), (key3019, -2), (key3028, -2), (key3028, -2), (key3005, -2), (key3019, -2), (key3019, -2), (key2916, 2), (key2916, 2), (key2925, 2), (key2604, 2), (key2604, 2), (key2916, 2), (key2916, 2), (key2925, 2), (key2925, 2), (key2604, 2), (key2916, 2), (key2916, 2)]

theorem rawRowCheck8798 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form7 = rawRow8798 := by decide +kernel

def row8798 : Integer.Sparse Key := [(key2604, 6), (key2916, 12), (key2925, 6), (key3005, -6), (key3019, -12), (key3028, -6)]

theorem rowCheck8798 : row8798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8798 := by decide +kernel

theorem rowEval8798 (x : Key → ℝ) : Integer.Sparse.eval row8798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8798, Integer.Sparse.eval_collectBalanced, rawRowCheck8798]

def rawRow8799 : Integer.Sparse Key := [(key3019, -2), (key3028, -2), (key3019, -2), (key3019, -2), (key3028, -2), (key3005, -2), (key3028, -2), (key3005, -2), (key3019, -2), (key3019, -2), (key3005, -2), (key3019, -2), (key2916, 2), (key2925, 2), (key2916, 2), (key2916, 2), (key2925, 2), (key2604, 2), (key2925, 2), (key2604, 2), (key2916, 2), (key2916, 2), (key2604, 2), (key2916, 2)]

theorem rawRowCheck8799 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form7 = rawRow8799 := by decide +kernel

def row8799 : Integer.Sparse Key := [(key2604, 6), (key2916, 12), (key2925, 6), (key3005, -6), (key3019, -12), (key3028, -6)]

theorem rowCheck8799 : row8799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8799 := by decide +kernel

theorem rowEval8799 (x : Key → ℝ) : Integer.Sparse.eval row8799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8799, Integer.Sparse.eval_collectBalanced, rawRowCheck8799]

def rawRow8800 : Integer.Sparse Key := [(key3028, -2), (key3019, -2), (key3019, -2), (key3028, -2), (key3019, -2), (key3028, -2), (key3005, -2), (key3019, -2), (key3005, -2), (key3019, -2), (key3019, -2), (key3005, -2), (key2925, 2), (key2916, 2), (key2916, 2), (key2925, 2), (key2916, 2), (key2925, 2), (key2604, 2), (key2916, 2), (key2604, 2), (key2916, 2), (key2916, 2), (key2604, 2)]

theorem rawRowCheck8800 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form7 = rawRow8800 := by decide +kernel

def row8800 : Integer.Sparse Key := [(key2604, 6), (key2916, 12), (key2925, 6), (key3005, -6), (key3019, -12), (key3028, -6)]

theorem rowCheck8800 : row8800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8800 := by decide +kernel

theorem rowEval8800 (x : Key → ℝ) : Integer.Sparse.eval row8800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck8800, Integer.Sparse.eval_collectBalanced, rawRowCheck8800]

def rawRow8801 : Integer.Sparse Key := [(key1526, -2), (key1534, -2), (key1534, -2), (key1526, -2), (key1534, -2), (key1526, -2), (key1894, -2), (key1534, -2), (key1894, -2), (key1534, -2), (key1534, -2), (key1894, -2), (key1604, 1), (key1612, 1), (key1604, 1), (key1679, 1), (key1612, 1), (key1679, 1), (key1604, 1), (key1612, 1), (key1604, 1), (key1916, 1), (key1612, 1), (key1916, 1), (key1604, 1), (key1679, 1), (key1604, 1), (key1916, 1), (key1679, 1), (key1916, 1), (key1612, 1), (key1679, 1), (key1612, 1), (key1916, 1), (key1679, 1), (key1916, 1)]

theorem rawRowCheck8801 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form8 = rawRow8801 := by decide +kernel

def row8801 : Integer.Sparse Key := [(key1526, -6), (key1534, -12), (key1604, 6), (key1612, 6), (key1679, 6), (key1894, -6), (key1916, 6)]

theorem rowCheck8801 : row8801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8801 := by decide +kernel

theorem rowEval8801 (x : Key → ℝ) : Integer.Sparse.eval row8801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8801, Integer.Sparse.eval_collectBalanced, rawRowCheck8801]

def rawRow8802 : Integer.Sparse Key := [(key1534, -2), (key1526, -2), (key1534, -2), (key1534, -2), (key1526, -2), (key1894, -2), (key1526, -2), (key1894, -2), (key1534, -2), (key1534, -2), (key1894, -2), (key1534, -2), (key1612, 1), (key1604, 1), (key1679, 1), (key1604, 1), (key1679, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1916, 1), (key1604, 1), (key1916, 1), (key1612, 1), (key1679, 1), (key1604, 1), (key1916, 1), (key1604, 1), (key1916, 1), (key1679, 1), (key1679, 1), (key1612, 1), (key1916, 1), (key1612, 1), (key1916, 1), (key1679, 1)]

theorem rawRowCheck8802 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form8 = rawRow8802 := by decide +kernel

def row8802 : Integer.Sparse Key := [(key1526, -6), (key1534, -12), (key1604, 6), (key1612, 6), (key1679, 6), (key1894, -6), (key1916, 6)]

theorem rowCheck8802 : row8802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8802 := by decide +kernel

theorem rowEval8802 (x : Key → ℝ) : Integer.Sparse.eval row8802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8802, Integer.Sparse.eval_collectBalanced, rawRowCheck8802]

def rawRow8803 : Integer.Sparse Key := [(key1534, -2), (key1534, -2), (key1526, -2), (key1894, -2), (key1894, -2), (key1534, -2), (key1534, -2), (key1526, -2), (key1526, -2), (key1894, -2), (key1534, -2), (key1534, -2), (key1679, 1), (key1679, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1), (key1916, 1), (key1916, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1), (key1916, 1), (key1916, 1), (key1679, 1), (key1679, 1), (key1604, 1), (key1604, 1), (key1916, 1), (key1916, 1), (key1679, 1), (key1679, 1), (key1612, 1), (key1612, 1)]

theorem rawRowCheck8803 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form8 = rawRow8803 := by decide +kernel

def row8803 : Integer.Sparse Key := [(key1526, -6), (key1534, -12), (key1604, 6), (key1612, 6), (key1679, 6), (key1894, -6), (key1916, 6)]

theorem rowCheck8803 : row8803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8803 := by decide +kernel

theorem rowEval8803 (x : Key → ℝ) : Integer.Sparse.eval row8803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8803, Integer.Sparse.eval_collectBalanced, rawRowCheck8803]

def rawRow8804 : Integer.Sparse Key := [(key1894, -2), (key1894, -2), (key1894, -2), (key1534, -2), (key1534, -2), (key1534, -2), (key1534, -2), (key1534, -2), (key1534, -2), (key1526, -2), (key1526, -2), (key1526, -2), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1)]

theorem rawRowCheck8804 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form8 = rawRow8804 := by decide +kernel

def row8804 : Integer.Sparse Key := [(key1526, -6), (key1534, -12), (key1604, 6), (key1612, 6), (key1679, 6), (key1894, -6), (key1916, 6)]

theorem rowCheck8804 : row8804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8804 := by decide +kernel

theorem rowEval8804 (x : Key → ℝ) : Integer.Sparse.eval row8804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8804, Integer.Sparse.eval_collectBalanced, rawRowCheck8804]

def rawRow8805 : Integer.Sparse Key := [(key1271, -2), (key1271, -2), (key1271, -2), (key1679, -2), (key1679, -2), (key1679, -2), (key1679, -2), (key1679, -2), (key1679, -2), (key1693, -2), (key1693, -2), (key1693, -2), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1)]

theorem rawRowCheck8805 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form8 = rawRow8805 := by decide +kernel

def row8805 : Integer.Sparse Key := [(key1259, 6), (key1271, -6), (key1534, 6), (key1612, 6), (key1640, 6), (key1679, -12), (key1693, -6)]

theorem rowCheck8805 : row8805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8805 := by decide +kernel

theorem rowEval8805 (x : Key → ℝ) : Integer.Sparse.eval row8805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8805, Integer.Sparse.eval_collectBalanced, rawRowCheck8805]

def rawRow8806 : Integer.Sparse Key := [(key1679, -2), (key1679, -2), (key1693, -2), (key1271, -2), (key1271, -2), (key1679, -2), (key1679, -2), (key1693, -2), (key1693, -2), (key1271, -2), (key1679, -2), (key1679, -2), (key1534, 1), (key1534, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1), (key1259, 1), (key1259, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1), (key1259, 1), (key1259, 1), (key1534, 1), (key1534, 1), (key1640, 1), (key1640, 1), (key1259, 1), (key1259, 1), (key1534, 1), (key1534, 1), (key1612, 1), (key1612, 1)]

theorem rawRowCheck8806 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form8 = rawRow8806 := by decide +kernel

def row8806 : Integer.Sparse Key := [(key1259, 6), (key1271, -6), (key1534, 6), (key1612, 6), (key1640, 6), (key1679, -12), (key1693, -6)]

theorem rowCheck8806 : row8806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8806 := by decide +kernel

theorem rowEval8806 (x : Key → ℝ) : Integer.Sparse.eval row8806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8806, Integer.Sparse.eval_collectBalanced, rawRowCheck8806]

def rawRow8807 : Integer.Sparse Key := [(key1679, -2), (key1693, -2), (key1679, -2), (key1679, -2), (key1693, -2), (key1271, -2), (key1693, -2), (key1271, -2), (key1679, -2), (key1679, -2), (key1271, -2), (key1679, -2), (key1612, 1), (key1640, 1), (key1534, 1), (key1640, 1), (key1534, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1259, 1), (key1640, 1), (key1259, 1), (key1612, 1), (key1534, 1), (key1640, 1), (key1259, 1), (key1640, 1), (key1259, 1), (key1534, 1), (key1534, 1), (key1612, 1), (key1259, 1), (key1612, 1), (key1259, 1), (key1534, 1)]

theorem rawRowCheck8807 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form8 = rawRow8807 := by decide +kernel

def row8807 : Integer.Sparse Key := [(key1259, 6), (key1271, -6), (key1534, 6), (key1612, 6), (key1640, 6), (key1679, -12), (key1693, -6)]

theorem rowCheck8807 : row8807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8807 := by decide +kernel

theorem rowEval8807 (x : Key → ℝ) : Integer.Sparse.eval row8807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8807, Integer.Sparse.eval_collectBalanced, rawRowCheck8807]

def rawRow8808 : Integer.Sparse Key := [(key1693, -2), (key1679, -2), (key1679, -2), (key1693, -2), (key1679, -2), (key1693, -2), (key1271, -2), (key1679, -2), (key1271, -2), (key1679, -2), (key1679, -2), (key1271, -2), (key1640, 1), (key1612, 1), (key1640, 1), (key1534, 1), (key1612, 1), (key1534, 1), (key1640, 1), (key1612, 1), (key1640, 1), (key1259, 1), (key1612, 1), (key1259, 1), (key1640, 1), (key1534, 1), (key1640, 1), (key1259, 1), (key1534, 1), (key1259, 1), (key1612, 1), (key1534, 1), (key1612, 1), (key1259, 1), (key1534, 1), (key1259, 1)]

theorem rawRowCheck8808 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form8 = rawRow8808 := by decide +kernel

def row8808 : Integer.Sparse Key := [(key1259, 6), (key1271, -6), (key1534, 6), (key1612, 6), (key1640, 6), (key1679, -12), (key1693, -6)]

theorem rowCheck8808 : row8808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8808 := by decide +kernel

theorem rowEval8808 (x : Key → ℝ) : Integer.Sparse.eval row8808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck8808, Integer.Sparse.eval_collectBalanced, rawRowCheck8808]

def rawRow8809 : Integer.Sparse Key := [(key2464, 1), (key2470, 1), (key2464, 1), (key2478, 1), (key2470, 1), (key2478, 1), (key2464, 1), (key2470, 1), (key2464, 1), (key2501, 1), (key2470, 1), (key2501, 1), (key2464, 1), (key2478, 1), (key2464, 1), (key2501, 1), (key2478, 1), (key2501, 1), (key2470, 1), (key2478, 1), (key2470, 1), (key2501, 1), (key2478, 1), (key2501, 1), (key2568, -2), (key2568, -2), (key2570, -2), (key2568, -2), (key2568, -2), (key2575, -2), (key2568, -2), (key2570, -2), (key2568, -2), (key2575, -2), (key2570, -2), (key2575, -2)]

theorem rawRowCheck8809 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form9 = rawRow8809 := by decide +kernel

def row8809 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8809 : row8809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8809 := by decide +kernel

theorem rowEval8809 (x : Key → ℝ) : Integer.Sparse.eval row8809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8809, Integer.Sparse.eval_collectBalanced, rawRowCheck8809]

def rawRow8810 : Integer.Sparse Key := [(key2470, 1), (key2464, 1), (key2478, 1), (key2464, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2501, 1), (key2464, 1), (key2501, 1), (key2470, 1), (key2478, 1), (key2464, 1), (key2501, 1), (key2464, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2501, 1), (key2470, 1), (key2501, 1), (key2478, 1), (key2568, -2), (key2570, -2), (key2568, -2), (key2568, -2), (key2575, -2), (key2568, -2), (key2570, -2), (key2568, -2), (key2575, -2), (key2568, -2), (key2575, -2), (key2570, -2)]

theorem rawRowCheck8810 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form9 = rawRow8810 := by decide +kernel

def row8810 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8810 : row8810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8810 := by decide +kernel

theorem rowEval8810 (x : Key → ℝ) : Integer.Sparse.eval row8810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8810, Integer.Sparse.eval_collectBalanced, rawRowCheck8810]

def rawRow8811 : Integer.Sparse Key := [(key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2570, -2), (key2568, -2), (key2568, -2), (key2575, -2), (key2568, -2), (key2568, -2), (key2575, -2), (key2575, -2), (key2570, -2), (key2570, -2), (key2568, -2), (key2568, -2)]

theorem rawRowCheck8811 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form9 = rawRow8811 := by decide +kernel

def row8811 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8811 : row8811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8811 := by decide +kernel

theorem rowEval8811 (x : Key → ℝ) : Integer.Sparse.eval row8811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8811, Integer.Sparse.eval_collectBalanced, rawRowCheck8811]

def rawRow8812 : Integer.Sparse Key := [(key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2575, -2), (key2575, -2), (key2575, -2), (key2570, -2), (key2570, -2), (key2570, -2), (key2568, -2), (key2568, -2), (key2568, -2), (key2568, -2), (key2568, -2), (key2568, -2)]

theorem rawRowCheck8812 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form9 = rawRow8812 := by decide +kernel

def row8812 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8812 : row8812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8812 := by decide +kernel

theorem rowEval8812 (x : Key → ℝ) : Integer.Sparse.eval row8812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8812, Integer.Sparse.eval_collectBalanced, rawRowCheck8812]

def rawRow8813 : Integer.Sparse Key := [(key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2370, -2), (key2370, -2), (key2370, -2), (key2398, -2), (key2398, -2), (key2398, -2), (key2464, -2), (key2464, -2), (key2464, -2), (key2464, -2), (key2464, -2), (key2464, -2)]

theorem rawRowCheck8813 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form9 = rawRow8813 := by decide +kernel

def row8813 : Integer.Sparse Key := [(key2370, -6), (key2398, -6), (key2464, -12), (key2589, 6), (key2768, 6), (key2845, 6), (key2876, 6)]

theorem rowCheck8813 : row8813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8813 := by decide +kernel

theorem rowEval8813 (x : Key → ℝ) : Integer.Sparse.eval row8813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8813, Integer.Sparse.eval_collectBalanced, rawRowCheck8813]

def rawRow8814 : Integer.Sparse Key := [(key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2762, -2), (key2839, -2), (key2839, -2), (key2583, -2), (key2839, -2), (key2839, -2), (key2370, -2), (key2370, -2), (key2398, -2), (key2398, -2), (key2464, -2), (key2464, -2)]

theorem rawRowCheck8814 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form9 = rawRow8814 := by decide +kernel

def row8814 : Integer.Sparse Key := [(key2370, -4), (key2398, -4), (key2464, -4), (key2583, -2), (key2589, 6), (key2762, -2), (key2768, 6), (key2839, -8), (key2845, 6), (key2876, 6)]

theorem rowCheck8814 : row8814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8814 := by decide +kernel

theorem rowEval8814 (x : Key → ℝ) : Integer.Sparse.eval row8814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8814, Integer.Sparse.eval_collectBalanced, rawRowCheck8814]

def rawRow8815 : Integer.Sparse Key := [(key2845, 1), (key2876, 1), (key2768, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2589, 1), (key2876, 1), (key2589, 1), (key2845, 1), (key2768, 1), (key2876, 1), (key2589, 1), (key2876, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2589, 1), (key2845, 1), (key2589, 1), (key2768, 1), (key2839, -2), (key2762, -2), (key2839, -2), (key2839, -2), (key2583, -2), (key2839, -2), (key2762, -2), (key2839, -2), (key2583, -2), (key2839, -2), (key2370, -2), (key2398, -2)]

theorem rawRowCheck8815 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form9 = rawRow8815 := by decide +kernel

def row8815 : Integer.Sparse Key := [(key2370, -2), (key2398, -2), (key2583, -4), (key2589, 6), (key2762, -4), (key2768, 6), (key2839, -12), (key2845, 6), (key2876, 6)]

theorem rowCheck8815 : row8815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8815 := by decide +kernel

theorem rowEval8815 (x : Key → ℝ) : Integer.Sparse.eval row8815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8815, Integer.Sparse.eval_collectBalanced, rawRowCheck8815]

def rawRow8816 : Integer.Sparse Key := [(key2876, 1), (key2845, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key2768, 1), (key2876, 1), (key2845, 1), (key2876, 1), (key2589, 1), (key2845, 1), (key2589, 1), (key2876, 1), (key2768, 1), (key2876, 1), (key2589, 1), (key2768, 1), (key2589, 1), (key2845, 1), (key2768, 1), (key2845, 1), (key2589, 1), (key2768, 1), (key2589, 1), (key2839, -2), (key2839, -2), (key2762, -2), (key2839, -2), (key2839, -2), (key2583, -2), (key2839, -2), (key2762, -2), (key2839, -2), (key2583, -2), (key2762, -2), (key2583, -2)]

theorem rawRowCheck8816 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form9 = rawRow8816 := by decide +kernel

def row8816 : Integer.Sparse Key := [(key2583, -6), (key2589, 6), (key2762, -6), (key2768, 6), (key2839, -12), (key2845, 6), (key2876, 6)]

theorem rowCheck8816 : row8816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8816 := by decide +kernel

theorem rowEval8816 (x : Key → ℝ) : Integer.Sparse.eval row8816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck8816, Integer.Sparse.eval_collectBalanced, rawRowCheck8816]

def rawRow8817 : Integer.Sparse Key := [(key1525, -6), (key1525, -6), (key1525, -6), (key1892, -6), (key1603, 2), (key1603, 2), (key1677, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1603, 2), (key1677, 2), (key1603, 2), (key1914, 2), (key1677, 2), (key1914, 2)]

theorem rawRowCheck8817 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form10 = rawRow8817 := by decide +kernel

def row8817 : Integer.Sparse Key := [(key1525, -18), (key1603, 12), (key1677, 6), (key1892, -6), (key1914, 6)]

theorem rowCheck8817 : row8817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8817 := by decide +kernel

theorem rowEval8817 (x : Key → ℝ) : Integer.Sparse.eval row8817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck8817, Integer.Sparse.eval_collectBalanced, rawRowCheck8817]

def rawRow8818 : Integer.Sparse Key := [(key1525, -6), (key1525, -6), (key1892, -6), (key1525, -6), (key1603, 2), (key1677, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1603, 2), (key1677, 2), (key1603, 2), (key1914, 2), (key1603, 2), (key1914, 2), (key1677, 2)]

theorem rawRowCheck8818 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form10 = rawRow8818 := by decide +kernel

def row8818 : Integer.Sparse Key := [(key1525, -18), (key1603, 12), (key1677, 6), (key1892, -6), (key1914, 6)]

theorem rowCheck8818 : row8818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8818 := by decide +kernel

theorem rowEval8818 (x : Key → ℝ) : Integer.Sparse.eval row8818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8818, Integer.Sparse.eval_collectBalanced, rawRowCheck8818]

def rawRow8819 : Integer.Sparse Key := [(key1525, -6), (key1892, -6), (key1525, -6), (key1525, -6), (key1677, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1914, 2), (key1677, 2), (key1677, 2), (key1603, 2), (key1603, 2)]

theorem rawRowCheck8819 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form10 = rawRow8819 := by decide +kernel

def row8819 : Integer.Sparse Key := [(key1525, -18), (key1603, 12), (key1677, 6), (key1892, -6), (key1914, 6)]

theorem rowCheck8819 : row8819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8819 := by decide +kernel

theorem rowEval8819 (x : Key → ℝ) : Integer.Sparse.eval row8819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8819, Integer.Sparse.eval_collectBalanced, rawRowCheck8819]

def rawRow8820 : Integer.Sparse Key := [(key1892, -6), (key1525, -6), (key1525, -6), (key1525, -6), (key1914, 2), (key1914, 2), (key1914, 2), (key1677, 2), (key1677, 2), (key1677, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2)]

theorem rawRowCheck8820 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow8820 := by decide +kernel

def row8820 : Integer.Sparse Key := [(key1525, -18), (key1603, 12), (key1677, 6), (key1892, -6), (key1914, 6)]

theorem rowCheck8820 : row8820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8820 := by decide +kernel

theorem rowEval8820 (x : Key → ℝ) : Integer.Sparse.eval row8820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8820, Integer.Sparse.eval_collectBalanced, rawRowCheck8820]

def rawRow8821 : Integer.Sparse Key := [(key1269, -6), (key1677, -6), (key1677, -6), (key1677, -6), (key1250, 2), (key1250, 2), (key1250, 2), (key1525, 2), (key1525, 2), (key1525, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2)]

theorem rawRowCheck8821 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form10 = rawRow8821 := by decide +kernel

def row8821 : Integer.Sparse Key := [(key1250, 6), (key1269, -6), (key1525, 6), (key1603, 12), (key1677, -18)]

theorem rowCheck8821 : row8821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8821 := by decide +kernel

theorem rowEval8821 (x : Key → ℝ) : Integer.Sparse.eval row8821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8821, Integer.Sparse.eval_collectBalanced, rawRowCheck8821]

def rawRow8822 : Integer.Sparse Key := [(key1677, -6), (key1269, -6), (key1677, -6), (key1677, -6), (key1525, 2), (key1603, 2), (key1603, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1250, 2), (key1250, 2), (key1525, 2), (key1525, 2), (key1603, 2), (key1603, 2)]

theorem rawRowCheck8822 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form10 = rawRow8822 := by decide +kernel

def row8822 : Integer.Sparse Key := [(key1250, 6), (key1269, -6), (key1525, 6), (key1603, 12), (key1677, -18)]

theorem rowCheck8822 : row8822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8822 := by decide +kernel

theorem rowEval8822 (x : Key → ℝ) : Integer.Sparse.eval row8822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8822, Integer.Sparse.eval_collectBalanced, rawRowCheck8822]

def rawRow8823 : Integer.Sparse Key := [(key1677, -6), (key1677, -6), (key1269, -6), (key1677, -6), (key1603, 2), (key1525, 2), (key1603, 2), (key1603, 2), (key1250, 2), (key1603, 2), (key1525, 2), (key1603, 2), (key1250, 2), (key1603, 2), (key1250, 2), (key1525, 2)]

theorem rawRowCheck8823 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form10 = rawRow8823 := by decide +kernel

def row8823 : Integer.Sparse Key := [(key1250, 6), (key1269, -6), (key1525, 6), (key1603, 12), (key1677, -18)]

theorem rowCheck8823 : row8823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8823 := by decide +kernel

theorem rowEval8823 (x : Key → ℝ) : Integer.Sparse.eval row8823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8823, Integer.Sparse.eval_collectBalanced, rawRowCheck8823]

def rawRow8824 : Integer.Sparse Key := [(key1677, -6), (key1677, -6), (key1677, -6), (key1269, -6), (key1603, 2), (key1603, 2), (key1525, 2), (key1603, 2), (key1603, 2), (key1250, 2), (key1603, 2), (key1525, 2), (key1603, 2), (key1250, 2), (key1525, 2), (key1250, 2)]

theorem rawRowCheck8824 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form10 = rawRow8824 := by decide +kernel

def row8824 : Integer.Sparse Key := [(key1250, 6), (key1269, -6), (key1525, 6), (key1603, 12), (key1677, -18)]

theorem rowCheck8824 : row8824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8824 := by decide +kernel

theorem rowEval8824 (x : Key → ℝ) : Integer.Sparse.eval row8824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck8824, Integer.Sparse.eval_collectBalanced, rawRowCheck8824]

def rawRow8825 : Integer.Sparse Key := [(key2354, 6), (key2358, 6), (key2358, 6), (key2358, 6), (key2529, -6), (key2529, -6), (key2529, -6), (key2559, -6)]

theorem rawRowCheck8825 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form11 = rawRow8825 := by decide +kernel

def row8825 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2529, -18), (key2559, -6)]

theorem rowCheck8825 : row8825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8825 := by decide +kernel

theorem rowEval8825 (x : Key → ℝ) : Integer.Sparse.eval row8825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck8825, Integer.Sparse.eval_collectBalanced, rawRowCheck8825]

def rawRow8826 : Integer.Sparse Key := [(key2358, 6), (key2354, 6), (key2358, 6), (key2358, 6), (key2529, -6), (key2529, -6), (key2559, -6), (key2529, -6)]

theorem rawRowCheck8826 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form11 = rawRow8826 := by decide +kernel

def row8826 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2529, -18), (key2559, -6)]

theorem rowCheck8826 : row8826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8826 := by decide +kernel

theorem rowEval8826 (x : Key → ℝ) : Integer.Sparse.eval row8826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8826, Integer.Sparse.eval_collectBalanced, rawRowCheck8826]

def rawRow8827 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2354, 6), (key2358, 6), (key2529, -6), (key2559, -6), (key2529, -6), (key2529, -6)]

theorem rawRowCheck8827 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form11 = rawRow8827 := by decide +kernel

def row8827 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2529, -18), (key2559, -6)]

theorem rowCheck8827 : row8827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8827 := by decide +kernel

theorem rowEval8827 (x : Key → ℝ) : Integer.Sparse.eval row8827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8827, Integer.Sparse.eval_collectBalanced, rawRowCheck8827]

def rawRow8828 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2358, 6), (key2354, 6), (key2559, -6), (key2529, -6), (key2529, -6), (key2529, -6)]

theorem rawRowCheck8828 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form11 = rawRow8828 := by decide +kernel

def row8828 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2529, -18), (key2559, -6)]

theorem rowCheck8828 : row8828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8828 := by decide +kernel

theorem rowEval8828 (x : Key → ℝ) : Integer.Sparse.eval row8828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8828, Integer.Sparse.eval_collectBalanced, rawRowCheck8828]

def rawRow8829 : Integer.Sparse Key := [(key2514, 6), (key2514, 6), (key2514, 6), (key2559, 6), (key2354, -6), (key2449, -6), (key2449, -6), (key2449, -6)]

theorem rawRowCheck8829 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form11 = rawRow8829 := by decide +kernel

def row8829 : Integer.Sparse Key := [(key2354, -6), (key2449, -18), (key2514, 18), (key2559, 6)]

theorem rowCheck8829 : row8829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8829 := by decide +kernel

theorem rowEval8829 (x : Key → ℝ) : Integer.Sparse.eval row8829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8829, Integer.Sparse.eval_collectBalanced, rawRowCheck8829]

def rawRow8830 : Integer.Sparse Key := [(key2514, 6), (key2514, 6), (key2559, 6), (key2514, 6), (key2449, -6), (key2354, -6), (key2449, -6), (key2449, -6)]

theorem rawRowCheck8830 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form11 = rawRow8830 := by decide +kernel

def row8830 : Integer.Sparse Key := [(key2354, -6), (key2449, -18), (key2514, 18), (key2559, 6)]

theorem rowCheck8830 : row8830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8830 := by decide +kernel

theorem rowEval8830 (x : Key → ℝ) : Integer.Sparse.eval row8830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8830, Integer.Sparse.eval_collectBalanced, rawRowCheck8830]

def rawRow8831 : Integer.Sparse Key := [(key2514, 6), (key2559, 6), (key2514, 6), (key2514, 6), (key2449, -6), (key2449, -6), (key2354, -6), (key2449, -6)]

theorem rawRowCheck8831 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form11 = rawRow8831 := by decide +kernel

def row8831 : Integer.Sparse Key := [(key2354, -6), (key2449, -18), (key2514, 18), (key2559, 6)]

theorem rowCheck8831 : row8831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8831 := by decide +kernel

theorem rowEval8831 (x : Key → ℝ) : Integer.Sparse.eval row8831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8831, Integer.Sparse.eval_collectBalanced, rawRowCheck8831]

end MUB6.Certificate.GramRows

end OAI
