import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
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
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2816 : Integer.Sparse Key := [(key2428, -2), (key2428, -2), (key2444, -2), (key2430, 2), (key2430, 2), (key2444, 2), (key2496, 2), (key2496, 2), (key2510, 2), (key2510, -6), (key2574, -2), (key2574, -2), (key2577, -2), (key2577, 6)]

theorem rawRowCheck2816 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form6 = rawRow2816 := by decide +kernel

def row2816 : Integer.Sparse Key := [(key2428, -4), (key2430, 4), (key2496, 4), (key2510, -4), (key2574, -4), (key2577, 4)]

theorem rowCheck2816 : row2816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2816 := by decide +kernel

theorem rowEval2816 (x : Key → ℝ) : Integer.Sparse.eval row2816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2816, Integer.Sparse.eval_collectBalanced, rawRowCheck2816]

def rawRow2817 : Integer.Sparse Key := [(key2428, -2), (key2444, -2), (key2428, -2), (key2430, 2), (key2444, 2), (key2430, 2), (key2496, 2), (key2510, 2), (key2496, 2), (key2510, -6), (key2574, -2), (key2577, -2), (key2574, -2), (key2577, 6)]

theorem rawRowCheck2817 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form6 = rawRow2817 := by decide +kernel

def row2817 : Integer.Sparse Key := [(key2428, -4), (key2430, 4), (key2496, 4), (key2510, -4), (key2574, -4), (key2577, 4)]

theorem rowCheck2817 : row2817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2817 := by decide +kernel

theorem rowEval2817 (x : Key → ℝ) : Integer.Sparse.eval row2817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2817, Integer.Sparse.eval_collectBalanced, rawRowCheck2817]

def rawRow2818 : Integer.Sparse Key := [(key2444, -2), (key2428, -2), (key2428, -2), (key2444, 2), (key2430, 2), (key2430, 2), (key2510, 2), (key2496, 2), (key2496, 2), (key2510, -6), (key2577, -2), (key2574, -2), (key2574, -2), (key2577, 6)]

theorem rawRowCheck2818 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form6 = rawRow2818 := by decide +kernel

def row2818 : Integer.Sparse Key := [(key2428, -4), (key2430, 4), (key2496, 4), (key2510, -4), (key2574, -4), (key2577, 4)]

theorem rowCheck2818 : row2818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2818 := by decide +kernel

theorem rowEval2818 (x : Key → ℝ) : Integer.Sparse.eval row2818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2818, Integer.Sparse.eval_collectBalanced, rawRowCheck2818]

def rawRow2819 : Integer.Sparse Key := [(key2421, -2), (key2430, -2), (key2430, -2), (key2421, 2), (key2428, 2), (key2428, 2), (key2496, 2), (key2510, 2), (key2510, 2), (key2496, -6), (key2574, -2), (key2577, -2), (key2577, -2), (key2574, 6)]

theorem rawRowCheck2819 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form6 = rawRow2819 := by decide +kernel

def row2819 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2496, -4), (key2510, 4), (key2574, 4), (key2577, -4)]

theorem rowCheck2819 : row2819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2819 := by decide +kernel

theorem rowEval2819 (x : Key → ℝ) : Integer.Sparse.eval row2819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2819, Integer.Sparse.eval_collectBalanced, rawRowCheck2819]

def rawRow2820 : Integer.Sparse Key := [(key2430, -2), (key2421, -2), (key2430, -2), (key2428, 2), (key2421, 2), (key2428, 2), (key2510, 2), (key2496, 2), (key2510, 2), (key2496, -6), (key2577, -2), (key2574, -2), (key2577, -2), (key2574, 6)]

theorem rawRowCheck2820 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form6 = rawRow2820 := by decide +kernel

def row2820 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2496, -4), (key2510, 4), (key2574, 4), (key2577, -4)]

theorem rowCheck2820 : row2820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2820 := by decide +kernel

theorem rowEval2820 (x : Key → ℝ) : Integer.Sparse.eval row2820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2820, Integer.Sparse.eval_collectBalanced, rawRowCheck2820]

def rawRow2821 : Integer.Sparse Key := [(key2430, -2), (key2430, -2), (key2421, -2), (key2428, 2), (key2428, 2), (key2421, 2), (key2510, 2), (key2510, 2), (key2496, 2), (key2496, -6), (key2577, -2), (key2577, -2), (key2574, -2), (key2574, 6)]

theorem rawRowCheck2821 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form6 = rawRow2821 := by decide +kernel

def row2821 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2496, -4), (key2510, 4), (key2574, 4), (key2577, -4)]

theorem rowCheck2821 : row2821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2821 := by decide +kernel

theorem rowEval2821 (x : Key → ℝ) : Integer.Sparse.eval row2821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2821, Integer.Sparse.eval_collectBalanced, rawRowCheck2821]

def rawRow2822 : Integer.Sparse Key := [(key3132, -2), (key3132, -2), (key3145, -2), (key3140, 2), (key3140, 2), (key3148, 2), (key2428, 2), (key2428, 2), (key2444, 2), (key2577, -6), (key2430, -2), (key2430, -2), (key2444, -2), (key2510, 6)]

theorem rawRowCheck2822 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form6 = rawRow2822 := by decide +kernel

def row2822 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2510, 6), (key2577, -6), (key3132, -4), (key3140, 4), (key3145, -2), (key3148, 2)]

theorem rowCheck2822 : row2822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2822 := by decide +kernel

theorem rowEval2822 (x : Key → ℝ) : Integer.Sparse.eval row2822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2822, Integer.Sparse.eval_collectBalanced, rawRowCheck2822]

def rawRow2823 : Integer.Sparse Key := [(key3132, -2), (key3145, -2), (key3132, -2), (key3140, 2), (key3148, 2), (key3140, 2), (key2428, 2), (key2444, 2), (key2428, 2), (key2577, -6), (key2430, -2), (key2444, -2), (key2430, -2), (key2510, 6)]

theorem rawRowCheck2823 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form6 = rawRow2823 := by decide +kernel

def row2823 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2510, 6), (key2577, -6), (key3132, -4), (key3140, 4), (key3145, -2), (key3148, 2)]

theorem rowCheck2823 : row2823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2823 := by decide +kernel

theorem rowEval2823 (x : Key → ℝ) : Integer.Sparse.eval row2823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2823, Integer.Sparse.eval_collectBalanced, rawRowCheck2823]

def rawRow2824 : Integer.Sparse Key := [(key3145, -2), (key3132, -2), (key3132, -2), (key3148, 2), (key3140, 2), (key3140, 2), (key2444, 2), (key2428, 2), (key2428, 2), (key2577, -6), (key2444, -2), (key2430, -2), (key2430, -2), (key2510, 6)]

theorem rawRowCheck2824 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form6 = rawRow2824 := by decide +kernel

def row2824 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2510, 6), (key2577, -6), (key3132, -4), (key3140, 4), (key3145, -2), (key3148, 2)]

theorem rowCheck2824 : row2824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2824 := by decide +kernel

theorem rowEval2824 (x : Key → ℝ) : Integer.Sparse.eval row2824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2824, Integer.Sparse.eval_collectBalanced, rawRowCheck2824]

def rawRow2825 : Integer.Sparse Key := [(key3036, -2), (key3042, -2), (key3140, -2), (key3036, 2), (key3040, 2), (key3132, 2), (key3040, 2), (key3044, 2), (key3148, 2), (key2428, -6), (key2430, -2), (key2444, -2), (key2510, -2), (key2430, 6)]

theorem rawRowCheck2825 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form6 = rawRow2825 := by decide +kernel

def row2825 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

theorem rowCheck2825 : row2825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2825 := by decide +kernel

theorem rowEval2825 (x : Key → ℝ) : Integer.Sparse.eval row2825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2825, Integer.Sparse.eval_collectBalanced, rawRowCheck2825]

def rawRow2826 : Integer.Sparse Key := [(key3042, -2), (key3036, -2), (key3140, -2), (key3040, 2), (key3036, 2), (key3132, 2), (key3044, 2), (key3040, 2), (key3148, 2), (key2428, -6), (key2444, -2), (key2430, -2), (key2510, -2), (key2430, 6)]

theorem rawRowCheck2826 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form6 = rawRow2826 := by decide +kernel

def row2826 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

theorem rowCheck2826 : row2826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2826 := by decide +kernel

theorem rowEval2826 (x : Key → ℝ) : Integer.Sparse.eval row2826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2826, Integer.Sparse.eval_collectBalanced, rawRowCheck2826]

def rawRow2827 : Integer.Sparse Key := [(key3036, -2), (key3140, -2), (key3042, -2), (key3036, 2), (key3132, 2), (key3040, 2), (key3040, 2), (key3148, 2), (key3044, 2), (key2428, -6), (key2430, -2), (key2510, -2), (key2444, -2), (key2430, 6)]

theorem rawRowCheck2827 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form6 = rawRow2827 := by decide +kernel

def row2827 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

theorem rowCheck2827 : row2827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2827 := by decide +kernel

theorem rowEval2827 (x : Key → ℝ) : Integer.Sparse.eval row2827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2827, Integer.Sparse.eval_collectBalanced, rawRowCheck2827]

def rawRow2828 : Integer.Sparse Key := [(key3140, -2), (key3036, -2), (key3042, -2), (key3132, 2), (key3036, 2), (key3040, 2), (key3148, 2), (key3040, 2), (key3044, 2), (key2428, -6), (key2510, -2), (key2430, -2), (key2444, -2), (key2430, 6)]

theorem rawRowCheck2828 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form6 = rawRow2828 := by decide +kernel

def row2828 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

theorem rowCheck2828 : row2828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2828 := by decide +kernel

theorem rowEval2828 (x : Key → ℝ) : Integer.Sparse.eval row2828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck2828, Integer.Sparse.eval_collectBalanced, rawRowCheck2828]

def rawRow2829 : Integer.Sparse Key := [(key3042, -2), (key3140, -2), (key3036, -2), (key3040, 2), (key3132, 2), (key3036, 2), (key3044, 2), (key3148, 2), (key3040, 2), (key2428, -6), (key2444, -2), (key2510, -2), (key2430, -2), (key2430, 6)]

theorem rawRowCheck2829 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form6 = rawRow2829 := by decide +kernel

def row2829 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

theorem rowCheck2829 : row2829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2829 := by decide +kernel

theorem rowEval2829 (x : Key → ℝ) : Integer.Sparse.eval row2829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2829, Integer.Sparse.eval_collectBalanced, rawRowCheck2829]

def rawRow2830 : Integer.Sparse Key := [(key3140, -2), (key3042, -2), (key3036, -2), (key3132, 2), (key3040, 2), (key3036, 2), (key3148, 2), (key3044, 2), (key3040, 2), (key2428, -6), (key2510, -2), (key2444, -2), (key2430, -2), (key2430, 6)]

theorem rawRowCheck2830 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form6 = rawRow2830 := by decide +kernel

def row2830 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

theorem rowCheck2830 : row2830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2830 := by decide +kernel

theorem rowEval2830 (x : Key → ℝ) : Integer.Sparse.eval row2830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck2830, Integer.Sparse.eval_collectBalanced, rawRowCheck2830]

def rawRow2831 : Integer.Sparse Key := [(key3132, -2), (key3145, -2), (key3145, -2), (key3140, 2), (key3148, 2), (key3148, 2), (key3036, 2), (key3042, 2), (key3042, 2), (key3140, -6), (key2421, -2), (key2428, -2), (key2428, -2), (key2496, 6)]

theorem rawRowCheck2831 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form6 = rawRow2831 := by decide +kernel

def row2831 : Integer.Sparse Key := [(key2421, -2), (key2428, -4), (key2496, 6), (key3036, 2), (key3042, 4), (key3132, -2), (key3140, -4), (key3145, -4), (key3148, 4)]

theorem rowCheck2831 : row2831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2831 := by decide +kernel

theorem rowEval2831 (x : Key → ℝ) : Integer.Sparse.eval row2831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2831, Integer.Sparse.eval_collectBalanced, rawRowCheck2831]

def rawRow2832 : Integer.Sparse Key := [(key3145, -2), (key3132, -2), (key3145, -2), (key3148, 2), (key3140, 2), (key3148, 2), (key3042, 2), (key3036, 2), (key3042, 2), (key3140, -6), (key2428, -2), (key2421, -2), (key2428, -2), (key2496, 6)]

theorem rawRowCheck2832 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form6 = rawRow2832 := by decide +kernel

def row2832 : Integer.Sparse Key := [(key2421, -2), (key2428, -4), (key2496, 6), (key3036, 2), (key3042, 4), (key3132, -2), (key3140, -4), (key3145, -4), (key3148, 4)]

theorem rowCheck2832 : row2832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2832 := by decide +kernel

theorem rowEval2832 (x : Key → ℝ) : Integer.Sparse.eval row2832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2832, Integer.Sparse.eval_collectBalanced, rawRowCheck2832]

def rawRow2833 : Integer.Sparse Key := [(key3145, -2), (key3145, -2), (key3132, -2), (key3148, 2), (key3148, 2), (key3140, 2), (key3042, 2), (key3042, 2), (key3036, 2), (key3140, -6), (key2428, -2), (key2428, -2), (key2421, -2), (key2496, 6)]

theorem rawRowCheck2833 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form6 = rawRow2833 := by decide +kernel

def row2833 : Integer.Sparse Key := [(key2421, -2), (key2428, -4), (key2496, 6), (key3036, 2), (key3042, 4), (key3132, -2), (key3140, -4), (key3145, -4), (key3148, 4)]

theorem rowCheck2833 : row2833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2833 := by decide +kernel

theorem rowEval2833 (x : Key → ℝ) : Integer.Sparse.eval row2833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2833, Integer.Sparse.eval_collectBalanced, rawRowCheck2833]

def rawRow2834 : Integer.Sparse Key := [(key3040, -2), (key3044, -2), (key3148, -2), (key3042, 2), (key3044, 2), (key3145, 2), (key3036, 2), (key3042, 2), (key3140, 2), (key3042, -6), (key2421, -2), (key2428, -2), (key2496, -2), (key2428, 6)]

theorem rawRowCheck2834 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form6 = rawRow2834 := by decide +kernel

def row2834 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

theorem rowCheck2834 : row2834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2834 := by decide +kernel

theorem rowEval2834 (x : Key → ℝ) : Integer.Sparse.eval row2834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2834, Integer.Sparse.eval_collectBalanced, rawRowCheck2834]

def rawRow2835 : Integer.Sparse Key := [(key3044, -2), (key3040, -2), (key3148, -2), (key3044, 2), (key3042, 2), (key3145, 2), (key3042, 2), (key3036, 2), (key3140, 2), (key3042, -6), (key2428, -2), (key2421, -2), (key2496, -2), (key2428, 6)]

theorem rawRowCheck2835 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form6 = rawRow2835 := by decide +kernel

def row2835 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

theorem rowCheck2835 : row2835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2835 := by decide +kernel

theorem rowEval2835 (x : Key → ℝ) : Integer.Sparse.eval row2835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2835, Integer.Sparse.eval_collectBalanced, rawRowCheck2835]

def rawRow2836 : Integer.Sparse Key := [(key3040, -2), (key3148, -2), (key3044, -2), (key3042, 2), (key3145, 2), (key3044, 2), (key3036, 2), (key3140, 2), (key3042, 2), (key3042, -6), (key2421, -2), (key2496, -2), (key2428, -2), (key2428, 6)]

theorem rawRowCheck2836 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form6 = rawRow2836 := by decide +kernel

def row2836 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

theorem rowCheck2836 : row2836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2836 := by decide +kernel

theorem rowEval2836 (x : Key → ℝ) : Integer.Sparse.eval row2836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2836, Integer.Sparse.eval_collectBalanced, rawRowCheck2836]

def rawRow2837 : Integer.Sparse Key := [(key3148, -2), (key3040, -2), (key3044, -2), (key3145, 2), (key3042, 2), (key3044, 2), (key3140, 2), (key3036, 2), (key3042, 2), (key3042, -6), (key2496, -2), (key2421, -2), (key2428, -2), (key2428, 6)]

theorem rawRowCheck2837 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form6 = rawRow2837 := by decide +kernel

def row2837 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

theorem rowCheck2837 : row2837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2837 := by decide +kernel

theorem rowEval2837 (x : Key → ℝ) : Integer.Sparse.eval row2837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck2837, Integer.Sparse.eval_collectBalanced, rawRowCheck2837]

def rawRow2838 : Integer.Sparse Key := [(key3044, -2), (key3148, -2), (key3040, -2), (key3044, 2), (key3145, 2), (key3042, 2), (key3042, 2), (key3140, 2), (key3036, 2), (key3042, -6), (key2428, -2), (key2496, -2), (key2421, -2), (key2428, 6)]

theorem rawRowCheck2838 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form6 = rawRow2838 := by decide +kernel

def row2838 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

theorem rowCheck2838 : row2838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2838 := by decide +kernel

theorem rowEval2838 (x : Key → ℝ) : Integer.Sparse.eval row2838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2838, Integer.Sparse.eval_collectBalanced, rawRowCheck2838]

def rawRow2839 : Integer.Sparse Key := [(key3148, -2), (key3044, -2), (key3040, -2), (key3145, 2), (key3044, 2), (key3042, 2), (key3140, 2), (key3042, 2), (key3036, 2), (key3042, -6), (key2496, -2), (key2428, -2), (key2421, -2), (key2428, 6)]

theorem rawRowCheck2839 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form6 = rawRow2839 := by decide +kernel

def row2839 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

theorem rowCheck2839 : row2839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2839 := by decide +kernel

theorem rowEval2839 (x : Key → ℝ) : Integer.Sparse.eval row2839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck2839, Integer.Sparse.eval_collectBalanced, rawRowCheck2839]

def rawRow2840 : Integer.Sparse Key := [(key1256, -2), (key1256, -2), (key1261, -2), (key1256, 1), (key1256, 1), (key1265, 1), (key1265, 1), (key1268, 1), (key1268, 1), (key1531, 2), (key1531, 2), (key1536, 2), (key1531, -1), (key1531, -1), (key1765, -1), (key1765, -1), (key1768, -1), (key1768, -1), (key1609, -1), (key1609, -1), (key1648, -1), (key1648, -1), (key1651, -1), (key1651, -1), (key1609, 1), (key1609, 1), (key1806, 1), (key1806, 1), (key1809, 1), (key1809, 1)]

theorem rawRowCheck2840 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form7 = rawRow2840 := by decide +kernel

def row2840 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

theorem rowCheck2840 : row2840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2840 := by decide +kernel

theorem rowEval2840 (x : Key → ℝ) : Integer.Sparse.eval row2840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2840, Integer.Sparse.eval_collectBalanced, rawRowCheck2840]

def rawRow2841 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1256, -2), (key1265, 1), (key1268, 1), (key1256, 1), (key1268, 1), (key1256, 1), (key1265, 1), (key1531, 2), (key1536, 2), (key1531, 2), (key1765, -1), (key1768, -1), (key1531, -1), (key1768, -1), (key1531, -1), (key1765, -1), (key1648, -1), (key1651, -1), (key1609, -1), (key1651, -1), (key1609, -1), (key1648, -1), (key1806, 1), (key1809, 1), (key1609, 1), (key1809, 1), (key1609, 1), (key1806, 1)]

theorem rawRowCheck2841 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form7 = rawRow2841 := by decide +kernel

def row2841 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

theorem rowCheck2841 : row2841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2841 := by decide +kernel

theorem rowEval2841 (x : Key → ℝ) : Integer.Sparse.eval row2841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2841, Integer.Sparse.eval_collectBalanced, rawRowCheck2841]

def rawRow2842 : Integer.Sparse Key := [(key1261, -2), (key1256, -2), (key1256, -2), (key1268, 1), (key1265, 1), (key1268, 1), (key1256, 1), (key1265, 1), (key1256, 1), (key1536, 2), (key1531, 2), (key1531, 2), (key1768, -1), (key1765, -1), (key1768, -1), (key1531, -1), (key1765, -1), (key1531, -1), (key1651, -1), (key1648, -1), (key1651, -1), (key1609, -1), (key1648, -1), (key1609, -1), (key1809, 1), (key1806, 1), (key1809, 1), (key1609, 1), (key1806, 1), (key1609, 1)]

theorem rawRowCheck2842 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form7 = rawRow2842 := by decide +kernel

def row2842 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

theorem rowCheck2842 : row2842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2842 := by decide +kernel

theorem rowEval2842 (x : Key → ℝ) : Integer.Sparse.eval row2842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2842, Integer.Sparse.eval_collectBalanced, rawRowCheck2842]

def rawRow2843 : Integer.Sparse Key := [(key1265, -2), (key1268, -2), (key1268, -2), (key1256, 1), (key1261, 1), (key1256, 1), (key1268, 1), (key1261, 1), (key1268, 1), (key1765, 2), (key1768, 2), (key1768, 2), (key1531, -1), (key1536, -1), (key1531, -1), (key1768, -1), (key1536, -1), (key1768, -1), (key1806, -1), (key1809, -1), (key1806, -1), (key1837, -1), (key1809, -1), (key1837, -1), (key1648, 1), (key1651, 1), (key1648, 1), (key1837, 1), (key1651, 1), (key1837, 1)]

theorem rawRowCheck2843 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form7 = rawRow2843 := by decide +kernel

def row2843 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

theorem rowCheck2843 : row2843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2843 := by decide +kernel

theorem rowEval2843 (x : Key → ℝ) : Integer.Sparse.eval row2843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2843, Integer.Sparse.eval_collectBalanced, rawRowCheck2843]

def rawRow2844 : Integer.Sparse Key := [(key1268, -2), (key1265, -2), (key1268, -2), (key1261, 1), (key1256, 1), (key1268, 1), (key1256, 1), (key1268, 1), (key1261, 1), (key1768, 2), (key1765, 2), (key1768, 2), (key1536, -1), (key1531, -1), (key1768, -1), (key1531, -1), (key1768, -1), (key1536, -1), (key1809, -1), (key1806, -1), (key1837, -1), (key1806, -1), (key1837, -1), (key1809, -1), (key1651, 1), (key1648, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1651, 1)]

theorem rawRowCheck2844 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form7 = rawRow2844 := by decide +kernel

def row2844 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

theorem rowCheck2844 : row2844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2844 := by decide +kernel

theorem rowEval2844 (x : Key → ℝ) : Integer.Sparse.eval row2844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2844, Integer.Sparse.eval_collectBalanced, rawRowCheck2844]

def rawRow2845 : Integer.Sparse Key := [(key1268, -2), (key1268, -2), (key1265, -2), (key1268, 1), (key1268, 1), (key1261, 1), (key1261, 1), (key1256, 1), (key1256, 1), (key1768, 2), (key1768, 2), (key1765, 2), (key1768, -1), (key1768, -1), (key1536, -1), (key1536, -1), (key1531, -1), (key1531, -1), (key1837, -1), (key1837, -1), (key1809, -1), (key1809, -1), (key1806, -1), (key1806, -1), (key1837, 1), (key1837, 1), (key1651, 1), (key1651, 1), (key1648, 1), (key1648, 1)]

theorem rawRowCheck2845 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form7 = rawRow2845 := by decide +kernel

def row2845 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

theorem rowCheck2845 : row2845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2845 := by decide +kernel

theorem rowEval2845 (x : Key → ℝ) : Integer.Sparse.eval row2845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2845, Integer.Sparse.eval_collectBalanced, rawRowCheck2845]

def rawRow2846 : Integer.Sparse Key := [(key1531, -2), (key1531, -2), (key1536, -2), (key1609, 1), (key1609, 1), (key1648, 1), (key1648, 1), (key1651, 1), (key1651, 1), (key1256, 2), (key1256, 2), (key1261, 2), (key1609, -1), (key1609, -1), (key1806, -1), (key1806, -1), (key1809, -1), (key1809, -1), (key1256, -1), (key1256, -1), (key1265, -1), (key1265, -1), (key1268, -1), (key1268, -1), (key1531, 1), (key1531, 1), (key1765, 1), (key1765, 1), (key1768, 1), (key1768, 1)]

theorem rawRowCheck2846 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form7 = rawRow2846 := by decide +kernel

def row2846 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

theorem rowCheck2846 : row2846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2846 := by decide +kernel

theorem rowEval2846 (x : Key → ℝ) : Integer.Sparse.eval row2846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2846, Integer.Sparse.eval_collectBalanced, rawRowCheck2846]

def rawRow2847 : Integer.Sparse Key := [(key1531, -2), (key1536, -2), (key1531, -2), (key1648, 1), (key1651, 1), (key1609, 1), (key1651, 1), (key1609, 1), (key1648, 1), (key1256, 2), (key1261, 2), (key1256, 2), (key1806, -1), (key1809, -1), (key1609, -1), (key1809, -1), (key1609, -1), (key1806, -1), (key1265, -1), (key1268, -1), (key1256, -1), (key1268, -1), (key1256, -1), (key1265, -1), (key1765, 1), (key1768, 1), (key1531, 1), (key1768, 1), (key1531, 1), (key1765, 1)]

theorem rawRowCheck2847 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form7 = rawRow2847 := by decide +kernel

def row2847 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

theorem rowCheck2847 : row2847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2847 := by decide +kernel

theorem rowEval2847 (x : Key → ℝ) : Integer.Sparse.eval row2847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2847, Integer.Sparse.eval_collectBalanced, rawRowCheck2847]

def rawRow2848 : Integer.Sparse Key := [(key1536, -2), (key1531, -2), (key1531, -2), (key1651, 1), (key1648, 1), (key1651, 1), (key1609, 1), (key1648, 1), (key1609, 1), (key1261, 2), (key1256, 2), (key1256, 2), (key1809, -1), (key1806, -1), (key1809, -1), (key1609, -1), (key1806, -1), (key1609, -1), (key1268, -1), (key1265, -1), (key1268, -1), (key1256, -1), (key1265, -1), (key1256, -1), (key1768, 1), (key1765, 1), (key1768, 1), (key1531, 1), (key1765, 1), (key1531, 1)]

theorem rawRowCheck2848 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form7 = rawRow2848 := by decide +kernel

def row2848 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

theorem rowCheck2848 : row2848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2848 := by decide +kernel

theorem rowEval2848 (x : Key → ℝ) : Integer.Sparse.eval row2848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2848, Integer.Sparse.eval_collectBalanced, rawRowCheck2848]

def rawRow2849 : Integer.Sparse Key := [(key1648, -2), (key1651, -2), (key1674, -2), (key1531, 1), (key1536, 1), (key1609, 1), (key1651, 1), (key1642, 1), (key1674, 1), (key1806, 2), (key1809, 2), (key1832, 2), (key1256, -1), (key1261, -1), (key1609, -1), (key1809, -1), (key1642, -1), (key1832, -1), (key1765, -1), (key1768, -1), (key1806, -1), (key1837, -1), (key1832, -1), (key1848, -1), (key1265, 1), (key1268, 1), (key1648, 1), (key1837, 1), (key1674, 1), (key1848, 1)]

theorem rawRowCheck2849 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form7 = rawRow2849 := by decide +kernel

def row2849 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

theorem rowCheck2849 : row2849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2849 := by decide +kernel

theorem rowEval2849 (x : Key → ℝ) : Integer.Sparse.eval row2849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2849, Integer.Sparse.eval_collectBalanced, rawRowCheck2849]

def rawRow2850 : Integer.Sparse Key := [(key1651, -2), (key1648, -2), (key1674, -2), (key1536, 1), (key1531, 1), (key1651, 1), (key1609, 1), (key1674, 1), (key1642, 1), (key1809, 2), (key1806, 2), (key1832, 2), (key1261, -1), (key1256, -1), (key1809, -1), (key1609, -1), (key1832, -1), (key1642, -1), (key1768, -1), (key1765, -1), (key1837, -1), (key1806, -1), (key1848, -1), (key1832, -1), (key1268, 1), (key1265, 1), (key1837, 1), (key1648, 1), (key1848, 1), (key1674, 1)]

theorem rawRowCheck2850 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form7 = rawRow2850 := by decide +kernel

def row2850 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

theorem rowCheck2850 : row2850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2850 := by decide +kernel

theorem rowEval2850 (x : Key → ℝ) : Integer.Sparse.eval row2850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2850, Integer.Sparse.eval_collectBalanced, rawRowCheck2850]

def rawRow2851 : Integer.Sparse Key := [(key1648, -2), (key1674, -2), (key1651, -2), (key1609, 1), (key1642, 1), (key1531, 1), (key1674, 1), (key1536, 1), (key1651, 1), (key1806, 2), (key1832, 2), (key1809, 2), (key1609, -1), (key1642, -1), (key1256, -1), (key1832, -1), (key1261, -1), (key1809, -1), (key1806, -1), (key1832, -1), (key1765, -1), (key1848, -1), (key1768, -1), (key1837, -1), (key1648, 1), (key1674, 1), (key1265, 1), (key1848, 1), (key1268, 1), (key1837, 1)]

theorem rawRowCheck2851 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form7 = rawRow2851 := by decide +kernel

def row2851 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

theorem rowCheck2851 : row2851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2851 := by decide +kernel

theorem rowEval2851 (x : Key → ℝ) : Integer.Sparse.eval row2851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2851, Integer.Sparse.eval_collectBalanced, rawRowCheck2851]

def rawRow2852 : Integer.Sparse Key := [(key1674, -2), (key1648, -2), (key1651, -2), (key1642, 1), (key1609, 1), (key1674, 1), (key1531, 1), (key1651, 1), (key1536, 1), (key1832, 2), (key1806, 2), (key1809, 2), (key1642, -1), (key1609, -1), (key1832, -1), (key1256, -1), (key1809, -1), (key1261, -1), (key1832, -1), (key1806, -1), (key1848, -1), (key1765, -1), (key1837, -1), (key1768, -1), (key1674, 1), (key1648, 1), (key1848, 1), (key1265, 1), (key1837, 1), (key1268, 1)]

theorem rawRowCheck2852 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form7 = rawRow2852 := by decide +kernel

def row2852 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

theorem rowCheck2852 : row2852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2852 := by decide +kernel

theorem rowEval2852 (x : Key → ℝ) : Integer.Sparse.eval row2852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck2852, Integer.Sparse.eval_collectBalanced, rawRowCheck2852]

def rawRow2853 : Integer.Sparse Key := [(key1651, -2), (key1674, -2), (key1648, -2), (key1651, 1), (key1674, 1), (key1536, 1), (key1642, 1), (key1531, 1), (key1609, 1), (key1809, 2), (key1832, 2), (key1806, 2), (key1809, -1), (key1832, -1), (key1261, -1), (key1642, -1), (key1256, -1), (key1609, -1), (key1837, -1), (key1848, -1), (key1768, -1), (key1832, -1), (key1765, -1), (key1806, -1), (key1837, 1), (key1848, 1), (key1268, 1), (key1674, 1), (key1265, 1), (key1648, 1)]

theorem rawRowCheck2853 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form7 = rawRow2853 := by decide +kernel

def row2853 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

theorem rowCheck2853 : row2853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2853 := by decide +kernel

theorem rowEval2853 (x : Key → ℝ) : Integer.Sparse.eval row2853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2853, Integer.Sparse.eval_collectBalanced, rawRowCheck2853]

def rawRow2854 : Integer.Sparse Key := [(key1674, -2), (key1651, -2), (key1648, -2), (key1674, 1), (key1651, 1), (key1642, 1), (key1536, 1), (key1609, 1), (key1531, 1), (key1832, 2), (key1809, 2), (key1806, 2), (key1832, -1), (key1809, -1), (key1642, -1), (key1261, -1), (key1609, -1), (key1256, -1), (key1848, -1), (key1837, -1), (key1832, -1), (key1768, -1), (key1806, -1), (key1765, -1), (key1848, 1), (key1837, 1), (key1674, 1), (key1268, 1), (key1648, 1), (key1265, 1)]

theorem rawRowCheck2854 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form7 = rawRow2854 := by decide +kernel

def row2854 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

theorem rowCheck2854 : row2854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2854 := by decide +kernel

theorem rowEval2854 (x : Key → ℝ) : Integer.Sparse.eval row2854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck2854, Integer.Sparse.eval_collectBalanced, rawRowCheck2854]

def rawRow2855 : Integer.Sparse Key := [(key1765, -2), (key1768, -2), (key1768, -2), (key1806, 1), (key1809, 1), (key1806, 1), (key1837, 1), (key1809, 1), (key1837, 1), (key1265, 2), (key1268, 2), (key1268, 2), (key1648, -1), (key1651, -1), (key1648, -1), (key1837, -1), (key1651, -1), (key1837, -1), (key1256, -1), (key1261, -1), (key1256, -1), (key1268, -1), (key1261, -1), (key1268, -1), (key1531, 1), (key1536, 1), (key1531, 1), (key1768, 1), (key1536, 1), (key1768, 1)]

theorem rawRowCheck2855 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form7 = rawRow2855 := by decide +kernel

def row2855 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

theorem rowCheck2855 : row2855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2855 := by decide +kernel

theorem rowEval2855 (x : Key → ℝ) : Integer.Sparse.eval row2855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2855, Integer.Sparse.eval_collectBalanced, rawRowCheck2855]

def rawRow2856 : Integer.Sparse Key := [(key1768, -2), (key1765, -2), (key1768, -2), (key1809, 1), (key1806, 1), (key1837, 1), (key1806, 1), (key1837, 1), (key1809, 1), (key1268, 2), (key1265, 2), (key1268, 2), (key1651, -1), (key1648, -1), (key1837, -1), (key1648, -1), (key1837, -1), (key1651, -1), (key1261, -1), (key1256, -1), (key1268, -1), (key1256, -1), (key1268, -1), (key1261, -1), (key1536, 1), (key1531, 1), (key1768, 1), (key1531, 1), (key1768, 1), (key1536, 1)]

theorem rawRowCheck2856 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form7 = rawRow2856 := by decide +kernel

def row2856 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

theorem rowCheck2856 : row2856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2856 := by decide +kernel

theorem rowEval2856 (x : Key → ℝ) : Integer.Sparse.eval row2856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2856, Integer.Sparse.eval_collectBalanced, rawRowCheck2856]

def rawRow2857 : Integer.Sparse Key := [(key1768, -2), (key1768, -2), (key1765, -2), (key1837, 1), (key1837, 1), (key1809, 1), (key1809, 1), (key1806, 1), (key1806, 1), (key1268, 2), (key1268, 2), (key1265, 2), (key1837, -1), (key1837, -1), (key1651, -1), (key1651, -1), (key1648, -1), (key1648, -1), (key1268, -1), (key1268, -1), (key1261, -1), (key1261, -1), (key1256, -1), (key1256, -1), (key1768, 1), (key1768, 1), (key1536, 1), (key1536, 1), (key1531, 1), (key1531, 1)]

theorem rawRowCheck2857 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form7 = rawRow2857 := by decide +kernel

def row2857 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

theorem rowCheck2857 : row2857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2857 := by decide +kernel

theorem rowEval2857 (x : Key → ℝ) : Integer.Sparse.eval row2857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2857, Integer.Sparse.eval_collectBalanced, rawRowCheck2857]

def rawRow2858 : Integer.Sparse Key := [(key1806, -2), (key1809, -2), (key1832, -2), (key1765, 1), (key1768, 1), (key1806, 1), (key1837, 1), (key1832, 1), (key1848, 1), (key1648, 2), (key1651, 2), (key1674, 2), (key1265, -1), (key1268, -1), (key1648, -1), (key1837, -1), (key1674, -1), (key1848, -1), (key1531, -1), (key1536, -1), (key1609, -1), (key1651, -1), (key1642, -1), (key1674, -1), (key1256, 1), (key1261, 1), (key1609, 1), (key1809, 1), (key1642, 1), (key1832, 1)]

theorem rawRowCheck2858 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form7 = rawRow2858 := by decide +kernel

def row2858 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

theorem rowCheck2858 : row2858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2858 := by decide +kernel

theorem rowEval2858 (x : Key → ℝ) : Integer.Sparse.eval row2858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2858, Integer.Sparse.eval_collectBalanced, rawRowCheck2858]

def rawRow2859 : Integer.Sparse Key := [(key1809, -2), (key1806, -2), (key1832, -2), (key1768, 1), (key1765, 1), (key1837, 1), (key1806, 1), (key1848, 1), (key1832, 1), (key1651, 2), (key1648, 2), (key1674, 2), (key1268, -1), (key1265, -1), (key1837, -1), (key1648, -1), (key1848, -1), (key1674, -1), (key1536, -1), (key1531, -1), (key1651, -1), (key1609, -1), (key1674, -1), (key1642, -1), (key1261, 1), (key1256, 1), (key1809, 1), (key1609, 1), (key1832, 1), (key1642, 1)]

theorem rawRowCheck2859 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form7 = rawRow2859 := by decide +kernel

def row2859 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

theorem rowCheck2859 : row2859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2859 := by decide +kernel

theorem rowEval2859 (x : Key → ℝ) : Integer.Sparse.eval row2859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2859, Integer.Sparse.eval_collectBalanced, rawRowCheck2859]

def rawRow2860 : Integer.Sparse Key := [(key1806, -2), (key1832, -2), (key1809, -2), (key1806, 1), (key1832, 1), (key1765, 1), (key1848, 1), (key1768, 1), (key1837, 1), (key1648, 2), (key1674, 2), (key1651, 2), (key1648, -1), (key1674, -1), (key1265, -1), (key1848, -1), (key1268, -1), (key1837, -1), (key1609, -1), (key1642, -1), (key1531, -1), (key1674, -1), (key1536, -1), (key1651, -1), (key1609, 1), (key1642, 1), (key1256, 1), (key1832, 1), (key1261, 1), (key1809, 1)]

theorem rawRowCheck2860 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form7 = rawRow2860 := by decide +kernel

def row2860 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

theorem rowCheck2860 : row2860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2860 := by decide +kernel

theorem rowEval2860 (x : Key → ℝ) : Integer.Sparse.eval row2860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2860, Integer.Sparse.eval_collectBalanced, rawRowCheck2860]

def rawRow2861 : Integer.Sparse Key := [(key1832, -2), (key1806, -2), (key1809, -2), (key1832, 1), (key1806, 1), (key1848, 1), (key1765, 1), (key1837, 1), (key1768, 1), (key1674, 2), (key1648, 2), (key1651, 2), (key1674, -1), (key1648, -1), (key1848, -1), (key1265, -1), (key1837, -1), (key1268, -1), (key1642, -1), (key1609, -1), (key1674, -1), (key1531, -1), (key1651, -1), (key1536, -1), (key1642, 1), (key1609, 1), (key1832, 1), (key1256, 1), (key1809, 1), (key1261, 1)]

theorem rawRowCheck2861 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form7 = rawRow2861 := by decide +kernel

def row2861 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

theorem rowCheck2861 : row2861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2861 := by decide +kernel

theorem rowEval2861 (x : Key → ℝ) : Integer.Sparse.eval row2861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck2861, Integer.Sparse.eval_collectBalanced, rawRowCheck2861]

def rawRow2862 : Integer.Sparse Key := [(key1809, -2), (key1832, -2), (key1806, -2), (key1837, 1), (key1848, 1), (key1768, 1), (key1832, 1), (key1765, 1), (key1806, 1), (key1651, 2), (key1674, 2), (key1648, 2), (key1837, -1), (key1848, -1), (key1268, -1), (key1674, -1), (key1265, -1), (key1648, -1), (key1651, -1), (key1674, -1), (key1536, -1), (key1642, -1), (key1531, -1), (key1609, -1), (key1809, 1), (key1832, 1), (key1261, 1), (key1642, 1), (key1256, 1), (key1609, 1)]

theorem rawRowCheck2862 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form7 = rawRow2862 := by decide +kernel

def row2862 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

theorem rowCheck2862 : row2862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2862 := by decide +kernel

theorem rowEval2862 (x : Key → ℝ) : Integer.Sparse.eval row2862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2862, Integer.Sparse.eval_collectBalanced, rawRowCheck2862]

def rawRow2863 : Integer.Sparse Key := [(key1832, -2), (key1809, -2), (key1806, -2), (key1848, 1), (key1837, 1), (key1832, 1), (key1768, 1), (key1806, 1), (key1765, 1), (key1674, 2), (key1651, 2), (key1648, 2), (key1848, -1), (key1837, -1), (key1674, -1), (key1268, -1), (key1648, -1), (key1265, -1), (key1674, -1), (key1651, -1), (key1642, -1), (key1536, -1), (key1609, -1), (key1531, -1), (key1832, 1), (key1809, 1), (key1642, 1), (key1261, 1), (key1609, 1), (key1256, 1)]

theorem rawRowCheck2863 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form7 = rawRow2863 := by decide +kernel

def row2863 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

theorem rowCheck2863 : row2863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2863 := by decide +kernel

theorem rowEval2863 (x : Key → ℝ) : Integer.Sparse.eval row2863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck2863, Integer.Sparse.eval_collectBalanced, rawRowCheck2863]

def rawRow2864 : Integer.Sparse Key := [(key976, -2), (key976, -2), (key983, -2), (key983, 6), (key1090, 2), (key1090, 2), (key1097, 2), (key1097, -2), (key1182, -2), (key1182, -2), (key1168, -6), (key1168, 2), (key1219, 2), (key1219, 2)]

theorem rawRowCheck2864 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form8 = rawRow2864 := by decide +kernel

def row2864 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

theorem rowCheck2864 : row2864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2864 := by decide +kernel

theorem rowEval2864 (x : Key → ℝ) : Integer.Sparse.eval row2864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2864, Integer.Sparse.eval_collectBalanced, rawRowCheck2864]

def rawRow2865 : Integer.Sparse Key := [(key976, -2), (key983, -2), (key976, -2), (key983, 6), (key1090, 2), (key1097, 2), (key1090, 2), (key1182, -2), (key1097, -2), (key1182, -2), (key1168, -6), (key1219, 2), (key1168, 2), (key1219, 2)]

theorem rawRowCheck2865 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form8 = rawRow2865 := by decide +kernel

def row2865 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

theorem rowCheck2865 : row2865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2865 := by decide +kernel

theorem rowEval2865 (x : Key → ℝ) : Integer.Sparse.eval row2865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2865, Integer.Sparse.eval_collectBalanced, rawRowCheck2865]

def rawRow2866 : Integer.Sparse Key := [(key983, -2), (key976, -2), (key976, -2), (key983, 6), (key1097, 2), (key1090, 2), (key1090, 2), (key1182, -2), (key1182, -2), (key1097, -2), (key1168, -6), (key1219, 2), (key1219, 2), (key1168, 2)]

theorem rawRowCheck2866 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form8 = rawRow2866 := by decide +kernel

def row2866 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

theorem rowCheck2866 : row2866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2866 := by decide +kernel

theorem rowEval2866 (x : Key → ℝ) : Integer.Sparse.eval row2866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2866, Integer.Sparse.eval_collectBalanced, rawRowCheck2866]

def rawRow2867 : Integer.Sparse Key := [(key976, -2), (key983, -2), (key983, -2), (key976, 6), (key1180, 2), (key1182, 2), (key1182, 2), (key1090, -2), (key1090, -2), (key1180, -2), (key1219, -6), (key1168, 2), (key1168, 2), (key1219, 2)]

theorem rawRowCheck2867 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form8 = rawRow2867 := by decide +kernel

def row2867 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

theorem rowCheck2867 : row2867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2867 := by decide +kernel

theorem rowEval2867 (x : Key → ℝ) : Integer.Sparse.eval row2867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2867, Integer.Sparse.eval_collectBalanced, rawRowCheck2867]

def rawRow2868 : Integer.Sparse Key := [(key983, -2), (key976, -2), (key983, -2), (key976, 6), (key1182, 2), (key1180, 2), (key1182, 2), (key1090, -2), (key1180, -2), (key1090, -2), (key1219, -6), (key1168, 2), (key1219, 2), (key1168, 2)]

theorem rawRowCheck2868 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form8 = rawRow2868 := by decide +kernel

def row2868 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

theorem rowCheck2868 : row2868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2868 := by decide +kernel

theorem rowEval2868 (x : Key → ℝ) : Integer.Sparse.eval row2868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2868, Integer.Sparse.eval_collectBalanced, rawRowCheck2868]

def rawRow2869 : Integer.Sparse Key := [(key983, -2), (key983, -2), (key976, -2), (key976, 6), (key1182, 2), (key1182, 2), (key1180, 2), (key1180, -2), (key1090, -2), (key1090, -2), (key1219, -6), (key1219, 2), (key1168, 2), (key1168, 2)]

theorem rawRowCheck2869 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form8 = rawRow2869 := by decide +kernel

def row2869 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

theorem rowCheck2869 : row2869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2869 := by decide +kernel

theorem rowEval2869 (x : Key → ℝ) : Integer.Sparse.eval row2869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2869, Integer.Sparse.eval_collectBalanced, rawRowCheck2869]

def rawRow2870 : Integer.Sparse Key := [(key1090, -2), (key1090, -2), (key1097, -2), (key1168, 6), (key976, 2), (key976, 2), (key983, 2), (key1168, -2), (key1219, -2), (key1219, -2), (key983, -6), (key1097, 2), (key1182, 2), (key1182, 2)]

theorem rawRowCheck2870 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form8 = rawRow2870 := by decide +kernel

def row2870 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

theorem rowCheck2870 : row2870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2870 := by decide +kernel

theorem rowEval2870 (x : Key → ℝ) : Integer.Sparse.eval row2870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2870, Integer.Sparse.eval_collectBalanced, rawRowCheck2870]

def rawRow2871 : Integer.Sparse Key := [(key1090, -2), (key1097, -2), (key1090, -2), (key1168, 6), (key976, 2), (key983, 2), (key976, 2), (key1219, -2), (key1168, -2), (key1219, -2), (key983, -6), (key1182, 2), (key1097, 2), (key1182, 2)]

theorem rawRowCheck2871 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form8 = rawRow2871 := by decide +kernel

def row2871 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

theorem rowCheck2871 : row2871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2871 := by decide +kernel

theorem rowEval2871 (x : Key → ℝ) : Integer.Sparse.eval row2871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2871, Integer.Sparse.eval_collectBalanced, rawRowCheck2871]

def rawRow2872 : Integer.Sparse Key := [(key1097, -2), (key1090, -2), (key1090, -2), (key1168, 6), (key983, 2), (key976, 2), (key976, 2), (key1219, -2), (key1219, -2), (key1168, -2), (key983, -6), (key1182, 2), (key1182, 2), (key1097, 2)]

theorem rawRowCheck2872 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form8 = rawRow2872 := by decide +kernel

def row2872 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

theorem rowCheck2872 : row2872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2872 := by decide +kernel

theorem rowEval2872 (x : Key → ℝ) : Integer.Sparse.eval row2872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2872, Integer.Sparse.eval_collectBalanced, rawRowCheck2872]

def rawRow2873 : Integer.Sparse Key := [(key1090, -2), (key1097, -2), (key1168, -2), (key1090, 6), (key1180, 2), (key1182, 2), (key1219, 2), (key976, -2), (key1090, -2), (key1180, -2), (key1182, -6), (key983, 2), (key1097, 2), (key1182, 2)]

theorem rawRowCheck2873 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form8 = rawRow2873 := by decide +kernel

def row2873 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

theorem rowCheck2873 : row2873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2873 := by decide +kernel

theorem rowEval2873 (x : Key → ℝ) : Integer.Sparse.eval row2873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2873, Integer.Sparse.eval_collectBalanced, rawRowCheck2873]

def rawRow2874 : Integer.Sparse Key := [(key1097, -2), (key1090, -2), (key1168, -2), (key1090, 6), (key1182, 2), (key1180, 2), (key1219, 2), (key976, -2), (key1180, -2), (key1090, -2), (key1182, -6), (key983, 2), (key1182, 2), (key1097, 2)]

theorem rawRowCheck2874 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form8 = rawRow2874 := by decide +kernel

def row2874 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

theorem rowCheck2874 : row2874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2874 := by decide +kernel

theorem rowEval2874 (x : Key → ℝ) : Integer.Sparse.eval row2874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2874, Integer.Sparse.eval_collectBalanced, rawRowCheck2874]

def rawRow2875 : Integer.Sparse Key := [(key1090, -2), (key1168, -2), (key1097, -2), (key1090, 6), (key1180, 2), (key1219, 2), (key1182, 2), (key1090, -2), (key976, -2), (key1180, -2), (key1182, -6), (key1097, 2), (key983, 2), (key1182, 2)]

theorem rawRowCheck2875 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form8 = rawRow2875 := by decide +kernel

def row2875 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

theorem rowCheck2875 : row2875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2875 := by decide +kernel

theorem rowEval2875 (x : Key → ℝ) : Integer.Sparse.eval row2875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2875, Integer.Sparse.eval_collectBalanced, rawRowCheck2875]

def rawRow2876 : Integer.Sparse Key := [(key1168, -2), (key1090, -2), (key1097, -2), (key1090, 6), (key1219, 2), (key1180, 2), (key1182, 2), (key1090, -2), (key1180, -2), (key976, -2), (key1182, -6), (key1097, 2), (key1182, 2), (key983, 2)]

theorem rawRowCheck2876 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form8 = rawRow2876 := by decide +kernel

def row2876 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

theorem rowCheck2876 : row2876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2876 := by decide +kernel

theorem rowEval2876 (x : Key → ℝ) : Integer.Sparse.eval row2876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck2876, Integer.Sparse.eval_collectBalanced, rawRowCheck2876]

def rawRow2877 : Integer.Sparse Key := [(key1097, -2), (key1168, -2), (key1090, -2), (key1090, 6), (key1182, 2), (key1219, 2), (key1180, 2), (key1180, -2), (key976, -2), (key1090, -2), (key1182, -6), (key1182, 2), (key983, 2), (key1097, 2)]

theorem rawRowCheck2877 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form8 = rawRow2877 := by decide +kernel

def row2877 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

theorem rowCheck2877 : row2877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2877 := by decide +kernel

theorem rowEval2877 (x : Key → ℝ) : Integer.Sparse.eval row2877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2877, Integer.Sparse.eval_collectBalanced, rawRowCheck2877]

def rawRow2878 : Integer.Sparse Key := [(key1168, -2), (key1097, -2), (key1090, -2), (key1090, 6), (key1219, 2), (key1182, 2), (key1180, 2), (key1180, -2), (key1090, -2), (key976, -2), (key1182, -6), (key1182, 2), (key1097, 2), (key983, 2)]

theorem rawRowCheck2878 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form8 = rawRow2878 := by decide +kernel

def row2878 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

theorem rowCheck2878 : row2878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2878 := by decide +kernel

theorem rowEval2878 (x : Key → ℝ) : Integer.Sparse.eval row2878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck2878, Integer.Sparse.eval_collectBalanced, rawRowCheck2878]

def rawRow2879 : Integer.Sparse Key := [(key1180, -2), (key1182, -2), (key1182, -2), (key1219, 6), (key976, 2), (key983, 2), (key983, 2), (key1168, -2), (key1168, -2), (key1219, -2), (key976, -6), (key1090, 2), (key1090, 2), (key1180, 2)]

theorem rawRowCheck2879 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form8 = rawRow2879 := by decide +kernel

def row2879 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

theorem rowCheck2879 : row2879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2879 := by decide +kernel

theorem rowEval2879 (x : Key → ℝ) : Integer.Sparse.eval row2879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2879, Integer.Sparse.eval_collectBalanced, rawRowCheck2879]

def rawRow2880 : Integer.Sparse Key := [(key1182, -2), (key1180, -2), (key1182, -2), (key1219, 6), (key983, 2), (key976, 2), (key983, 2), (key1168, -2), (key1219, -2), (key1168, -2), (key976, -6), (key1090, 2), (key1180, 2), (key1090, 2)]

theorem rawRowCheck2880 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form8 = rawRow2880 := by decide +kernel

def row2880 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

theorem rowCheck2880 : row2880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2880 := by decide +kernel

theorem rowEval2880 (x : Key → ℝ) : Integer.Sparse.eval row2880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2880, Integer.Sparse.eval_collectBalanced, rawRowCheck2880]

def rawRow2881 : Integer.Sparse Key := [(key1182, -2), (key1182, -2), (key1180, -2), (key1219, 6), (key983, 2), (key983, 2), (key976, 2), (key1219, -2), (key1168, -2), (key1168, -2), (key976, -6), (key1180, 2), (key1090, 2), (key1090, 2)]

theorem rawRowCheck2881 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form8 = rawRow2881 := by decide +kernel

def row2881 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

theorem rowCheck2881 : row2881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2881 := by decide +kernel

theorem rowEval2881 (x : Key → ℝ) : Integer.Sparse.eval row2881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2881, Integer.Sparse.eval_collectBalanced, rawRowCheck2881]

def rawRow2882 : Integer.Sparse Key := [(key1180, -2), (key1182, -2), (key1219, -2), (key1182, 6), (key1090, 2), (key1097, 2), (key1168, 2), (key983, -2), (key1097, -2), (key1182, -2), (key1090, -6), (key976, 2), (key1090, 2), (key1180, 2)]

theorem rawRowCheck2882 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form8 = rawRow2882 := by decide +kernel

def row2882 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

theorem rowCheck2882 : row2882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2882 := by decide +kernel

theorem rowEval2882 (x : Key → ℝ) : Integer.Sparse.eval row2882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2882, Integer.Sparse.eval_collectBalanced, rawRowCheck2882]

def rawRow2883 : Integer.Sparse Key := [(key1182, -2), (key1180, -2), (key1219, -2), (key1182, 6), (key1097, 2), (key1090, 2), (key1168, 2), (key983, -2), (key1182, -2), (key1097, -2), (key1090, -6), (key976, 2), (key1180, 2), (key1090, 2)]

theorem rawRowCheck2883 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form8 = rawRow2883 := by decide +kernel

def row2883 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

theorem rowCheck2883 : row2883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2883 := by decide +kernel

theorem rowEval2883 (x : Key → ℝ) : Integer.Sparse.eval row2883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2883, Integer.Sparse.eval_collectBalanced, rawRowCheck2883]

def rawRow2884 : Integer.Sparse Key := [(key1180, -2), (key1219, -2), (key1182, -2), (key1182, 6), (key1090, 2), (key1168, 2), (key1097, 2), (key1097, -2), (key983, -2), (key1182, -2), (key1090, -6), (key1090, 2), (key976, 2), (key1180, 2)]

theorem rawRowCheck2884 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form8 = rawRow2884 := by decide +kernel

def row2884 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

theorem rowCheck2884 : row2884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2884 := by decide +kernel

theorem rowEval2884 (x : Key → ℝ) : Integer.Sparse.eval row2884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2884, Integer.Sparse.eval_collectBalanced, rawRowCheck2884]

def rawRow2885 : Integer.Sparse Key := [(key1219, -2), (key1180, -2), (key1182, -2), (key1182, 6), (key1168, 2), (key1090, 2), (key1097, 2), (key1097, -2), (key1182, -2), (key983, -2), (key1090, -6), (key1090, 2), (key1180, 2), (key976, 2)]

theorem rawRowCheck2885 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form8 = rawRow2885 := by decide +kernel

def row2885 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

theorem rowCheck2885 : row2885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2885 := by decide +kernel

theorem rowEval2885 (x : Key → ℝ) : Integer.Sparse.eval row2885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck2885, Integer.Sparse.eval_collectBalanced, rawRowCheck2885]

def rawRow2886 : Integer.Sparse Key := [(key1182, -2), (key1219, -2), (key1180, -2), (key1182, 6), (key1097, 2), (key1168, 2), (key1090, 2), (key1182, -2), (key983, -2), (key1097, -2), (key1090, -6), (key1180, 2), (key976, 2), (key1090, 2)]

theorem rawRowCheck2886 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form8 = rawRow2886 := by decide +kernel

def row2886 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

theorem rowCheck2886 : row2886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2886 := by decide +kernel

theorem rowEval2886 (x : Key → ℝ) : Integer.Sparse.eval row2886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2886, Integer.Sparse.eval_collectBalanced, rawRowCheck2886]

def rawRow2887 : Integer.Sparse Key := [(key1219, -2), (key1182, -2), (key1180, -2), (key1182, 6), (key1168, 2), (key1097, 2), (key1090, 2), (key1182, -2), (key1097, -2), (key983, -2), (key1090, -6), (key1180, 2), (key1090, 2), (key976, 2)]

theorem rawRowCheck2887 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form8 = rawRow2887 := by decide +kernel

def row2887 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

theorem rowCheck2887 : row2887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2887 := by decide +kernel

theorem rowEval2887 (x : Key → ℝ) : Integer.Sparse.eval row2887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck2887, Integer.Sparse.eval_collectBalanced, rawRowCheck2887]

def rawRow2888 : Integer.Sparse Key := [(key2379, -2), (key2393, -2), (key2393, -2), (key2382, 1), (key2382, 1), (key2393, 1), (key2393, 1), (key2395, 1), (key2395, 1), (key2473, 2), (key2483, 2), (key2483, 2), (key2483, -1), (key2483, -1), (key2507, -1), (key2507, -1), (key2526, -1), (key2526, -1), (key2539, -1), (key2539, -1), (key2544, -1), (key2544, -1), (key2545, -1), (key2545, -1), (key2544, 1), (key2544, 1), (key2555, 1), (key2555, 1), (key2565, 1), (key2565, 1)]

theorem rawRowCheck2888 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form9 = rawRow2888 := by decide +kernel

def row2888 : Integer.Sparse Key := [(key2379, -2), (key2382, 2), (key2393, -2), (key2395, 2), (key2473, 2), (key2483, 2), (key2507, -2), (key2526, -2), (key2539, -2), (key2545, -2), (key2555, 2), (key2565, 2)]

theorem rowCheck2888 : row2888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2888 := by decide +kernel

theorem rowEval2888 (x : Key → ℝ) : Integer.Sparse.eval row2888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2888, Integer.Sparse.eval_collectBalanced, rawRowCheck2888]

def rawRow2889 : Integer.Sparse Key := [(key2393, -2), (key2379, -2), (key2393, -2), (key2393, 1), (key2395, 1), (key2382, 1), (key2395, 1), (key2382, 1), (key2393, 1), (key2483, 2), (key2473, 2), (key2483, 2), (key2507, -1), (key2526, -1), (key2483, -1), (key2526, -1), (key2483, -1), (key2507, -1), (key2544, -1), (key2545, -1), (key2539, -1), (key2545, -1), (key2539, -1), (key2544, -1), (key2555, 1), (key2565, 1), (key2544, 1), (key2565, 1), (key2544, 1), (key2555, 1)]

theorem rawRowCheck2889 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form9 = rawRow2889 := by decide +kernel

def row2889 : Integer.Sparse Key := [(key2379, -2), (key2382, 2), (key2393, -2), (key2395, 2), (key2473, 2), (key2483, 2), (key2507, -2), (key2526, -2), (key2539, -2), (key2545, -2), (key2555, 2), (key2565, 2)]

theorem rowCheck2889 : row2889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2889 := by decide +kernel

theorem rowEval2889 (x : Key → ℝ) : Integer.Sparse.eval row2889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2889, Integer.Sparse.eval_collectBalanced, rawRowCheck2889]

def rawRow2890 : Integer.Sparse Key := [(key2393, -2), (key2393, -2), (key2379, -2), (key2395, 1), (key2393, 1), (key2395, 1), (key2382, 1), (key2393, 1), (key2382, 1), (key2483, 2), (key2483, 2), (key2473, 2), (key2526, -1), (key2507, -1), (key2526, -1), (key2483, -1), (key2507, -1), (key2483, -1), (key2545, -1), (key2544, -1), (key2545, -1), (key2539, -1), (key2544, -1), (key2539, -1), (key2565, 1), (key2555, 1), (key2565, 1), (key2544, 1), (key2555, 1), (key2544, 1)]

theorem rawRowCheck2890 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form9 = rawRow2890 := by decide +kernel

def row2890 : Integer.Sparse Key := [(key2379, -2), (key2382, 2), (key2393, -2), (key2395, 2), (key2473, 2), (key2483, 2), (key2507, -2), (key2526, -2), (key2539, -2), (key2545, -2), (key2555, 2), (key2565, 2)]

theorem rowCheck2890 : row2890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2890 := by decide +kernel

theorem rowEval2890 (x : Key → ℝ) : Integer.Sparse.eval row2890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2890, Integer.Sparse.eval_collectBalanced, rawRowCheck2890]

def rawRow2891 : Integer.Sparse Key := [(key2382, -2), (key2382, -2), (key2395, -2), (key2379, 1), (key2382, 1), (key2379, 1), (key2393, 1), (key2382, 1), (key2393, 1), (key2507, 2), (key2507, 2), (key2526, 2), (key2473, -1), (key2483, -1), (key2473, -1), (key2507, -1), (key2483, -1), (key2507, -1), (key2555, -1), (key2557, -1), (key2555, -1), (key2565, -1), (key2557, -1), (key2565, -1), (key2539, 1), (key2545, 1), (key2539, 1), (key2557, 1), (key2545, 1), (key2557, 1)]

theorem rawRowCheck2891 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form9 = rawRow2891 := by decide +kernel

def row2891 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2473, -2), (key2483, -2), (key2507, 2), (key2526, 2), (key2539, 2), (key2545, 2), (key2555, -2), (key2565, -2)]

theorem rowCheck2891 : row2891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2891 := by decide +kernel

theorem rowEval2891 (x : Key → ℝ) : Integer.Sparse.eval row2891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2891, Integer.Sparse.eval_collectBalanced, rawRowCheck2891]

def rawRow2892 : Integer.Sparse Key := [(key2382, -2), (key2395, -2), (key2382, -2), (key2382, 1), (key2379, 1), (key2393, 1), (key2379, 1), (key2393, 1), (key2382, 1), (key2507, 2), (key2526, 2), (key2507, 2), (key2483, -1), (key2473, -1), (key2507, -1), (key2473, -1), (key2507, -1), (key2483, -1), (key2557, -1), (key2555, -1), (key2565, -1), (key2555, -1), (key2565, -1), (key2557, -1), (key2545, 1), (key2539, 1), (key2557, 1), (key2539, 1), (key2557, 1), (key2545, 1)]

theorem rawRowCheck2892 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form9 = rawRow2892 := by decide +kernel

def row2892 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2473, -2), (key2483, -2), (key2507, 2), (key2526, 2), (key2539, 2), (key2545, 2), (key2555, -2), (key2565, -2)]

theorem rowCheck2892 : row2892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2892 := by decide +kernel

theorem rowEval2892 (x : Key → ℝ) : Integer.Sparse.eval row2892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2892, Integer.Sparse.eval_collectBalanced, rawRowCheck2892]

def rawRow2893 : Integer.Sparse Key := [(key2395, -2), (key2382, -2), (key2382, -2), (key2393, 1), (key2393, 1), (key2382, 1), (key2382, 1), (key2379, 1), (key2379, 1), (key2526, 2), (key2507, 2), (key2507, 2), (key2507, -1), (key2507, -1), (key2483, -1), (key2483, -1), (key2473, -1), (key2473, -1), (key2565, -1), (key2565, -1), (key2557, -1), (key2557, -1), (key2555, -1), (key2555, -1), (key2557, 1), (key2557, 1), (key2545, 1), (key2545, 1), (key2539, 1), (key2539, 1)]

theorem rawRowCheck2893 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form9 = rawRow2893 := by decide +kernel

def row2893 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2473, -2), (key2483, -2), (key2507, 2), (key2526, 2), (key2539, 2), (key2545, 2), (key2555, -2), (key2565, -2)]

theorem rowCheck2893 : row2893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2893 := by decide +kernel

theorem rowEval2893 (x : Key → ℝ) : Integer.Sparse.eval row2893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2893, Integer.Sparse.eval_collectBalanced, rawRowCheck2893]

def rawRow2894 : Integer.Sparse Key := [(key2848, -2), (key2891, -2), (key2891, -2), (key2882, 1), (key2882, 1), (key2912, 1), (key2912, 1), (key2914, 1), (key2914, 1), (key2379, 2), (key2393, 2), (key2393, 2), (key2544, -1), (key2544, -1), (key2555, -1), (key2555, -1), (key2565, -1), (key2565, -1), (key2382, -1), (key2382, -1), (key2393, -1), (key2393, -1), (key2395, -1), (key2395, -1), (key2483, 1), (key2483, 1), (key2507, 1), (key2507, 1), (key2526, 1), (key2526, 1)]

theorem rawRowCheck2894 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form9 = rawRow2894 := by decide +kernel

def row2894 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2891, -4), (key2912, 2), (key2914, 2)]

theorem rowCheck2894 : row2894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2894 := by decide +kernel

theorem rowEval2894 (x : Key → ℝ) : Integer.Sparse.eval row2894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2894, Integer.Sparse.eval_collectBalanced, rawRowCheck2894]

def rawRow2895 : Integer.Sparse Key := [(key2891, -2), (key2848, -2), (key2891, -2), (key2912, 1), (key2914, 1), (key2882, 1), (key2914, 1), (key2882, 1), (key2912, 1), (key2393, 2), (key2379, 2), (key2393, 2), (key2555, -1), (key2565, -1), (key2544, -1), (key2565, -1), (key2544, -1), (key2555, -1), (key2393, -1), (key2395, -1), (key2382, -1), (key2395, -1), (key2382, -1), (key2393, -1), (key2507, 1), (key2526, 1), (key2483, 1), (key2526, 1), (key2483, 1), (key2507, 1)]

theorem rawRowCheck2895 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form9 = rawRow2895 := by decide +kernel

def row2895 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2891, -4), (key2912, 2), (key2914, 2)]

theorem rowCheck2895 : row2895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2895 := by decide +kernel

theorem rowEval2895 (x : Key → ℝ) : Integer.Sparse.eval row2895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2895, Integer.Sparse.eval_collectBalanced, rawRowCheck2895]

def rawRow2896 : Integer.Sparse Key := [(key2891, -2), (key2891, -2), (key2848, -2), (key2914, 1), (key2912, 1), (key2914, 1), (key2882, 1), (key2912, 1), (key2882, 1), (key2393, 2), (key2393, 2), (key2379, 2), (key2565, -1), (key2555, -1), (key2565, -1), (key2544, -1), (key2555, -1), (key2544, -1), (key2395, -1), (key2393, -1), (key2395, -1), (key2382, -1), (key2393, -1), (key2382, -1), (key2526, 1), (key2507, 1), (key2526, 1), (key2483, 1), (key2507, 1), (key2483, 1)]

theorem rawRowCheck2896 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form9 = rawRow2896 := by decide +kernel

def row2896 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2891, -4), (key2912, 2), (key2914, 2)]

theorem rowCheck2896 : row2896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2896 := by decide +kernel

theorem rowEval2896 (x : Key → ℝ) : Integer.Sparse.eval row2896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2896, Integer.Sparse.eval_collectBalanced, rawRowCheck2896]

def rawRow2897 : Integer.Sparse Key := [(key2774, -2), (key2882, -2), (key2914, -2), (key2771, 1), (key2774, 1), (key2848, 1), (key2891, 1), (key2882, 1), (key2912, 1), (key2933, 2), (key2991, 2), (key3003, 2), (key2379, -1), (key2393, -1), (key2407, -1), (key2441, -1), (key2544, -1), (key2555, -1), (key2441, -1), (key2445, -1), (key2507, -1), (key2526, -1), (key2557, -1), (key2565, -1), (key2382, 1), (key2395, 1), (key2410, 1), (key2445, 1), (key2545, 1), (key2557, 1)]

theorem rawRowCheck2897 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form9 = rawRow2897 := by decide +kernel

def row2897 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, -1), (key2395, 1), (key2407, -1), (key2410, 1), (key2441, -2), (key2507, -1), (key2526, -1), (key2544, -1), (key2545, 1), (key2555, -1), (key2565, -1), (key2771, 1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 2), (key2991, 2), (key3003, 2)]

theorem rowCheck2897 : row2897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2897 := by decide +kernel

theorem rowEval2897 (x : Key → ℝ) : Integer.Sparse.eval row2897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2897, Integer.Sparse.eval_collectBalanced, rawRowCheck2897]

def rawRow2898 : Integer.Sparse Key := [(key2774, -2), (key2914, -2), (key2882, -2), (key2774, 1), (key2771, 1), (key2891, 1), (key2848, 1), (key2912, 1), (key2882, 1), (key2933, 2), (key3003, 2), (key2991, 2), (key2393, -1), (key2379, -1), (key2441, -1), (key2407, -1), (key2555, -1), (key2544, -1), (key2445, -1), (key2441, -1), (key2526, -1), (key2507, -1), (key2565, -1), (key2557, -1), (key2395, 1), (key2382, 1), (key2445, 1), (key2410, 1), (key2557, 1), (key2545, 1)]

theorem rawRowCheck2898 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form9 = rawRow2898 := by decide +kernel

def row2898 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, -1), (key2395, 1), (key2407, -1), (key2410, 1), (key2441, -2), (key2507, -1), (key2526, -1), (key2544, -1), (key2545, 1), (key2555, -1), (key2565, -1), (key2771, 1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 2), (key2991, 2), (key3003, 2)]

theorem rowCheck2898 : row2898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2898 := by decide +kernel

theorem rowEval2898 (x : Key → ℝ) : Integer.Sparse.eval row2898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2898, Integer.Sparse.eval_collectBalanced, rawRowCheck2898]

def rawRow2899 : Integer.Sparse Key := [(key2882, -2), (key2774, -2), (key2914, -2), (key2848, 1), (key2882, 1), (key2771, 1), (key2912, 1), (key2774, 1), (key2891, 1), (key2991, 2), (key2933, 2), (key3003, 2), (key2771, -1), (key2912, -1), (key2592, -1), (key2991, -1), (key2393, -1), (key2441, -1), (key2507, -1), (key2557, -1), (key2441, -1), (key2565, -1), (key2445, -1), (key2526, -1), (key2410, 1), (key2545, 1), (key2382, 1), (key2557, 1), (key2395, 1), (key2445, 1)]

theorem rawRowCheck2899 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form9 = rawRow2899 := by decide +kernel

def row2899 : Integer.Sparse Key := [(key2382, 1), (key2393, -1), (key2395, 1), (key2410, 1), (key2441, -2), (key2507, -1), (key2526, -1), (key2545, 1), (key2565, -1), (key2592, -1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2914, -2), (key2933, 2), (key2991, 1), (key3003, 2)]

theorem rowCheck2899 : row2899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2899 := by decide +kernel

theorem rowEval2899 (x : Key → ℝ) : Integer.Sparse.eval row2899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2899, Integer.Sparse.eval_collectBalanced, rawRowCheck2899]

def rawRow2900 : Integer.Sparse Key := [(key2882, -2), (key2914, -2), (key2774, -2), (key2882, 1), (key2848, 1), (key2912, 1), (key2771, 1), (key2891, 1), (key2774, 1), (key2991, 2), (key3003, 2), (key2933, 2), (key2912, -1), (key2771, -1), (key2991, -1), (key2592, -1), (key2441, -1), (key2393, -1), (key2557, -1), (key2507, -1), (key2565, -1), (key2441, -1), (key2526, -1), (key2445, -1), (key2545, 1), (key2410, 1), (key2557, 1), (key2382, 1), (key2445, 1), (key2395, 1)]

theorem rawRowCheck2900 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form9 = rawRow2900 := by decide +kernel

def row2900 : Integer.Sparse Key := [(key2382, 1), (key2393, -1), (key2395, 1), (key2410, 1), (key2441, -2), (key2507, -1), (key2526, -1), (key2545, 1), (key2565, -1), (key2592, -1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2914, -2), (key2933, 2), (key2991, 1), (key3003, 2)]

theorem rowCheck2900 : row2900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2900 := by decide +kernel

theorem rowEval2900 (x : Key → ℝ) : Integer.Sparse.eval row2900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form9) x := by
  rw [rowCheck2900, Integer.Sparse.eval_collectBalanced, rawRowCheck2900]

def rawRow2901 : Integer.Sparse Key := [(key2914, -2), (key2774, -2), (key2882, -2), (key2891, 1), (key2912, 1), (key2774, 1), (key2882, 1), (key2771, 1), (key2848, 1), (key3003, 2), (key2933, 2), (key2991, 2), (key2933, -1), (key2991, -1), (key2602, -1), (key2912, -1), (key2379, -1), (key2407, -1), (key2526, -1), (key2565, -1), (key2445, -1), (key2557, -1), (key2441, -1), (key2507, -1), (key2445, 1), (key2557, 1), (key2395, 1), (key2545, 1), (key2382, 1), (key2410, 1)]

theorem rawRowCheck2901 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form9 = rawRow2901 := by decide +kernel

def row2901 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2395, 1), (key2407, -1), (key2410, 1), (key2441, -1), (key2507, -1), (key2526, -1), (key2545, 1), (key2565, -1), (key2602, -1), (key2771, 1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2914, -2), (key2933, 1), (key2991, 1), (key3003, 2)]

theorem rowCheck2901 : row2901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2901 := by decide +kernel

theorem rowEval2901 (x : Key → ℝ) : Integer.Sparse.eval row2901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2901, Integer.Sparse.eval_collectBalanced, rawRowCheck2901]

def rawRow2902 : Integer.Sparse Key := [(key2914, -2), (key2882, -2), (key2774, -2), (key2912, 1), (key2891, 1), (key2882, 1), (key2774, 1), (key2848, 1), (key2771, 1), (key3003, 2), (key2991, 2), (key2933, 2), (key2991, -1), (key2933, -1), (key2912, -1), (key2602, -1), (key2771, -1), (key2592, -1), (key2565, -1), (key2526, -1), (key2557, -1), (key2445, -1), (key2507, -1), (key2441, -1), (key2557, 1), (key2445, 1), (key2545, 1), (key2395, 1), (key2410, 1), (key2382, 1)]

theorem rawRowCheck2902 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form9 = rawRow2902 := by decide +kernel

def row2902 : Integer.Sparse Key := [(key2382, 1), (key2395, 1), (key2410, 1), (key2441, -1), (key2507, -1), (key2526, -1), (key2545, 1), (key2565, -1), (key2592, -1), (key2602, -1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2914, -2), (key2933, 1), (key2991, 1), (key3003, 2)]

theorem rowCheck2902 : row2902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2902 := by decide +kernel

theorem rowEval2902 (x : Key → ℝ) : Integer.Sparse.eval row2902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form9) x := by
  rw [rowCheck2902, Integer.Sparse.eval_collectBalanced, rawRowCheck2902]

def rawRow2903 : Integer.Sparse Key := [(key2970, -2), (key2970, -2), (key2996, -2), (key2991, 1), (key2993, 1), (key2991, 1), (key3003, 1), (key2993, 1), (key3003, 1), (key2595, 2), (key2595, 2), (key2603, 2), (key2882, -1), (key2914, -1), (key2882, -1), (key2993, -1), (key2914, -1), (key2993, -1), (key2379, -1), (key2382, -1), (key2379, -1), (key2393, -1), (key2382, -1), (key2393, -1), (key2473, 1), (key2483, 1), (key2473, 1), (key2507, 1), (key2483, 1), (key2507, 1)]

theorem rawRowCheck2903 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form9 = rawRow2903 := by decide +kernel

def row2903 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2595, 4), (key2603, 2), (key2882, -2), (key2914, -2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

theorem rowCheck2903 : row2903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2903 := by decide +kernel

theorem rowEval2903 (x : Key → ℝ) : Integer.Sparse.eval row2903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2903, Integer.Sparse.eval_collectBalanced, rawRowCheck2903]

def rawRow2904 : Integer.Sparse Key := [(key2970, -2), (key2996, -2), (key2970, -2), (key2993, 1), (key2991, 1), (key3003, 1), (key2991, 1), (key3003, 1), (key2993, 1), (key2595, 2), (key2603, 2), (key2595, 2), (key2914, -1), (key2882, -1), (key2993, -1), (key2882, -1), (key2993, -1), (key2914, -1), (key2382, -1), (key2379, -1), (key2393, -1), (key2379, -1), (key2393, -1), (key2382, -1), (key2483, 1), (key2473, 1), (key2507, 1), (key2473, 1), (key2507, 1), (key2483, 1)]

theorem rawRowCheck2904 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form9 = rawRow2904 := by decide +kernel

def row2904 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2595, 4), (key2603, 2), (key2882, -2), (key2914, -2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

theorem rowCheck2904 : row2904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2904 := by decide +kernel

theorem rowEval2904 (x : Key → ℝ) : Integer.Sparse.eval row2904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2904, Integer.Sparse.eval_collectBalanced, rawRowCheck2904]

def rawRow2905 : Integer.Sparse Key := [(key2996, -2), (key2970, -2), (key2970, -2), (key3003, 1), (key3003, 1), (key2993, 1), (key2993, 1), (key2991, 1), (key2991, 1), (key2603, 2), (key2595, 2), (key2595, 2), (key2993, -1), (key2993, -1), (key2914, -1), (key2914, -1), (key2882, -1), (key2882, -1), (key2393, -1), (key2393, -1), (key2382, -1), (key2382, -1), (key2379, -1), (key2379, -1), (key2507, 1), (key2507, 1), (key2483, 1), (key2483, 1), (key2473, 1), (key2473, 1)]

theorem rawRowCheck2905 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form9 = rawRow2905 := by decide +kernel

def row2905 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2595, 4), (key2603, 2), (key2882, -2), (key2914, -2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

theorem rowCheck2905 : row2905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2905 := by decide +kernel

theorem rowEval2905 (x : Key → ℝ) : Integer.Sparse.eval row2905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2905, Integer.Sparse.eval_collectBalanced, rawRowCheck2905]

def rawRow2906 : Integer.Sparse Key := [(key2933, -2), (key2991, -2), (key3003, -2), (key2933, 1), (key2934, 1), (key2970, 1), (key2996, 1), (key2993, 1), (key3003, 1), (key2774, 2), (key2882, 2), (key2914, 2), (key2595, -1), (key2603, -1), (key2774, -1), (key2934, -1), (key2914, -1), (key2993, -1), (key2771, -1), (key2774, -1), (key2848, -1), (key2891, -1), (key2882, -1), (key2912, -1), (key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1)]

theorem rawRowCheck2906 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form9 = rawRow2906 := by decide +kernel

def row2906 : Integer.Sparse Key := [(key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1), (key2595, -1), (key2603, -1), (key2771, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2912, -1), (key2914, 1), (key2933, -1), (key2970, 1), (key2991, -2), (key2996, 1), (key3003, -1)]

theorem rowCheck2906 : row2906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2906 := by decide +kernel

theorem rowEval2906 (x : Key → ℝ) : Integer.Sparse.eval row2906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2906, Integer.Sparse.eval_collectBalanced, rawRowCheck2906]

def rawRow2907 : Integer.Sparse Key := [(key2933, -2), (key3003, -2), (key2991, -2), (key2934, 1), (key2933, 1), (key2996, 1), (key2970, 1), (key3003, 1), (key2993, 1), (key2774, 2), (key2914, 2), (key2882, 2), (key2603, -1), (key2595, -1), (key2934, -1), (key2774, -1), (key2993, -1), (key2914, -1), (key2774, -1), (key2771, -1), (key2891, -1), (key2848, -1), (key2912, -1), (key2882, -1), (key2393, 1), (key2379, 1), (key2441, 1), (key2407, 1), (key2555, 1), (key2544, 1)]

theorem rawRowCheck2907 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form9 = rawRow2907 := by decide +kernel

def row2907 : Integer.Sparse Key := [(key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1), (key2595, -1), (key2603, -1), (key2771, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2912, -1), (key2914, 1), (key2933, -1), (key2970, 1), (key2991, -2), (key2996, 1), (key3003, -1)]

theorem rowCheck2907 : row2907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2907 := by decide +kernel

theorem rowEval2907 (x : Key → ℝ) : Integer.Sparse.eval row2907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2907, Integer.Sparse.eval_collectBalanced, rawRowCheck2907]

def rawRow2908 : Integer.Sparse Key := [(key2991, -2), (key2933, -2), (key3003, -2), (key2970, 1), (key2993, 1), (key2933, 1), (key3003, 1), (key2934, 1), (key2996, 1), (key2882, 2), (key2774, 2), (key2914, 2), (key2774, -1), (key2914, -1), (key2595, -1), (key2993, -1), (key2603, -1), (key2934, -1), (key2848, -1), (key2882, -1), (key2771, -1), (key2912, -1), (key2774, -1), (key2891, -1), (key2771, 1), (key2912, 1), (key2592, 1), (key2991, 1), (key2393, 1), (key2441, 1)]

theorem rawRowCheck2908 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form9 = rawRow2908 := by decide +kernel

def row2908 : Integer.Sparse Key := [(key2393, 1), (key2441, 1), (key2592, 1), (key2595, -1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2914, 1), (key2933, -1), (key2970, 1), (key2991, -1), (key2996, 1), (key3003, -1)]

theorem rowCheck2908 : row2908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2908 := by decide +kernel

theorem rowEval2908 (x : Key → ℝ) : Integer.Sparse.eval row2908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2908, Integer.Sparse.eval_collectBalanced, rawRowCheck2908]

def rawRow2909 : Integer.Sparse Key := [(key2991, -2), (key3003, -2), (key2933, -2), (key2993, 1), (key2970, 1), (key3003, 1), (key2933, 1), (key2996, 1), (key2934, 1), (key2882, 2), (key2914, 2), (key2774, 2), (key2914, -1), (key2774, -1), (key2993, -1), (key2595, -1), (key2934, -1), (key2603, -1), (key2882, -1), (key2848, -1), (key2912, -1), (key2771, -1), (key2891, -1), (key2774, -1), (key2912, 1), (key2771, 1), (key2991, 1), (key2592, 1), (key2441, 1), (key2393, 1)]

theorem rawRowCheck2909 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form9 = rawRow2909 := by decide +kernel

def row2909 : Integer.Sparse Key := [(key2393, 1), (key2441, 1), (key2592, 1), (key2595, -1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2914, 1), (key2933, -1), (key2970, 1), (key2991, -1), (key2996, 1), (key3003, -1)]

theorem rowCheck2909 : row2909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2909 := by decide +kernel

theorem rowEval2909 (x : Key → ℝ) : Integer.Sparse.eval row2909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form9) x := by
  rw [rowCheck2909, Integer.Sparse.eval_collectBalanced, rawRowCheck2909]

def rawRow2910 : Integer.Sparse Key := [(key3003, -2), (key2933, -2), (key2991, -2), (key2996, 1), (key3003, 1), (key2934, 1), (key2993, 1), (key2933, 1), (key2970, 1), (key2914, 2), (key2774, 2), (key2882, 2), (key2934, -1), (key2993, -1), (key2603, -1), (key2914, -1), (key2595, -1), (key2774, -1), (key2891, -1), (key2912, -1), (key2774, -1), (key2882, -1), (key2771, -1), (key2848, -1), (key2933, 1), (key2991, 1), (key2602, 1), (key2912, 1), (key2379, 1), (key2407, 1)]

theorem rawRowCheck2910 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form9 = rawRow2910 := by decide +kernel

def row2910 : Integer.Sparse Key := [(key2379, 1), (key2407, 1), (key2595, -1), (key2602, 1), (key2603, -1), (key2771, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2914, 1), (key2970, 1), (key2991, -1), (key2996, 1), (key3003, -1)]

theorem rowCheck2910 : row2910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2910 := by decide +kernel

theorem rowEval2910 (x : Key → ℝ) : Integer.Sparse.eval row2910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2910, Integer.Sparse.eval_collectBalanced, rawRowCheck2910]

def rawRow2911 : Integer.Sparse Key := [(key3003, -2), (key2991, -2), (key2933, -2), (key3003, 1), (key2996, 1), (key2993, 1), (key2934, 1), (key2970, 1), (key2933, 1), (key2914, 2), (key2882, 2), (key2774, 2), (key2993, -1), (key2934, -1), (key2914, -1), (key2603, -1), (key2774, -1), (key2595, -1), (key2912, -1), (key2891, -1), (key2882, -1), (key2774, -1), (key2848, -1), (key2771, -1), (key2991, 1), (key2933, 1), (key2912, 1), (key2602, 1), (key2771, 1), (key2592, 1)]

theorem rawRowCheck2911 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form9 = rawRow2911 := by decide +kernel

def row2911 : Integer.Sparse Key := [(key2592, 1), (key2595, -1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2914, 1), (key2970, 1), (key2991, -1), (key2996, 1), (key3003, -1)]

theorem rowCheck2911 : row2911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2911 := by decide +kernel

theorem rowEval2911 (x : Key → ℝ) : Integer.Sparse.eval row2911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form9) x := by
  rw [rowCheck2911, Integer.Sparse.eval_collectBalanced, rawRowCheck2911]

def rawRow2912 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2366, -2), (key2366, 6), (key2456, 2), (key2456, 2), (key2461, 2), (key2461, -2), (key2523, -2), (key2523, -2), (key2567, -6), (key2567, 2), (key2579, 2), (key2579, 2)]

theorem rawRowCheck2912 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form10 = rawRow2912 := by decide +kernel

def row2912 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2366, 4), (key2456, 4), (key2523, -4), (key2567, -4), (key2579, 4)]

theorem rowCheck2912 : row2912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2912 := by decide +kernel

theorem rowEval2912 (x : Key → ℝ) : Integer.Sparse.eval row2912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2912, Integer.Sparse.eval_collectBalanced, rawRowCheck2912]

def rawRow2913 : Integer.Sparse Key := [(key2357, -2), (key2363, -2), (key2361, -2), (key2366, 6), (key2456, 2), (key2461, 2), (key2456, 2), (key2523, -2), (key2461, -2), (key2523, -2), (key2567, -6), (key2579, 2), (key2567, 2), (key2579, 2)]

theorem rawRowCheck2913 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form10 = rawRow2913 := by decide +kernel

def row2913 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2456, 4), (key2523, -4), (key2567, -4), (key2579, 4)]

theorem rowCheck2913 : row2913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2913 := by decide +kernel

theorem rowEval2913 (x : Key → ℝ) : Integer.Sparse.eval row2913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2913, Integer.Sparse.eval_collectBalanced, rawRowCheck2913]

def rawRow2914 : Integer.Sparse Key := [(key2363, -2), (key2357, -2), (key2361, -2), (key2366, 6), (key2461, 2), (key2456, 2), (key2456, 2), (key2523, -2), (key2523, -2), (key2461, -2), (key2567, -6), (key2579, 2), (key2579, 2), (key2567, 2)]

theorem rawRowCheck2914 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form10 = rawRow2914 := by decide +kernel

def row2914 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2456, 4), (key2523, -4), (key2567, -4), (key2579, 4)]

theorem rowCheck2914 : row2914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2914 := by decide +kernel

theorem rowEval2914 (x : Key → ℝ) : Integer.Sparse.eval row2914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2914, Integer.Sparse.eval_collectBalanced, rawRowCheck2914]

def rawRow2915 : Integer.Sparse Key := [(key2357, -2), (key2363, -2), (key2363, -2), (key2361, 6), (key2517, 2), (key2523, 2), (key2523, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2579, -6), (key2567, 2), (key2567, 2), (key2579, 2)]

theorem rawRowCheck2915 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form10 = rawRow2915 := by decide +kernel

def row2915 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2456, -4), (key2523, 4), (key2567, 4), (key2579, -4)]

theorem rowCheck2915 : row2915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2915 := by decide +kernel

theorem rowEval2915 (x : Key → ℝ) : Integer.Sparse.eval row2915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2915, Integer.Sparse.eval_collectBalanced, rawRowCheck2915]

def rawRow2916 : Integer.Sparse Key := [(key2363, -2), (key2357, -2), (key2363, -2), (key2361, 6), (key2523, 2), (key2517, 2), (key2523, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2579, -6), (key2567, 2), (key2579, 2), (key2567, 2)]

theorem rawRowCheck2916 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form10 = rawRow2916 := by decide +kernel

def row2916 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2456, -4), (key2523, 4), (key2567, 4), (key2579, -4)]

theorem rowCheck2916 : row2916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2916 := by decide +kernel

theorem rowEval2916 (x : Key → ℝ) : Integer.Sparse.eval row2916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2916, Integer.Sparse.eval_collectBalanced, rawRowCheck2916]

def rawRow2917 : Integer.Sparse Key := [(key2363, -2), (key2363, -2), (key2357, -2), (key2361, 6), (key2523, 2), (key2523, 2), (key2517, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2579, -6), (key2579, 2), (key2567, 2), (key2567, 2)]

theorem rawRowCheck2917 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form10 = rawRow2917 := by decide +kernel

def row2917 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2456, -4), (key2523, 4), (key2567, 4), (key2579, -4)]

theorem rowCheck2917 : row2917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2917 := by decide +kernel

theorem rowEval2917 (x : Key → ℝ) : Integer.Sparse.eval row2917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2917, Integer.Sparse.eval_collectBalanced, rawRowCheck2917]

def rawRow2918 : Integer.Sparse Key := [(key2452, -2), (key2452, -2), (key2458, -2), (key2519, 6), (key2357, 2), (key2361, 2), (key2366, 2), (key2567, -2), (key2579, -2), (key2579, -2), (key2366, -6), (key2461, 2), (key2523, 2), (key2523, 2)]

theorem rawRowCheck2918 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form10 = rawRow2918 := by decide +kernel

def row2918 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2366, -4), (key2452, -4), (key2458, -2), (key2461, 2), (key2519, 6), (key2523, 4), (key2567, -2), (key2579, -4)]

theorem rowCheck2918 : row2918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2918 := by decide +kernel

theorem rowEval2918 (x : Key → ℝ) : Integer.Sparse.eval row2918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2918, Integer.Sparse.eval_collectBalanced, rawRowCheck2918]

def rawRow2919 : Integer.Sparse Key := [(key2452, -2), (key2458, -2), (key2452, -2), (key2519, 6), (key2357, 2), (key2363, 2), (key2361, 2), (key2579, -2), (key2567, -2), (key2579, -2), (key2366, -6), (key2523, 2), (key2461, 2), (key2523, 2)]

theorem rawRowCheck2919 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form10 = rawRow2919 := by decide +kernel

def row2919 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2366, -6), (key2452, -4), (key2458, -2), (key2461, 2), (key2519, 6), (key2523, 4), (key2567, -2), (key2579, -4)]

theorem rowCheck2919 : row2919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2919 := by decide +kernel

theorem rowEval2919 (x : Key → ℝ) : Integer.Sparse.eval row2919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2919, Integer.Sparse.eval_collectBalanced, rawRowCheck2919]

def rawRow2920 : Integer.Sparse Key := [(key2458, -2), (key2452, -2), (key2452, -2), (key2519, 6), (key2363, 2), (key2357, 2), (key2361, 2), (key2579, -2), (key2579, -2), (key2567, -2), (key2366, -6), (key2523, 2), (key2523, 2), (key2461, 2)]

theorem rawRowCheck2920 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form10 = rawRow2920 := by decide +kernel

def row2920 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2366, -6), (key2452, -4), (key2458, -2), (key2461, 2), (key2519, 6), (key2523, 4), (key2567, -2), (key2579, -4)]

theorem rowCheck2920 : row2920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2920 := by decide +kernel

theorem rowEval2920 (x : Key → ℝ) : Integer.Sparse.eval row2920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2920, Integer.Sparse.eval_collectBalanced, rawRowCheck2920]

def rawRow2921 : Integer.Sparse Key := [(key2452, -2), (key2458, -2), (key2519, -2), (key2452, 6), (key2528, 2), (key2530, 2), (key2560, 2), (key2361, -2), (key2456, -2), (key2517, -2), (key2523, -6), (key2366, 2), (key2461, 2), (key2523, 2)]

theorem rawRowCheck2921 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form10 = rawRow2921 := by decide +kernel

def row2921 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

theorem rowCheck2921 : row2921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2921 := by decide +kernel

theorem rowEval2921 (x : Key → ℝ) : Integer.Sparse.eval row2921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2921, Integer.Sparse.eval_collectBalanced, rawRowCheck2921]

def rawRow2922 : Integer.Sparse Key := [(key2458, -2), (key2452, -2), (key2519, -2), (key2452, 6), (key2530, 2), (key2528, 2), (key2560, 2), (key2361, -2), (key2517, -2), (key2456, -2), (key2523, -6), (key2366, 2), (key2523, 2), (key2461, 2)]

theorem rawRowCheck2922 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form10 = rawRow2922 := by decide +kernel

def row2922 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

theorem rowCheck2922 : row2922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2922 := by decide +kernel

theorem rowEval2922 (x : Key → ℝ) : Integer.Sparse.eval row2922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2922, Integer.Sparse.eval_collectBalanced, rawRowCheck2922]

def rawRow2923 : Integer.Sparse Key := [(key2452, -2), (key2519, -2), (key2458, -2), (key2452, 6), (key2528, 2), (key2560, 2), (key2530, 2), (key2456, -2), (key2361, -2), (key2517, -2), (key2523, -6), (key2461, 2), (key2366, 2), (key2523, 2)]

theorem rawRowCheck2923 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form10 = rawRow2923 := by decide +kernel

def row2923 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

theorem rowCheck2923 : row2923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2923 := by decide +kernel

theorem rowEval2923 (x : Key → ℝ) : Integer.Sparse.eval row2923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2923, Integer.Sparse.eval_collectBalanced, rawRowCheck2923]

def rawRow2924 : Integer.Sparse Key := [(key2519, -2), (key2452, -2), (key2458, -2), (key2452, 6), (key2560, 2), (key2528, 2), (key2530, 2), (key2456, -2), (key2517, -2), (key2361, -2), (key2523, -6), (key2461, 2), (key2523, 2), (key2366, 2)]

theorem rawRowCheck2924 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form10 = rawRow2924 := by decide +kernel

def row2924 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

theorem rowCheck2924 : row2924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2924 := by decide +kernel

theorem rowEval2924 (x : Key → ℝ) : Integer.Sparse.eval row2924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck2924, Integer.Sparse.eval_collectBalanced, rawRowCheck2924]

def rawRow2925 : Integer.Sparse Key := [(key2458, -2), (key2519, -2), (key2452, -2), (key2452, 6), (key2530, 2), (key2560, 2), (key2528, 2), (key2517, -2), (key2361, -2), (key2456, -2), (key2523, -6), (key2523, 2), (key2366, 2), (key2461, 2)]

theorem rawRowCheck2925 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form10 = rawRow2925 := by decide +kernel

def row2925 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

theorem rowCheck2925 : row2925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2925 := by decide +kernel

theorem rowEval2925 (x : Key → ℝ) : Integer.Sparse.eval row2925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2925, Integer.Sparse.eval_collectBalanced, rawRowCheck2925]

def rawRow2926 : Integer.Sparse Key := [(key2519, -2), (key2458, -2), (key2452, -2), (key2452, 6), (key2560, 2), (key2530, 2), (key2528, 2), (key2517, -2), (key2456, -2), (key2361, -2), (key2523, -6), (key2523, 2), (key2461, 2), (key2366, 2)]

theorem rawRowCheck2926 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form10 = rawRow2926 := by decide +kernel

def row2926 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

theorem rowCheck2926 : row2926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2926 := by decide +kernel

theorem rowEval2926 (x : Key → ℝ) : Integer.Sparse.eval row2926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck2926, Integer.Sparse.eval_collectBalanced, rawRowCheck2926]

def rawRow2927 : Integer.Sparse Key := [(key2528, -2), (key2530, -2), (key2530, -2), (key2560, 6), (key2357, 2), (key2363, 2), (key2363, 2), (key2519, -2), (key2519, -2), (key2560, -2), (key2361, -6), (key2456, 2), (key2456, 2), (key2517, 2)]

theorem rawRowCheck2927 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form10 = rawRow2927 := by decide +kernel

def row2927 : Integer.Sparse Key := [(key2357, 2), (key2361, -6), (key2363, 4), (key2456, 4), (key2517, 2), (key2519, -4), (key2528, -2), (key2530, -4), (key2560, 4)]

theorem rowCheck2927 : row2927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2927 := by decide +kernel

theorem rowEval2927 (x : Key → ℝ) : Integer.Sparse.eval row2927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2927, Integer.Sparse.eval_collectBalanced, rawRowCheck2927]

def rawRow2928 : Integer.Sparse Key := [(key2530, -2), (key2528, -2), (key2530, -2), (key2560, 6), (key2363, 2), (key2357, 2), (key2363, 2), (key2519, -2), (key2560, -2), (key2519, -2), (key2361, -6), (key2456, 2), (key2517, 2), (key2456, 2)]

theorem rawRowCheck2928 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form10 = rawRow2928 := by decide +kernel

def row2928 : Integer.Sparse Key := [(key2357, 2), (key2361, -6), (key2363, 4), (key2456, 4), (key2517, 2), (key2519, -4), (key2528, -2), (key2530, -4), (key2560, 4)]

theorem rowCheck2928 : row2928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2928 := by decide +kernel

theorem rowEval2928 (x : Key → ℝ) : Integer.Sparse.eval row2928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2928, Integer.Sparse.eval_collectBalanced, rawRowCheck2928]

def rawRow2929 : Integer.Sparse Key := [(key2530, -2), (key2530, -2), (key2528, -2), (key2560, 6), (key2363, 2), (key2363, 2), (key2357, 2), (key2560, -2), (key2519, -2), (key2519, -2), (key2361, -6), (key2517, 2), (key2456, 2), (key2456, 2)]

theorem rawRowCheck2929 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form10 = rawRow2929 := by decide +kernel

def row2929 : Integer.Sparse Key := [(key2357, 2), (key2361, -6), (key2363, 4), (key2456, 4), (key2517, 2), (key2519, -4), (key2528, -2), (key2530, -4), (key2560, 4)]

theorem rowCheck2929 : row2929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2929 := by decide +kernel

theorem rowEval2929 (x : Key → ℝ) : Integer.Sparse.eval row2929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2929, Integer.Sparse.eval_collectBalanced, rawRowCheck2929]

def rawRow2930 : Integer.Sparse Key := [(key2528, -2), (key2530, -2), (key2560, -2), (key2530, 6), (key2452, 2), (key2458, 2), (key2519, 2), (key2363, -2), (key2458, -2), (key2530, -2), (key2456, -6), (key2361, 2), (key2456, 2), (key2517, 2)]

theorem rawRowCheck2930 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form10 = rawRow2930 := by decide +kernel

def row2930 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

theorem rowCheck2930 : row2930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2930 := by decide +kernel

theorem rowEval2930 (x : Key → ℝ) : Integer.Sparse.eval row2930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2930, Integer.Sparse.eval_collectBalanced, rawRowCheck2930]

def rawRow2931 : Integer.Sparse Key := [(key2530, -2), (key2528, -2), (key2560, -2), (key2530, 6), (key2458, 2), (key2452, 2), (key2519, 2), (key2363, -2), (key2530, -2), (key2458, -2), (key2456, -6), (key2361, 2), (key2517, 2), (key2456, 2)]

theorem rawRowCheck2931 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form10 = rawRow2931 := by decide +kernel

def row2931 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

theorem rowCheck2931 : row2931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2931 := by decide +kernel

theorem rowEval2931 (x : Key → ℝ) : Integer.Sparse.eval row2931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2931, Integer.Sparse.eval_collectBalanced, rawRowCheck2931]

def rawRow2932 : Integer.Sparse Key := [(key2528, -2), (key2560, -2), (key2530, -2), (key2530, 6), (key2452, 2), (key2519, 2), (key2458, 2), (key2458, -2), (key2363, -2), (key2530, -2), (key2456, -6), (key2456, 2), (key2361, 2), (key2517, 2)]

theorem rawRowCheck2932 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form10 = rawRow2932 := by decide +kernel

def row2932 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

theorem rowCheck2932 : row2932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2932 := by decide +kernel

theorem rowEval2932 (x : Key → ℝ) : Integer.Sparse.eval row2932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2932, Integer.Sparse.eval_collectBalanced, rawRowCheck2932]

def rawRow2933 : Integer.Sparse Key := [(key2560, -2), (key2528, -2), (key2530, -2), (key2530, 6), (key2519, 2), (key2452, 2), (key2458, 2), (key2458, -2), (key2530, -2), (key2363, -2), (key2456, -6), (key2456, 2), (key2517, 2), (key2361, 2)]

theorem rawRowCheck2933 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form10 = rawRow2933 := by decide +kernel

def row2933 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

theorem rowCheck2933 : row2933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2933 := by decide +kernel

theorem rowEval2933 (x : Key → ℝ) : Integer.Sparse.eval row2933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck2933, Integer.Sparse.eval_collectBalanced, rawRowCheck2933]

def rawRow2934 : Integer.Sparse Key := [(key2530, -2), (key2560, -2), (key2528, -2), (key2530, 6), (key2458, 2), (key2519, 2), (key2452, 2), (key2530, -2), (key2363, -2), (key2458, -2), (key2456, -6), (key2517, 2), (key2361, 2), (key2456, 2)]

theorem rawRowCheck2934 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form10 = rawRow2934 := by decide +kernel

def row2934 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

theorem rowCheck2934 : row2934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2934 := by decide +kernel

theorem rowEval2934 (x : Key → ℝ) : Integer.Sparse.eval row2934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2934, Integer.Sparse.eval_collectBalanced, rawRowCheck2934]

def rawRow2935 : Integer.Sparse Key := [(key2560, -2), (key2530, -2), (key2528, -2), (key2530, 6), (key2519, 2), (key2458, 2), (key2452, 2), (key2530, -2), (key2458, -2), (key2363, -2), (key2456, -6), (key2517, 2), (key2456, 2), (key2361, 2)]

theorem rawRowCheck2935 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form10 = rawRow2935 := by decide +kernel

def row2935 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

theorem rowCheck2935 : row2935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2935 := by decide +kernel

theorem rowEval2935 (x : Key → ℝ) : Integer.Sparse.eval row2935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck2935, Integer.Sparse.eval_collectBalanced, rawRowCheck2935]

def rawRow2936 : Integer.Sparse Key := [(key2361, -2), (key2361, -2), (key2364, -2), (key2364, 6), (key2456, 2), (key2456, 2), (key2459, 2), (key2459, -2), (key2520, -2), (key2520, -2), (key2531, -6), (key2531, 2), (key2561, 2), (key2561, 2)]

theorem rawRowCheck2936 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form11 = rawRow2936 := by decide +kernel

def row2936 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

theorem rowCheck2936 : row2936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2936 := by decide +kernel

theorem rowEval2936 (x : Key → ℝ) : Integer.Sparse.eval row2936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2936, Integer.Sparse.eval_collectBalanced, rawRowCheck2936]

def rawRow2937 : Integer.Sparse Key := [(key2361, -2), (key2364, -2), (key2361, -2), (key2364, 6), (key2456, 2), (key2459, 2), (key2456, 2), (key2520, -2), (key2459, -2), (key2520, -2), (key2531, -6), (key2561, 2), (key2531, 2), (key2561, 2)]

theorem rawRowCheck2937 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form11 = rawRow2937 := by decide +kernel

def row2937 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

theorem rowCheck2937 : row2937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2937 := by decide +kernel

theorem rowEval2937 (x : Key → ℝ) : Integer.Sparse.eval row2937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2937, Integer.Sparse.eval_collectBalanced, rawRowCheck2937]

def rawRow2938 : Integer.Sparse Key := [(key2364, -2), (key2361, -2), (key2361, -2), (key2364, 6), (key2459, 2), (key2456, 2), (key2456, 2), (key2520, -2), (key2520, -2), (key2459, -2), (key2531, -6), (key2561, 2), (key2561, 2), (key2531, 2)]

theorem rawRowCheck2938 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form11 = rawRow2938 := by decide +kernel

def row2938 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

theorem rowCheck2938 : row2938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2938 := by decide +kernel

theorem rowEval2938 (x : Key → ℝ) : Integer.Sparse.eval row2938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2938, Integer.Sparse.eval_collectBalanced, rawRowCheck2938]

def rawRow2939 : Integer.Sparse Key := [(key2361, -2), (key2364, -2), (key2364, -2), (key2361, 6), (key2517, 2), (key2520, 2), (key2520, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2561, -6), (key2531, 2), (key2531, 2), (key2561, 2)]

theorem rawRowCheck2939 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form11 = rawRow2939 := by decide +kernel

def row2939 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

theorem rowCheck2939 : row2939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2939 := by decide +kernel

theorem rowEval2939 (x : Key → ℝ) : Integer.Sparse.eval row2939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2939, Integer.Sparse.eval_collectBalanced, rawRowCheck2939]

def rawRow2940 : Integer.Sparse Key := [(key2364, -2), (key2361, -2), (key2364, -2), (key2361, 6), (key2520, 2), (key2517, 2), (key2520, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2561, -6), (key2531, 2), (key2561, 2), (key2531, 2)]

theorem rawRowCheck2940 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form11 = rawRow2940 := by decide +kernel

def row2940 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

theorem rowCheck2940 : row2940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2940 := by decide +kernel

theorem rowEval2940 (x : Key → ℝ) : Integer.Sparse.eval row2940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2940, Integer.Sparse.eval_collectBalanced, rawRowCheck2940]

def rawRow2941 : Integer.Sparse Key := [(key2364, -2), (key2364, -2), (key2361, -2), (key2361, 6), (key2520, 2), (key2520, 2), (key2517, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2561, -6), (key2561, 2), (key2531, 2), (key2531, 2)]

theorem rawRowCheck2941 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form11 = rawRow2941 := by decide +kernel

def row2941 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

theorem rowCheck2941 : row2941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2941 := by decide +kernel

theorem rowEval2941 (x : Key → ℝ) : Integer.Sparse.eval row2941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2941, Integer.Sparse.eval_collectBalanced, rawRowCheck2941]

def rawRow2942 : Integer.Sparse Key := [(key2456, -2), (key2456, -2), (key2459, -2), (key2531, 6), (key2361, 2), (key2361, 2), (key2364, 2), (key2531, -2), (key2561, -2), (key2561, -2), (key2364, -6), (key2459, 2), (key2520, 2), (key2520, 2)]

theorem rawRowCheck2942 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form11 = rawRow2942 := by decide +kernel

def row2942 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

theorem rowCheck2942 : row2942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2942 := by decide +kernel

theorem rowEval2942 (x : Key → ℝ) : Integer.Sparse.eval row2942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2942, Integer.Sparse.eval_collectBalanced, rawRowCheck2942]

def rawRow2943 : Integer.Sparse Key := [(key2456, -2), (key2459, -2), (key2456, -2), (key2531, 6), (key2361, 2), (key2364, 2), (key2361, 2), (key2561, -2), (key2531, -2), (key2561, -2), (key2364, -6), (key2520, 2), (key2459, 2), (key2520, 2)]

theorem rawRowCheck2943 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form11 = rawRow2943 := by decide +kernel

def row2943 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

theorem rowCheck2943 : row2943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2943 := by decide +kernel

theorem rowEval2943 (x : Key → ℝ) : Integer.Sparse.eval row2943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2943, Integer.Sparse.eval_collectBalanced, rawRowCheck2943]

end MUB6.Certificate.GramRows

end OAI
