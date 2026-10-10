import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15872 : Integer.Sparse Key := [(key2464, -2), (key2476, -2), (key2467, -2), (key2499, 6), (key2370, -2), (key2386, -2), (key2373, -2), (key2839, 2), (key2886, 2), (key2762, 2), (key2908, 2), (key2765, 2), (key2874, 2), (key2965, -2), (key2928, -2), (key2987, -2), (key2586, 6), (key2842, -2), (key2765, -2), (key2874, -2)]

theorem rawRowCheck15872 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form8 = rawRow15872 := by decide +kernel

def row15872 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

theorem rowCheck15872 : row15872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15872 := by decide +kernel

theorem rowEval15872 (x : Key → ℝ) : Integer.Sparse.eval row15872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15872, Integer.Sparse.eval_collectBalanced, rawRowCheck15872]

def rawRow15873 : Integer.Sparse Key := [(key2476, -2), (key2464, -2), (key2467, -2), (key2499, 6), (key2386, -2), (key2370, -2), (key2373, -2), (key2886, 2), (key2839, 2), (key2908, 2), (key2762, 2), (key2874, 2), (key2765, 2), (key2965, -2), (key2987, -2), (key2928, -2), (key2586, 6), (key2842, -2), (key2874, -2), (key2765, -2)]

theorem rawRowCheck15873 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form8 = rawRow15873 := by decide +kernel

def row15873 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

theorem rowCheck15873 : row15873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15873 := by decide +kernel

theorem rowEval15873 (x : Key → ℝ) : Integer.Sparse.eval row15873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15873, Integer.Sparse.eval_collectBalanced, rawRowCheck15873]

def rawRow15874 : Integer.Sparse Key := [(key2467, -2), (key2476, -2), (key2464, -2), (key2499, 6), (key2373, -2), (key2386, -2), (key2370, -2), (key2874, 2), (key2908, 2), (key2765, 2), (key2886, 2), (key2762, 2), (key2839, 2), (key2987, -2), (key2928, -2), (key2965, -2), (key2586, 6), (key2874, -2), (key2765, -2), (key2842, -2)]

theorem rawRowCheck15874 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form8 = rawRow15874 := by decide +kernel

def row15874 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

theorem rowCheck15874 : row15874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15874 := by decide +kernel

theorem rowEval15874 (x : Key → ℝ) : Integer.Sparse.eval row15874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15874, Integer.Sparse.eval_collectBalanced, rawRowCheck15874]

def rawRow15875 : Integer.Sparse Key := [(key2476, -2), (key2467, -2), (key2464, -2), (key2499, 6), (key2386, -2), (key2373, -2), (key2370, -2), (key2908, 2), (key2874, 2), (key2886, 2), (key2765, 2), (key2839, 2), (key2762, 2), (key2987, -2), (key2965, -2), (key2928, -2), (key2586, 6), (key2874, -2), (key2842, -2), (key2765, -2)]

theorem rawRowCheck15875 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form8 = rawRow15875 := by decide +kernel

def row15875 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

theorem rowCheck15875 : row15875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15875 := by decide +kernel

theorem rowEval15875 (x : Key → ℝ) : Integer.Sparse.eval row15875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15875, Integer.Sparse.eval_collectBalanced, rawRowCheck15875]

def rawRow15876 : Integer.Sparse Key := [(key2534, -2), (key2534, -2), (key2540, -2), (key2551, 6), (key2373, -2), (key2373, -2), (key2386, -2), (key2401, 2), (key2401, 2), (key2467, 2), (key2467, 2), (key2476, 2), (key2476, 2), (key2433, -2), (key2499, -2), (key2499, -2), (key2370, 6), (key2762, -2), (key2839, -2), (key2839, -2)]

theorem rawRowCheck15876 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form8 = rawRow15876 := by decide +kernel

def row15876 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2401, 4), (key2433, -2), (key2467, 4), (key2476, 4), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, -2), (key2839, -4)]

theorem rowCheck15876 : row15876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15876 := by decide +kernel

theorem rowEval15876 (x : Key → ℝ) : Integer.Sparse.eval row15876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15876, Integer.Sparse.eval_collectBalanced, rawRowCheck15876]

def rawRow15877 : Integer.Sparse Key := [(key2534, -2), (key2540, -2), (key2534, -2), (key2551, 6), (key2373, -2), (key2386, -2), (key2373, -2), (key2467, 2), (key2476, 2), (key2401, 2), (key2476, 2), (key2401, 2), (key2467, 2), (key2499, -2), (key2433, -2), (key2499, -2), (key2370, 6), (key2839, -2), (key2762, -2), (key2839, -2)]

theorem rawRowCheck15877 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form8 = rawRow15877 := by decide +kernel

def row15877 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2401, 4), (key2433, -2), (key2467, 4), (key2476, 4), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, -2), (key2839, -4)]

theorem rowCheck15877 : row15877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15877 := by decide +kernel

theorem rowEval15877 (x : Key → ℝ) : Integer.Sparse.eval row15877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15877, Integer.Sparse.eval_collectBalanced, rawRowCheck15877]

def rawRow15878 : Integer.Sparse Key := [(key2540, -2), (key2534, -2), (key2534, -2), (key2551, 6), (key2386, -2), (key2373, -2), (key2373, -2), (key2476, 2), (key2467, 2), (key2476, 2), (key2401, 2), (key2467, 2), (key2401, 2), (key2499, -2), (key2499, -2), (key2433, -2), (key2370, 6), (key2839, -2), (key2839, -2), (key2762, -2)]

theorem rawRowCheck15878 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form8 = rawRow15878 := by decide +kernel

def row15878 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2401, 4), (key2433, -2), (key2467, 4), (key2476, 4), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, -2), (key2839, -4)]

theorem rowCheck15878 : row15878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15878 := by decide +kernel

theorem rowEval15878 (x : Key → ℝ) : Integer.Sparse.eval row15878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15878, Integer.Sparse.eval_collectBalanced, rawRowCheck15878]

def rawRow15879 : Integer.Sparse Key := [(key2011, 4), (key2040, 4), (key2048, 4), (key2011, -4), (key2020, -4), (key2048, -4), (key2125, -4), (key2135, -4), (key2220, -4), (key2135, 12)]

theorem rawRowCheck15879 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form9 = rawRow15879 := by decide +kernel

def row15879 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck15879 : row15879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15879 := by decide +kernel

theorem rowEval15879 (x : Key → ℝ) : Integer.Sparse.eval row15879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15879, Integer.Sparse.eval_collectBalanced, rawRowCheck15879]

def rawRow15880 : Integer.Sparse Key := [(key2011, 4), (key2048, 4), (key2040, 4), (key2020, -4), (key2011, -4), (key2048, -4), (key2135, -4), (key2125, -4), (key2220, -4), (key2135, 12)]

theorem rawRowCheck15880 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form9 = rawRow15880 := by decide +kernel

def row15880 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck15880 : row15880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15880 := by decide +kernel

theorem rowEval15880 (x : Key → ℝ) : Integer.Sparse.eval row15880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15880, Integer.Sparse.eval_collectBalanced, rawRowCheck15880]

def rawRow15881 : Integer.Sparse Key := [(key2040, 4), (key2011, 4), (key2048, 4), (key2011, -4), (key2048, -4), (key2020, -4), (key2125, -4), (key2220, -4), (key2135, -4), (key2135, 12)]

theorem rawRowCheck15881 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form9 = rawRow15881 := by decide +kernel

def row15881 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck15881 : row15881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15881 := by decide +kernel

theorem rowEval15881 (x : Key → ℝ) : Integer.Sparse.eval row15881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15881, Integer.Sparse.eval_collectBalanced, rawRowCheck15881]

def rawRow15882 : Integer.Sparse Key := [(key2040, 4), (key2048, 4), (key2011, 4), (key2048, -4), (key2011, -4), (key2020, -4), (key2220, -4), (key2125, -4), (key2135, -4), (key2135, 12)]

theorem rawRowCheck15882 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form9 = rawRow15882 := by decide +kernel

def row15882 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck15882 : row15882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15882 := by decide +kernel

theorem rowEval15882 (x : Key → ℝ) : Integer.Sparse.eval row15882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15882, Integer.Sparse.eval_collectBalanced, rawRowCheck15882]

def rawRow15883 : Integer.Sparse Key := [(key2048, 4), (key2011, 4), (key2040, 4), (key2020, -4), (key2048, -4), (key2011, -4), (key2135, -4), (key2220, -4), (key2125, -4), (key2135, 12)]

theorem rawRowCheck15883 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form9 = rawRow15883 := by decide +kernel

def row15883 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck15883 : row15883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15883 := by decide +kernel

theorem rowEval15883 (x : Key → ℝ) : Integer.Sparse.eval row15883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15883, Integer.Sparse.eval_collectBalanced, rawRowCheck15883]

def rawRow15884 : Integer.Sparse Key := [(key2048, 4), (key2040, 4), (key2011, 4), (key2048, -4), (key2020, -4), (key2011, -4), (key2220, -4), (key2135, -4), (key2125, -4), (key2135, 12)]

theorem rawRowCheck15884 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form9 = rawRow15884 := by decide +kernel

def row15884 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck15884 : row15884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15884 := by decide +kernel

theorem rowEval15884 (x : Key → ℝ) : Integer.Sparse.eval row15884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15884, Integer.Sparse.eval_collectBalanced, rawRowCheck15884]

def rawRow15885 : Integer.Sparse Key := [(key2020, 4), (key2048, 4), (key2048, 4), (key2011, -4), (key2011, -4), (key2040, -4), (key2135, -4), (key2135, -4), (key2220, -4), (key2125, 12)]

theorem rawRowCheck15885 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form9 = rawRow15885 := by decide +kernel

def row15885 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

theorem rowCheck15885 : row15885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15885 := by decide +kernel

theorem rowEval15885 (x : Key → ℝ) : Integer.Sparse.eval row15885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15885, Integer.Sparse.eval_collectBalanced, rawRowCheck15885]

def rawRow15886 : Integer.Sparse Key := [(key2048, 4), (key2020, 4), (key2048, 4), (key2011, -4), (key2040, -4), (key2011, -4), (key2135, -4), (key2220, -4), (key2135, -4), (key2125, 12)]

theorem rawRowCheck15886 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form9 = rawRow15886 := by decide +kernel

def row15886 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

theorem rowCheck15886 : row15886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15886 := by decide +kernel

theorem rowEval15886 (x : Key → ℝ) : Integer.Sparse.eval row15886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15886, Integer.Sparse.eval_collectBalanced, rawRowCheck15886]

def rawRow15887 : Integer.Sparse Key := [(key2048, 4), (key2048, 4), (key2020, 4), (key2040, -4), (key2011, -4), (key2011, -4), (key2220, -4), (key2135, -4), (key2135, -4), (key2125, 12)]

theorem rawRowCheck15887 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form9 = rawRow15887 := by decide +kernel

def row15887 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

theorem rowCheck15887 : row15887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15887 := by decide +kernel

theorem rowEval15887 (x : Key → ℝ) : Integer.Sparse.eval row15887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15887, Integer.Sparse.eval_collectBalanced, rawRowCheck15887]

def rawRow15888 : Integer.Sparse Key := [(key2011, 4), (key2040, 4), (key2048, 4), (key2125, -4), (key2135, -4), (key2220, -4), (key2011, -4), (key2020, -4), (key2048, -4), (key2135, 12)]

theorem rawRowCheck15888 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form9 = rawRow15888 := by decide +kernel

def row15888 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck15888 : row15888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15888 := by decide +kernel

theorem rowEval15888 (x : Key → ℝ) : Integer.Sparse.eval row15888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15888, Integer.Sparse.eval_collectBalanced, rawRowCheck15888]

def rawRow15889 : Integer.Sparse Key := [(key2011, 4), (key2048, 4), (key2040, 4), (key2135, -4), (key2125, -4), (key2220, -4), (key2020, -4), (key2011, -4), (key2048, -4), (key2135, 12)]

theorem rawRowCheck15889 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form9 = rawRow15889 := by decide +kernel

def row15889 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck15889 : row15889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15889 := by decide +kernel

theorem rowEval15889 (x : Key → ℝ) : Integer.Sparse.eval row15889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15889, Integer.Sparse.eval_collectBalanced, rawRowCheck15889]

def rawRow15890 : Integer.Sparse Key := [(key2040, 4), (key2011, 4), (key2048, 4), (key2125, -4), (key2220, -4), (key2135, -4), (key2011, -4), (key2048, -4), (key2020, -4), (key2135, 12)]

theorem rawRowCheck15890 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form9 = rawRow15890 := by decide +kernel

def row15890 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck15890 : row15890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15890 := by decide +kernel

theorem rowEval15890 (x : Key → ℝ) : Integer.Sparse.eval row15890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15890, Integer.Sparse.eval_collectBalanced, rawRowCheck15890]

def rawRow15891 : Integer.Sparse Key := [(key2040, 4), (key2048, 4), (key2011, 4), (key2220, -4), (key2125, -4), (key2135, -4), (key2048, -4), (key2011, -4), (key2020, -4), (key2135, 12)]

theorem rawRowCheck15891 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form9 = rawRow15891 := by decide +kernel

def row15891 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck15891 : row15891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15891 := by decide +kernel

theorem rowEval15891 (x : Key → ℝ) : Integer.Sparse.eval row15891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15891, Integer.Sparse.eval_collectBalanced, rawRowCheck15891]

def rawRow15892 : Integer.Sparse Key := [(key2048, 4), (key2011, 4), (key2040, 4), (key2135, -4), (key2220, -4), (key2125, -4), (key2020, -4), (key2048, -4), (key2011, -4), (key2135, 12)]

theorem rawRowCheck15892 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form9 = rawRow15892 := by decide +kernel

def row15892 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck15892 : row15892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15892 := by decide +kernel

theorem rowEval15892 (x : Key → ℝ) : Integer.Sparse.eval row15892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15892, Integer.Sparse.eval_collectBalanced, rawRowCheck15892]

def rawRow15893 : Integer.Sparse Key := [(key2048, 4), (key2040, 4), (key2011, 4), (key2220, -4), (key2135, -4), (key2125, -4), (key2048, -4), (key2020, -4), (key2011, -4), (key2135, 12)]

theorem rawRowCheck15893 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form9 = rawRow15893 := by decide +kernel

def row15893 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck15893 : row15893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15893 := by decide +kernel

theorem rowEval15893 (x : Key → ℝ) : Integer.Sparse.eval row15893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15893, Integer.Sparse.eval_collectBalanced, rawRowCheck15893]

def rawRow15894 : Integer.Sparse Key := [(key2020, 4), (key2048, 4), (key2048, 4), (key2135, -4), (key2135, -4), (key2220, -4), (key2011, -4), (key2011, -4), (key2040, -4), (key2125, 12)]

theorem rawRowCheck15894 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form9 = rawRow15894 := by decide +kernel

def row15894 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

theorem rowCheck15894 : row15894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15894 := by decide +kernel

theorem rowEval15894 (x : Key → ℝ) : Integer.Sparse.eval row15894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15894, Integer.Sparse.eval_collectBalanced, rawRowCheck15894]

def rawRow15895 : Integer.Sparse Key := [(key2048, 4), (key2020, 4), (key2048, 4), (key2135, -4), (key2220, -4), (key2135, -4), (key2011, -4), (key2040, -4), (key2011, -4), (key2125, 12)]

theorem rawRowCheck15895 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form9 = rawRow15895 := by decide +kernel

def row15895 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

theorem rowCheck15895 : row15895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15895 := by decide +kernel

theorem rowEval15895 (x : Key → ℝ) : Integer.Sparse.eval row15895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15895, Integer.Sparse.eval_collectBalanced, rawRowCheck15895]

def rawRow15896 : Integer.Sparse Key := [(key2048, 4), (key2048, 4), (key2020, 4), (key2220, -4), (key2135, -4), (key2135, -4), (key2040, -4), (key2011, -4), (key2011, -4), (key2125, 12)]

theorem rawRowCheck15896 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form9 = rawRow15896 := by decide +kernel

def row15896 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

theorem rowCheck15896 : row15896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15896 := by decide +kernel

theorem rowEval15896 (x : Key → ℝ) : Integer.Sparse.eval row15896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15896, Integer.Sparse.eval_collectBalanced, rawRowCheck15896]

def rawRow15897 : Integer.Sparse Key := [(key2663, -1), (key2666, -1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2666, 2), (key2701, 2), (key2722, 2), (key2778, -1), (key2781, -1), (key2851, -1), (key2866, -1), (key2892, -1), (key2902, -1), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, 2), (key2895, 2), (key2902, 2), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2856, -1), (key2866, -1), (key2935, 2), (key2971, 2), (key2981, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, -1)]

theorem rawRowCheck15897 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form10 = rawRow15897 := by decide +kernel

def row15897 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

theorem rowCheck15897 : row15897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15897 := by decide +kernel

theorem rowEval15897 (x : Key → ℝ) : Integer.Sparse.eval row15897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15897, Integer.Sparse.eval_collectBalanced, rawRowCheck15897]

def rawRow15898 : Integer.Sparse Key := [(key2666, -1), (key2663, -1), (key2722, -1), (key2698, -1), (key2745, -1), (key2734, -1), (key2666, 2), (key2722, 2), (key2701, 2), (key2781, -1), (key2778, -1), (key2866, -1), (key2851, -1), (key2902, -1), (key2892, -1), (key2790, 2), (key2778, 2), (key2825, 2), (key2801, 2), (key2902, 2), (key2895, 2), (key2790, -1), (key2781, -1), (key2825, -1), (key2804, -1), (key2866, -1), (key2856, -1), (key2935, 2), (key2981, 2), (key2971, 2), (key2941, -1), (key2935, -1), (key2958, -1), (key2947, -1), (key2981, -1), (key2974, -1)]

theorem rawRowCheck15898 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form10 = rawRow15898 := by decide +kernel

def row15898 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

theorem rowCheck15898 : row15898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15898 := by decide +kernel

theorem rowEval15898 (x : Key → ℝ) : Integer.Sparse.eval row15898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15898, Integer.Sparse.eval_collectBalanced, rawRowCheck15898]

def rawRow15899 : Integer.Sparse Key := [(key2698, -1), (key2734, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2701, 2), (key2666, 2), (key2722, 2), (key2851, -1), (key2892, -1), (key2778, -1), (key2902, -1), (key2781, -1), (key2866, -1), (key2801, 2), (key2895, 2), (key2778, 2), (key2902, 2), (key2790, 2), (key2825, 2), (key2804, -1), (key2856, -1), (key2781, -1), (key2866, -1), (key2790, -1), (key2825, -1), (key2971, 2), (key2935, 2), (key2981, 2), (key2947, -1), (key2974, -1), (key2935, -1), (key2981, -1), (key2941, -1), (key2958, -1)]

theorem rawRowCheck15899 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form10 = rawRow15899 := by decide +kernel

def row15899 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

theorem rowCheck15899 : row15899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15899 := by decide +kernel

theorem rowEval15899 (x : Key → ℝ) : Integer.Sparse.eval row15899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15899, Integer.Sparse.eval_collectBalanced, rawRowCheck15899]

def rawRow15900 : Integer.Sparse Key := [(key2734, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2722, -1), (key2666, -1), (key2701, 2), (key2722, 2), (key2666, 2), (key2892, -1), (key2851, -1), (key2902, -1), (key2778, -1), (key2866, -1), (key2781, -1), (key2895, 2), (key2801, 2), (key2902, 2), (key2778, 2), (key2825, 2), (key2790, 2), (key2856, -1), (key2804, -1), (key2866, -1), (key2781, -1), (key2825, -1), (key2790, -1), (key2971, 2), (key2981, 2), (key2935, 2), (key2974, -1), (key2947, -1), (key2981, -1), (key2935, -1), (key2958, -1), (key2941, -1)]

theorem rawRowCheck15900 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form10 = rawRow15900 := by decide +kernel

def row15900 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

theorem rowCheck15900 : row15900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15900 := by decide +kernel

theorem rowEval15900 (x : Key → ℝ) : Integer.Sparse.eval row15900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15900, Integer.Sparse.eval_collectBalanced, rawRowCheck15900]

def rawRow15901 : Integer.Sparse Key := [(key2722, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2663, -1), (key2698, -1), (key2722, 2), (key2666, 2), (key2701, 2), (key2866, -1), (key2902, -1), (key2781, -1), (key2892, -1), (key2778, -1), (key2851, -1), (key2825, 2), (key2902, 2), (key2790, 2), (key2895, 2), (key2778, 2), (key2801, 2), (key2825, -1), (key2866, -1), (key2790, -1), (key2856, -1), (key2781, -1), (key2804, -1), (key2981, 2), (key2935, 2), (key2971, 2), (key2958, -1), (key2981, -1), (key2941, -1), (key2974, -1), (key2935, -1), (key2947, -1)]

theorem rawRowCheck15901 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form10 = rawRow15901 := by decide +kernel

def row15901 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

theorem rowCheck15901 : row15901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15901 := by decide +kernel

theorem rowEval15901 (x : Key → ℝ) : Integer.Sparse.eval row15901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15901, Integer.Sparse.eval_collectBalanced, rawRowCheck15901]

def rawRow15902 : Integer.Sparse Key := [(key2745, -1), (key2722, -1), (key2734, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2722, 2), (key2701, 2), (key2666, 2), (key2902, -1), (key2866, -1), (key2892, -1), (key2781, -1), (key2851, -1), (key2778, -1), (key2902, 2), (key2825, 2), (key2895, 2), (key2790, 2), (key2801, 2), (key2778, 2), (key2866, -1), (key2825, -1), (key2856, -1), (key2790, -1), (key2804, -1), (key2781, -1), (key2981, 2), (key2971, 2), (key2935, 2), (key2981, -1), (key2958, -1), (key2974, -1), (key2941, -1), (key2947, -1), (key2935, -1)]

theorem rawRowCheck15902 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form10 = rawRow15902 := by decide +kernel

def row15902 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

theorem rowCheck15902 : row15902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15902 := by decide +kernel

theorem rowEval15902 (x : Key → ℝ) : Integer.Sparse.eval row15902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15902, Integer.Sparse.eval_collectBalanced, rawRowCheck15902]

def rawRow15903 : Integer.Sparse Key := [(key2666, -1), (key2666, -1), (key2701, -1), (key2701, -1), (key2734, -1), (key2734, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2790, -1), (key2790, -1), (key2856, -1), (key2856, -1), (key2895, -1), (key2895, -1), (key2781, 2), (key2781, 2), (key2804, 2), (key2804, 2), (key2892, 2), (key2892, 2), (key2778, -1), (key2778, -1), (key2801, -1), (key2801, -1), (key2851, -1), (key2851, -1), (key2941, 2), (key2974, 2), (key2974, 2), (key2935, -1), (key2935, -1), (key2947, -1), (key2947, -1), (key2971, -1), (key2971, -1)]

theorem rawRowCheck15903 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form10 = rawRow15903 := by decide +kernel

def row15903 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2734, -2), (key2778, -2), (key2781, 4), (key2790, -2), (key2801, -2), (key2804, 4), (key2851, -2), (key2856, -2), (key2892, 4), (key2895, -2), (key2935, -2), (key2941, 2), (key2947, -2), (key2971, -2), (key2974, 4)]

theorem rowCheck15903 : row15903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15903 := by decide +kernel

theorem rowEval15903 (x : Key → ℝ) : Integer.Sparse.eval row15903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15903, Integer.Sparse.eval_collectBalanced, rawRowCheck15903]

def rawRow15904 : Integer.Sparse Key := [(key2701, -1), (key2734, -1), (key2666, -1), (key2734, -1), (key2666, -1), (key2701, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2856, -1), (key2895, -1), (key2790, -1), (key2895, -1), (key2790, -1), (key2856, -1), (key2804, 2), (key2892, 2), (key2781, 2), (key2892, 2), (key2781, 2), (key2804, 2), (key2801, -1), (key2851, -1), (key2778, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key2974, 2), (key2941, 2), (key2974, 2), (key2947, -1), (key2971, -1), (key2935, -1), (key2971, -1), (key2935, -1), (key2947, -1)]

theorem rawRowCheck15904 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form10 = rawRow15904 := by decide +kernel

def row15904 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2734, -2), (key2778, -2), (key2781, 4), (key2790, -2), (key2801, -2), (key2804, 4), (key2851, -2), (key2856, -2), (key2892, 4), (key2895, -2), (key2935, -2), (key2941, 2), (key2947, -2), (key2971, -2), (key2974, 4)]

theorem rowCheck15904 : row15904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15904 := by decide +kernel

theorem rowEval15904 (x : Key → ℝ) : Integer.Sparse.eval row15904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15904, Integer.Sparse.eval_collectBalanced, rawRowCheck15904]

def rawRow15905 : Integer.Sparse Key := [(key2734, -1), (key2701, -1), (key2734, -1), (key2666, -1), (key2701, -1), (key2666, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2895, -1), (key2856, -1), (key2895, -1), (key2790, -1), (key2856, -1), (key2790, -1), (key2892, 2), (key2804, 2), (key2892, 2), (key2781, 2), (key2804, 2), (key2781, 2), (key2851, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key2778, -1), (key2974, 2), (key2974, 2), (key2941, 2), (key2971, -1), (key2947, -1), (key2971, -1), (key2935, -1), (key2947, -1), (key2935, -1)]

theorem rawRowCheck15905 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form10 = rawRow15905 := by decide +kernel

def row15905 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2734, -2), (key2778, -2), (key2781, 4), (key2790, -2), (key2801, -2), (key2804, 4), (key2851, -2), (key2856, -2), (key2892, 4), (key2895, -2), (key2935, -2), (key2941, 2), (key2947, -2), (key2971, -2), (key2974, 4)]

theorem rowCheck15905 : row15905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15905 := by decide +kernel

theorem rowEval15905 (x : Key → ℝ) : Integer.Sparse.eval row15905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15905, Integer.Sparse.eval_collectBalanced, rawRowCheck15905]

def rawRow15906 : Integer.Sparse Key := [(key2698, -1), (key2701, -1), (key2851, -1), (key2971, -1), (key2856, -1), (key2974, -1), (key2722, 2), (key2866, 2), (key2981, 2), (key2663, -1), (key2666, -1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, 2), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, -1), (key2666, 2), (key2701, 2), (key2722, 2), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2856, -1), (key2866, -1)]

theorem rawRowCheck15906 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form10 = rawRow15906 := by decide +kernel

def row15906 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

theorem rowCheck15906 : row15906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15906 := by decide +kernel

theorem rowEval15906 (x : Key → ℝ) : Integer.Sparse.eval row15906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15906, Integer.Sparse.eval_collectBalanced, rawRowCheck15906]

def rawRow15907 : Integer.Sparse Key := [(key2701, -1), (key2698, -1), (key2971, -1), (key2851, -1), (key2974, -1), (key2856, -1), (key2722, 2), (key2981, 2), (key2866, 2), (key2666, -1), (key2663, -1), (key2722, -1), (key2698, -1), (key2745, -1), (key2734, -1), (key2790, 2), (key2778, 2), (key2825, 2), (key2801, 2), (key2902, 2), (key2895, 2), (key2941, -1), (key2935, -1), (key2958, -1), (key2947, -1), (key2981, -1), (key2974, -1), (key2666, 2), (key2722, 2), (key2701, 2), (key2790, -1), (key2781, -1), (key2825, -1), (key2804, -1), (key2866, -1), (key2856, -1)]

theorem rawRowCheck15907 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form10 = rawRow15907 := by decide +kernel

def row15907 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

theorem rowCheck15907 : row15907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15907 := by decide +kernel

theorem rowEval15907 (x : Key → ℝ) : Integer.Sparse.eval row15907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15907, Integer.Sparse.eval_collectBalanced, rawRowCheck15907]

def rawRow15908 : Integer.Sparse Key := [(key2851, -1), (key2856, -1), (key2698, -1), (key2974, -1), (key2701, -1), (key2971, -1), (key2866, 2), (key2722, 2), (key2981, 2), (key2698, -1), (key2734, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2801, 2), (key2895, 2), (key2778, 2), (key2902, 2), (key2790, 2), (key2825, 2), (key2947, -1), (key2974, -1), (key2935, -1), (key2981, -1), (key2941, -1), (key2958, -1), (key2701, 2), (key2666, 2), (key2722, 2), (key2804, -1), (key2856, -1), (key2781, -1), (key2866, -1), (key2790, -1), (key2825, -1)]

theorem rawRowCheck15908 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form10 = rawRow15908 := by decide +kernel

def row15908 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

theorem rowCheck15908 : row15908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15908 := by decide +kernel

theorem rowEval15908 (x : Key → ℝ) : Integer.Sparse.eval row15908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15908, Integer.Sparse.eval_collectBalanced, rawRowCheck15908]

def rawRow15909 : Integer.Sparse Key := [(key2856, -1), (key2851, -1), (key2974, -1), (key2698, -1), (key2971, -1), (key2701, -1), (key2866, 2), (key2981, 2), (key2722, 2), (key2734, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2722, -1), (key2666, -1), (key2895, 2), (key2801, 2), (key2902, 2), (key2778, 2), (key2825, 2), (key2790, 2), (key2974, -1), (key2947, -1), (key2981, -1), (key2935, -1), (key2958, -1), (key2941, -1), (key2701, 2), (key2722, 2), (key2666, 2), (key2856, -1), (key2804, -1), (key2866, -1), (key2781, -1), (key2825, -1), (key2790, -1)]

theorem rawRowCheck15909 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form10 = rawRow15909 := by decide +kernel

def row15909 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

theorem rowCheck15909 : row15909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15909 := by decide +kernel

theorem rowEval15909 (x : Key → ℝ) : Integer.Sparse.eval row15909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15909, Integer.Sparse.eval_collectBalanced, rawRowCheck15909]

def rawRow15910 : Integer.Sparse Key := [(key2971, -1), (key2974, -1), (key2701, -1), (key2856, -1), (key2698, -1), (key2851, -1), (key2981, 2), (key2722, 2), (key2866, 2), (key2722, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2663, -1), (key2698, -1), (key2825, 2), (key2902, 2), (key2790, 2), (key2895, 2), (key2778, 2), (key2801, 2), (key2958, -1), (key2981, -1), (key2941, -1), (key2974, -1), (key2935, -1), (key2947, -1), (key2722, 2), (key2666, 2), (key2701, 2), (key2825, -1), (key2866, -1), (key2790, -1), (key2856, -1), (key2781, -1), (key2804, -1)]

theorem rawRowCheck15910 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form10 = rawRow15910 := by decide +kernel

def row15910 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

theorem rowCheck15910 : row15910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15910 := by decide +kernel

theorem rowEval15910 (x : Key → ℝ) : Integer.Sparse.eval row15910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15910, Integer.Sparse.eval_collectBalanced, rawRowCheck15910]

def rawRow15911 : Integer.Sparse Key := [(key2974, -1), (key2971, -1), (key2856, -1), (key2701, -1), (key2851, -1), (key2698, -1), (key2981, 2), (key2866, 2), (key2722, 2), (key2745, -1), (key2722, -1), (key2734, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2902, 2), (key2825, 2), (key2895, 2), (key2790, 2), (key2801, 2), (key2778, 2), (key2981, -1), (key2958, -1), (key2974, -1), (key2941, -1), (key2947, -1), (key2935, -1), (key2722, 2), (key2701, 2), (key2666, 2), (key2866, -1), (key2825, -1), (key2856, -1), (key2790, -1), (key2804, -1), (key2781, -1)]

theorem rawRowCheck15911 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form10 = rawRow15911 := by decide +kernel

def row15911 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

theorem rowCheck15911 : row15911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15911 := by decide +kernel

theorem rowEval15911 (x : Key → ℝ) : Integer.Sparse.eval row15911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15911, Integer.Sparse.eval_collectBalanced, rawRowCheck15911]

def rawRow15912 : Integer.Sparse Key := [(key2734, -1), (key2734, -1), (key2892, -1), (key2892, -1), (key2895, -1), (key2895, -1), (key2745, 2), (key2902, 2), (key2902, 2), (key2666, -1), (key2666, -1), (key2781, -1), (key2781, -1), (key2790, -1), (key2790, -1), (key2701, 2), (key2701, 2), (key2804, 2), (key2804, 2), (key2856, 2), (key2856, 2), (key2722, -1), (key2722, -1), (key2825, -1), (key2825, -1), (key2866, -1), (key2866, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2778, -1), (key2778, -1), (key2801, -1), (key2801, -1), (key2851, -1), (key2851, -1)]

theorem rawRowCheck15912 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form10 = rawRow15912 := by decide +kernel

def row15912 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, 4), (key2722, -2), (key2734, -2), (key2745, 2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, -2), (key2804, 4), (key2825, -2), (key2851, -2), (key2856, 4), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, 4)]

theorem rowCheck15912 : row15912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15912 := by decide +kernel

theorem rowEval15912 (x : Key → ℝ) : Integer.Sparse.eval row15912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15912, Integer.Sparse.eval_collectBalanced, rawRowCheck15912]

def rawRow15913 : Integer.Sparse Key := [(key2892, -1), (key2895, -1), (key2734, -1), (key2895, -1), (key2734, -1), (key2892, -1), (key2902, 2), (key2745, 2), (key2902, 2), (key2781, -1), (key2790, -1), (key2666, -1), (key2790, -1), (key2666, -1), (key2781, -1), (key2804, 2), (key2856, 2), (key2701, 2), (key2856, 2), (key2701, 2), (key2804, 2), (key2825, -1), (key2866, -1), (key2722, -1), (key2866, -1), (key2722, -1), (key2825, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, -1), (key2851, -1), (key2778, -1), (key2851, -1), (key2778, -1), (key2801, -1)]

theorem rawRowCheck15913 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form10 = rawRow15913 := by decide +kernel

def row15913 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, 4), (key2722, -2), (key2734, -2), (key2745, 2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, -2), (key2804, 4), (key2825, -2), (key2851, -2), (key2856, 4), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, 4)]

theorem rowCheck15913 : row15913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15913 := by decide +kernel

theorem rowEval15913 (x : Key → ℝ) : Integer.Sparse.eval row15913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15913, Integer.Sparse.eval_collectBalanced, rawRowCheck15913]

def rawRow15914 : Integer.Sparse Key := [(key2895, -1), (key2892, -1), (key2895, -1), (key2734, -1), (key2892, -1), (key2734, -1), (key2902, 2), (key2902, 2), (key2745, 2), (key2790, -1), (key2781, -1), (key2790, -1), (key2666, -1), (key2781, -1), (key2666, -1), (key2856, 2), (key2804, 2), (key2856, 2), (key2701, 2), (key2804, 2), (key2701, 2), (key2866, -1), (key2825, -1), (key2866, -1), (key2722, -1), (key2825, -1), (key2722, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2851, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key2778, -1)]

theorem rawRowCheck15914 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form10 = rawRow15914 := by decide +kernel

def row15914 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, 4), (key2722, -2), (key2734, -2), (key2745, 2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, -2), (key2804, 4), (key2825, -2), (key2851, -2), (key2856, 4), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, 4)]

theorem rowCheck15914 : row15914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15914 := by decide +kernel

theorem rowEval15914 (x : Key → ℝ) : Integer.Sparse.eval row15914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15914, Integer.Sparse.eval_collectBalanced, rawRowCheck15914]

def rawRow15915 : Integer.Sparse Key := [(key1359, -2), (key1364, -2), (key1374, -2), (key1364, 6), (key1711, -2), (key1716, -2), (key1723, -2), (key1485, 2), (key1490, 2), (key1711, 2), (key1861, 2), (key1723, 2), (key1867, 2), (key1490, -2), (key1716, -2), (key1861, -2), (key1741, 6), (key1513, -2), (key1741, -2), (key1877, -2)]

theorem rawRowCheck15915 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form11 = rawRow15915 := by decide +kernel

def row15915 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

theorem rowCheck15915 : row15915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15915 := by decide +kernel

theorem rowEval15915 (x : Key → ℝ) : Integer.Sparse.eval row15915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15915, Integer.Sparse.eval_collectBalanced, rawRowCheck15915]

def rawRow15916 : Integer.Sparse Key := [(key1364, -2), (key1359, -2), (key1374, -2), (key1364, 6), (key1716, -2), (key1711, -2), (key1723, -2), (key1490, 2), (key1485, 2), (key1861, 2), (key1711, 2), (key1867, 2), (key1723, 2), (key1490, -2), (key1861, -2), (key1716, -2), (key1741, 6), (key1513, -2), (key1877, -2), (key1741, -2)]

theorem rawRowCheck15916 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form11 = rawRow15916 := by decide +kernel

def row15916 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

theorem rowCheck15916 : row15916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15916 := by decide +kernel

theorem rowEval15916 (x : Key → ℝ) : Integer.Sparse.eval row15916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15916, Integer.Sparse.eval_collectBalanced, rawRowCheck15916]

def rawRow15917 : Integer.Sparse Key := [(key1359, -2), (key1374, -2), (key1364, -2), (key1364, 6), (key1711, -2), (key1723, -2), (key1716, -2), (key1711, 2), (key1723, 2), (key1485, 2), (key1867, 2), (key1490, 2), (key1861, 2), (key1716, -2), (key1490, -2), (key1861, -2), (key1741, 6), (key1741, -2), (key1513, -2), (key1877, -2)]

theorem rawRowCheck15917 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form11 = rawRow15917 := by decide +kernel

def row15917 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

theorem rowCheck15917 : row15917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15917 := by decide +kernel

theorem rowEval15917 (x : Key → ℝ) : Integer.Sparse.eval row15917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15917, Integer.Sparse.eval_collectBalanced, rawRowCheck15917]

def rawRow15918 : Integer.Sparse Key := [(key1374, -2), (key1359, -2), (key1364, -2), (key1364, 6), (key1723, -2), (key1711, -2), (key1716, -2), (key1723, 2), (key1711, 2), (key1867, 2), (key1485, 2), (key1861, 2), (key1490, 2), (key1716, -2), (key1861, -2), (key1490, -2), (key1741, 6), (key1741, -2), (key1877, -2), (key1513, -2)]

theorem rawRowCheck15918 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form11 = rawRow15918 := by decide +kernel

def row15918 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

theorem rowCheck15918 : row15918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15918 := by decide +kernel

theorem rowEval15918 (x : Key → ℝ) : Integer.Sparse.eval row15918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15918, Integer.Sparse.eval_collectBalanced, rawRowCheck15918]

def rawRow15919 : Integer.Sparse Key := [(key1364, -2), (key1374, -2), (key1359, -2), (key1364, 6), (key1716, -2), (key1723, -2), (key1711, -2), (key1861, 2), (key1867, 2), (key1490, 2), (key1723, 2), (key1485, 2), (key1711, 2), (key1861, -2), (key1490, -2), (key1716, -2), (key1741, 6), (key1877, -2), (key1513, -2), (key1741, -2)]

theorem rawRowCheck15919 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form11 = rawRow15919 := by decide +kernel

def row15919 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

theorem rowCheck15919 : row15919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15919 := by decide +kernel

theorem rowEval15919 (x : Key → ℝ) : Integer.Sparse.eval row15919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15919, Integer.Sparse.eval_collectBalanced, rawRowCheck15919]

def rawRow15920 : Integer.Sparse Key := [(key1374, -2), (key1364, -2), (key1359, -2), (key1364, 6), (key1723, -2), (key1716, -2), (key1711, -2), (key1867, 2), (key1861, 2), (key1723, 2), (key1490, 2), (key1711, 2), (key1485, 2), (key1861, -2), (key1716, -2), (key1490, -2), (key1741, 6), (key1877, -2), (key1741, -2), (key1513, -2)]

theorem rawRowCheck15920 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form11 = rawRow15920 := by decide +kernel

def row15920 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

theorem rowCheck15920 : row15920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15920 := by decide +kernel

theorem rowEval15920 (x : Key → ℝ) : Integer.Sparse.eval row15920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15920, Integer.Sparse.eval_collectBalanced, rawRowCheck15920]

def rawRow15921 : Integer.Sparse Key := [(key1364, -2), (key1364, -2), (key1374, -2), (key1359, 6), (key1861, -2), (key1861, -2), (key1867, -2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1723, 2), (key1723, 2), (key1485, -2), (key1711, -2), (key1711, -2), (key1877, 6), (key1513, -2), (key1741, -2), (key1741, -2)]

theorem rawRowCheck15921 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form11 = rawRow15921 := by decide +kernel

def row15921 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

theorem rowCheck15921 : row15921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15921 := by decide +kernel

theorem rowEval15921 (x : Key → ℝ) : Integer.Sparse.eval row15921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15921, Integer.Sparse.eval_collectBalanced, rawRowCheck15921]

def rawRow15922 : Integer.Sparse Key := [(key1364, -2), (key1374, -2), (key1364, -2), (key1359, 6), (key1861, -2), (key1867, -2), (key1861, -2), (key1716, 2), (key1723, 2), (key1490, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1711, -2), (key1485, -2), (key1711, -2), (key1877, 6), (key1741, -2), (key1513, -2), (key1741, -2)]

theorem rawRowCheck15922 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form11 = rawRow15922 := by decide +kernel

def row15922 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

theorem rowCheck15922 : row15922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15922 := by decide +kernel

theorem rowEval15922 (x : Key → ℝ) : Integer.Sparse.eval row15922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15922, Integer.Sparse.eval_collectBalanced, rawRowCheck15922]

def rawRow15923 : Integer.Sparse Key := [(key1374, -2), (key1364, -2), (key1364, -2), (key1359, 6), (key1867, -2), (key1861, -2), (key1861, -2), (key1723, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1711, -2), (key1711, -2), (key1485, -2), (key1877, 6), (key1741, -2), (key1741, -2), (key1513, -2)]

theorem rawRowCheck15923 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form11 = rawRow15923 := by decide +kernel

def row15923 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

theorem rowCheck15923 : row15923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15923 := by decide +kernel

theorem rowEval15923 (x : Key → ℝ) : Integer.Sparse.eval row15923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15923, Integer.Sparse.eval_collectBalanced, rawRowCheck15923]

def rawRow15924 : Integer.Sparse Key := [(key1485, -2), (key1490, -2), (key1513, -2), (key1490, 6), (key1711, -2), (key1716, -2), (key1741, -2), (key1359, 2), (key1364, 2), (key1711, 2), (key1861, 2), (key1741, 2), (key1877, 2), (key1364, -2), (key1716, -2), (key1861, -2), (key1723, 6), (key1374, -2), (key1723, -2), (key1867, -2)]

theorem rawRowCheck15924 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form11 = rawRow15924 := by decide +kernel

def row15924 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

theorem rowCheck15924 : row15924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15924 := by decide +kernel

theorem rowEval15924 (x : Key → ℝ) : Integer.Sparse.eval row15924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15924, Integer.Sparse.eval_collectBalanced, rawRowCheck15924]

def rawRow15925 : Integer.Sparse Key := [(key1490, -2), (key1485, -2), (key1513, -2), (key1490, 6), (key1716, -2), (key1711, -2), (key1741, -2), (key1364, 2), (key1359, 2), (key1861, 2), (key1711, 2), (key1877, 2), (key1741, 2), (key1364, -2), (key1861, -2), (key1716, -2), (key1723, 6), (key1374, -2), (key1867, -2), (key1723, -2)]

theorem rawRowCheck15925 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form11 = rawRow15925 := by decide +kernel

def row15925 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

theorem rowCheck15925 : row15925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15925 := by decide +kernel

theorem rowEval15925 (x : Key → ℝ) : Integer.Sparse.eval row15925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15925, Integer.Sparse.eval_collectBalanced, rawRowCheck15925]

def rawRow15926 : Integer.Sparse Key := [(key1485, -2), (key1513, -2), (key1490, -2), (key1490, 6), (key1711, -2), (key1741, -2), (key1716, -2), (key1711, 2), (key1741, 2), (key1359, 2), (key1877, 2), (key1364, 2), (key1861, 2), (key1716, -2), (key1364, -2), (key1861, -2), (key1723, 6), (key1723, -2), (key1374, -2), (key1867, -2)]

theorem rawRowCheck15926 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form11 = rawRow15926 := by decide +kernel

def row15926 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

theorem rowCheck15926 : row15926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15926 := by decide +kernel

theorem rowEval15926 (x : Key → ℝ) : Integer.Sparse.eval row15926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15926, Integer.Sparse.eval_collectBalanced, rawRowCheck15926]

def rawRow15927 : Integer.Sparse Key := [(key1513, -2), (key1485, -2), (key1490, -2), (key1490, 6), (key1741, -2), (key1711, -2), (key1716, -2), (key1741, 2), (key1711, 2), (key1877, 2), (key1359, 2), (key1861, 2), (key1364, 2), (key1716, -2), (key1861, -2), (key1364, -2), (key1723, 6), (key1723, -2), (key1867, -2), (key1374, -2)]

theorem rawRowCheck15927 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form11 = rawRow15927 := by decide +kernel

def row15927 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

theorem rowCheck15927 : row15927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15927 := by decide +kernel

theorem rowEval15927 (x : Key → ℝ) : Integer.Sparse.eval row15927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15927, Integer.Sparse.eval_collectBalanced, rawRowCheck15927]

def rawRow15928 : Integer.Sparse Key := [(key1490, -2), (key1513, -2), (key1485, -2), (key1490, 6), (key1716, -2), (key1741, -2), (key1711, -2), (key1861, 2), (key1877, 2), (key1364, 2), (key1741, 2), (key1359, 2), (key1711, 2), (key1861, -2), (key1364, -2), (key1716, -2), (key1723, 6), (key1867, -2), (key1374, -2), (key1723, -2)]

theorem rawRowCheck15928 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form11 = rawRow15928 := by decide +kernel

def row15928 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

theorem rowCheck15928 : row15928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15928 := by decide +kernel

theorem rowEval15928 (x : Key → ℝ) : Integer.Sparse.eval row15928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15928, Integer.Sparse.eval_collectBalanced, rawRowCheck15928]

def rawRow15929 : Integer.Sparse Key := [(key1513, -2), (key1490, -2), (key1485, -2), (key1490, 6), (key1741, -2), (key1716, -2), (key1711, -2), (key1877, 2), (key1861, 2), (key1741, 2), (key1364, 2), (key1711, 2), (key1359, 2), (key1861, -2), (key1716, -2), (key1364, -2), (key1723, 6), (key1867, -2), (key1723, -2), (key1374, -2)]

theorem rawRowCheck15929 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form11 = rawRow15929 := by decide +kernel

def row15929 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

theorem rowCheck15929 : row15929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15929 := by decide +kernel

theorem rowEval15929 (x : Key → ℝ) : Integer.Sparse.eval row15929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15929, Integer.Sparse.eval_collectBalanced, rawRowCheck15929]

def rawRow15930 : Integer.Sparse Key := [(key1490, -2), (key1490, -2), (key1513, -2), (key1485, 6), (key1861, -2), (key1861, -2), (key1877, -2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1741, 2), (key1741, 2), (key1359, -2), (key1711, -2), (key1711, -2), (key1867, 6), (key1374, -2), (key1723, -2), (key1723, -2)]

theorem rawRowCheck15930 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form11 = rawRow15930 := by decide +kernel

def row15930 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

theorem rowCheck15930 : row15930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15930 := by decide +kernel

theorem rowEval15930 (x : Key → ℝ) : Integer.Sparse.eval row15930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15930, Integer.Sparse.eval_collectBalanced, rawRowCheck15930]

def rawRow15931 : Integer.Sparse Key := [(key1490, -2), (key1513, -2), (key1490, -2), (key1485, 6), (key1861, -2), (key1877, -2), (key1861, -2), (key1716, 2), (key1741, 2), (key1364, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1711, -2), (key1359, -2), (key1711, -2), (key1867, 6), (key1723, -2), (key1374, -2), (key1723, -2)]

theorem rawRowCheck15931 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form11 = rawRow15931 := by decide +kernel

def row15931 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

theorem rowCheck15931 : row15931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15931 := by decide +kernel

theorem rowEval15931 (x : Key → ℝ) : Integer.Sparse.eval row15931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15931, Integer.Sparse.eval_collectBalanced, rawRowCheck15931]

def rawRow15932 : Integer.Sparse Key := [(key1513, -2), (key1490, -2), (key1490, -2), (key1485, 6), (key1877, -2), (key1861, -2), (key1861, -2), (key1741, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1711, -2), (key1711, -2), (key1359, -2), (key1867, 6), (key1723, -2), (key1723, -2), (key1374, -2)]

theorem rawRowCheck15932 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form11 = rawRow15932 := by decide +kernel

def row15932 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

theorem rowCheck15932 : row15932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15932 := by decide +kernel

theorem rowEval15932 (x : Key → ℝ) : Integer.Sparse.eval row15932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15932, Integer.Sparse.eval_collectBalanced, rawRowCheck15932]

def rawRow15933 : Integer.Sparse Key := [(key1711, -2), (key1716, -2), (key1723, -2), (key1741, 6), (key1359, -2), (key1364, -2), (key1374, -2), (key1485, 2), (key1490, 2), (key1711, 2), (key1861, 2), (key1723, 2), (key1867, 2), (key1513, -2), (key1741, -2), (key1877, -2), (key1364, 6), (key1490, -2), (key1716, -2), (key1861, -2)]

theorem rawRowCheck15933 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form11 = rawRow15933 := by decide +kernel

def row15933 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

theorem rowCheck15933 : row15933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15933 := by decide +kernel

theorem rowEval15933 (x : Key → ℝ) : Integer.Sparse.eval row15933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15933, Integer.Sparse.eval_collectBalanced, rawRowCheck15933]

def rawRow15934 : Integer.Sparse Key := [(key1716, -2), (key1711, -2), (key1723, -2), (key1741, 6), (key1364, -2), (key1359, -2), (key1374, -2), (key1490, 2), (key1485, 2), (key1861, 2), (key1711, 2), (key1867, 2), (key1723, 2), (key1513, -2), (key1877, -2), (key1741, -2), (key1364, 6), (key1490, -2), (key1861, -2), (key1716, -2)]

theorem rawRowCheck15934 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form11 = rawRow15934 := by decide +kernel

def row15934 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

theorem rowCheck15934 : row15934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15934 := by decide +kernel

theorem rowEval15934 (x : Key → ℝ) : Integer.Sparse.eval row15934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15934, Integer.Sparse.eval_collectBalanced, rawRowCheck15934]

def rawRow15935 : Integer.Sparse Key := [(key1711, -2), (key1723, -2), (key1716, -2), (key1741, 6), (key1359, -2), (key1374, -2), (key1364, -2), (key1711, 2), (key1723, 2), (key1485, 2), (key1867, 2), (key1490, 2), (key1861, 2), (key1741, -2), (key1513, -2), (key1877, -2), (key1364, 6), (key1716, -2), (key1490, -2), (key1861, -2)]

theorem rawRowCheck15935 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form11 = rawRow15935 := by decide +kernel

def row15935 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

theorem rowCheck15935 : row15935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15935 := by decide +kernel

theorem rowEval15935 (x : Key → ℝ) : Integer.Sparse.eval row15935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15935, Integer.Sparse.eval_collectBalanced, rawRowCheck15935]

def rawRow15936 : Integer.Sparse Key := [(key1723, -2), (key1711, -2), (key1716, -2), (key1741, 6), (key1374, -2), (key1359, -2), (key1364, -2), (key1723, 2), (key1711, 2), (key1867, 2), (key1485, 2), (key1861, 2), (key1490, 2), (key1741, -2), (key1877, -2), (key1513, -2), (key1364, 6), (key1716, -2), (key1861, -2), (key1490, -2)]

theorem rawRowCheck15936 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form11 = rawRow15936 := by decide +kernel

def row15936 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

theorem rowCheck15936 : row15936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15936 := by decide +kernel

theorem rowEval15936 (x : Key → ℝ) : Integer.Sparse.eval row15936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15936, Integer.Sparse.eval_collectBalanced, rawRowCheck15936]

def rawRow15937 : Integer.Sparse Key := [(key1716, -2), (key1723, -2), (key1711, -2), (key1741, 6), (key1364, -2), (key1374, -2), (key1359, -2), (key1861, 2), (key1867, 2), (key1490, 2), (key1723, 2), (key1485, 2), (key1711, 2), (key1877, -2), (key1513, -2), (key1741, -2), (key1364, 6), (key1861, -2), (key1490, -2), (key1716, -2)]

theorem rawRowCheck15937 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form11 = rawRow15937 := by decide +kernel

def row15937 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

theorem rowCheck15937 : row15937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15937 := by decide +kernel

theorem rowEval15937 (x : Key → ℝ) : Integer.Sparse.eval row15937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15937, Integer.Sparse.eval_collectBalanced, rawRowCheck15937]

def rawRow15938 : Integer.Sparse Key := [(key1723, -2), (key1716, -2), (key1711, -2), (key1741, 6), (key1374, -2), (key1364, -2), (key1359, -2), (key1867, 2), (key1861, 2), (key1723, 2), (key1490, 2), (key1711, 2), (key1485, 2), (key1877, -2), (key1741, -2), (key1513, -2), (key1364, 6), (key1861, -2), (key1716, -2), (key1490, -2)]

theorem rawRowCheck15938 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form11 = rawRow15938 := by decide +kernel

def row15938 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

theorem rowCheck15938 : row15938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15938 := by decide +kernel

theorem rowEval15938 (x : Key → ℝ) : Integer.Sparse.eval row15938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15938, Integer.Sparse.eval_collectBalanced, rawRowCheck15938]

def rawRow15939 : Integer.Sparse Key := [(key1711, -2), (key1716, -2), (key1741, -2), (key1723, 6), (key1485, -2), (key1490, -2), (key1513, -2), (key1359, 2), (key1364, 2), (key1711, 2), (key1861, 2), (key1741, 2), (key1877, 2), (key1374, -2), (key1723, -2), (key1867, -2), (key1490, 6), (key1364, -2), (key1716, -2), (key1861, -2)]

theorem rawRowCheck15939 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form11 = rawRow15939 := by decide +kernel

def row15939 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

theorem rowCheck15939 : row15939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15939 := by decide +kernel

theorem rowEval15939 (x : Key → ℝ) : Integer.Sparse.eval row15939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15939, Integer.Sparse.eval_collectBalanced, rawRowCheck15939]

def rawRow15940 : Integer.Sparse Key := [(key1716, -2), (key1711, -2), (key1741, -2), (key1723, 6), (key1490, -2), (key1485, -2), (key1513, -2), (key1364, 2), (key1359, 2), (key1861, 2), (key1711, 2), (key1877, 2), (key1741, 2), (key1374, -2), (key1867, -2), (key1723, -2), (key1490, 6), (key1364, -2), (key1861, -2), (key1716, -2)]

theorem rawRowCheck15940 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form11 = rawRow15940 := by decide +kernel

def row15940 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

theorem rowCheck15940 : row15940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15940 := by decide +kernel

theorem rowEval15940 (x : Key → ℝ) : Integer.Sparse.eval row15940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15940, Integer.Sparse.eval_collectBalanced, rawRowCheck15940]

def rawRow15941 : Integer.Sparse Key := [(key1711, -2), (key1741, -2), (key1716, -2), (key1723, 6), (key1485, -2), (key1513, -2), (key1490, -2), (key1711, 2), (key1741, 2), (key1359, 2), (key1877, 2), (key1364, 2), (key1861, 2), (key1723, -2), (key1374, -2), (key1867, -2), (key1490, 6), (key1716, -2), (key1364, -2), (key1861, -2)]

theorem rawRowCheck15941 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form11 = rawRow15941 := by decide +kernel

def row15941 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

theorem rowCheck15941 : row15941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15941 := by decide +kernel

theorem rowEval15941 (x : Key → ℝ) : Integer.Sparse.eval row15941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15941, Integer.Sparse.eval_collectBalanced, rawRowCheck15941]

def rawRow15942 : Integer.Sparse Key := [(key1741, -2), (key1711, -2), (key1716, -2), (key1723, 6), (key1513, -2), (key1485, -2), (key1490, -2), (key1741, 2), (key1711, 2), (key1877, 2), (key1359, 2), (key1861, 2), (key1364, 2), (key1723, -2), (key1867, -2), (key1374, -2), (key1490, 6), (key1716, -2), (key1861, -2), (key1364, -2)]

theorem rawRowCheck15942 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form11 = rawRow15942 := by decide +kernel

def row15942 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

theorem rowCheck15942 : row15942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15942 := by decide +kernel

theorem rowEval15942 (x : Key → ℝ) : Integer.Sparse.eval row15942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15942, Integer.Sparse.eval_collectBalanced, rawRowCheck15942]

def rawRow15943 : Integer.Sparse Key := [(key1716, -2), (key1741, -2), (key1711, -2), (key1723, 6), (key1490, -2), (key1513, -2), (key1485, -2), (key1861, 2), (key1877, 2), (key1364, 2), (key1741, 2), (key1359, 2), (key1711, 2), (key1867, -2), (key1374, -2), (key1723, -2), (key1490, 6), (key1861, -2), (key1364, -2), (key1716, -2)]

theorem rawRowCheck15943 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form11 = rawRow15943 := by decide +kernel

def row15943 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

theorem rowCheck15943 : row15943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15943 := by decide +kernel

theorem rowEval15943 (x : Key → ℝ) : Integer.Sparse.eval row15943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15943, Integer.Sparse.eval_collectBalanced, rawRowCheck15943]

def rawRow15944 : Integer.Sparse Key := [(key1741, -2), (key1716, -2), (key1711, -2), (key1723, 6), (key1513, -2), (key1490, -2), (key1485, -2), (key1877, 2), (key1861, 2), (key1741, 2), (key1364, 2), (key1711, 2), (key1359, 2), (key1867, -2), (key1723, -2), (key1374, -2), (key1490, 6), (key1861, -2), (key1716, -2), (key1364, -2)]

theorem rawRowCheck15944 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form11 = rawRow15944 := by decide +kernel

def row15944 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

theorem rowCheck15944 : row15944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15944 := by decide +kernel

theorem rowEval15944 (x : Key → ℝ) : Integer.Sparse.eval row15944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15944, Integer.Sparse.eval_collectBalanced, rawRowCheck15944]

def rawRow15945 : Integer.Sparse Key := [(key1861, -2), (key1861, -2), (key1867, -2), (key1877, 6), (key1364, -2), (key1364, -2), (key1374, -2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1723, 2), (key1723, 2), (key1513, -2), (key1741, -2), (key1741, -2), (key1359, 6), (key1485, -2), (key1711, -2), (key1711, -2)]

theorem rawRowCheck15945 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form11 = rawRow15945 := by decide +kernel

def row15945 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

theorem rowCheck15945 : row15945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15945 := by decide +kernel

theorem rowEval15945 (x : Key → ℝ) : Integer.Sparse.eval row15945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15945, Integer.Sparse.eval_collectBalanced, rawRowCheck15945]

def rawRow15946 : Integer.Sparse Key := [(key1861, -2), (key1867, -2), (key1861, -2), (key1877, 6), (key1364, -2), (key1374, -2), (key1364, -2), (key1716, 2), (key1723, 2), (key1490, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1741, -2), (key1513, -2), (key1741, -2), (key1359, 6), (key1711, -2), (key1485, -2), (key1711, -2)]

theorem rawRowCheck15946 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form11 = rawRow15946 := by decide +kernel

def row15946 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

theorem rowCheck15946 : row15946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15946 := by decide +kernel

theorem rowEval15946 (x : Key → ℝ) : Integer.Sparse.eval row15946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15946, Integer.Sparse.eval_collectBalanced, rawRowCheck15946]

def rawRow15947 : Integer.Sparse Key := [(key1867, -2), (key1861, -2), (key1861, -2), (key1877, 6), (key1374, -2), (key1364, -2), (key1364, -2), (key1723, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1741, -2), (key1741, -2), (key1513, -2), (key1359, 6), (key1711, -2), (key1711, -2), (key1485, -2)]

theorem rawRowCheck15947 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form11 = rawRow15947 := by decide +kernel

def row15947 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

theorem rowCheck15947 : row15947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15947 := by decide +kernel

theorem rowEval15947 (x : Key → ℝ) : Integer.Sparse.eval row15947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15947, Integer.Sparse.eval_collectBalanced, rawRowCheck15947]

def rawRow15948 : Integer.Sparse Key := [(key1861, -2), (key1861, -2), (key1877, -2), (key1867, 6), (key1490, -2), (key1490, -2), (key1513, -2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1741, 2), (key1741, 2), (key1374, -2), (key1723, -2), (key1723, -2), (key1485, 6), (key1359, -2), (key1711, -2), (key1711, -2)]

theorem rawRowCheck15948 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form11 = rawRow15948 := by decide +kernel

def row15948 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

theorem rowCheck15948 : row15948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15948 := by decide +kernel

theorem rowEval15948 (x : Key → ℝ) : Integer.Sparse.eval row15948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15948, Integer.Sparse.eval_collectBalanced, rawRowCheck15948]

def rawRow15949 : Integer.Sparse Key := [(key1861, -2), (key1877, -2), (key1861, -2), (key1867, 6), (key1490, -2), (key1513, -2), (key1490, -2), (key1716, 2), (key1741, 2), (key1364, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1723, -2), (key1374, -2), (key1723, -2), (key1485, 6), (key1711, -2), (key1359, -2), (key1711, -2)]

theorem rawRowCheck15949 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form11 = rawRow15949 := by decide +kernel

def row15949 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

theorem rowCheck15949 : row15949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15949 := by decide +kernel

theorem rowEval15949 (x : Key → ℝ) : Integer.Sparse.eval row15949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15949, Integer.Sparse.eval_collectBalanced, rawRowCheck15949]

def rawRow15950 : Integer.Sparse Key := [(key1877, -2), (key1861, -2), (key1861, -2), (key1867, 6), (key1513, -2), (key1490, -2), (key1490, -2), (key1741, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1723, -2), (key1723, -2), (key1374, -2), (key1485, 6), (key1711, -2), (key1711, -2), (key1359, -2)]

theorem rawRowCheck15950 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form11 = rawRow15950 := by decide +kernel

def row15950 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

theorem rowCheck15950 : row15950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15950 := by decide +kernel

theorem rowEval15950 (x : Key → ℝ) : Integer.Sparse.eval row15950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15950, Integer.Sparse.eval_collectBalanced, rawRowCheck15950]

def rawRow15951 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2392, 2), (key2378, -2), (key2381, -2), (key2392, -2), (key2472, 2), (key2480, 2), (key2482, 2), (key2406, -1), (key2409, -1), (key2472, -1), (key2538, -1), (key2482, -1), (key2543, -1), (key2503, -2), (key2506, -2), (key2522, -2), (key2437, -1), (key2440, -1), (key2503, -1), (key2554, -1), (key2522, -1), (key2563, -1), (key2440, 4), (key2506, 4), (key2554, 4)]

theorem rawRowCheck15951 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form12 = rawRow15951 := by decide +kernel

def row15951 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

theorem rowCheck15951 : row15951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15951 := by decide +kernel

theorem rowEval15951 (x : Key → ℝ) : Integer.Sparse.eval row15951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15951, Integer.Sparse.eval_collectBalanced, rawRowCheck15951]

def rawRow15952 : Integer.Sparse Key := [(key2378, 2), (key2392, 2), (key2390, 2), (key2381, -2), (key2378, -2), (key2392, -2), (key2472, 2), (key2482, 2), (key2480, 2), (key2409, -1), (key2406, -1), (key2538, -1), (key2472, -1), (key2543, -1), (key2482, -1), (key2506, -2), (key2503, -2), (key2522, -2), (key2440, -1), (key2437, -1), (key2554, -1), (key2503, -1), (key2563, -1), (key2522, -1), (key2440, 4), (key2554, 4), (key2506, 4)]

theorem rawRowCheck15952 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form12 = rawRow15952 := by decide +kernel

def row15952 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

theorem rowCheck15952 : row15952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15952 := by decide +kernel

theorem rowEval15952 (x : Key → ℝ) : Integer.Sparse.eval row15952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15952, Integer.Sparse.eval_collectBalanced, rawRowCheck15952]

def rawRow15953 : Integer.Sparse Key := [(key2390, 2), (key2378, 2), (key2392, 2), (key2378, -2), (key2392, -2), (key2381, -2), (key2480, 2), (key2472, 2), (key2482, 2), (key2472, -1), (key2482, -1), (key2406, -1), (key2543, -1), (key2409, -1), (key2538, -1), (key2503, -2), (key2522, -2), (key2506, -2), (key2503, -1), (key2522, -1), (key2437, -1), (key2563, -1), (key2440, -1), (key2554, -1), (key2506, 4), (key2440, 4), (key2554, 4)]

theorem rawRowCheck15953 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form12 = rawRow15953 := by decide +kernel

def row15953 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

theorem rowCheck15953 : row15953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15953 := by decide +kernel

theorem rowEval15953 (x : Key → ℝ) : Integer.Sparse.eval row15953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15953, Integer.Sparse.eval_collectBalanced, rawRowCheck15953]

def rawRow15954 : Integer.Sparse Key := [(key2390, 2), (key2392, 2), (key2378, 2), (key2392, -2), (key2378, -2), (key2381, -2), (key2480, 2), (key2482, 2), (key2472, 2), (key2482, -1), (key2472, -1), (key2543, -1), (key2406, -1), (key2538, -1), (key2409, -1), (key2522, -2), (key2503, -2), (key2506, -2), (key2522, -1), (key2503, -1), (key2563, -1), (key2437, -1), (key2554, -1), (key2440, -1), (key2506, 4), (key2554, 4), (key2440, 4)]

theorem rawRowCheck15954 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form12 = rawRow15954 := by decide +kernel

def row15954 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

theorem rowCheck15954 : row15954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15954 := by decide +kernel

theorem rowEval15954 (x : Key → ℝ) : Integer.Sparse.eval row15954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15954, Integer.Sparse.eval_collectBalanced, rawRowCheck15954]

def rawRow15955 : Integer.Sparse Key := [(key2392, 2), (key2378, 2), (key2390, 2), (key2381, -2), (key2392, -2), (key2378, -2), (key2482, 2), (key2472, 2), (key2480, 2), (key2538, -1), (key2543, -1), (key2409, -1), (key2482, -1), (key2406, -1), (key2472, -1), (key2506, -2), (key2522, -2), (key2503, -2), (key2554, -1), (key2563, -1), (key2440, -1), (key2522, -1), (key2437, -1), (key2503, -1), (key2554, 4), (key2440, 4), (key2506, 4)]

theorem rawRowCheck15955 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form12 = rawRow15955 := by decide +kernel

def row15955 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

theorem rowCheck15955 : row15955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15955 := by decide +kernel

theorem rowEval15955 (x : Key → ℝ) : Integer.Sparse.eval row15955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15955, Integer.Sparse.eval_collectBalanced, rawRowCheck15955]

def rawRow15956 : Integer.Sparse Key := [(key2392, 2), (key2390, 2), (key2378, 2), (key2392, -2), (key2381, -2), (key2378, -2), (key2482, 2), (key2480, 2), (key2472, 2), (key2543, -1), (key2538, -1), (key2482, -1), (key2409, -1), (key2472, -1), (key2406, -1), (key2522, -2), (key2506, -2), (key2503, -2), (key2563, -1), (key2554, -1), (key2522, -1), (key2440, -1), (key2503, -1), (key2437, -1), (key2554, 4), (key2506, 4), (key2440, 4)]

theorem rawRowCheck15956 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form12 = rawRow15956 := by decide +kernel

def row15956 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

theorem rowCheck15956 : row15956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15956 := by decide +kernel

theorem rowEval15956 (x : Key → ℝ) : Integer.Sparse.eval row15956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15956, Integer.Sparse.eval_collectBalanced, rawRowCheck15956]

def rawRow15957 : Integer.Sparse Key := [(key2381, 2), (key2392, 2), (key2392, 2), (key2378, -2), (key2378, -2), (key2390, -2), (key2538, 2), (key2543, 2), (key2543, 2), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2554, -2), (key2554, -2), (key2563, -2), (key2440, -1), (key2440, -1), (key2506, -1), (key2506, -1), (key2522, -1), (key2522, -1), (key2437, 4), (key2503, 4), (key2503, 4)]

theorem rawRowCheck15957 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form12 = rawRow15957 := by decide +kernel

def row15957 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

theorem rowCheck15957 : row15957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15957 := by decide +kernel

theorem rowEval15957 (x : Key → ℝ) : Integer.Sparse.eval row15957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15957, Integer.Sparse.eval_collectBalanced, rawRowCheck15957]

def rawRow15958 : Integer.Sparse Key := [(key2392, 2), (key2381, 2), (key2392, 2), (key2378, -2), (key2390, -2), (key2378, -2), (key2543, 2), (key2538, 2), (key2543, 2), (key2472, -1), (key2480, -1), (key2406, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2554, -2), (key2563, -2), (key2554, -2), (key2506, -1), (key2522, -1), (key2440, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2503, 4), (key2437, 4), (key2503, 4)]

theorem rawRowCheck15958 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form12 = rawRow15958 := by decide +kernel

def row15958 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

theorem rowCheck15958 : row15958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15958 := by decide +kernel

theorem rowEval15958 (x : Key → ℝ) : Integer.Sparse.eval row15958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15958, Integer.Sparse.eval_collectBalanced, rawRowCheck15958]

def rawRow15959 : Integer.Sparse Key := [(key2392, 2), (key2392, 2), (key2381, 2), (key2390, -2), (key2378, -2), (key2378, -2), (key2543, 2), (key2543, 2), (key2538, 2), (key2480, -1), (key2472, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2406, -1), (key2563, -2), (key2554, -2), (key2554, -2), (key2522, -1), (key2506, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2440, -1), (key2503, 4), (key2503, 4), (key2437, 4)]

theorem rawRowCheck15959 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form12 = rawRow15959 := by decide +kernel

def row15959 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

theorem rowCheck15959 : row15959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15959 := by decide +kernel

theorem rowEval15959 (x : Key → ℝ) : Integer.Sparse.eval row15959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15959, Integer.Sparse.eval_collectBalanced, rawRowCheck15959]

def rawRow15960 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2440, 2), (key2406, -2), (key2409, -2), (key2440, -2), (key2472, 2), (key2503, 2), (key2506, 2), (key2378, -1), (key2381, -1), (key2472, -1), (key2538, -1), (key2506, -1), (key2554, -1), (key2480, -2), (key2482, -2), (key2522, -2), (key2390, -1), (key2392, -1), (key2480, -1), (key2543, -1), (key2522, -1), (key2563, -1), (key2392, 4), (key2482, 4), (key2543, 4)]

theorem rawRowCheck15960 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form12 = rawRow15960 := by decide +kernel

def row15960 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

theorem rowCheck15960 : row15960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15960 := by decide +kernel

theorem rowEval15960 (x : Key → ℝ) : Integer.Sparse.eval row15960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15960, Integer.Sparse.eval_collectBalanced, rawRowCheck15960]

def rawRow15961 : Integer.Sparse Key := [(key2406, 2), (key2440, 2), (key2437, 2), (key2409, -2), (key2406, -2), (key2440, -2), (key2472, 2), (key2506, 2), (key2503, 2), (key2381, -1), (key2378, -1), (key2538, -1), (key2472, -1), (key2554, -1), (key2506, -1), (key2482, -2), (key2480, -2), (key2522, -2), (key2392, -1), (key2390, -1), (key2543, -1), (key2480, -1), (key2563, -1), (key2522, -1), (key2392, 4), (key2543, 4), (key2482, 4)]

theorem rawRowCheck15961 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form12 = rawRow15961 := by decide +kernel

def row15961 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

theorem rowCheck15961 : row15961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15961 := by decide +kernel

theorem rowEval15961 (x : Key → ℝ) : Integer.Sparse.eval row15961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15961, Integer.Sparse.eval_collectBalanced, rawRowCheck15961]

def rawRow15962 : Integer.Sparse Key := [(key2437, 2), (key2406, 2), (key2440, 2), (key2406, -2), (key2440, -2), (key2409, -2), (key2503, 2), (key2472, 2), (key2506, 2), (key2472, -1), (key2506, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2480, -2), (key2522, -2), (key2482, -2), (key2480, -1), (key2522, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2482, 4), (key2392, 4), (key2543, 4)]

theorem rawRowCheck15962 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form12 = rawRow15962 := by decide +kernel

def row15962 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

theorem rowCheck15962 : row15962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15962 := by decide +kernel

theorem rowEval15962 (x : Key → ℝ) : Integer.Sparse.eval row15962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15962, Integer.Sparse.eval_collectBalanced, rawRowCheck15962]

def rawRow15963 : Integer.Sparse Key := [(key2437, 2), (key2440, 2), (key2406, 2), (key2440, -2), (key2406, -2), (key2409, -2), (key2503, 2), (key2506, 2), (key2472, 2), (key2506, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2538, -1), (key2381, -1), (key2522, -2), (key2480, -2), (key2482, -2), (key2522, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2543, -1), (key2392, -1), (key2482, 4), (key2543, 4), (key2392, 4)]

theorem rawRowCheck15963 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form12 = rawRow15963 := by decide +kernel

def row15963 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

theorem rowCheck15963 : row15963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15963 := by decide +kernel

theorem rowEval15963 (x : Key → ℝ) : Integer.Sparse.eval row15963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15963, Integer.Sparse.eval_collectBalanced, rawRowCheck15963]

def rawRow15964 : Integer.Sparse Key := [(key2440, 2), (key2406, 2), (key2437, 2), (key2409, -2), (key2440, -2), (key2406, -2), (key2506, 2), (key2472, 2), (key2503, 2), (key2538, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2378, -1), (key2472, -1), (key2482, -2), (key2522, -2), (key2480, -2), (key2543, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2390, -1), (key2480, -1), (key2543, 4), (key2392, 4), (key2482, 4)]

theorem rawRowCheck15964 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form12 = rawRow15964 := by decide +kernel

def row15964 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

theorem rowCheck15964 : row15964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15964 := by decide +kernel

theorem rowEval15964 (x : Key → ℝ) : Integer.Sparse.eval row15964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15964, Integer.Sparse.eval_collectBalanced, rawRowCheck15964]

def rawRow15965 : Integer.Sparse Key := [(key2440, 2), (key2437, 2), (key2406, 2), (key2440, -2), (key2409, -2), (key2406, -2), (key2506, 2), (key2503, 2), (key2472, 2), (key2554, -1), (key2538, -1), (key2506, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2522, -2), (key2482, -2), (key2480, -2), (key2563, -1), (key2543, -1), (key2522, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2543, 4), (key2482, 4), (key2392, 4)]

theorem rawRowCheck15965 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form12 = rawRow15965 := by decide +kernel

def row15965 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

theorem rowCheck15965 : row15965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15965 := by decide +kernel

theorem rowEval15965 (x : Key → ℝ) : Integer.Sparse.eval row15965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15965, Integer.Sparse.eval_collectBalanced, rawRowCheck15965]

def rawRow15966 : Integer.Sparse Key := [(key2409, 2), (key2440, 2), (key2440, 2), (key2406, -2), (key2406, -2), (key2437, -2), (key2538, 2), (key2554, 2), (key2554, 2), (key2378, -1), (key2378, -1), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2543, -2), (key2543, -2), (key2563, -2), (key2392, -1), (key2392, -1), (key2482, -1), (key2482, -1), (key2522, -1), (key2522, -1), (key2390, 4), (key2480, 4), (key2480, 4)]

theorem rawRowCheck15966 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form12 = rawRow15966 := by decide +kernel

def row15966 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck15966 : row15966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15966 := by decide +kernel

theorem rowEval15966 (x : Key → ℝ) : Integer.Sparse.eval row15966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15966, Integer.Sparse.eval_collectBalanced, rawRowCheck15966]

def rawRow15967 : Integer.Sparse Key := [(key2440, 2), (key2409, 2), (key2440, 2), (key2406, -2), (key2437, -2), (key2406, -2), (key2554, 2), (key2538, 2), (key2554, 2), (key2472, -1), (key2503, -1), (key2378, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2543, -2), (key2563, -2), (key2543, -2), (key2482, -1), (key2522, -1), (key2392, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2480, 4), (key2390, 4), (key2480, 4)]

theorem rawRowCheck15967 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form12 = rawRow15967 := by decide +kernel

def row15967 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck15967 : row15967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15967 := by decide +kernel

theorem rowEval15967 (x : Key → ℝ) : Integer.Sparse.eval row15967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15967, Integer.Sparse.eval_collectBalanced, rawRowCheck15967]

def rawRow15968 : Integer.Sparse Key := [(key2440, 2), (key2440, 2), (key2409, 2), (key2437, -2), (key2406, -2), (key2406, -2), (key2554, 2), (key2554, 2), (key2538, 2), (key2503, -1), (key2472, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2563, -2), (key2543, -2), (key2543, -2), (key2522, -1), (key2482, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2392, -1), (key2480, 4), (key2480, 4), (key2390, 4)]

theorem rawRowCheck15968 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form12 = rawRow15968 := by decide +kernel

def row15968 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck15968 : row15968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15968 := by decide +kernel

theorem rowEval15968 (x : Key → ℝ) : Integer.Sparse.eval row15968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15968, Integer.Sparse.eval_collectBalanced, rawRowCheck15968]

def rawRow15969 : Integer.Sparse Key := [(key2472, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2), (key2522, -2), (key2378, 2), (key2390, 2), (key2392, 2), (key2437, -1), (key2440, -1), (key2503, -1), (key2554, -1), (key2522, -1), (key2563, -1), (key2378, -2), (key2381, -2), (key2392, -2), (key2406, -1), (key2409, -1), (key2472, -1), (key2538, -1), (key2482, -1), (key2543, -1), (key2440, 4), (key2506, 4), (key2554, 4)]

theorem rawRowCheck15969 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form12 = rawRow15969 := by decide +kernel

def row15969 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

theorem rowCheck15969 : row15969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15969 := by decide +kernel

theorem rowEval15969 (x : Key → ℝ) : Integer.Sparse.eval row15969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15969, Integer.Sparse.eval_collectBalanced, rawRowCheck15969]

def rawRow15970 : Integer.Sparse Key := [(key2472, 2), (key2482, 2), (key2480, 2), (key2506, -2), (key2503, -2), (key2522, -2), (key2378, 2), (key2392, 2), (key2390, 2), (key2440, -1), (key2437, -1), (key2554, -1), (key2503, -1), (key2563, -1), (key2522, -1), (key2381, -2), (key2378, -2), (key2392, -2), (key2409, -1), (key2406, -1), (key2538, -1), (key2472, -1), (key2543, -1), (key2482, -1), (key2440, 4), (key2554, 4), (key2506, 4)]

theorem rawRowCheck15970 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form12 = rawRow15970 := by decide +kernel

def row15970 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

theorem rowCheck15970 : row15970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15970 := by decide +kernel

theorem rowEval15970 (x : Key → ℝ) : Integer.Sparse.eval row15970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15970, Integer.Sparse.eval_collectBalanced, rawRowCheck15970]

def rawRow15971 : Integer.Sparse Key := [(key2480, 2), (key2472, 2), (key2482, 2), (key2503, -2), (key2522, -2), (key2506, -2), (key2390, 2), (key2378, 2), (key2392, 2), (key2503, -1), (key2522, -1), (key2437, -1), (key2563, -1), (key2440, -1), (key2554, -1), (key2378, -2), (key2392, -2), (key2381, -2), (key2472, -1), (key2482, -1), (key2406, -1), (key2543, -1), (key2409, -1), (key2538, -1), (key2506, 4), (key2440, 4), (key2554, 4)]

theorem rawRowCheck15971 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form12 = rawRow15971 := by decide +kernel

def row15971 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

theorem rowCheck15971 : row15971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15971 := by decide +kernel

theorem rowEval15971 (x : Key → ℝ) : Integer.Sparse.eval row15971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15971, Integer.Sparse.eval_collectBalanced, rawRowCheck15971]

def rawRow15972 : Integer.Sparse Key := [(key2480, 2), (key2482, 2), (key2472, 2), (key2522, -2), (key2503, -2), (key2506, -2), (key2390, 2), (key2392, 2), (key2378, 2), (key2522, -1), (key2503, -1), (key2563, -1), (key2437, -1), (key2554, -1), (key2440, -1), (key2392, -2), (key2378, -2), (key2381, -2), (key2482, -1), (key2472, -1), (key2543, -1), (key2406, -1), (key2538, -1), (key2409, -1), (key2506, 4), (key2554, 4), (key2440, 4)]

theorem rawRowCheck15972 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form12 = rawRow15972 := by decide +kernel

def row15972 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

theorem rowCheck15972 : row15972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15972 := by decide +kernel

theorem rowEval15972 (x : Key → ℝ) : Integer.Sparse.eval row15972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15972, Integer.Sparse.eval_collectBalanced, rawRowCheck15972]

def rawRow15973 : Integer.Sparse Key := [(key2482, 2), (key2472, 2), (key2480, 2), (key2506, -2), (key2522, -2), (key2503, -2), (key2392, 2), (key2378, 2), (key2390, 2), (key2554, -1), (key2563, -1), (key2440, -1), (key2522, -1), (key2437, -1), (key2503, -1), (key2381, -2), (key2392, -2), (key2378, -2), (key2538, -1), (key2543, -1), (key2409, -1), (key2482, -1), (key2406, -1), (key2472, -1), (key2554, 4), (key2440, 4), (key2506, 4)]

theorem rawRowCheck15973 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form12 = rawRow15973 := by decide +kernel

def row15973 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

theorem rowCheck15973 : row15973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15973 := by decide +kernel

theorem rowEval15973 (x : Key → ℝ) : Integer.Sparse.eval row15973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15973, Integer.Sparse.eval_collectBalanced, rawRowCheck15973]

def rawRow15974 : Integer.Sparse Key := [(key2482, 2), (key2480, 2), (key2472, 2), (key2522, -2), (key2506, -2), (key2503, -2), (key2392, 2), (key2390, 2), (key2378, 2), (key2563, -1), (key2554, -1), (key2522, -1), (key2440, -1), (key2503, -1), (key2437, -1), (key2392, -2), (key2381, -2), (key2378, -2), (key2543, -1), (key2538, -1), (key2482, -1), (key2409, -1), (key2472, -1), (key2406, -1), (key2554, 4), (key2506, 4), (key2440, 4)]

theorem rawRowCheck15974 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form12 = rawRow15974 := by decide +kernel

def row15974 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

theorem rowCheck15974 : row15974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15974 := by decide +kernel

theorem rowEval15974 (x : Key → ℝ) : Integer.Sparse.eval row15974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15974, Integer.Sparse.eval_collectBalanced, rawRowCheck15974]

def rawRow15975 : Integer.Sparse Key := [(key2472, 2), (key2503, 2), (key2506, 2), (key2480, -2), (key2482, -2), (key2522, -2), (key2406, 2), (key2437, 2), (key2440, 2), (key2390, -1), (key2392, -1), (key2480, -1), (key2543, -1), (key2522, -1), (key2563, -1), (key2406, -2), (key2409, -2), (key2440, -2), (key2378, -1), (key2381, -1), (key2472, -1), (key2538, -1), (key2506, -1), (key2554, -1), (key2392, 4), (key2482, 4), (key2543, 4)]

theorem rawRowCheck15975 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form12 = rawRow15975 := by decide +kernel

def row15975 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

theorem rowCheck15975 : row15975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15975 := by decide +kernel

theorem rowEval15975 (x : Key → ℝ) : Integer.Sparse.eval row15975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15975, Integer.Sparse.eval_collectBalanced, rawRowCheck15975]

def rawRow15976 : Integer.Sparse Key := [(key2472, 2), (key2506, 2), (key2503, 2), (key2482, -2), (key2480, -2), (key2522, -2), (key2406, 2), (key2440, 2), (key2437, 2), (key2392, -1), (key2390, -1), (key2543, -1), (key2480, -1), (key2563, -1), (key2522, -1), (key2409, -2), (key2406, -2), (key2440, -2), (key2381, -1), (key2378, -1), (key2538, -1), (key2472, -1), (key2554, -1), (key2506, -1), (key2392, 4), (key2543, 4), (key2482, 4)]

theorem rawRowCheck15976 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form12 = rawRow15976 := by decide +kernel

def row15976 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

theorem rowCheck15976 : row15976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15976 := by decide +kernel

theorem rowEval15976 (x : Key → ℝ) : Integer.Sparse.eval row15976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15976, Integer.Sparse.eval_collectBalanced, rawRowCheck15976]

def rawRow15977 : Integer.Sparse Key := [(key2503, 2), (key2472, 2), (key2506, 2), (key2480, -2), (key2522, -2), (key2482, -2), (key2437, 2), (key2406, 2), (key2440, 2), (key2480, -1), (key2522, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2406, -2), (key2440, -2), (key2409, -2), (key2472, -1), (key2506, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2482, 4), (key2392, 4), (key2543, 4)]

theorem rawRowCheck15977 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form12 = rawRow15977 := by decide +kernel

def row15977 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

theorem rowCheck15977 : row15977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15977 := by decide +kernel

theorem rowEval15977 (x : Key → ℝ) : Integer.Sparse.eval row15977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15977, Integer.Sparse.eval_collectBalanced, rawRowCheck15977]

def rawRow15978 : Integer.Sparse Key := [(key2503, 2), (key2506, 2), (key2472, 2), (key2522, -2), (key2480, -2), (key2482, -2), (key2437, 2), (key2440, 2), (key2406, 2), (key2522, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2543, -1), (key2392, -1), (key2440, -2), (key2406, -2), (key2409, -2), (key2506, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2538, -1), (key2381, -1), (key2482, 4), (key2543, 4), (key2392, 4)]

theorem rawRowCheck15978 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form12 = rawRow15978 := by decide +kernel

def row15978 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

theorem rowCheck15978 : row15978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15978 := by decide +kernel

theorem rowEval15978 (x : Key → ℝ) : Integer.Sparse.eval row15978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15978, Integer.Sparse.eval_collectBalanced, rawRowCheck15978]

def rawRow15979 : Integer.Sparse Key := [(key2506, 2), (key2472, 2), (key2503, 2), (key2482, -2), (key2522, -2), (key2480, -2), (key2440, 2), (key2406, 2), (key2437, 2), (key2543, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2390, -1), (key2480, -1), (key2409, -2), (key2440, -2), (key2406, -2), (key2538, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2378, -1), (key2472, -1), (key2543, 4), (key2392, 4), (key2482, 4)]

theorem rawRowCheck15979 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form12 = rawRow15979 := by decide +kernel

def row15979 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

theorem rowCheck15979 : row15979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15979 := by decide +kernel

theorem rowEval15979 (x : Key → ℝ) : Integer.Sparse.eval row15979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15979, Integer.Sparse.eval_collectBalanced, rawRowCheck15979]

def rawRow15980 : Integer.Sparse Key := [(key2506, 2), (key2503, 2), (key2472, 2), (key2522, -2), (key2482, -2), (key2480, -2), (key2440, 2), (key2437, 2), (key2406, 2), (key2563, -1), (key2543, -1), (key2522, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2440, -2), (key2409, -2), (key2406, -2), (key2554, -1), (key2538, -1), (key2506, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2543, 4), (key2482, 4), (key2392, 4)]

theorem rawRowCheck15980 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form12 = rawRow15980 := by decide +kernel

def row15980 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

theorem rowCheck15980 : row15980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15980 := by decide +kernel

theorem rowEval15980 (x : Key → ℝ) : Integer.Sparse.eval row15980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15980, Integer.Sparse.eval_collectBalanced, rawRowCheck15980]

def rawRow15981 : Integer.Sparse Key := [(key2538, 2), (key2543, 2), (key2543, 2), (key2554, -2), (key2554, -2), (key2563, -2), (key2381, 2), (key2392, 2), (key2392, 2), (key2440, -1), (key2440, -1), (key2506, -1), (key2506, -1), (key2522, -1), (key2522, -1), (key2378, -2), (key2378, -2), (key2390, -2), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2437, 4), (key2503, 4), (key2503, 4)]

theorem rawRowCheck15981 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form12 = rawRow15981 := by decide +kernel

def row15981 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

theorem rowCheck15981 : row15981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15981 := by decide +kernel

theorem rowEval15981 (x : Key → ℝ) : Integer.Sparse.eval row15981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15981, Integer.Sparse.eval_collectBalanced, rawRowCheck15981]

def rawRow15982 : Integer.Sparse Key := [(key2543, 2), (key2538, 2), (key2543, 2), (key2554, -2), (key2563, -2), (key2554, -2), (key2392, 2), (key2381, 2), (key2392, 2), (key2506, -1), (key2522, -1), (key2440, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2378, -2), (key2390, -2), (key2378, -2), (key2472, -1), (key2480, -1), (key2406, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2503, 4), (key2437, 4), (key2503, 4)]

theorem rawRowCheck15982 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form12 = rawRow15982 := by decide +kernel

def row15982 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

theorem rowCheck15982 : row15982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15982 := by decide +kernel

theorem rowEval15982 (x : Key → ℝ) : Integer.Sparse.eval row15982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15982, Integer.Sparse.eval_collectBalanced, rawRowCheck15982]

def rawRow15983 : Integer.Sparse Key := [(key2543, 2), (key2543, 2), (key2538, 2), (key2563, -2), (key2554, -2), (key2554, -2), (key2392, 2), (key2392, 2), (key2381, 2), (key2522, -1), (key2506, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2440, -1), (key2390, -2), (key2378, -2), (key2378, -2), (key2480, -1), (key2472, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2406, -1), (key2503, 4), (key2503, 4), (key2437, 4)]

theorem rawRowCheck15983 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form12 = rawRow15983 := by decide +kernel

def row15983 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

theorem rowCheck15983 : row15983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15983 := by decide +kernel

theorem rowEval15983 (x : Key → ℝ) : Integer.Sparse.eval row15983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15983, Integer.Sparse.eval_collectBalanced, rawRowCheck15983]

def rawRow15984 : Integer.Sparse Key := [(key2538, 2), (key2554, 2), (key2554, 2), (key2543, -2), (key2543, -2), (key2563, -2), (key2409, 2), (key2440, 2), (key2440, 2), (key2392, -1), (key2392, -1), (key2482, -1), (key2482, -1), (key2522, -1), (key2522, -1), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, -1), (key2378, -1), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2390, 4), (key2480, 4), (key2480, 4)]

theorem rawRowCheck15984 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form12 = rawRow15984 := by decide +kernel

def row15984 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck15984 : row15984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15984 := by decide +kernel

theorem rowEval15984 (x : Key → ℝ) : Integer.Sparse.eval row15984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15984, Integer.Sparse.eval_collectBalanced, rawRowCheck15984]

def rawRow15985 : Integer.Sparse Key := [(key2554, 2), (key2538, 2), (key2554, 2), (key2543, -2), (key2563, -2), (key2543, -2), (key2440, 2), (key2409, 2), (key2440, 2), (key2482, -1), (key2522, -1), (key2392, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, -1), (key2503, -1), (key2378, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2480, 4), (key2390, 4), (key2480, 4)]

theorem rawRowCheck15985 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form12 = rawRow15985 := by decide +kernel

def row15985 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck15985 : row15985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15985 := by decide +kernel

theorem rowEval15985 (x : Key → ℝ) : Integer.Sparse.eval row15985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15985, Integer.Sparse.eval_collectBalanced, rawRowCheck15985]

def rawRow15986 : Integer.Sparse Key := [(key2554, 2), (key2554, 2), (key2538, 2), (key2563, -2), (key2543, -2), (key2543, -2), (key2440, 2), (key2440, 2), (key2409, 2), (key2522, -1), (key2482, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2392, -1), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, -1), (key2472, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2480, 4), (key2480, 4), (key2390, 4)]

theorem rawRowCheck15986 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form12 = rawRow15986 := by decide +kernel

def row15986 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck15986 : row15986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15986 := by decide +kernel

theorem rowEval15986 (x : Key → ℝ) : Integer.Sparse.eval row15986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15986, Integer.Sparse.eval_collectBalanced, rawRowCheck15986]

def rawRow15987 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2609, -1), (key2613, -1), (key2625, -1), (key2647, -1), (key2637, -1), (key2652, -1), (key2779, 2), (key2783, 2), (key2791, 2), (key2664, -1), (key2668, -1), (key2779, -1), (key2937, -1), (key2791, -1), (key2942, -1), (key2802, -1), (key2806, -1), (key2852, -1), (key2894, -1), (key2857, -1), (key2896, -1), (key2699, -1), (key2703, -1), (key2852, -1), (key2973, -1), (key2857, -1), (key2975, -1), (key2699, 2), (key2736, 2), (key2802, 2), (key2949, 2), (key2896, 2), (key2975, 2)]

theorem rawRowCheck15987 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form13 = rawRow15987 := by decide +kernel

def row15987 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

theorem rowCheck15987 : row15987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15987 := by decide +kernel

theorem rowEval15987 (x : Key → ℝ) : Integer.Sparse.eval row15987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck15987, Integer.Sparse.eval_collectBalanced, rawRowCheck15987]

def rawRow15988 : Integer.Sparse Key := [(key2629, 2), (key2625, 2), (key2637, 2), (key2613, -1), (key2609, -1), (key2647, -1), (key2625, -1), (key2652, -1), (key2637, -1), (key2783, 2), (key2779, 2), (key2791, 2), (key2668, -1), (key2664, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2791, -1), (key2806, -1), (key2802, -1), (key2894, -1), (key2852, -1), (key2896, -1), (key2857, -1), (key2703, -1), (key2699, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2857, -1), (key2736, 2), (key2699, 2), (key2949, 2), (key2802, 2), (key2975, 2), (key2896, 2)]

theorem rawRowCheck15988 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form13 = rawRow15988 := by decide +kernel

def row15988 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

theorem rowCheck15988 : row15988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15988 := by decide +kernel

theorem rowEval15988 (x : Key → ℝ) : Integer.Sparse.eval row15988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15988, Integer.Sparse.eval_collectBalanced, rawRowCheck15988]

def rawRow15989 : Integer.Sparse Key := [(key2625, 2), (key2637, 2), (key2629, 2), (key2625, -1), (key2637, -1), (key2609, -1), (key2652, -1), (key2613, -1), (key2647, -1), (key2779, 2), (key2791, 2), (key2783, 2), (key2779, -1), (key2791, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2852, -1), (key2857, -1), (key2802, -1), (key2896, -1), (key2806, -1), (key2894, -1), (key2852, -1), (key2857, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2802, 2), (key2896, 2), (key2699, 2), (key2975, 2), (key2736, 2), (key2949, 2)]

theorem rawRowCheck15989 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form13 = rawRow15989 := by decide +kernel

def row15989 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

theorem rowCheck15989 : row15989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15989 := by decide +kernel

theorem rowEval15989 (x : Key → ℝ) : Integer.Sparse.eval row15989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck15989, Integer.Sparse.eval_collectBalanced, rawRowCheck15989]

def rawRow15990 : Integer.Sparse Key := [(key2637, 2), (key2625, 2), (key2629, 2), (key2637, -1), (key2625, -1), (key2652, -1), (key2609, -1), (key2647, -1), (key2613, -1), (key2791, 2), (key2779, 2), (key2783, 2), (key2791, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2937, -1), (key2668, -1), (key2857, -1), (key2852, -1), (key2896, -1), (key2802, -1), (key2894, -1), (key2806, -1), (key2857, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2973, -1), (key2703, -1), (key2896, 2), (key2802, 2), (key2975, 2), (key2699, 2), (key2949, 2), (key2736, 2)]

theorem rawRowCheck15990 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form13 = rawRow15990 := by decide +kernel

def row15990 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

theorem rowCheck15990 : row15990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15990 := by decide +kernel

theorem rowEval15990 (x : Key → ℝ) : Integer.Sparse.eval row15990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck15990, Integer.Sparse.eval_collectBalanced, rawRowCheck15990]

def rawRow15991 : Integer.Sparse Key := [(key2629, 2), (key2637, 2), (key2625, 2), (key2647, -1), (key2652, -1), (key2613, -1), (key2637, -1), (key2609, -1), (key2625, -1), (key2783, 2), (key2791, 2), (key2779, 2), (key2937, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2664, -1), (key2779, -1), (key2894, -1), (key2896, -1), (key2806, -1), (key2857, -1), (key2802, -1), (key2852, -1), (key2973, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2699, -1), (key2852, -1), (key2949, 2), (key2975, 2), (key2736, 2), (key2896, 2), (key2699, 2), (key2802, 2)]

theorem rawRowCheck15991 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form13 = rawRow15991 := by decide +kernel

def row15991 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

theorem rowCheck15991 : row15991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15991 := by decide +kernel

theorem rowEval15991 (x : Key → ℝ) : Integer.Sparse.eval row15991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15991, Integer.Sparse.eval_collectBalanced, rawRowCheck15991]

def rawRow15992 : Integer.Sparse Key := [(key2637, 2), (key2629, 2), (key2625, 2), (key2652, -1), (key2647, -1), (key2637, -1), (key2613, -1), (key2625, -1), (key2609, -1), (key2791, 2), (key2783, 2), (key2779, 2), (key2942, -1), (key2937, -1), (key2791, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2896, -1), (key2894, -1), (key2857, -1), (key2806, -1), (key2852, -1), (key2802, -1), (key2975, -1), (key2973, -1), (key2857, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2975, 2), (key2949, 2), (key2896, 2), (key2736, 2), (key2802, 2), (key2699, 2)]

theorem rawRowCheck15992 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form13 = rawRow15992 := by decide +kernel

def row15992 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

theorem rowCheck15992 : row15992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15992 := by decide +kernel

theorem rowEval15992 (x : Key → ℝ) : Integer.Sparse.eval row15992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck15992, Integer.Sparse.eval_collectBalanced, rawRowCheck15992]

def rawRow15993 : Integer.Sparse Key := [(key2647, 2), (key2647, 2), (key2652, 2), (key2613, -1), (key2613, -1), (key2629, -1), (key2629, -1), (key2637, -1), (key2637, -1), (key2937, 2), (key2937, 2), (key2942, 2), (key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2975, -1), (key2975, -1), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2703, 2), (key2703, 2), (key2806, 2), (key2806, 2), (key2857, 2), (key2857, 2)]

theorem rawRowCheck15993 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form13 = rawRow15993 := by decide +kernel

def row15993 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

theorem rowCheck15993 : row15993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15993 := by decide +kernel

theorem rowEval15993 (x : Key → ℝ) : Integer.Sparse.eval row15993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15993, Integer.Sparse.eval_collectBalanced, rawRowCheck15993]

def rawRow15994 : Integer.Sparse Key := [(key2647, 2), (key2652, 2), (key2647, 2), (key2629, -1), (key2637, -1), (key2613, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2937, 2), (key2942, 2), (key2937, 2), (key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2806, 2), (key2857, 2), (key2703, 2), (key2857, 2), (key2703, 2), (key2806, 2)]

theorem rawRowCheck15994 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form13 = rawRow15994 := by decide +kernel

def row15994 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

theorem rowCheck15994 : row15994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15994 := by decide +kernel

theorem rowEval15994 (x : Key → ℝ) : Integer.Sparse.eval row15994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15994, Integer.Sparse.eval_collectBalanced, rawRowCheck15994]

def rawRow15995 : Integer.Sparse Key := [(key2652, 2), (key2647, 2), (key2647, 2), (key2637, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2613, -1), (key2942, 2), (key2937, 2), (key2937, 2), (key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2975, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2949, -1), (key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2857, 2), (key2806, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2703, 2)]

theorem rawRowCheck15995 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form13 = rawRow15995 := by decide +kernel

def row15995 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

theorem rowCheck15995 : row15995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15995 := by decide +kernel

theorem rowEval15995 (x : Key → ℝ) : Integer.Sparse.eval row15995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck15995, Integer.Sparse.eval_collectBalanced, rawRowCheck15995]

def rawRow15996 : Integer.Sparse Key := [(key2699, 2), (key2703, 2), (key2723, 2), (key2664, -1), (key2668, -1), (key2699, -1), (key2736, -1), (key2723, -1), (key2746, -1), (key2802, 2), (key2806, 2), (key2826, 2), (key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2779, -1), (key2783, -1), (key2852, -1), (key2894, -1), (key2867, -1), (key2903, -1), (key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2625, 2), (key2647, 2), (key2779, 2), (key2937, 2), (key2903, 2), (key2982, 2)]

theorem rawRowCheck15996 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form13 = rawRow15996 := by decide +kernel

def row15996 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

theorem rowCheck15996 : row15996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15996 := by decide +kernel

theorem rowEval15996 (x : Key → ℝ) : Integer.Sparse.eval row15996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck15996, Integer.Sparse.eval_collectBalanced, rawRowCheck15996]

def rawRow15997 : Integer.Sparse Key := [(key2703, 2), (key2699, 2), (key2723, 2), (key2668, -1), (key2664, -1), (key2736, -1), (key2699, -1), (key2746, -1), (key2723, -1), (key2806, 2), (key2802, 2), (key2826, 2), (key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2783, -1), (key2779, -1), (key2894, -1), (key2852, -1), (key2903, -1), (key2867, -1), (key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2647, 2), (key2625, 2), (key2937, 2), (key2779, 2), (key2982, 2), (key2903, 2)]

theorem rawRowCheck15997 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form13 = rawRow15997 := by decide +kernel

def row15997 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

theorem rowCheck15997 : row15997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15997 := by decide +kernel

theorem rowEval15997 (x : Key → ℝ) : Integer.Sparse.eval row15997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15997, Integer.Sparse.eval_collectBalanced, rawRowCheck15997]

def rawRow15998 : Integer.Sparse Key := [(key2699, 2), (key2723, 2), (key2703, 2), (key2699, -1), (key2723, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2802, 2), (key2826, 2), (key2806, 2), (key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2852, -1), (key2867, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2779, 2), (key2903, 2), (key2625, 2), (key2982, 2), (key2647, 2), (key2937, 2)]

theorem rawRowCheck15998 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form13 = rawRow15998 := by decide +kernel

def row15998 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

theorem rowCheck15998 : row15998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15998 := by decide +kernel

theorem rowEval15998 (x : Key → ℝ) : Integer.Sparse.eval row15998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck15998, Integer.Sparse.eval_collectBalanced, rawRowCheck15998]

def rawRow15999 : Integer.Sparse Key := [(key2723, 2), (key2699, 2), (key2703, 2), (key2723, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2736, -1), (key2668, -1), (key2826, 2), (key2802, 2), (key2806, 2), (key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2867, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2894, -1), (key2783, -1), (key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2903, 2), (key2779, 2), (key2982, 2), (key2625, 2), (key2937, 2), (key2647, 2)]

theorem rawRowCheck15999 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form13 = rawRow15999 := by decide +kernel

def row15999 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

theorem rowCheck15999 : row15999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15999 := by decide +kernel

theorem rowEval15999 (x : Key → ℝ) : Integer.Sparse.eval row15999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15999, Integer.Sparse.eval_collectBalanced, rawRowCheck15999]

end MUB6.Certificate.GramRows

end OAI
