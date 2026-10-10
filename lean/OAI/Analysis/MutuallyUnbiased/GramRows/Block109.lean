import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10880 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2625, -2), (key2629, -2), (key2852, -2), (key2973, -2), (key2867, -2), (key2982, -2), (key2637, -2), (key2857, -2), (key2975, -2), (key2664, 1), (key2668, 1), (key2699, 1), (key2736, 1), (key2723, 1), (key2746, 1), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1), (key2625, 1), (key2647, 1), (key2779, 1), (key2937, 1), (key2903, 1), (key2982, 1), (key2637, 1), (key2652, 1), (key2791, 1), (key2942, 1), (key2896, 1), (key2975, 1)]

theorem rawRowCheck10880 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form5 = rawRow10880 := by decide +kernel

def row10880 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10880 : row10880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10880 := by decide +kernel

theorem rowEval10880 (x : Key → ℝ) : Integer.Sparse.eval row10880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10880, Integer.Sparse.eval_collectBalanced, rawRowCheck10880]

def rawRow10881 : Integer.Sparse Key := [(key2703, -2), (key2699, -2), (key2723, -2), (key2629, -2), (key2625, -2), (key2973, -2), (key2852, -2), (key2982, -2), (key2867, -2), (key2637, -2), (key2975, -2), (key2857, -2), (key2668, 1), (key2664, 1), (key2736, 1), (key2699, 1), (key2746, 1), (key2723, 1), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1), (key2647, 1), (key2625, 1), (key2937, 1), (key2779, 1), (key2982, 1), (key2903, 1), (key2652, 1), (key2637, 1), (key2942, 1), (key2791, 1), (key2975, 1), (key2896, 1)]

theorem rawRowCheck10881 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form5 = rawRow10881 := by decide +kernel

def row10881 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10881 : row10881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10881 := by decide +kernel

theorem rowEval10881 (x : Key → ℝ) : Integer.Sparse.eval row10881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10881, Integer.Sparse.eval_collectBalanced, rawRowCheck10881]

def rawRow10882 : Integer.Sparse Key := [(key2699, -2), (key2723, -2), (key2703, -2), (key2852, -2), (key2867, -2), (key2625, -2), (key2982, -2), (key2629, -2), (key2973, -2), (key2857, -2), (key2637, -2), (key2975, -2), (key2699, 1), (key2723, 1), (key2664, 1), (key2746, 1), (key2668, 1), (key2736, 1), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2779, 1), (key2903, 1), (key2625, 1), (key2982, 1), (key2647, 1), (key2937, 1), (key2791, 1), (key2896, 1), (key2637, 1), (key2975, 1), (key2652, 1), (key2942, 1)]

theorem rawRowCheck10882 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form5 = rawRow10882 := by decide +kernel

def row10882 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10882 : row10882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10882 := by decide +kernel

theorem rowEval10882 (x : Key → ℝ) : Integer.Sparse.eval row10882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10882, Integer.Sparse.eval_collectBalanced, rawRowCheck10882]

def rawRow10883 : Integer.Sparse Key := [(key2723, -2), (key2699, -2), (key2703, -2), (key2867, -2), (key2852, -2), (key2982, -2), (key2625, -2), (key2973, -2), (key2629, -2), (key2857, -2), (key2975, -2), (key2637, -2), (key2723, 1), (key2699, 1), (key2746, 1), (key2664, 1), (key2736, 1), (key2668, 1), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1), (key2903, 1), (key2779, 1), (key2982, 1), (key2625, 1), (key2937, 1), (key2647, 1), (key2896, 1), (key2791, 1), (key2975, 1), (key2637, 1), (key2942, 1), (key2652, 1)]

theorem rawRowCheck10883 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form5 = rawRow10883 := by decide +kernel

def row10883 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10883 : row10883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10883 := by decide +kernel

theorem rowEval10883 (x : Key → ℝ) : Integer.Sparse.eval row10883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck10883, Integer.Sparse.eval_collectBalanced, rawRowCheck10883]

def rawRow10884 : Integer.Sparse Key := [(key2703, -2), (key2723, -2), (key2699, -2), (key2973, -2), (key2982, -2), (key2629, -2), (key2867, -2), (key2625, -2), (key2852, -2), (key2975, -2), (key2637, -2), (key2857, -2), (key2736, 1), (key2746, 1), (key2668, 1), (key2723, 1), (key2664, 1), (key2699, 1), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1), (key2937, 1), (key2982, 1), (key2647, 1), (key2903, 1), (key2625, 1), (key2779, 1), (key2942, 1), (key2975, 1), (key2652, 1), (key2896, 1), (key2637, 1), (key2791, 1)]

theorem rawRowCheck10884 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form5 = rawRow10884 := by decide +kernel

def row10884 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10884 : row10884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10884 := by decide +kernel

theorem rowEval10884 (x : Key → ℝ) : Integer.Sparse.eval row10884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10884, Integer.Sparse.eval_collectBalanced, rawRowCheck10884]

def rawRow10885 : Integer.Sparse Key := [(key2723, -2), (key2703, -2), (key2699, -2), (key2982, -2), (key2973, -2), (key2867, -2), (key2629, -2), (key2852, -2), (key2625, -2), (key2975, -2), (key2857, -2), (key2637, -2), (key2746, 1), (key2736, 1), (key2723, 1), (key2668, 1), (key2699, 1), (key2664, 1), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1), (key2982, 1), (key2937, 1), (key2903, 1), (key2647, 1), (key2779, 1), (key2625, 1), (key2975, 1), (key2942, 1), (key2896, 1), (key2652, 1), (key2791, 1), (key2637, 1)]

theorem rawRowCheck10885 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form5 = rawRow10885 := by decide +kernel

def row10885 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10885 : row10885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10885 := by decide +kernel

theorem rowEval10885 (x : Key → ℝ) : Integer.Sparse.eval row10885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck10885, Integer.Sparse.eval_collectBalanced, rawRowCheck10885]

def rawRow10886 : Integer.Sparse Key := [(key2852, -2), (key2857, -2), (key2867, -2), (key2625, -2), (key2637, -2), (key2699, -2), (key2975, -2), (key2723, -2), (key2982, -2), (key2629, -2), (key2703, -2), (key2973, -2), (key2779, 1), (key2791, 1), (key2802, 1), (key2896, 1), (key2826, 1), (key2903, 1), (key2625, 1), (key2637, 1), (key2699, 1), (key2975, 1), (key2723, 1), (key2982, 1), (key2609, 1), (key2652, 1), (key2664, 1), (key2942, 1), (key2746, 1), (key2959, 1), (key2613, 1), (key2647, 1), (key2668, 1), (key2937, 1), (key2736, 1), (key2949, 1)]

theorem rawRowCheck10886 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form5 = rawRow10886 := by decide +kernel

def row10886 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10886 : row10886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10886 := by decide +kernel

theorem rowEval10886 (x : Key → ℝ) : Integer.Sparse.eval row10886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10886, Integer.Sparse.eval_collectBalanced, rawRowCheck10886]

def rawRow10887 : Integer.Sparse Key := [(key2857, -2), (key2852, -2), (key2867, -2), (key2637, -2), (key2625, -2), (key2975, -2), (key2699, -2), (key2982, -2), (key2723, -2), (key2629, -2), (key2973, -2), (key2703, -2), (key2791, 1), (key2779, 1), (key2896, 1), (key2802, 1), (key2903, 1), (key2826, 1), (key2637, 1), (key2625, 1), (key2975, 1), (key2699, 1), (key2982, 1), (key2723, 1), (key2652, 1), (key2609, 1), (key2942, 1), (key2664, 1), (key2959, 1), (key2746, 1), (key2647, 1), (key2613, 1), (key2937, 1), (key2668, 1), (key2949, 1), (key2736, 1)]

theorem rawRowCheck10887 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form5 = rawRow10887 := by decide +kernel

def row10887 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10887 : row10887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10887 := by decide +kernel

theorem rowEval10887 (x : Key → ℝ) : Integer.Sparse.eval row10887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10887, Integer.Sparse.eval_collectBalanced, rawRowCheck10887]

def rawRow10888 : Integer.Sparse Key := [(key2852, -2), (key2867, -2), (key2857, -2), (key2699, -2), (key2723, -2), (key2625, -2), (key2982, -2), (key2637, -2), (key2975, -2), (key2703, -2), (key2629, -2), (key2973, -2), (key2802, 1), (key2826, 1), (key2779, 1), (key2903, 1), (key2791, 1), (key2896, 1), (key2699, 1), (key2723, 1), (key2625, 1), (key2982, 1), (key2637, 1), (key2975, 1), (key2664, 1), (key2746, 1), (key2609, 1), (key2959, 1), (key2652, 1), (key2942, 1), (key2668, 1), (key2736, 1), (key2613, 1), (key2949, 1), (key2647, 1), (key2937, 1)]

theorem rawRowCheck10888 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form5 = rawRow10888 := by decide +kernel

def row10888 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10888 : row10888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10888 := by decide +kernel

theorem rowEval10888 (x : Key → ℝ) : Integer.Sparse.eval row10888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10888, Integer.Sparse.eval_collectBalanced, rawRowCheck10888]

def rawRow10889 : Integer.Sparse Key := [(key2867, -2), (key2852, -2), (key2857, -2), (key2723, -2), (key2699, -2), (key2982, -2), (key2625, -2), (key2975, -2), (key2637, -2), (key2703, -2), (key2973, -2), (key2629, -2), (key2826, 1), (key2802, 1), (key2903, 1), (key2779, 1), (key2896, 1), (key2791, 1), (key2723, 1), (key2699, 1), (key2982, 1), (key2625, 1), (key2975, 1), (key2637, 1), (key2746, 1), (key2664, 1), (key2959, 1), (key2609, 1), (key2942, 1), (key2652, 1), (key2736, 1), (key2668, 1), (key2949, 1), (key2613, 1), (key2937, 1), (key2647, 1)]

theorem rawRowCheck10889 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form5 = rawRow10889 := by decide +kernel

def row10889 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10889 : row10889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10889 := by decide +kernel

theorem rowEval10889 (x : Key → ℝ) : Integer.Sparse.eval row10889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck10889, Integer.Sparse.eval_collectBalanced, rawRowCheck10889]

def rawRow10890 : Integer.Sparse Key := [(key2857, -2), (key2867, -2), (key2852, -2), (key2975, -2), (key2982, -2), (key2637, -2), (key2723, -2), (key2625, -2), (key2699, -2), (key2973, -2), (key2629, -2), (key2703, -2), (key2896, 1), (key2903, 1), (key2791, 1), (key2826, 1), (key2779, 1), (key2802, 1), (key2975, 1), (key2982, 1), (key2637, 1), (key2723, 1), (key2625, 1), (key2699, 1), (key2942, 1), (key2959, 1), (key2652, 1), (key2746, 1), (key2609, 1), (key2664, 1), (key2937, 1), (key2949, 1), (key2647, 1), (key2736, 1), (key2613, 1), (key2668, 1)]

theorem rawRowCheck10890 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form5 = rawRow10890 := by decide +kernel

def row10890 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10890 : row10890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10890 := by decide +kernel

theorem rowEval10890 (x : Key → ℝ) : Integer.Sparse.eval row10890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10890, Integer.Sparse.eval_collectBalanced, rawRowCheck10890]

def rawRow10891 : Integer.Sparse Key := [(key2867, -2), (key2857, -2), (key2852, -2), (key2982, -2), (key2975, -2), (key2723, -2), (key2637, -2), (key2699, -2), (key2625, -2), (key2973, -2), (key2703, -2), (key2629, -2), (key2903, 1), (key2896, 1), (key2826, 1), (key2791, 1), (key2802, 1), (key2779, 1), (key2982, 1), (key2975, 1), (key2723, 1), (key2637, 1), (key2699, 1), (key2625, 1), (key2959, 1), (key2942, 1), (key2746, 1), (key2652, 1), (key2664, 1), (key2609, 1), (key2949, 1), (key2937, 1), (key2736, 1), (key2647, 1), (key2668, 1), (key2613, 1)]

theorem rawRowCheck10891 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form5 = rawRow10891 := by decide +kernel

def row10891 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10891 : row10891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10891 := by decide +kernel

theorem rowEval10891 (x : Key → ℝ) : Integer.Sparse.eval row10891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck10891, Integer.Sparse.eval_collectBalanced, rawRowCheck10891]

def rawRow10892 : Integer.Sparse Key := [(key2973, -2), (key2975, -2), (key2982, -2), (key2629, -2), (key2637, -2), (key2703, -2), (key2857, -2), (key2723, -2), (key2867, -2), (key2625, -2), (key2699, -2), (key2852, -2), (key2937, 1), (key2942, 1), (key2949, 1), (key2975, 1), (key2959, 1), (key2982, 1), (key2647, 1), (key2652, 1), (key2736, 1), (key2896, 1), (key2746, 1), (key2903, 1), (key2613, 1), (key2637, 1), (key2668, 1), (key2791, 1), (key2723, 1), (key2826, 1), (key2609, 1), (key2625, 1), (key2664, 1), (key2779, 1), (key2699, 1), (key2802, 1)]

theorem rawRowCheck10892 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form5 = rawRow10892 := by decide +kernel

def row10892 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10892 : row10892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10892 := by decide +kernel

theorem rowEval10892 (x : Key → ℝ) : Integer.Sparse.eval row10892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10892, Integer.Sparse.eval_collectBalanced, rawRowCheck10892]

def rawRow10893 : Integer.Sparse Key := [(key2975, -2), (key2973, -2), (key2982, -2), (key2637, -2), (key2629, -2), (key2857, -2), (key2703, -2), (key2867, -2), (key2723, -2), (key2625, -2), (key2852, -2), (key2699, -2), (key2942, 1), (key2937, 1), (key2975, 1), (key2949, 1), (key2982, 1), (key2959, 1), (key2652, 1), (key2647, 1), (key2896, 1), (key2736, 1), (key2903, 1), (key2746, 1), (key2637, 1), (key2613, 1), (key2791, 1), (key2668, 1), (key2826, 1), (key2723, 1), (key2625, 1), (key2609, 1), (key2779, 1), (key2664, 1), (key2802, 1), (key2699, 1)]

theorem rawRowCheck10893 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form5 = rawRow10893 := by decide +kernel

def row10893 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10893 : row10893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10893 := by decide +kernel

theorem rowEval10893 (x : Key → ℝ) : Integer.Sparse.eval row10893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10893, Integer.Sparse.eval_collectBalanced, rawRowCheck10893]

def rawRow10894 : Integer.Sparse Key := [(key2973, -2), (key2982, -2), (key2975, -2), (key2703, -2), (key2723, -2), (key2629, -2), (key2867, -2), (key2637, -2), (key2857, -2), (key2699, -2), (key2625, -2), (key2852, -2), (key2949, 1), (key2959, 1), (key2937, 1), (key2982, 1), (key2942, 1), (key2975, 1), (key2736, 1), (key2746, 1), (key2647, 1), (key2903, 1), (key2652, 1), (key2896, 1), (key2668, 1), (key2723, 1), (key2613, 1), (key2826, 1), (key2637, 1), (key2791, 1), (key2664, 1), (key2699, 1), (key2609, 1), (key2802, 1), (key2625, 1), (key2779, 1)]

theorem rawRowCheck10894 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form5 = rawRow10894 := by decide +kernel

def row10894 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10894 : row10894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10894 := by decide +kernel

theorem rowEval10894 (x : Key → ℝ) : Integer.Sparse.eval row10894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10894, Integer.Sparse.eval_collectBalanced, rawRowCheck10894]

def rawRow10895 : Integer.Sparse Key := [(key2982, -2), (key2973, -2), (key2975, -2), (key2723, -2), (key2703, -2), (key2867, -2), (key2629, -2), (key2857, -2), (key2637, -2), (key2699, -2), (key2852, -2), (key2625, -2), (key2959, 1), (key2949, 1), (key2982, 1), (key2937, 1), (key2975, 1), (key2942, 1), (key2746, 1), (key2736, 1), (key2903, 1), (key2647, 1), (key2896, 1), (key2652, 1), (key2723, 1), (key2668, 1), (key2826, 1), (key2613, 1), (key2791, 1), (key2637, 1), (key2699, 1), (key2664, 1), (key2802, 1), (key2609, 1), (key2779, 1), (key2625, 1)]

theorem rawRowCheck10895 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form5 = rawRow10895 := by decide +kernel

def row10895 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10895 : row10895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10895 := by decide +kernel

theorem rowEval10895 (x : Key → ℝ) : Integer.Sparse.eval row10895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck10895, Integer.Sparse.eval_collectBalanced, rawRowCheck10895]

def rawRow10896 : Integer.Sparse Key := [(key2975, -2), (key2982, -2), (key2973, -2), (key2857, -2), (key2867, -2), (key2637, -2), (key2723, -2), (key2629, -2), (key2703, -2), (key2852, -2), (key2625, -2), (key2699, -2), (key2975, 1), (key2982, 1), (key2942, 1), (key2959, 1), (key2937, 1), (key2949, 1), (key2896, 1), (key2903, 1), (key2652, 1), (key2746, 1), (key2647, 1), (key2736, 1), (key2791, 1), (key2826, 1), (key2637, 1), (key2723, 1), (key2613, 1), (key2668, 1), (key2779, 1), (key2802, 1), (key2625, 1), (key2699, 1), (key2609, 1), (key2664, 1)]

theorem rawRowCheck10896 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form5 = rawRow10896 := by decide +kernel

def row10896 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10896 : row10896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10896 := by decide +kernel

theorem rowEval10896 (x : Key → ℝ) : Integer.Sparse.eval row10896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10896, Integer.Sparse.eval_collectBalanced, rawRowCheck10896]

def rawRow10897 : Integer.Sparse Key := [(key2982, -2), (key2975, -2), (key2973, -2), (key2867, -2), (key2857, -2), (key2723, -2), (key2637, -2), (key2703, -2), (key2629, -2), (key2852, -2), (key2699, -2), (key2625, -2), (key2982, 1), (key2975, 1), (key2959, 1), (key2942, 1), (key2949, 1), (key2937, 1), (key2903, 1), (key2896, 1), (key2746, 1), (key2652, 1), (key2736, 1), (key2647, 1), (key2826, 1), (key2791, 1), (key2723, 1), (key2637, 1), (key2668, 1), (key2613, 1), (key2802, 1), (key2779, 1), (key2699, 1), (key2625, 1), (key2664, 1), (key2609, 1)]

theorem rawRowCheck10897 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form5 = rawRow10897 := by decide +kernel

def row10897 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10897 : row10897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10897 := by decide +kernel

theorem rowEval10897 (x : Key → ℝ) : Integer.Sparse.eval row10897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck10897, Integer.Sparse.eval_collectBalanced, rawRowCheck10897]

def rawRow10898 : Integer.Sparse Key := [(key2647, -2), (key2647, -2), (key2652, -2), (key2736, -2), (key2736, -2), (key2894, -2), (key2894, -2), (key2896, -2), (key2896, -2), (key2746, -2), (key2903, -2), (key2903, -2), (key2613, 1), (key2613, 1), (key2629, 1), (key2629, 1), (key2637, 1), (key2637, 1), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1), (key2703, 1), (key2703, 1), (key2806, 1), (key2806, 1), (key2857, 1), (key2857, 1), (key2723, 1), (key2723, 1), (key2826, 1), (key2826, 1), (key2867, 1), (key2867, 1)]

theorem rawRowCheck10898 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form5 = rawRow10898 := by decide +kernel

def row10898 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

theorem rowCheck10898 : row10898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10898 := by decide +kernel

theorem rowEval10898 (x : Key → ℝ) : Integer.Sparse.eval row10898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10898, Integer.Sparse.eval_collectBalanced, rawRowCheck10898]

def rawRow10899 : Integer.Sparse Key := [(key2647, -2), (key2652, -2), (key2647, -2), (key2894, -2), (key2896, -2), (key2736, -2), (key2896, -2), (key2736, -2), (key2894, -2), (key2903, -2), (key2746, -2), (key2903, -2), (key2629, 1), (key2637, 1), (key2613, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2806, 1), (key2857, 1), (key2703, 1), (key2857, 1), (key2703, 1), (key2806, 1), (key2826, 1), (key2867, 1), (key2723, 1), (key2867, 1), (key2723, 1), (key2826, 1)]

theorem rawRowCheck10899 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form5 = rawRow10899 := by decide +kernel

def row10899 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

theorem rowCheck10899 : row10899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10899 := by decide +kernel

theorem rowEval10899 (x : Key → ℝ) : Integer.Sparse.eval row10899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10899, Integer.Sparse.eval_collectBalanced, rawRowCheck10899]

def rawRow10900 : Integer.Sparse Key := [(key2652, -2), (key2647, -2), (key2647, -2), (key2896, -2), (key2894, -2), (key2896, -2), (key2736, -2), (key2894, -2), (key2736, -2), (key2903, -2), (key2903, -2), (key2746, -2), (key2637, 1), (key2629, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2613, 1), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2857, 1), (key2806, 1), (key2857, 1), (key2703, 1), (key2806, 1), (key2703, 1), (key2867, 1), (key2826, 1), (key2867, 1), (key2723, 1), (key2826, 1), (key2723, 1)]

theorem rawRowCheck10900 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form5 = rawRow10900 := by decide +kernel

def row10900 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

theorem rowCheck10900 : row10900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10900 := by decide +kernel

theorem rowEval10900 (x : Key → ℝ) : Integer.Sparse.eval row10900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10900, Integer.Sparse.eval_collectBalanced, rawRowCheck10900]

def rawRow10901 : Integer.Sparse Key := [(key2736, -2), (key2736, -2), (key2746, -2), (key2647, -2), (key2647, -2), (key2894, -2), (key2894, -2), (key2903, -2), (key2903, -2), (key2652, -2), (key2896, -2), (key2896, -2), (key2668, 1), (key2668, 1), (key2703, 1), (key2703, 1), (key2723, 1), (key2723, 1), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1), (key2629, 1), (key2629, 1), (key2783, 1), (key2783, 1), (key2867, 1), (key2867, 1), (key2637, 1), (key2637, 1), (key2791, 1), (key2791, 1), (key2857, 1), (key2857, 1)]

theorem rawRowCheck10901 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form5 = rawRow10901 := by decide +kernel

def row10901 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

theorem rowCheck10901 : row10901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10901 := by decide +kernel

theorem rowEval10901 (x : Key → ℝ) : Integer.Sparse.eval row10901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10901, Integer.Sparse.eval_collectBalanced, rawRowCheck10901]

def rawRow10902 : Integer.Sparse Key := [(key2736, -2), (key2746, -2), (key2736, -2), (key2894, -2), (key2903, -2), (key2647, -2), (key2903, -2), (key2647, -2), (key2894, -2), (key2896, -2), (key2652, -2), (key2896, -2), (key2703, 1), (key2723, 1), (key2668, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2857, 1), (key2637, 1), (key2857, 1), (key2637, 1), (key2791, 1)]

theorem rawRowCheck10902 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form5 = rawRow10902 := by decide +kernel

def row10902 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

theorem rowCheck10902 : row10902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10902 := by decide +kernel

theorem rowEval10902 (x : Key → ℝ) : Integer.Sparse.eval row10902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10902, Integer.Sparse.eval_collectBalanced, rawRowCheck10902]

def rawRow10903 : Integer.Sparse Key := [(key2746, -2), (key2736, -2), (key2736, -2), (key2903, -2), (key2894, -2), (key2903, -2), (key2647, -2), (key2894, -2), (key2647, -2), (key2896, -2), (key2896, -2), (key2652, -2), (key2723, 1), (key2703, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2668, 1), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1), (key2867, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2629, 1), (key2857, 1), (key2791, 1), (key2857, 1), (key2637, 1), (key2791, 1), (key2637, 1)]

theorem rawRowCheck10903 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form5 = rawRow10903 := by decide +kernel

def row10903 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

theorem rowCheck10903 : row10903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10903 := by decide +kernel

theorem rowEval10903 (x : Key → ℝ) : Integer.Sparse.eval row10903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck10903, Integer.Sparse.eval_collectBalanced, rawRowCheck10903]

def rawRow10904 : Integer.Sparse Key := [(key2894, -2), (key2896, -2), (key2903, -2), (key2647, -2), (key2652, -2), (key2736, -2), (key2896, -2), (key2746, -2), (key2903, -2), (key2647, -2), (key2736, -2), (key2894, -2), (key2783, 1), (key2791, 1), (key2806, 1), (key2857, 1), (key2826, 1), (key2867, 1), (key2629, 1), (key2637, 1), (key2703, 1), (key2857, 1), (key2723, 1), (key2867, 1), (key2613, 1), (key2637, 1), (key2668, 1), (key2791, 1), (key2723, 1), (key2826, 1), (key2613, 1), (key2629, 1), (key2668, 1), (key2783, 1), (key2703, 1), (key2806, 1)]

theorem rawRowCheck10904 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form5 = rawRow10904 := by decide +kernel

def row10904 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

theorem rowCheck10904 : row10904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10904 := by decide +kernel

theorem rowEval10904 (x : Key → ℝ) : Integer.Sparse.eval row10904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10904, Integer.Sparse.eval_collectBalanced, rawRowCheck10904]

def rawRow10905 : Integer.Sparse Key := [(key2896, -2), (key2894, -2), (key2903, -2), (key2652, -2), (key2647, -2), (key2896, -2), (key2736, -2), (key2903, -2), (key2746, -2), (key2647, -2), (key2894, -2), (key2736, -2), (key2791, 1), (key2783, 1), (key2857, 1), (key2806, 1), (key2867, 1), (key2826, 1), (key2637, 1), (key2629, 1), (key2857, 1), (key2703, 1), (key2867, 1), (key2723, 1), (key2637, 1), (key2613, 1), (key2791, 1), (key2668, 1), (key2826, 1), (key2723, 1), (key2629, 1), (key2613, 1), (key2783, 1), (key2668, 1), (key2806, 1), (key2703, 1)]

theorem rawRowCheck10905 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form5 = rawRow10905 := by decide +kernel

def row10905 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

theorem rowCheck10905 : row10905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10905 := by decide +kernel

theorem rowEval10905 (x : Key → ℝ) : Integer.Sparse.eval row10905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10905, Integer.Sparse.eval_collectBalanced, rawRowCheck10905]

def rawRow10906 : Integer.Sparse Key := [(key2894, -2), (key2903, -2), (key2896, -2), (key2736, -2), (key2746, -2), (key2647, -2), (key2903, -2), (key2652, -2), (key2896, -2), (key2736, -2), (key2647, -2), (key2894, -2), (key2806, 1), (key2826, 1), (key2783, 1), (key2867, 1), (key2791, 1), (key2857, 1), (key2703, 1), (key2723, 1), (key2629, 1), (key2867, 1), (key2637, 1), (key2857, 1), (key2668, 1), (key2723, 1), (key2613, 1), (key2826, 1), (key2637, 1), (key2791, 1), (key2668, 1), (key2703, 1), (key2613, 1), (key2806, 1), (key2629, 1), (key2783, 1)]

theorem rawRowCheck10906 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form5 = rawRow10906 := by decide +kernel

def row10906 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

theorem rowCheck10906 : row10906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10906 := by decide +kernel

theorem rowEval10906 (x : Key → ℝ) : Integer.Sparse.eval row10906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10906, Integer.Sparse.eval_collectBalanced, rawRowCheck10906]

def rawRow10907 : Integer.Sparse Key := [(key2903, -2), (key2894, -2), (key2896, -2), (key2746, -2), (key2736, -2), (key2903, -2), (key2647, -2), (key2896, -2), (key2652, -2), (key2736, -2), (key2894, -2), (key2647, -2), (key2826, 1), (key2806, 1), (key2867, 1), (key2783, 1), (key2857, 1), (key2791, 1), (key2723, 1), (key2703, 1), (key2867, 1), (key2629, 1), (key2857, 1), (key2637, 1), (key2723, 1), (key2668, 1), (key2826, 1), (key2613, 1), (key2791, 1), (key2637, 1), (key2703, 1), (key2668, 1), (key2806, 1), (key2613, 1), (key2783, 1), (key2629, 1)]

theorem rawRowCheck10907 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form5 = rawRow10907 := by decide +kernel

def row10907 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

theorem rowCheck10907 : row10907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10907 := by decide +kernel

theorem rowEval10907 (x : Key → ℝ) : Integer.Sparse.eval row10907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck10907, Integer.Sparse.eval_collectBalanced, rawRowCheck10907]

def rawRow10908 : Integer.Sparse Key := [(key2896, -2), (key2903, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2652, -2), (key2746, -2), (key2647, -2), (key2736, -2), (key2894, -2), (key2647, -2), (key2736, -2), (key2857, 1), (key2867, 1), (key2791, 1), (key2826, 1), (key2783, 1), (key2806, 1), (key2857, 1), (key2867, 1), (key2637, 1), (key2723, 1), (key2629, 1), (key2703, 1), (key2791, 1), (key2826, 1), (key2637, 1), (key2723, 1), (key2613, 1), (key2668, 1), (key2783, 1), (key2806, 1), (key2629, 1), (key2703, 1), (key2613, 1), (key2668, 1)]

theorem rawRowCheck10908 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form5 = rawRow10908 := by decide +kernel

def row10908 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

theorem rowCheck10908 : row10908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10908 := by decide +kernel

theorem rowEval10908 (x : Key → ℝ) : Integer.Sparse.eval row10908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10908, Integer.Sparse.eval_collectBalanced, rawRowCheck10908]

def rawRow10909 : Integer.Sparse Key := [(key2903, -2), (key2896, -2), (key2894, -2), (key2903, -2), (key2896, -2), (key2746, -2), (key2652, -2), (key2736, -2), (key2647, -2), (key2894, -2), (key2736, -2), (key2647, -2), (key2867, 1), (key2857, 1), (key2826, 1), (key2791, 1), (key2806, 1), (key2783, 1), (key2867, 1), (key2857, 1), (key2723, 1), (key2637, 1), (key2703, 1), (key2629, 1), (key2826, 1), (key2791, 1), (key2723, 1), (key2637, 1), (key2668, 1), (key2613, 1), (key2806, 1), (key2783, 1), (key2703, 1), (key2629, 1), (key2668, 1), (key2613, 1)]

theorem rawRowCheck10909 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form5 = rawRow10909 := by decide +kernel

def row10909 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

theorem rowCheck10909 : row10909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10909 := by decide +kernel

theorem rowEval10909 (x : Key → ℝ) : Integer.Sparse.eval row10909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck10909, Integer.Sparse.eval_collectBalanced, rawRowCheck10909]

def rawRow10910 : Integer.Sparse Key := [(key2838, -24), (key2582, 6), (key2761, 6), (key2838, 6), (key2872, 6)]

theorem rawRowCheck10910 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form6 = rawRow10910 := by decide +kernel

def row10910 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10910 : row10910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10910 := by decide +kernel

theorem rowEval10910 (x : Key → ℝ) : Integer.Sparse.eval row10910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10910, Integer.Sparse.eval_collectBalanced, rawRowCheck10910]

def rawRow10911 : Integer.Sparse Key := [(key2838, -24), (key2582, 6), (key2761, 6), (key2872, 6), (key2838, 6)]

theorem rawRowCheck10911 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form6 = rawRow10911 := by decide +kernel

def row10911 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10911 : row10911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10911 := by decide +kernel

theorem rowEval10911 (x : Key → ℝ) : Integer.Sparse.eval row10911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10911, Integer.Sparse.eval_collectBalanced, rawRowCheck10911]

def rawRow10912 : Integer.Sparse Key := [(key2838, -24), (key2582, 6), (key2838, 6), (key2761, 6), (key2872, 6)]

theorem rawRowCheck10912 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form6 = rawRow10912 := by decide +kernel

def row10912 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10912 : row10912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10912 := by decide +kernel

theorem rowEval10912 (x : Key → ℝ) : Integer.Sparse.eval row10912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10912, Integer.Sparse.eval_collectBalanced, rawRowCheck10912]

def rawRow10913 : Integer.Sparse Key := [(key2838, -24), (key2582, 6), (key2838, 6), (key2872, 6), (key2761, 6)]

theorem rawRowCheck10913 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form6 = rawRow10913 := by decide +kernel

def row10913 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10913 : row10913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10913 := by decide +kernel

theorem rowEval10913 (x : Key → ℝ) : Integer.Sparse.eval row10913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10913, Integer.Sparse.eval_collectBalanced, rawRowCheck10913]

def rawRow10914 : Integer.Sparse Key := [(key2838, -24), (key2582, 6), (key2872, 6), (key2761, 6), (key2838, 6)]

theorem rawRowCheck10914 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form6 = rawRow10914 := by decide +kernel

def row10914 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10914 : row10914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10914 := by decide +kernel

theorem rowEval10914 (x : Key → ℝ) : Integer.Sparse.eval row10914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10914, Integer.Sparse.eval_collectBalanced, rawRowCheck10914]

def rawRow10915 : Integer.Sparse Key := [(key2838, -24), (key2582, 6), (key2872, 6), (key2838, 6), (key2761, 6)]

theorem rawRowCheck10915 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form6 = rawRow10915 := by decide +kernel

def row10915 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10915 : row10915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10915 := by decide +kernel

theorem rowEval10915 (x : Key → ℝ) : Integer.Sparse.eval row10915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10915, Integer.Sparse.eval_collectBalanced, rawRowCheck10915]

def rawRow10916 : Integer.Sparse Key := [(key2838, -24), (key2761, 6), (key2582, 6), (key2838, 6), (key2872, 6)]

theorem rawRowCheck10916 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form6 = rawRow10916 := by decide +kernel

def row10916 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10916 : row10916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10916 := by decide +kernel

theorem rowEval10916 (x : Key → ℝ) : Integer.Sparse.eval row10916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10916, Integer.Sparse.eval_collectBalanced, rawRowCheck10916]

def rawRow10917 : Integer.Sparse Key := [(key2838, -24), (key2761, 6), (key2582, 6), (key2872, 6), (key2838, 6)]

theorem rawRowCheck10917 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form6 = rawRow10917 := by decide +kernel

def row10917 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10917 : row10917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10917 := by decide +kernel

theorem rowEval10917 (x : Key → ℝ) : Integer.Sparse.eval row10917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10917, Integer.Sparse.eval_collectBalanced, rawRowCheck10917]

def rawRow10918 : Integer.Sparse Key := [(key2838, -24), (key2761, 6), (key2838, 6), (key2582, 6), (key2872, 6)]

theorem rawRowCheck10918 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form6 = rawRow10918 := by decide +kernel

def row10918 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10918 : row10918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10918 := by decide +kernel

theorem rowEval10918 (x : Key → ℝ) : Integer.Sparse.eval row10918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10918, Integer.Sparse.eval_collectBalanced, rawRowCheck10918]

def rawRow10919 : Integer.Sparse Key := [(key2838, -24), (key2761, 6), (key2838, 6), (key2872, 6), (key2582, 6)]

theorem rawRowCheck10919 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form6 = rawRow10919 := by decide +kernel

def row10919 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10919 : row10919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10919 := by decide +kernel

theorem rowEval10919 (x : Key → ℝ) : Integer.Sparse.eval row10919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10919, Integer.Sparse.eval_collectBalanced, rawRowCheck10919]

def rawRow10920 : Integer.Sparse Key := [(key2838, -24), (key2761, 6), (key2872, 6), (key2582, 6), (key2838, 6)]

theorem rawRowCheck10920 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form6 = rawRow10920 := by decide +kernel

def row10920 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10920 : row10920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10920 := by decide +kernel

theorem rowEval10920 (x : Key → ℝ) : Integer.Sparse.eval row10920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10920, Integer.Sparse.eval_collectBalanced, rawRowCheck10920]

def rawRow10921 : Integer.Sparse Key := [(key2838, -24), (key2761, 6), (key2872, 6), (key2838, 6), (key2582, 6)]

theorem rawRowCheck10921 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form6 = rawRow10921 := by decide +kernel

def row10921 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10921 : row10921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10921 := by decide +kernel

theorem rowEval10921 (x : Key → ℝ) : Integer.Sparse.eval row10921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10921, Integer.Sparse.eval_collectBalanced, rawRowCheck10921]

def rawRow10922 : Integer.Sparse Key := [(key2838, -24), (key2838, 6), (key2582, 6), (key2761, 6), (key2872, 6)]

theorem rawRowCheck10922 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form6 = rawRow10922 := by decide +kernel

def row10922 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10922 : row10922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10922 := by decide +kernel

theorem rowEval10922 (x : Key → ℝ) : Integer.Sparse.eval row10922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10922, Integer.Sparse.eval_collectBalanced, rawRowCheck10922]

def rawRow10923 : Integer.Sparse Key := [(key2838, -24), (key2838, 6), (key2582, 6), (key2872, 6), (key2761, 6)]

theorem rawRowCheck10923 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form6 = rawRow10923 := by decide +kernel

def row10923 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10923 : row10923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10923 := by decide +kernel

theorem rowEval10923 (x : Key → ℝ) : Integer.Sparse.eval row10923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10923, Integer.Sparse.eval_collectBalanced, rawRowCheck10923]

def rawRow10924 : Integer.Sparse Key := [(key2838, -24), (key2838, 6), (key2761, 6), (key2582, 6), (key2872, 6)]

theorem rawRowCheck10924 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form6 = rawRow10924 := by decide +kernel

def row10924 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10924 : row10924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10924 := by decide +kernel

theorem rowEval10924 (x : Key → ℝ) : Integer.Sparse.eval row10924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10924, Integer.Sparse.eval_collectBalanced, rawRowCheck10924]

def rawRow10925 : Integer.Sparse Key := [(key2838, -24), (key2838, 6), (key2761, 6), (key2872, 6), (key2582, 6)]

theorem rawRowCheck10925 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form6 = rawRow10925 := by decide +kernel

def row10925 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10925 : row10925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10925 := by decide +kernel

theorem rowEval10925 (x : Key → ℝ) : Integer.Sparse.eval row10925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10925, Integer.Sparse.eval_collectBalanced, rawRowCheck10925]

def rawRow10926 : Integer.Sparse Key := [(key2838, -24), (key2838, 6), (key2872, 6), (key2582, 6), (key2761, 6)]

theorem rawRowCheck10926 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form6 = rawRow10926 := by decide +kernel

def row10926 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10926 : row10926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10926 := by decide +kernel

theorem rowEval10926 (x : Key → ℝ) : Integer.Sparse.eval row10926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10926, Integer.Sparse.eval_collectBalanced, rawRowCheck10926]

def rawRow10927 : Integer.Sparse Key := [(key2838, -24), (key2838, 6), (key2872, 6), (key2761, 6), (key2582, 6)]

theorem rawRowCheck10927 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form6 = rawRow10927 := by decide +kernel

def row10927 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10927 : row10927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10927 := by decide +kernel

theorem rowEval10927 (x : Key → ℝ) : Integer.Sparse.eval row10927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10927, Integer.Sparse.eval_collectBalanced, rawRowCheck10927]

def rawRow10928 : Integer.Sparse Key := [(key2838, -24), (key2872, 6), (key2582, 6), (key2761, 6), (key2838, 6)]

theorem rawRowCheck10928 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form6 = rawRow10928 := by decide +kernel

def row10928 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10928 : row10928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10928 := by decide +kernel

theorem rowEval10928 (x : Key → ℝ) : Integer.Sparse.eval row10928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10928, Integer.Sparse.eval_collectBalanced, rawRowCheck10928]

def rawRow10929 : Integer.Sparse Key := [(key2838, -24), (key2872, 6), (key2582, 6), (key2838, 6), (key2761, 6)]

theorem rawRowCheck10929 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form6 = rawRow10929 := by decide +kernel

def row10929 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10929 : row10929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10929 := by decide +kernel

theorem rowEval10929 (x : Key → ℝ) : Integer.Sparse.eval row10929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10929, Integer.Sparse.eval_collectBalanced, rawRowCheck10929]

def rawRow10930 : Integer.Sparse Key := [(key2838, -24), (key2872, 6), (key2761, 6), (key2582, 6), (key2838, 6)]

theorem rawRowCheck10930 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form6 = rawRow10930 := by decide +kernel

def row10930 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10930 : row10930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10930 := by decide +kernel

theorem rowEval10930 (x : Key → ℝ) : Integer.Sparse.eval row10930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10930, Integer.Sparse.eval_collectBalanced, rawRowCheck10930]

def rawRow10931 : Integer.Sparse Key := [(key2838, -24), (key2872, 6), (key2761, 6), (key2838, 6), (key2582, 6)]

theorem rawRowCheck10931 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form6 = rawRow10931 := by decide +kernel

def row10931 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10931 : row10931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10931 := by decide +kernel

theorem rowEval10931 (x : Key → ℝ) : Integer.Sparse.eval row10931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10931, Integer.Sparse.eval_collectBalanced, rawRowCheck10931]

def rawRow10932 : Integer.Sparse Key := [(key2838, -24), (key2872, 6), (key2838, 6), (key2582, 6), (key2761, 6)]

theorem rawRowCheck10932 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form6 = rawRow10932 := by decide +kernel

def row10932 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10932 : row10932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10932 := by decide +kernel

theorem rowEval10932 (x : Key → ℝ) : Integer.Sparse.eval row10932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10932, Integer.Sparse.eval_collectBalanced, rawRowCheck10932]

def rawRow10933 : Integer.Sparse Key := [(key2838, -24), (key2872, 6), (key2838, 6), (key2761, 6), (key2582, 6)]

theorem rawRowCheck10933 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form6 = rawRow10933 := by decide +kernel

def row10933 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

theorem rowCheck10933 : row10933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10933 := by decide +kernel

theorem rowEval10933 (x : Key → ℝ) : Integer.Sparse.eval row10933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10933, Integer.Sparse.eval_collectBalanced, rawRowCheck10933]

def rawRow10934 : Integer.Sparse Key := [(key2872, -24), (key2582, 6), (key2761, 6), (key2838, 6), (key2838, 6)]

theorem rawRowCheck10934 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form6 = rawRow10934 := by decide +kernel

def row10934 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

theorem rowCheck10934 : row10934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10934 := by decide +kernel

theorem rowEval10934 (x : Key → ℝ) : Integer.Sparse.eval row10934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10934, Integer.Sparse.eval_collectBalanced, rawRowCheck10934]

def rawRow10935 : Integer.Sparse Key := [(key2872, -24), (key2582, 6), (key2838, 6), (key2761, 6), (key2838, 6)]

theorem rawRowCheck10935 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form6 = rawRow10935 := by decide +kernel

def row10935 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

theorem rowCheck10935 : row10935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10935 := by decide +kernel

theorem rowEval10935 (x : Key → ℝ) : Integer.Sparse.eval row10935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10935, Integer.Sparse.eval_collectBalanced, rawRowCheck10935]

def rawRow10936 : Integer.Sparse Key := [(key2872, -24), (key2582, 6), (key2838, 6), (key2838, 6), (key2761, 6)]

theorem rawRowCheck10936 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form6 = rawRow10936 := by decide +kernel

def row10936 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

theorem rowCheck10936 : row10936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10936 := by decide +kernel

theorem rowEval10936 (x : Key → ℝ) : Integer.Sparse.eval row10936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10936, Integer.Sparse.eval_collectBalanced, rawRowCheck10936]

def rawRow10937 : Integer.Sparse Key := [(key2872, -24), (key2761, 6), (key2582, 6), (key2838, 6), (key2838, 6)]

theorem rawRowCheck10937 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form6 = rawRow10937 := by decide +kernel

def row10937 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

theorem rowCheck10937 : row10937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10937 := by decide +kernel

theorem rowEval10937 (x : Key → ℝ) : Integer.Sparse.eval row10937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10937, Integer.Sparse.eval_collectBalanced, rawRowCheck10937]

def rawRow10938 : Integer.Sparse Key := [(key2872, -24), (key2761, 6), (key2838, 6), (key2582, 6), (key2838, 6)]

theorem rawRowCheck10938 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form6 = rawRow10938 := by decide +kernel

def row10938 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

theorem rowCheck10938 : row10938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10938 := by decide +kernel

theorem rowEval10938 (x : Key → ℝ) : Integer.Sparse.eval row10938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10938, Integer.Sparse.eval_collectBalanced, rawRowCheck10938]

def rawRow10939 : Integer.Sparse Key := [(key2872, -24), (key2761, 6), (key2838, 6), (key2838, 6), (key2582, 6)]

theorem rawRowCheck10939 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form6 = rawRow10939 := by decide +kernel

def row10939 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

theorem rowCheck10939 : row10939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10939 := by decide +kernel

theorem rowEval10939 (x : Key → ℝ) : Integer.Sparse.eval row10939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10939, Integer.Sparse.eval_collectBalanced, rawRowCheck10939]

def rawRow10940 : Integer.Sparse Key := [(key2872, -24), (key2838, 6), (key2582, 6), (key2761, 6), (key2838, 6)]

theorem rawRowCheck10940 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form6 = rawRow10940 := by decide +kernel

def row10940 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

theorem rowCheck10940 : row10940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10940 := by decide +kernel

theorem rowEval10940 (x : Key → ℝ) : Integer.Sparse.eval row10940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10940, Integer.Sparse.eval_collectBalanced, rawRowCheck10940]

def rawRow10941 : Integer.Sparse Key := [(key2872, -24), (key2838, 6), (key2582, 6), (key2838, 6), (key2761, 6)]

theorem rawRowCheck10941 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form6 = rawRow10941 := by decide +kernel

def row10941 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

theorem rowCheck10941 : row10941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10941 := by decide +kernel

theorem rowEval10941 (x : Key → ℝ) : Integer.Sparse.eval row10941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10941, Integer.Sparse.eval_collectBalanced, rawRowCheck10941]

def rawRow10942 : Integer.Sparse Key := [(key2872, -24), (key2838, 6), (key2761, 6), (key2582, 6), (key2838, 6)]

theorem rawRowCheck10942 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form6 = rawRow10942 := by decide +kernel

def row10942 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

theorem rowCheck10942 : row10942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10942 := by decide +kernel

theorem rowEval10942 (x : Key → ℝ) : Integer.Sparse.eval row10942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10942, Integer.Sparse.eval_collectBalanced, rawRowCheck10942]

def rawRow10943 : Integer.Sparse Key := [(key2872, -24), (key2838, 6), (key2761, 6), (key2838, 6), (key2582, 6)]

theorem rawRowCheck10943 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form6 = rawRow10943 := by decide +kernel

def row10943 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

theorem rowCheck10943 : row10943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10943 := by decide +kernel

theorem rowEval10943 (x : Key → ℝ) : Integer.Sparse.eval row10943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10943, Integer.Sparse.eval_collectBalanced, rawRowCheck10943]

def rawRow10944 : Integer.Sparse Key := [(key2872, -24), (key2838, 6), (key2838, 6), (key2582, 6), (key2761, 6)]

theorem rawRowCheck10944 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form6 = rawRow10944 := by decide +kernel

def row10944 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

theorem rowCheck10944 : row10944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10944 := by decide +kernel

theorem rowEval10944 (x : Key → ℝ) : Integer.Sparse.eval row10944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10944, Integer.Sparse.eval_collectBalanced, rawRowCheck10944]

def rawRow10945 : Integer.Sparse Key := [(key2872, -24), (key2838, 6), (key2838, 6), (key2761, 6), (key2582, 6)]

theorem rawRowCheck10945 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form6 = rawRow10945 := by decide +kernel

def row10945 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

theorem rowCheck10945 : row10945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10945 := by decide +kernel

theorem rowEval10945 (x : Key → ℝ) : Integer.Sparse.eval row10945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10945, Integer.Sparse.eval_collectBalanced, rawRowCheck10945]

def rawRow10946 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2852, -2), (key2894, -2), (key2857, -2), (key2896, -2), (key2826, -2), (key2867, -2), (key2903, -2), (key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2852, 2), (key2973, 2), (key2857, 2), (key2975, 2), (key2723, 2), (key2867, 2), (key2982, 2)]

theorem rawRowCheck10946 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form7 = rawRow10946 := by decide +kernel

def row10946 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10946 : row10946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10946 := by decide +kernel

theorem rowEval10946 (x : Key → ℝ) : Integer.Sparse.eval row10946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10946, Integer.Sparse.eval_collectBalanced, rawRowCheck10946]

def rawRow10947 : Integer.Sparse Key := [(key2783, -2), (key2779, -2), (key2791, -2), (key2806, -2), (key2802, -2), (key2894, -2), (key2852, -2), (key2896, -2), (key2857, -2), (key2826, -2), (key2903, -2), (key2867, -2), (key2629, 2), (key2625, 2), (key2637, 2), (key2703, 2), (key2699, 2), (key2973, 2), (key2852, 2), (key2975, 2), (key2857, 2), (key2723, 2), (key2982, 2), (key2867, 2)]

theorem rawRowCheck10947 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form7 = rawRow10947 := by decide +kernel

def row10947 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10947 : row10947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10947 := by decide +kernel

theorem rowEval10947 (x : Key → ℝ) : Integer.Sparse.eval row10947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10947, Integer.Sparse.eval_collectBalanced, rawRowCheck10947]

def rawRow10948 : Integer.Sparse Key := [(key2779, -2), (key2791, -2), (key2783, -2), (key2852, -2), (key2857, -2), (key2802, -2), (key2896, -2), (key2806, -2), (key2894, -2), (key2867, -2), (key2826, -2), (key2903, -2), (key2625, 2), (key2637, 2), (key2629, 2), (key2852, 2), (key2857, 2), (key2699, 2), (key2975, 2), (key2703, 2), (key2973, 2), (key2867, 2), (key2723, 2), (key2982, 2)]

theorem rawRowCheck10948 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form7 = rawRow10948 := by decide +kernel

def row10948 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10948 : row10948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10948 := by decide +kernel

theorem rowEval10948 (x : Key → ℝ) : Integer.Sparse.eval row10948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10948, Integer.Sparse.eval_collectBalanced, rawRowCheck10948]

def rawRow10949 : Integer.Sparse Key := [(key2791, -2), (key2779, -2), (key2783, -2), (key2857, -2), (key2852, -2), (key2896, -2), (key2802, -2), (key2894, -2), (key2806, -2), (key2867, -2), (key2903, -2), (key2826, -2), (key2637, 2), (key2625, 2), (key2629, 2), (key2857, 2), (key2852, 2), (key2975, 2), (key2699, 2), (key2973, 2), (key2703, 2), (key2867, 2), (key2982, 2), (key2723, 2)]

theorem rawRowCheck10949 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form7 = rawRow10949 := by decide +kernel

def row10949 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10949 : row10949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10949 := by decide +kernel

theorem rowEval10949 (x : Key → ℝ) : Integer.Sparse.eval row10949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10949, Integer.Sparse.eval_collectBalanced, rawRowCheck10949]

def rawRow10950 : Integer.Sparse Key := [(key2783, -2), (key2791, -2), (key2779, -2), (key2894, -2), (key2896, -2), (key2806, -2), (key2857, -2), (key2802, -2), (key2852, -2), (key2903, -2), (key2826, -2), (key2867, -2), (key2629, 2), (key2637, 2), (key2625, 2), (key2973, 2), (key2975, 2), (key2703, 2), (key2857, 2), (key2699, 2), (key2852, 2), (key2982, 2), (key2723, 2), (key2867, 2)]

theorem rawRowCheck10950 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form7 = rawRow10950 := by decide +kernel

def row10950 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10950 : row10950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10950 := by decide +kernel

theorem rowEval10950 (x : Key → ℝ) : Integer.Sparse.eval row10950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10950, Integer.Sparse.eval_collectBalanced, rawRowCheck10950]

def rawRow10951 : Integer.Sparse Key := [(key2791, -2), (key2783, -2), (key2779, -2), (key2896, -2), (key2894, -2), (key2857, -2), (key2806, -2), (key2852, -2), (key2802, -2), (key2903, -2), (key2867, -2), (key2826, -2), (key2637, 2), (key2629, 2), (key2625, 2), (key2975, 2), (key2973, 2), (key2857, 2), (key2703, 2), (key2852, 2), (key2699, 2), (key2982, 2), (key2867, 2), (key2723, 2)]

theorem rawRowCheck10951 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form7 = rawRow10951 := by decide +kernel

def row10951 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10951 : row10951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10951 := by decide +kernel

theorem rowEval10951 (x : Key → ℝ) : Integer.Sparse.eval row10951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10951, Integer.Sparse.eval_collectBalanced, rawRowCheck10951]

def rawRow10952 : Integer.Sparse Key := [(key2802, -2), (key2806, -2), (key2826, -2), (key2779, -2), (key2783, -2), (key2852, -2), (key2894, -2), (key2867, -2), (key2903, -2), (key2791, -2), (key2857, -2), (key2896, -2), (key2699, 2), (key2703, 2), (key2723, 2), (key2625, 2), (key2629, 2), (key2852, 2), (key2973, 2), (key2867, 2), (key2982, 2), (key2637, 2), (key2857, 2), (key2975, 2)]

theorem rawRowCheck10952 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form7 = rawRow10952 := by decide +kernel

def row10952 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10952 : row10952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10952 := by decide +kernel

theorem rowEval10952 (x : Key → ℝ) : Integer.Sparse.eval row10952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10952, Integer.Sparse.eval_collectBalanced, rawRowCheck10952]

def rawRow10953 : Integer.Sparse Key := [(key2806, -2), (key2802, -2), (key2826, -2), (key2783, -2), (key2779, -2), (key2894, -2), (key2852, -2), (key2903, -2), (key2867, -2), (key2791, -2), (key2896, -2), (key2857, -2), (key2703, 2), (key2699, 2), (key2723, 2), (key2629, 2), (key2625, 2), (key2973, 2), (key2852, 2), (key2982, 2), (key2867, 2), (key2637, 2), (key2975, 2), (key2857, 2)]

theorem rawRowCheck10953 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form7 = rawRow10953 := by decide +kernel

def row10953 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10953 : row10953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10953 := by decide +kernel

theorem rowEval10953 (x : Key → ℝ) : Integer.Sparse.eval row10953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10953, Integer.Sparse.eval_collectBalanced, rawRowCheck10953]

def rawRow10954 : Integer.Sparse Key := [(key2802, -2), (key2826, -2), (key2806, -2), (key2852, -2), (key2867, -2), (key2779, -2), (key2903, -2), (key2783, -2), (key2894, -2), (key2857, -2), (key2791, -2), (key2896, -2), (key2699, 2), (key2723, 2), (key2703, 2), (key2852, 2), (key2867, 2), (key2625, 2), (key2982, 2), (key2629, 2), (key2973, 2), (key2857, 2), (key2637, 2), (key2975, 2)]

theorem rawRowCheck10954 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form7 = rawRow10954 := by decide +kernel

def row10954 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10954 : row10954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10954 := by decide +kernel

theorem rowEval10954 (x : Key → ℝ) : Integer.Sparse.eval row10954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10954, Integer.Sparse.eval_collectBalanced, rawRowCheck10954]

def rawRow10955 : Integer.Sparse Key := [(key2826, -2), (key2802, -2), (key2806, -2), (key2867, -2), (key2852, -2), (key2903, -2), (key2779, -2), (key2894, -2), (key2783, -2), (key2857, -2), (key2896, -2), (key2791, -2), (key2723, 2), (key2699, 2), (key2703, 2), (key2867, 2), (key2852, 2), (key2982, 2), (key2625, 2), (key2973, 2), (key2629, 2), (key2857, 2), (key2975, 2), (key2637, 2)]

theorem rawRowCheck10955 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form7 = rawRow10955 := by decide +kernel

def row10955 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10955 : row10955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10955 := by decide +kernel

theorem rowEval10955 (x : Key → ℝ) : Integer.Sparse.eval row10955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck10955, Integer.Sparse.eval_collectBalanced, rawRowCheck10955]

def rawRow10956 : Integer.Sparse Key := [(key2806, -2), (key2826, -2), (key2802, -2), (key2894, -2), (key2903, -2), (key2783, -2), (key2867, -2), (key2779, -2), (key2852, -2), (key2896, -2), (key2791, -2), (key2857, -2), (key2703, 2), (key2723, 2), (key2699, 2), (key2973, 2), (key2982, 2), (key2629, 2), (key2867, 2), (key2625, 2), (key2852, 2), (key2975, 2), (key2637, 2), (key2857, 2)]

theorem rawRowCheck10956 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form7 = rawRow10956 := by decide +kernel

def row10956 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10956 : row10956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10956 := by decide +kernel

theorem rowEval10956 (x : Key → ℝ) : Integer.Sparse.eval row10956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10956, Integer.Sparse.eval_collectBalanced, rawRowCheck10956]

def rawRow10957 : Integer.Sparse Key := [(key2826, -2), (key2806, -2), (key2802, -2), (key2903, -2), (key2894, -2), (key2867, -2), (key2783, -2), (key2852, -2), (key2779, -2), (key2896, -2), (key2857, -2), (key2791, -2), (key2723, 2), (key2703, 2), (key2699, 2), (key2982, 2), (key2973, 2), (key2867, 2), (key2629, 2), (key2852, 2), (key2625, 2), (key2975, 2), (key2857, 2), (key2637, 2)]

theorem rawRowCheck10957 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form7 = rawRow10957 := by decide +kernel

def row10957 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10957 : row10957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10957 := by decide +kernel

theorem rowEval10957 (x : Key → ℝ) : Integer.Sparse.eval row10957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck10957, Integer.Sparse.eval_collectBalanced, rawRowCheck10957]

def rawRow10958 : Integer.Sparse Key := [(key2852, -2), (key2857, -2), (key2867, -2), (key2779, -2), (key2791, -2), (key2802, -2), (key2896, -2), (key2826, -2), (key2903, -2), (key2783, -2), (key2806, -2), (key2894, -2), (key2852, 2), (key2857, 2), (key2867, 2), (key2625, 2), (key2637, 2), (key2699, 2), (key2975, 2), (key2723, 2), (key2982, 2), (key2629, 2), (key2703, 2), (key2973, 2)]

theorem rawRowCheck10958 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form7 = rawRow10958 := by decide +kernel

def row10958 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10958 : row10958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10958 := by decide +kernel

theorem rowEval10958 (x : Key → ℝ) : Integer.Sparse.eval row10958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10958, Integer.Sparse.eval_collectBalanced, rawRowCheck10958]

def rawRow10959 : Integer.Sparse Key := [(key2857, -2), (key2852, -2), (key2867, -2), (key2791, -2), (key2779, -2), (key2896, -2), (key2802, -2), (key2903, -2), (key2826, -2), (key2783, -2), (key2894, -2), (key2806, -2), (key2857, 2), (key2852, 2), (key2867, 2), (key2637, 2), (key2625, 2), (key2975, 2), (key2699, 2), (key2982, 2), (key2723, 2), (key2629, 2), (key2973, 2), (key2703, 2)]

theorem rawRowCheck10959 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form7 = rawRow10959 := by decide +kernel

def row10959 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10959 : row10959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10959 := by decide +kernel

theorem rowEval10959 (x : Key → ℝ) : Integer.Sparse.eval row10959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10959, Integer.Sparse.eval_collectBalanced, rawRowCheck10959]

def rawRow10960 : Integer.Sparse Key := [(key2852, -2), (key2867, -2), (key2857, -2), (key2802, -2), (key2826, -2), (key2779, -2), (key2903, -2), (key2791, -2), (key2896, -2), (key2806, -2), (key2783, -2), (key2894, -2), (key2852, 2), (key2867, 2), (key2857, 2), (key2699, 2), (key2723, 2), (key2625, 2), (key2982, 2), (key2637, 2), (key2975, 2), (key2703, 2), (key2629, 2), (key2973, 2)]

theorem rawRowCheck10960 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form7 = rawRow10960 := by decide +kernel

def row10960 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10960 : row10960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10960 := by decide +kernel

theorem rowEval10960 (x : Key → ℝ) : Integer.Sparse.eval row10960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10960, Integer.Sparse.eval_collectBalanced, rawRowCheck10960]

def rawRow10961 : Integer.Sparse Key := [(key2867, -2), (key2852, -2), (key2857, -2), (key2826, -2), (key2802, -2), (key2903, -2), (key2779, -2), (key2896, -2), (key2791, -2), (key2806, -2), (key2894, -2), (key2783, -2), (key2867, 2), (key2852, 2), (key2857, 2), (key2723, 2), (key2699, 2), (key2982, 2), (key2625, 2), (key2975, 2), (key2637, 2), (key2703, 2), (key2973, 2), (key2629, 2)]

theorem rawRowCheck10961 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form7 = rawRow10961 := by decide +kernel

def row10961 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10961 : row10961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10961 := by decide +kernel

theorem rowEval10961 (x : Key → ℝ) : Integer.Sparse.eval row10961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck10961, Integer.Sparse.eval_collectBalanced, rawRowCheck10961]

def rawRow10962 : Integer.Sparse Key := [(key2857, -2), (key2867, -2), (key2852, -2), (key2896, -2), (key2903, -2), (key2791, -2), (key2826, -2), (key2779, -2), (key2802, -2), (key2894, -2), (key2783, -2), (key2806, -2), (key2857, 2), (key2867, 2), (key2852, 2), (key2975, 2), (key2982, 2), (key2637, 2), (key2723, 2), (key2625, 2), (key2699, 2), (key2973, 2), (key2629, 2), (key2703, 2)]

theorem rawRowCheck10962 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form7 = rawRow10962 := by decide +kernel

def row10962 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10962 : row10962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10962 := by decide +kernel

theorem rowEval10962 (x : Key → ℝ) : Integer.Sparse.eval row10962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10962, Integer.Sparse.eval_collectBalanced, rawRowCheck10962]

def rawRow10963 : Integer.Sparse Key := [(key2867, -2), (key2857, -2), (key2852, -2), (key2903, -2), (key2896, -2), (key2826, -2), (key2791, -2), (key2802, -2), (key2779, -2), (key2894, -2), (key2806, -2), (key2783, -2), (key2867, 2), (key2857, 2), (key2852, 2), (key2982, 2), (key2975, 2), (key2723, 2), (key2637, 2), (key2699, 2), (key2625, 2), (key2973, 2), (key2703, 2), (key2629, 2)]

theorem rawRowCheck10963 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form7 = rawRow10963 := by decide +kernel

def row10963 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10963 : row10963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10963 := by decide +kernel

theorem rowEval10963 (x : Key → ℝ) : Integer.Sparse.eval row10963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck10963, Integer.Sparse.eval_collectBalanced, rawRowCheck10963]

def rawRow10964 : Integer.Sparse Key := [(key2894, -2), (key2896, -2), (key2903, -2), (key2783, -2), (key2791, -2), (key2806, -2), (key2857, -2), (key2826, -2), (key2867, -2), (key2779, -2), (key2802, -2), (key2852, -2), (key2973, 2), (key2975, 2), (key2982, 2), (key2629, 2), (key2637, 2), (key2703, 2), (key2857, 2), (key2723, 2), (key2867, 2), (key2625, 2), (key2699, 2), (key2852, 2)]

theorem rawRowCheck10964 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form7 = rawRow10964 := by decide +kernel

def row10964 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10964 : row10964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10964 := by decide +kernel

theorem rowEval10964 (x : Key → ℝ) : Integer.Sparse.eval row10964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10964, Integer.Sparse.eval_collectBalanced, rawRowCheck10964]

def rawRow10965 : Integer.Sparse Key := [(key2896, -2), (key2894, -2), (key2903, -2), (key2791, -2), (key2783, -2), (key2857, -2), (key2806, -2), (key2867, -2), (key2826, -2), (key2779, -2), (key2852, -2), (key2802, -2), (key2975, 2), (key2973, 2), (key2982, 2), (key2637, 2), (key2629, 2), (key2857, 2), (key2703, 2), (key2867, 2), (key2723, 2), (key2625, 2), (key2852, 2), (key2699, 2)]

theorem rawRowCheck10965 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form7 = rawRow10965 := by decide +kernel

def row10965 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10965 : row10965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10965 := by decide +kernel

theorem rowEval10965 (x : Key → ℝ) : Integer.Sparse.eval row10965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10965, Integer.Sparse.eval_collectBalanced, rawRowCheck10965]

def rawRow10966 : Integer.Sparse Key := [(key2894, -2), (key2903, -2), (key2896, -2), (key2806, -2), (key2826, -2), (key2783, -2), (key2867, -2), (key2791, -2), (key2857, -2), (key2802, -2), (key2779, -2), (key2852, -2), (key2973, 2), (key2982, 2), (key2975, 2), (key2703, 2), (key2723, 2), (key2629, 2), (key2867, 2), (key2637, 2), (key2857, 2), (key2699, 2), (key2625, 2), (key2852, 2)]

theorem rawRowCheck10966 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form7 = rawRow10966 := by decide +kernel

def row10966 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10966 : row10966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10966 := by decide +kernel

theorem rowEval10966 (x : Key → ℝ) : Integer.Sparse.eval row10966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10966, Integer.Sparse.eval_collectBalanced, rawRowCheck10966]

def rawRow10967 : Integer.Sparse Key := [(key2903, -2), (key2894, -2), (key2896, -2), (key2826, -2), (key2806, -2), (key2867, -2), (key2783, -2), (key2857, -2), (key2791, -2), (key2802, -2), (key2852, -2), (key2779, -2), (key2982, 2), (key2973, 2), (key2975, 2), (key2723, 2), (key2703, 2), (key2867, 2), (key2629, 2), (key2857, 2), (key2637, 2), (key2699, 2), (key2852, 2), (key2625, 2)]

theorem rawRowCheck10967 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form7 = rawRow10967 := by decide +kernel

def row10967 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10967 : row10967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10967 := by decide +kernel

theorem rowEval10967 (x : Key → ℝ) : Integer.Sparse.eval row10967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck10967, Integer.Sparse.eval_collectBalanced, rawRowCheck10967]

def rawRow10968 : Integer.Sparse Key := [(key2896, -2), (key2903, -2), (key2894, -2), (key2857, -2), (key2867, -2), (key2791, -2), (key2826, -2), (key2783, -2), (key2806, -2), (key2852, -2), (key2779, -2), (key2802, -2), (key2975, 2), (key2982, 2), (key2973, 2), (key2857, 2), (key2867, 2), (key2637, 2), (key2723, 2), (key2629, 2), (key2703, 2), (key2852, 2), (key2625, 2), (key2699, 2)]

theorem rawRowCheck10968 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form7 = rawRow10968 := by decide +kernel

def row10968 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10968 : row10968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10968 := by decide +kernel

theorem rowEval10968 (x : Key → ℝ) : Integer.Sparse.eval row10968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10968, Integer.Sparse.eval_collectBalanced, rawRowCheck10968]

def rawRow10969 : Integer.Sparse Key := [(key2903, -2), (key2896, -2), (key2894, -2), (key2867, -2), (key2857, -2), (key2826, -2), (key2791, -2), (key2806, -2), (key2783, -2), (key2852, -2), (key2802, -2), (key2779, -2), (key2982, 2), (key2975, 2), (key2973, 2), (key2867, 2), (key2857, 2), (key2723, 2), (key2637, 2), (key2703, 2), (key2629, 2), (key2852, 2), (key2699, 2), (key2625, 2)]

theorem rawRowCheck10969 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form7 = rawRow10969 := by decide +kernel

def row10969 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

theorem rowCheck10969 : row10969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10969 := by decide +kernel

theorem rowEval10969 (x : Key → ℝ) : Integer.Sparse.eval row10969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck10969, Integer.Sparse.eval_collectBalanced, rawRowCheck10969]

def rawRow10970 : Integer.Sparse Key := [(key2937, -2), (key2937, -2), (key2942, -2), (key2949, -2), (key2949, -2), (key2973, -2), (key2973, -2), (key2975, -2), (key2975, -2), (key2959, -2), (key2982, -2), (key2982, -2), (key2647, 2), (key2647, 2), (key2652, 2), (key2736, 2), (key2736, 2), (key2894, 2), (key2894, 2), (key2896, 2), (key2896, 2), (key2746, 2), (key2903, 2), (key2903, 2)]

theorem rawRowCheck10970 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form7 = rawRow10970 := by decide +kernel

def row10970 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

theorem rowCheck10970 : row10970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10970 := by decide +kernel

theorem rowEval10970 (x : Key → ℝ) : Integer.Sparse.eval row10970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10970, Integer.Sparse.eval_collectBalanced, rawRowCheck10970]

def rawRow10971 : Integer.Sparse Key := [(key2937, -2), (key2942, -2), (key2937, -2), (key2973, -2), (key2975, -2), (key2949, -2), (key2975, -2), (key2949, -2), (key2973, -2), (key2982, -2), (key2959, -2), (key2982, -2), (key2647, 2), (key2652, 2), (key2647, 2), (key2894, 2), (key2896, 2), (key2736, 2), (key2896, 2), (key2736, 2), (key2894, 2), (key2903, 2), (key2746, 2), (key2903, 2)]

theorem rawRowCheck10971 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form7 = rawRow10971 := by decide +kernel

def row10971 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

theorem rowCheck10971 : row10971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10971 := by decide +kernel

theorem rowEval10971 (x : Key → ℝ) : Integer.Sparse.eval row10971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10971, Integer.Sparse.eval_collectBalanced, rawRowCheck10971]

def rawRow10972 : Integer.Sparse Key := [(key2942, -2), (key2937, -2), (key2937, -2), (key2975, -2), (key2973, -2), (key2975, -2), (key2949, -2), (key2973, -2), (key2949, -2), (key2982, -2), (key2982, -2), (key2959, -2), (key2652, 2), (key2647, 2), (key2647, 2), (key2896, 2), (key2894, 2), (key2896, 2), (key2736, 2), (key2894, 2), (key2736, 2), (key2903, 2), (key2903, 2), (key2746, 2)]

theorem rawRowCheck10972 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form7 = rawRow10972 := by decide +kernel

def row10972 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

theorem rowCheck10972 : row10972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10972 := by decide +kernel

theorem rowEval10972 (x : Key → ℝ) : Integer.Sparse.eval row10972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10972, Integer.Sparse.eval_collectBalanced, rawRowCheck10972]

def rawRow10973 : Integer.Sparse Key := [(key2949, -2), (key2949, -2), (key2959, -2), (key2937, -2), (key2937, -2), (key2973, -2), (key2973, -2), (key2982, -2), (key2982, -2), (key2942, -2), (key2975, -2), (key2975, -2), (key2736, 2), (key2736, 2), (key2746, 2), (key2647, 2), (key2647, 2), (key2894, 2), (key2894, 2), (key2903, 2), (key2903, 2), (key2652, 2), (key2896, 2), (key2896, 2)]

theorem rawRowCheck10973 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form7 = rawRow10973 := by decide +kernel

def row10973 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

theorem rowCheck10973 : row10973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10973 := by decide +kernel

theorem rowEval10973 (x : Key → ℝ) : Integer.Sparse.eval row10973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10973, Integer.Sparse.eval_collectBalanced, rawRowCheck10973]

def rawRow10974 : Integer.Sparse Key := [(key2949, -2), (key2959, -2), (key2949, -2), (key2973, -2), (key2982, -2), (key2937, -2), (key2982, -2), (key2937, -2), (key2973, -2), (key2975, -2), (key2942, -2), (key2975, -2), (key2736, 2), (key2746, 2), (key2736, 2), (key2894, 2), (key2903, 2), (key2647, 2), (key2903, 2), (key2647, 2), (key2894, 2), (key2896, 2), (key2652, 2), (key2896, 2)]

theorem rawRowCheck10974 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form7 = rawRow10974 := by decide +kernel

def row10974 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

theorem rowCheck10974 : row10974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10974 := by decide +kernel

theorem rowEval10974 (x : Key → ℝ) : Integer.Sparse.eval row10974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10974, Integer.Sparse.eval_collectBalanced, rawRowCheck10974]

def rawRow10975 : Integer.Sparse Key := [(key2959, -2), (key2949, -2), (key2949, -2), (key2982, -2), (key2973, -2), (key2982, -2), (key2937, -2), (key2973, -2), (key2937, -2), (key2975, -2), (key2975, -2), (key2942, -2), (key2746, 2), (key2736, 2), (key2736, 2), (key2903, 2), (key2894, 2), (key2903, 2), (key2647, 2), (key2894, 2), (key2647, 2), (key2896, 2), (key2896, 2), (key2652, 2)]

theorem rawRowCheck10975 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form7 = rawRow10975 := by decide +kernel

def row10975 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

theorem rowCheck10975 : row10975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10975 := by decide +kernel

theorem rowEval10975 (x : Key → ℝ) : Integer.Sparse.eval row10975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck10975, Integer.Sparse.eval_collectBalanced, rawRowCheck10975]

def rawRow10976 : Integer.Sparse Key := [(key2973, -2), (key2975, -2), (key2982, -2), (key2937, -2), (key2942, -2), (key2949, -2), (key2975, -2), (key2959, -2), (key2982, -2), (key2937, -2), (key2949, -2), (key2973, -2), (key2894, 2), (key2896, 2), (key2903, 2), (key2647, 2), (key2652, 2), (key2736, 2), (key2896, 2), (key2746, 2), (key2903, 2), (key2647, 2), (key2736, 2), (key2894, 2)]

theorem rawRowCheck10976 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form7 = rawRow10976 := by decide +kernel

def row10976 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

theorem rowCheck10976 : row10976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10976 := by decide +kernel

theorem rowEval10976 (x : Key → ℝ) : Integer.Sparse.eval row10976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10976, Integer.Sparse.eval_collectBalanced, rawRowCheck10976]

def rawRow10977 : Integer.Sparse Key := [(key2975, -2), (key2973, -2), (key2982, -2), (key2942, -2), (key2937, -2), (key2975, -2), (key2949, -2), (key2982, -2), (key2959, -2), (key2937, -2), (key2973, -2), (key2949, -2), (key2896, 2), (key2894, 2), (key2903, 2), (key2652, 2), (key2647, 2), (key2896, 2), (key2736, 2), (key2903, 2), (key2746, 2), (key2647, 2), (key2894, 2), (key2736, 2)]

theorem rawRowCheck10977 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form7 = rawRow10977 := by decide +kernel

def row10977 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

theorem rowCheck10977 : row10977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10977 := by decide +kernel

theorem rowEval10977 (x : Key → ℝ) : Integer.Sparse.eval row10977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10977, Integer.Sparse.eval_collectBalanced, rawRowCheck10977]

def rawRow10978 : Integer.Sparse Key := [(key2973, -2), (key2982, -2), (key2975, -2), (key2949, -2), (key2959, -2), (key2937, -2), (key2982, -2), (key2942, -2), (key2975, -2), (key2949, -2), (key2937, -2), (key2973, -2), (key2894, 2), (key2903, 2), (key2896, 2), (key2736, 2), (key2746, 2), (key2647, 2), (key2903, 2), (key2652, 2), (key2896, 2), (key2736, 2), (key2647, 2), (key2894, 2)]

theorem rawRowCheck10978 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form7 = rawRow10978 := by decide +kernel

def row10978 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

theorem rowCheck10978 : row10978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10978 := by decide +kernel

theorem rowEval10978 (x : Key → ℝ) : Integer.Sparse.eval row10978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10978, Integer.Sparse.eval_collectBalanced, rawRowCheck10978]

def rawRow10979 : Integer.Sparse Key := [(key2982, -2), (key2973, -2), (key2975, -2), (key2959, -2), (key2949, -2), (key2982, -2), (key2937, -2), (key2975, -2), (key2942, -2), (key2949, -2), (key2973, -2), (key2937, -2), (key2903, 2), (key2894, 2), (key2896, 2), (key2746, 2), (key2736, 2), (key2903, 2), (key2647, 2), (key2896, 2), (key2652, 2), (key2736, 2), (key2894, 2), (key2647, 2)]

theorem rawRowCheck10979 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form7 = rawRow10979 := by decide +kernel

def row10979 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

theorem rowCheck10979 : row10979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10979 := by decide +kernel

theorem rowEval10979 (x : Key → ℝ) : Integer.Sparse.eval row10979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck10979, Integer.Sparse.eval_collectBalanced, rawRowCheck10979]

def rawRow10980 : Integer.Sparse Key := [(key2975, -2), (key2982, -2), (key2973, -2), (key2975, -2), (key2982, -2), (key2942, -2), (key2959, -2), (key2937, -2), (key2949, -2), (key2973, -2), (key2937, -2), (key2949, -2), (key2896, 2), (key2903, 2), (key2894, 2), (key2896, 2), (key2903, 2), (key2652, 2), (key2746, 2), (key2647, 2), (key2736, 2), (key2894, 2), (key2647, 2), (key2736, 2)]

theorem rawRowCheck10980 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form7 = rawRow10980 := by decide +kernel

def row10980 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

theorem rowCheck10980 : row10980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10980 := by decide +kernel

theorem rowEval10980 (x : Key → ℝ) : Integer.Sparse.eval row10980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10980, Integer.Sparse.eval_collectBalanced, rawRowCheck10980]

def rawRow10981 : Integer.Sparse Key := [(key2982, -2), (key2975, -2), (key2973, -2), (key2982, -2), (key2975, -2), (key2959, -2), (key2942, -2), (key2949, -2), (key2937, -2), (key2973, -2), (key2949, -2), (key2937, -2), (key2903, 2), (key2896, 2), (key2894, 2), (key2903, 2), (key2896, 2), (key2746, 2), (key2652, 2), (key2736, 2), (key2647, 2), (key2894, 2), (key2736, 2), (key2647, 2)]

theorem rawRowCheck10981 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form7 = rawRow10981 := by decide +kernel

def row10981 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

theorem rowCheck10981 : row10981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10981 := by decide +kernel

theorem rowEval10981 (x : Key → ℝ) : Integer.Sparse.eval row10981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck10981, Integer.Sparse.eval_collectBalanced, rawRowCheck10981]

def rawRow10982 : Integer.Sparse Key := [(key1312, -2), (key1317, -2), (key1325, -2), (key1420, -2), (key1425, -2), (key1618, -2), (key1814, -2), (key1623, -2), (key1816, -2), (key1443, -2), (key1632, -2), (key1824, -2), (key1292, 1), (key1297, 1), (key1312, 1), (key1338, 1), (key1325, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1542, 1), (key1773, 1), (key1555, 1), (key1779, 1), (key1420, 1), (key1456, 1), (key1569, 1), (key1789, 1), (key1658, 1), (key1816, 1), (key1443, 1), (key1465, 1), (key1592, 1), (key1797, 1), (key1666, 1), (key1824, 1)]

theorem rawRowCheck10982 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form8 = rawRow10982 := by decide +kernel

def row10982 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10982 : row10982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10982 := by decide +kernel

theorem rowEval10982 (x : Key → ℝ) : Integer.Sparse.eval row10982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10982, Integer.Sparse.eval_collectBalanced, rawRowCheck10982]

def rawRow10983 : Integer.Sparse Key := [(key1317, -2), (key1312, -2), (key1325, -2), (key1425, -2), (key1420, -2), (key1814, -2), (key1618, -2), (key1816, -2), (key1623, -2), (key1443, -2), (key1824, -2), (key1632, -2), (key1297, 1), (key1292, 1), (key1338, 1), (key1312, 1), (key1344, 1), (key1325, 1), (key1392, 1), (key1387, 1), (key1773, 1), (key1542, 1), (key1779, 1), (key1555, 1), (key1456, 1), (key1420, 1), (key1789, 1), (key1569, 1), (key1816, 1), (key1658, 1), (key1465, 1), (key1443, 1), (key1797, 1), (key1592, 1), (key1824, 1), (key1666, 1)]

theorem rawRowCheck10983 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form8 = rawRow10983 := by decide +kernel

def row10983 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10983 : row10983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10983 := by decide +kernel

theorem rowEval10983 (x : Key → ℝ) : Integer.Sparse.eval row10983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10983, Integer.Sparse.eval_collectBalanced, rawRowCheck10983]

def rawRow10984 : Integer.Sparse Key := [(key1312, -2), (key1325, -2), (key1317, -2), (key1618, -2), (key1623, -2), (key1420, -2), (key1816, -2), (key1425, -2), (key1814, -2), (key1632, -2), (key1443, -2), (key1824, -2), (key1312, 1), (key1325, 1), (key1292, 1), (key1344, 1), (key1297, 1), (key1338, 1), (key1542, 1), (key1555, 1), (key1387, 1), (key1779, 1), (key1392, 1), (key1773, 1), (key1569, 1), (key1658, 1), (key1420, 1), (key1816, 1), (key1456, 1), (key1789, 1), (key1592, 1), (key1666, 1), (key1443, 1), (key1824, 1), (key1465, 1), (key1797, 1)]

theorem rawRowCheck10984 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form8 = rawRow10984 := by decide +kernel

def row10984 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10984 : row10984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10984 := by decide +kernel

theorem rowEval10984 (x : Key → ℝ) : Integer.Sparse.eval row10984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10984, Integer.Sparse.eval_collectBalanced, rawRowCheck10984]

def rawRow10985 : Integer.Sparse Key := [(key1325, -2), (key1312, -2), (key1317, -2), (key1623, -2), (key1618, -2), (key1816, -2), (key1420, -2), (key1814, -2), (key1425, -2), (key1632, -2), (key1824, -2), (key1443, -2), (key1325, 1), (key1312, 1), (key1344, 1), (key1292, 1), (key1338, 1), (key1297, 1), (key1555, 1), (key1542, 1), (key1779, 1), (key1387, 1), (key1773, 1), (key1392, 1), (key1658, 1), (key1569, 1), (key1816, 1), (key1420, 1), (key1789, 1), (key1456, 1), (key1666, 1), (key1592, 1), (key1824, 1), (key1443, 1), (key1797, 1), (key1465, 1)]

theorem rawRowCheck10985 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form8 = rawRow10985 := by decide +kernel

def row10985 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10985 : row10985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10985 := by decide +kernel

theorem rowEval10985 (x : Key → ℝ) : Integer.Sparse.eval row10985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10985, Integer.Sparse.eval_collectBalanced, rawRowCheck10985]

def rawRow10986 : Integer.Sparse Key := [(key1317, -2), (key1325, -2), (key1312, -2), (key1814, -2), (key1816, -2), (key1425, -2), (key1623, -2), (key1420, -2), (key1618, -2), (key1824, -2), (key1443, -2), (key1632, -2), (key1338, 1), (key1344, 1), (key1297, 1), (key1325, 1), (key1292, 1), (key1312, 1), (key1773, 1), (key1779, 1), (key1392, 1), (key1555, 1), (key1387, 1), (key1542, 1), (key1789, 1), (key1816, 1), (key1456, 1), (key1658, 1), (key1420, 1), (key1569, 1), (key1797, 1), (key1824, 1), (key1465, 1), (key1666, 1), (key1443, 1), (key1592, 1)]

theorem rawRowCheck10986 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form8 = rawRow10986 := by decide +kernel

def row10986 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10986 : row10986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10986 := by decide +kernel

theorem rowEval10986 (x : Key → ℝ) : Integer.Sparse.eval row10986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10986, Integer.Sparse.eval_collectBalanced, rawRowCheck10986]

def rawRow10987 : Integer.Sparse Key := [(key1325, -2), (key1317, -2), (key1312, -2), (key1816, -2), (key1814, -2), (key1623, -2), (key1425, -2), (key1618, -2), (key1420, -2), (key1824, -2), (key1632, -2), (key1443, -2), (key1344, 1), (key1338, 1), (key1325, 1), (key1297, 1), (key1312, 1), (key1292, 1), (key1779, 1), (key1773, 1), (key1555, 1), (key1392, 1), (key1542, 1), (key1387, 1), (key1816, 1), (key1789, 1), (key1658, 1), (key1456, 1), (key1569, 1), (key1420, 1), (key1824, 1), (key1797, 1), (key1666, 1), (key1465, 1), (key1592, 1), (key1443, 1)]

theorem rawRowCheck10987 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form8 = rawRow10987 := by decide +kernel

def row10987 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10987 : row10987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10987 := by decide +kernel

theorem rowEval10987 (x : Key → ℝ) : Integer.Sparse.eval row10987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10987, Integer.Sparse.eval_collectBalanced, rawRowCheck10987]

def rawRow10988 : Integer.Sparse Key := [(key1420, -2), (key1425, -2), (key1443, -2), (key1312, -2), (key1317, -2), (key1618, -2), (key1814, -2), (key1632, -2), (key1824, -2), (key1325, -2), (key1623, -2), (key1816, -2), (key1387, 1), (key1392, 1), (key1420, 1), (key1456, 1), (key1443, 1), (key1465, 1), (key1292, 1), (key1297, 1), (key1569, 1), (key1789, 1), (key1592, 1), (key1797, 1), (key1312, 1), (key1338, 1), (key1542, 1), (key1773, 1), (key1666, 1), (key1824, 1), (key1325, 1), (key1344, 1), (key1555, 1), (key1779, 1), (key1658, 1), (key1816, 1)]

theorem rawRowCheck10988 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form8 = rawRow10988 := by decide +kernel

def row10988 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10988 : row10988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10988 := by decide +kernel

theorem rowEval10988 (x : Key → ℝ) : Integer.Sparse.eval row10988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10988, Integer.Sparse.eval_collectBalanced, rawRowCheck10988]

def rawRow10989 : Integer.Sparse Key := [(key1425, -2), (key1420, -2), (key1443, -2), (key1317, -2), (key1312, -2), (key1814, -2), (key1618, -2), (key1824, -2), (key1632, -2), (key1325, -2), (key1816, -2), (key1623, -2), (key1392, 1), (key1387, 1), (key1456, 1), (key1420, 1), (key1465, 1), (key1443, 1), (key1297, 1), (key1292, 1), (key1789, 1), (key1569, 1), (key1797, 1), (key1592, 1), (key1338, 1), (key1312, 1), (key1773, 1), (key1542, 1), (key1824, 1), (key1666, 1), (key1344, 1), (key1325, 1), (key1779, 1), (key1555, 1), (key1816, 1), (key1658, 1)]

theorem rawRowCheck10989 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form8 = rawRow10989 := by decide +kernel

def row10989 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10989 : row10989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10989 := by decide +kernel

theorem rowEval10989 (x : Key → ℝ) : Integer.Sparse.eval row10989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10989, Integer.Sparse.eval_collectBalanced, rawRowCheck10989]

def rawRow10990 : Integer.Sparse Key := [(key1420, -2), (key1443, -2), (key1425, -2), (key1618, -2), (key1632, -2), (key1312, -2), (key1824, -2), (key1317, -2), (key1814, -2), (key1623, -2), (key1325, -2), (key1816, -2), (key1420, 1), (key1443, 1), (key1387, 1), (key1465, 1), (key1392, 1), (key1456, 1), (key1569, 1), (key1592, 1), (key1292, 1), (key1797, 1), (key1297, 1), (key1789, 1), (key1542, 1), (key1666, 1), (key1312, 1), (key1824, 1), (key1338, 1), (key1773, 1), (key1555, 1), (key1658, 1), (key1325, 1), (key1816, 1), (key1344, 1), (key1779, 1)]

theorem rawRowCheck10990 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form8 = rawRow10990 := by decide +kernel

def row10990 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10990 : row10990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10990 := by decide +kernel

theorem rowEval10990 (x : Key → ℝ) : Integer.Sparse.eval row10990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10990, Integer.Sparse.eval_collectBalanced, rawRowCheck10990]

def rawRow10991 : Integer.Sparse Key := [(key1443, -2), (key1420, -2), (key1425, -2), (key1632, -2), (key1618, -2), (key1824, -2), (key1312, -2), (key1814, -2), (key1317, -2), (key1623, -2), (key1816, -2), (key1325, -2), (key1443, 1), (key1420, 1), (key1465, 1), (key1387, 1), (key1456, 1), (key1392, 1), (key1592, 1), (key1569, 1), (key1797, 1), (key1292, 1), (key1789, 1), (key1297, 1), (key1666, 1), (key1542, 1), (key1824, 1), (key1312, 1), (key1773, 1), (key1338, 1), (key1658, 1), (key1555, 1), (key1816, 1), (key1325, 1), (key1779, 1), (key1344, 1)]

theorem rawRowCheck10991 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form8 = rawRow10991 := by decide +kernel

def row10991 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10991 : row10991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10991 := by decide +kernel

theorem rowEval10991 (x : Key → ℝ) : Integer.Sparse.eval row10991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck10991, Integer.Sparse.eval_collectBalanced, rawRowCheck10991]

def rawRow10992 : Integer.Sparse Key := [(key1425, -2), (key1443, -2), (key1420, -2), (key1814, -2), (key1824, -2), (key1317, -2), (key1632, -2), (key1312, -2), (key1618, -2), (key1816, -2), (key1325, -2), (key1623, -2), (key1456, 1), (key1465, 1), (key1392, 1), (key1443, 1), (key1387, 1), (key1420, 1), (key1789, 1), (key1797, 1), (key1297, 1), (key1592, 1), (key1292, 1), (key1569, 1), (key1773, 1), (key1824, 1), (key1338, 1), (key1666, 1), (key1312, 1), (key1542, 1), (key1779, 1), (key1816, 1), (key1344, 1), (key1658, 1), (key1325, 1), (key1555, 1)]

theorem rawRowCheck10992 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form8 = rawRow10992 := by decide +kernel

def row10992 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10992 : row10992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10992 := by decide +kernel

theorem rowEval10992 (x : Key → ℝ) : Integer.Sparse.eval row10992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10992, Integer.Sparse.eval_collectBalanced, rawRowCheck10992]

def rawRow10993 : Integer.Sparse Key := [(key1443, -2), (key1425, -2), (key1420, -2), (key1824, -2), (key1814, -2), (key1632, -2), (key1317, -2), (key1618, -2), (key1312, -2), (key1816, -2), (key1623, -2), (key1325, -2), (key1465, 1), (key1456, 1), (key1443, 1), (key1392, 1), (key1420, 1), (key1387, 1), (key1797, 1), (key1789, 1), (key1592, 1), (key1297, 1), (key1569, 1), (key1292, 1), (key1824, 1), (key1773, 1), (key1666, 1), (key1338, 1), (key1542, 1), (key1312, 1), (key1816, 1), (key1779, 1), (key1658, 1), (key1344, 1), (key1555, 1), (key1325, 1)]

theorem rawRowCheck10993 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form8 = rawRow10993 := by decide +kernel

def row10993 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10993 : row10993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10993 := by decide +kernel

theorem rowEval10993 (x : Key → ℝ) : Integer.Sparse.eval row10993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck10993, Integer.Sparse.eval_collectBalanced, rawRowCheck10993]

def rawRow10994 : Integer.Sparse Key := [(key1618, -2), (key1623, -2), (key1632, -2), (key1312, -2), (key1325, -2), (key1420, -2), (key1816, -2), (key1443, -2), (key1824, -2), (key1317, -2), (key1425, -2), (key1814, -2), (key1542, 1), (key1555, 1), (key1569, 1), (key1658, 1), (key1592, 1), (key1666, 1), (key1312, 1), (key1325, 1), (key1420, 1), (key1816, 1), (key1443, 1), (key1824, 1), (key1292, 1), (key1344, 1), (key1387, 1), (key1779, 1), (key1465, 1), (key1797, 1), (key1297, 1), (key1338, 1), (key1392, 1), (key1773, 1), (key1456, 1), (key1789, 1)]

theorem rawRowCheck10994 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form8 = rawRow10994 := by decide +kernel

def row10994 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10994 : row10994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10994 := by decide +kernel

theorem rowEval10994 (x : Key → ℝ) : Integer.Sparse.eval row10994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10994, Integer.Sparse.eval_collectBalanced, rawRowCheck10994]

def rawRow10995 : Integer.Sparse Key := [(key1623, -2), (key1618, -2), (key1632, -2), (key1325, -2), (key1312, -2), (key1816, -2), (key1420, -2), (key1824, -2), (key1443, -2), (key1317, -2), (key1814, -2), (key1425, -2), (key1555, 1), (key1542, 1), (key1658, 1), (key1569, 1), (key1666, 1), (key1592, 1), (key1325, 1), (key1312, 1), (key1816, 1), (key1420, 1), (key1824, 1), (key1443, 1), (key1344, 1), (key1292, 1), (key1779, 1), (key1387, 1), (key1797, 1), (key1465, 1), (key1338, 1), (key1297, 1), (key1773, 1), (key1392, 1), (key1789, 1), (key1456, 1)]

theorem rawRowCheck10995 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form8 = rawRow10995 := by decide +kernel

def row10995 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10995 : row10995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10995 := by decide +kernel

theorem rowEval10995 (x : Key → ℝ) : Integer.Sparse.eval row10995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10995, Integer.Sparse.eval_collectBalanced, rawRowCheck10995]

def rawRow10996 : Integer.Sparse Key := [(key1618, -2), (key1632, -2), (key1623, -2), (key1420, -2), (key1443, -2), (key1312, -2), (key1824, -2), (key1325, -2), (key1816, -2), (key1425, -2), (key1317, -2), (key1814, -2), (key1569, 1), (key1592, 1), (key1542, 1), (key1666, 1), (key1555, 1), (key1658, 1), (key1420, 1), (key1443, 1), (key1312, 1), (key1824, 1), (key1325, 1), (key1816, 1), (key1387, 1), (key1465, 1), (key1292, 1), (key1797, 1), (key1344, 1), (key1779, 1), (key1392, 1), (key1456, 1), (key1297, 1), (key1789, 1), (key1338, 1), (key1773, 1)]

theorem rawRowCheck10996 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form8 = rawRow10996 := by decide +kernel

def row10996 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10996 : row10996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10996 := by decide +kernel

theorem rowEval10996 (x : Key → ℝ) : Integer.Sparse.eval row10996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10996, Integer.Sparse.eval_collectBalanced, rawRowCheck10996]

def rawRow10997 : Integer.Sparse Key := [(key1632, -2), (key1618, -2), (key1623, -2), (key1443, -2), (key1420, -2), (key1824, -2), (key1312, -2), (key1816, -2), (key1325, -2), (key1425, -2), (key1814, -2), (key1317, -2), (key1592, 1), (key1569, 1), (key1666, 1), (key1542, 1), (key1658, 1), (key1555, 1), (key1443, 1), (key1420, 1), (key1824, 1), (key1312, 1), (key1816, 1), (key1325, 1), (key1465, 1), (key1387, 1), (key1797, 1), (key1292, 1), (key1779, 1), (key1344, 1), (key1456, 1), (key1392, 1), (key1789, 1), (key1297, 1), (key1773, 1), (key1338, 1)]

theorem rawRowCheck10997 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form8 = rawRow10997 := by decide +kernel

def row10997 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10997 : row10997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10997 := by decide +kernel

theorem rowEval10997 (x : Key → ℝ) : Integer.Sparse.eval row10997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck10997, Integer.Sparse.eval_collectBalanced, rawRowCheck10997]

def rawRow10998 : Integer.Sparse Key := [(key1623, -2), (key1632, -2), (key1618, -2), (key1816, -2), (key1824, -2), (key1325, -2), (key1443, -2), (key1312, -2), (key1420, -2), (key1814, -2), (key1317, -2), (key1425, -2), (key1658, 1), (key1666, 1), (key1555, 1), (key1592, 1), (key1542, 1), (key1569, 1), (key1816, 1), (key1824, 1), (key1325, 1), (key1443, 1), (key1312, 1), (key1420, 1), (key1779, 1), (key1797, 1), (key1344, 1), (key1465, 1), (key1292, 1), (key1387, 1), (key1773, 1), (key1789, 1), (key1338, 1), (key1456, 1), (key1297, 1), (key1392, 1)]

theorem rawRowCheck10998 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form8 = rawRow10998 := by decide +kernel

def row10998 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10998 : row10998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10998 := by decide +kernel

theorem rowEval10998 (x : Key → ℝ) : Integer.Sparse.eval row10998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10998, Integer.Sparse.eval_collectBalanced, rawRowCheck10998]

def rawRow10999 : Integer.Sparse Key := [(key1632, -2), (key1623, -2), (key1618, -2), (key1824, -2), (key1816, -2), (key1443, -2), (key1325, -2), (key1420, -2), (key1312, -2), (key1814, -2), (key1425, -2), (key1317, -2), (key1666, 1), (key1658, 1), (key1592, 1), (key1555, 1), (key1569, 1), (key1542, 1), (key1824, 1), (key1816, 1), (key1443, 1), (key1325, 1), (key1420, 1), (key1312, 1), (key1797, 1), (key1779, 1), (key1465, 1), (key1344, 1), (key1387, 1), (key1292, 1), (key1789, 1), (key1773, 1), (key1456, 1), (key1338, 1), (key1392, 1), (key1297, 1)]

theorem rawRowCheck10999 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form8 = rawRow10999 := by decide +kernel

def row10999 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck10999 : row10999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10999 := by decide +kernel

theorem rowEval10999 (x : Key → ℝ) : Integer.Sparse.eval row10999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck10999, Integer.Sparse.eval_collectBalanced, rawRowCheck10999]

def rawRow11000 : Integer.Sparse Key := [(key1814, -2), (key1816, -2), (key1824, -2), (key1317, -2), (key1325, -2), (key1425, -2), (key1623, -2), (key1443, -2), (key1632, -2), (key1312, -2), (key1420, -2), (key1618, -2), (key1773, 1), (key1779, 1), (key1789, 1), (key1816, 1), (key1797, 1), (key1824, 1), (key1338, 1), (key1344, 1), (key1456, 1), (key1658, 1), (key1465, 1), (key1666, 1), (key1297, 1), (key1325, 1), (key1392, 1), (key1555, 1), (key1443, 1), (key1592, 1), (key1292, 1), (key1312, 1), (key1387, 1), (key1542, 1), (key1420, 1), (key1569, 1)]

theorem rawRowCheck11000 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form8 = rawRow11000 := by decide +kernel

def row11000 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck11000 : row11000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11000 := by decide +kernel

theorem rowEval11000 (x : Key → ℝ) : Integer.Sparse.eval row11000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11000, Integer.Sparse.eval_collectBalanced, rawRowCheck11000]

def rawRow11001 : Integer.Sparse Key := [(key1816, -2), (key1814, -2), (key1824, -2), (key1325, -2), (key1317, -2), (key1623, -2), (key1425, -2), (key1632, -2), (key1443, -2), (key1312, -2), (key1618, -2), (key1420, -2), (key1779, 1), (key1773, 1), (key1816, 1), (key1789, 1), (key1824, 1), (key1797, 1), (key1344, 1), (key1338, 1), (key1658, 1), (key1456, 1), (key1666, 1), (key1465, 1), (key1325, 1), (key1297, 1), (key1555, 1), (key1392, 1), (key1592, 1), (key1443, 1), (key1312, 1), (key1292, 1), (key1542, 1), (key1387, 1), (key1569, 1), (key1420, 1)]

theorem rawRowCheck11001 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form8 = rawRow11001 := by decide +kernel

def row11001 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck11001 : row11001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11001 := by decide +kernel

theorem rowEval11001 (x : Key → ℝ) : Integer.Sparse.eval row11001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11001, Integer.Sparse.eval_collectBalanced, rawRowCheck11001]

def rawRow11002 : Integer.Sparse Key := [(key1814, -2), (key1824, -2), (key1816, -2), (key1425, -2), (key1443, -2), (key1317, -2), (key1632, -2), (key1325, -2), (key1623, -2), (key1420, -2), (key1312, -2), (key1618, -2), (key1789, 1), (key1797, 1), (key1773, 1), (key1824, 1), (key1779, 1), (key1816, 1), (key1456, 1), (key1465, 1), (key1338, 1), (key1666, 1), (key1344, 1), (key1658, 1), (key1392, 1), (key1443, 1), (key1297, 1), (key1592, 1), (key1325, 1), (key1555, 1), (key1387, 1), (key1420, 1), (key1292, 1), (key1569, 1), (key1312, 1), (key1542, 1)]

theorem rawRowCheck11002 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form8 = rawRow11002 := by decide +kernel

def row11002 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck11002 : row11002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11002 := by decide +kernel

theorem rowEval11002 (x : Key → ℝ) : Integer.Sparse.eval row11002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11002, Integer.Sparse.eval_collectBalanced, rawRowCheck11002]

def rawRow11003 : Integer.Sparse Key := [(key1824, -2), (key1814, -2), (key1816, -2), (key1443, -2), (key1425, -2), (key1632, -2), (key1317, -2), (key1623, -2), (key1325, -2), (key1420, -2), (key1618, -2), (key1312, -2), (key1797, 1), (key1789, 1), (key1824, 1), (key1773, 1), (key1816, 1), (key1779, 1), (key1465, 1), (key1456, 1), (key1666, 1), (key1338, 1), (key1658, 1), (key1344, 1), (key1443, 1), (key1392, 1), (key1592, 1), (key1297, 1), (key1555, 1), (key1325, 1), (key1420, 1), (key1387, 1), (key1569, 1), (key1292, 1), (key1542, 1), (key1312, 1)]

theorem rawRowCheck11003 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form8 = rawRow11003 := by decide +kernel

def row11003 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck11003 : row11003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11003 := by decide +kernel

theorem rowEval11003 (x : Key → ℝ) : Integer.Sparse.eval row11003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck11003, Integer.Sparse.eval_collectBalanced, rawRowCheck11003]

def rawRow11004 : Integer.Sparse Key := [(key1816, -2), (key1824, -2), (key1814, -2), (key1623, -2), (key1632, -2), (key1325, -2), (key1443, -2), (key1317, -2), (key1425, -2), (key1618, -2), (key1312, -2), (key1420, -2), (key1816, 1), (key1824, 1), (key1779, 1), (key1797, 1), (key1773, 1), (key1789, 1), (key1658, 1), (key1666, 1), (key1344, 1), (key1465, 1), (key1338, 1), (key1456, 1), (key1555, 1), (key1592, 1), (key1325, 1), (key1443, 1), (key1297, 1), (key1392, 1), (key1542, 1), (key1569, 1), (key1312, 1), (key1420, 1), (key1292, 1), (key1387, 1)]

theorem rawRowCheck11004 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form8 = rawRow11004 := by decide +kernel

def row11004 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck11004 : row11004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11004 := by decide +kernel

theorem rowEval11004 (x : Key → ℝ) : Integer.Sparse.eval row11004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11004, Integer.Sparse.eval_collectBalanced, rawRowCheck11004]

def rawRow11005 : Integer.Sparse Key := [(key1824, -2), (key1816, -2), (key1814, -2), (key1632, -2), (key1623, -2), (key1443, -2), (key1325, -2), (key1425, -2), (key1317, -2), (key1618, -2), (key1420, -2), (key1312, -2), (key1824, 1), (key1816, 1), (key1797, 1), (key1779, 1), (key1789, 1), (key1773, 1), (key1666, 1), (key1658, 1), (key1465, 1), (key1344, 1), (key1456, 1), (key1338, 1), (key1592, 1), (key1555, 1), (key1443, 1), (key1325, 1), (key1392, 1), (key1297, 1), (key1569, 1), (key1542, 1), (key1420, 1), (key1312, 1), (key1387, 1), (key1292, 1)]

theorem rawRowCheck11005 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form8 = rawRow11005 := by decide +kernel

def row11005 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck11005 : row11005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11005 := by decide +kernel

theorem rowEval11005 (x : Key → ℝ) : Integer.Sparse.eval row11005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck11005, Integer.Sparse.eval_collectBalanced, rawRowCheck11005]

def rawRow11006 : Integer.Sparse Key := [(key1338, -2), (key1338, -2), (key1344, -2), (key1456, -2), (key1456, -2), (key1656, -2), (key1656, -2), (key1658, -2), (key1658, -2), (key1465, -2), (key1666, -2), (key1666, -2), (key1297, 1), (key1297, 1), (key1317, 1), (key1317, 1), (key1325, 1), (key1325, 1), (key1392, 1), (key1392, 1), (key1547, 1), (key1547, 1), (key1555, 1), (key1555, 1), (key1425, 1), (key1425, 1), (key1574, 1), (key1574, 1), (key1623, 1), (key1623, 1), (key1443, 1), (key1443, 1), (key1592, 1), (key1592, 1), (key1632, 1), (key1632, 1)]

theorem rawRowCheck11006 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form8 = rawRow11006 := by decide +kernel

def row11006 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

theorem rowCheck11006 : row11006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11006 := by decide +kernel

theorem rowEval11006 (x : Key → ℝ) : Integer.Sparse.eval row11006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11006, Integer.Sparse.eval_collectBalanced, rawRowCheck11006]

def rawRow11007 : Integer.Sparse Key := [(key1338, -2), (key1344, -2), (key1338, -2), (key1656, -2), (key1658, -2), (key1456, -2), (key1658, -2), (key1456, -2), (key1656, -2), (key1666, -2), (key1465, -2), (key1666, -2), (key1317, 1), (key1325, 1), (key1297, 1), (key1325, 1), (key1297, 1), (key1317, 1), (key1547, 1), (key1555, 1), (key1392, 1), (key1555, 1), (key1392, 1), (key1547, 1), (key1574, 1), (key1623, 1), (key1425, 1), (key1623, 1), (key1425, 1), (key1574, 1), (key1592, 1), (key1632, 1), (key1443, 1), (key1632, 1), (key1443, 1), (key1592, 1)]

theorem rawRowCheck11007 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form8 = rawRow11007 := by decide +kernel

def row11007 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

theorem rowCheck11007 : row11007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11007 := by decide +kernel

theorem rowEval11007 (x : Key → ℝ) : Integer.Sparse.eval row11007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11007, Integer.Sparse.eval_collectBalanced, rawRowCheck11007]

end MUB6.Certificate.GramRows

end OAI
