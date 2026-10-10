import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow192 : Integer.Sparse Key := [(key2809, -2), (key2829, 1), (key2835, 1), (key2786, 2), (key2870, -1), (key2923, -1), (key2794, -1), (key2798, -1), (key2860, 1), (key2920, 1), (key2706, 2), (key2726, -1), (key2732, -1), (key2632, -2), (key2870, 1), (key3026, 1), (key2640, 1), (key2644, 1), (key2860, -1), (key3023, -1), (key2671, -2), (key2726, 1), (key2758, 1), (key2612, 2), (key2948, -1), (key2960, -1), (key2646, -1), (key2653, -1), (key2735, 1), (key2747, 1), (key2667, 1), (key2673, 1), (key2782, -1), (key2795, -1), (key2612, -1), (key2618, -1), (key2805, 1), (key2831, 1), (key2628, 1), (key2641, 1), (key2702, -1), (key2728, -1)]

theorem rawRowCheck192 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block0.form1 = rawRow192 := by decide +kernel

def row192 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, 1), (key2671, -2), (key2673, 1), (key2702, -1), (key2706, 2), (key2728, -1), (key2732, -1), (key2735, 1), (key2747, 1), (key2758, 1), (key2782, -1), (key2786, 2), (key2794, -1), (key2795, -1), (key2798, -1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2835, 1), (key2920, 1), (key2923, -1), (key2948, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

theorem rowCheck192 : row192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow192 := by decide +kernel

theorem rowEval192 (x : Key → ℝ) : Integer.Sparse.eval row192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block0.form1) x := by
  rw [rowCheck192, Integer.Sparse.eval_collectBalanced, rawRowCheck192]

def rawRow193 : Integer.Sparse Key := [(key2809, -2), (key2835, 1), (key2829, 1), (key2786, 2), (key2923, -1), (key2870, -1), (key2798, -1), (key2794, -1), (key2920, 1), (key2860, 1), (key2706, 2), (key2732, -1), (key2726, -1), (key2632, -2), (key3026, 1), (key2870, 1), (key2644, 1), (key2640, 1), (key3023, -1), (key2860, -1), (key2671, -2), (key2758, 1), (key2726, 1), (key2616, 2), (key2960, -1), (key2948, -1), (key2653, -1), (key2646, -1), (key2747, 1), (key2735, 1), (key2673, 1), (key2667, 1), (key2795, -1), (key2782, -1), (key2618, -1), (key2612, -1), (key2831, 1), (key2805, 1), (key2641, 1), (key2628, 1), (key2728, -1), (key2702, -1)]

theorem rawRowCheck193 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block0.form1 = rawRow193 := by decide +kernel

def row193 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, 1), (key2671, -2), (key2673, 1), (key2702, -1), (key2706, 2), (key2728, -1), (key2732, -1), (key2735, 1), (key2747, 1), (key2758, 1), (key2782, -1), (key2786, 2), (key2794, -1), (key2795, -1), (key2798, -1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2835, 1), (key2920, 1), (key2923, -1), (key2948, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

theorem rowCheck193 : row193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow193 := by decide +kernel

theorem rowEval193 (x : Key → ℝ) : Integer.Sparse.eval row193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck193, Integer.Sparse.eval_collectBalanced, rawRowCheck193]

def rawRow194 : Integer.Sparse Key := [(key2835, -2), (key2809, 1), (key2829, 1), (key2923, 2), (key2786, -1), (key2870, -1), (key2920, -1), (key2927, -1), (key2798, 1), (key2885, 1), (key2732, 2), (key2706, -1), (key2726, -1), (key3026, -2), (key2632, 1), (key2870, 1), (key3023, 1), (key3030, 1), (key2644, -1), (key2885, -1), (key2758, -2), (key2671, 1), (key2726, 1), (key3017, 2), (key2616, -1), (key2829, -1), (key2747, -1), (key3000, -1), (key2653, 1), (key2998, 1), (key2795, 1), (key2943, 1), (key2673, -1), (key2938, -1), (key2831, -1), (key2960, -1), (key2618, 1), (key2950, 1), (key2728, 1), (key2983, 1), (key2641, -1), (key2976, -1)]

theorem rawRowCheck194 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block0.form1 = rawRow194 := by decide +kernel

def row194 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -1), (key2653, 1), (key2671, 1), (key2673, -1), (key2706, -1), (key2728, 1), (key2732, 2), (key2747, -1), (key2758, -2), (key2786, -1), (key2795, 1), (key2798, 1), (key2809, 1), (key2831, -1), (key2835, -2), (key2920, -1), (key2923, 2), (key2927, -1), (key2938, -1), (key2943, 1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1), (key2998, 1), (key3000, -1), (key3017, 2), (key3023, 1), (key3026, -2), (key3030, 1)]

theorem rowCheck194 : row194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow194 := by decide +kernel

theorem rowEval194 (x : Key → ℝ) : Integer.Sparse.eval row194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck194, Integer.Sparse.eval_collectBalanced, rawRowCheck194]

def rawRow195 : Integer.Sparse Key := [(key2835, -2), (key2829, 1), (key2809, 1), (key2923, 2), (key2870, -1), (key2786, -1), (key2927, -1), (key2920, -1), (key2885, 1), (key2798, 1), (key2732, 2), (key2726, -1), (key2706, -1), (key3026, -2), (key2870, 1), (key2632, 1), (key3030, 1), (key3023, 1), (key2885, -1), (key2644, -1), (key2758, -2), (key2726, 1), (key2671, 1), (key3017, 2), (key2829, -1), (key2616, -1), (key3000, -1), (key2747, -1), (key2998, 1), (key2653, 1), (key2943, 1), (key2795, 1), (key2938, -1), (key2673, -1), (key2960, -1), (key2831, -1), (key2950, 1), (key2618, 1), (key2983, 1), (key2728, 1), (key2976, -1), (key2641, -1)]

theorem rawRowCheck195 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block0.form1 = rawRow195 := by decide +kernel

def row195 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -1), (key2653, 1), (key2671, 1), (key2673, -1), (key2706, -1), (key2728, 1), (key2732, 2), (key2747, -1), (key2758, -2), (key2786, -1), (key2795, 1), (key2798, 1), (key2809, 1), (key2831, -1), (key2835, -2), (key2920, -1), (key2923, 2), (key2927, -1), (key2938, -1), (key2943, 1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1), (key2998, 1), (key3000, -1), (key3017, 2), (key3023, 1), (key3026, -2), (key3030, 1)]

theorem rowCheck195 : row195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow195 := by decide +kernel

theorem rowEval195 (x : Key → ℝ) : Integer.Sparse.eval row195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck195, Integer.Sparse.eval_collectBalanced, rawRowCheck195]

def rawRow196 : Integer.Sparse Key := [(key2920, -2), (key2923, 1), (key2927, 1), (key2798, 2), (key2835, -1), (key2885, -1), (key2786, -1), (key2794, -1), (key2809, 1), (key2860, 1), (key3023, 2), (key3026, -1), (key3030, -1), (key2644, -2), (key2732, 1), (key2885, 1), (key2632, 1), (key2640, 1), (key2706, -1), (key2860, -1), (key3010, -2), (key3017, 1), (key3030, 1), (key2660, 2), (key2758, -1), (key2927, -1), (key2616, -1), (key2640, -1), (key2671, 1), (key2794, 1), (key2728, 1), (key2747, 1), (key2831, -1), (key2904, -1), (key2641, -1), (key2653, -1), (key2795, 1), (key2897, 1), (key2618, 1), (key2648, 1), (key2673, -1), (key2737, -1)]

theorem rawRowCheck196 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block0.form1 = rawRow196 := by decide +kernel

def row196 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, 1), (key2673, -1), (key2706, -1), (key2728, 1), (key2732, 1), (key2737, -1), (key2747, 1), (key2758, -1), (key2786, -1), (key2795, 1), (key2798, 2), (key2809, 1), (key2831, -1), (key2835, -1), (key2897, 1), (key2904, -1), (key2920, -2), (key2923, 1), (key3010, -2), (key3017, 1), (key3023, 2), (key3026, -1)]

theorem rowCheck196 : row196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow196 := by decide +kernel

theorem rowEval196 (x : Key → ℝ) : Integer.Sparse.eval row196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck196, Integer.Sparse.eval_collectBalanced, rawRowCheck196]

def rawRow197 : Integer.Sparse Key := [(key2920, -2), (key2927, 1), (key2923, 1), (key2798, 2), (key2885, -1), (key2835, -1), (key2794, -1), (key2786, -1), (key2860, 1), (key2809, 1), (key3023, 2), (key3030, -1), (key3026, -1), (key2644, -2), (key2885, 1), (key2732, 1), (key2640, 1), (key2632, 1), (key2860, -1), (key2706, -1), (key3010, -2), (key3030, 1), (key3017, 1), (key2660, 2), (key2927, -1), (key2758, -1), (key2640, -1), (key2616, -1), (key2794, 1), (key2671, 1), (key2747, 1), (key2728, 1), (key2904, -1), (key2831, -1), (key2653, -1), (key2641, -1), (key2897, 1), (key2795, 1), (key2648, 1), (key2618, 1), (key2737, -1), (key2673, -1)]

theorem rawRowCheck197 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block0.form1 = rawRow197 := by decide +kernel

def row197 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, 1), (key2673, -1), (key2706, -1), (key2728, 1), (key2732, 1), (key2737, -1), (key2747, 1), (key2758, -1), (key2786, -1), (key2795, 1), (key2798, 2), (key2809, 1), (key2831, -1), (key2835, -1), (key2897, 1), (key2904, -1), (key2920, -2), (key2923, 1), (key3010, -2), (key3017, 1), (key3023, 2), (key3026, -1)]

theorem rowCheck197 : row197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow197 := by decide +kernel

theorem rowEval197 (x : Key → ℝ) : Integer.Sparse.eval row197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck197, Integer.Sparse.eval_collectBalanced, rawRowCheck197]

def rawRow198 : Integer.Sparse Key := [(key2923, -2), (key2920, 1), (key2927, 1), (key2835, 2), (key2798, -1), (key2885, -1), (key2809, -1), (key2829, -1), (key2786, 1), (key2870, 1), (key3026, 2), (key3023, -1), (key3030, -1), (key2732, -2), (key2644, 1), (key2885, 1), (key2706, 1), (key2726, 1), (key2632, -1), (key2870, -1), (key3017, -2), (key3010, 1), (key3030, 1), (key2758, 2), (key2660, -1), (key2927, -1), (key2671, -1), (key2726, -1), (key2616, 1), (key2829, 1), (key2831, 1), (key2960, 1), (key2728, -1), (key2983, -1), (key2795, -1), (key2943, -1), (key2641, 1), (key2976, 1), (key2673, 1), (key2938, 1), (key2618, -1), (key2950, -1)]

theorem rawRowCheck198 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block0.form1 = rawRow198 := by decide +kernel

def row198 : Integer.Sparse Key := [(key2616, 1), (key2618, -1), (key2632, -1), (key2641, 1), (key2644, 1), (key2660, -1), (key2671, -1), (key2673, 1), (key2706, 1), (key2728, -1), (key2732, -2), (key2758, 2), (key2786, 1), (key2795, -1), (key2798, -1), (key2809, -1), (key2831, 1), (key2835, 2), (key2920, 1), (key2923, -2), (key2938, 1), (key2943, -1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, -1), (key3010, 1), (key3017, -2), (key3023, -1), (key3026, 2)]

theorem rowCheck198 : row198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow198 := by decide +kernel

theorem rowEval198 (x : Key → ℝ) : Integer.Sparse.eval row198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck198, Integer.Sparse.eval_collectBalanced, rawRowCheck198]

def rawRow199 : Integer.Sparse Key := [(key2923, -2), (key2927, 1), (key2920, 1), (key2835, 2), (key2885, -1), (key2798, -1), (key2829, -1), (key2809, -1), (key2870, 1), (key2786, 1), (key3026, 2), (key3030, -1), (key3023, -1), (key2732, -2), (key2885, 1), (key2644, 1), (key2726, 1), (key2706, 1), (key2870, -1), (key2632, -1), (key3017, -2), (key3030, 1), (key3010, 1), (key2758, 2), (key2927, -1), (key2660, -1), (key2726, -1), (key2671, -1), (key2829, 1), (key2616, 1), (key2960, 1), (key2831, 1), (key2983, -1), (key2728, -1), (key2943, -1), (key2795, -1), (key2976, 1), (key2641, 1), (key2938, 1), (key2673, 1), (key2950, -1), (key2618, -1)]

theorem rawRowCheck199 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block0.form1 = rawRow199 := by decide +kernel

def row199 : Integer.Sparse Key := [(key2616, 1), (key2618, -1), (key2632, -1), (key2641, 1), (key2644, 1), (key2660, -1), (key2671, -1), (key2673, 1), (key2706, 1), (key2728, -1), (key2732, -2), (key2758, 2), (key2786, 1), (key2795, -1), (key2798, -1), (key2809, -1), (key2831, 1), (key2835, 2), (key2920, 1), (key2923, -2), (key2938, 1), (key2943, -1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, -1), (key3010, 1), (key3017, -2), (key3023, -1), (key3026, 2)]

theorem rowCheck199 : row199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow199 := by decide +kernel

theorem rowEval199 (x : Key → ℝ) : Integer.Sparse.eval row199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck199, Integer.Sparse.eval_collectBalanced, rawRowCheck199]

def rawRow200 : Integer.Sparse Key := [(key3008, -2), (key3010, 1), (key3010, 1), (key3012, 2), (key3023, -1), (key3023, -1), (key3017, -1), (key3017, -1), (key3026, 1), (key3026, 1), (key2658, 2), (key2660, -1), (key2660, -1), (key2753, -2), (key2920, 1), (key2920, 1), (key2758, 1), (key2758, 1), (key2923, -1), (key2923, -1), (key2621, -2), (key2644, 1), (key2644, 1), (key2676, 2), (key2798, -1), (key2798, -1), (key2732, -1), (key2732, -1), (key2835, 1), (key2835, 1), (key2616, 1), (key2616, 1), (key2632, -1), (key2632, -1), (key2671, -1), (key2671, -1), (key2786, 1), (key2786, 1), (key2706, 1), (key2706, 1), (key2809, -1), (key2809, -1)]

theorem rawRowCheck200 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block0.form1 = rawRow200 := by decide +kernel

def row200 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2632, -2), (key2644, 2), (key2658, 2), (key2660, -2), (key2671, -2), (key2676, 2), (key2706, 2), (key2732, -2), (key2753, -2), (key2758, 2), (key2786, 2), (key2798, -2), (key2809, -2), (key2835, 2), (key2920, 2), (key2923, -2), (key3008, -2), (key3010, 2), (key3012, 2), (key3017, -2), (key3023, -2), (key3026, 2)]

theorem rowCheck200 : row200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow200 := by decide +kernel

theorem rowEval200 (x : Key → ℝ) : Integer.Sparse.eval row200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck200, Integer.Sparse.eval_collectBalanced, rawRowCheck200]

def rawRow201 : Integer.Sparse Key := [(key3010, -2), (key3008, 1), (key3010, 1), (key3023, 2), (key3012, -1), (key3023, -1), (key3026, -1), (key3030, -1), (key3017, 1), (key3030, 1), (key2660, 2), (key2658, -1), (key2660, -1), (key2920, -2), (key2753, 1), (key2920, 1), (key2923, 1), (key2927, 1), (key2758, -1), (key2927, -1), (key2644, -2), (key2621, 1), (key2644, 1), (key2798, 2), (key2676, -1), (key2798, -1), (key2835, -1), (key2885, -1), (key2732, 1), (key2885, 1), (key2632, 1), (key2640, 1), (key2616, -1), (key2640, -1), (key2786, -1), (key2794, -1), (key2671, 1), (key2794, 1), (key2809, 1), (key2860, 1), (key2706, -1), (key2860, -1)]

theorem rawRowCheck201 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block0.form1 = rawRow201 := by decide +kernel

def row201 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2632, 1), (key2644, -1), (key2658, -1), (key2660, 1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2786, -1), (key2798, 1), (key2809, 1), (key2835, -1), (key2920, -1), (key2923, 1), (key3008, 1), (key3010, -1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, -1)]

theorem rowCheck201 : row201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow201 := by decide +kernel

theorem rowEval201 (x : Key → ℝ) : Integer.Sparse.eval row201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck201, Integer.Sparse.eval_collectBalanced, rawRowCheck201]

def rawRow202 : Integer.Sparse Key := [(key3010, -2), (key3010, 1), (key3008, 1), (key3023, 2), (key3023, -1), (key3012, -1), (key3030, -1), (key3026, -1), (key3030, 1), (key3017, 1), (key2660, 2), (key2660, -1), (key2658, -1), (key2920, -2), (key2920, 1), (key2753, 1), (key2927, 1), (key2923, 1), (key2927, -1), (key2758, -1), (key2644, -2), (key2644, 1), (key2621, 1), (key2798, 2), (key2798, -1), (key2676, -1), (key2885, -1), (key2835, -1), (key2885, 1), (key2732, 1), (key2640, 1), (key2632, 1), (key2640, -1), (key2616, -1), (key2794, -1), (key2786, -1), (key2794, 1), (key2671, 1), (key2860, 1), (key2809, 1), (key2860, -1), (key2706, -1)]

theorem rawRowCheck202 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block0.form1 = rawRow202 := by decide +kernel

def row202 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2632, 1), (key2644, -1), (key2658, -1), (key2660, 1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2786, -1), (key2798, 1), (key2809, 1), (key2835, -1), (key2920, -1), (key2923, 1), (key3008, 1), (key3010, -1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, -1)]

theorem rowCheck202 : row202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow202 := by decide +kernel

theorem rowEval202 (x : Key → ℝ) : Integer.Sparse.eval row202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck202, Integer.Sparse.eval_collectBalanced, rawRowCheck202]

def rawRow203 : Integer.Sparse Key := [(key3012, -2), (key3017, 1), (key3017, 1), (key3008, 2), (key3026, -1), (key3026, -1), (key3010, -1), (key3010, -1), (key3023, 1), (key3023, 1), (key2753, 2), (key2758, -1), (key2758, -1), (key2658, -2), (key2923, 1), (key2923, 1), (key2660, 1), (key2660, 1), (key2920, -1), (key2920, -1), (key2676, -2), (key2732, 1), (key2732, 1), (key2621, 2), (key2835, -1), (key2835, -1), (key2644, -1), (key2644, -1), (key2798, 1), (key2798, 1), (key2671, 1), (key2671, 1), (key2706, -1), (key2706, -1), (key2616, -1), (key2616, -1), (key2809, 1), (key2809, 1), (key2632, 1), (key2632, 1), (key2786, -1), (key2786, -1)]

theorem rawRowCheck203 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block0.form1 = rawRow203 := by decide +kernel

def row203 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2671, 2), (key2676, -2), (key2706, -2), (key2732, 2), (key2753, 2), (key2758, -2), (key2786, -2), (key2798, 2), (key2809, 2), (key2835, -2), (key2920, -2), (key2923, 2), (key3008, 2), (key3010, -2), (key3012, -2), (key3017, 2), (key3023, 2), (key3026, -2)]

theorem rowCheck203 : row203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow203 := by decide +kernel

theorem rowEval203 (x : Key → ℝ) : Integer.Sparse.eval row203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck203, Integer.Sparse.eval_collectBalanced, rawRowCheck203]

def rawRow204 : Integer.Sparse Key := [(key3017, -2), (key3012, 1), (key3017, 1), (key3026, 2), (key3008, -1), (key3026, -1), (key3023, -1), (key3030, -1), (key3010, 1), (key3030, 1), (key2758, 2), (key2753, -1), (key2758, -1), (key2923, -2), (key2658, 1), (key2923, 1), (key2920, 1), (key2927, 1), (key2660, -1), (key2927, -1), (key2732, -2), (key2676, 1), (key2732, 1), (key2835, 2), (key2621, -1), (key2835, -1), (key2798, -1), (key2885, -1), (key2644, 1), (key2885, 1), (key2706, 1), (key2726, 1), (key2671, -1), (key2726, -1), (key2809, -1), (key2829, -1), (key2616, 1), (key2829, 1), (key2786, 1), (key2870, 1), (key2632, -1), (key2870, -1)]

theorem rawRowCheck204 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block0.form1 = rawRow204 := by decide +kernel

def row204 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, -1), (key2676, 1), (key2706, 1), (key2732, -1), (key2753, -1), (key2758, 1), (key2786, 1), (key2798, -1), (key2809, -1), (key2835, 1), (key2920, 1), (key2923, -1), (key3008, -1), (key3010, 1), (key3012, 1), (key3017, -1), (key3023, -1), (key3026, 1)]

theorem rowCheck204 : row204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow204 := by decide +kernel

theorem rowEval204 (x : Key → ℝ) : Integer.Sparse.eval row204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck204, Integer.Sparse.eval_collectBalanced, rawRowCheck204]

def rawRow205 : Integer.Sparse Key := [(key3017, -2), (key3017, 1), (key3012, 1), (key3026, 2), (key3026, -1), (key3008, -1), (key3030, -1), (key3023, -1), (key3030, 1), (key3010, 1), (key2758, 2), (key2758, -1), (key2753, -1), (key2923, -2), (key2923, 1), (key2658, 1), (key2927, 1), (key2920, 1), (key2927, -1), (key2660, -1), (key2732, -2), (key2732, 1), (key2676, 1), (key2835, 2), (key2835, -1), (key2621, -1), (key2885, -1), (key2798, -1), (key2885, 1), (key2644, 1), (key2726, 1), (key2706, 1), (key2726, -1), (key2671, -1), (key2829, -1), (key2809, -1), (key2829, 1), (key2616, 1), (key2870, 1), (key2786, 1), (key2870, -1), (key2632, -1)]

theorem rawRowCheck205 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block0.form1 = rawRow205 := by decide +kernel

def row205 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, -1), (key2676, 1), (key2706, 1), (key2732, -1), (key2753, -1), (key2758, 1), (key2786, 1), (key2798, -1), (key2809, -1), (key2835, 1), (key2920, 1), (key2923, -1), (key3008, -1), (key3010, 1), (key3012, 1), (key3017, -1), (key3023, -1), (key3026, 1)]

theorem rowCheck205 : row205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow205 := by decide +kernel

theorem rowEval205 (x : Key → ℝ) : Integer.Sparse.eval row205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck205, Integer.Sparse.eval_collectBalanced, rawRowCheck205]

def rawRow206 : Integer.Sparse Key := [(key3023, -2), (key3026, 1), (key3030, 1), (key3010, 2), (key3017, -1), (key3030, -1), (key3008, -1), (key3010, -1), (key3012, 1), (key3023, 1), (key2920, 2), (key2923, -1), (key2927, -1), (key2660, -2), (key2758, 1), (key2927, 1), (key2658, 1), (key2660, 1), (key2753, -1), (key2920, -1), (key2798, -2), (key2835, 1), (key2885, 1), (key2644, 2), (key2732, -1), (key2885, -1), (key2621, -1), (key2644, -1), (key2676, 1), (key2798, 1), (key2786, 1), (key2794, 1), (key2809, -1), (key2860, -1), (key2632, -1), (key2640, -1), (key2706, 1), (key2860, 1), (key2616, 1), (key2640, 1), (key2671, -1), (key2794, -1)]

theorem rawRowCheck206 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block0.form1 = rawRow206 := by decide +kernel

def row206 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, -1), (key2676, 1), (key2706, 1), (key2732, -1), (key2753, -1), (key2758, 1), (key2786, 1), (key2798, -1), (key2809, -1), (key2835, 1), (key2920, 1), (key2923, -1), (key3008, -1), (key3010, 1), (key3012, 1), (key3017, -1), (key3023, -1), (key3026, 1)]

theorem rowCheck206 : row206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow206 := by decide +kernel

theorem rowEval206 (x : Key → ℝ) : Integer.Sparse.eval row206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck206, Integer.Sparse.eval_collectBalanced, rawRowCheck206]

def rawRow207 : Integer.Sparse Key := [(key3023, -2), (key3030, 1), (key3026, 1), (key3010, 2), (key3030, -1), (key3017, -1), (key3010, -1), (key3008, -1), (key3023, 1), (key3012, 1), (key2920, 2), (key2927, -1), (key2923, -1), (key2660, -2), (key2927, 1), (key2758, 1), (key2660, 1), (key2658, 1), (key2920, -1), (key2753, -1), (key2798, -2), (key2885, 1), (key2835, 1), (key2644, 2), (key2885, -1), (key2732, -1), (key2644, -1), (key2621, -1), (key2798, 1), (key2676, 1), (key2794, 1), (key2786, 1), (key2860, -1), (key2809, -1), (key2640, -1), (key2632, -1), (key2860, 1), (key2706, 1), (key2640, 1), (key2616, 1), (key2794, -1), (key2671, -1)]

theorem rawRowCheck207 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block0.form1 = rawRow207 := by decide +kernel

def row207 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, -1), (key2676, 1), (key2706, 1), (key2732, -1), (key2753, -1), (key2758, 1), (key2786, 1), (key2798, -1), (key2809, -1), (key2835, 1), (key2920, 1), (key2923, -1), (key3008, -1), (key3010, 1), (key3012, 1), (key3017, -1), (key3023, -1), (key3026, 1)]

theorem rowCheck207 : row207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow207 := by decide +kernel

theorem rowEval207 (x : Key → ℝ) : Integer.Sparse.eval row207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck207, Integer.Sparse.eval_collectBalanced, rawRowCheck207]

def rawRow208 : Integer.Sparse Key := [(key3026, -2), (key3023, 1), (key3030, 1), (key3017, 2), (key3010, -1), (key3030, -1), (key3012, -1), (key3017, -1), (key3008, 1), (key3026, 1), (key2923, 2), (key2920, -1), (key2927, -1), (key2758, -2), (key2660, 1), (key2927, 1), (key2753, 1), (key2758, 1), (key2658, -1), (key2923, -1), (key2835, -2), (key2798, 1), (key2885, 1), (key2732, 2), (key2644, -1), (key2885, -1), (key2676, -1), (key2732, -1), (key2621, 1), (key2835, 1), (key2809, 1), (key2829, 1), (key2786, -1), (key2870, -1), (key2706, -1), (key2726, -1), (key2632, 1), (key2870, 1), (key2671, 1), (key2726, 1), (key2616, -1), (key2829, -1)]

theorem rawRowCheck208 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block0.form1 = rawRow208 := by decide +kernel

def row208 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2632, 1), (key2644, -1), (key2658, -1), (key2660, 1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2786, -1), (key2798, 1), (key2809, 1), (key2835, -1), (key2920, -1), (key2923, 1), (key3008, 1), (key3010, -1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, -1)]

theorem rowCheck208 : row208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow208 := by decide +kernel

theorem rowEval208 (x : Key → ℝ) : Integer.Sparse.eval row208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck208, Integer.Sparse.eval_collectBalanced, rawRowCheck208]

def rawRow209 : Integer.Sparse Key := [(key3026, -2), (key3030, 1), (key3023, 1), (key3017, 2), (key3030, -1), (key3010, -1), (key3017, -1), (key3012, -1), (key3026, 1), (key3008, 1), (key2923, 2), (key2927, -1), (key2920, -1), (key2758, -2), (key2927, 1), (key2660, 1), (key2758, 1), (key2753, 1), (key2923, -1), (key2658, -1), (key2835, -2), (key2885, 1), (key2798, 1), (key2732, 2), (key2885, -1), (key2644, -1), (key2732, -1), (key2676, -1), (key2835, 1), (key2621, 1), (key2829, 1), (key2809, 1), (key2870, -1), (key2786, -1), (key2726, -1), (key2706, -1), (key2870, 1), (key2632, 1), (key2726, 1), (key2671, 1), (key2829, -1), (key2616, -1)]

theorem rawRowCheck209 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block0.form1 = rawRow209 := by decide +kernel

def row209 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2632, 1), (key2644, -1), (key2658, -1), (key2660, 1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2786, -1), (key2798, 1), (key2809, 1), (key2835, -1), (key2920, -1), (key2923, 1), (key3008, 1), (key3010, -1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, -1)]

theorem rowCheck209 : row209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow209 := by decide +kernel

theorem rowEval209 (x : Key → ℝ) : Integer.Sparse.eval row209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck209, Integer.Sparse.eval_collectBalanced, rawRowCheck209]

def rawRow210 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2614, 2), (key2624, 1), (key2630, 1), (key2630, -1), (key2638, -1), (key2657, -2), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2669, -2), (key2698, -1), (key2704, -1), (key2704, 1), (key2724, 1), (key2752, 2), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2784, 1), (key2792, 1), (key2801, 1), (key2807, 1), (key2807, -1), (key2827, -1), (key2918, -1), (key2919, -1), (key2918, 1), (key2922, 1), (key3007, 2), (key3007, -1), (key3009, -1), (key3011, -2), (key3011, 1), (key3016, 1), (key3021, 1), (key3022, 1), (key3021, -1), (key3025, -1)]

theorem rawRowCheck210 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block0.form2 = rawRow210 := by decide +kernel

def row210 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck210 : row210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow210 := by decide +kernel

theorem rowEval210 (x : Key → ℝ) : Integer.Sparse.eval row210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block0.form2) x := by
  rw [rowCheck210, Integer.Sparse.eval_collectBalanced, rawRowCheck210]

def rawRow211 : Integer.Sparse Key := [(key2614, -1), (key2608, -1), (key2614, 2), (key2630, 1), (key2624, 1), (key2638, -1), (key2630, -1), (key2657, -2), (key2659, 1), (key2657, 1), (key2669, 1), (key2663, 1), (key2669, -2), (key2704, -1), (key2698, -1), (key2724, 1), (key2704, 1), (key2752, 2), (key2757, -1), (key2752, -1), (key2784, -1), (key2778, -1), (key2792, 1), (key2784, 1), (key2807, 1), (key2801, 1), (key2827, -1), (key2807, -1), (key2919, -1), (key2918, -1), (key2922, 1), (key2918, 1), (key3007, 2), (key3009, -1), (key3007, -1), (key3011, -2), (key3016, 1), (key3011, 1), (key3022, 1), (key3021, 1), (key3025, -1), (key3021, -1)]

theorem rawRowCheck211 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block0.form2 = rawRow211 := by decide +kernel

def row211 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck211 : row211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow211 := by decide +kernel

theorem rowEval211 (x : Key → ℝ) : Integer.Sparse.eval row211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck211, Integer.Sparse.eval_collectBalanced, rawRowCheck211]

def rawRow212 : Integer.Sparse Key := [(key2614, -1), (key2614, -1), (key2608, 2), (key2638, 1), (key2638, 1), (key2624, -1), (key2624, -1), (key2659, -2), (key2657, 1), (key2657, 1), (key2669, 1), (key2669, 1), (key2663, -2), (key2724, -1), (key2724, -1), (key2698, 1), (key2698, 1), (key2757, 2), (key2752, -1), (key2752, -1), (key2792, -1), (key2792, -1), (key2778, 1), (key2778, 1), (key2827, 1), (key2827, 1), (key2801, -1), (key2801, -1), (key2922, -1), (key2922, -1), (key2919, 1), (key2919, 1), (key3009, 2), (key3007, -1), (key3007, -1), (key3016, -2), (key3011, 1), (key3011, 1), (key3025, 1), (key3025, 1), (key3022, -1), (key3022, -1)]

theorem rawRowCheck212 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block0.form2 = rawRow212 := by decide +kernel

def row212 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, -2), (key2669, 2), (key2698, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2778, 2), (key2792, -2), (key2801, -2), (key2827, 2), (key2919, 2), (key2922, -2), (key3007, -2), (key3009, 2), (key3011, 2), (key3016, -2), (key3022, -2), (key3025, 2)]

theorem rowCheck212 : row212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow212 := by decide +kernel

theorem rowEval212 (x : Key → ℝ) : Integer.Sparse.eval row212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck212, Integer.Sparse.eval_collectBalanced, rawRowCheck212]

def rawRow213 : Integer.Sparse Key := [(key2624, -1), (key2630, -1), (key2638, 2), (key2608, 1), (key2614, 1), (key2657, -1), (key2659, -1), (key2614, -2), (key2630, 1), (key2638, 1), (key2698, 1), (key2704, 1), (key2752, -2), (key2663, -1), (key2669, -1), (key2752, 1), (key2757, 1), (key2669, 2), (key2704, -1), (key2724, -1), (key2801, -1), (key2807, -1), (key2918, 1), (key2919, 1), (key2778, 1), (key2784, 1), (key2918, -1), (key2922, -1), (key2784, -1), (key2792, -1), (key2807, 1), (key2827, 1), (key3011, 2), (key3021, -1), (key3022, -1), (key3007, -2), (key3021, 1), (key3025, 1), (key3007, 1), (key3009, 1), (key3011, -1), (key3016, -1)]

theorem rawRowCheck213 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block0.form2 = rawRow213 := by decide +kernel

def row213 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 1), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck213 : row213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow213 := by decide +kernel

theorem rowEval213 (x : Key → ℝ) : Integer.Sparse.eval row213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block0.form2) x := by
  rw [rowCheck213, Integer.Sparse.eval_collectBalanced, rawRowCheck213]

def rawRow214 : Integer.Sparse Key := [(key2630, -1), (key2624, -1), (key2638, 2), (key2614, 1), (key2608, 1), (key2659, -1), (key2657, -1), (key2614, -2), (key2638, 1), (key2630, 1), (key2704, 1), (key2698, 1), (key2752, -2), (key2669, -1), (key2663, -1), (key2757, 1), (key2752, 1), (key2669, 2), (key2724, -1), (key2704, -1), (key2807, -1), (key2801, -1), (key2919, 1), (key2918, 1), (key2784, 1), (key2778, 1), (key2922, -1), (key2918, -1), (key2792, -1), (key2784, -1), (key2827, 1), (key2807, 1), (key3011, 2), (key3022, -1), (key3021, -1), (key3007, -2), (key3025, 1), (key3021, 1), (key3009, 1), (key3007, 1), (key3016, -1), (key3011, -1)]

theorem rawRowCheck214 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block0.form2 = rawRow214 := by decide +kernel

def row214 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 1), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck214 : row214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow214 := by decide +kernel

theorem rowEval214 (x : Key → ℝ) : Integer.Sparse.eval row214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck214, Integer.Sparse.eval_collectBalanced, rawRowCheck214]

def rawRow215 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2624, 2), (key2657, 1), (key2659, 1), (key2608, -1), (key2624, -1), (key2638, -2), (key2614, 1), (key2630, 1), (key2704, 1), (key2752, 1), (key2698, -2), (key2724, -1), (key2757, -1), (key2663, 1), (key2698, 1), (key2724, 2), (key2669, -1), (key2704, -1), (key2858, -1), (key2919, -1), (key2801, 1), (key2851, 1), (key2868, 1), (key2922, 1), (key2778, -1), (key2851, -1), (key2827, -1), (key2868, -1), (key2792, 1), (key2858, 1), (key3022, 2), (key3011, -1), (key3021, -1), (key3025, -2), (key3007, 1), (key3021, 1), (key3016, 1), (key3025, 1), (key3009, -1), (key3022, -1)]

theorem rawRowCheck215 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block0.form2 = rawRow215 := by decide +kernel

def row215 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck215 : row215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow215 := by decide +kernel

theorem rowEval215 (x : Key → ℝ) : Integer.Sparse.eval row215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck215, Integer.Sparse.eval_collectBalanced, rawRowCheck215]

def rawRow216 : Integer.Sparse Key := [(key2638, -1), (key2630, -1), (key2624, 2), (key2659, 1), (key2657, 1), (key2624, -1), (key2608, -1), (key2638, -2), (key2630, 1), (key2614, 1), (key2752, 1), (key2704, 1), (key2698, -2), (key2757, -1), (key2724, -1), (key2698, 1), (key2663, 1), (key2724, 2), (key2704, -1), (key2669, -1), (key2919, -1), (key2858, -1), (key2851, 1), (key2801, 1), (key2922, 1), (key2868, 1), (key2851, -1), (key2778, -1), (key2868, -1), (key2827, -1), (key2858, 1), (key2792, 1), (key3022, 2), (key3021, -1), (key3011, -1), (key3025, -2), (key3021, 1), (key3007, 1), (key3025, 1), (key3016, 1), (key3022, -1), (key3009, -1)]

theorem rawRowCheck216 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block0.form2 = rawRow216 := by decide +kernel

def row216 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck216 : row216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow216 := by decide +kernel

theorem rowEval216 (x : Key → ℝ) : Integer.Sparse.eval row216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck216, Integer.Sparse.eval_collectBalanced, rawRowCheck216]

def rawRow217 : Integer.Sparse Key := [(key2657, -1), (key2657, -1), (key2659, 2), (key2614, 1), (key2614, 1), (key2638, -1), (key2638, -1), (key2608, -2), (key2624, 1), (key2624, 1), (key2724, 1), (key2724, 1), (key2757, -2), (key2669, -1), (key2669, -1), (key2752, 1), (key2752, 1), (key2663, 2), (key2698, -1), (key2698, -1), (key2827, -1), (key2827, -1), (key2922, 1), (key2922, 1), (key2792, 1), (key2792, 1), (key2919, -1), (key2919, -1), (key2778, -1), (key2778, -1), (key2801, 1), (key2801, 1), (key3016, 2), (key3025, -1), (key3025, -1), (key3009, -2), (key3022, 1), (key3022, 1), (key3007, 1), (key3007, 1), (key3011, -1), (key3011, -1)]

theorem rawRowCheck217 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block0.form2 = rawRow217 := by decide +kernel

def row217 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, -2), (key2792, 2), (key2801, 2), (key2827, -2), (key2919, -2), (key2922, 2), (key3007, 2), (key3009, -2), (key3011, -2), (key3016, 2), (key3022, 2), (key3025, -2)]

theorem rowCheck217 : row217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow217 := by decide +kernel

theorem rowEval217 (x : Key → ℝ) : Integer.Sparse.eval row217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck217, Integer.Sparse.eval_collectBalanced, rawRowCheck217]

def rawRow218 : Integer.Sparse Key := [(key2657, -1), (key2659, -1), (key2657, 2), (key2630, 1), (key2638, 1), (key2614, -1), (key2630, -1), (key2624, -2), (key2608, 1), (key2624, 1), (key2724, 1), (key2757, 1), (key2724, -2), (key2704, -1), (key2752, -1), (key2669, 1), (key2704, 1), (key2698, 2), (key2663, -1), (key2698, -1), (key2868, -1), (key2922, -1), (key2827, 1), (key2868, 1), (key2858, 1), (key2919, 1), (key2792, -1), (key2858, -1), (key2801, -1), (key2851, -1), (key2778, 1), (key2851, 1), (key3025, 2), (key3016, -1), (key3025, -1), (key3022, -2), (key3009, 1), (key3022, 1), (key3011, 1), (key3021, 1), (key3007, -1), (key3021, -1)]

theorem rawRowCheck218 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block0.form2 = rawRow218 := by decide +kernel

def row218 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 1), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck218 : row218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow218 := by decide +kernel

theorem rowEval218 (x : Key → ℝ) : Integer.Sparse.eval row218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck218, Integer.Sparse.eval_collectBalanced, rawRowCheck218]

def rawRow219 : Integer.Sparse Key := [(key2659, -1), (key2657, -1), (key2657, 2), (key2638, 1), (key2630, 1), (key2630, -1), (key2614, -1), (key2624, -2), (key2624, 1), (key2608, 1), (key2757, 1), (key2724, 1), (key2724, -2), (key2752, -1), (key2704, -1), (key2704, 1), (key2669, 1), (key2698, 2), (key2698, -1), (key2663, -1), (key2922, -1), (key2868, -1), (key2868, 1), (key2827, 1), (key2919, 1), (key2858, 1), (key2858, -1), (key2792, -1), (key2851, -1), (key2801, -1), (key2851, 1), (key2778, 1), (key3025, 2), (key3025, -1), (key3016, -1), (key3022, -2), (key3022, 1), (key3009, 1), (key3021, 1), (key3011, 1), (key3021, -1), (key3007, -1)]

theorem rawRowCheck219 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block0.form2 = rawRow219 := by decide +kernel

def row219 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 1), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck219 : row219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow219 := by decide +kernel

theorem rowEval219 (x : Key → ℝ) : Integer.Sparse.eval row219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck219, Integer.Sparse.eval_collectBalanced, rawRowCheck219]

def rawRow220 : Integer.Sparse Key := [(key2663, -1), (key2669, -1), (key2669, 2), (key2698, 1), (key2704, 1), (key2704, -1), (key2752, -1), (key2724, -2), (key2724, 1), (key2757, 1), (key2608, 1), (key2614, 1), (key2614, -2), (key2801, -1), (key2807, -1), (key2807, 1), (key2827, 1), (key3011, 2), (key3011, -1), (key3016, -1), (key2624, -1), (key2630, -1), (key2630, 1), (key2638, 1), (key2698, 1), (key2704, 1), (key2704, -1), (key2724, -1), (key3021, -1), (key3022, -1), (key3021, 1), (key3025, 1), (key2657, 2), (key2657, -1), (key2659, -1), (key2752, -2), (key2752, 1), (key2757, 1), (key2918, 1), (key2919, 1), (key2918, -1), (key2922, -1)]

theorem rawRowCheck220 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block0.form2 = rawRow220 := by decide +kernel

def row220 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck220 : row220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow220 := by decide +kernel

theorem rowEval220 (x : Key → ℝ) : Integer.Sparse.eval row220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block0.form2) x := by
  rw [rowCheck220, Integer.Sparse.eval_collectBalanced, rawRowCheck220]

def rawRow221 : Integer.Sparse Key := [(key2669, -1), (key2663, -1), (key2669, 2), (key2704, 1), (key2698, 1), (key2752, -1), (key2704, -1), (key2724, -2), (key2757, 1), (key2724, 1), (key2614, 1), (key2608, 1), (key2614, -2), (key2807, -1), (key2801, -1), (key2827, 1), (key2807, 1), (key3011, 2), (key3016, -1), (key3011, -1), (key2630, -1), (key2624, -1), (key2638, 1), (key2630, 1), (key2704, 1), (key2698, 1), (key2724, -1), (key2704, -1), (key3022, -1), (key3021, -1), (key3025, 1), (key3021, 1), (key2657, 2), (key2659, -1), (key2657, -1), (key2752, -2), (key2757, 1), (key2752, 1), (key2919, 1), (key2918, 1), (key2922, -1), (key2918, -1)]

theorem rawRowCheck221 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block0.form2 = rawRow221 := by decide +kernel

def row221 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck221 : row221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow221 := by decide +kernel

theorem rowEval221 (x : Key → ℝ) : Integer.Sparse.eval row221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck221, Integer.Sparse.eval_collectBalanced, rawRowCheck221]

def rawRow222 : Integer.Sparse Key := [(key2669, -1), (key2669, -1), (key2663, 2), (key2752, 1), (key2752, 1), (key2698, -1), (key2698, -1), (key2757, -2), (key2724, 1), (key2724, 1), (key2614, 1), (key2614, 1), (key2608, -2), (key2827, -1), (key2827, -1), (key2801, 1), (key2801, 1), (key3016, 2), (key3011, -1), (key3011, -1), (key2638, -1), (key2638, -1), (key2624, 1), (key2624, 1), (key2724, 1), (key2724, 1), (key2698, -1), (key2698, -1), (key3025, -1), (key3025, -1), (key3022, 1), (key3022, 1), (key2659, 2), (key2657, -1), (key2657, -1), (key2757, -2), (key2752, 1), (key2752, 1), (key2922, 1), (key2922, 1), (key2919, -1), (key2919, -1)]

theorem rawRowCheck222 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block0.form2 = rawRow222 := by decide +kernel

def row222 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -4), (key2724, 4), (key2752, 4), (key2757, -4), (key2801, 2), (key2827, -2), (key2919, -2), (key2922, 2), (key3011, -2), (key3016, 2), (key3022, 2), (key3025, -2)]

theorem rowCheck222 : row222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow222 := by decide +kernel

theorem rowEval222 (x : Key → ℝ) : Integer.Sparse.eval row222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck222, Integer.Sparse.eval_collectBalanced, rawRowCheck222]

def rawRow223 : Integer.Sparse Key := [(key2698, -1), (key2704, -1), (key2724, 2), (key2663, 1), (key2669, 1), (key2724, -1), (key2757, -1), (key2669, -2), (key2704, 1), (key2752, 1), (key2801, 1), (key2807, 1), (key2827, -2), (key2608, -1), (key2614, -1), (key3011, 1), (key3016, 1), (key2614, 2), (key2807, -1), (key2827, -1), (key2698, -1), (key2704, -1), (key3021, 1), (key3022, 1), (key2624, 1), (key2630, 1), (key3021, -1), (key3025, -1), (key2630, -1), (key2638, -1), (key2704, 1), (key2724, 1), (key2752, 2), (key2918, -1), (key2919, -1), (key2657, -2), (key2918, 1), (key2922, 1), (key2657, 1), (key2659, 1), (key2752, -1), (key2757, -1)]

theorem rawRowCheck223 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block0.form2 = rawRow223 := by decide +kernel

def row223 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2801, 1), (key2827, -3), (key2919, -1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck223 : row223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow223 := by decide +kernel

theorem rowEval223 (x : Key → ℝ) : Integer.Sparse.eval row223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block0.form2) x := by
  rw [rowCheck223, Integer.Sparse.eval_collectBalanced, rawRowCheck223]

end MUB6.Certificate.GramRows

end OAI
