import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3456 : Integer.Sparse Key := [(key2630, -1), (key2624, -1), (key3021, -1), (key2851, -1), (key3025, -1), (key2868, -1), (key2638, 2), (key3022, 2), (key2858, 2), (key2614, 1), (key2608, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key3011, 1), (key2659, -1), (key2657, -1), (key2757, -1), (key2752, -1), (key2922, -1), (key2919, -1), (key2614, -2), (key2827, -2), (key2807, -2), (key2638, 1), (key2630, 1), (key2724, 1), (key2704, 1), (key2868, 1), (key2858, 1)]

theorem rawRowCheck3456 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form15 = rawRow3456 := by decide +kernel

def row3456 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

theorem rowCheck3456 : row3456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3456 := by decide +kernel

theorem rowEval3456 (x : Key → ℝ) : Integer.Sparse.eval row3456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3456, Integer.Sparse.eval_collectBalanced, rawRowCheck3456]

def rawRow3457 : Integer.Sparse Key := [(key2851, -1), (key2868, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2858, 2), (key2638, 2), (key3022, 2), (key2801, 1), (key2827, 1), (key2608, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2752, -1), (key2919, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2807, -2), (key2614, -2), (key2827, -2), (key2704, 1), (key2858, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2724, 1)]

theorem rawRowCheck3457 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form15 = rawRow3457 := by decide +kernel

def row3457 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

theorem rowCheck3457 : row3457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3457 := by decide +kernel

theorem rowEval3457 (x : Key → ℝ) : Integer.Sparse.eval row3457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3457, Integer.Sparse.eval_collectBalanced, rawRowCheck3457]

def rawRow3458 : Integer.Sparse Key := [(key2868, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key3021, -1), (key2630, -1), (key2858, 2), (key3022, 2), (key2638, 2), (key2827, 1), (key2801, 1), (key3016, 1), (key2608, 1), (key2827, 1), (key2614, 1), (key2919, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2757, -1), (key2659, -1), (key2807, -2), (key2827, -2), (key2614, -2), (key2858, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2724, 1), (key2638, 1)]

theorem rawRowCheck3458 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form15 = rawRow3458 := by decide +kernel

def row3458 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

theorem rowCheck3458 : row3458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3458 := by decide +kernel

theorem rowEval3458 (x : Key → ℝ) : Integer.Sparse.eval row3458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3458, Integer.Sparse.eval_collectBalanced, rawRowCheck3458]

def rawRow3459 : Integer.Sparse Key := [(key3021, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2624, -1), (key2851, -1), (key3022, 2), (key2638, 2), (key2858, 2), (key3011, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2608, 1), (key2801, 1), (key2757, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2657, -1), (key2752, -1), (key2827, -2), (key2614, -2), (key2807, -2), (key2724, 1), (key2868, 1), (key2638, 1), (key2858, 1), (key2630, 1), (key2704, 1)]

theorem rawRowCheck3459 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form15 = rawRow3459 := by decide +kernel

def row3459 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

theorem rowCheck3459 : row3459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3459 := by decide +kernel

theorem rowEval3459 (x : Key → ℝ) : Integer.Sparse.eval row3459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3459, Integer.Sparse.eval_collectBalanced, rawRowCheck3459]

def rawRow3460 : Integer.Sparse Key := [(key3025, -1), (key3021, -1), (key2868, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key3022, 2), (key2858, 2), (key2638, 2), (key3016, 1), (key3011, 1), (key2827, 1), (key2614, 1), (key2801, 1), (key2608, 1), (key2922, -1), (key2757, -1), (key2919, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2827, -2), (key2807, -2), (key2614, -2), (key2868, 1), (key2724, 1), (key2858, 1), (key2638, 1), (key2704, 1), (key2630, 1)]

theorem rawRowCheck3460 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form15 = rawRow3460 := by decide +kernel

def row3460 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

theorem rowCheck3460 : row3460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3460 := by decide +kernel

theorem rowEval3460 (x : Key → ℝ) : Integer.Sparse.eval row3460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3460, Integer.Sparse.eval_collectBalanced, rawRowCheck3460]

def rawRow3461 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2704, -1), (key2858, -1), (key2724, -1), (key2868, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2657, 1), (key2659, 1), (key2752, 1), (key2919, 1), (key2757, 1), (key2922, 1), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1), (key2638, -2), (key2792, -2), (key2858, -2), (key2614, 1), (key2630, 1), (key2669, 1), (key2704, 1), (key2784, 1), (key2807, 1)]

theorem rawRowCheck3461 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form15 = rawRow3461 := by decide +kernel

def row3461 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, -1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

theorem rowCheck3461 : row3461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3461 := by decide +kernel

theorem rowEval3461 (x : Key → ℝ) : Integer.Sparse.eval row3461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3461, Integer.Sparse.eval_collectBalanced, rawRowCheck3461]

def rawRow3462 : Integer.Sparse Key := [(key2638, -1), (key2630, -1), (key2858, -1), (key2704, -1), (key2868, -1), (key2724, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2659, 1), (key2657, 1), (key2919, 1), (key2752, 1), (key2922, 1), (key2757, 1), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1), (key2638, -2), (key2858, -2), (key2792, -2), (key2630, 1), (key2614, 1), (key2704, 1), (key2669, 1), (key2807, 1), (key2784, 1)]

theorem rawRowCheck3462 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form15 = rawRow3462 := by decide +kernel

def row3462 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, -1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

theorem rowCheck3462 : row3462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3462 := by decide +kernel

theorem rowEval3462 (x : Key → ℝ) : Integer.Sparse.eval row3462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck3462, Integer.Sparse.eval_collectBalanced, rawRowCheck3462]

def rawRow3463 : Integer.Sparse Key := [(key2704, -1), (key2724, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2752, 1), (key2757, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2919, 1), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2792, -2), (key2638, -2), (key2858, -2), (key2669, 1), (key2784, 1), (key2614, 1), (key2807, 1), (key2630, 1), (key2704, 1)]

theorem rawRowCheck3463 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form15 = rawRow3463 := by decide +kernel

def row3463 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

theorem rowCheck3463 : row3463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3463 := by decide +kernel

theorem rowEval3463 (x : Key → ℝ) : Integer.Sparse.eval row3463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3463, Integer.Sparse.eval_collectBalanced, rawRowCheck3463]

def rawRow3464 : Integer.Sparse Key := [(key2724, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2858, -1), (key2638, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2757, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2919, 1), (key2659, 1), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1), (key2792, -2), (key2858, -2), (key2638, -2), (key2784, 1), (key2669, 1), (key2807, 1), (key2614, 1), (key2704, 1), (key2630, 1)]

theorem rawRowCheck3464 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form15 = rawRow3464 := by decide +kernel

def row3464 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

theorem rowCheck3464 : row3464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3464 := by decide +kernel

theorem rowEval3464 (x : Key → ℝ) : Integer.Sparse.eval row3464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3464, Integer.Sparse.eval_collectBalanced, rawRowCheck3464]

def rawRow3465 : Integer.Sparse Key := [(key2858, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2630, -1), (key2704, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2919, 1), (key2922, 1), (key2659, 1), (key2757, 1), (key2657, 1), (key2752, 1), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1), (key2858, -2), (key2638, -2), (key2792, -2), (key2704, 1), (key2807, 1), (key2630, 1), (key2784, 1), (key2614, 1), (key2669, 1)]

theorem rawRowCheck3465 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form15 = rawRow3465 := by decide +kernel

def row3465 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, -1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

theorem rowCheck3465 : row3465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3465 := by decide +kernel

theorem rowEval3465 (x : Key → ℝ) : Integer.Sparse.eval row3465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck3465, Integer.Sparse.eval_collectBalanced, rawRowCheck3465]

def rawRow3466 : Integer.Sparse Key := [(key2868, -1), (key2858, -1), (key2724, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2922, 1), (key2919, 1), (key2757, 1), (key2659, 1), (key2752, 1), (key2657, 1), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1), (key2858, -2), (key2792, -2), (key2638, -2), (key2807, 1), (key2704, 1), (key2784, 1), (key2630, 1), (key2669, 1), (key2614, 1)]

theorem rawRowCheck3466 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form15 = rawRow3466 := by decide +kernel

def row3466 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, -1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

theorem rowCheck3466 : row3466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3466 := by decide +kernel

theorem rowEval3466 (x : Key → ℝ) : Integer.Sparse.eval row3466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3466, Integer.Sparse.eval_collectBalanced, rawRowCheck3466]

def rawRow3467 : Integer.Sparse Key := [(key2657, -1), (key2657, -1), (key2918, -1), (key2918, -1), (key2922, -1), (key2922, -1), (key2659, 2), (key2919, 2), (key2919, 2), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1), (key2638, -1), (key2638, -1), (key2792, -1), (key2792, -1), (key2858, -1), (key2858, -1), (key2608, -2), (key2801, -2), (key2801, -2), (key2624, 1), (key2624, 1), (key2698, 1), (key2698, 1), (key2851, 1), (key2851, 1)]

theorem rawRowCheck3467 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form15 = rawRow3467 := by decide +kernel

def row3467 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, 2), (key2792, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, -2), (key2918, -2), (key2919, 4), (key2922, -2)]

theorem rowCheck3467 : row3467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3467 := by decide +kernel

theorem rowEval3467 (x : Key → ℝ) : Integer.Sparse.eval row3467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3467, Integer.Sparse.eval_collectBalanced, rawRowCheck3467]

def rawRow3468 : Integer.Sparse Key := [(key2918, -1), (key2922, -1), (key2657, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2919, 2), (key2659, 2), (key2919, 2), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2792, -1), (key2858, -1), (key2638, -1), (key2858, -1), (key2638, -1), (key2792, -1), (key2801, -2), (key2608, -2), (key2801, -2), (key2698, 1), (key2851, 1), (key2624, 1), (key2851, 1), (key2624, 1), (key2698, 1)]

theorem rawRowCheck3468 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form15 = rawRow3468 := by decide +kernel

def row3468 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, 2), (key2792, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, -2), (key2918, -2), (key2919, 4), (key2922, -2)]

theorem rowCheck3468 : row3468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3468 := by decide +kernel

theorem rowEval3468 (x : Key → ℝ) : Integer.Sparse.eval row3468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3468, Integer.Sparse.eval_collectBalanced, rawRowCheck3468]

def rawRow3469 : Integer.Sparse Key := [(key2922, -1), (key2918, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2657, -1), (key2919, 2), (key2919, 2), (key2659, 2), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1), (key2858, -1), (key2792, -1), (key2858, -1), (key2638, -1), (key2792, -1), (key2638, -1), (key2801, -2), (key2801, -2), (key2608, -2), (key2851, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2624, 1)]

theorem rawRowCheck3469 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form15 = rawRow3469 := by decide +kernel

def row3469 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, 2), (key2792, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, -2), (key2918, -2), (key2919, 4), (key2922, -2)]

theorem rowCheck3469 : row3469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3469 := by decide +kernel

theorem rowEval3469 (x : Key → ℝ) : Integer.Sparse.eval row3469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3469, Integer.Sparse.eval_collectBalanced, rawRowCheck3469]

def rawRow3470 : Integer.Sparse Key := [(key2657, -1), (key2659, -1), (key2752, -1), (key2919, -1), (key2757, -1), (key2922, -1), (key2657, 2), (key2752, 2), (key2918, 2), (key2630, 1), (key2638, 1), (key2704, 1), (key2858, 1), (key2724, 1), (key2868, 1), (key2614, -1), (key2630, -1), (key2669, -1), (key2784, -1), (key2704, -1), (key2807, -1), (key2624, -2), (key2698, -2), (key2851, -2), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1)]

theorem rawRowCheck3470 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form15 = rawRow3470 := by decide +kernel

def row3470 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck3470 : row3470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3470 := by decide +kernel

theorem rowEval3470 (x : Key → ℝ) : Integer.Sparse.eval row3470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3470, Integer.Sparse.eval_collectBalanced, rawRowCheck3470]

def rawRow3471 : Integer.Sparse Key := [(key2659, -1), (key2657, -1), (key2919, -1), (key2752, -1), (key2922, -1), (key2757, -1), (key2657, 2), (key2918, 2), (key2752, 2), (key2638, 1), (key2630, 1), (key2858, 1), (key2704, 1), (key2868, 1), (key2724, 1), (key2630, -1), (key2614, -1), (key2784, -1), (key2669, -1), (key2807, -1), (key2704, -1), (key2624, -2), (key2851, -2), (key2698, -2), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1)]

theorem rawRowCheck3471 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form15 = rawRow3471 := by decide +kernel

def row3471 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck3471 : row3471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3471 := by decide +kernel

theorem rowEval3471 (x : Key → ℝ) : Integer.Sparse.eval row3471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck3471, Integer.Sparse.eval_collectBalanced, rawRowCheck3471]

def rawRow3472 : Integer.Sparse Key := [(key2752, -1), (key2757, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2752, 2), (key2657, 2), (key2918, 2), (key2704, 1), (key2724, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2858, 1), (key2669, -1), (key2704, -1), (key2614, -1), (key2807, -1), (key2630, -1), (key2784, -1), (key2698, -2), (key2624, -2), (key2851, -2), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1)]

theorem rawRowCheck3472 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form15 = rawRow3472 := by decide +kernel

def row3472 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck3472 : row3472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3472 := by decide +kernel

theorem rowEval3472 (x : Key → ℝ) : Integer.Sparse.eval row3472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3472, Integer.Sparse.eval_collectBalanced, rawRowCheck3472]

def rawRow3473 : Integer.Sparse Key := [(key2757, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2919, -1), (key2659, -1), (key2752, 2), (key2918, 2), (key2657, 2), (key2724, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2858, 1), (key2638, 1), (key2704, -1), (key2669, -1), (key2807, -1), (key2614, -1), (key2784, -1), (key2630, -1), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1)]

theorem rawRowCheck3473 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form15 = rawRow3473 := by decide +kernel

def row3473 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck3473 : row3473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3473 := by decide +kernel

theorem rowEval3473 (x : Key → ℝ) : Integer.Sparse.eval row3473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3473, Integer.Sparse.eval_collectBalanced, rawRowCheck3473]

def rawRow3474 : Integer.Sparse Key := [(key2919, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2657, -1), (key2752, -1), (key2918, 2), (key2657, 2), (key2752, 2), (key2858, 1), (key2868, 1), (key2638, 1), (key2724, 1), (key2630, 1), (key2704, 1), (key2784, -1), (key2807, -1), (key2630, -1), (key2704, -1), (key2614, -1), (key2669, -1), (key2851, -2), (key2624, -2), (key2698, -2), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1)]

theorem rawRowCheck3474 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form15 = rawRow3474 := by decide +kernel

def row3474 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck3474 : row3474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3474 := by decide +kernel

theorem rowEval3474 (x : Key → ℝ) : Integer.Sparse.eval row3474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck3474, Integer.Sparse.eval_collectBalanced, rawRowCheck3474]

def rawRow3475 : Integer.Sparse Key := [(key2922, -1), (key2919, -1), (key2757, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2918, 2), (key2752, 2), (key2657, 2), (key2868, 1), (key2858, 1), (key2724, 1), (key2638, 1), (key2704, 1), (key2630, 1), (key2807, -1), (key2784, -1), (key2704, -1), (key2630, -1), (key2669, -1), (key2614, -1), (key2851, -2), (key2698, -2), (key2624, -2), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1)]

theorem rawRowCheck3475 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form15 = rawRow3475 := by decide +kernel

def row3475 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck3475 : row3475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3475 := by decide +kernel

theorem rowEval3475 (x : Key → ℝ) : Integer.Sparse.eval row3475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3475, Integer.Sparse.eval_collectBalanced, rawRowCheck3475]

def rawRow3476 : Integer.Sparse Key := [(key2674, -2), (key2796, -2), (key2796, -2), (key2671, 1), (key2671, 1), (key2786, 1), (key2786, 1), (key2794, 1), (key2794, 1), (key2738, 2), (key2898, 2), (key2898, 2), (key2706, -1), (key2706, -1), (key2809, -1), (key2809, -1), (key2860, -1), (key2860, -1), (key2748, -1), (key2748, -1), (key2905, -1), (key2905, -1), (key2913, -1), (key2913, -1), (key2729, 1), (key2729, 1), (key2832, 1), (key2832, 1), (key2883, 1), (key2883, 1)]

theorem rawRowCheck3476 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form0 = rawRow3476 := by decide +kernel

def row3476 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, 2), (key2796, -4), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2898, 4), (key2905, -2), (key2913, -2)]

theorem rowCheck3476 : row3476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3476 := by decide +kernel

theorem rowEval3476 (x : Key → ℝ) : Integer.Sparse.eval row3476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3476, Integer.Sparse.eval_collectBalanced, rawRowCheck3476]

def rawRow3477 : Integer.Sparse Key := [(key2796, -2), (key2674, -2), (key2796, -2), (key2786, 1), (key2794, 1), (key2671, 1), (key2794, 1), (key2671, 1), (key2786, 1), (key2898, 2), (key2738, 2), (key2898, 2), (key2809, -1), (key2860, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key2809, -1), (key2905, -1), (key2913, -1), (key2748, -1), (key2913, -1), (key2748, -1), (key2905, -1), (key2832, 1), (key2883, 1), (key2729, 1), (key2883, 1), (key2729, 1), (key2832, 1)]

theorem rawRowCheck3477 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form0 = rawRow3477 := by decide +kernel

def row3477 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, 2), (key2796, -4), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2898, 4), (key2905, -2), (key2913, -2)]

theorem rowCheck3477 : row3477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3477 := by decide +kernel

theorem rowEval3477 (x : Key → ℝ) : Integer.Sparse.eval row3477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3477, Integer.Sparse.eval_collectBalanced, rawRowCheck3477]

def rawRow3478 : Integer.Sparse Key := [(key2796, -2), (key2796, -2), (key2674, -2), (key2794, 1), (key2786, 1), (key2794, 1), (key2671, 1), (key2786, 1), (key2671, 1), (key2898, 2), (key2898, 2), (key2738, 2), (key2860, -1), (key2809, -1), (key2860, -1), (key2706, -1), (key2809, -1), (key2706, -1), (key2913, -1), (key2905, -1), (key2913, -1), (key2748, -1), (key2905, -1), (key2748, -1), (key2883, 1), (key2832, 1), (key2883, 1), (key2729, 1), (key2832, 1), (key2729, 1)]

theorem rawRowCheck3478 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form0 = rawRow3478 := by decide +kernel

def row3478 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, 2), (key2796, -4), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2898, 4), (key2905, -2), (key2913, -2)]

theorem rowCheck3478 : row3478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3478 := by decide +kernel

theorem rowEval3478 (x : Key → ℝ) : Integer.Sparse.eval row3478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck3478, Integer.Sparse.eval_collectBalanced, rawRowCheck3478]

def rawRow3479 : Integer.Sparse Key := [(key2619, -2), (key2832, -2), (key2832, -2), (key2616, 1), (key2616, 1), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2649, 2), (key2905, 2), (key2905, 2), (key2632, -1), (key2632, -1), (key2786, -1), (key2786, -1), (key2870, -1), (key2870, -1), (key2654, -1), (key2654, -1), (key2898, -1), (key2898, -1), (key2913, -1), (key2913, -1), (key2642, 1), (key2642, 1), (key2796, 1), (key2796, 1), (key2883, 1), (key2883, 1)]

theorem rawRowCheck3479 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form0 = rawRow3479 := by decide +kernel

def row3479 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2898, -2), (key2905, 4), (key2913, -2)]

theorem rowCheck3479 : row3479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3479 := by decide +kernel

theorem rowEval3479 (x : Key → ℝ) : Integer.Sparse.eval row3479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3479, Integer.Sparse.eval_collectBalanced, rawRowCheck3479]

def rawRow3480 : Integer.Sparse Key := [(key2832, -2), (key2619, -2), (key2832, -2), (key2809, 1), (key2829, 1), (key2616, 1), (key2829, 1), (key2616, 1), (key2809, 1), (key2905, 2), (key2649, 2), (key2905, 2), (key2786, -1), (key2870, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2786, -1), (key2898, -1), (key2913, -1), (key2654, -1), (key2913, -1), (key2654, -1), (key2898, -1), (key2796, 1), (key2883, 1), (key2642, 1), (key2883, 1), (key2642, 1), (key2796, 1)]

theorem rawRowCheck3480 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form0 = rawRow3480 := by decide +kernel

def row3480 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2898, -2), (key2905, 4), (key2913, -2)]

theorem rowCheck3480 : row3480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3480 := by decide +kernel

theorem rowEval3480 (x : Key → ℝ) : Integer.Sparse.eval row3480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3480, Integer.Sparse.eval_collectBalanced, rawRowCheck3480]

def rawRow3481 : Integer.Sparse Key := [(key2832, -2), (key2832, -2), (key2619, -2), (key2829, 1), (key2809, 1), (key2829, 1), (key2616, 1), (key2809, 1), (key2616, 1), (key2905, 2), (key2905, 2), (key2649, 2), (key2870, -1), (key2786, -1), (key2870, -1), (key2632, -1), (key2786, -1), (key2632, -1), (key2913, -1), (key2898, -1), (key2913, -1), (key2654, -1), (key2898, -1), (key2654, -1), (key2883, 1), (key2796, 1), (key2883, 1), (key2642, 1), (key2796, 1), (key2642, 1)]

theorem rawRowCheck3481 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form0 = rawRow3481 := by decide +kernel

def row3481 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2898, -2), (key2905, 4), (key2913, -2)]

theorem rowCheck3481 : row3481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3481 := by decide +kernel

theorem rowEval3481 (x : Key → ℝ) : Integer.Sparse.eval row3481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3481, Integer.Sparse.eval_collectBalanced, rawRowCheck3481]

def rawRow3482 : Integer.Sparse Key := [(key2738, -2), (key2898, -2), (key2898, -2), (key2748, 1), (key2748, 1), (key2905, 1), (key2905, 1), (key2913, 1), (key2913, 1), (key2674, 2), (key2796, 2), (key2796, 2), (key2729, -1), (key2729, -1), (key2832, -1), (key2832, -1), (key2883, -1), (key2883, -1), (key2671, -1), (key2671, -1), (key2786, -1), (key2786, -1), (key2794, -1), (key2794, -1), (key2706, 1), (key2706, 1), (key2809, 1), (key2809, 1), (key2860, 1), (key2860, 1)]

theorem rawRowCheck3482 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form0 = rawRow3482 := by decide +kernel

def row3482 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, -2), (key2794, -2), (key2796, 4), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2898, -4), (key2905, 2), (key2913, 2)]

theorem rowCheck3482 : row3482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3482 := by decide +kernel

theorem rowEval3482 (x : Key → ℝ) : Integer.Sparse.eval row3482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3482, Integer.Sparse.eval_collectBalanced, rawRowCheck3482]

def rawRow3483 : Integer.Sparse Key := [(key2898, -2), (key2738, -2), (key2898, -2), (key2905, 1), (key2913, 1), (key2748, 1), (key2913, 1), (key2748, 1), (key2905, 1), (key2796, 2), (key2674, 2), (key2796, 2), (key2832, -1), (key2883, -1), (key2729, -1), (key2883, -1), (key2729, -1), (key2832, -1), (key2786, -1), (key2794, -1), (key2671, -1), (key2794, -1), (key2671, -1), (key2786, -1), (key2809, 1), (key2860, 1), (key2706, 1), (key2860, 1), (key2706, 1), (key2809, 1)]

theorem rawRowCheck3483 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form0 = rawRow3483 := by decide +kernel

def row3483 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, -2), (key2794, -2), (key2796, 4), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2898, -4), (key2905, 2), (key2913, 2)]

theorem rowCheck3483 : row3483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3483 := by decide +kernel

theorem rowEval3483 (x : Key → ℝ) : Integer.Sparse.eval row3483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3483, Integer.Sparse.eval_collectBalanced, rawRowCheck3483]

def rawRow3484 : Integer.Sparse Key := [(key2898, -2), (key2898, -2), (key2738, -2), (key2913, 1), (key2905, 1), (key2913, 1), (key2748, 1), (key2905, 1), (key2748, 1), (key2796, 2), (key2796, 2), (key2674, 2), (key2883, -1), (key2832, -1), (key2883, -1), (key2729, -1), (key2832, -1), (key2729, -1), (key2794, -1), (key2786, -1), (key2794, -1), (key2671, -1), (key2786, -1), (key2671, -1), (key2860, 1), (key2809, 1), (key2860, 1), (key2706, 1), (key2809, 1), (key2706, 1)]

theorem rawRowCheck3484 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form0 = rawRow3484 := by decide +kernel

def row3484 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, -2), (key2794, -2), (key2796, 4), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2898, -4), (key2905, 2), (key2913, 2)]

theorem rowCheck3484 : row3484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3484 := by decide +kernel

theorem rowEval3484 (x : Key → ℝ) : Integer.Sparse.eval row3484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck3484, Integer.Sparse.eval_collectBalanced, rawRowCheck3484]

def rawRow3485 : Integer.Sparse Key := [(key2649, -2), (key2905, -2), (key2905, -2), (key2654, 1), (key2654, 1), (key2898, 1), (key2898, 1), (key2913, 1), (key2913, 1), (key2619, 2), (key2832, 2), (key2832, 2), (key2642, -1), (key2642, -1), (key2796, -1), (key2796, -1), (key2883, -1), (key2883, -1), (key2616, -1), (key2616, -1), (key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2632, 1), (key2632, 1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1)]

theorem rawRowCheck3485 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form0 = rawRow3485 := by decide +kernel

def row3485 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2898, 2), (key2905, -4), (key2913, 2)]

theorem rowCheck3485 : row3485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3485 := by decide +kernel

theorem rowEval3485 (x : Key → ℝ) : Integer.Sparse.eval row3485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3485, Integer.Sparse.eval_collectBalanced, rawRowCheck3485]

def rawRow3486 : Integer.Sparse Key := [(key2905, -2), (key2649, -2), (key2905, -2), (key2898, 1), (key2913, 1), (key2654, 1), (key2913, 1), (key2654, 1), (key2898, 1), (key2832, 2), (key2619, 2), (key2832, 2), (key2796, -1), (key2883, -1), (key2642, -1), (key2883, -1), (key2642, -1), (key2796, -1), (key2809, -1), (key2829, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2809, -1), (key2786, 1), (key2870, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2786, 1)]

theorem rawRowCheck3486 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form0 = rawRow3486 := by decide +kernel

def row3486 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2898, 2), (key2905, -4), (key2913, 2)]

theorem rowCheck3486 : row3486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3486 := by decide +kernel

theorem rowEval3486 (x : Key → ℝ) : Integer.Sparse.eval row3486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3486, Integer.Sparse.eval_collectBalanced, rawRowCheck3486]

def rawRow3487 : Integer.Sparse Key := [(key2905, -2), (key2905, -2), (key2649, -2), (key2913, 1), (key2898, 1), (key2913, 1), (key2654, 1), (key2898, 1), (key2654, 1), (key2832, 2), (key2832, 2), (key2619, 2), (key2883, -1), (key2796, -1), (key2883, -1), (key2642, -1), (key2796, -1), (key2642, -1), (key2829, -1), (key2809, -1), (key2829, -1), (key2616, -1), (key2809, -1), (key2616, -1), (key2870, 1), (key2786, 1), (key2870, 1), (key2632, 1), (key2786, 1), (key2632, 1)]

theorem rawRowCheck3487 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form0 = rawRow3487 := by decide +kernel

def row3487 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2898, 2), (key2905, -4), (key2913, 2)]

theorem rowCheck3487 : row3487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3487 := by decide +kernel

theorem rowEval3487 (x : Key → ℝ) : Integer.Sparse.eval row3487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3487, Integer.Sparse.eval_collectBalanced, rawRowCheck3487]

def rawRow3488 : Integer.Sparse Key := [(key1334, -6), (key1288, 2), (key1308, 2), (key1308, 2), (key1769, 6), (key1383, -2), (key1538, -2), (key1538, -2), (key1785, -2), (key1810, -2), (key1810, -2), (key1452, 2), (key1652, 2), (key1652, 2)]

theorem rawRowCheck3488 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form1 = rawRow3488 := by decide +kernel

def row3488 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, -2), (key1452, 2), (key1538, -4), (key1652, 4), (key1769, 6), (key1785, -2), (key1810, -4)]

theorem rowCheck3488 : row3488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3488 := by decide +kernel

theorem rowEval3488 (x : Key → ℝ) : Integer.Sparse.eval row3488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3488, Integer.Sparse.eval_collectBalanced, rawRowCheck3488]

def rawRow3489 : Integer.Sparse Key := [(key1334, -6), (key1308, 2), (key1288, 2), (key1308, 2), (key1769, 6), (key1538, -2), (key1383, -2), (key1538, -2), (key1810, -2), (key1785, -2), (key1810, -2), (key1652, 2), (key1452, 2), (key1652, 2)]

theorem rawRowCheck3489 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form1 = rawRow3489 := by decide +kernel

def row3489 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, -2), (key1452, 2), (key1538, -4), (key1652, 4), (key1769, 6), (key1785, -2), (key1810, -4)]

theorem rowCheck3489 : row3489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3489 := by decide +kernel

theorem rowEval3489 (x : Key → ℝ) : Integer.Sparse.eval row3489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3489, Integer.Sparse.eval_collectBalanced, rawRowCheck3489]

def rawRow3490 : Integer.Sparse Key := [(key1334, -6), (key1308, 2), (key1308, 2), (key1288, 2), (key1769, 6), (key1538, -2), (key1538, -2), (key1383, -2), (key1810, -2), (key1810, -2), (key1785, -2), (key1652, 2), (key1652, 2), (key1452, 2)]

theorem rawRowCheck3490 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form1 = rawRow3490 := by decide +kernel

def row3490 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, -2), (key1452, 2), (key1538, -4), (key1652, 4), (key1769, 6), (key1785, -2), (key1810, -4)]

theorem rowCheck3490 : row3490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3490 := by decide +kernel

theorem rowEval3490 (x : Key → ℝ) : Integer.Sparse.eval row3490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3490, Integer.Sparse.eval_collectBalanced, rawRowCheck3490]

def rawRow3491 : Integer.Sparse Key := [(key1452, -6), (key1383, 2), (key1416, 2), (key1416, 2), (key1785, 6), (key1288, -2), (key1565, -2), (key1565, -2), (key1769, -2), (key1810, -2), (key1810, -2), (key1334, 2), (key1652, 2), (key1652, 2)]

theorem rawRowCheck3491 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow3491 := by decide +kernel

def row3491 : Integer.Sparse Key := [(key1288, -2), (key1334, 2), (key1383, 2), (key1416, 4), (key1452, -6), (key1565, -4), (key1652, 4), (key1769, -2), (key1785, 6), (key1810, -4)]

theorem rowCheck3491 : row3491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3491 := by decide +kernel

theorem rowEval3491 (x : Key → ℝ) : Integer.Sparse.eval row3491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3491, Integer.Sparse.eval_collectBalanced, rawRowCheck3491]

def rawRow3492 : Integer.Sparse Key := [(key1452, -6), (key1416, 2), (key1383, 2), (key1416, 2), (key1785, 6), (key1565, -2), (key1288, -2), (key1565, -2), (key1810, -2), (key1769, -2), (key1810, -2), (key1652, 2), (key1334, 2), (key1652, 2)]

theorem rawRowCheck3492 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow3492 := by decide +kernel

def row3492 : Integer.Sparse Key := [(key1288, -2), (key1334, 2), (key1383, 2), (key1416, 4), (key1452, -6), (key1565, -4), (key1652, 4), (key1769, -2), (key1785, 6), (key1810, -4)]

theorem rowCheck3492 : row3492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3492 := by decide +kernel

theorem rowEval3492 (x : Key → ℝ) : Integer.Sparse.eval row3492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3492, Integer.Sparse.eval_collectBalanced, rawRowCheck3492]

def rawRow3493 : Integer.Sparse Key := [(key1452, -6), (key1416, 2), (key1416, 2), (key1383, 2), (key1785, 6), (key1565, -2), (key1565, -2), (key1288, -2), (key1810, -2), (key1810, -2), (key1769, -2), (key1652, 2), (key1652, 2), (key1334, 2)]

theorem rawRowCheck3493 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow3493 := by decide +kernel

def row3493 : Integer.Sparse Key := [(key1288, -2), (key1334, 2), (key1383, 2), (key1416, 4), (key1452, -6), (key1565, -4), (key1652, 4), (key1769, -2), (key1785, 6), (key1810, -4)]

theorem rowCheck3493 : row3493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3493 := by decide +kernel

theorem rowEval3493 (x : Key → ℝ) : Integer.Sparse.eval row3493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3493, Integer.Sparse.eval_collectBalanced, rawRowCheck3493]

def rawRow3494 : Integer.Sparse Key := [(key1769, -6), (key1785, 2), (key1810, 2), (key1810, 2), (key1334, 6), (key1452, -2), (key1652, -2), (key1652, -2), (key1288, -2), (key1308, -2), (key1308, -2), (key1383, 2), (key1538, 2), (key1538, 2)]

theorem rawRowCheck3494 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form1 = rawRow3494 := by decide +kernel

def row3494 : Integer.Sparse Key := [(key1288, -2), (key1308, -4), (key1334, 6), (key1383, 2), (key1452, -2), (key1538, 4), (key1652, -4), (key1769, -6), (key1785, 2), (key1810, 4)]

theorem rowCheck3494 : row3494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3494 := by decide +kernel

theorem rowEval3494 (x : Key → ℝ) : Integer.Sparse.eval row3494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3494, Integer.Sparse.eval_collectBalanced, rawRowCheck3494]

def rawRow3495 : Integer.Sparse Key := [(key1769, -6), (key1810, 2), (key1785, 2), (key1810, 2), (key1334, 6), (key1652, -2), (key1452, -2), (key1652, -2), (key1308, -2), (key1288, -2), (key1308, -2), (key1538, 2), (key1383, 2), (key1538, 2)]

theorem rawRowCheck3495 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form1 = rawRow3495 := by decide +kernel

def row3495 : Integer.Sparse Key := [(key1288, -2), (key1308, -4), (key1334, 6), (key1383, 2), (key1452, -2), (key1538, 4), (key1652, -4), (key1769, -6), (key1785, 2), (key1810, 4)]

theorem rowCheck3495 : row3495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3495 := by decide +kernel

theorem rowEval3495 (x : Key → ℝ) : Integer.Sparse.eval row3495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3495, Integer.Sparse.eval_collectBalanced, rawRowCheck3495]

def rawRow3496 : Integer.Sparse Key := [(key1769, -6), (key1810, 2), (key1810, 2), (key1785, 2), (key1334, 6), (key1652, -2), (key1652, -2), (key1452, -2), (key1308, -2), (key1308, -2), (key1288, -2), (key1538, 2), (key1538, 2), (key1383, 2)]

theorem rawRowCheck3496 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form1 = rawRow3496 := by decide +kernel

def row3496 : Integer.Sparse Key := [(key1288, -2), (key1308, -4), (key1334, 6), (key1383, 2), (key1452, -2), (key1538, 4), (key1652, -4), (key1769, -6), (key1785, 2), (key1810, 4)]

theorem rowCheck3496 : row3496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3496 := by decide +kernel

theorem rowEval3496 (x : Key → ℝ) : Integer.Sparse.eval row3496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3496, Integer.Sparse.eval_collectBalanced, rawRowCheck3496]

def rawRow3497 : Integer.Sparse Key := [(key1785, -6), (key1769, 2), (key1810, 2), (key1810, 2), (key1452, 6), (key1334, -2), (key1652, -2), (key1652, -2), (key1383, -2), (key1416, -2), (key1416, -2), (key1288, 2), (key1565, 2), (key1565, 2)]

theorem rawRowCheck3497 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow3497 := by decide +kernel

def row3497 : Integer.Sparse Key := [(key1288, 2), (key1334, -2), (key1383, -2), (key1416, -4), (key1452, 6), (key1565, 4), (key1652, -4), (key1769, 2), (key1785, -6), (key1810, 4)]

theorem rowCheck3497 : row3497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3497 := by decide +kernel

theorem rowEval3497 (x : Key → ℝ) : Integer.Sparse.eval row3497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3497, Integer.Sparse.eval_collectBalanced, rawRowCheck3497]

def rawRow3498 : Integer.Sparse Key := [(key1785, -6), (key1810, 2), (key1769, 2), (key1810, 2), (key1452, 6), (key1652, -2), (key1334, -2), (key1652, -2), (key1416, -2), (key1383, -2), (key1416, -2), (key1565, 2), (key1288, 2), (key1565, 2)]

theorem rawRowCheck3498 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow3498 := by decide +kernel

def row3498 : Integer.Sparse Key := [(key1288, 2), (key1334, -2), (key1383, -2), (key1416, -4), (key1452, 6), (key1565, 4), (key1652, -4), (key1769, 2), (key1785, -6), (key1810, 4)]

theorem rowCheck3498 : row3498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3498 := by decide +kernel

theorem rowEval3498 (x : Key → ℝ) : Integer.Sparse.eval row3498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3498, Integer.Sparse.eval_collectBalanced, rawRowCheck3498]

def rawRow3499 : Integer.Sparse Key := [(key1785, -6), (key1810, 2), (key1810, 2), (key1769, 2), (key1452, 6), (key1652, -2), (key1652, -2), (key1334, -2), (key1416, -2), (key1416, -2), (key1383, -2), (key1565, 2), (key1565, 2), (key1288, 2)]

theorem rawRowCheck3499 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow3499 := by decide +kernel

def row3499 : Integer.Sparse Key := [(key1288, 2), (key1334, -2), (key1383, -2), (key1416, -4), (key1452, 6), (key1565, 4), (key1652, -4), (key1769, 2), (key1785, -6), (key1810, 4)]

theorem rowCheck3499 : row3499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3499 := by decide +kernel

theorem rowEval3499 (x : Key → ℝ) : Integer.Sparse.eval row3499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3499, Integer.Sparse.eval_collectBalanced, rawRowCheck3499]

def rawRow3500 : Integer.Sparse Key := [(key2647, -2), (key2647, -2), (key2652, -2), (key2613, 1), (key2613, 1), (key2629, 1), (key2629, 1), (key2637, 1), (key2637, 1), (key2937, 2), (key2937, 2), (key2942, 2), (key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2975, -1), (key2975, -1), (key2736, 1), (key2736, 1), (key2894, 1), (key2894, 1), (key2896, 1), (key2896, 1)]

theorem rawRowCheck3500 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form2 = rawRow3500 := by decide +kernel

def row3500 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, -2), (key2736, 2), (key2783, -2), (key2791, -2), (key2894, 2), (key2896, 2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

theorem rowCheck3500 : row3500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3500 := by decide +kernel

theorem rowEval3500 (x : Key → ℝ) : Integer.Sparse.eval row3500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3500, Integer.Sparse.eval_collectBalanced, rawRowCheck3500]

def rawRow3501 : Integer.Sparse Key := [(key2647, -2), (key2652, -2), (key2647, -2), (key2629, 1), (key2637, 1), (key2613, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2937, 2), (key2942, 2), (key2937, 2), (key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2894, 1), (key2896, 1), (key2736, 1), (key2896, 1), (key2736, 1), (key2894, 1)]

theorem rawRowCheck3501 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form2 = rawRow3501 := by decide +kernel

def row3501 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, -2), (key2736, 2), (key2783, -2), (key2791, -2), (key2894, 2), (key2896, 2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

theorem rowCheck3501 : row3501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3501 := by decide +kernel

theorem rowEval3501 (x : Key → ℝ) : Integer.Sparse.eval row3501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3501, Integer.Sparse.eval_collectBalanced, rawRowCheck3501]

def rawRow3502 : Integer.Sparse Key := [(key2652, -2), (key2647, -2), (key2647, -2), (key2637, 1), (key2629, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2613, 1), (key2942, 2), (key2937, 2), (key2937, 2), (key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2975, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2949, -1), (key2896, 1), (key2894, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2736, 1)]

theorem rawRowCheck3502 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form2 = rawRow3502 := by decide +kernel

def row3502 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, -2), (key2736, 2), (key2783, -2), (key2791, -2), (key2894, 2), (key2896, 2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

theorem rowCheck3502 : row3502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3502 := by decide +kernel

theorem rowEval3502 (x : Key → ℝ) : Integer.Sparse.eval row3502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3502, Integer.Sparse.eval_collectBalanced, rawRowCheck3502]

def rawRow3503 : Integer.Sparse Key := [(key2736, -2), (key2736, -2), (key2746, -2), (key2668, 1), (key2668, 1), (key2703, 1), (key2703, 1), (key2723, 1), (key2723, 1), (key2949, 2), (key2949, 2), (key2959, 2), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2937, -1), (key2937, -1), (key2973, -1), (key2973, -1), (key2982, -1), (key2982, -1), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1)]

theorem rawRowCheck3503 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form2 = rawRow3503 := by decide +kernel

def row3503 : Integer.Sparse Key := [(key2613, -2), (key2647, 2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2806, -2), (key2826, -2), (key2894, 2), (key2903, 2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

theorem rowCheck3503 : row3503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3503 := by decide +kernel

theorem rowEval3503 (x : Key → ℝ) : Integer.Sparse.eval row3503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3503, Integer.Sparse.eval_collectBalanced, rawRowCheck3503]

def rawRow3504 : Integer.Sparse Key := [(key2736, -2), (key2746, -2), (key2736, -2), (key2703, 1), (key2723, 1), (key2668, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2949, 2), (key2959, 2), (key2949, 2), (key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1)]

theorem rawRowCheck3504 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form2 = rawRow3504 := by decide +kernel

def row3504 : Integer.Sparse Key := [(key2613, -2), (key2647, 2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2806, -2), (key2826, -2), (key2894, 2), (key2903, 2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

theorem rowCheck3504 : row3504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3504 := by decide +kernel

theorem rowEval3504 (x : Key → ℝ) : Integer.Sparse.eval row3504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3504, Integer.Sparse.eval_collectBalanced, rawRowCheck3504]

def rawRow3505 : Integer.Sparse Key := [(key2746, -2), (key2736, -2), (key2736, -2), (key2723, 1), (key2703, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2668, 1), (key2959, 2), (key2949, 2), (key2949, 2), (key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2982, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1)]

theorem rawRowCheck3505 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form2 = rawRow3505 := by decide +kernel

def row3505 : Integer.Sparse Key := [(key2613, -2), (key2647, 2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2806, -2), (key2826, -2), (key2894, 2), (key2903, 2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

theorem rowCheck3505 : row3505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3505 := by decide +kernel

theorem rowEval3505 (x : Key → ℝ) : Integer.Sparse.eval row3505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3505, Integer.Sparse.eval_collectBalanced, rawRowCheck3505]

def rawRow3506 : Integer.Sparse Key := [(key2937, -2), (key2937, -2), (key2942, -2), (key2949, 1), (key2949, 1), (key2973, 1), (key2973, 1), (key2975, 1), (key2975, 1), (key2647, 2), (key2647, 2), (key2652, 2), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2613, -1), (key2613, -1), (key2629, -1), (key2629, -1), (key2637, -1), (key2637, -1), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1)]

theorem rawRowCheck3506 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form2 = rawRow3506 := by decide +kernel

def row3506 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, 2), (key2736, -2), (key2783, 2), (key2791, 2), (key2894, -2), (key2896, -2), (key2937, -4), (key2942, -2), (key2949, 2), (key2973, 2), (key2975, 2)]

theorem rowCheck3506 : row3506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3506 := by decide +kernel

theorem rowEval3506 (x : Key → ℝ) : Integer.Sparse.eval row3506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3506, Integer.Sparse.eval_collectBalanced, rawRowCheck3506]

def rawRow3507 : Integer.Sparse Key := [(key2937, -2), (key2942, -2), (key2937, -2), (key2973, 1), (key2975, 1), (key2949, 1), (key2975, 1), (key2949, 1), (key2973, 1), (key2647, 2), (key2652, 2), (key2647, 2), (key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1)]

theorem rawRowCheck3507 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form2 = rawRow3507 := by decide +kernel

def row3507 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, 2), (key2736, -2), (key2783, 2), (key2791, 2), (key2894, -2), (key2896, -2), (key2937, -4), (key2942, -2), (key2949, 2), (key2973, 2), (key2975, 2)]

theorem rowCheck3507 : row3507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3507 := by decide +kernel

theorem rowEval3507 (x : Key → ℝ) : Integer.Sparse.eval row3507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3507, Integer.Sparse.eval_collectBalanced, rawRowCheck3507]

def rawRow3508 : Integer.Sparse Key := [(key2942, -2), (key2937, -2), (key2937, -2), (key2975, 1), (key2973, 1), (key2975, 1), (key2949, 1), (key2973, 1), (key2949, 1), (key2652, 2), (key2647, 2), (key2647, 2), (key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2637, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2613, -1), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1)]

theorem rawRowCheck3508 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form2 = rawRow3508 := by decide +kernel

def row3508 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, 2), (key2736, -2), (key2783, 2), (key2791, 2), (key2894, -2), (key2896, -2), (key2937, -4), (key2942, -2), (key2949, 2), (key2973, 2), (key2975, 2)]

theorem rowCheck3508 : row3508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3508 := by decide +kernel

theorem rowEval3508 (x : Key → ℝ) : Integer.Sparse.eval row3508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3508, Integer.Sparse.eval_collectBalanced, rawRowCheck3508]

def rawRow3509 : Integer.Sparse Key := [(key2949, -2), (key2949, -2), (key2959, -2), (key2937, 1), (key2937, 1), (key2973, 1), (key2973, 1), (key2982, 1), (key2982, 1), (key2736, 2), (key2736, 2), (key2746, 2), (key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2723, -1), (key2723, -1), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1)]

theorem rawRowCheck3509 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form2 = rawRow3509 := by decide +kernel

def row3509 : Integer.Sparse Key := [(key2613, 2), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2806, 2), (key2826, 2), (key2894, -2), (key2903, -2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

theorem rowCheck3509 : row3509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3509 := by decide +kernel

theorem rowEval3509 (x : Key → ℝ) : Integer.Sparse.eval row3509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3509, Integer.Sparse.eval_collectBalanced, rawRowCheck3509]

def rawRow3510 : Integer.Sparse Key := [(key2949, -2), (key2959, -2), (key2949, -2), (key2973, 1), (key2982, 1), (key2937, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2736, 2), (key2746, 2), (key2736, 2), (key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1)]

theorem rawRowCheck3510 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form2 = rawRow3510 := by decide +kernel

def row3510 : Integer.Sparse Key := [(key2613, 2), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2806, 2), (key2826, 2), (key2894, -2), (key2903, -2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

theorem rowCheck3510 : row3510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3510 := by decide +kernel

theorem rowEval3510 (x : Key → ℝ) : Integer.Sparse.eval row3510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3510, Integer.Sparse.eval_collectBalanced, rawRowCheck3510]

def rawRow3511 : Integer.Sparse Key := [(key2959, -2), (key2949, -2), (key2949, -2), (key2982, 1), (key2973, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2937, 1), (key2746, 2), (key2736, 2), (key2736, 2), (key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2723, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1)]

theorem rawRowCheck3511 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form2 = rawRow3511 := by decide +kernel

def row3511 : Integer.Sparse Key := [(key2613, 2), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2806, 2), (key2826, 2), (key2894, -2), (key2903, -2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

theorem rowCheck3511 : row3511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3511 := by decide +kernel

theorem rowEval3511 (x : Key → ℝ) : Integer.Sparse.eval row3511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3511, Integer.Sparse.eval_collectBalanced, rawRowCheck3511]

def rawRow3512 : Integer.Sparse Key := [(key999, -2), (key999, -2), (key1013, -2), (key994, 6), (key1191, 2), (key1191, 2), (key1197, 2), (key1029, -2), (key1107, -2), (key1107, -2), (key1210, -6), (key1069, 2), (key1148, 2), (key1148, 2)]

theorem rawRowCheck3512 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form3 = rawRow3512 := by decide +kernel

def row3512 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1069, 2), (key1107, -4), (key1148, 4), (key1191, 4), (key1197, 2), (key1210, -6)]

theorem rowCheck3512 : row3512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3512 := by decide +kernel

theorem rowEval3512 (x : Key → ℝ) : Integer.Sparse.eval row3512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3512, Integer.Sparse.eval_collectBalanced, rawRowCheck3512]

def rawRow3513 : Integer.Sparse Key := [(key999, -2), (key1013, -2), (key999, -2), (key994, 6), (key1191, 2), (key1197, 2), (key1191, 2), (key1107, -2), (key1029, -2), (key1107, -2), (key1210, -6), (key1148, 2), (key1069, 2), (key1148, 2)]

theorem rawRowCheck3513 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form3 = rawRow3513 := by decide +kernel

def row3513 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1069, 2), (key1107, -4), (key1148, 4), (key1191, 4), (key1197, 2), (key1210, -6)]

theorem rowCheck3513 : row3513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3513 := by decide +kernel

theorem rowEval3513 (x : Key → ℝ) : Integer.Sparse.eval row3513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3513, Integer.Sparse.eval_collectBalanced, rawRowCheck3513]

def rawRow3514 : Integer.Sparse Key := [(key1013, -2), (key999, -2), (key999, -2), (key994, 6), (key1197, 2), (key1191, 2), (key1191, 2), (key1107, -2), (key1107, -2), (key1029, -2), (key1210, -6), (key1148, 2), (key1148, 2), (key1069, 2)]

theorem rawRowCheck3514 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form3 = rawRow3514 := by decide +kernel

def row3514 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1069, 2), (key1107, -4), (key1148, 4), (key1191, 4), (key1197, 2), (key1210, -6)]

theorem rowCheck3514 : row3514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3514 := by decide +kernel

theorem rowEval3514 (x : Key → ℝ) : Integer.Sparse.eval row3514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3514, Integer.Sparse.eval_collectBalanced, rawRowCheck3514]

def rawRow3515 : Integer.Sparse Key := [(key1034, -2), (key1034, -2), (key1069, -2), (key1029, 6), (key1191, 2), (key1191, 2), (key1210, 2), (key994, -2), (key1107, -2), (key1107, -2), (key1197, -6), (key1013, 2), (key1121, 2), (key1121, 2)]

theorem rawRowCheck3515 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow3515 := by decide +kernel

def row3515 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1121, 4), (key1191, 4), (key1197, -6), (key1210, 2)]

theorem rowCheck3515 : row3515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3515 := by decide +kernel

theorem rowEval3515 (x : Key → ℝ) : Integer.Sparse.eval row3515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3515, Integer.Sparse.eval_collectBalanced, rawRowCheck3515]

def rawRow3516 : Integer.Sparse Key := [(key1034, -2), (key1069, -2), (key1034, -2), (key1029, 6), (key1191, 2), (key1210, 2), (key1191, 2), (key1107, -2), (key994, -2), (key1107, -2), (key1197, -6), (key1121, 2), (key1013, 2), (key1121, 2)]

theorem rawRowCheck3516 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow3516 := by decide +kernel

def row3516 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1121, 4), (key1191, 4), (key1197, -6), (key1210, 2)]

theorem rowCheck3516 : row3516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3516 := by decide +kernel

theorem rowEval3516 (x : Key → ℝ) : Integer.Sparse.eval row3516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3516, Integer.Sparse.eval_collectBalanced, rawRowCheck3516]

def rawRow3517 : Integer.Sparse Key := [(key1069, -2), (key1034, -2), (key1034, -2), (key1029, 6), (key1210, 2), (key1191, 2), (key1191, 2), (key1107, -2), (key1107, -2), (key994, -2), (key1197, -6), (key1121, 2), (key1121, 2), (key1013, 2)]

theorem rawRowCheck3517 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow3517 := by decide +kernel

def row3517 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1121, 4), (key1191, 4), (key1197, -6), (key1210, 2)]

theorem rowCheck3517 : row3517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3517 := by decide +kernel

theorem rowEval3517 (x : Key → ℝ) : Integer.Sparse.eval row3517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3517, Integer.Sparse.eval_collectBalanced, rawRowCheck3517]

def rawRow3518 : Integer.Sparse Key := [(key1191, -2), (key1191, -2), (key1197, -2), (key1210, 6), (key999, 2), (key999, 2), (key1013, 2), (key1069, -2), (key1148, -2), (key1148, -2), (key994, -6), (key1029, 2), (key1107, 2), (key1107, 2)]

theorem rawRowCheck3518 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form3 = rawRow3518 := by decide +kernel

def row3518 : Integer.Sparse Key := [(key994, -6), (key999, 4), (key1013, 2), (key1029, 2), (key1069, -2), (key1107, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

theorem rowCheck3518 : row3518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3518 := by decide +kernel

theorem rowEval3518 (x : Key → ℝ) : Integer.Sparse.eval row3518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3518, Integer.Sparse.eval_collectBalanced, rawRowCheck3518]

def rawRow3519 : Integer.Sparse Key := [(key1191, -2), (key1197, -2), (key1191, -2), (key1210, 6), (key999, 2), (key1013, 2), (key999, 2), (key1148, -2), (key1069, -2), (key1148, -2), (key994, -6), (key1107, 2), (key1029, 2), (key1107, 2)]

theorem rawRowCheck3519 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form3 = rawRow3519 := by decide +kernel

def row3519 : Integer.Sparse Key := [(key994, -6), (key999, 4), (key1013, 2), (key1029, 2), (key1069, -2), (key1107, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

theorem rowCheck3519 : row3519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3519 := by decide +kernel

theorem rowEval3519 (x : Key → ℝ) : Integer.Sparse.eval row3519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3519, Integer.Sparse.eval_collectBalanced, rawRowCheck3519]

def rawRow3520 : Integer.Sparse Key := [(key1197, -2), (key1191, -2), (key1191, -2), (key1210, 6), (key1013, 2), (key999, 2), (key999, 2), (key1148, -2), (key1148, -2), (key1069, -2), (key994, -6), (key1107, 2), (key1107, 2), (key1029, 2)]

theorem rawRowCheck3520 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form3 = rawRow3520 := by decide +kernel

def row3520 : Integer.Sparse Key := [(key994, -6), (key999, 4), (key1013, 2), (key1029, 2), (key1069, -2), (key1107, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

theorem rowCheck3520 : row3520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3520 := by decide +kernel

theorem rowEval3520 (x : Key → ℝ) : Integer.Sparse.eval row3520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3520, Integer.Sparse.eval_collectBalanced, rawRowCheck3520]

def rawRow3521 : Integer.Sparse Key := [(key1191, -2), (key1191, -2), (key1210, -2), (key1197, 6), (key1034, 2), (key1034, 2), (key1069, 2), (key1013, -2), (key1121, -2), (key1121, -2), (key1029, -6), (key994, 2), (key1107, 2), (key1107, 2)]

theorem rawRowCheck3521 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow3521 := by decide +kernel

def row3521 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -6), (key1034, 4), (key1069, 2), (key1107, 4), (key1121, -4), (key1191, -4), (key1197, 6), (key1210, -2)]

theorem rowCheck3521 : row3521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3521 := by decide +kernel

theorem rowEval3521 (x : Key → ℝ) : Integer.Sparse.eval row3521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3521, Integer.Sparse.eval_collectBalanced, rawRowCheck3521]

def rawRow3522 : Integer.Sparse Key := [(key1191, -2), (key1210, -2), (key1191, -2), (key1197, 6), (key1034, 2), (key1069, 2), (key1034, 2), (key1121, -2), (key1013, -2), (key1121, -2), (key1029, -6), (key1107, 2), (key994, 2), (key1107, 2)]

theorem rawRowCheck3522 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow3522 := by decide +kernel

def row3522 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -6), (key1034, 4), (key1069, 2), (key1107, 4), (key1121, -4), (key1191, -4), (key1197, 6), (key1210, -2)]

theorem rowCheck3522 : row3522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3522 := by decide +kernel

theorem rowEval3522 (x : Key → ℝ) : Integer.Sparse.eval row3522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3522, Integer.Sparse.eval_collectBalanced, rawRowCheck3522]

def rawRow3523 : Integer.Sparse Key := [(key1210, -2), (key1191, -2), (key1191, -2), (key1197, 6), (key1069, 2), (key1034, 2), (key1034, 2), (key1121, -2), (key1121, -2), (key1013, -2), (key1029, -6), (key1107, 2), (key1107, 2), (key994, 2)]

theorem rawRowCheck3523 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow3523 := by decide +kernel

def row3523 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -6), (key1034, 4), (key1069, 2), (key1107, 4), (key1121, -4), (key1191, -4), (key1197, 6), (key1210, -2)]

theorem rowCheck3523 : row3523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3523 := by decide +kernel

theorem rowEval3523 (x : Key → ℝ) : Integer.Sparse.eval row3523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3523, Integer.Sparse.eval_collectBalanced, rawRowCheck3523]

def rawRow3524 : Integer.Sparse Key := [(key2634, -6), (key2607, 2), (key2623, 2), (key2623, 2), (key2720, 6), (key2662, -2), (key2697, -2), (key2697, -2), (key2823, -2), (key2864, -2), (key2864, -2), (key2788, 2), (key2854, 2), (key2854, 2)]

theorem rawRowCheck3524 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form4 = rawRow3524 := by decide +kernel

def row3524 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, -2), (key2697, -4), (key2720, 6), (key2788, 2), (key2823, -2), (key2854, 4), (key2864, -4)]

theorem rowCheck3524 : row3524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3524 := by decide +kernel

theorem rowEval3524 (x : Key → ℝ) : Integer.Sparse.eval row3524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3524, Integer.Sparse.eval_collectBalanced, rawRowCheck3524]

def rawRow3525 : Integer.Sparse Key := [(key2634, -6), (key2623, 2), (key2607, 2), (key2623, 2), (key2720, 6), (key2697, -2), (key2662, -2), (key2697, -2), (key2864, -2), (key2823, -2), (key2864, -2), (key2854, 2), (key2788, 2), (key2854, 2)]

theorem rawRowCheck3525 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form4 = rawRow3525 := by decide +kernel

def row3525 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, -2), (key2697, -4), (key2720, 6), (key2788, 2), (key2823, -2), (key2854, 4), (key2864, -4)]

theorem rowCheck3525 : row3525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3525 := by decide +kernel

theorem rowEval3525 (x : Key → ℝ) : Integer.Sparse.eval row3525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3525, Integer.Sparse.eval_collectBalanced, rawRowCheck3525]

def rawRow3526 : Integer.Sparse Key := [(key2634, -6), (key2623, 2), (key2623, 2), (key2607, 2), (key2720, 6), (key2697, -2), (key2697, -2), (key2662, -2), (key2864, -2), (key2864, -2), (key2823, -2), (key2854, 2), (key2854, 2), (key2788, 2)]

theorem rawRowCheck3526 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form4 = rawRow3526 := by decide +kernel

def row3526 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, -2), (key2697, -4), (key2720, 6), (key2788, 2), (key2823, -2), (key2854, 4), (key2864, -4)]

theorem rowCheck3526 : row3526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3526 := by decide +kernel

theorem rowEval3526 (x : Key → ℝ) : Integer.Sparse.eval row3526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3526, Integer.Sparse.eval_collectBalanced, rawRowCheck3526]

def rawRow3527 : Integer.Sparse Key := [(key2788, -6), (key2662, 2), (key2777, 2), (key2777, 2), (key2823, 6), (key2607, -2), (key2800, -2), (key2800, -2), (key2720, -2), (key2864, -2), (key2864, -2), (key2634, 2), (key2854, 2), (key2854, 2)]

theorem rawRowCheck3527 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form4 = rawRow3527 := by decide +kernel

def row3527 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, 2), (key2720, -2), (key2777, 4), (key2788, -6), (key2800, -4), (key2823, 6), (key2854, 4), (key2864, -4)]

theorem rowCheck3527 : row3527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3527 := by decide +kernel

theorem rowEval3527 (x : Key → ℝ) : Integer.Sparse.eval row3527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3527, Integer.Sparse.eval_collectBalanced, rawRowCheck3527]

def rawRow3528 : Integer.Sparse Key := [(key2788, -6), (key2777, 2), (key2662, 2), (key2777, 2), (key2823, 6), (key2800, -2), (key2607, -2), (key2800, -2), (key2864, -2), (key2720, -2), (key2864, -2), (key2854, 2), (key2634, 2), (key2854, 2)]

theorem rawRowCheck3528 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form4 = rawRow3528 := by decide +kernel

def row3528 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, 2), (key2720, -2), (key2777, 4), (key2788, -6), (key2800, -4), (key2823, 6), (key2854, 4), (key2864, -4)]

theorem rowCheck3528 : row3528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3528 := by decide +kernel

theorem rowEval3528 (x : Key → ℝ) : Integer.Sparse.eval row3528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3528, Integer.Sparse.eval_collectBalanced, rawRowCheck3528]

def rawRow3529 : Integer.Sparse Key := [(key2788, -6), (key2777, 2), (key2777, 2), (key2662, 2), (key2823, 6), (key2800, -2), (key2800, -2), (key2607, -2), (key2864, -2), (key2864, -2), (key2720, -2), (key2854, 2), (key2854, 2), (key2634, 2)]

theorem rawRowCheck3529 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form4 = rawRow3529 := by decide +kernel

def row3529 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, 2), (key2720, -2), (key2777, 4), (key2788, -6), (key2800, -4), (key2823, 6), (key2854, 4), (key2864, -4)]

theorem rowCheck3529 : row3529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3529 := by decide +kernel

theorem rowEval3529 (x : Key → ℝ) : Integer.Sparse.eval row3529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3529, Integer.Sparse.eval_collectBalanced, rawRowCheck3529]

def rawRow3530 : Integer.Sparse Key := [(key2720, -6), (key2823, 2), (key2864, 2), (key2864, 2), (key2634, 6), (key2788, -2), (key2854, -2), (key2854, -2), (key2607, -2), (key2623, -2), (key2623, -2), (key2662, 2), (key2697, 2), (key2697, 2)]

theorem rawRowCheck3530 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form4 = rawRow3530 := by decide +kernel

def row3530 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, 2), (key2697, 4), (key2720, -6), (key2788, -2), (key2823, 2), (key2854, -4), (key2864, 4)]

theorem rowCheck3530 : row3530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3530 := by decide +kernel

theorem rowEval3530 (x : Key → ℝ) : Integer.Sparse.eval row3530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3530, Integer.Sparse.eval_collectBalanced, rawRowCheck3530]

def rawRow3531 : Integer.Sparse Key := [(key2720, -6), (key2864, 2), (key2823, 2), (key2864, 2), (key2634, 6), (key2854, -2), (key2788, -2), (key2854, -2), (key2623, -2), (key2607, -2), (key2623, -2), (key2697, 2), (key2662, 2), (key2697, 2)]

theorem rawRowCheck3531 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form4 = rawRow3531 := by decide +kernel

def row3531 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, 2), (key2697, 4), (key2720, -6), (key2788, -2), (key2823, 2), (key2854, -4), (key2864, 4)]

theorem rowCheck3531 : row3531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3531 := by decide +kernel

theorem rowEval3531 (x : Key → ℝ) : Integer.Sparse.eval row3531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3531, Integer.Sparse.eval_collectBalanced, rawRowCheck3531]

def rawRow3532 : Integer.Sparse Key := [(key2720, -6), (key2864, 2), (key2864, 2), (key2823, 2), (key2634, 6), (key2854, -2), (key2854, -2), (key2788, -2), (key2623, -2), (key2623, -2), (key2607, -2), (key2697, 2), (key2697, 2), (key2662, 2)]

theorem rawRowCheck3532 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form4 = rawRow3532 := by decide +kernel

def row3532 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, 2), (key2697, 4), (key2720, -6), (key2788, -2), (key2823, 2), (key2854, -4), (key2864, 4)]

theorem rowCheck3532 : row3532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3532 := by decide +kernel

theorem rowEval3532 (x : Key → ℝ) : Integer.Sparse.eval row3532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3532, Integer.Sparse.eval_collectBalanced, rawRowCheck3532]

def rawRow3533 : Integer.Sparse Key := [(key2823, -6), (key2720, 2), (key2864, 2), (key2864, 2), (key2788, 6), (key2634, -2), (key2854, -2), (key2854, -2), (key2662, -2), (key2777, -2), (key2777, -2), (key2607, 2), (key2800, 2), (key2800, 2)]

theorem rawRowCheck3533 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form4 = rawRow3533 := by decide +kernel

def row3533 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, -2), (key2720, 2), (key2777, -4), (key2788, 6), (key2800, 4), (key2823, -6), (key2854, -4), (key2864, 4)]

theorem rowCheck3533 : row3533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3533 := by decide +kernel

theorem rowEval3533 (x : Key → ℝ) : Integer.Sparse.eval row3533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3533, Integer.Sparse.eval_collectBalanced, rawRowCheck3533]

def rawRow3534 : Integer.Sparse Key := [(key2823, -6), (key2864, 2), (key2720, 2), (key2864, 2), (key2788, 6), (key2854, -2), (key2634, -2), (key2854, -2), (key2777, -2), (key2662, -2), (key2777, -2), (key2800, 2), (key2607, 2), (key2800, 2)]

theorem rawRowCheck3534 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form4 = rawRow3534 := by decide +kernel

def row3534 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, -2), (key2720, 2), (key2777, -4), (key2788, 6), (key2800, 4), (key2823, -6), (key2854, -4), (key2864, 4)]

theorem rowCheck3534 : row3534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3534 := by decide +kernel

theorem rowEval3534 (x : Key → ℝ) : Integer.Sparse.eval row3534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3534, Integer.Sparse.eval_collectBalanced, rawRowCheck3534]

def rawRow3535 : Integer.Sparse Key := [(key2823, -6), (key2864, 2), (key2864, 2), (key2720, 2), (key2788, 6), (key2854, -2), (key2854, -2), (key2634, -2), (key2777, -2), (key2777, -2), (key2662, -2), (key2800, 2), (key2800, 2), (key2607, 2)]

theorem rawRowCheck3535 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form4 = rawRow3535 := by decide +kernel

def row3535 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, -2), (key2720, 2), (key2777, -4), (key2788, 6), (key2800, 4), (key2823, -6), (key2854, -4), (key2864, 4)]

theorem rowCheck3535 : row3535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3535 := by decide +kernel

theorem rowEval3535 (x : Key → ℝ) : Integer.Sparse.eval row3535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3535, Integer.Sparse.eval_collectBalanced, rawRowCheck3535]

def rawRow3536 : Integer.Sparse Key := [(key1392, -1), (key1392, -1), (key1547, -1), (key1547, -1), (key1555, -1), (key1555, -1), (key1387, 2), (key1542, 2), (key1542, 2), (key1456, 1), (key1456, 1), (key1656, 1), (key1656, 1), (key1658, 1), (key1658, 1), (key1420, -1), (key1420, -1), (key1569, -1), (key1569, -1), (key1618, -1), (key1618, -1), (key1465, -2), (key1666, -2), (key1666, -2), (key1443, 1), (key1443, 1), (key1592, 1), (key1592, 1), (key1632, 1), (key1632, 1)]

theorem rawRowCheck3536 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form5 = rawRow3536 := by decide +kernel

def row3536 : Integer.Sparse Key := [(key1387, 2), (key1392, -2), (key1420, -2), (key1443, 2), (key1456, 2), (key1465, -2), (key1542, 4), (key1547, -2), (key1555, -2), (key1569, -2), (key1592, 2), (key1618, -2), (key1632, 2), (key1656, 2), (key1658, 2), (key1666, -4)]

theorem rowCheck3536 : row3536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3536 := by decide +kernel

theorem rowEval3536 (x : Key → ℝ) : Integer.Sparse.eval row3536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3536, Integer.Sparse.eval_collectBalanced, rawRowCheck3536]

def rawRow3537 : Integer.Sparse Key := [(key1547, -1), (key1555, -1), (key1392, -1), (key1555, -1), (key1392, -1), (key1547, -1), (key1542, 2), (key1387, 2), (key1542, 2), (key1656, 1), (key1658, 1), (key1456, 1), (key1658, 1), (key1456, 1), (key1656, 1), (key1569, -1), (key1618, -1), (key1420, -1), (key1618, -1), (key1420, -1), (key1569, -1), (key1666, -2), (key1465, -2), (key1666, -2), (key1592, 1), (key1632, 1), (key1443, 1), (key1632, 1), (key1443, 1), (key1592, 1)]

theorem rawRowCheck3537 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form5 = rawRow3537 := by decide +kernel

def row3537 : Integer.Sparse Key := [(key1387, 2), (key1392, -2), (key1420, -2), (key1443, 2), (key1456, 2), (key1465, -2), (key1542, 4), (key1547, -2), (key1555, -2), (key1569, -2), (key1592, 2), (key1618, -2), (key1632, 2), (key1656, 2), (key1658, 2), (key1666, -4)]

theorem rowCheck3537 : row3537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3537 := by decide +kernel

theorem rowEval3537 (x : Key → ℝ) : Integer.Sparse.eval row3537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3537, Integer.Sparse.eval_collectBalanced, rawRowCheck3537]

def rawRow3538 : Integer.Sparse Key := [(key1555, -1), (key1547, -1), (key1555, -1), (key1392, -1), (key1547, -1), (key1392, -1), (key1542, 2), (key1542, 2), (key1387, 2), (key1658, 1), (key1656, 1), (key1658, 1), (key1456, 1), (key1656, 1), (key1456, 1), (key1618, -1), (key1569, -1), (key1618, -1), (key1420, -1), (key1569, -1), (key1420, -1), (key1666, -2), (key1666, -2), (key1465, -2), (key1632, 1), (key1592, 1), (key1632, 1), (key1443, 1), (key1592, 1), (key1443, 1)]

theorem rawRowCheck3538 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form5 = rawRow3538 := by decide +kernel

def row3538 : Integer.Sparse Key := [(key1387, 2), (key1392, -2), (key1420, -2), (key1443, 2), (key1456, 2), (key1465, -2), (key1542, 4), (key1547, -2), (key1555, -2), (key1569, -2), (key1592, 2), (key1618, -2), (key1632, 2), (key1656, 2), (key1658, 2), (key1666, -4)]

theorem rowCheck3538 : row3538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3538 := by decide +kernel

theorem rowEval3538 (x : Key → ℝ) : Integer.Sparse.eval row3538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3538, Integer.Sparse.eval_collectBalanced, rawRowCheck3538]

def rawRow3539 : Integer.Sparse Key := [(key1297, -1), (key1297, -1), (key1574, -1), (key1574, -1), (key1592, -1), (key1592, -1), (key1292, 2), (key1569, 2), (key1569, 2), (key1338, 1), (key1338, 1), (key1656, 1), (key1656, 1), (key1666, 1), (key1666, 1), (key1312, -1), (key1312, -1), (key1542, -1), (key1542, -1), (key1618, -1), (key1618, -1), (key1344, -2), (key1658, -2), (key1658, -2), (key1325, 1), (key1325, 1), (key1555, 1), (key1555, 1), (key1623, 1), (key1623, 1)]

theorem rawRowCheck3539 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form5 = rawRow3539 := by decide +kernel

def row3539 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1325, 2), (key1338, 2), (key1344, -2), (key1542, -2), (key1555, 2), (key1569, 4), (key1574, -2), (key1592, -2), (key1618, -2), (key1623, 2), (key1656, 2), (key1658, -4), (key1666, 2)]

theorem rowCheck3539 : row3539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3539 := by decide +kernel

theorem rowEval3539 (x : Key → ℝ) : Integer.Sparse.eval row3539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3539, Integer.Sparse.eval_collectBalanced, rawRowCheck3539]

def rawRow3540 : Integer.Sparse Key := [(key1574, -1), (key1592, -1), (key1297, -1), (key1592, -1), (key1297, -1), (key1574, -1), (key1569, 2), (key1292, 2), (key1569, 2), (key1656, 1), (key1666, 1), (key1338, 1), (key1666, 1), (key1338, 1), (key1656, 1), (key1542, -1), (key1618, -1), (key1312, -1), (key1618, -1), (key1312, -1), (key1542, -1), (key1658, -2), (key1344, -2), (key1658, -2), (key1555, 1), (key1623, 1), (key1325, 1), (key1623, 1), (key1325, 1), (key1555, 1)]

theorem rawRowCheck3540 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form5 = rawRow3540 := by decide +kernel

def row3540 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1325, 2), (key1338, 2), (key1344, -2), (key1542, -2), (key1555, 2), (key1569, 4), (key1574, -2), (key1592, -2), (key1618, -2), (key1623, 2), (key1656, 2), (key1658, -4), (key1666, 2)]

theorem rowCheck3540 : row3540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3540 := by decide +kernel

theorem rowEval3540 (x : Key → ℝ) : Integer.Sparse.eval row3540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3540, Integer.Sparse.eval_collectBalanced, rawRowCheck3540]

def rawRow3541 : Integer.Sparse Key := [(key1592, -1), (key1574, -1), (key1592, -1), (key1297, -1), (key1574, -1), (key1297, -1), (key1569, 2), (key1569, 2), (key1292, 2), (key1666, 1), (key1656, 1), (key1666, 1), (key1338, 1), (key1656, 1), (key1338, 1), (key1618, -1), (key1542, -1), (key1618, -1), (key1312, -1), (key1542, -1), (key1312, -1), (key1658, -2), (key1658, -2), (key1344, -2), (key1623, 1), (key1555, 1), (key1623, 1), (key1325, 1), (key1555, 1), (key1325, 1)]

theorem rawRowCheck3541 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form5 = rawRow3541 := by decide +kernel

def row3541 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1325, 2), (key1338, 2), (key1344, -2), (key1542, -2), (key1555, 2), (key1569, 4), (key1574, -2), (key1592, -2), (key1618, -2), (key1623, 2), (key1656, 2), (key1658, -4), (key1666, 2)]

theorem rowCheck3541 : row3541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3541 := by decide +kernel

theorem rowEval3541 (x : Key → ℝ) : Integer.Sparse.eval row3541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3541, Integer.Sparse.eval_collectBalanced, rawRowCheck3541]

def rawRow3542 : Integer.Sparse Key := [(key1456, -1), (key1456, -1), (key1656, -1), (key1656, -1), (key1658, -1), (key1658, -1), (key1465, 2), (key1666, 2), (key1666, 2), (key1392, 1), (key1392, 1), (key1547, 1), (key1547, 1), (key1555, 1), (key1555, 1), (key1443, -1), (key1443, -1), (key1592, -1), (key1592, -1), (key1632, -1), (key1632, -1), (key1387, -2), (key1542, -2), (key1542, -2), (key1420, 1), (key1420, 1), (key1569, 1), (key1569, 1), (key1618, 1), (key1618, 1)]

theorem rawRowCheck3542 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form5 = rawRow3542 := by decide +kernel

def row3542 : Integer.Sparse Key := [(key1387, -2), (key1392, 2), (key1420, 2), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -4), (key1547, 2), (key1555, 2), (key1569, 2), (key1592, -2), (key1618, 2), (key1632, -2), (key1656, -2), (key1658, -2), (key1666, 4)]

theorem rowCheck3542 : row3542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3542 := by decide +kernel

theorem rowEval3542 (x : Key → ℝ) : Integer.Sparse.eval row3542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3542, Integer.Sparse.eval_collectBalanced, rawRowCheck3542]

def rawRow3543 : Integer.Sparse Key := [(key1656, -1), (key1658, -1), (key1456, -1), (key1658, -1), (key1456, -1), (key1656, -1), (key1666, 2), (key1465, 2), (key1666, 2), (key1547, 1), (key1555, 1), (key1392, 1), (key1555, 1), (key1392, 1), (key1547, 1), (key1592, -1), (key1632, -1), (key1443, -1), (key1632, -1), (key1443, -1), (key1592, -1), (key1542, -2), (key1387, -2), (key1542, -2), (key1569, 1), (key1618, 1), (key1420, 1), (key1618, 1), (key1420, 1), (key1569, 1)]

theorem rawRowCheck3543 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form5 = rawRow3543 := by decide +kernel

def row3543 : Integer.Sparse Key := [(key1387, -2), (key1392, 2), (key1420, 2), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -4), (key1547, 2), (key1555, 2), (key1569, 2), (key1592, -2), (key1618, 2), (key1632, -2), (key1656, -2), (key1658, -2), (key1666, 4)]

theorem rowCheck3543 : row3543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3543 := by decide +kernel

theorem rowEval3543 (x : Key → ℝ) : Integer.Sparse.eval row3543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3543, Integer.Sparse.eval_collectBalanced, rawRowCheck3543]

def rawRow3544 : Integer.Sparse Key := [(key1658, -1), (key1656, -1), (key1658, -1), (key1456, -1), (key1656, -1), (key1456, -1), (key1666, 2), (key1666, 2), (key1465, 2), (key1555, 1), (key1547, 1), (key1555, 1), (key1392, 1), (key1547, 1), (key1392, 1), (key1632, -1), (key1592, -1), (key1632, -1), (key1443, -1), (key1592, -1), (key1443, -1), (key1542, -2), (key1542, -2), (key1387, -2), (key1618, 1), (key1569, 1), (key1618, 1), (key1420, 1), (key1569, 1), (key1420, 1)]

theorem rawRowCheck3544 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form5 = rawRow3544 := by decide +kernel

def row3544 : Integer.Sparse Key := [(key1387, -2), (key1392, 2), (key1420, 2), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -4), (key1547, 2), (key1555, 2), (key1569, 2), (key1592, -2), (key1618, 2), (key1632, -2), (key1656, -2), (key1658, -2), (key1666, 4)]

theorem rowCheck3544 : row3544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3544 := by decide +kernel

theorem rowEval3544 (x : Key → ℝ) : Integer.Sparse.eval row3544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3544, Integer.Sparse.eval_collectBalanced, rawRowCheck3544]

def rawRow3545 : Integer.Sparse Key := [(key1338, -1), (key1338, -1), (key1656, -1), (key1656, -1), (key1666, -1), (key1666, -1), (key1344, 2), (key1658, 2), (key1658, 2), (key1297, 1), (key1297, 1), (key1574, 1), (key1574, 1), (key1592, 1), (key1592, 1), (key1325, -1), (key1325, -1), (key1555, -1), (key1555, -1), (key1623, -1), (key1623, -1), (key1292, -2), (key1569, -2), (key1569, -2), (key1312, 1), (key1312, 1), (key1542, 1), (key1542, 1), (key1618, 1), (key1618, 1)]

theorem rawRowCheck3545 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form5 = rawRow3545 := by decide +kernel

def row3545 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1325, -2), (key1338, -2), (key1344, 2), (key1542, 2), (key1555, -2), (key1569, -4), (key1574, 2), (key1592, 2), (key1618, 2), (key1623, -2), (key1656, -2), (key1658, 4), (key1666, -2)]

theorem rowCheck3545 : row3545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3545 := by decide +kernel

theorem rowEval3545 (x : Key → ℝ) : Integer.Sparse.eval row3545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3545, Integer.Sparse.eval_collectBalanced, rawRowCheck3545]

def rawRow3546 : Integer.Sparse Key := [(key1656, -1), (key1666, -1), (key1338, -1), (key1666, -1), (key1338, -1), (key1656, -1), (key1658, 2), (key1344, 2), (key1658, 2), (key1574, 1), (key1592, 1), (key1297, 1), (key1592, 1), (key1297, 1), (key1574, 1), (key1555, -1), (key1623, -1), (key1325, -1), (key1623, -1), (key1325, -1), (key1555, -1), (key1569, -2), (key1292, -2), (key1569, -2), (key1542, 1), (key1618, 1), (key1312, 1), (key1618, 1), (key1312, 1), (key1542, 1)]

theorem rawRowCheck3546 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form5 = rawRow3546 := by decide +kernel

def row3546 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1325, -2), (key1338, -2), (key1344, 2), (key1542, 2), (key1555, -2), (key1569, -4), (key1574, 2), (key1592, 2), (key1618, 2), (key1623, -2), (key1656, -2), (key1658, 4), (key1666, -2)]

theorem rowCheck3546 : row3546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3546 := by decide +kernel

theorem rowEval3546 (x : Key → ℝ) : Integer.Sparse.eval row3546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3546, Integer.Sparse.eval_collectBalanced, rawRowCheck3546]

def rawRow3547 : Integer.Sparse Key := [(key1666, -1), (key1656, -1), (key1666, -1), (key1338, -1), (key1656, -1), (key1338, -1), (key1658, 2), (key1658, 2), (key1344, 2), (key1592, 1), (key1574, 1), (key1592, 1), (key1297, 1), (key1574, 1), (key1297, 1), (key1623, -1), (key1555, -1), (key1623, -1), (key1325, -1), (key1555, -1), (key1325, -1), (key1569, -2), (key1569, -2), (key1292, -2), (key1618, 1), (key1542, 1), (key1618, 1), (key1312, 1), (key1542, 1), (key1312, 1)]

theorem rawRowCheck3547 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form5 = rawRow3547 := by decide +kernel

def row3547 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1325, -2), (key1338, -2), (key1344, 2), (key1542, 2), (key1555, -2), (key1569, -4), (key1574, 2), (key1592, 2), (key1618, 2), (key1623, -2), (key1656, -2), (key1658, 4), (key1666, -2)]

theorem rowCheck3547 : row3547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3547 := by decide +kernel

theorem rowEval3547 (x : Key → ℝ) : Integer.Sparse.eval row3547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3547, Integer.Sparse.eval_collectBalanced, rawRowCheck3547]

def rawRow3548 : Integer.Sparse Key := [(key3052, -2), (key3052, -2), (key3067, -2), (key3048, 2), (key3048, 2), (key3062, 2), (key3108, 2), (key3108, 2), (key3135, 2), (key3097, -6), (key3111, -2), (key3111, -2), (key3137, -2), (key3104, 6)]

theorem rawRowCheck3548 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form6 = rawRow3548 := by decide +kernel

def row3548 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, 2), (key3067, -2), (key3097, -6), (key3104, 6), (key3108, 4), (key3111, -4), (key3135, 2), (key3137, -2)]

theorem rowCheck3548 : row3548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3548 := by decide +kernel

theorem rowEval3548 (x : Key → ℝ) : Integer.Sparse.eval row3548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3548, Integer.Sparse.eval_collectBalanced, rawRowCheck3548]

def rawRow3549 : Integer.Sparse Key := [(key3052, -2), (key3067, -2), (key3052, -2), (key3048, 2), (key3062, 2), (key3048, 2), (key3108, 2), (key3135, 2), (key3108, 2), (key3097, -6), (key3111, -2), (key3137, -2), (key3111, -2), (key3104, 6)]

theorem rawRowCheck3549 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form6 = rawRow3549 := by decide +kernel

def row3549 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, 2), (key3067, -2), (key3097, -6), (key3104, 6), (key3108, 4), (key3111, -4), (key3135, 2), (key3137, -2)]

theorem rowCheck3549 : row3549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3549 := by decide +kernel

theorem rowEval3549 (x : Key → ℝ) : Integer.Sparse.eval row3549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3549, Integer.Sparse.eval_collectBalanced, rawRowCheck3549]

def rawRow3550 : Integer.Sparse Key := [(key3067, -2), (key3052, -2), (key3052, -2), (key3062, 2), (key3048, 2), (key3048, 2), (key3135, 2), (key3108, 2), (key3108, 2), (key3097, -6), (key3137, -2), (key3111, -2), (key3111, -2), (key3104, 6)]

theorem rawRowCheck3550 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form6 = rawRow3550 := by decide +kernel

def row3550 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, 2), (key3067, -2), (key3097, -6), (key3104, 6), (key3108, 4), (key3111, -4), (key3135, 2), (key3137, -2)]

theorem rowCheck3550 : row3550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3550 := by decide +kernel

theorem rowEval3550 (x : Key → ℝ) : Integer.Sparse.eval row3550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3550, Integer.Sparse.eval_collectBalanced, rawRowCheck3550]

def rawRow3551 : Integer.Sparse Key := [(key3052, -2), (key3052, -2), (key3104, -2), (key3048, 2), (key3048, 2), (key3097, 2), (key3071, 2), (key3071, 2), (key3137, 2), (key3062, -6), (key3073, -2), (key3073, -2), (key3135, -2), (key3067, 6)]

theorem rawRowCheck3551 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form6 = rawRow3551 := by decide +kernel

def row3551 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -6), (key3067, 6), (key3071, 4), (key3073, -4), (key3097, 2), (key3104, -2), (key3135, -2), (key3137, 2)]

theorem rowCheck3551 : row3551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3551 := by decide +kernel

theorem rowEval3551 (x : Key → ℝ) : Integer.Sparse.eval row3551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3551, Integer.Sparse.eval_collectBalanced, rawRowCheck3551]

def rawRow3552 : Integer.Sparse Key := [(key3052, -2), (key3104, -2), (key3052, -2), (key3048, 2), (key3097, 2), (key3048, 2), (key3071, 2), (key3137, 2), (key3071, 2), (key3062, -6), (key3073, -2), (key3135, -2), (key3073, -2), (key3067, 6)]

theorem rawRowCheck3552 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form6 = rawRow3552 := by decide +kernel

def row3552 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -6), (key3067, 6), (key3071, 4), (key3073, -4), (key3097, 2), (key3104, -2), (key3135, -2), (key3137, 2)]

theorem rowCheck3552 : row3552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3552 := by decide +kernel

theorem rowEval3552 (x : Key → ℝ) : Integer.Sparse.eval row3552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3552, Integer.Sparse.eval_collectBalanced, rawRowCheck3552]

def rawRow3553 : Integer.Sparse Key := [(key3104, -2), (key3052, -2), (key3052, -2), (key3097, 2), (key3048, 2), (key3048, 2), (key3137, 2), (key3071, 2), (key3071, 2), (key3062, -6), (key3135, -2), (key3073, -2), (key3073, -2), (key3067, 6)]

theorem rawRowCheck3553 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form6 = rawRow3553 := by decide +kernel

def row3553 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -6), (key3067, 6), (key3071, 4), (key3073, -4), (key3097, 2), (key3104, -2), (key3135, -2), (key3137, 2)]

theorem rowCheck3553 : row3553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3553 := by decide +kernel

theorem rowEval3553 (x : Key → ℝ) : Integer.Sparse.eval row3553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3553, Integer.Sparse.eval_collectBalanced, rawRowCheck3553]

def rawRow3554 : Integer.Sparse Key := [(key3108, -2), (key3108, -2), (key3135, -2), (key3111, 2), (key3111, 2), (key3137, 2), (key3052, 2), (key3052, 2), (key3067, 2), (key3104, -6), (key3048, -2), (key3048, -2), (key3062, -2), (key3097, 6)]

theorem rawRowCheck3554 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form6 = rawRow3554 := by decide +kernel

def row3554 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, -2), (key3067, 2), (key3097, 6), (key3104, -6), (key3108, -4), (key3111, 4), (key3135, -2), (key3137, 2)]

theorem rowCheck3554 : row3554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3554 := by decide +kernel

theorem rowEval3554 (x : Key → ℝ) : Integer.Sparse.eval row3554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3554, Integer.Sparse.eval_collectBalanced, rawRowCheck3554]

def rawRow3555 : Integer.Sparse Key := [(key3108, -2), (key3135, -2), (key3108, -2), (key3111, 2), (key3137, 2), (key3111, 2), (key3052, 2), (key3067, 2), (key3052, 2), (key3104, -6), (key3048, -2), (key3062, -2), (key3048, -2), (key3097, 6)]

theorem rawRowCheck3555 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form6 = rawRow3555 := by decide +kernel

def row3555 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, -2), (key3067, 2), (key3097, 6), (key3104, -6), (key3108, -4), (key3111, 4), (key3135, -2), (key3137, 2)]

theorem rowCheck3555 : row3555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3555 := by decide +kernel

theorem rowEval3555 (x : Key → ℝ) : Integer.Sparse.eval row3555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3555, Integer.Sparse.eval_collectBalanced, rawRowCheck3555]

def rawRow3556 : Integer.Sparse Key := [(key3135, -2), (key3108, -2), (key3108, -2), (key3137, 2), (key3111, 2), (key3111, 2), (key3067, 2), (key3052, 2), (key3052, 2), (key3104, -6), (key3062, -2), (key3048, -2), (key3048, -2), (key3097, 6)]

theorem rawRowCheck3556 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form6 = rawRow3556 := by decide +kernel

def row3556 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, -2), (key3067, 2), (key3097, 6), (key3104, -6), (key3108, -4), (key3111, 4), (key3135, -2), (key3137, 2)]

theorem rowCheck3556 : row3556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3556 := by decide +kernel

theorem rowEval3556 (x : Key → ℝ) : Integer.Sparse.eval row3556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3556, Integer.Sparse.eval_collectBalanced, rawRowCheck3556]

def rawRow3557 : Integer.Sparse Key := [(key3071, -2), (key3071, -2), (key3137, -2), (key3073, 2), (key3073, 2), (key3135, 2), (key3052, 2), (key3052, 2), (key3104, 2), (key3067, -6), (key3048, -2), (key3048, -2), (key3097, -2), (key3062, 6)]

theorem rawRowCheck3557 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form6 = rawRow3557 := by decide +kernel

def row3557 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 6), (key3067, -6), (key3071, -4), (key3073, 4), (key3097, -2), (key3104, 2), (key3135, 2), (key3137, -2)]

theorem rowCheck3557 : row3557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3557 := by decide +kernel

theorem rowEval3557 (x : Key → ℝ) : Integer.Sparse.eval row3557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3557, Integer.Sparse.eval_collectBalanced, rawRowCheck3557]

def rawRow3558 : Integer.Sparse Key := [(key3071, -2), (key3137, -2), (key3071, -2), (key3073, 2), (key3135, 2), (key3073, 2), (key3052, 2), (key3104, 2), (key3052, 2), (key3067, -6), (key3048, -2), (key3097, -2), (key3048, -2), (key3062, 6)]

theorem rawRowCheck3558 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form6 = rawRow3558 := by decide +kernel

def row3558 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 6), (key3067, -6), (key3071, -4), (key3073, 4), (key3097, -2), (key3104, 2), (key3135, 2), (key3137, -2)]

theorem rowCheck3558 : row3558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3558 := by decide +kernel

theorem rowEval3558 (x : Key → ℝ) : Integer.Sparse.eval row3558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3558, Integer.Sparse.eval_collectBalanced, rawRowCheck3558]

def rawRow3559 : Integer.Sparse Key := [(key3137, -2), (key3071, -2), (key3071, -2), (key3135, 2), (key3073, 2), (key3073, 2), (key3104, 2), (key3052, 2), (key3052, 2), (key3067, -6), (key3097, -2), (key3048, -2), (key3048, -2), (key3062, 6)]

theorem rawRowCheck3559 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form6 = rawRow3559 := by decide +kernel

def row3559 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 6), (key3067, -6), (key3071, -4), (key3073, 4), (key3097, -2), (key3104, 2), (key3135, 2), (key3137, -2)]

theorem rowCheck3559 : row3559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3559 := by decide +kernel

theorem rowEval3559 (x : Key → ℝ) : Integer.Sparse.eval row3559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3559, Integer.Sparse.eval_collectBalanced, rawRowCheck3559]

def rawRow3560 : Integer.Sparse Key := [(key1338, -2), (key1338, -2), (key1344, -2), (key1297, 1), (key1297, 1), (key1317, 1), (key1317, 1), (key1325, 1), (key1325, 1), (key1773, 2), (key1773, 2), (key1779, 2), (key1392, -1), (key1392, -1), (key1547, -1), (key1547, -1), (key1555, -1), (key1555, -1), (key1789, -1), (key1789, -1), (key1814, -1), (key1814, -1), (key1816, -1), (key1816, -1), (key1456, 1), (key1456, 1), (key1656, 1), (key1656, 1), (key1658, 1), (key1658, 1)]

theorem rawRowCheck3560 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form7 = rawRow3560 := by decide +kernel

def row3560 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, -2), (key1456, 2), (key1547, -2), (key1555, -2), (key1656, 2), (key1658, 2), (key1773, 4), (key1779, 2), (key1789, -2), (key1814, -2), (key1816, -2)]

theorem rowCheck3560 : row3560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3560 := by decide +kernel

theorem rowEval3560 (x : Key → ℝ) : Integer.Sparse.eval row3560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3560, Integer.Sparse.eval_collectBalanced, rawRowCheck3560]

def rawRow3561 : Integer.Sparse Key := [(key1338, -2), (key1344, -2), (key1338, -2), (key1317, 1), (key1325, 1), (key1297, 1), (key1325, 1), (key1297, 1), (key1317, 1), (key1773, 2), (key1779, 2), (key1773, 2), (key1547, -1), (key1555, -1), (key1392, -1), (key1555, -1), (key1392, -1), (key1547, -1), (key1814, -1), (key1816, -1), (key1789, -1), (key1816, -1), (key1789, -1), (key1814, -1), (key1656, 1), (key1658, 1), (key1456, 1), (key1658, 1), (key1456, 1), (key1656, 1)]

theorem rawRowCheck3561 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form7 = rawRow3561 := by decide +kernel

def row3561 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, -2), (key1456, 2), (key1547, -2), (key1555, -2), (key1656, 2), (key1658, 2), (key1773, 4), (key1779, 2), (key1789, -2), (key1814, -2), (key1816, -2)]

theorem rowCheck3561 : row3561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3561 := by decide +kernel

theorem rowEval3561 (x : Key → ℝ) : Integer.Sparse.eval row3561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3561, Integer.Sparse.eval_collectBalanced, rawRowCheck3561]

def rawRow3562 : Integer.Sparse Key := [(key1344, -2), (key1338, -2), (key1338, -2), (key1325, 1), (key1317, 1), (key1325, 1), (key1297, 1), (key1317, 1), (key1297, 1), (key1779, 2), (key1773, 2), (key1773, 2), (key1555, -1), (key1547, -1), (key1555, -1), (key1392, -1), (key1547, -1), (key1392, -1), (key1816, -1), (key1814, -1), (key1816, -1), (key1789, -1), (key1814, -1), (key1789, -1), (key1658, 1), (key1656, 1), (key1658, 1), (key1456, 1), (key1656, 1), (key1456, 1)]

theorem rawRowCheck3562 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form7 = rawRow3562 := by decide +kernel

def row3562 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, -2), (key1456, 2), (key1547, -2), (key1555, -2), (key1656, 2), (key1658, 2), (key1773, 4), (key1779, 2), (key1789, -2), (key1814, -2), (key1816, -2)]

theorem rowCheck3562 : row3562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3562 := by decide +kernel

theorem rowEval3562 (x : Key → ℝ) : Integer.Sparse.eval row3562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck3562, Integer.Sparse.eval_collectBalanced, rawRowCheck3562]

def rawRow3563 : Integer.Sparse Key := [(key1456, -2), (key1456, -2), (key1465, -2), (key1392, 1), (key1392, 1), (key1425, 1), (key1425, 1), (key1443, 1), (key1443, 1), (key1789, 2), (key1789, 2), (key1797, 2), (key1297, -1), (key1297, -1), (key1574, -1), (key1574, -1), (key1592, -1), (key1592, -1), (key1773, -1), (key1773, -1), (key1814, -1), (key1814, -1), (key1824, -1), (key1824, -1), (key1338, 1), (key1338, 1), (key1656, 1), (key1656, 1), (key1666, 1), (key1666, 1)]

theorem rawRowCheck3563 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form7 = rawRow3563 := by decide +kernel

def row3563 : Integer.Sparse Key := [(key1297, -2), (key1338, 2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1574, -2), (key1592, -2), (key1656, 2), (key1666, 2), (key1773, -2), (key1789, 4), (key1797, 2), (key1814, -2), (key1824, -2)]

theorem rowCheck3563 : row3563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3563 := by decide +kernel

theorem rowEval3563 (x : Key → ℝ) : Integer.Sparse.eval row3563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3563, Integer.Sparse.eval_collectBalanced, rawRowCheck3563]

def rawRow3564 : Integer.Sparse Key := [(key1456, -2), (key1465, -2), (key1456, -2), (key1425, 1), (key1443, 1), (key1392, 1), (key1443, 1), (key1392, 1), (key1425, 1), (key1789, 2), (key1797, 2), (key1789, 2), (key1574, -1), (key1592, -1), (key1297, -1), (key1592, -1), (key1297, -1), (key1574, -1), (key1814, -1), (key1824, -1), (key1773, -1), (key1824, -1), (key1773, -1), (key1814, -1), (key1656, 1), (key1666, 1), (key1338, 1), (key1666, 1), (key1338, 1), (key1656, 1)]

theorem rawRowCheck3564 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form7 = rawRow3564 := by decide +kernel

def row3564 : Integer.Sparse Key := [(key1297, -2), (key1338, 2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1574, -2), (key1592, -2), (key1656, 2), (key1666, 2), (key1773, -2), (key1789, 4), (key1797, 2), (key1814, -2), (key1824, -2)]

theorem rowCheck3564 : row3564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3564 := by decide +kernel

theorem rowEval3564 (x : Key → ℝ) : Integer.Sparse.eval row3564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3564, Integer.Sparse.eval_collectBalanced, rawRowCheck3564]

def rawRow3565 : Integer.Sparse Key := [(key1465, -2), (key1456, -2), (key1456, -2), (key1443, 1), (key1425, 1), (key1443, 1), (key1392, 1), (key1425, 1), (key1392, 1), (key1797, 2), (key1789, 2), (key1789, 2), (key1592, -1), (key1574, -1), (key1592, -1), (key1297, -1), (key1574, -1), (key1297, -1), (key1824, -1), (key1814, -1), (key1824, -1), (key1773, -1), (key1814, -1), (key1773, -1), (key1666, 1), (key1656, 1), (key1666, 1), (key1338, 1), (key1656, 1), (key1338, 1)]

theorem rawRowCheck3565 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form7 = rawRow3565 := by decide +kernel

def row3565 : Integer.Sparse Key := [(key1297, -2), (key1338, 2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1574, -2), (key1592, -2), (key1656, 2), (key1666, 2), (key1773, -2), (key1789, 4), (key1797, 2), (key1814, -2), (key1824, -2)]

theorem rowCheck3565 : row3565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3565 := by decide +kernel

theorem rowEval3565 (x : Key → ℝ) : Integer.Sparse.eval row3565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3565, Integer.Sparse.eval_collectBalanced, rawRowCheck3565]

def rawRow3566 : Integer.Sparse Key := [(key1773, -2), (key1773, -2), (key1779, -2), (key1789, 1), (key1789, 1), (key1814, 1), (key1814, 1), (key1816, 1), (key1816, 1), (key1338, 2), (key1338, 2), (key1344, 2), (key1456, -1), (key1456, -1), (key1656, -1), (key1656, -1), (key1658, -1), (key1658, -1), (key1297, -1), (key1297, -1), (key1317, -1), (key1317, -1), (key1325, -1), (key1325, -1), (key1392, 1), (key1392, 1), (key1547, 1), (key1547, 1), (key1555, 1), (key1555, 1)]

theorem rawRowCheck3566 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form7 = rawRow3566 := by decide +kernel

def row3566 : Integer.Sparse Key := [(key1297, -2), (key1317, -2), (key1325, -2), (key1338, 4), (key1344, 2), (key1392, 2), (key1456, -2), (key1547, 2), (key1555, 2), (key1656, -2), (key1658, -2), (key1773, -4), (key1779, -2), (key1789, 2), (key1814, 2), (key1816, 2)]

theorem rowCheck3566 : row3566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3566 := by decide +kernel

theorem rowEval3566 (x : Key → ℝ) : Integer.Sparse.eval row3566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3566, Integer.Sparse.eval_collectBalanced, rawRowCheck3566]

def rawRow3567 : Integer.Sparse Key := [(key1773, -2), (key1779, -2), (key1773, -2), (key1814, 1), (key1816, 1), (key1789, 1), (key1816, 1), (key1789, 1), (key1814, 1), (key1338, 2), (key1344, 2), (key1338, 2), (key1656, -1), (key1658, -1), (key1456, -1), (key1658, -1), (key1456, -1), (key1656, -1), (key1317, -1), (key1325, -1), (key1297, -1), (key1325, -1), (key1297, -1), (key1317, -1), (key1547, 1), (key1555, 1), (key1392, 1), (key1555, 1), (key1392, 1), (key1547, 1)]

theorem rawRowCheck3567 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form7 = rawRow3567 := by decide +kernel

def row3567 : Integer.Sparse Key := [(key1297, -2), (key1317, -2), (key1325, -2), (key1338, 4), (key1344, 2), (key1392, 2), (key1456, -2), (key1547, 2), (key1555, 2), (key1656, -2), (key1658, -2), (key1773, -4), (key1779, -2), (key1789, 2), (key1814, 2), (key1816, 2)]

theorem rowCheck3567 : row3567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3567 := by decide +kernel

theorem rowEval3567 (x : Key → ℝ) : Integer.Sparse.eval row3567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3567, Integer.Sparse.eval_collectBalanced, rawRowCheck3567]

def rawRow3568 : Integer.Sparse Key := [(key1779, -2), (key1773, -2), (key1773, -2), (key1816, 1), (key1814, 1), (key1816, 1), (key1789, 1), (key1814, 1), (key1789, 1), (key1344, 2), (key1338, 2), (key1338, 2), (key1658, -1), (key1656, -1), (key1658, -1), (key1456, -1), (key1656, -1), (key1456, -1), (key1325, -1), (key1317, -1), (key1325, -1), (key1297, -1), (key1317, -1), (key1297, -1), (key1555, 1), (key1547, 1), (key1555, 1), (key1392, 1), (key1547, 1), (key1392, 1)]

theorem rawRowCheck3568 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form7 = rawRow3568 := by decide +kernel

def row3568 : Integer.Sparse Key := [(key1297, -2), (key1317, -2), (key1325, -2), (key1338, 4), (key1344, 2), (key1392, 2), (key1456, -2), (key1547, 2), (key1555, 2), (key1656, -2), (key1658, -2), (key1773, -4), (key1779, -2), (key1789, 2), (key1814, 2), (key1816, 2)]

theorem rowCheck3568 : row3568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3568 := by decide +kernel

theorem rowEval3568 (x : Key → ℝ) : Integer.Sparse.eval row3568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck3568, Integer.Sparse.eval_collectBalanced, rawRowCheck3568]

def rawRow3569 : Integer.Sparse Key := [(key1789, -2), (key1789, -2), (key1797, -2), (key1773, 1), (key1773, 1), (key1814, 1), (key1814, 1), (key1824, 1), (key1824, 1), (key1456, 2), (key1456, 2), (key1465, 2), (key1338, -1), (key1338, -1), (key1656, -1), (key1656, -1), (key1666, -1), (key1666, -1), (key1392, -1), (key1392, -1), (key1425, -1), (key1425, -1), (key1443, -1), (key1443, -1), (key1297, 1), (key1297, 1), (key1574, 1), (key1574, 1), (key1592, 1), (key1592, 1)]

theorem rawRowCheck3569 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form7 = rawRow3569 := by decide +kernel

def row3569 : Integer.Sparse Key := [(key1297, 2), (key1338, -2), (key1392, -2), (key1425, -2), (key1443, -2), (key1456, 4), (key1465, 2), (key1574, 2), (key1592, 2), (key1656, -2), (key1666, -2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

theorem rowCheck3569 : row3569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3569 := by decide +kernel

theorem rowEval3569 (x : Key → ℝ) : Integer.Sparse.eval row3569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3569, Integer.Sparse.eval_collectBalanced, rawRowCheck3569]

def rawRow3570 : Integer.Sparse Key := [(key1789, -2), (key1797, -2), (key1789, -2), (key1814, 1), (key1824, 1), (key1773, 1), (key1824, 1), (key1773, 1), (key1814, 1), (key1456, 2), (key1465, 2), (key1456, 2), (key1656, -1), (key1666, -1), (key1338, -1), (key1666, -1), (key1338, -1), (key1656, -1), (key1425, -1), (key1443, -1), (key1392, -1), (key1443, -1), (key1392, -1), (key1425, -1), (key1574, 1), (key1592, 1), (key1297, 1), (key1592, 1), (key1297, 1), (key1574, 1)]

theorem rawRowCheck3570 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form7 = rawRow3570 := by decide +kernel

def row3570 : Integer.Sparse Key := [(key1297, 2), (key1338, -2), (key1392, -2), (key1425, -2), (key1443, -2), (key1456, 4), (key1465, 2), (key1574, 2), (key1592, 2), (key1656, -2), (key1666, -2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

theorem rowCheck3570 : row3570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3570 := by decide +kernel

theorem rowEval3570 (x : Key → ℝ) : Integer.Sparse.eval row3570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3570, Integer.Sparse.eval_collectBalanced, rawRowCheck3570]

def rawRow3571 : Integer.Sparse Key := [(key1797, -2), (key1789, -2), (key1789, -2), (key1824, 1), (key1814, 1), (key1824, 1), (key1773, 1), (key1814, 1), (key1773, 1), (key1465, 2), (key1456, 2), (key1456, 2), (key1666, -1), (key1656, -1), (key1666, -1), (key1338, -1), (key1656, -1), (key1338, -1), (key1443, -1), (key1425, -1), (key1443, -1), (key1392, -1), (key1425, -1), (key1392, -1), (key1592, 1), (key1574, 1), (key1592, 1), (key1297, 1), (key1574, 1), (key1297, 1)]

theorem rawRowCheck3571 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form7 = rawRow3571 := by decide +kernel

def row3571 : Integer.Sparse Key := [(key1297, 2), (key1338, -2), (key1392, -2), (key1425, -2), (key1443, -2), (key1456, 4), (key1465, 2), (key1574, 2), (key1592, 2), (key1656, -2), (key1666, -2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

theorem rowCheck3571 : row3571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3571 := by decide +kernel

theorem rowEval3571 (x : Key → ℝ) : Integer.Sparse.eval row3571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3571, Integer.Sparse.eval_collectBalanced, rawRowCheck3571]

def rawRow3572 : Integer.Sparse Key := [(key997, -2), (key997, -2), (key1012, -2), (key993, 6), (key1189, 2), (key1189, 2), (key1196, 2), (key1028, -2), (key1106, -2), (key1106, -2), (key1209, -6), (key1068, 2), (key1147, 2), (key1147, 2)]

theorem rawRowCheck3572 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form8 = rawRow3572 := by decide +kernel

def row3572 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1068, 2), (key1106, -4), (key1147, 4), (key1189, 4), (key1196, 2), (key1209, -6)]

theorem rowCheck3572 : row3572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3572 := by decide +kernel

theorem rowEval3572 (x : Key → ℝ) : Integer.Sparse.eval row3572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3572, Integer.Sparse.eval_collectBalanced, rawRowCheck3572]

def rawRow3573 : Integer.Sparse Key := [(key997, -2), (key1012, -2), (key997, -2), (key993, 6), (key1189, 2), (key1196, 2), (key1189, 2), (key1106, -2), (key1028, -2), (key1106, -2), (key1209, -6), (key1147, 2), (key1068, 2), (key1147, 2)]

theorem rawRowCheck3573 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form8 = rawRow3573 := by decide +kernel

def row3573 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1068, 2), (key1106, -4), (key1147, 4), (key1189, 4), (key1196, 2), (key1209, -6)]

theorem rowCheck3573 : row3573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3573 := by decide +kernel

theorem rowEval3573 (x : Key → ℝ) : Integer.Sparse.eval row3573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3573, Integer.Sparse.eval_collectBalanced, rawRowCheck3573]

def rawRow3574 : Integer.Sparse Key := [(key1012, -2), (key997, -2), (key997, -2), (key993, 6), (key1196, 2), (key1189, 2), (key1189, 2), (key1106, -2), (key1106, -2), (key1028, -2), (key1209, -6), (key1147, 2), (key1147, 2), (key1068, 2)]

theorem rawRowCheck3574 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form8 = rawRow3574 := by decide +kernel

def row3574 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1068, 2), (key1106, -4), (key1147, 4), (key1189, 4), (key1196, 2), (key1209, -6)]

theorem rowCheck3574 : row3574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3574 := by decide +kernel

theorem rowEval3574 (x : Key → ℝ) : Integer.Sparse.eval row3574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3574, Integer.Sparse.eval_collectBalanced, rawRowCheck3574]

def rawRow3575 : Integer.Sparse Key := [(key1032, -2), (key1032, -2), (key1068, -2), (key1028, 6), (key1189, 2), (key1189, 2), (key1209, 2), (key993, -2), (key1106, -2), (key1106, -2), (key1196, -6), (key1012, 2), (key1120, 2), (key1120, 2)]

theorem rawRowCheck3575 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form8 = rawRow3575 := by decide +kernel

def row3575 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1120, 4), (key1189, 4), (key1196, -6), (key1209, 2)]

theorem rowCheck3575 : row3575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3575 := by decide +kernel

theorem rowEval3575 (x : Key → ℝ) : Integer.Sparse.eval row3575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3575, Integer.Sparse.eval_collectBalanced, rawRowCheck3575]

def rawRow3576 : Integer.Sparse Key := [(key1032, -2), (key1068, -2), (key1032, -2), (key1028, 6), (key1189, 2), (key1209, 2), (key1189, 2), (key1106, -2), (key993, -2), (key1106, -2), (key1196, -6), (key1120, 2), (key1012, 2), (key1120, 2)]

theorem rawRowCheck3576 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form8 = rawRow3576 := by decide +kernel

def row3576 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1120, 4), (key1189, 4), (key1196, -6), (key1209, 2)]

theorem rowCheck3576 : row3576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3576 := by decide +kernel

theorem rowEval3576 (x : Key → ℝ) : Integer.Sparse.eval row3576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3576, Integer.Sparse.eval_collectBalanced, rawRowCheck3576]

def rawRow3577 : Integer.Sparse Key := [(key1068, -2), (key1032, -2), (key1032, -2), (key1028, 6), (key1209, 2), (key1189, 2), (key1189, 2), (key1106, -2), (key1106, -2), (key993, -2), (key1196, -6), (key1120, 2), (key1120, 2), (key1012, 2)]

theorem rawRowCheck3577 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form8 = rawRow3577 := by decide +kernel

def row3577 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1120, 4), (key1189, 4), (key1196, -6), (key1209, 2)]

theorem rowCheck3577 : row3577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3577 := by decide +kernel

theorem rowEval3577 (x : Key → ℝ) : Integer.Sparse.eval row3577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3577, Integer.Sparse.eval_collectBalanced, rawRowCheck3577]

def rawRow3578 : Integer.Sparse Key := [(key1189, -2), (key1189, -2), (key1196, -2), (key1209, 6), (key997, 2), (key997, 2), (key1012, 2), (key1068, -2), (key1147, -2), (key1147, -2), (key993, -6), (key1028, 2), (key1106, 2), (key1106, 2)]

theorem rawRowCheck3578 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form8 = rawRow3578 := by decide +kernel

def row3578 : Integer.Sparse Key := [(key993, -6), (key997, 4), (key1012, 2), (key1028, 2), (key1068, -2), (key1106, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

theorem rowCheck3578 : row3578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3578 := by decide +kernel

theorem rowEval3578 (x : Key → ℝ) : Integer.Sparse.eval row3578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3578, Integer.Sparse.eval_collectBalanced, rawRowCheck3578]

def rawRow3579 : Integer.Sparse Key := [(key1189, -2), (key1196, -2), (key1189, -2), (key1209, 6), (key997, 2), (key1012, 2), (key997, 2), (key1147, -2), (key1068, -2), (key1147, -2), (key993, -6), (key1106, 2), (key1028, 2), (key1106, 2)]

theorem rawRowCheck3579 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form8 = rawRow3579 := by decide +kernel

def row3579 : Integer.Sparse Key := [(key993, -6), (key997, 4), (key1012, 2), (key1028, 2), (key1068, -2), (key1106, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

theorem rowCheck3579 : row3579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3579 := by decide +kernel

theorem rowEval3579 (x : Key → ℝ) : Integer.Sparse.eval row3579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3579, Integer.Sparse.eval_collectBalanced, rawRowCheck3579]

def rawRow3580 : Integer.Sparse Key := [(key1196, -2), (key1189, -2), (key1189, -2), (key1209, 6), (key1012, 2), (key997, 2), (key997, 2), (key1147, -2), (key1147, -2), (key1068, -2), (key993, -6), (key1106, 2), (key1106, 2), (key1028, 2)]

theorem rawRowCheck3580 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form8 = rawRow3580 := by decide +kernel

def row3580 : Integer.Sparse Key := [(key993, -6), (key997, 4), (key1012, 2), (key1028, 2), (key1068, -2), (key1106, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

theorem rowCheck3580 : row3580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3580 := by decide +kernel

theorem rowEval3580 (x : Key → ℝ) : Integer.Sparse.eval row3580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3580, Integer.Sparse.eval_collectBalanced, rawRowCheck3580]

def rawRow3581 : Integer.Sparse Key := [(key1189, -2), (key1189, -2), (key1209, -2), (key1196, 6), (key1032, 2), (key1032, 2), (key1068, 2), (key1012, -2), (key1120, -2), (key1120, -2), (key1028, -6), (key993, 2), (key1106, 2), (key1106, 2)]

theorem rawRowCheck3581 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form8 = rawRow3581 := by decide +kernel

def row3581 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -6), (key1032, 4), (key1068, 2), (key1106, 4), (key1120, -4), (key1189, -4), (key1196, 6), (key1209, -2)]

theorem rowCheck3581 : row3581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3581 := by decide +kernel

theorem rowEval3581 (x : Key → ℝ) : Integer.Sparse.eval row3581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3581, Integer.Sparse.eval_collectBalanced, rawRowCheck3581]

def rawRow3582 : Integer.Sparse Key := [(key1189, -2), (key1209, -2), (key1189, -2), (key1196, 6), (key1032, 2), (key1068, 2), (key1032, 2), (key1120, -2), (key1012, -2), (key1120, -2), (key1028, -6), (key1106, 2), (key993, 2), (key1106, 2)]

theorem rawRowCheck3582 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form8 = rawRow3582 := by decide +kernel

def row3582 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -6), (key1032, 4), (key1068, 2), (key1106, 4), (key1120, -4), (key1189, -4), (key1196, 6), (key1209, -2)]

theorem rowCheck3582 : row3582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3582 := by decide +kernel

theorem rowEval3582 (x : Key → ℝ) : Integer.Sparse.eval row3582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3582, Integer.Sparse.eval_collectBalanced, rawRowCheck3582]

def rawRow3583 : Integer.Sparse Key := [(key1209, -2), (key1189, -2), (key1189, -2), (key1196, 6), (key1068, 2), (key1032, 2), (key1032, 2), (key1120, -2), (key1120, -2), (key1012, -2), (key1028, -6), (key1106, 2), (key1106, 2), (key993, 2)]

theorem rawRowCheck3583 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form8 = rawRow3583 := by decide +kernel

def row3583 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -6), (key1032, 4), (key1068, 2), (key1106, 4), (key1120, -4), (key1189, -4), (key1196, 6), (key1209, -2)]

theorem rowCheck3583 : row3583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3583 := by decide +kernel

theorem rowEval3583 (x : Key → ℝ) : Integer.Sparse.eval row3583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3583, Integer.Sparse.eval_collectBalanced, rawRowCheck3583]

end MUB6.Certificate.GramRows

end OAI
