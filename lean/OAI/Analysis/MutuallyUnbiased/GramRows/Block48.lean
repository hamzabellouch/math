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
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3072 : Integer.Sparse Key := [(key2919, -2), (key2918, -2), (key2922, -2), (key2792, 1), (key2784, 1), (key2858, 1), (key2807, 1), (key2868, 1), (key2827, 1), (key3022, 2), (key3021, 2), (key3025, 2), (key2638, -1), (key2630, -1), (key2858, -1), (key2704, -1), (key2868, -1), (key2724, -1), (key3009, -1), (key3007, -1), (key3022, -1), (key3011, -1), (key3025, -1), (key3016, -1), (key2659, 1), (key2657, 1), (key2919, 1), (key2752, 1), (key2922, 1), (key2757, 1)]

theorem rawRowCheck3072 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form2 = rawRow3072 := by decide +kernel

def row3072 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

theorem rowCheck3072 : row3072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3072 := by decide +kernel

theorem rowEval3072 (x : Key → ℝ) : Integer.Sparse.eval row3072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3072, Integer.Sparse.eval_collectBalanced, rawRowCheck3072]

def rawRow3073 : Integer.Sparse Key := [(key2918, -2), (key2922, -2), (key2919, -2), (key2807, 1), (key2827, 1), (key2784, 1), (key2868, 1), (key2792, 1), (key2858, 1), (key3021, 2), (key3025, 2), (key3022, 2), (key2704, -1), (key2724, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key3011, -1), (key3016, -1), (key3007, -1), (key3025, -1), (key3009, -1), (key3022, -1), (key2752, 1), (key2757, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2919, 1)]

theorem rawRowCheck3073 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form2 = rawRow3073 := by decide +kernel

def row3073 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

theorem rowCheck3073 : row3073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3073 := by decide +kernel

theorem rowEval3073 (x : Key → ℝ) : Integer.Sparse.eval row3073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3073, Integer.Sparse.eval_collectBalanced, rawRowCheck3073]

def rawRow3074 : Integer.Sparse Key := [(key2922, -2), (key2918, -2), (key2919, -2), (key2827, 1), (key2807, 1), (key2868, 1), (key2784, 1), (key2858, 1), (key2792, 1), (key3025, 2), (key3021, 2), (key3022, 2), (key2724, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2858, -1), (key2638, -1), (key3016, -1), (key3011, -1), (key3025, -1), (key3007, -1), (key3022, -1), (key3009, -1), (key2757, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2919, 1), (key2659, 1)]

theorem rawRowCheck3074 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form2 = rawRow3074 := by decide +kernel

def row3074 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

theorem rowCheck3074 : row3074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3074 := by decide +kernel

theorem rowEval3074 (x : Key → ℝ) : Integer.Sparse.eval row3074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3074, Integer.Sparse.eval_collectBalanced, rawRowCheck3074]

def rawRow3075 : Integer.Sparse Key := [(key2919, -2), (key2922, -2), (key2918, -2), (key2858, 1), (key2868, 1), (key2792, 1), (key2827, 1), (key2784, 1), (key2807, 1), (key3022, 2), (key3025, 2), (key3021, 2), (key2858, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2630, -1), (key2704, -1), (key3022, -1), (key3025, -1), (key3009, -1), (key3016, -1), (key3007, -1), (key3011, -1), (key2919, 1), (key2922, 1), (key2659, 1), (key2757, 1), (key2657, 1), (key2752, 1)]

theorem rawRowCheck3075 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form2 = rawRow3075 := by decide +kernel

def row3075 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

theorem rowCheck3075 : row3075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3075 := by decide +kernel

theorem rowEval3075 (x : Key → ℝ) : Integer.Sparse.eval row3075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3075, Integer.Sparse.eval_collectBalanced, rawRowCheck3075]

def rawRow3076 : Integer.Sparse Key := [(key2922, -2), (key2919, -2), (key2918, -2), (key2868, 1), (key2858, 1), (key2827, 1), (key2792, 1), (key2807, 1), (key2784, 1), (key3025, 2), (key3022, 2), (key3021, 2), (key2868, -1), (key2858, -1), (key2724, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key3025, -1), (key3022, -1), (key3016, -1), (key3009, -1), (key3011, -1), (key3007, -1), (key2922, 1), (key2919, 1), (key2757, 1), (key2659, 1), (key2752, 1), (key2657, 1)]

theorem rawRowCheck3076 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form2 = rawRow3076 := by decide +kernel

def row3076 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

theorem rowCheck3076 : row3076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3076 := by decide +kernel

theorem rowEval3076 (x : Key → ℝ) : Integer.Sparse.eval row3076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3076, Integer.Sparse.eval_collectBalanced, rawRowCheck3076]

def rawRow3077 : Integer.Sparse Key := [(key3011, -2), (key3011, -2), (key3016, -2), (key3007, 1), (key3007, 1), (key3021, 1), (key3021, 1), (key3025, 1), (key3025, 1), (key2752, 2), (key2752, 2), (key2757, 2), (key2657, -1), (key2657, -1), (key2918, -1), (key2918, -1), (key2922, -1), (key2922, -1), (key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2724, -1), (key2724, -1), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1)]

theorem rawRowCheck3077 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form2 = rawRow3077 := by decide +kernel

def row3077 : Integer.Sparse Key := [(key2614, 2), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2807, 2), (key2827, 2), (key2918, -2), (key2922, -2), (key3007, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3025, 2)]

theorem rowCheck3077 : row3077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3077 := by decide +kernel

theorem rowEval3077 (x : Key → ℝ) : Integer.Sparse.eval row3077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3077, Integer.Sparse.eval_collectBalanced, rawRowCheck3077]

def rawRow3078 : Integer.Sparse Key := [(key3011, -2), (key3016, -2), (key3011, -2), (key3021, 1), (key3025, 1), (key3007, 1), (key3025, 1), (key3007, 1), (key3021, 1), (key2752, 2), (key2757, 2), (key2752, 2), (key2918, -1), (key2922, -1), (key2657, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1)]

theorem rawRowCheck3078 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form2 = rawRow3078 := by decide +kernel

def row3078 : Integer.Sparse Key := [(key2614, 2), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2807, 2), (key2827, 2), (key2918, -2), (key2922, -2), (key3007, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3025, 2)]

theorem rowCheck3078 : row3078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3078 := by decide +kernel

theorem rowEval3078 (x : Key → ℝ) : Integer.Sparse.eval row3078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3078, Integer.Sparse.eval_collectBalanced, rawRowCheck3078]

def rawRow3079 : Integer.Sparse Key := [(key3016, -2), (key3011, -2), (key3011, -2), (key3025, 1), (key3021, 1), (key3025, 1), (key3007, 1), (key3021, 1), (key3007, 1), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, -1), (key2918, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2657, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1)]

theorem rawRowCheck3079 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form2 = rawRow3079 := by decide +kernel

def row3079 : Integer.Sparse Key := [(key2614, 2), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2807, 2), (key2827, 2), (key2918, -2), (key2922, -2), (key3007, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3025, 2)]

theorem rowCheck3079 : row3079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3079 := by decide +kernel

theorem rowEval3079 (x : Key → ℝ) : Integer.Sparse.eval row3079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3079, Integer.Sparse.eval_collectBalanced, rawRowCheck3079]

def rawRow3080 : Integer.Sparse Key := [(key3021, -2), (key3022, -2), (key3025, -2), (key3007, 1), (key3009, 1), (key3011, 1), (key3022, 1), (key3016, 1), (key3025, 1), (key2918, 2), (key2919, 2), (key2922, 2), (key2657, -1), (key2659, -1), (key2752, -1), (key2919, -1), (key2757, -1), (key2922, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2858, -1), (key2827, -1), (key2868, -1), (key2630, 1), (key2638, 1), (key2704, 1), (key2858, 1), (key2724, 1), (key2868, 1)]

theorem rawRowCheck3080 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form2 = rawRow3080 := by decide +kernel

def row3080 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck3080 : row3080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3080 := by decide +kernel

theorem rowEval3080 (x : Key → ℝ) : Integer.Sparse.eval row3080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3080, Integer.Sparse.eval_collectBalanced, rawRowCheck3080]

def rawRow3081 : Integer.Sparse Key := [(key3022, -2), (key3021, -2), (key3025, -2), (key3009, 1), (key3007, 1), (key3022, 1), (key3011, 1), (key3025, 1), (key3016, 1), (key2919, 2), (key2918, 2), (key2922, 2), (key2659, -1), (key2657, -1), (key2919, -1), (key2752, -1), (key2922, -1), (key2757, -1), (key2792, -1), (key2784, -1), (key2858, -1), (key2807, -1), (key2868, -1), (key2827, -1), (key2638, 1), (key2630, 1), (key2858, 1), (key2704, 1), (key2868, 1), (key2724, 1)]

theorem rawRowCheck3081 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form2 = rawRow3081 := by decide +kernel

def row3081 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck3081 : row3081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3081 := by decide +kernel

theorem rowEval3081 (x : Key → ℝ) : Integer.Sparse.eval row3081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3081, Integer.Sparse.eval_collectBalanced, rawRowCheck3081]

def rawRow3082 : Integer.Sparse Key := [(key3021, -2), (key3025, -2), (key3022, -2), (key3011, 1), (key3016, 1), (key3007, 1), (key3025, 1), (key3009, 1), (key3022, 1), (key2918, 2), (key2922, 2), (key2919, 2), (key2752, -1), (key2757, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2807, -1), (key2827, -1), (key2784, -1), (key2868, -1), (key2792, -1), (key2858, -1), (key2704, 1), (key2724, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2858, 1)]

theorem rawRowCheck3082 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form2 = rawRow3082 := by decide +kernel

def row3082 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck3082 : row3082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3082 := by decide +kernel

theorem rowEval3082 (x : Key → ℝ) : Integer.Sparse.eval row3082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3082, Integer.Sparse.eval_collectBalanced, rawRowCheck3082]

def rawRow3083 : Integer.Sparse Key := [(key3025, -2), (key3021, -2), (key3022, -2), (key3016, 1), (key3011, 1), (key3025, 1), (key3007, 1), (key3022, 1), (key3009, 1), (key2922, 2), (key2918, 2), (key2919, 2), (key2757, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2919, -1), (key2659, -1), (key2827, -1), (key2807, -1), (key2868, -1), (key2784, -1), (key2858, -1), (key2792, -1), (key2724, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2858, 1), (key2638, 1)]

theorem rawRowCheck3083 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form2 = rawRow3083 := by decide +kernel

def row3083 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck3083 : row3083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3083 := by decide +kernel

theorem rowEval3083 (x : Key → ℝ) : Integer.Sparse.eval row3083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3083, Integer.Sparse.eval_collectBalanced, rawRowCheck3083]

def rawRow3084 : Integer.Sparse Key := [(key3022, -2), (key3025, -2), (key3021, -2), (key3022, 1), (key3025, 1), (key3009, 1), (key3016, 1), (key3007, 1), (key3011, 1), (key2919, 2), (key2922, 2), (key2918, 2), (key2919, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2657, -1), (key2752, -1), (key2858, -1), (key2868, -1), (key2792, -1), (key2827, -1), (key2784, -1), (key2807, -1), (key2858, 1), (key2868, 1), (key2638, 1), (key2724, 1), (key2630, 1), (key2704, 1)]

theorem rawRowCheck3084 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form2 = rawRow3084 := by decide +kernel

def row3084 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck3084 : row3084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3084 := by decide +kernel

theorem rowEval3084 (x : Key → ℝ) : Integer.Sparse.eval row3084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3084, Integer.Sparse.eval_collectBalanced, rawRowCheck3084]

def rawRow3085 : Integer.Sparse Key := [(key3025, -2), (key3022, -2), (key3021, -2), (key3025, 1), (key3022, 1), (key3016, 1), (key3009, 1), (key3011, 1), (key3007, 1), (key2922, 2), (key2919, 2), (key2918, 2), (key2922, -1), (key2919, -1), (key2757, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2868, -1), (key2858, -1), (key2827, -1), (key2792, -1), (key2807, -1), (key2784, -1), (key2868, 1), (key2858, 1), (key2724, 1), (key2638, 1), (key2704, 1), (key2630, 1)]

theorem rawRowCheck3085 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form2 = rawRow3085 := by decide +kernel

def row3085 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck3085 : row3085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3085 := by decide +kernel

theorem rowEval3085 (x : Key → ℝ) : Integer.Sparse.eval row3085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3085, Integer.Sparse.eval_collectBalanced, rawRowCheck3085]

def rawRow3086 : Integer.Sparse Key := [(key1028, -2), (key1036, -2), (key1071, -2), (key1036, 6), (key1106, 2), (key1114, 2), (key1150, 2), (key1001, -2), (key1114, -2), (key1232, -2), (key1123, -6), (key1015, 2), (key1123, 2), (key1235, 2)]

theorem rawRowCheck3086 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form3 = rawRow3086 := by decide +kernel

def row3086 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

theorem rowCheck3086 : row3086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3086 := by decide +kernel

theorem rowEval3086 (x : Key → ℝ) : Integer.Sparse.eval row3086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3086, Integer.Sparse.eval_collectBalanced, rawRowCheck3086]

def rawRow3087 : Integer.Sparse Key := [(key1036, -2), (key1028, -2), (key1071, -2), (key1036, 6), (key1114, 2), (key1106, 2), (key1150, 2), (key1001, -2), (key1232, -2), (key1114, -2), (key1123, -6), (key1015, 2), (key1235, 2), (key1123, 2)]

theorem rawRowCheck3087 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form3 = rawRow3087 := by decide +kernel

def row3087 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

theorem rowCheck3087 : row3087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3087 := by decide +kernel

theorem rowEval3087 (x : Key → ℝ) : Integer.Sparse.eval row3087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3087, Integer.Sparse.eval_collectBalanced, rawRowCheck3087]

def rawRow3088 : Integer.Sparse Key := [(key1028, -2), (key1071, -2), (key1036, -2), (key1036, 6), (key1106, 2), (key1150, 2), (key1114, 2), (key1114, -2), (key1001, -2), (key1232, -2), (key1123, -6), (key1123, 2), (key1015, 2), (key1235, 2)]

theorem rawRowCheck3088 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form3 = rawRow3088 := by decide +kernel

def row3088 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

theorem rowCheck3088 : row3088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3088 := by decide +kernel

theorem rowEval3088 (x : Key → ℝ) : Integer.Sparse.eval row3088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3088, Integer.Sparse.eval_collectBalanced, rawRowCheck3088]

def rawRow3089 : Integer.Sparse Key := [(key1071, -2), (key1028, -2), (key1036, -2), (key1036, 6), (key1150, 2), (key1106, 2), (key1114, 2), (key1114, -2), (key1232, -2), (key1001, -2), (key1123, -6), (key1123, 2), (key1235, 2), (key1015, 2)]

theorem rawRowCheck3089 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form3 = rawRow3089 := by decide +kernel

def row3089 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

theorem rowCheck3089 : row3089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3089 := by decide +kernel

theorem rowEval3089 (x : Key → ℝ) : Integer.Sparse.eval row3089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3089, Integer.Sparse.eval_collectBalanced, rawRowCheck3089]

def rawRow3090 : Integer.Sparse Key := [(key1036, -2), (key1071, -2), (key1028, -2), (key1036, 6), (key1114, 2), (key1150, 2), (key1106, 2), (key1232, -2), (key1001, -2), (key1114, -2), (key1123, -6), (key1235, 2), (key1015, 2), (key1123, 2)]

theorem rawRowCheck3090 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form3 = rawRow3090 := by decide +kernel

def row3090 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

theorem rowCheck3090 : row3090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3090 := by decide +kernel

theorem rowEval3090 (x : Key → ℝ) : Integer.Sparse.eval row3090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3090, Integer.Sparse.eval_collectBalanced, rawRowCheck3090]

def rawRow3091 : Integer.Sparse Key := [(key1071, -2), (key1036, -2), (key1028, -2), (key1036, 6), (key1150, 2), (key1114, 2), (key1106, 2), (key1232, -2), (key1114, -2), (key1001, -2), (key1123, -6), (key1235, 2), (key1123, 2), (key1015, 2)]

theorem rawRowCheck3091 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form3 = rawRow3091 := by decide +kernel

def row3091 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

theorem rowCheck3091 : row3091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3091 := by decide +kernel

theorem rowEval3091 (x : Key → ℝ) : Integer.Sparse.eval row3091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3091, Integer.Sparse.eval_collectBalanced, rawRowCheck3091]

def rawRow3092 : Integer.Sparse Key := [(key1036, -2), (key1036, -2), (key1071, -2), (key1028, 6), (key1232, 2), (key1232, 2), (key1242, 2), (key993, -2), (key1106, -2), (key1106, -2), (key1235, -6), (key1015, 2), (key1123, 2), (key1123, 2)]

theorem rawRowCheck3092 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form3 = rawRow3092 := by decide +kernel

def row3092 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1123, 4), (key1232, 4), (key1235, -6), (key1242, 2)]

theorem rowCheck3092 : row3092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3092 := by decide +kernel

theorem rowEval3092 (x : Key → ℝ) : Integer.Sparse.eval row3092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3092, Integer.Sparse.eval_collectBalanced, rawRowCheck3092]

def rawRow3093 : Integer.Sparse Key := [(key1036, -2), (key1071, -2), (key1036, -2), (key1028, 6), (key1232, 2), (key1242, 2), (key1232, 2), (key1106, -2), (key993, -2), (key1106, -2), (key1235, -6), (key1123, 2), (key1015, 2), (key1123, 2)]

theorem rawRowCheck3093 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form3 = rawRow3093 := by decide +kernel

def row3093 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1123, 4), (key1232, 4), (key1235, -6), (key1242, 2)]

theorem rowCheck3093 : row3093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3093 := by decide +kernel

theorem rowEval3093 (x : Key → ℝ) : Integer.Sparse.eval row3093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3093, Integer.Sparse.eval_collectBalanced, rawRowCheck3093]

def rawRow3094 : Integer.Sparse Key := [(key1071, -2), (key1036, -2), (key1036, -2), (key1028, 6), (key1242, 2), (key1232, 2), (key1232, 2), (key1106, -2), (key1106, -2), (key993, -2), (key1235, -6), (key1123, 2), (key1123, 2), (key1015, 2)]

theorem rawRowCheck3094 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form3 = rawRow3094 := by decide +kernel

def row3094 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1123, 4), (key1232, 4), (key1235, -6), (key1242, 2)]

theorem rowCheck3094 : row3094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3094 := by decide +kernel

theorem rowEval3094 (x : Key → ℝ) : Integer.Sparse.eval row3094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3094, Integer.Sparse.eval_collectBalanced, rawRowCheck3094]

def rawRow3095 : Integer.Sparse Key := [(key1106, -2), (key1114, -2), (key1150, -2), (key1123, 6), (key1028, 2), (key1036, 2), (key1071, 2), (key1015, -2), (key1123, -2), (key1235, -2), (key1036, -6), (key1001, 2), (key1114, 2), (key1232, 2)]

theorem rawRowCheck3095 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form3 = rawRow3095 := by decide +kernel

def row3095 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

theorem rowCheck3095 : row3095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3095 := by decide +kernel

theorem rowEval3095 (x : Key → ℝ) : Integer.Sparse.eval row3095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3095, Integer.Sparse.eval_collectBalanced, rawRowCheck3095]

def rawRow3096 : Integer.Sparse Key := [(key1114, -2), (key1106, -2), (key1150, -2), (key1123, 6), (key1036, 2), (key1028, 2), (key1071, 2), (key1015, -2), (key1235, -2), (key1123, -2), (key1036, -6), (key1001, 2), (key1232, 2), (key1114, 2)]

theorem rawRowCheck3096 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form3 = rawRow3096 := by decide +kernel

def row3096 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

theorem rowCheck3096 : row3096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3096 := by decide +kernel

theorem rowEval3096 (x : Key → ℝ) : Integer.Sparse.eval row3096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3096, Integer.Sparse.eval_collectBalanced, rawRowCheck3096]

def rawRow3097 : Integer.Sparse Key := [(key1106, -2), (key1150, -2), (key1114, -2), (key1123, 6), (key1028, 2), (key1071, 2), (key1036, 2), (key1123, -2), (key1015, -2), (key1235, -2), (key1036, -6), (key1114, 2), (key1001, 2), (key1232, 2)]

theorem rawRowCheck3097 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form3 = rawRow3097 := by decide +kernel

def row3097 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

theorem rowCheck3097 : row3097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3097 := by decide +kernel

theorem rowEval3097 (x : Key → ℝ) : Integer.Sparse.eval row3097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3097, Integer.Sparse.eval_collectBalanced, rawRowCheck3097]

def rawRow3098 : Integer.Sparse Key := [(key1150, -2), (key1106, -2), (key1114, -2), (key1123, 6), (key1071, 2), (key1028, 2), (key1036, 2), (key1123, -2), (key1235, -2), (key1015, -2), (key1036, -6), (key1114, 2), (key1232, 2), (key1001, 2)]

theorem rawRowCheck3098 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form3 = rawRow3098 := by decide +kernel

def row3098 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

theorem rowCheck3098 : row3098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3098 := by decide +kernel

theorem rowEval3098 (x : Key → ℝ) : Integer.Sparse.eval row3098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3098, Integer.Sparse.eval_collectBalanced, rawRowCheck3098]

def rawRow3099 : Integer.Sparse Key := [(key1114, -2), (key1150, -2), (key1106, -2), (key1123, 6), (key1036, 2), (key1071, 2), (key1028, 2), (key1235, -2), (key1015, -2), (key1123, -2), (key1036, -6), (key1232, 2), (key1001, 2), (key1114, 2)]

theorem rawRowCheck3099 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form3 = rawRow3099 := by decide +kernel

def row3099 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

theorem rowCheck3099 : row3099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3099 := by decide +kernel

theorem rowEval3099 (x : Key → ℝ) : Integer.Sparse.eval row3099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3099, Integer.Sparse.eval_collectBalanced, rawRowCheck3099]

def rawRow3100 : Integer.Sparse Key := [(key1150, -2), (key1114, -2), (key1106, -2), (key1123, 6), (key1071, 2), (key1036, 2), (key1028, 2), (key1235, -2), (key1123, -2), (key1015, -2), (key1036, -6), (key1232, 2), (key1114, 2), (key1001, 2)]

theorem rawRowCheck3100 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form3 = rawRow3100 := by decide +kernel

def row3100 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

theorem rowCheck3100 : row3100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3100 := by decide +kernel

theorem rowEval3100 (x : Key → ℝ) : Integer.Sparse.eval row3100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3100, Integer.Sparse.eval_collectBalanced, rawRowCheck3100]

def rawRow3101 : Integer.Sparse Key := [(key1114, -2), (key1123, -2), (key1150, -2), (key1106, 6), (key1232, 2), (key1235, 2), (key1242, 2), (key993, -2), (key1028, -2), (key1106, -2), (key1232, -6), (key1001, 2), (key1036, 2), (key1114, 2)]

theorem rawRowCheck3101 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form3 = rawRow3101 := by decide +kernel

def row3101 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

theorem rowCheck3101 : row3101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3101 := by decide +kernel

theorem rowEval3101 (x : Key → ℝ) : Integer.Sparse.eval row3101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3101, Integer.Sparse.eval_collectBalanced, rawRowCheck3101]

def rawRow3102 : Integer.Sparse Key := [(key1123, -2), (key1114, -2), (key1150, -2), (key1106, 6), (key1235, 2), (key1232, 2), (key1242, 2), (key993, -2), (key1106, -2), (key1028, -2), (key1232, -6), (key1001, 2), (key1114, 2), (key1036, 2)]

theorem rawRowCheck3102 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form3 = rawRow3102 := by decide +kernel

def row3102 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

theorem rowCheck3102 : row3102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3102 := by decide +kernel

theorem rowEval3102 (x : Key → ℝ) : Integer.Sparse.eval row3102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3102, Integer.Sparse.eval_collectBalanced, rawRowCheck3102]

def rawRow3103 : Integer.Sparse Key := [(key1114, -2), (key1150, -2), (key1123, -2), (key1106, 6), (key1232, 2), (key1242, 2), (key1235, 2), (key1028, -2), (key993, -2), (key1106, -2), (key1232, -6), (key1036, 2), (key1001, 2), (key1114, 2)]

theorem rawRowCheck3103 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form3 = rawRow3103 := by decide +kernel

def row3103 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

theorem rowCheck3103 : row3103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3103 := by decide +kernel

theorem rowEval3103 (x : Key → ℝ) : Integer.Sparse.eval row3103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3103, Integer.Sparse.eval_collectBalanced, rawRowCheck3103]

def rawRow3104 : Integer.Sparse Key := [(key1150, -2), (key1114, -2), (key1123, -2), (key1106, 6), (key1242, 2), (key1232, 2), (key1235, 2), (key1028, -2), (key1106, -2), (key993, -2), (key1232, -6), (key1036, 2), (key1114, 2), (key1001, 2)]

theorem rawRowCheck3104 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form3 = rawRow3104 := by decide +kernel

def row3104 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

theorem rowCheck3104 : row3104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3104 := by decide +kernel

theorem rowEval3104 (x : Key → ℝ) : Integer.Sparse.eval row3104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3104, Integer.Sparse.eval_collectBalanced, rawRowCheck3104]

def rawRow3105 : Integer.Sparse Key := [(key1123, -2), (key1150, -2), (key1114, -2), (key1106, 6), (key1235, 2), (key1242, 2), (key1232, 2), (key1106, -2), (key993, -2), (key1028, -2), (key1232, -6), (key1114, 2), (key1001, 2), (key1036, 2)]

theorem rawRowCheck3105 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form3 = rawRow3105 := by decide +kernel

def row3105 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

theorem rowCheck3105 : row3105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3105 := by decide +kernel

theorem rowEval3105 (x : Key → ℝ) : Integer.Sparse.eval row3105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3105, Integer.Sparse.eval_collectBalanced, rawRowCheck3105]

def rawRow3106 : Integer.Sparse Key := [(key1150, -2), (key1123, -2), (key1114, -2), (key1106, 6), (key1242, 2), (key1235, 2), (key1232, 2), (key1106, -2), (key1028, -2), (key993, -2), (key1232, -6), (key1114, 2), (key1036, 2), (key1001, 2)]

theorem rawRowCheck3106 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form3 = rawRow3106 := by decide +kernel

def row3106 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

theorem rowCheck3106 : row3106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3106 := by decide +kernel

theorem rowEval3106 (x : Key → ℝ) : Integer.Sparse.eval row3106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3106, Integer.Sparse.eval_collectBalanced, rawRowCheck3106]

def rawRow3107 : Integer.Sparse Key := [(key1232, -2), (key1232, -2), (key1242, -2), (key1235, 6), (key1036, 2), (key1036, 2), (key1071, 2), (key1015, -2), (key1123, -2), (key1123, -2), (key1028, -6), (key993, 2), (key1106, 2), (key1106, 2)]

theorem rawRowCheck3107 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow3107 := by decide +kernel

def row3107 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -6), (key1036, 4), (key1071, 2), (key1106, 4), (key1123, -4), (key1232, -4), (key1235, 6), (key1242, -2)]

theorem rowCheck3107 : row3107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3107 := by decide +kernel

theorem rowEval3107 (x : Key → ℝ) : Integer.Sparse.eval row3107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3107, Integer.Sparse.eval_collectBalanced, rawRowCheck3107]

def rawRow3108 : Integer.Sparse Key := [(key1232, -2), (key1242, -2), (key1232, -2), (key1235, 6), (key1036, 2), (key1071, 2), (key1036, 2), (key1123, -2), (key1015, -2), (key1123, -2), (key1028, -6), (key1106, 2), (key993, 2), (key1106, 2)]

theorem rawRowCheck3108 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow3108 := by decide +kernel

def row3108 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -6), (key1036, 4), (key1071, 2), (key1106, 4), (key1123, -4), (key1232, -4), (key1235, 6), (key1242, -2)]

theorem rowCheck3108 : row3108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3108 := by decide +kernel

theorem rowEval3108 (x : Key → ℝ) : Integer.Sparse.eval row3108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3108, Integer.Sparse.eval_collectBalanced, rawRowCheck3108]

def rawRow3109 : Integer.Sparse Key := [(key1242, -2), (key1232, -2), (key1232, -2), (key1235, 6), (key1071, 2), (key1036, 2), (key1036, 2), (key1123, -2), (key1123, -2), (key1015, -2), (key1028, -6), (key1106, 2), (key1106, 2), (key993, 2)]

theorem rawRowCheck3109 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow3109 := by decide +kernel

def row3109 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -6), (key1036, 4), (key1071, 2), (key1106, 4), (key1123, -4), (key1232, -4), (key1235, 6), (key1242, -2)]

theorem rowCheck3109 : row3109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3109 := by decide +kernel

theorem rowEval3109 (x : Key → ℝ) : Integer.Sparse.eval row3109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3109, Integer.Sparse.eval_collectBalanced, rawRowCheck3109]

def rawRow3110 : Integer.Sparse Key := [(key1232, -2), (key1235, -2), (key1242, -2), (key1232, 6), (key1114, 2), (key1123, 2), (key1150, 2), (key1001, -2), (key1036, -2), (key1114, -2), (key1106, -6), (key993, 2), (key1028, 2), (key1106, 2)]

theorem rawRowCheck3110 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form3 = rawRow3110 := by decide +kernel

def row3110 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck3110 : row3110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3110 := by decide +kernel

theorem rowEval3110 (x : Key → ℝ) : Integer.Sparse.eval row3110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3110, Integer.Sparse.eval_collectBalanced, rawRowCheck3110]

def rawRow3111 : Integer.Sparse Key := [(key1235, -2), (key1232, -2), (key1242, -2), (key1232, 6), (key1123, 2), (key1114, 2), (key1150, 2), (key1001, -2), (key1114, -2), (key1036, -2), (key1106, -6), (key993, 2), (key1106, 2), (key1028, 2)]

theorem rawRowCheck3111 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form3 = rawRow3111 := by decide +kernel

def row3111 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck3111 : row3111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3111 := by decide +kernel

theorem rowEval3111 (x : Key → ℝ) : Integer.Sparse.eval row3111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3111, Integer.Sparse.eval_collectBalanced, rawRowCheck3111]

def rawRow3112 : Integer.Sparse Key := [(key1232, -2), (key1242, -2), (key1235, -2), (key1232, 6), (key1114, 2), (key1150, 2), (key1123, 2), (key1036, -2), (key1001, -2), (key1114, -2), (key1106, -6), (key1028, 2), (key993, 2), (key1106, 2)]

theorem rawRowCheck3112 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form3 = rawRow3112 := by decide +kernel

def row3112 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck3112 : row3112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3112 := by decide +kernel

theorem rowEval3112 (x : Key → ℝ) : Integer.Sparse.eval row3112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3112, Integer.Sparse.eval_collectBalanced, rawRowCheck3112]

def rawRow3113 : Integer.Sparse Key := [(key1242, -2), (key1232, -2), (key1235, -2), (key1232, 6), (key1150, 2), (key1114, 2), (key1123, 2), (key1036, -2), (key1114, -2), (key1001, -2), (key1106, -6), (key1028, 2), (key1106, 2), (key993, 2)]

theorem rawRowCheck3113 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form3 = rawRow3113 := by decide +kernel

def row3113 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck3113 : row3113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3113 := by decide +kernel

theorem rowEval3113 (x : Key → ℝ) : Integer.Sparse.eval row3113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3113, Integer.Sparse.eval_collectBalanced, rawRowCheck3113]

def rawRow3114 : Integer.Sparse Key := [(key1235, -2), (key1242, -2), (key1232, -2), (key1232, 6), (key1123, 2), (key1150, 2), (key1114, 2), (key1114, -2), (key1001, -2), (key1036, -2), (key1106, -6), (key1106, 2), (key993, 2), (key1028, 2)]

theorem rawRowCheck3114 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form3 = rawRow3114 := by decide +kernel

def row3114 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck3114 : row3114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3114 := by decide +kernel

theorem rowEval3114 (x : Key → ℝ) : Integer.Sparse.eval row3114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3114, Integer.Sparse.eval_collectBalanced, rawRowCheck3114]

def rawRow3115 : Integer.Sparse Key := [(key1242, -2), (key1235, -2), (key1232, -2), (key1232, 6), (key1150, 2), (key1123, 2), (key1114, 2), (key1114, -2), (key1036, -2), (key1001, -2), (key1106, -6), (key1106, 2), (key1028, 2), (key993, 2)]

theorem rawRowCheck3115 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form3 = rawRow3115 := by decide +kernel

def row3115 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck3115 : row3115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3115 := by decide +kernel

theorem rowEval3115 (x : Key → ℝ) : Integer.Sparse.eval row3115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3115, Integer.Sparse.eval_collectBalanced, rawRowCheck3115]

def rawRow3116 : Integer.Sparse Key := [(key2780, -6), (key2665, 2), (key2780, 2), (key2789, 2), (key2803, 6), (key2610, -2), (key2803, -2), (key2824, -2), (key2700, -2), (key2853, -2), (key2855, -2), (key2626, 2), (key2853, 2), (key2865, 2)]

theorem rawRowCheck3116 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form4 = rawRow3116 := by decide +kernel

def row3116 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

theorem rowCheck3116 : row3116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3116 := by decide +kernel

theorem rowEval3116 (x : Key → ℝ) : Integer.Sparse.eval row3116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3116, Integer.Sparse.eval_collectBalanced, rawRowCheck3116]

def rawRow3117 : Integer.Sparse Key := [(key2780, -6), (key2665, 2), (key2789, 2), (key2780, 2), (key2803, 6), (key2610, -2), (key2824, -2), (key2803, -2), (key2700, -2), (key2855, -2), (key2853, -2), (key2626, 2), (key2865, 2), (key2853, 2)]

theorem rawRowCheck3117 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form4 = rawRow3117 := by decide +kernel

def row3117 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

theorem rowCheck3117 : row3117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3117 := by decide +kernel

theorem rowEval3117 (x : Key → ℝ) : Integer.Sparse.eval row3117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3117, Integer.Sparse.eval_collectBalanced, rawRowCheck3117]

def rawRow3118 : Integer.Sparse Key := [(key2780, -6), (key2780, 2), (key2665, 2), (key2789, 2), (key2803, 6), (key2803, -2), (key2610, -2), (key2824, -2), (key2853, -2), (key2700, -2), (key2855, -2), (key2853, 2), (key2626, 2), (key2865, 2)]

theorem rawRowCheck3118 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form4 = rawRow3118 := by decide +kernel

def row3118 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

theorem rowCheck3118 : row3118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3118 := by decide +kernel

theorem rowEval3118 (x : Key → ℝ) : Integer.Sparse.eval row3118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3118, Integer.Sparse.eval_collectBalanced, rawRowCheck3118]

def rawRow3119 : Integer.Sparse Key := [(key2780, -6), (key2780, 2), (key2789, 2), (key2665, 2), (key2803, 6), (key2803, -2), (key2824, -2), (key2610, -2), (key2853, -2), (key2855, -2), (key2700, -2), (key2853, 2), (key2865, 2), (key2626, 2)]

theorem rawRowCheck3119 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form4 = rawRow3119 := by decide +kernel

def row3119 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

theorem rowCheck3119 : row3119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3119 := by decide +kernel

theorem rowEval3119 (x : Key → ℝ) : Integer.Sparse.eval row3119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3119, Integer.Sparse.eval_collectBalanced, rawRowCheck3119]

def rawRow3120 : Integer.Sparse Key := [(key2780, -6), (key2789, 2), (key2665, 2), (key2780, 2), (key2803, 6), (key2824, -2), (key2610, -2), (key2803, -2), (key2855, -2), (key2700, -2), (key2853, -2), (key2865, 2), (key2626, 2), (key2853, 2)]

theorem rawRowCheck3120 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form4 = rawRow3120 := by decide +kernel

def row3120 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

theorem rowCheck3120 : row3120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3120 := by decide +kernel

theorem rowEval3120 (x : Key → ℝ) : Integer.Sparse.eval row3120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3120, Integer.Sparse.eval_collectBalanced, rawRowCheck3120]

def rawRow3121 : Integer.Sparse Key := [(key2780, -6), (key2789, 2), (key2780, 2), (key2665, 2), (key2803, 6), (key2824, -2), (key2803, -2), (key2610, -2), (key2855, -2), (key2853, -2), (key2700, -2), (key2865, 2), (key2853, 2), (key2626, 2)]

theorem rawRowCheck3121 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form4 = rawRow3121 := by decide +kernel

def row3121 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

theorem rowCheck3121 : row3121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3121 := by decide +kernel

theorem rowEval3121 (x : Key → ℝ) : Integer.Sparse.eval row3121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3121, Integer.Sparse.eval_collectBalanced, rawRowCheck3121]

def rawRow3122 : Integer.Sparse Key := [(key2789, -6), (key2665, 2), (key2780, 2), (key2780, 2), (key2824, 6), (key2610, -2), (key2803, -2), (key2803, -2), (key2721, -2), (key2865, -2), (key2865, -2), (key2635, 2), (key2855, 2), (key2855, 2)]

theorem rawRowCheck3122 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form4 = rawRow3122 := by decide +kernel

def row3122 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, 2), (key2721, -2), (key2780, 4), (key2789, -6), (key2803, -4), (key2824, 6), (key2855, 4), (key2865, -4)]

theorem rowCheck3122 : row3122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3122 := by decide +kernel

theorem rowEval3122 (x : Key → ℝ) : Integer.Sparse.eval row3122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3122, Integer.Sparse.eval_collectBalanced, rawRowCheck3122]

def rawRow3123 : Integer.Sparse Key := [(key2789, -6), (key2780, 2), (key2665, 2), (key2780, 2), (key2824, 6), (key2803, -2), (key2610, -2), (key2803, -2), (key2865, -2), (key2721, -2), (key2865, -2), (key2855, 2), (key2635, 2), (key2855, 2)]

theorem rawRowCheck3123 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form4 = rawRow3123 := by decide +kernel

def row3123 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, 2), (key2721, -2), (key2780, 4), (key2789, -6), (key2803, -4), (key2824, 6), (key2855, 4), (key2865, -4)]

theorem rowCheck3123 : row3123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3123 := by decide +kernel

theorem rowEval3123 (x : Key → ℝ) : Integer.Sparse.eval row3123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3123, Integer.Sparse.eval_collectBalanced, rawRowCheck3123]

def rawRow3124 : Integer.Sparse Key := [(key2789, -6), (key2780, 2), (key2780, 2), (key2665, 2), (key2824, 6), (key2803, -2), (key2803, -2), (key2610, -2), (key2865, -2), (key2865, -2), (key2721, -2), (key2855, 2), (key2855, 2), (key2635, 2)]

theorem rawRowCheck3124 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form4 = rawRow3124 := by decide +kernel

def row3124 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, 2), (key2721, -2), (key2780, 4), (key2789, -6), (key2803, -4), (key2824, 6), (key2855, 4), (key2865, -4)]

theorem rowCheck3124 : row3124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3124 := by decide +kernel

theorem rowEval3124 (x : Key → ℝ) : Integer.Sparse.eval row3124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3124, Integer.Sparse.eval_collectBalanced, rawRowCheck3124]

def rawRow3125 : Integer.Sparse Key := [(key2803, -6), (key2700, 2), (key2853, 2), (key2855, 2), (key2780, 6), (key2626, -2), (key2853, -2), (key2865, -2), (key2665, -2), (key2780, -2), (key2789, -2), (key2610, 2), (key2803, 2), (key2824, 2)]

theorem rawRowCheck3125 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form4 = rawRow3125 := by decide +kernel

def row3125 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

theorem rowCheck3125 : row3125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3125 := by decide +kernel

theorem rowEval3125 (x : Key → ℝ) : Integer.Sparse.eval row3125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3125, Integer.Sparse.eval_collectBalanced, rawRowCheck3125]

def rawRow3126 : Integer.Sparse Key := [(key2803, -6), (key2700, 2), (key2855, 2), (key2853, 2), (key2780, 6), (key2626, -2), (key2865, -2), (key2853, -2), (key2665, -2), (key2789, -2), (key2780, -2), (key2610, 2), (key2824, 2), (key2803, 2)]

theorem rawRowCheck3126 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form4 = rawRow3126 := by decide +kernel

def row3126 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

theorem rowCheck3126 : row3126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3126 := by decide +kernel

theorem rowEval3126 (x : Key → ℝ) : Integer.Sparse.eval row3126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3126, Integer.Sparse.eval_collectBalanced, rawRowCheck3126]

def rawRow3127 : Integer.Sparse Key := [(key2803, -6), (key2853, 2), (key2700, 2), (key2855, 2), (key2780, 6), (key2853, -2), (key2626, -2), (key2865, -2), (key2780, -2), (key2665, -2), (key2789, -2), (key2803, 2), (key2610, 2), (key2824, 2)]

theorem rawRowCheck3127 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form4 = rawRow3127 := by decide +kernel

def row3127 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

theorem rowCheck3127 : row3127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3127 := by decide +kernel

theorem rowEval3127 (x : Key → ℝ) : Integer.Sparse.eval row3127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3127, Integer.Sparse.eval_collectBalanced, rawRowCheck3127]

def rawRow3128 : Integer.Sparse Key := [(key2803, -6), (key2853, 2), (key2855, 2), (key2700, 2), (key2780, 6), (key2853, -2), (key2865, -2), (key2626, -2), (key2780, -2), (key2789, -2), (key2665, -2), (key2803, 2), (key2824, 2), (key2610, 2)]

theorem rawRowCheck3128 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form4 = rawRow3128 := by decide +kernel

def row3128 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

theorem rowCheck3128 : row3128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3128 := by decide +kernel

theorem rowEval3128 (x : Key → ℝ) : Integer.Sparse.eval row3128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3128, Integer.Sparse.eval_collectBalanced, rawRowCheck3128]

def rawRow3129 : Integer.Sparse Key := [(key2803, -6), (key2855, 2), (key2700, 2), (key2853, 2), (key2780, 6), (key2865, -2), (key2626, -2), (key2853, -2), (key2789, -2), (key2665, -2), (key2780, -2), (key2824, 2), (key2610, 2), (key2803, 2)]

theorem rawRowCheck3129 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form4 = rawRow3129 := by decide +kernel

def row3129 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

theorem rowCheck3129 : row3129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3129 := by decide +kernel

theorem rowEval3129 (x : Key → ℝ) : Integer.Sparse.eval row3129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3129, Integer.Sparse.eval_collectBalanced, rawRowCheck3129]

def rawRow3130 : Integer.Sparse Key := [(key2803, -6), (key2855, 2), (key2853, 2), (key2700, 2), (key2780, 6), (key2865, -2), (key2853, -2), (key2626, -2), (key2789, -2), (key2780, -2), (key2665, -2), (key2824, 2), (key2803, 2), (key2610, 2)]

theorem rawRowCheck3130 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form4 = rawRow3130 := by decide +kernel

def row3130 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

theorem rowCheck3130 : row3130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3130 := by decide +kernel

theorem rowEval3130 (x : Key → ℝ) : Integer.Sparse.eval row3130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3130, Integer.Sparse.eval_collectBalanced, rawRowCheck3130]

def rawRow3131 : Integer.Sparse Key := [(key2855, -6), (key2700, 2), (key2803, 2), (key2853, 2), (key2865, 6), (key2626, -2), (key2780, -2), (key2853, -2), (key2721, -2), (key2824, -2), (key2865, -2), (key2635, 2), (key2789, 2), (key2855, 2)]

theorem rawRowCheck3131 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form4 = rawRow3131 := by decide +kernel

def row3131 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

theorem rowCheck3131 : row3131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3131 := by decide +kernel

theorem rowEval3131 (x : Key → ℝ) : Integer.Sparse.eval row3131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3131, Integer.Sparse.eval_collectBalanced, rawRowCheck3131]

def rawRow3132 : Integer.Sparse Key := [(key2855, -6), (key2700, 2), (key2853, 2), (key2803, 2), (key2865, 6), (key2626, -2), (key2853, -2), (key2780, -2), (key2721, -2), (key2865, -2), (key2824, -2), (key2635, 2), (key2855, 2), (key2789, 2)]

theorem rawRowCheck3132 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form4 = rawRow3132 := by decide +kernel

def row3132 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

theorem rowCheck3132 : row3132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3132 := by decide +kernel

theorem rowEval3132 (x : Key → ℝ) : Integer.Sparse.eval row3132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3132, Integer.Sparse.eval_collectBalanced, rawRowCheck3132]

def rawRow3133 : Integer.Sparse Key := [(key2855, -6), (key2803, 2), (key2700, 2), (key2853, 2), (key2865, 6), (key2780, -2), (key2626, -2), (key2853, -2), (key2824, -2), (key2721, -2), (key2865, -2), (key2789, 2), (key2635, 2), (key2855, 2)]

theorem rawRowCheck3133 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form4 = rawRow3133 := by decide +kernel

def row3133 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

theorem rowCheck3133 : row3133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3133 := by decide +kernel

theorem rowEval3133 (x : Key → ℝ) : Integer.Sparse.eval row3133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3133, Integer.Sparse.eval_collectBalanced, rawRowCheck3133]

def rawRow3134 : Integer.Sparse Key := [(key2855, -6), (key2803, 2), (key2853, 2), (key2700, 2), (key2865, 6), (key2780, -2), (key2853, -2), (key2626, -2), (key2824, -2), (key2865, -2), (key2721, -2), (key2789, 2), (key2855, 2), (key2635, 2)]

theorem rawRowCheck3134 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form4 = rawRow3134 := by decide +kernel

def row3134 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

theorem rowCheck3134 : row3134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3134 := by decide +kernel

theorem rowEval3134 (x : Key → ℝ) : Integer.Sparse.eval row3134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3134, Integer.Sparse.eval_collectBalanced, rawRowCheck3134]

def rawRow3135 : Integer.Sparse Key := [(key2855, -6), (key2853, 2), (key2700, 2), (key2803, 2), (key2865, 6), (key2853, -2), (key2626, -2), (key2780, -2), (key2865, -2), (key2721, -2), (key2824, -2), (key2855, 2), (key2635, 2), (key2789, 2)]

theorem rawRowCheck3135 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form4 = rawRow3135 := by decide +kernel

def row3135 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

theorem rowCheck3135 : row3135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3135 := by decide +kernel

theorem rowEval3135 (x : Key → ℝ) : Integer.Sparse.eval row3135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3135, Integer.Sparse.eval_collectBalanced, rawRowCheck3135]

def rawRow3136 : Integer.Sparse Key := [(key2855, -6), (key2853, 2), (key2803, 2), (key2700, 2), (key2865, 6), (key2853, -2), (key2780, -2), (key2626, -2), (key2865, -2), (key2824, -2), (key2721, -2), (key2855, 2), (key2789, 2), (key2635, 2)]

theorem rawRowCheck3136 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form4 = rawRow3136 := by decide +kernel

def row3136 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

theorem rowCheck3136 : row3136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3136 := by decide +kernel

theorem rowEval3136 (x : Key → ℝ) : Integer.Sparse.eval row3136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3136, Integer.Sparse.eval_collectBalanced, rawRowCheck3136]

def rawRow3137 : Integer.Sparse Key := [(key2824, -6), (key2721, 2), (key2865, 2), (key2865, 2), (key2789, 6), (key2635, -2), (key2855, -2), (key2855, -2), (key2665, -2), (key2780, -2), (key2780, -2), (key2610, 2), (key2803, 2), (key2803, 2)]

theorem rawRowCheck3137 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form4 = rawRow3137 := by decide +kernel

def row3137 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, -2), (key2721, 2), (key2780, -4), (key2789, 6), (key2803, 4), (key2824, -6), (key2855, -4), (key2865, 4)]

theorem rowCheck3137 : row3137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3137 := by decide +kernel

theorem rowEval3137 (x : Key → ℝ) : Integer.Sparse.eval row3137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3137, Integer.Sparse.eval_collectBalanced, rawRowCheck3137]

def rawRow3138 : Integer.Sparse Key := [(key2824, -6), (key2865, 2), (key2721, 2), (key2865, 2), (key2789, 6), (key2855, -2), (key2635, -2), (key2855, -2), (key2780, -2), (key2665, -2), (key2780, -2), (key2803, 2), (key2610, 2), (key2803, 2)]

theorem rawRowCheck3138 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form4 = rawRow3138 := by decide +kernel

def row3138 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, -2), (key2721, 2), (key2780, -4), (key2789, 6), (key2803, 4), (key2824, -6), (key2855, -4), (key2865, 4)]

theorem rowCheck3138 : row3138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3138 := by decide +kernel

theorem rowEval3138 (x : Key → ℝ) : Integer.Sparse.eval row3138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3138, Integer.Sparse.eval_collectBalanced, rawRowCheck3138]

def rawRow3139 : Integer.Sparse Key := [(key2824, -6), (key2865, 2), (key2865, 2), (key2721, 2), (key2789, 6), (key2855, -2), (key2855, -2), (key2635, -2), (key2780, -2), (key2780, -2), (key2665, -2), (key2803, 2), (key2803, 2), (key2610, 2)]

theorem rawRowCheck3139 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form4 = rawRow3139 := by decide +kernel

def row3139 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, -2), (key2721, 2), (key2780, -4), (key2789, 6), (key2803, 4), (key2824, -6), (key2855, -4), (key2865, 4)]

theorem rowCheck3139 : row3139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3139 := by decide +kernel

theorem rowEval3139 (x : Key → ℝ) : Integer.Sparse.eval row3139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3139, Integer.Sparse.eval_collectBalanced, rawRowCheck3139]

def rawRow3140 : Integer.Sparse Key := [(key2865, -6), (key2721, 2), (key2824, 2), (key2865, 2), (key2855, 6), (key2635, -2), (key2789, -2), (key2855, -2), (key2700, -2), (key2803, -2), (key2853, -2), (key2626, 2), (key2780, 2), (key2853, 2)]

theorem rawRowCheck3140 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form4 = rawRow3140 := by decide +kernel

def row3140 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

theorem rowCheck3140 : row3140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3140 := by decide +kernel

theorem rowEval3140 (x : Key → ℝ) : Integer.Sparse.eval row3140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3140, Integer.Sparse.eval_collectBalanced, rawRowCheck3140]

def rawRow3141 : Integer.Sparse Key := [(key2865, -6), (key2721, 2), (key2865, 2), (key2824, 2), (key2855, 6), (key2635, -2), (key2855, -2), (key2789, -2), (key2700, -2), (key2853, -2), (key2803, -2), (key2626, 2), (key2853, 2), (key2780, 2)]

theorem rawRowCheck3141 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form4 = rawRow3141 := by decide +kernel

def row3141 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

theorem rowCheck3141 : row3141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3141 := by decide +kernel

theorem rowEval3141 (x : Key → ℝ) : Integer.Sparse.eval row3141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3141, Integer.Sparse.eval_collectBalanced, rawRowCheck3141]

def rawRow3142 : Integer.Sparse Key := [(key2865, -6), (key2824, 2), (key2721, 2), (key2865, 2), (key2855, 6), (key2789, -2), (key2635, -2), (key2855, -2), (key2803, -2), (key2700, -2), (key2853, -2), (key2780, 2), (key2626, 2), (key2853, 2)]

theorem rawRowCheck3142 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form4 = rawRow3142 := by decide +kernel

def row3142 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

theorem rowCheck3142 : row3142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3142 := by decide +kernel

theorem rowEval3142 (x : Key → ℝ) : Integer.Sparse.eval row3142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3142, Integer.Sparse.eval_collectBalanced, rawRowCheck3142]

def rawRow3143 : Integer.Sparse Key := [(key2865, -6), (key2824, 2), (key2865, 2), (key2721, 2), (key2855, 6), (key2789, -2), (key2855, -2), (key2635, -2), (key2803, -2), (key2853, -2), (key2700, -2), (key2780, 2), (key2853, 2), (key2626, 2)]

theorem rawRowCheck3143 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form4 = rawRow3143 := by decide +kernel

def row3143 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

theorem rowCheck3143 : row3143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3143 := by decide +kernel

theorem rowEval3143 (x : Key → ℝ) : Integer.Sparse.eval row3143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3143, Integer.Sparse.eval_collectBalanced, rawRowCheck3143]

def rawRow3144 : Integer.Sparse Key := [(key2865, -6), (key2865, 2), (key2721, 2), (key2824, 2), (key2855, 6), (key2855, -2), (key2635, -2), (key2789, -2), (key2853, -2), (key2700, -2), (key2803, -2), (key2853, 2), (key2626, 2), (key2780, 2)]

theorem rawRowCheck3144 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form4 = rawRow3144 := by decide +kernel

def row3144 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

theorem rowCheck3144 : row3144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3144 := by decide +kernel

theorem rowEval3144 (x : Key → ℝ) : Integer.Sparse.eval row3144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3144, Integer.Sparse.eval_collectBalanced, rawRowCheck3144]

def rawRow3145 : Integer.Sparse Key := [(key2865, -6), (key2865, 2), (key2824, 2), (key2721, 2), (key2855, 6), (key2855, -2), (key2789, -2), (key2635, -2), (key2853, -2), (key2803, -2), (key2700, -2), (key2853, 2), (key2780, 2), (key2626, 2)]

theorem rawRowCheck3145 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form4 = rawRow3145 := by decide +kernel

def row3145 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

theorem rowCheck3145 : row3145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3145 := by decide +kernel

theorem rowEval3145 (x : Key → ℝ) : Integer.Sparse.eval row3145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3145, Integer.Sparse.eval_collectBalanced, rawRowCheck3145]

def rawRow3146 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1568, -1), (key1904, -1), (key1594, -1), (key1912, -1), (key1299, 2), (key1576, 2), (key1904, 2), (key1311, 1), (key1319, 1), (key1617, 1), (key1919, 1), (key1634, 1), (key1927, 1), (key1319, -1), (key1352, -1), (key1549, -1), (key1897, -1), (key1682, -1), (key1919, -1), (key1327, -2), (key1625, -2), (key1921, -2), (key1327, 1), (key1355, 1), (key1557, 1), (key1900, 1), (key1684, 1), (key1921, 1)]

theorem rawRowCheck3146 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form5 = rawRow3146 := by decide +kernel

def row3146 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck3146 : row3146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3146 := by decide +kernel

theorem rowEval3146 (x : Key → ℝ) : Integer.Sparse.eval row3146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3146, Integer.Sparse.eval_collectBalanced, rawRowCheck3146]

def rawRow3147 : Integer.Sparse Key := [(key1299, -1), (key1291, -1), (key1904, -1), (key1568, -1), (key1912, -1), (key1594, -1), (key1299, 2), (key1904, 2), (key1576, 2), (key1319, 1), (key1311, 1), (key1919, 1), (key1617, 1), (key1927, 1), (key1634, 1), (key1352, -1), (key1319, -1), (key1897, -1), (key1549, -1), (key1919, -1), (key1682, -1), (key1327, -2), (key1921, -2), (key1625, -2), (key1355, 1), (key1327, 1), (key1900, 1), (key1557, 1), (key1921, 1), (key1684, 1)]

theorem rawRowCheck3147 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form5 = rawRow3147 := by decide +kernel

def row3147 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck3147 : row3147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3147 := by decide +kernel

theorem rowEval3147 (x : Key → ℝ) : Integer.Sparse.eval row3147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3147, Integer.Sparse.eval_collectBalanced, rawRowCheck3147]

def rawRow3148 : Integer.Sparse Key := [(key1568, -1), (key1594, -1), (key1291, -1), (key1912, -1), (key1299, -1), (key1904, -1), (key1576, 2), (key1299, 2), (key1904, 2), (key1617, 1), (key1634, 1), (key1311, 1), (key1927, 1), (key1319, 1), (key1919, 1), (key1549, -1), (key1682, -1), (key1319, -1), (key1919, -1), (key1352, -1), (key1897, -1), (key1625, -2), (key1327, -2), (key1921, -2), (key1557, 1), (key1684, 1), (key1327, 1), (key1921, 1), (key1355, 1), (key1900, 1)]

theorem rawRowCheck3148 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form5 = rawRow3148 := by decide +kernel

def row3148 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck3148 : row3148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3148 := by decide +kernel

theorem rowEval3148 (x : Key → ℝ) : Integer.Sparse.eval row3148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3148, Integer.Sparse.eval_collectBalanced, rawRowCheck3148]

def rawRow3149 : Integer.Sparse Key := [(key1594, -1), (key1568, -1), (key1912, -1), (key1291, -1), (key1904, -1), (key1299, -1), (key1576, 2), (key1904, 2), (key1299, 2), (key1634, 1), (key1617, 1), (key1927, 1), (key1311, 1), (key1919, 1), (key1319, 1), (key1682, -1), (key1549, -1), (key1919, -1), (key1319, -1), (key1897, -1), (key1352, -1), (key1625, -2), (key1921, -2), (key1327, -2), (key1684, 1), (key1557, 1), (key1921, 1), (key1327, 1), (key1900, 1), (key1355, 1)]

theorem rawRowCheck3149 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form5 = rawRow3149 := by decide +kernel

def row3149 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck3149 : row3149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3149 := by decide +kernel

theorem rowEval3149 (x : Key → ℝ) : Integer.Sparse.eval row3149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3149, Integer.Sparse.eval_collectBalanced, rawRowCheck3149]

def rawRow3150 : Integer.Sparse Key := [(key1904, -1), (key1912, -1), (key1299, -1), (key1594, -1), (key1291, -1), (key1568, -1), (key1904, 2), (key1299, 2), (key1576, 2), (key1919, 1), (key1927, 1), (key1319, 1), (key1634, 1), (key1311, 1), (key1617, 1), (key1897, -1), (key1919, -1), (key1352, -1), (key1682, -1), (key1319, -1), (key1549, -1), (key1921, -2), (key1327, -2), (key1625, -2), (key1900, 1), (key1921, 1), (key1355, 1), (key1684, 1), (key1327, 1), (key1557, 1)]

theorem rawRowCheck3150 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form5 = rawRow3150 := by decide +kernel

def row3150 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck3150 : row3150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3150 := by decide +kernel

theorem rowEval3150 (x : Key → ℝ) : Integer.Sparse.eval row3150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3150, Integer.Sparse.eval_collectBalanced, rawRowCheck3150]

def rawRow3151 : Integer.Sparse Key := [(key1912, -1), (key1904, -1), (key1594, -1), (key1299, -1), (key1568, -1), (key1291, -1), (key1904, 2), (key1576, 2), (key1299, 2), (key1927, 1), (key1919, 1), (key1634, 1), (key1319, 1), (key1617, 1), (key1311, 1), (key1919, -1), (key1897, -1), (key1682, -1), (key1352, -1), (key1549, -1), (key1319, -1), (key1921, -2), (key1625, -2), (key1327, -2), (key1921, 1), (key1900, 1), (key1684, 1), (key1355, 1), (key1557, 1), (key1327, 1)]

theorem rawRowCheck3151 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form5 = rawRow3151 := by decide +kernel

def row3151 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck3151 : row3151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3151 := by decide +kernel

theorem rowEval3151 (x : Key → ℝ) : Integer.Sparse.eval row3151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3151, Integer.Sparse.eval_collectBalanced, rawRowCheck3151]

def rawRow3152 : Integer.Sparse Key := [(key1299, -1), (key1299, -1), (key1576, -1), (key1576, -1), (key1594, -1), (key1594, -1), (key1291, 2), (key1568, 2), (key1568, 2), (key1352, 1), (key1352, 1), (key1682, 1), (key1682, 1), (key1690, 1), (key1690, 1), (key1311, -1), (key1311, -1), (key1541, -1), (key1541, -1), (key1617, -1), (key1617, -1), (key1355, -2), (key1684, -2), (key1684, -2), (key1327, 1), (key1327, 1), (key1557, 1), (key1557, 1), (key1625, 1), (key1625, 1)]

theorem rawRowCheck3152 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form5 = rawRow3152 := by decide +kernel

def row3152 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1541, -2), (key1557, 2), (key1568, 4), (key1576, -2), (key1594, -2), (key1617, -2), (key1625, 2), (key1682, 2), (key1684, -4), (key1690, 2)]

theorem rowCheck3152 : row3152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3152 := by decide +kernel

theorem rowEval3152 (x : Key → ℝ) : Integer.Sparse.eval row3152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3152, Integer.Sparse.eval_collectBalanced, rawRowCheck3152]

def rawRow3153 : Integer.Sparse Key := [(key1576, -1), (key1594, -1), (key1299, -1), (key1594, -1), (key1299, -1), (key1576, -1), (key1568, 2), (key1291, 2), (key1568, 2), (key1682, 1), (key1690, 1), (key1352, 1), (key1690, 1), (key1352, 1), (key1682, 1), (key1541, -1), (key1617, -1), (key1311, -1), (key1617, -1), (key1311, -1), (key1541, -1), (key1684, -2), (key1355, -2), (key1684, -2), (key1557, 1), (key1625, 1), (key1327, 1), (key1625, 1), (key1327, 1), (key1557, 1)]

theorem rawRowCheck3153 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form5 = rawRow3153 := by decide +kernel

def row3153 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1541, -2), (key1557, 2), (key1568, 4), (key1576, -2), (key1594, -2), (key1617, -2), (key1625, 2), (key1682, 2), (key1684, -4), (key1690, 2)]

theorem rowCheck3153 : row3153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3153 := by decide +kernel

theorem rowEval3153 (x : Key → ℝ) : Integer.Sparse.eval row3153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3153, Integer.Sparse.eval_collectBalanced, rawRowCheck3153]

def rawRow3154 : Integer.Sparse Key := [(key1594, -1), (key1576, -1), (key1594, -1), (key1299, -1), (key1576, -1), (key1299, -1), (key1568, 2), (key1568, 2), (key1291, 2), (key1690, 1), (key1682, 1), (key1690, 1), (key1352, 1), (key1682, 1), (key1352, 1), (key1617, -1), (key1541, -1), (key1617, -1), (key1311, -1), (key1541, -1), (key1311, -1), (key1684, -2), (key1684, -2), (key1355, -2), (key1625, 1), (key1557, 1), (key1625, 1), (key1327, 1), (key1557, 1), (key1327, 1)]

theorem rawRowCheck3154 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form5 = rawRow3154 := by decide +kernel

def row3154 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1541, -2), (key1557, 2), (key1568, 4), (key1576, -2), (key1594, -2), (key1617, -2), (key1625, 2), (key1682, 2), (key1684, -4), (key1690, 2)]

theorem rowCheck3154 : row3154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3154 := by decide +kernel

theorem rowEval3154 (x : Key → ℝ) : Integer.Sparse.eval row3154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3154, Integer.Sparse.eval_collectBalanced, rawRowCheck3154]

def rawRow3155 : Integer.Sparse Key := [(key1311, -1), (key1319, -1), (key1617, -1), (key1919, -1), (key1634, -1), (key1927, -1), (key1327, 2), (key1625, 2), (key1921, 2), (key1291, 1), (key1299, 1), (key1568, 1), (key1904, 1), (key1594, 1), (key1912, 1), (key1327, -1), (key1355, -1), (key1557, -1), (key1900, -1), (key1684, -1), (key1921, -1), (key1299, -2), (key1576, -2), (key1904, -2), (key1319, 1), (key1352, 1), (key1549, 1), (key1897, 1), (key1682, 1), (key1919, 1)]

theorem rawRowCheck3155 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form5 = rawRow3155 := by decide +kernel

def row3155 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck3155 : row3155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3155 := by decide +kernel

theorem rowEval3155 (x : Key → ℝ) : Integer.Sparse.eval row3155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3155, Integer.Sparse.eval_collectBalanced, rawRowCheck3155]

def rawRow3156 : Integer.Sparse Key := [(key1319, -1), (key1311, -1), (key1919, -1), (key1617, -1), (key1927, -1), (key1634, -1), (key1327, 2), (key1921, 2), (key1625, 2), (key1299, 1), (key1291, 1), (key1904, 1), (key1568, 1), (key1912, 1), (key1594, 1), (key1355, -1), (key1327, -1), (key1900, -1), (key1557, -1), (key1921, -1), (key1684, -1), (key1299, -2), (key1904, -2), (key1576, -2), (key1352, 1), (key1319, 1), (key1897, 1), (key1549, 1), (key1919, 1), (key1682, 1)]

theorem rawRowCheck3156 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form5 = rawRow3156 := by decide +kernel

def row3156 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck3156 : row3156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3156 := by decide +kernel

theorem rowEval3156 (x : Key → ℝ) : Integer.Sparse.eval row3156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3156, Integer.Sparse.eval_collectBalanced, rawRowCheck3156]

def rawRow3157 : Integer.Sparse Key := [(key1617, -1), (key1634, -1), (key1311, -1), (key1927, -1), (key1319, -1), (key1919, -1), (key1625, 2), (key1327, 2), (key1921, 2), (key1568, 1), (key1594, 1), (key1291, 1), (key1912, 1), (key1299, 1), (key1904, 1), (key1557, -1), (key1684, -1), (key1327, -1), (key1921, -1), (key1355, -1), (key1900, -1), (key1576, -2), (key1299, -2), (key1904, -2), (key1549, 1), (key1682, 1), (key1319, 1), (key1919, 1), (key1352, 1), (key1897, 1)]

theorem rawRowCheck3157 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form5 = rawRow3157 := by decide +kernel

def row3157 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck3157 : row3157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3157 := by decide +kernel

theorem rowEval3157 (x : Key → ℝ) : Integer.Sparse.eval row3157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3157, Integer.Sparse.eval_collectBalanced, rawRowCheck3157]

def rawRow3158 : Integer.Sparse Key := [(key1634, -1), (key1617, -1), (key1927, -1), (key1311, -1), (key1919, -1), (key1319, -1), (key1625, 2), (key1921, 2), (key1327, 2), (key1594, 1), (key1568, 1), (key1912, 1), (key1291, 1), (key1904, 1), (key1299, 1), (key1684, -1), (key1557, -1), (key1921, -1), (key1327, -1), (key1900, -1), (key1355, -1), (key1576, -2), (key1904, -2), (key1299, -2), (key1682, 1), (key1549, 1), (key1919, 1), (key1319, 1), (key1897, 1), (key1352, 1)]

theorem rawRowCheck3158 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form5 = rawRow3158 := by decide +kernel

def row3158 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck3158 : row3158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3158 := by decide +kernel

theorem rowEval3158 (x : Key → ℝ) : Integer.Sparse.eval row3158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3158, Integer.Sparse.eval_collectBalanced, rawRowCheck3158]

def rawRow3159 : Integer.Sparse Key := [(key1919, -1), (key1927, -1), (key1319, -1), (key1634, -1), (key1311, -1), (key1617, -1), (key1921, 2), (key1327, 2), (key1625, 2), (key1904, 1), (key1912, 1), (key1299, 1), (key1594, 1), (key1291, 1), (key1568, 1), (key1900, -1), (key1921, -1), (key1355, -1), (key1684, -1), (key1327, -1), (key1557, -1), (key1904, -2), (key1299, -2), (key1576, -2), (key1897, 1), (key1919, 1), (key1352, 1), (key1682, 1), (key1319, 1), (key1549, 1)]

theorem rawRowCheck3159 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form5 = rawRow3159 := by decide +kernel

def row3159 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck3159 : row3159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3159 := by decide +kernel

theorem rowEval3159 (x : Key → ℝ) : Integer.Sparse.eval row3159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3159, Integer.Sparse.eval_collectBalanced, rawRowCheck3159]

def rawRow3160 : Integer.Sparse Key := [(key1927, -1), (key1919, -1), (key1634, -1), (key1319, -1), (key1617, -1), (key1311, -1), (key1921, 2), (key1625, 2), (key1327, 2), (key1912, 1), (key1904, 1), (key1594, 1), (key1299, 1), (key1568, 1), (key1291, 1), (key1921, -1), (key1900, -1), (key1684, -1), (key1355, -1), (key1557, -1), (key1327, -1), (key1904, -2), (key1576, -2), (key1299, -2), (key1919, 1), (key1897, 1), (key1682, 1), (key1352, 1), (key1549, 1), (key1319, 1)]

theorem rawRowCheck3160 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form5 = rawRow3160 := by decide +kernel

def row3160 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck3160 : row3160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3160 := by decide +kernel

theorem rowEval3160 (x : Key → ℝ) : Integer.Sparse.eval row3160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3160, Integer.Sparse.eval_collectBalanced, rawRowCheck3160]

def rawRow3161 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1427, -1), (key1625, -1), (key1445, -1), (key1634, -1), (key1311, 2), (key1419, 2), (key1617, 2), (key1352, 1), (key1355, 1), (key1473, 1), (key1684, 1), (key1481, 1), (key1690, 1), (key1291, -1), (key1311, -1), (key1386, -1), (key1541, -1), (key1419, -1), (key1568, -1), (key1352, -2), (key1473, -2), (key1682, -2), (key1299, 1), (key1319, 1), (key1394, 1), (key1549, 1), (key1427, 1), (key1576, 1)]

theorem rawRowCheck3161 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form5 = rawRow3161 := by decide +kernel

def row3161 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

theorem rowCheck3161 : row3161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3161 := by decide +kernel

theorem rowEval3161 (x : Key → ℝ) : Integer.Sparse.eval row3161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3161, Integer.Sparse.eval_collectBalanced, rawRowCheck3161]

def rawRow3162 : Integer.Sparse Key := [(key1327, -1), (key1319, -1), (key1625, -1), (key1427, -1), (key1634, -1), (key1445, -1), (key1311, 2), (key1617, 2), (key1419, 2), (key1355, 1), (key1352, 1), (key1684, 1), (key1473, 1), (key1690, 1), (key1481, 1), (key1311, -1), (key1291, -1), (key1541, -1), (key1386, -1), (key1568, -1), (key1419, -1), (key1352, -2), (key1682, -2), (key1473, -2), (key1319, 1), (key1299, 1), (key1549, 1), (key1394, 1), (key1576, 1), (key1427, 1)]

theorem rawRowCheck3162 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form5 = rawRow3162 := by decide +kernel

def row3162 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

theorem rowCheck3162 : row3162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3162 := by decide +kernel

theorem rowEval3162 (x : Key → ℝ) : Integer.Sparse.eval row3162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3162, Integer.Sparse.eval_collectBalanced, rawRowCheck3162]

def rawRow3163 : Integer.Sparse Key := [(key1427, -1), (key1445, -1), (key1319, -1), (key1634, -1), (key1327, -1), (key1625, -1), (key1419, 2), (key1311, 2), (key1617, 2), (key1473, 1), (key1481, 1), (key1352, 1), (key1690, 1), (key1355, 1), (key1684, 1), (key1386, -1), (key1419, -1), (key1291, -1), (key1568, -1), (key1311, -1), (key1541, -1), (key1473, -2), (key1352, -2), (key1682, -2), (key1394, 1), (key1427, 1), (key1299, 1), (key1576, 1), (key1319, 1), (key1549, 1)]

theorem rawRowCheck3163 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form5 = rawRow3163 := by decide +kernel

def row3163 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

theorem rowCheck3163 : row3163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3163 := by decide +kernel

theorem rowEval3163 (x : Key → ℝ) : Integer.Sparse.eval row3163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3163, Integer.Sparse.eval_collectBalanced, rawRowCheck3163]

def rawRow3164 : Integer.Sparse Key := [(key1445, -1), (key1427, -1), (key1634, -1), (key1319, -1), (key1625, -1), (key1327, -1), (key1419, 2), (key1617, 2), (key1311, 2), (key1481, 1), (key1473, 1), (key1690, 1), (key1352, 1), (key1684, 1), (key1355, 1), (key1419, -1), (key1386, -1), (key1568, -1), (key1291, -1), (key1541, -1), (key1311, -1), (key1473, -2), (key1682, -2), (key1352, -2), (key1427, 1), (key1394, 1), (key1576, 1), (key1299, 1), (key1549, 1), (key1319, 1)]

theorem rawRowCheck3164 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form5 = rawRow3164 := by decide +kernel

def row3164 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

theorem rowCheck3164 : row3164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3164 := by decide +kernel

theorem rowEval3164 (x : Key → ℝ) : Integer.Sparse.eval row3164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3164, Integer.Sparse.eval_collectBalanced, rawRowCheck3164]

def rawRow3165 : Integer.Sparse Key := [(key1625, -1), (key1634, -1), (key1327, -1), (key1445, -1), (key1319, -1), (key1427, -1), (key1617, 2), (key1311, 2), (key1419, 2), (key1684, 1), (key1690, 1), (key1355, 1), (key1481, 1), (key1352, 1), (key1473, 1), (key1541, -1), (key1568, -1), (key1311, -1), (key1419, -1), (key1291, -1), (key1386, -1), (key1682, -2), (key1352, -2), (key1473, -2), (key1549, 1), (key1576, 1), (key1319, 1), (key1427, 1), (key1299, 1), (key1394, 1)]

theorem rawRowCheck3165 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form5 = rawRow3165 := by decide +kernel

def row3165 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

theorem rowCheck3165 : row3165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3165 := by decide +kernel

theorem rowEval3165 (x : Key → ℝ) : Integer.Sparse.eval row3165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3165, Integer.Sparse.eval_collectBalanced, rawRowCheck3165]

def rawRow3166 : Integer.Sparse Key := [(key1634, -1), (key1625, -1), (key1445, -1), (key1327, -1), (key1427, -1), (key1319, -1), (key1617, 2), (key1419, 2), (key1311, 2), (key1690, 1), (key1684, 1), (key1481, 1), (key1355, 1), (key1473, 1), (key1352, 1), (key1568, -1), (key1541, -1), (key1419, -1), (key1311, -1), (key1386, -1), (key1291, -1), (key1682, -2), (key1473, -2), (key1352, -2), (key1576, 1), (key1549, 1), (key1427, 1), (key1319, 1), (key1394, 1), (key1299, 1)]

theorem rawRowCheck3166 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form5 = rawRow3166 := by decide +kernel

def row3166 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

theorem rowCheck3166 : row3166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3166 := by decide +kernel

theorem rowEval3166 (x : Key → ℝ) : Integer.Sparse.eval row3166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3166, Integer.Sparse.eval_collectBalanced, rawRowCheck3166]

def rawRow3167 : Integer.Sparse Key := [(key1352, -1), (key1352, -1), (key1682, -1), (key1682, -1), (key1690, -1), (key1690, -1), (key1355, 2), (key1684, 2), (key1684, 2), (key1299, 1), (key1299, 1), (key1576, 1), (key1576, 1), (key1594, 1), (key1594, 1), (key1327, -1), (key1327, -1), (key1557, -1), (key1557, -1), (key1625, -1), (key1625, -1), (key1291, -2), (key1568, -2), (key1568, -2), (key1311, 1), (key1311, 1), (key1541, 1), (key1541, 1), (key1617, 1), (key1617, 1)]

theorem rawRowCheck3167 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form5 = rawRow3167 := by decide +kernel

def row3167 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1327, -2), (key1352, -2), (key1355, 2), (key1541, 2), (key1557, -2), (key1568, -4), (key1576, 2), (key1594, 2), (key1617, 2), (key1625, -2), (key1682, -2), (key1684, 4), (key1690, -2)]

theorem rowCheck3167 : row3167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3167 := by decide +kernel

theorem rowEval3167 (x : Key → ℝ) : Integer.Sparse.eval row3167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3167, Integer.Sparse.eval_collectBalanced, rawRowCheck3167]

def rawRow3168 : Integer.Sparse Key := [(key1682, -1), (key1690, -1), (key1352, -1), (key1690, -1), (key1352, -1), (key1682, -1), (key1684, 2), (key1355, 2), (key1684, 2), (key1576, 1), (key1594, 1), (key1299, 1), (key1594, 1), (key1299, 1), (key1576, 1), (key1557, -1), (key1625, -1), (key1327, -1), (key1625, -1), (key1327, -1), (key1557, -1), (key1568, -2), (key1291, -2), (key1568, -2), (key1541, 1), (key1617, 1), (key1311, 1), (key1617, 1), (key1311, 1), (key1541, 1)]

theorem rawRowCheck3168 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form5 = rawRow3168 := by decide +kernel

def row3168 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1327, -2), (key1352, -2), (key1355, 2), (key1541, 2), (key1557, -2), (key1568, -4), (key1576, 2), (key1594, 2), (key1617, 2), (key1625, -2), (key1682, -2), (key1684, 4), (key1690, -2)]

theorem rowCheck3168 : row3168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3168 := by decide +kernel

theorem rowEval3168 (x : Key → ℝ) : Integer.Sparse.eval row3168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3168, Integer.Sparse.eval_collectBalanced, rawRowCheck3168]

def rawRow3169 : Integer.Sparse Key := [(key1690, -1), (key1682, -1), (key1690, -1), (key1352, -1), (key1682, -1), (key1352, -1), (key1684, 2), (key1684, 2), (key1355, 2), (key1594, 1), (key1576, 1), (key1594, 1), (key1299, 1), (key1576, 1), (key1299, 1), (key1625, -1), (key1557, -1), (key1625, -1), (key1327, -1), (key1557, -1), (key1327, -1), (key1568, -2), (key1568, -2), (key1291, -2), (key1617, 1), (key1541, 1), (key1617, 1), (key1311, 1), (key1541, 1), (key1311, 1)]

theorem rawRowCheck3169 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form5 = rawRow3169 := by decide +kernel

def row3169 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1327, -2), (key1352, -2), (key1355, 2), (key1541, 2), (key1557, -2), (key1568, -4), (key1576, 2), (key1594, 2), (key1617, 2), (key1625, -2), (key1682, -2), (key1684, 4), (key1690, -2)]

theorem rowCheck3169 : row3169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3169 := by decide +kernel

theorem rowEval3169 (x : Key → ℝ) : Integer.Sparse.eval row3169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3169, Integer.Sparse.eval_collectBalanced, rawRowCheck3169]

def rawRow3170 : Integer.Sparse Key := [(key1352, -1), (key1355, -1), (key1473, -1), (key1684, -1), (key1481, -1), (key1690, -1), (key1352, 2), (key1473, 2), (key1682, 2), (key1319, 1), (key1327, 1), (key1427, 1), (key1625, 1), (key1445, 1), (key1634, 1), (key1299, -1), (key1319, -1), (key1394, -1), (key1549, -1), (key1427, -1), (key1576, -1), (key1311, -2), (key1419, -2), (key1617, -2), (key1291, 1), (key1311, 1), (key1386, 1), (key1541, 1), (key1419, 1), (key1568, 1)]

theorem rawRowCheck3170 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form5 = rawRow3170 := by decide +kernel

def row3170 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

theorem rowCheck3170 : row3170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3170 := by decide +kernel

theorem rowEval3170 (x : Key → ℝ) : Integer.Sparse.eval row3170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3170, Integer.Sparse.eval_collectBalanced, rawRowCheck3170]

def rawRow3171 : Integer.Sparse Key := [(key1355, -1), (key1352, -1), (key1684, -1), (key1473, -1), (key1690, -1), (key1481, -1), (key1352, 2), (key1682, 2), (key1473, 2), (key1327, 1), (key1319, 1), (key1625, 1), (key1427, 1), (key1634, 1), (key1445, 1), (key1319, -1), (key1299, -1), (key1549, -1), (key1394, -1), (key1576, -1), (key1427, -1), (key1311, -2), (key1617, -2), (key1419, -2), (key1311, 1), (key1291, 1), (key1541, 1), (key1386, 1), (key1568, 1), (key1419, 1)]

theorem rawRowCheck3171 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form5 = rawRow3171 := by decide +kernel

def row3171 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

theorem rowCheck3171 : row3171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3171 := by decide +kernel

theorem rowEval3171 (x : Key → ℝ) : Integer.Sparse.eval row3171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3171, Integer.Sparse.eval_collectBalanced, rawRowCheck3171]

def rawRow3172 : Integer.Sparse Key := [(key1473, -1), (key1481, -1), (key1352, -1), (key1690, -1), (key1355, -1), (key1684, -1), (key1473, 2), (key1352, 2), (key1682, 2), (key1427, 1), (key1445, 1), (key1319, 1), (key1634, 1), (key1327, 1), (key1625, 1), (key1394, -1), (key1427, -1), (key1299, -1), (key1576, -1), (key1319, -1), (key1549, -1), (key1419, -2), (key1311, -2), (key1617, -2), (key1386, 1), (key1419, 1), (key1291, 1), (key1568, 1), (key1311, 1), (key1541, 1)]

theorem rawRowCheck3172 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form5 = rawRow3172 := by decide +kernel

def row3172 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

theorem rowCheck3172 : row3172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3172 := by decide +kernel

theorem rowEval3172 (x : Key → ℝ) : Integer.Sparse.eval row3172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3172, Integer.Sparse.eval_collectBalanced, rawRowCheck3172]

def rawRow3173 : Integer.Sparse Key := [(key1481, -1), (key1473, -1), (key1690, -1), (key1352, -1), (key1684, -1), (key1355, -1), (key1473, 2), (key1682, 2), (key1352, 2), (key1445, 1), (key1427, 1), (key1634, 1), (key1319, 1), (key1625, 1), (key1327, 1), (key1427, -1), (key1394, -1), (key1576, -1), (key1299, -1), (key1549, -1), (key1319, -1), (key1419, -2), (key1617, -2), (key1311, -2), (key1419, 1), (key1386, 1), (key1568, 1), (key1291, 1), (key1541, 1), (key1311, 1)]

theorem rawRowCheck3173 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form5 = rawRow3173 := by decide +kernel

def row3173 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

theorem rowCheck3173 : row3173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3173 := by decide +kernel

theorem rowEval3173 (x : Key → ℝ) : Integer.Sparse.eval row3173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3173, Integer.Sparse.eval_collectBalanced, rawRowCheck3173]

def rawRow3174 : Integer.Sparse Key := [(key1684, -1), (key1690, -1), (key1355, -1), (key1481, -1), (key1352, -1), (key1473, -1), (key1682, 2), (key1352, 2), (key1473, 2), (key1625, 1), (key1634, 1), (key1327, 1), (key1445, 1), (key1319, 1), (key1427, 1), (key1549, -1), (key1576, -1), (key1319, -1), (key1427, -1), (key1299, -1), (key1394, -1), (key1617, -2), (key1311, -2), (key1419, -2), (key1541, 1), (key1568, 1), (key1311, 1), (key1419, 1), (key1291, 1), (key1386, 1)]

theorem rawRowCheck3174 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form5 = rawRow3174 := by decide +kernel

def row3174 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

theorem rowCheck3174 : row3174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3174 := by decide +kernel

theorem rowEval3174 (x : Key → ℝ) : Integer.Sparse.eval row3174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3174, Integer.Sparse.eval_collectBalanced, rawRowCheck3174]

def rawRow3175 : Integer.Sparse Key := [(key1690, -1), (key1684, -1), (key1481, -1), (key1355, -1), (key1473, -1), (key1352, -1), (key1682, 2), (key1473, 2), (key1352, 2), (key1634, 1), (key1625, 1), (key1445, 1), (key1327, 1), (key1427, 1), (key1319, 1), (key1576, -1), (key1549, -1), (key1427, -1), (key1319, -1), (key1394, -1), (key1299, -1), (key1617, -2), (key1419, -2), (key1311, -2), (key1568, 1), (key1541, 1), (key1419, 1), (key1311, 1), (key1386, 1), (key1291, 1)]

theorem rawRowCheck3175 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form5 = rawRow3175 := by decide +kernel

def row3175 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

theorem rowCheck3175 : row3175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3175 := by decide +kernel

theorem rowEval3175 (x : Key → ℝ) : Integer.Sparse.eval row3175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3175, Integer.Sparse.eval_collectBalanced, rawRowCheck3175]

def rawRow3176 : Integer.Sparse Key := [(key2679, -2), (key2691, -2), (key3014, -2), (key2684, 2), (key2691, 2), (key2820, 2), (key2710, 2), (key2717, 2), (key3024, 2), (key2717, -6), (key2754, -2), (key2755, -2), (key2921, -2), (key2755, 6)]

theorem rawRowCheck3176 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form6 = rawRow3176 := by decide +kernel

def row3176 : Integer.Sparse Key := [(key2679, -2), (key2684, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3014, -2), (key3024, 2)]

theorem rowCheck3176 : row3176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3176 := by decide +kernel

theorem rowEval3176 (x : Key → ℝ) : Integer.Sparse.eval row3176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3176, Integer.Sparse.eval_collectBalanced, rawRowCheck3176]

def rawRow3177 : Integer.Sparse Key := [(key2691, -2), (key2679, -2), (key3014, -2), (key2691, 2), (key2684, 2), (key2820, 2), (key2717, 2), (key2710, 2), (key3024, 2), (key2717, -6), (key2755, -2), (key2754, -2), (key2921, -2), (key2755, 6)]

theorem rawRowCheck3177 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form6 = rawRow3177 := by decide +kernel

def row3177 : Integer.Sparse Key := [(key2679, -2), (key2684, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3014, -2), (key3024, 2)]

theorem rowCheck3177 : row3177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3177 := by decide +kernel

theorem rowEval3177 (x : Key → ℝ) : Integer.Sparse.eval row3177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3177, Integer.Sparse.eval_collectBalanced, rawRowCheck3177]

def rawRow3178 : Integer.Sparse Key := [(key3047, -2), (key3115, -2), (key2691, -2), (key2684, 2), (key2820, 2), (key2691, 2), (key2710, 2), (key3024, 2), (key2717, 2), (key2717, -6), (key2754, -2), (key2921, -2), (key2755, -2), (key2755, 6)]

theorem rawRowCheck3178 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form6 = rawRow3178 := by decide +kernel

def row3178 : Integer.Sparse Key := [(key2684, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3024, 2), (key3047, -2), (key3115, -2)]

theorem rowCheck3178 : row3178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3178 := by decide +kernel

theorem rowEval3178 (x : Key → ℝ) : Integer.Sparse.eval row3178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3178, Integer.Sparse.eval_collectBalanced, rawRowCheck3178]

def rawRow3179 : Integer.Sparse Key := [(key3115, -2), (key3047, -2), (key2691, -2), (key2820, 2), (key2684, 2), (key2691, 2), (key3024, 2), (key2710, 2), (key2717, 2), (key2717, -6), (key2921, -2), (key2754, -2), (key2755, -2), (key2755, 6)]

theorem rawRowCheck3179 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form6 = rawRow3179 := by decide +kernel

def row3179 : Integer.Sparse Key := [(key2684, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3024, 2), (key3047, -2), (key3115, -2)]

theorem rowCheck3179 : row3179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3179 := by decide +kernel

theorem rowEval3179 (x : Key → ℝ) : Integer.Sparse.eval row3179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3179, Integer.Sparse.eval_collectBalanced, rawRowCheck3179]

def rawRow3180 : Integer.Sparse Key := [(key3058, -2), (key3115, -2), (key2679, -2), (key2691, 2), (key2820, 2), (key2684, 2), (key2717, 2), (key3024, 2), (key2710, 2), (key2717, -6), (key2755, -2), (key2921, -2), (key2754, -2), (key2755, 6)]

theorem rawRowCheck3180 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form6 = rawRow3180 := by decide +kernel

def row3180 : Integer.Sparse Key := [(key2679, -2), (key2684, 2), (key2691, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3024, 2), (key3058, -2), (key3115, -2)]

theorem rowCheck3180 : row3180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3180 := by decide +kernel

theorem rowEval3180 (x : Key → ℝ) : Integer.Sparse.eval row3180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3180, Integer.Sparse.eval_collectBalanced, rawRowCheck3180]

def rawRow3181 : Integer.Sparse Key := [(key3115, -2), (key3058, -2), (key3047, -2), (key2820, 2), (key2691, 2), (key2684, 2), (key3024, 2), (key2717, 2), (key2710, 2), (key2717, -6), (key2921, -2), (key2755, -2), (key2754, -2), (key2755, 6)]

theorem rawRowCheck3181 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form6 = rawRow3181 := by decide +kernel

def row3181 : Integer.Sparse Key := [(key2684, 2), (key2691, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3024, 2), (key3047, -2), (key3058, -2), (key3115, -2)]

theorem rowCheck3181 : row3181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3181 := by decide +kernel

theorem rowEval3181 (x : Key → ℝ) : Integer.Sparse.eval row3181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3181, Integer.Sparse.eval_collectBalanced, rawRowCheck3181]

def rawRow3182 : Integer.Sparse Key := [(key3053, -2), (key3053, -2), (key3105, -2), (key2679, 2), (key2679, 2), (key2813, 2), (key2717, 2), (key2717, 2), (key3024, 2), (key2710, -6), (key2755, -2), (key2755, -2), (key2921, -2), (key2754, 6)]

theorem rawRowCheck3182 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form6 = rawRow3182 := by decide +kernel

def row3182 : Integer.Sparse Key := [(key2679, 4), (key2710, -6), (key2717, 4), (key2754, 6), (key2755, -4), (key2813, 2), (key2921, -2), (key3024, 2), (key3053, -4), (key3105, -2)]

theorem rowCheck3182 : row3182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3182 := by decide +kernel

theorem rowEval3182 (x : Key → ℝ) : Integer.Sparse.eval row3182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3182, Integer.Sparse.eval_collectBalanced, rawRowCheck3182]

def rawRow3183 : Integer.Sparse Key := [(key3053, -2), (key3105, -2), (key3053, -2), (key3047, 2), (key3096, 2), (key2679, 2), (key2717, 2), (key3024, 2), (key2717, 2), (key2710, -6), (key2755, -2), (key2921, -2), (key2755, -2), (key2754, 6)]

theorem rawRowCheck3183 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form6 = rawRow3183 := by decide +kernel

def row3183 : Integer.Sparse Key := [(key2679, 2), (key2710, -6), (key2717, 4), (key2754, 6), (key2755, -4), (key2921, -2), (key3024, 2), (key3047, 2), (key3053, -4), (key3096, 2), (key3105, -2)]

theorem rowCheck3183 : row3183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3183 := by decide +kernel

theorem rowEval3183 (x : Key → ℝ) : Integer.Sparse.eval row3183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3183, Integer.Sparse.eval_collectBalanced, rawRowCheck3183]

def rawRow3184 : Integer.Sparse Key := [(key3105, -2), (key3053, -2), (key3053, -2), (key3096, 2), (key3047, 2), (key3047, 2), (key3024, 2), (key2717, 2), (key2717, 2), (key2710, -6), (key2921, -2), (key2755, -2), (key2755, -2), (key2754, 6)]

theorem rawRowCheck3184 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form6 = rawRow3184 := by decide +kernel

def row3184 : Integer.Sparse Key := [(key2710, -6), (key2717, 4), (key2754, 6), (key2755, -4), (key2921, -2), (key3024, 2), (key3047, 4), (key3053, -4), (key3096, 2), (key3105, -2)]

theorem rowCheck3184 : row3184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3184 := by decide +kernel

theorem rowEval3184 (x : Key → ℝ) : Integer.Sparse.eval row3184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3184, Integer.Sparse.eval_collectBalanced, rawRowCheck3184]

def rawRow3185 : Integer.Sparse Key := [(key3061, -2), (key3075, -2), (key3143, -2), (key3068, 2), (key3076, 2), (key3142, 2), (key2679, 2), (key2691, 2), (key3014, 2), (key2755, -6), (key2684, -2), (key2691, -2), (key2820, -2), (key2717, 6)]

theorem rawRowCheck3185 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form6 = rawRow3185 := by decide +kernel

def row3185 : Integer.Sparse Key := [(key2679, 2), (key2684, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3014, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3142, 2), (key3143, -2)]

theorem rowCheck3185 : row3185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3185 := by decide +kernel

theorem rowEval3185 (x : Key → ℝ) : Integer.Sparse.eval row3185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3185, Integer.Sparse.eval_collectBalanced, rawRowCheck3185]

def rawRow3186 : Integer.Sparse Key := [(key3075, -2), (key3061, -2), (key3143, -2), (key3076, 2), (key3068, 2), (key3142, 2), (key2691, 2), (key2679, 2), (key3014, 2), (key2755, -6), (key2691, -2), (key2684, -2), (key2820, -2), (key2717, 6)]

theorem rawRowCheck3186 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form6 = rawRow3186 := by decide +kernel

def row3186 : Integer.Sparse Key := [(key2679, 2), (key2684, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3014, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3142, 2), (key3143, -2)]

theorem rowCheck3186 : row3186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3186 := by decide +kernel

theorem rowEval3186 (x : Key → ℝ) : Integer.Sparse.eval row3186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3186, Integer.Sparse.eval_collectBalanced, rawRowCheck3186]

def rawRow3187 : Integer.Sparse Key := [(key3061, -2), (key3143, -2), (key3075, -2), (key3068, 2), (key3142, 2), (key3076, 2), (key3047, 2), (key3115, 2), (key2691, 2), (key2755, -6), (key2684, -2), (key2820, -2), (key2691, -2), (key2717, 6)]

theorem rawRowCheck3187 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form6 = rawRow3187 := by decide +kernel

def row3187 : Integer.Sparse Key := [(key2684, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3047, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3115, 2), (key3142, 2), (key3143, -2)]

theorem rowCheck3187 : row3187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3187 := by decide +kernel

theorem rowEval3187 (x : Key → ℝ) : Integer.Sparse.eval row3187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3187, Integer.Sparse.eval_collectBalanced, rawRowCheck3187]

def rawRow3188 : Integer.Sparse Key := [(key3143, -2), (key3061, -2), (key3075, -2), (key3142, 2), (key3068, 2), (key3076, 2), (key3115, 2), (key3047, 2), (key2691, 2), (key2755, -6), (key2820, -2), (key2684, -2), (key2691, -2), (key2717, 6)]

theorem rawRowCheck3188 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form6 = rawRow3188 := by decide +kernel

def row3188 : Integer.Sparse Key := [(key2684, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3047, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3115, 2), (key3142, 2), (key3143, -2)]

theorem rowCheck3188 : row3188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3188 := by decide +kernel

theorem rowEval3188 (x : Key → ℝ) : Integer.Sparse.eval row3188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3188, Integer.Sparse.eval_collectBalanced, rawRowCheck3188]

def rawRow3189 : Integer.Sparse Key := [(key3075, -2), (key3143, -2), (key3061, -2), (key3076, 2), (key3142, 2), (key3068, 2), (key3058, 2), (key3115, 2), (key2679, 2), (key2755, -6), (key2691, -2), (key2820, -2), (key2684, -2), (key2717, 6)]

theorem rawRowCheck3189 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form6 = rawRow3189 := by decide +kernel

def row3189 : Integer.Sparse Key := [(key2679, 2), (key2684, -2), (key2691, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3058, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3115, 2), (key3142, 2), (key3143, -2)]

theorem rowCheck3189 : row3189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3189 := by decide +kernel

theorem rowEval3189 (x : Key → ℝ) : Integer.Sparse.eval row3189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3189, Integer.Sparse.eval_collectBalanced, rawRowCheck3189]

def rawRow3190 : Integer.Sparse Key := [(key3143, -2), (key3075, -2), (key3061, -2), (key3142, 2), (key3076, 2), (key3068, 2), (key3115, 2), (key3058, 2), (key3047, 2), (key2755, -6), (key2820, -2), (key2691, -2), (key2684, -2), (key2717, 6)]

theorem rawRowCheck3190 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form6 = rawRow3190 := by decide +kernel

def row3190 : Integer.Sparse Key := [(key2684, -2), (key2691, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3047, 2), (key3058, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3115, 2), (key3142, 2), (key3143, -2)]

theorem rowCheck3190 : row3190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3190 := by decide +kernel

theorem rowEval3190 (x : Key → ℝ) : Integer.Sparse.eval row3190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3190, Integer.Sparse.eval_collectBalanced, rawRowCheck3190]

def rawRow3191 : Integer.Sparse Key := [(key3053, -2), (key3068, -2), (key3105, -2), (key3047, 2), (key3061, 2), (key3096, 2), (key3058, 2), (key3076, 2), (key3115, 2), (key2679, -6), (key2691, -2), (key2717, -2), (key2820, -2), (key2684, 6)]

theorem rawRowCheck3191 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form6 = rawRow3191 := by decide +kernel

def row3191 : Integer.Sparse Key := [(key2679, -6), (key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, 2), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

theorem rowCheck3191 : row3191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3191 := by decide +kernel

theorem rowEval3191 (x : Key → ℝ) : Integer.Sparse.eval row3191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3191, Integer.Sparse.eval_collectBalanced, rawRowCheck3191]

def rawRow3192 : Integer.Sparse Key := [(key3068, -2), (key3053, -2), (key3105, -2), (key3061, 2), (key3047, 2), (key3096, 2), (key3076, 2), (key3058, 2), (key3115, 2), (key2679, -6), (key2717, -2), (key2691, -2), (key2820, -2), (key2684, 6)]

theorem rawRowCheck3192 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form6 = rawRow3192 := by decide +kernel

def row3192 : Integer.Sparse Key := [(key2679, -6), (key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, 2), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

theorem rowCheck3192 : row3192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3192 := by decide +kernel

theorem rowEval3192 (x : Key → ℝ) : Integer.Sparse.eval row3192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3192, Integer.Sparse.eval_collectBalanced, rawRowCheck3192]

def rawRow3193 : Integer.Sparse Key := [(key3053, -2), (key3105, -2), (key3068, -2), (key3047, 2), (key3096, 2), (key3061, 2), (key3058, 2), (key3115, 2), (key3076, 2), (key2679, -6), (key2691, -2), (key2820, -2), (key2717, -2), (key2684, 6)]

theorem rawRowCheck3193 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form6 = rawRow3193 := by decide +kernel

def row3193 : Integer.Sparse Key := [(key2679, -6), (key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, 2), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

theorem rowCheck3193 : row3193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3193 := by decide +kernel

theorem rowEval3193 (x : Key → ℝ) : Integer.Sparse.eval row3193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3193, Integer.Sparse.eval_collectBalanced, rawRowCheck3193]

def rawRow3194 : Integer.Sparse Key := [(key3105, -2), (key3053, -2), (key3068, -2), (key3096, 2), (key3047, 2), (key3061, 2), (key3115, 2), (key3058, 2), (key3076, 2), (key3047, -6), (key2820, -2), (key2691, -2), (key2717, -2), (key2684, 6)]

theorem rawRowCheck3194 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form6 = rawRow3194 := by decide +kernel

def row3194 : Integer.Sparse Key := [(key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, -4), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

theorem rowCheck3194 : row3194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3194 := by decide +kernel

theorem rowEval3194 (x : Key → ℝ) : Integer.Sparse.eval row3194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3194, Integer.Sparse.eval_collectBalanced, rawRowCheck3194]

def rawRow3195 : Integer.Sparse Key := [(key3068, -2), (key3105, -2), (key3053, -2), (key3061, 2), (key3096, 2), (key3047, 2), (key3076, 2), (key3115, 2), (key3058, 2), (key3047, -6), (key2717, -2), (key2820, -2), (key2691, -2), (key2684, 6)]

theorem rawRowCheck3195 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form6 = rawRow3195 := by decide +kernel

def row3195 : Integer.Sparse Key := [(key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, -4), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

theorem rowCheck3195 : row3195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3195 := by decide +kernel

theorem rowEval3195 (x : Key → ℝ) : Integer.Sparse.eval row3195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3195, Integer.Sparse.eval_collectBalanced, rawRowCheck3195]

def rawRow3196 : Integer.Sparse Key := [(key3105, -2), (key3068, -2), (key3053, -2), (key3096, 2), (key3061, 2), (key3047, 2), (key3115, 2), (key3076, 2), (key3058, 2), (key3047, -6), (key2820, -2), (key2717, -2), (key2691, -2), (key2684, 6)]

theorem rawRowCheck3196 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form6 = rawRow3196 := by decide +kernel

def row3196 : Integer.Sparse Key := [(key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, -4), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

theorem rowCheck3196 : row3196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3196 := by decide +kernel

theorem rowEval3196 (x : Key → ℝ) : Integer.Sparse.eval row3196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3196, Integer.Sparse.eval_collectBalanced, rawRowCheck3196]

def rawRow3197 : Integer.Sparse Key := [(key3075, -2), (key3075, -2), (key3143, -2), (key3076, 2), (key3076, 2), (key3142, 2), (key3053, 2), (key3053, 2), (key3105, 2), (key3068, -6), (key2679, -2), (key2679, -2), (key2813, -2), (key2710, 6)]

theorem rawRowCheck3197 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form6 = rawRow3197 := by decide +kernel

def row3197 : Integer.Sparse Key := [(key2679, -4), (key2710, 6), (key2813, -2), (key3053, 4), (key3068, -6), (key3075, -4), (key3076, 4), (key3105, 2), (key3142, 2), (key3143, -2)]

theorem rowCheck3197 : row3197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3197 := by decide +kernel

theorem rowEval3197 (x : Key → ℝ) : Integer.Sparse.eval row3197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3197, Integer.Sparse.eval_collectBalanced, rawRowCheck3197]

def rawRow3198 : Integer.Sparse Key := [(key3075, -2), (key3143, -2), (key3075, -2), (key3076, 2), (key3142, 2), (key3076, 2), (key3053, 2), (key3105, 2), (key3053, 2), (key3068, -6), (key3047, -2), (key3096, -2), (key2679, -2), (key2710, 6)]

theorem rawRowCheck3198 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form6 = rawRow3198 := by decide +kernel

def row3198 : Integer.Sparse Key := [(key2679, -2), (key2710, 6), (key3047, -2), (key3053, 4), (key3068, -6), (key3075, -4), (key3076, 4), (key3096, -2), (key3105, 2), (key3142, 2), (key3143, -2)]

theorem rowCheck3198 : row3198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3198 := by decide +kernel

theorem rowEval3198 (x : Key → ℝ) : Integer.Sparse.eval row3198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3198, Integer.Sparse.eval_collectBalanced, rawRowCheck3198]

def rawRow3199 : Integer.Sparse Key := [(key3143, -2), (key3075, -2), (key3075, -2), (key3142, 2), (key3076, 2), (key3076, 2), (key3105, 2), (key3053, 2), (key3053, 2), (key3068, -6), (key3096, -2), (key3047, -2), (key3047, -2), (key2710, 6)]

theorem rawRowCheck3199 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form6 = rawRow3199 := by decide +kernel

def row3199 : Integer.Sparse Key := [(key2710, 6), (key3047, -4), (key3053, 4), (key3068, -6), (key3075, -4), (key3076, 4), (key3096, -2), (key3105, 2), (key3142, 2), (key3143, -2)]

theorem rowCheck3199 : row3199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3199 := by decide +kernel

theorem rowEval3199 (x : Key → ℝ) : Integer.Sparse.eval row3199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3199, Integer.Sparse.eval_collectBalanced, rawRowCheck3199]

end MUB6.Certificate.GramRows

end OAI
