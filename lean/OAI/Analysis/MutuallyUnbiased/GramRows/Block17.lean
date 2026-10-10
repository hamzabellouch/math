import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
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

def rawRow640 : Integer.Sparse Key := [(key2985, -2), (key2633, -2), (key2985, -2), (key2978, 1), (key2994, 1), (key2643, 1), (key2994, 1), (key2643, 1), (key2978, 1), (key2962, 2), (key2617, 2), (key2962, 2), (key2749, -1), (key3004, -1), (key2655, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2833, -1), (key2964, -1), (key2620, -1), (key2964, -1), (key2620, -1), (key2833, -1), (key2730, 1), (key2994, 1), (key2643, 1), (key2994, 1), (key2643, 1), (key2730, 1)]

theorem rawRowCheck640 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form0 = rawRow640 := by decide +kernel

def row640 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2730, 2), (key2749, -2), (key2833, -2), (key2962, 4), (key2964, -2), (key2978, 2), (key2985, -4), (key2994, 4), (key3004, -2)]

theorem rowCheck640 : row640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow640 := by decide +kernel

theorem rowEval640 (x : Key → ℝ) : Integer.Sparse.eval row640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck640, Integer.Sparse.eval_collectBalanced, rawRowCheck640]

def rawRow641 : Integer.Sparse Key := [(key2985, -2), (key2985, -2), (key2633, -2), (key2994, 1), (key2978, 1), (key2994, 1), (key2643, 1), (key2978, 1), (key2643, 1), (key2962, 2), (key2962, 2), (key2617, 2), (key3004, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2655, -1), (key2964, -1), (key2833, -1), (key2964, -1), (key2620, -1), (key2833, -1), (key2620, -1), (key2994, 1), (key2730, 1), (key2994, 1), (key2643, 1), (key2730, 1), (key2643, 1)]

theorem rawRowCheck641 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form0 = rawRow641 := by decide +kernel

def row641 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2730, 2), (key2749, -2), (key2833, -2), (key2962, 4), (key2964, -2), (key2978, 2), (key2985, -4), (key2994, 4), (key3004, -2)]

theorem rowCheck641 : row641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow641 := by decide +kernel

theorem rowEval641 (x : Key → ℝ) : Integer.Sparse.eval row641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck641, Integer.Sparse.eval_collectBalanced, rawRowCheck641]

def rawRow642 : Integer.Sparse Key := [(key2643, -2), (key2730, -2), (key2994, -2), (key2633, 1), (key2643, 1), (key2707, 1), (key2978, 1), (key2730, 1), (key2985, 1), (key2655, 2), (key2749, 2), (key3004, 2), (key2617, -1), (key2655, -1), (key2672, -1), (key2749, -1), (key2945, -1), (key2962, -1), (key2643, -1), (key2656, -1), (key2797, -1), (key2915, -1), (key2946, -1), (key2994, -1), (key2620, 1), (key2656, 1), (key2675, 1), (key2751, 1), (key2946, 1), (key2964, 1)]

theorem rawRowCheck642 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form0 = rawRow642 := by decide +kernel

def row642 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, 1), (key2797, -1), (key2915, -1), (key2945, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

theorem rowCheck642 : row642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow642 := by decide +kernel

theorem rowEval642 (x : Key → ℝ) : Integer.Sparse.eval row642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck642, Integer.Sparse.eval_collectBalanced, rawRowCheck642]

def rawRow643 : Integer.Sparse Key := [(key2643, -2), (key2994, -2), (key2730, -2), (key2643, 1), (key2633, 1), (key2978, 1), (key2707, 1), (key2985, 1), (key2730, 1), (key2655, 2), (key3004, 2), (key2749, 2), (key2655, -1), (key2617, -1), (key2749, -1), (key2672, -1), (key2962, -1), (key2945, -1), (key2656, -1), (key2643, -1), (key2915, -1), (key2797, -1), (key2994, -1), (key2946, -1), (key2656, 1), (key2620, 1), (key2751, 1), (key2675, 1), (key2964, 1), (key2946, 1)]

theorem rawRowCheck643 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form0 = rawRow643 := by decide +kernel

def row643 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, 1), (key2797, -1), (key2915, -1), (key2945, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

theorem rowCheck643 : row643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow643 := by decide +kernel

theorem rowEval643 (x : Key → ℝ) : Integer.Sparse.eval row643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck643, Integer.Sparse.eval_collectBalanced, rawRowCheck643]

def rawRow644 : Integer.Sparse Key := [(key2730, -2), (key2643, -2), (key2994, -2), (key2707, 1), (key2730, 1), (key2633, 1), (key2985, 1), (key2643, 1), (key2978, 1), (key2749, 2), (key2655, 2), (key3004, 2), (key2672, -1), (key2749, -1), (key2617, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2797, -1), (key2946, -1), (key2643, -1), (key2994, -1), (key2656, -1), (key2915, -1), (key2675, 1), (key2946, 1), (key2620, 1), (key2964, 1), (key2656, 1), (key2751, 1)]

theorem rawRowCheck644 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form0 = rawRow644 := by decide +kernel

def row644 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2751, 1), (key2797, -1), (key2915, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

theorem rowCheck644 : row644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow644 := by decide +kernel

theorem rowEval644 (x : Key → ℝ) : Integer.Sparse.eval row644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck644, Integer.Sparse.eval_collectBalanced, rawRowCheck644]

def rawRow645 : Integer.Sparse Key := [(key2730, -2), (key2994, -2), (key2643, -2), (key2730, 1), (key2707, 1), (key2985, 1), (key2633, 1), (key2978, 1), (key2643, 1), (key2749, 2), (key3004, 2), (key2655, 2), (key2749, -1), (key2672, -1), (key2962, -1), (key2617, -1), (key2749, -1), (key2655, -1), (key2946, -1), (key2797, -1), (key2994, -1), (key2643, -1), (key2915, -1), (key2656, -1), (key2946, 1), (key2675, 1), (key2964, 1), (key2620, 1), (key2751, 1), (key2656, 1)]

theorem rawRowCheck645 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form0 = rawRow645 := by decide +kernel

def row645 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2751, 1), (key2797, -1), (key2915, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

theorem rowCheck645 : row645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow645 := by decide +kernel

theorem rowEval645 (x : Key → ℝ) : Integer.Sparse.eval row645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck645, Integer.Sparse.eval_collectBalanced, rawRowCheck645]

def rawRow646 : Integer.Sparse Key := [(key2994, -2), (key2643, -2), (key2730, -2), (key2978, 1), (key2985, 1), (key2643, 1), (key2730, 1), (key2633, 1), (key2707, 1), (key3004, 2), (key2655, 2), (key2749, 2), (key2945, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2617, -1), (key2672, -1), (key2915, -1), (key2994, -1), (key2656, -1), (key2946, -1), (key2643, -1), (key2797, -1), (key2751, 1), (key2964, 1), (key2656, 1), (key2946, 1), (key2620, 1), (key2675, 1)]

theorem rawRowCheck646 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form0 = rawRow646 := by decide +kernel

def row646 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, 1), (key2797, -1), (key2915, -1), (key2945, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

theorem rowCheck646 : row646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow646 := by decide +kernel

theorem rowEval646 (x : Key → ℝ) : Integer.Sparse.eval row646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck646, Integer.Sparse.eval_collectBalanced, rawRowCheck646]

def rawRow647 : Integer.Sparse Key := [(key2994, -2), (key2730, -2), (key2643, -2), (key2985, 1), (key2978, 1), (key2730, 1), (key2643, 1), (key2707, 1), (key2633, 1), (key3004, 2), (key2749, 2), (key2655, 2), (key2962, -1), (key2945, -1), (key2749, -1), (key2655, -1), (key2672, -1), (key2617, -1), (key2994, -1), (key2915, -1), (key2946, -1), (key2656, -1), (key2797, -1), (key2643, -1), (key2964, 1), (key2751, 1), (key2946, 1), (key2656, 1), (key2675, 1), (key2620, 1)]

theorem rawRowCheck647 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form0 = rawRow647 := by decide +kernel

def row647 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, 1), (key2797, -1), (key2915, -1), (key2945, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

theorem rowCheck647 : row647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow647 := by decide +kernel

theorem rowEval647 (x : Key → ℝ) : Integer.Sparse.eval row647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck647, Integer.Sparse.eval_collectBalanced, rawRowCheck647]

def rawRow648 : Integer.Sparse Key := [(key2650, -2), (key2906, -2), (key3001, -2), (key2655, 1), (key2656, 1), (key2899, 1), (key2999, 1), (key2915, 1), (key3004, 1), (key2620, 2), (key2833, 2), (key2964, 2), (key2643, -1), (key2656, -1), (key2797, -1), (key2946, -1), (key2915, -1), (key2994, -1), (key2617, -1), (key2620, -1), (key2810, -1), (key2833, -1), (key2952, -1), (key2962, -1), (key2633, 1), (key2643, 1), (key2707, 1), (key2730, 1), (key2978, 1), (key2985, 1)]

theorem rawRowCheck648 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block1.form0 = rawRow648 := by decide +kernel

def row648 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

theorem rowCheck648 : row648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow648 := by decide +kernel

theorem rowEval648 (x : Key → ℝ) : Integer.Sparse.eval row648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck648, Integer.Sparse.eval_collectBalanced, rawRowCheck648]

def rawRow649 : Integer.Sparse Key := [(key2650, -2), (key3001, -2), (key2906, -2), (key2656, 1), (key2655, 1), (key2999, 1), (key2899, 1), (key3004, 1), (key2915, 1), (key2620, 2), (key2964, 2), (key2833, 2), (key2656, -1), (key2643, -1), (key2946, -1), (key2797, -1), (key2994, -1), (key2915, -1), (key2620, -1), (key2617, -1), (key2833, -1), (key2810, -1), (key2962, -1), (key2952, -1), (key2643, 1), (key2633, 1), (key2730, 1), (key2707, 1), (key2985, 1), (key2978, 1)]

theorem rawRowCheck649 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block1.form0 = rawRow649 := by decide +kernel

def row649 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

theorem rowCheck649 : row649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow649 := by decide +kernel

theorem rowEval649 (x : Key → ℝ) : Integer.Sparse.eval row649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck649, Integer.Sparse.eval_collectBalanced, rawRowCheck649]

def rawRow650 : Integer.Sparse Key := [(key2906, -2), (key2650, -2), (key3001, -2), (key2899, 1), (key2915, 1), (key2655, 1), (key3004, 1), (key2656, 1), (key2999, 1), (key2833, 2), (key2620, 2), (key2964, 2), (key2797, -1), (key2915, -1), (key2643, -1), (key2994, -1), (key2656, -1), (key2946, -1), (key2810, -1), (key2833, -1), (key2617, -1), (key2962, -1), (key2620, -1), (key2833, -1), (key2707, 1), (key2978, 1), (key2633, 1), (key2985, 1), (key2643, 1), (key2730, 1)]

theorem rawRowCheck650 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block1.form0 = rawRow650 := by decide +kernel

def row650 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2899, 1), (key2906, -2), (key2946, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

theorem rowCheck650 : row650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow650 := by decide +kernel

theorem rowEval650 (x : Key → ℝ) : Integer.Sparse.eval row650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck650, Integer.Sparse.eval_collectBalanced, rawRowCheck650]

def rawRow651 : Integer.Sparse Key := [(key2906, -2), (key3001, -2), (key2650, -2), (key2915, 1), (key2899, 1), (key3004, 1), (key2655, 1), (key2999, 1), (key2656, 1), (key2833, 2), (key2964, 2), (key2620, 2), (key2915, -1), (key2797, -1), (key2994, -1), (key2643, -1), (key2946, -1), (key2656, -1), (key2833, -1), (key2810, -1), (key2962, -1), (key2617, -1), (key2833, -1), (key2620, -1), (key2978, 1), (key2707, 1), (key2985, 1), (key2633, 1), (key2730, 1), (key2643, 1)]

theorem rawRowCheck651 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block1.form0 = rawRow651 := by decide +kernel

def row651 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2899, 1), (key2906, -2), (key2946, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

theorem rowCheck651 : row651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow651 := by decide +kernel

theorem rowEval651 (x : Key → ℝ) : Integer.Sparse.eval row651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck651, Integer.Sparse.eval_collectBalanced, rawRowCheck651]

def rawRow652 : Integer.Sparse Key := [(key3001, -2), (key2650, -2), (key2906, -2), (key2999, 1), (key3004, 1), (key2656, 1), (key2915, 1), (key2655, 1), (key2899, 1), (key2964, 2), (key2620, 2), (key2833, 2), (key2946, -1), (key2994, -1), (key2656, -1), (key2915, -1), (key2643, -1), (key2797, -1), (key2952, -1), (key2962, -1), (key2620, -1), (key2833, -1), (key2617, -1), (key2810, -1), (key2730, 1), (key2985, 1), (key2643, 1), (key2978, 1), (key2633, 1), (key2707, 1)]

theorem rawRowCheck652 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block1.form0 = rawRow652 := by decide +kernel

def row652 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

theorem rowCheck652 : row652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow652 := by decide +kernel

theorem rowEval652 (x : Key → ℝ) : Integer.Sparse.eval row652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck652, Integer.Sparse.eval_collectBalanced, rawRowCheck652]

def rawRow653 : Integer.Sparse Key := [(key3001, -2), (key2906, -2), (key2650, -2), (key3004, 1), (key2999, 1), (key2915, 1), (key2656, 1), (key2899, 1), (key2655, 1), (key2964, 2), (key2833, 2), (key2620, 2), (key2994, -1), (key2946, -1), (key2915, -1), (key2656, -1), (key2797, -1), (key2643, -1), (key2962, -1), (key2952, -1), (key2833, -1), (key2620, -1), (key2810, -1), (key2617, -1), (key2985, 1), (key2730, 1), (key2978, 1), (key2643, 1), (key2707, 1), (key2633, 1)]

theorem rawRowCheck653 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block1.form0 = rawRow653 := by decide +kernel

def row653 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

theorem rowCheck653 : row653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow653 := by decide +kernel

theorem rowEval653 (x : Key → ℝ) : Integer.Sparse.eval row653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck653, Integer.Sparse.eval_collectBalanced, rawRowCheck653]

def rawRow654 : Integer.Sparse Key := [(key2655, -2), (key2749, -2), (key3004, -2), (key2650, 1), (key2656, 1), (key2739, 1), (key2999, 1), (key2751, 1), (key3001, 1), (key2643, 2), (key2730, 2), (key2994, 2), (key2620, -1), (key2656, -1), (key2675, -1), (key2946, -1), (key2751, -1), (key2964, -1), (key2633, -1), (key2643, -1), (key2707, -1), (key2978, -1), (key2730, -1), (key2985, -1), (key2617, 1), (key2655, 1), (key2672, 1), (key2749, 1), (key2945, 1), (key2962, 1)]

theorem rawRowCheck654 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form0 = rawRow654 := by decide +kernel

def row654 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck654 : row654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow654 := by decide +kernel

theorem rowEval654 (x : Key → ℝ) : Integer.Sparse.eval row654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck654, Integer.Sparse.eval_collectBalanced, rawRowCheck654]

def rawRow655 : Integer.Sparse Key := [(key2655, -2), (key3004, -2), (key2749, -2), (key2656, 1), (key2650, 1), (key2999, 1), (key2739, 1), (key3001, 1), (key2751, 1), (key2643, 2), (key2994, 2), (key2730, 2), (key2656, -1), (key2620, -1), (key2946, -1), (key2675, -1), (key2964, -1), (key2751, -1), (key2643, -1), (key2633, -1), (key2978, -1), (key2707, -1), (key2985, -1), (key2730, -1), (key2655, 1), (key2617, 1), (key2749, 1), (key2672, 1), (key2962, 1), (key2945, 1)]

theorem rawRowCheck655 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form0 = rawRow655 := by decide +kernel

def row655 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck655 : row655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow655 := by decide +kernel

theorem rowEval655 (x : Key → ℝ) : Integer.Sparse.eval row655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck655, Integer.Sparse.eval_collectBalanced, rawRowCheck655]

def rawRow656 : Integer.Sparse Key := [(key2749, -2), (key2655, -2), (key3004, -2), (key2739, 1), (key2751, 1), (key2650, 1), (key3001, 1), (key2656, 1), (key2999, 1), (key2730, 2), (key2643, 2), (key2994, 2), (key2675, -1), (key2751, -1), (key2620, -1), (key2964, -1), (key2656, -1), (key2946, -1), (key2707, -1), (key2730, -1), (key2633, -1), (key2985, -1), (key2643, -1), (key2978, -1), (key2672, 1), (key2749, 1), (key2617, 1), (key2962, 1), (key2655, 1), (key2749, 1)]

theorem rawRowCheck656 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form0 = rawRow656 := by decide +kernel

def row656 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck656 : row656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow656 := by decide +kernel

theorem rowEval656 (x : Key → ℝ) : Integer.Sparse.eval row656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck656, Integer.Sparse.eval_collectBalanced, rawRowCheck656]

def rawRow657 : Integer.Sparse Key := [(key2749, -2), (key3004, -2), (key2655, -2), (key2751, 1), (key2739, 1), (key3001, 1), (key2650, 1), (key2999, 1), (key2656, 1), (key2730, 2), (key2994, 2), (key2643, 2), (key2751, -1), (key2675, -1), (key2964, -1), (key2620, -1), (key2946, -1), (key2656, -1), (key2730, -1), (key2707, -1), (key2985, -1), (key2633, -1), (key2978, -1), (key2643, -1), (key2749, 1), (key2672, 1), (key2962, 1), (key2617, 1), (key2749, 1), (key2655, 1)]

theorem rawRowCheck657 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form0 = rawRow657 := by decide +kernel

def row657 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck657 : row657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow657 := by decide +kernel

theorem rowEval657 (x : Key → ℝ) : Integer.Sparse.eval row657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck657, Integer.Sparse.eval_collectBalanced, rawRowCheck657]

def rawRow658 : Integer.Sparse Key := [(key3004, -2), (key2655, -2), (key2749, -2), (key2999, 1), (key3001, 1), (key2656, 1), (key2751, 1), (key2650, 1), (key2739, 1), (key2994, 2), (key2643, 2), (key2730, 2), (key2946, -1), (key2964, -1), (key2656, -1), (key2751, -1), (key2620, -1), (key2675, -1), (key2978, -1), (key2985, -1), (key2643, -1), (key2730, -1), (key2633, -1), (key2707, -1), (key2945, 1), (key2962, 1), (key2655, 1), (key2749, 1), (key2617, 1), (key2672, 1)]

theorem rawRowCheck658 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form0 = rawRow658 := by decide +kernel

def row658 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck658 : row658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow658 := by decide +kernel

theorem rowEval658 (x : Key → ℝ) : Integer.Sparse.eval row658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck658, Integer.Sparse.eval_collectBalanced, rawRowCheck658]

def rawRow659 : Integer.Sparse Key := [(key3004, -2), (key2749, -2), (key2655, -2), (key3001, 1), (key2999, 1), (key2751, 1), (key2656, 1), (key2739, 1), (key2650, 1), (key2994, 2), (key2730, 2), (key2643, 2), (key2964, -1), (key2946, -1), (key2751, -1), (key2656, -1), (key2675, -1), (key2620, -1), (key2985, -1), (key2978, -1), (key2730, -1), (key2643, -1), (key2707, -1), (key2633, -1), (key2962, 1), (key2945, 1), (key2749, 1), (key2655, 1), (key2672, 1), (key2617, 1)]

theorem rawRowCheck659 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form0 = rawRow659 := by decide +kernel

def row659 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck659 : row659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow659 := by decide +kernel

theorem rowEval659 (x : Key → ℝ) : Integer.Sparse.eval row659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck659, Integer.Sparse.eval_collectBalanced, rawRowCheck659]

def rawRow660 : Integer.Sparse Key := [(key1422, -2), (key1422, -2), (key1422, -2), (key1453, 1), (key1453, 1), (key1453, 1), (key1453, 1), (key1453, 1), (key1453, 1), (key1571, 2), (key1571, 2), (key1571, 2), (key1653, -1), (key1653, -1), (key1653, -1), (key1653, -1), (key1653, -1), (key1653, -1), (key1786, -1), (key1786, -1), (key1786, -1), (key1786, -1), (key1786, -1), (key1786, -1), (key1811, 1), (key1811, 1), (key1811, 1), (key1811, 1), (key1811, 1), (key1811, 1)]

theorem rawRowCheck660 : GramPolynomial.normalizedRow 0 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form0 = rawRow660 := by decide +kernel

def row660 : Integer.Sparse Key := [(key1422, -6), (key1453, 6), (key1571, 6), (key1653, -6), (key1786, -6), (key1811, 6)]

theorem rowCheck660 : row660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow660 := by decide +kernel

theorem rowEval660 (x : Key → ℝ) : Integer.Sparse.eval row660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck660, Integer.Sparse.eval_collectBalanced, rawRowCheck660]

def rawRow661 : Integer.Sparse Key := [(key1389, -2), (key1453, -2), (key1453, -2), (key1389, 1), (key1389, 1), (key1422, 1), (key1422, 1), (key1453, 1), (key1453, 1), (key1544, 2), (key1653, 2), (key1653, 2), (key1544, -1), (key1544, -1), (key1571, -1), (key1571, -1), (key1653, -1), (key1653, -1), (key1770, -1), (key1770, -1), (key1811, -1), (key1811, -1), (key1838, -1), (key1838, -1), (key1770, 1), (key1770, 1), (key1786, 1), (key1786, 1), (key1838, 1), (key1838, 1)]

theorem rawRowCheck661 : GramPolynomial.normalizedRow 0 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form0 = rawRow661 := by decide +kernel

def row661 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

theorem rowCheck661 : row661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow661 := by decide +kernel

theorem rowEval661 (x : Key → ℝ) : Integer.Sparse.eval row661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck661, Integer.Sparse.eval_collectBalanced, rawRowCheck661]

def rawRow662 : Integer.Sparse Key := [(key1453, -2), (key1389, -2), (key1453, -2), (key1422, 1), (key1453, 1), (key1389, 1), (key1453, 1), (key1389, 1), (key1422, 1), (key1653, 2), (key1544, 2), (key1653, 2), (key1571, -1), (key1653, -1), (key1544, -1), (key1653, -1), (key1544, -1), (key1571, -1), (key1811, -1), (key1838, -1), (key1770, -1), (key1838, -1), (key1770, -1), (key1811, -1), (key1786, 1), (key1838, 1), (key1770, 1), (key1838, 1), (key1770, 1), (key1786, 1)]

theorem rawRowCheck662 : GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form0 = rawRow662 := by decide +kernel

def row662 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

theorem rowCheck662 : row662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow662 := by decide +kernel

theorem rowEval662 (x : Key → ℝ) : Integer.Sparse.eval row662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck662, Integer.Sparse.eval_collectBalanced, rawRowCheck662]

def rawRow663 : Integer.Sparse Key := [(key1453, -2), (key1453, -2), (key1389, -2), (key1453, 1), (key1422, 1), (key1453, 1), (key1389, 1), (key1422, 1), (key1389, 1), (key1653, 2), (key1653, 2), (key1544, 2), (key1653, -1), (key1571, -1), (key1653, -1), (key1544, -1), (key1571, -1), (key1544, -1), (key1838, -1), (key1811, -1), (key1838, -1), (key1770, -1), (key1811, -1), (key1770, -1), (key1838, 1), (key1786, 1), (key1838, 1), (key1770, 1), (key1786, 1), (key1770, 1)]

theorem rawRowCheck663 : GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form0 = rawRow663 := by decide +kernel

def row663 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

theorem rowCheck663 : row663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow663 := by decide +kernel

theorem rowEval663 (x : Key → ℝ) : Integer.Sparse.eval row663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck663, Integer.Sparse.eval_collectBalanced, rawRowCheck663]

def rawRow664 : Integer.Sparse Key := [(key1571, -2), (key1571, -2), (key1571, -2), (key1786, 1), (key1786, 1), (key1786, 1), (key1786, 1), (key1786, 1), (key1786, 1), (key1422, 2), (key1422, 2), (key1422, 2), (key1811, -1), (key1811, -1), (key1811, -1), (key1811, -1), (key1811, -1), (key1811, -1), (key1453, -1), (key1453, -1), (key1453, -1), (key1453, -1), (key1453, -1), (key1453, -1), (key1653, 1), (key1653, 1), (key1653, 1), (key1653, 1), (key1653, 1), (key1653, 1)]

theorem rawRowCheck664 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form0 = rawRow664 := by decide +kernel

def row664 : Integer.Sparse Key := [(key1422, 6), (key1453, -6), (key1571, -6), (key1653, 6), (key1786, 6), (key1811, -6)]

theorem rowCheck664 : row664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow664 := by decide +kernel

theorem rowEval664 (x : Key → ℝ) : Integer.Sparse.eval row664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck664, Integer.Sparse.eval_collectBalanced, rawRowCheck664]

def rawRow665 : Integer.Sparse Key := [(key1294, -2), (key1786, -2), (key1786, -2), (key1294, 1), (key1294, 1), (key1571, 1), (key1571, 1), (key1786, 1), (key1786, 1), (key1314, 2), (key1811, 2), (key1811, 2), (key1314, -1), (key1314, -1), (key1422, -1), (key1422, -1), (key1811, -1), (key1811, -1), (key1335, -1), (key1335, -1), (key1653, -1), (key1653, -1), (key1838, -1), (key1838, -1), (key1335, 1), (key1335, 1), (key1453, 1), (key1453, 1), (key1838, 1), (key1838, 1)]

theorem rawRowCheck665 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form0 = rawRow665 := by decide +kernel

def row665 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

theorem rowCheck665 : row665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow665 := by decide +kernel

theorem rowEval665 (x : Key → ℝ) : Integer.Sparse.eval row665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck665, Integer.Sparse.eval_collectBalanced, rawRowCheck665]

def rawRow666 : Integer.Sparse Key := [(key1786, -2), (key1294, -2), (key1786, -2), (key1571, 1), (key1786, 1), (key1294, 1), (key1786, 1), (key1294, 1), (key1571, 1), (key1811, 2), (key1314, 2), (key1811, 2), (key1422, -1), (key1811, -1), (key1314, -1), (key1811, -1), (key1314, -1), (key1422, -1), (key1653, -1), (key1838, -1), (key1335, -1), (key1838, -1), (key1335, -1), (key1653, -1), (key1453, 1), (key1838, 1), (key1335, 1), (key1838, 1), (key1335, 1), (key1453, 1)]

theorem rawRowCheck666 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form0 = rawRow666 := by decide +kernel

def row666 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

theorem rowCheck666 : row666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow666 := by decide +kernel

theorem rowEval666 (x : Key → ℝ) : Integer.Sparse.eval row666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck666, Integer.Sparse.eval_collectBalanced, rawRowCheck666]

def rawRow667 : Integer.Sparse Key := [(key1786, -2), (key1786, -2), (key1294, -2), (key1786, 1), (key1571, 1), (key1786, 1), (key1294, 1), (key1571, 1), (key1294, 1), (key1811, 2), (key1811, 2), (key1314, 2), (key1811, -1), (key1422, -1), (key1811, -1), (key1314, -1), (key1422, -1), (key1314, -1), (key1838, -1), (key1653, -1), (key1838, -1), (key1335, -1), (key1653, -1), (key1335, -1), (key1838, 1), (key1453, 1), (key1838, 1), (key1335, 1), (key1453, 1), (key1335, 1)]

theorem rawRowCheck667 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form0 = rawRow667 := by decide +kernel

def row667 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

theorem rowCheck667 : row667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow667 := by decide +kernel

theorem rowEval667 (x : Key → ℝ) : Integer.Sparse.eval row667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck667, Integer.Sparse.eval_collectBalanced, rawRowCheck667]

def rawRow668 : Integer.Sparse Key := [(key1544, -2), (key1653, -2), (key1653, -2), (key1770, 1), (key1770, 1), (key1811, 1), (key1811, 1), (key1838, 1), (key1838, 1), (key1389, 2), (key1453, 2), (key1453, 2), (key1770, -1), (key1770, -1), (key1786, -1), (key1786, -1), (key1838, -1), (key1838, -1), (key1389, -1), (key1389, -1), (key1422, -1), (key1422, -1), (key1453, -1), (key1453, -1), (key1544, 1), (key1544, 1), (key1571, 1), (key1571, 1), (key1653, 1), (key1653, 1)]

theorem rawRowCheck668 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form0 = rawRow668 := by decide +kernel

def row668 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

theorem rowCheck668 : row668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow668 := by decide +kernel

theorem rowEval668 (x : Key → ℝ) : Integer.Sparse.eval row668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck668, Integer.Sparse.eval_collectBalanced, rawRowCheck668]

def rawRow669 : Integer.Sparse Key := [(key1653, -2), (key1544, -2), (key1653, -2), (key1811, 1), (key1838, 1), (key1770, 1), (key1838, 1), (key1770, 1), (key1811, 1), (key1453, 2), (key1389, 2), (key1453, 2), (key1786, -1), (key1838, -1), (key1770, -1), (key1838, -1), (key1770, -1), (key1786, -1), (key1422, -1), (key1453, -1), (key1389, -1), (key1453, -1), (key1389, -1), (key1422, -1), (key1571, 1), (key1653, 1), (key1544, 1), (key1653, 1), (key1544, 1), (key1571, 1)]

theorem rawRowCheck669 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form0 = rawRow669 := by decide +kernel

def row669 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

theorem rowCheck669 : row669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow669 := by decide +kernel

theorem rowEval669 (x : Key → ℝ) : Integer.Sparse.eval row669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck669, Integer.Sparse.eval_collectBalanced, rawRowCheck669]

def rawRow670 : Integer.Sparse Key := [(key1653, -2), (key1653, -2), (key1544, -2), (key1838, 1), (key1811, 1), (key1838, 1), (key1770, 1), (key1811, 1), (key1770, 1), (key1453, 2), (key1453, 2), (key1389, 2), (key1838, -1), (key1786, -1), (key1838, -1), (key1770, -1), (key1786, -1), (key1770, -1), (key1453, -1), (key1422, -1), (key1453, -1), (key1389, -1), (key1422, -1), (key1389, -1), (key1653, 1), (key1571, 1), (key1653, 1), (key1544, 1), (key1571, 1), (key1544, 1)]

theorem rawRowCheck670 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form0 = rawRow670 := by decide +kernel

def row670 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

theorem rowCheck670 : row670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow670 := by decide +kernel

theorem rowEval670 (x : Key → ℝ) : Integer.Sparse.eval row670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck670, Integer.Sparse.eval_collectBalanced, rawRowCheck670]

def rawRow671 : Integer.Sparse Key := [(key1314, -2), (key1811, -2), (key1811, -2), (key1335, 1), (key1335, 1), (key1653, 1), (key1653, 1), (key1838, 1), (key1838, 1), (key1294, 2), (key1786, 2), (key1786, 2), (key1335, -1), (key1335, -1), (key1453, -1), (key1453, -1), (key1838, -1), (key1838, -1), (key1294, -1), (key1294, -1), (key1571, -1), (key1571, -1), (key1786, -1), (key1786, -1), (key1314, 1), (key1314, 1), (key1422, 1), (key1422, 1), (key1811, 1), (key1811, 1)]

theorem rawRowCheck671 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form0 = rawRow671 := by decide +kernel

def row671 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

theorem rowCheck671 : row671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow671 := by decide +kernel

theorem rowEval671 (x : Key → ℝ) : Integer.Sparse.eval row671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck671, Integer.Sparse.eval_collectBalanced, rawRowCheck671]

end MUB6.Certificate.GramRows

end OAI
