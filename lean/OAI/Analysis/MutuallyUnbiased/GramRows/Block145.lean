import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15488 : Integer.Sparse Key := [(key2390, 2), (key2378, 2), (key2394, 2), (key2378, -2), (key2394, -2), (key2383, -2), (key2887, 2), (key2843, 2), (key2889, 2), (key2843, -1), (key2889, -1), (key2766, -1), (key2910, -1), (key2772, -1), (key2880, -1), (key2966, -2), (key2995, -2), (key2968, -2), (key2966, -1), (key2995, -1), (key2929, -1), (key3002, -1), (key2931, -1), (key2989, -1), (key2968, 4), (key2931, 4), (key2989, 4)]

theorem rawRowCheck15488 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form12 = rawRow15488 := by decide +kernel

def row15488 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

theorem rowCheck15488 : row15488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15488 := by decide +kernel

theorem rowEval15488 (x : Key → ℝ) : Integer.Sparse.eval row15488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15488, Integer.Sparse.eval_collectBalanced, rawRowCheck15488]

def rawRow15489 : Integer.Sparse Key := [(key2390, 2), (key2394, 2), (key2378, 2), (key2394, -2), (key2378, -2), (key2383, -2), (key2887, 2), (key2889, 2), (key2843, 2), (key2889, -1), (key2843, -1), (key2910, -1), (key2766, -1), (key2880, -1), (key2772, -1), (key2995, -2), (key2966, -2), (key2968, -2), (key2995, -1), (key2966, -1), (key3002, -1), (key2929, -1), (key2989, -1), (key2931, -1), (key2968, 4), (key2989, 4), (key2931, 4)]

theorem rawRowCheck15489 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form12 = rawRow15489 := by decide +kernel

def row15489 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

theorem rowCheck15489 : row15489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15489 := by decide +kernel

theorem rowEval15489 (x : Key → ℝ) : Integer.Sparse.eval row15489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15489, Integer.Sparse.eval_collectBalanced, rawRowCheck15489]

def rawRow15490 : Integer.Sparse Key := [(key2394, 2), (key2378, 2), (key2390, 2), (key2383, -2), (key2394, -2), (key2378, -2), (key2889, 2), (key2843, 2), (key2887, 2), (key2880, -1), (key2910, -1), (key2772, -1), (key2889, -1), (key2766, -1), (key2843, -1), (key2968, -2), (key2995, -2), (key2966, -2), (key2989, -1), (key3002, -1), (key2931, -1), (key2995, -1), (key2929, -1), (key2966, -1), (key2989, 4), (key2931, 4), (key2968, 4)]

theorem rawRowCheck15490 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form12 = rawRow15490 := by decide +kernel

def row15490 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

theorem rowCheck15490 : row15490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15490 := by decide +kernel

theorem rowEval15490 (x : Key → ℝ) : Integer.Sparse.eval row15490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15490, Integer.Sparse.eval_collectBalanced, rawRowCheck15490]

def rawRow15491 : Integer.Sparse Key := [(key2394, 2), (key2390, 2), (key2378, 2), (key2394, -2), (key2383, -2), (key2378, -2), (key2889, 2), (key2887, 2), (key2843, 2), (key2910, -1), (key2880, -1), (key2889, -1), (key2772, -1), (key2843, -1), (key2766, -1), (key2995, -2), (key2968, -2), (key2966, -2), (key3002, -1), (key2989, -1), (key2995, -1), (key2931, -1), (key2966, -1), (key2929, -1), (key2989, 4), (key2968, 4), (key2931, 4)]

theorem rawRowCheck15491 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form12 = rawRow15491 := by decide +kernel

def row15491 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

theorem rowCheck15491 : row15491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15491 := by decide +kernel

theorem rowEval15491 (x : Key → ℝ) : Integer.Sparse.eval row15491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15491, Integer.Sparse.eval_collectBalanced, rawRowCheck15491]

def rawRow15492 : Integer.Sparse Key := [(key2406, 2), (key2406, 2), (key2411, 2), (key2437, -2), (key2443, -2), (key2443, -2), (key2587, 2), (key2587, 2), (key2593, 2), (key2966, -1), (key2968, -1), (key2966, -1), (key2989, -1), (key2968, -1), (key2989, -1), (key2598, -2), (key2600, -2), (key2600, -2), (key2887, -1), (key2889, -1), (key2887, -1), (key2910, -1), (key2889, -1), (key2910, -1), (key2995, 4), (key2995, 4), (key3002, 4)]

theorem rawRowCheck15492 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form12 = rawRow15492 := by decide +kernel

def row15492 : Integer.Sparse Key := [(key2406, 4), (key2411, 2), (key2437, -2), (key2443, -4), (key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2887, -2), (key2889, -2), (key2910, -2), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

theorem rowCheck15492 : row15492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15492 := by decide +kernel

theorem rowEval15492 (x : Key → ℝ) : Integer.Sparse.eval row15492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15492, Integer.Sparse.eval_collectBalanced, rawRowCheck15492]

def rawRow15493 : Integer.Sparse Key := [(key2406, 2), (key2411, 2), (key2406, 2), (key2443, -2), (key2437, -2), (key2443, -2), (key2587, 2), (key2593, 2), (key2587, 2), (key2968, -1), (key2966, -1), (key2989, -1), (key2966, -1), (key2989, -1), (key2968, -1), (key2600, -2), (key2598, -2), (key2600, -2), (key2889, -1), (key2887, -1), (key2910, -1), (key2887, -1), (key2910, -1), (key2889, -1), (key2995, 4), (key3002, 4), (key2995, 4)]

theorem rawRowCheck15493 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form12 = rawRow15493 := by decide +kernel

def row15493 : Integer.Sparse Key := [(key2406, 4), (key2411, 2), (key2437, -2), (key2443, -4), (key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2887, -2), (key2889, -2), (key2910, -2), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

theorem rowCheck15493 : row15493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15493 := by decide +kernel

theorem rowEval15493 (x : Key → ℝ) : Integer.Sparse.eval row15493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15493, Integer.Sparse.eval_collectBalanced, rawRowCheck15493]

def rawRow15494 : Integer.Sparse Key := [(key2411, 2), (key2406, 2), (key2406, 2), (key2443, -2), (key2443, -2), (key2437, -2), (key2593, 2), (key2587, 2), (key2587, 2), (key2989, -1), (key2989, -1), (key2968, -1), (key2968, -1), (key2966, -1), (key2966, -1), (key2600, -2), (key2600, -2), (key2598, -2), (key2910, -1), (key2910, -1), (key2889, -1), (key2889, -1), (key2887, -1), (key2887, -1), (key3002, 4), (key2995, 4), (key2995, 4)]

theorem rawRowCheck15494 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form12 = rawRow15494 := by decide +kernel

def row15494 : Integer.Sparse Key := [(key2406, 4), (key2411, 2), (key2437, -2), (key2443, -4), (key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2887, -2), (key2889, -2), (key2910, -2), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

theorem rowCheck15494 : row15494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15494 := by decide +kernel

theorem rowEval15494 (x : Key → ℝ) : Integer.Sparse.eval row15494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15494, Integer.Sparse.eval_collectBalanced, rawRowCheck15494]

def rawRow15495 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2406, -2), (key2411, -2), (key2443, -2), (key2843, 2), (key2966, 2), (key2968, 2), (key2587, -1), (key2593, -1), (key2843, -1), (key2880, -1), (key2968, -1), (key2989, -1), (key2887, -2), (key2889, -2), (key2995, -2), (key2598, -1), (key2600, -1), (key2887, -1), (key2910, -1), (key2995, -1), (key3002, -1), (key2600, 4), (key2889, 4), (key2910, 4)]

theorem rawRowCheck15495 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form12 = rawRow15495 := by decide +kernel

def row15495 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

theorem rowCheck15495 : row15495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15495 := by decide +kernel

theorem rowEval15495 (x : Key → ℝ) : Integer.Sparse.eval row15495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15495, Integer.Sparse.eval_collectBalanced, rawRowCheck15495]

def rawRow15496 : Integer.Sparse Key := [(key2406, 2), (key2443, 2), (key2437, 2), (key2411, -2), (key2406, -2), (key2443, -2), (key2843, 2), (key2968, 2), (key2966, 2), (key2593, -1), (key2587, -1), (key2880, -1), (key2843, -1), (key2989, -1), (key2968, -1), (key2889, -2), (key2887, -2), (key2995, -2), (key2600, -1), (key2598, -1), (key2910, -1), (key2887, -1), (key3002, -1), (key2995, -1), (key2600, 4), (key2910, 4), (key2889, 4)]

theorem rawRowCheck15496 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form12 = rawRow15496 := by decide +kernel

def row15496 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

theorem rowCheck15496 : row15496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15496 := by decide +kernel

theorem rowEval15496 (x : Key → ℝ) : Integer.Sparse.eval row15496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15496, Integer.Sparse.eval_collectBalanced, rawRowCheck15496]

def rawRow15497 : Integer.Sparse Key := [(key2437, 2), (key2406, 2), (key2443, 2), (key2406, -2), (key2443, -2), (key2411, -2), (key2966, 2), (key2843, 2), (key2968, 2), (key2843, -1), (key2968, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2887, -2), (key2995, -2), (key2889, -2), (key2887, -1), (key2995, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2889, 4), (key2600, 4), (key2910, 4)]

theorem rawRowCheck15497 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form12 = rawRow15497 := by decide +kernel

def row15497 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

theorem rowCheck15497 : row15497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15497 := by decide +kernel

theorem rowEval15497 (x : Key → ℝ) : Integer.Sparse.eval row15497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15497, Integer.Sparse.eval_collectBalanced, rawRowCheck15497]

def rawRow15498 : Integer.Sparse Key := [(key2437, 2), (key2443, 2), (key2406, 2), (key2443, -2), (key2406, -2), (key2411, -2), (key2966, 2), (key2968, 2), (key2843, 2), (key2968, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2880, -1), (key2593, -1), (key2995, -2), (key2887, -2), (key2889, -2), (key2995, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2910, -1), (key2600, -1), (key2889, 4), (key2910, 4), (key2600, 4)]

theorem rawRowCheck15498 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form12 = rawRow15498 := by decide +kernel

def row15498 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

theorem rowCheck15498 : row15498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15498 := by decide +kernel

theorem rowEval15498 (x : Key → ℝ) : Integer.Sparse.eval row15498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15498, Integer.Sparse.eval_collectBalanced, rawRowCheck15498]

def rawRow15499 : Integer.Sparse Key := [(key2443, 2), (key2406, 2), (key2437, 2), (key2411, -2), (key2443, -2), (key2406, -2), (key2968, 2), (key2843, 2), (key2966, 2), (key2880, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2587, -1), (key2843, -1), (key2889, -2), (key2995, -2), (key2887, -2), (key2910, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2598, -1), (key2887, -1), (key2910, 4), (key2600, 4), (key2889, 4)]

theorem rawRowCheck15499 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form12 = rawRow15499 := by decide +kernel

def row15499 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

theorem rowCheck15499 : row15499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15499 := by decide +kernel

theorem rowEval15499 (x : Key → ℝ) : Integer.Sparse.eval row15499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15499, Integer.Sparse.eval_collectBalanced, rawRowCheck15499]

def rawRow15500 : Integer.Sparse Key := [(key2443, 2), (key2437, 2), (key2406, 2), (key2443, -2), (key2411, -2), (key2406, -2), (key2968, 2), (key2966, 2), (key2843, 2), (key2989, -1), (key2880, -1), (key2968, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key2995, -2), (key2889, -2), (key2887, -2), (key3002, -1), (key2910, -1), (key2995, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2910, 4), (key2889, 4), (key2600, 4)]

theorem rawRowCheck15500 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form12 = rawRow15500 := by decide +kernel

def row15500 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

theorem rowCheck15500 : row15500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15500 := by decide +kernel

theorem rowEval15500 (x : Key → ℝ) : Integer.Sparse.eval row15500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15500, Integer.Sparse.eval_collectBalanced, rawRowCheck15500]

def rawRow15501 : Integer.Sparse Key := [(key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2378, 2), (key2390, 2), (key2394, 2), (key2929, -1), (key2931, -1), (key2966, -1), (key2989, -1), (key2995, -1), (key3002, -1), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2931, 4), (key2968, 4), (key2989, 4)]

theorem rawRowCheck15501 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form12 = rawRow15501 := by decide +kernel

def row15501 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

theorem rowCheck15501 : row15501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15501 := by decide +kernel

theorem rowEval15501 (x : Key → ℝ) : Integer.Sparse.eval row15501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15501, Integer.Sparse.eval_collectBalanced, rawRowCheck15501]

def rawRow15502 : Integer.Sparse Key := [(key2472, 2), (key2484, 2), (key2480, 2), (key2509, -2), (key2503, -2), (key2524, -2), (key2378, 2), (key2394, 2), (key2390, 2), (key2931, -1), (key2929, -1), (key2989, -1), (key2966, -1), (key3002, -1), (key2995, -1), (key2593, -2), (key2587, -2), (key2600, -2), (key2772, -1), (key2766, -1), (key2880, -1), (key2843, -1), (key2910, -1), (key2889, -1), (key2931, 4), (key2989, 4), (key2968, 4)]

theorem rawRowCheck15502 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form12 = rawRow15502 := by decide +kernel

def row15502 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

theorem rowCheck15502 : row15502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15502 := by decide +kernel

theorem rowEval15502 (x : Key → ℝ) : Integer.Sparse.eval row15502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15502, Integer.Sparse.eval_collectBalanced, rawRowCheck15502]

def rawRow15503 : Integer.Sparse Key := [(key2480, 2), (key2472, 2), (key2484, 2), (key2503, -2), (key2524, -2), (key2509, -2), (key2390, 2), (key2378, 2), (key2394, 2), (key2966, -1), (key2995, -1), (key2929, -1), (key3002, -1), (key2931, -1), (key2989, -1), (key2587, -2), (key2600, -2), (key2593, -2), (key2843, -1), (key2889, -1), (key2766, -1), (key2910, -1), (key2772, -1), (key2880, -1), (key2968, 4), (key2931, 4), (key2989, 4)]

theorem rawRowCheck15503 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form12 = rawRow15503 := by decide +kernel

def row15503 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

theorem rowCheck15503 : row15503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15503 := by decide +kernel

theorem rowEval15503 (x : Key → ℝ) : Integer.Sparse.eval row15503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15503, Integer.Sparse.eval_collectBalanced, rawRowCheck15503]

def rawRow15504 : Integer.Sparse Key := [(key2480, 2), (key2484, 2), (key2472, 2), (key2524, -2), (key2503, -2), (key2509, -2), (key2390, 2), (key2394, 2), (key2378, 2), (key2995, -1), (key2966, -1), (key3002, -1), (key2929, -1), (key2989, -1), (key2931, -1), (key2600, -2), (key2587, -2), (key2593, -2), (key2889, -1), (key2843, -1), (key2910, -1), (key2766, -1), (key2880, -1), (key2772, -1), (key2968, 4), (key2989, 4), (key2931, 4)]

theorem rawRowCheck15504 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form12 = rawRow15504 := by decide +kernel

def row15504 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

theorem rowCheck15504 : row15504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15504 := by decide +kernel

theorem rowEval15504 (x : Key → ℝ) : Integer.Sparse.eval row15504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15504, Integer.Sparse.eval_collectBalanced, rawRowCheck15504]

def rawRow15505 : Integer.Sparse Key := [(key2484, 2), (key2472, 2), (key2480, 2), (key2509, -2), (key2524, -2), (key2503, -2), (key2394, 2), (key2378, 2), (key2390, 2), (key2989, -1), (key3002, -1), (key2931, -1), (key2995, -1), (key2929, -1), (key2966, -1), (key2593, -2), (key2600, -2), (key2587, -2), (key2880, -1), (key2910, -1), (key2772, -1), (key2889, -1), (key2766, -1), (key2843, -1), (key2989, 4), (key2931, 4), (key2968, 4)]

theorem rawRowCheck15505 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form12 = rawRow15505 := by decide +kernel

def row15505 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

theorem rowCheck15505 : row15505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15505 := by decide +kernel

theorem rowEval15505 (x : Key → ℝ) : Integer.Sparse.eval row15505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15505, Integer.Sparse.eval_collectBalanced, rawRowCheck15505]

def rawRow15506 : Integer.Sparse Key := [(key2484, 2), (key2480, 2), (key2472, 2), (key2524, -2), (key2509, -2), (key2503, -2), (key2394, 2), (key2390, 2), (key2378, 2), (key3002, -1), (key2989, -1), (key2995, -1), (key2931, -1), (key2966, -1), (key2929, -1), (key2600, -2), (key2593, -2), (key2587, -2), (key2910, -1), (key2880, -1), (key2889, -1), (key2772, -1), (key2843, -1), (key2766, -1), (key2989, 4), (key2968, 4), (key2931, 4)]

theorem rawRowCheck15506 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form12 = rawRow15506 := by decide +kernel

def row15506 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

theorem rowCheck15506 : row15506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15506 := by decide +kernel

theorem rowEval15506 (x : Key → ℝ) : Integer.Sparse.eval row15506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15506, Integer.Sparse.eval_collectBalanced, rawRowCheck15506]

def rawRow15507 : Integer.Sparse Key := [(key2472, 2), (key2503, 2), (key2509, 2), (key2480, -2), (key2484, -2), (key2524, -2), (key2406, 2), (key2437, 2), (key2443, 2), (key2598, -1), (key2600, -1), (key2887, -1), (key2910, -1), (key2995, -1), (key3002, -1), (key2766, -2), (key2772, -2), (key2931, -2), (key2587, -1), (key2593, -1), (key2843, -1), (key2880, -1), (key2968, -1), (key2989, -1), (key2600, 4), (key2889, 4), (key2910, 4)]

theorem rawRowCheck15507 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form12 = rawRow15507 := by decide +kernel

def row15507 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

theorem rowCheck15507 : row15507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15507 := by decide +kernel

theorem rowEval15507 (x : Key → ℝ) : Integer.Sparse.eval row15507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15507, Integer.Sparse.eval_collectBalanced, rawRowCheck15507]

def rawRow15508 : Integer.Sparse Key := [(key2472, 2), (key2509, 2), (key2503, 2), (key2484, -2), (key2480, -2), (key2524, -2), (key2406, 2), (key2443, 2), (key2437, 2), (key2600, -1), (key2598, -1), (key2910, -1), (key2887, -1), (key3002, -1), (key2995, -1), (key2772, -2), (key2766, -2), (key2931, -2), (key2593, -1), (key2587, -1), (key2880, -1), (key2843, -1), (key2989, -1), (key2968, -1), (key2600, 4), (key2910, 4), (key2889, 4)]

theorem rawRowCheck15508 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form12 = rawRow15508 := by decide +kernel

def row15508 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

theorem rowCheck15508 : row15508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15508 := by decide +kernel

theorem rowEval15508 (x : Key → ℝ) : Integer.Sparse.eval row15508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15508, Integer.Sparse.eval_collectBalanced, rawRowCheck15508]

def rawRow15509 : Integer.Sparse Key := [(key2503, 2), (key2472, 2), (key2509, 2), (key2480, -2), (key2524, -2), (key2484, -2), (key2437, 2), (key2406, 2), (key2443, 2), (key2887, -1), (key2995, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2766, -2), (key2931, -2), (key2772, -2), (key2843, -1), (key2968, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2889, 4), (key2600, 4), (key2910, 4)]

theorem rawRowCheck15509 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form12 = rawRow15509 := by decide +kernel

def row15509 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

theorem rowCheck15509 : row15509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15509 := by decide +kernel

theorem rowEval15509 (x : Key → ℝ) : Integer.Sparse.eval row15509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15509, Integer.Sparse.eval_collectBalanced, rawRowCheck15509]

def rawRow15510 : Integer.Sparse Key := [(key2503, 2), (key2509, 2), (key2472, 2), (key2524, -2), (key2480, -2), (key2484, -2), (key2437, 2), (key2443, 2), (key2406, 2), (key2995, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2910, -1), (key2600, -1), (key2931, -2), (key2766, -2), (key2772, -2), (key2968, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2880, -1), (key2593, -1), (key2889, 4), (key2910, 4), (key2600, 4)]

theorem rawRowCheck15510 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form12 = rawRow15510 := by decide +kernel

def row15510 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

theorem rowCheck15510 : row15510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15510 := by decide +kernel

theorem rowEval15510 (x : Key → ℝ) : Integer.Sparse.eval row15510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15510, Integer.Sparse.eval_collectBalanced, rawRowCheck15510]

def rawRow15511 : Integer.Sparse Key := [(key2509, 2), (key2472, 2), (key2503, 2), (key2484, -2), (key2524, -2), (key2480, -2), (key2443, 2), (key2406, 2), (key2437, 2), (key2910, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2598, -1), (key2887, -1), (key2772, -2), (key2931, -2), (key2766, -2), (key2880, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2587, -1), (key2843, -1), (key2910, 4), (key2600, 4), (key2889, 4)]

theorem rawRowCheck15511 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form12 = rawRow15511 := by decide +kernel

def row15511 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

theorem rowCheck15511 : row15511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15511 := by decide +kernel

theorem rowEval15511 (x : Key → ℝ) : Integer.Sparse.eval row15511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15511, Integer.Sparse.eval_collectBalanced, rawRowCheck15511]

def rawRow15512 : Integer.Sparse Key := [(key2509, 2), (key2503, 2), (key2472, 2), (key2524, -2), (key2484, -2), (key2480, -2), (key2443, 2), (key2437, 2), (key2406, 2), (key3002, -1), (key2910, -1), (key2995, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2931, -2), (key2772, -2), (key2766, -2), (key2989, -1), (key2880, -1), (key2968, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key2910, 4), (key2889, 4), (key2600, 4)]

theorem rawRowCheck15512 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form12 = rawRow15512 := by decide +kernel

def row15512 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

theorem rowCheck15512 : row15512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15512 := by decide +kernel

theorem rowEval15512 (x : Key → ℝ) : Integer.Sparse.eval row15512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15512, Integer.Sparse.eval_collectBalanced, rawRowCheck15512]

def rawRow15513 : Integer.Sparse Key := [(key2480, 2), (key2503, 2), (key2524, 2), (key2472, -2), (key2484, -2), (key2509, -2), (key2480, 2), (key2503, 2), (key2524, 2), (key2587, -1), (key2600, -1), (key2766, -1), (key2910, -1), (key2931, -1), (key2989, -1), (key2843, -2), (key2889, -2), (key2968, -2), (key2587, -1), (key2600, -1), (key2766, -1), (key2910, -1), (key2931, -1), (key2989, -1), (key2593, 4), (key2772, 4), (key2880, 4)]

theorem rawRowCheck15513 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form12 = rawRow15513 := by decide +kernel

def row15513 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

theorem rowCheck15513 : row15513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15513 := by decide +kernel

theorem rowEval15513 (x : Key → ℝ) : Integer.Sparse.eval row15513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15513, Integer.Sparse.eval_collectBalanced, rawRowCheck15513]

def rawRow15514 : Integer.Sparse Key := [(key2480, 2), (key2524, 2), (key2503, 2), (key2484, -2), (key2472, -2), (key2509, -2), (key2480, 2), (key2524, 2), (key2503, 2), (key2600, -1), (key2587, -1), (key2910, -1), (key2766, -1), (key2989, -1), (key2931, -1), (key2889, -2), (key2843, -2), (key2968, -2), (key2600, -1), (key2587, -1), (key2910, -1), (key2766, -1), (key2989, -1), (key2931, -1), (key2593, 4), (key2880, 4), (key2772, 4)]

theorem rawRowCheck15514 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form12 = rawRow15514 := by decide +kernel

def row15514 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

theorem rowCheck15514 : row15514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15514 := by decide +kernel

theorem rowEval15514 (x : Key → ℝ) : Integer.Sparse.eval row15514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15514, Integer.Sparse.eval_collectBalanced, rawRowCheck15514]

def rawRow15515 : Integer.Sparse Key := [(key2503, 2), (key2480, 2), (key2524, 2), (key2472, -2), (key2509, -2), (key2484, -2), (key2503, 2), (key2480, 2), (key2524, 2), (key2766, -1), (key2931, -1), (key2587, -1), (key2989, -1), (key2600, -1), (key2910, -1), (key2843, -2), (key2968, -2), (key2889, -2), (key2766, -1), (key2931, -1), (key2587, -1), (key2989, -1), (key2600, -1), (key2910, -1), (key2772, 4), (key2593, 4), (key2880, 4)]

theorem rawRowCheck15515 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form12 = rawRow15515 := by decide +kernel

def row15515 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

theorem rowCheck15515 : row15515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15515 := by decide +kernel

theorem rowEval15515 (x : Key → ℝ) : Integer.Sparse.eval row15515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15515, Integer.Sparse.eval_collectBalanced, rawRowCheck15515]

def rawRow15516 : Integer.Sparse Key := [(key2503, 2), (key2524, 2), (key2480, 2), (key2509, -2), (key2472, -2), (key2484, -2), (key2503, 2), (key2524, 2), (key2480, 2), (key2931, -1), (key2766, -1), (key2989, -1), (key2587, -1), (key2910, -1), (key2600, -1), (key2968, -2), (key2843, -2), (key2889, -2), (key2931, -1), (key2766, -1), (key2989, -1), (key2587, -1), (key2910, -1), (key2600, -1), (key2772, 4), (key2880, 4), (key2593, 4)]

theorem rawRowCheck15516 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form12 = rawRow15516 := by decide +kernel

def row15516 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

theorem rowCheck15516 : row15516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15516 := by decide +kernel

theorem rowEval15516 (x : Key → ℝ) : Integer.Sparse.eval row15516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15516, Integer.Sparse.eval_collectBalanced, rawRowCheck15516]

def rawRow15517 : Integer.Sparse Key := [(key2524, 2), (key2480, 2), (key2503, 2), (key2484, -2), (key2509, -2), (key2472, -2), (key2524, 2), (key2480, 2), (key2503, 2), (key2910, -1), (key2989, -1), (key2600, -1), (key2931, -1), (key2587, -1), (key2766, -1), (key2889, -2), (key2968, -2), (key2843, -2), (key2910, -1), (key2989, -1), (key2600, -1), (key2931, -1), (key2587, -1), (key2766, -1), (key2880, 4), (key2593, 4), (key2772, 4)]

theorem rawRowCheck15517 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form12 = rawRow15517 := by decide +kernel

def row15517 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

theorem rowCheck15517 : row15517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15517 := by decide +kernel

theorem rowEval15517 (x : Key → ℝ) : Integer.Sparse.eval row15517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15517, Integer.Sparse.eval_collectBalanced, rawRowCheck15517]

def rawRow15518 : Integer.Sparse Key := [(key2524, 2), (key2503, 2), (key2480, 2), (key2509, -2), (key2484, -2), (key2472, -2), (key2524, 2), (key2503, 2), (key2480, 2), (key2989, -1), (key2910, -1), (key2931, -1), (key2600, -1), (key2766, -1), (key2587, -1), (key2968, -2), (key2889, -2), (key2843, -2), (key2989, -1), (key2910, -1), (key2931, -1), (key2600, -1), (key2766, -1), (key2587, -1), (key2880, 4), (key2772, 4), (key2593, 4)]

theorem rawRowCheck15518 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form12 = rawRow15518 := by decide +kernel

def row15518 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

theorem rowCheck15518 : row15518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15518 := by decide +kernel

theorem rowEval15518 (x : Key → ℝ) : Integer.Sparse.eval row15518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15518, Integer.Sparse.eval_collectBalanced, rawRowCheck15518]

def rawRow15519 : Integer.Sparse Key := [(key2608, 2), (key2614, 2), (key2614, 2), (key2624, -1), (key2630, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2638, -1), (key2663, 2), (key2669, 2), (key2669, 2), (key2698, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2778, -1), (key2784, -1), (key2778, -1), (key2792, -1), (key2784, -1), (key2792, -1), (key2801, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2)]

theorem rawRowCheck15519 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form13 = rawRow15519 := by decide +kernel

def row15519 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

theorem rowCheck15519 : row15519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15519 := by decide +kernel

theorem rowEval15519 (x : Key → ℝ) : Integer.Sparse.eval row15519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15519, Integer.Sparse.eval_collectBalanced, rawRowCheck15519]

def rawRow15520 : Integer.Sparse Key := [(key2614, 2), (key2608, 2), (key2614, 2), (key2630, -1), (key2624, -1), (key2638, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2669, 2), (key2663, 2), (key2669, 2), (key2704, -1), (key2698, -1), (key2724, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2784, -1), (key2778, -1), (key2792, -1), (key2778, -1), (key2792, -1), (key2784, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2)]

theorem rawRowCheck15520 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form13 = rawRow15520 := by decide +kernel

def row15520 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

theorem rowCheck15520 : row15520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15520 := by decide +kernel

theorem rowEval15520 (x : Key → ℝ) : Integer.Sparse.eval row15520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15520, Integer.Sparse.eval_collectBalanced, rawRowCheck15520]

def rawRow15521 : Integer.Sparse Key := [(key2614, 2), (key2614, 2), (key2608, 2), (key2638, -1), (key2638, -1), (key2630, -1), (key2630, -1), (key2624, -1), (key2624, -1), (key2669, 2), (key2669, 2), (key2663, 2), (key2724, -1), (key2724, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2792, -1), (key2792, -1), (key2784, -1), (key2784, -1), (key2778, -1), (key2778, -1), (key2827, -1), (key2827, -1), (key2807, -1), (key2807, -1), (key2801, -1), (key2801, -1), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2)]

theorem rawRowCheck15521 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form13 = rawRow15521 := by decide +kernel

def row15521 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

theorem rowCheck15521 : row15521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15521 := by decide +kernel

theorem rowEval15521 (x : Key → ℝ) : Integer.Sparse.eval row15521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15521, Integer.Sparse.eval_collectBalanced, rawRowCheck15521]

def rawRow15522 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2608, -1), (key2614, -1), (key2624, -1), (key2638, -1), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, 2), (key2752, 2), (key2663, -1), (key2669, -1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, -1), (key2851, -1), (key2858, -1), (key2918, -1), (key2919, -1), (key2778, -1), (key2784, -1), (key2851, -1), (key2868, -1), (key2918, -1), (key2922, -1), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2)]

theorem rawRowCheck15522 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form13 = rawRow15522 := by decide +kernel

def row15522 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

theorem rowCheck15522 : row15522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15522 := by decide +kernel

theorem rowEval15522 (x : Key → ℝ) : Integer.Sparse.eval row15522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15522, Integer.Sparse.eval_collectBalanced, rawRowCheck15522]

def rawRow15523 : Integer.Sparse Key := [(key2630, 2), (key2624, 2), (key2638, 2), (key2614, -1), (key2608, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2657, -1), (key2704, 2), (key2698, 2), (key2752, 2), (key2669, -1), (key2663, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2752, -1), (key2807, -1), (key2801, -1), (key2858, -1), (key2851, -1), (key2919, -1), (key2918, -1), (key2784, -1), (key2778, -1), (key2868, -1), (key2851, -1), (key2922, -1), (key2918, -1), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2)]

theorem rawRowCheck15523 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form13 = rawRow15523 := by decide +kernel

def row15523 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

theorem rowCheck15523 : row15523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15523 := by decide +kernel

theorem rowEval15523 (x : Key → ℝ) : Integer.Sparse.eval row15523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15523, Integer.Sparse.eval_collectBalanced, rawRowCheck15523]

def rawRow15524 : Integer.Sparse Key := [(key2624, 2), (key2638, 2), (key2630, 2), (key2624, -1), (key2638, -1), (key2608, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2698, 2), (key2752, 2), (key2704, 2), (key2698, -1), (key2752, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2851, -1), (key2918, -1), (key2801, -1), (key2919, -1), (key2807, -1), (key2858, -1), (key2851, -1), (key2918, -1), (key2778, -1), (key2922, -1), (key2784, -1), (key2868, -1), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2)]

theorem rawRowCheck15524 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form13 = rawRow15524 := by decide +kernel

def row15524 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

theorem rowCheck15524 : row15524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15524 := by decide +kernel

theorem rowEval15524 (x : Key → ℝ) : Integer.Sparse.eval row15524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15524, Integer.Sparse.eval_collectBalanced, rawRowCheck15524]

def rawRow15525 : Integer.Sparse Key := [(key2638, 2), (key2624, 2), (key2630, 2), (key2638, -1), (key2624, -1), (key2659, -1), (key2608, -1), (key2638, -1), (key2614, -1), (key2752, 2), (key2698, 2), (key2704, 2), (key2752, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2724, -1), (key2669, -1), (key2918, -1), (key2851, -1), (key2919, -1), (key2801, -1), (key2858, -1), (key2807, -1), (key2918, -1), (key2851, -1), (key2922, -1), (key2778, -1), (key2868, -1), (key2784, -1), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2)]

theorem rawRowCheck15525 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form13 = rawRow15525 := by decide +kernel

def row15525 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

theorem rowCheck15525 : row15525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15525 := by decide +kernel

theorem rowEval15525 (x : Key → ℝ) : Integer.Sparse.eval row15525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck15525, Integer.Sparse.eval_collectBalanced, rawRowCheck15525]

def rawRow15526 : Integer.Sparse Key := [(key2630, 2), (key2638, 2), (key2624, 2), (key2657, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2608, -1), (key2624, -1), (key2704, 2), (key2752, 2), (key2698, 2), (key2724, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2663, -1), (key2698, -1), (key2858, -1), (key2919, -1), (key2807, -1), (key2918, -1), (key2801, -1), (key2851, -1), (key2868, -1), (key2922, -1), (key2784, -1), (key2918, -1), (key2778, -1), (key2851, -1), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2)]

theorem rawRowCheck15526 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form13 = rawRow15526 := by decide +kernel

def row15526 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

theorem rowCheck15526 : row15526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15526 := by decide +kernel

theorem rowEval15526 (x : Key → ℝ) : Integer.Sparse.eval row15526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15526, Integer.Sparse.eval_collectBalanced, rawRowCheck15526]

def rawRow15527 : Integer.Sparse Key := [(key2638, 2), (key2630, 2), (key2624, 2), (key2659, -1), (key2657, -1), (key2638, -1), (key2614, -1), (key2624, -1), (key2608, -1), (key2752, 2), (key2704, 2), (key2698, 2), (key2757, -1), (key2724, -1), (key2752, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2919, -1), (key2858, -1), (key2918, -1), (key2807, -1), (key2851, -1), (key2801, -1), (key2922, -1), (key2868, -1), (key2918, -1), (key2784, -1), (key2851, -1), (key2778, -1), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2)]

theorem rawRowCheck15527 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form13 = rawRow15527 := by decide +kernel

def row15527 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

theorem rowCheck15527 : row15527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15527 := by decide +kernel

theorem rowEval15527 (x : Key → ℝ) : Integer.Sparse.eval row15527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck15527, Integer.Sparse.eval_collectBalanced, rawRowCheck15527]

def rawRow15528 : Integer.Sparse Key := [(key2663, 2), (key2669, 2), (key2669, 2), (key2698, -1), (key2704, -1), (key2698, -1), (key2752, -1), (key2704, -1), (key2752, -1), (key2608, 2), (key2614, 2), (key2614, 2), (key2801, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key2624, -1), (key2630, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2638, -1), (key2698, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2)]

theorem rawRowCheck15528 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form13 = rawRow15528 := by decide +kernel

def row15528 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -4), (key2704, -4), (key2724, -2), (key2752, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

theorem rowCheck15528 : row15528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15528 := by decide +kernel

theorem rowEval15528 (x : Key → ℝ) : Integer.Sparse.eval row15528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15528, Integer.Sparse.eval_collectBalanced, rawRowCheck15528]

def rawRow15529 : Integer.Sparse Key := [(key2669, 2), (key2663, 2), (key2669, 2), (key2704, -1), (key2698, -1), (key2752, -1), (key2698, -1), (key2752, -1), (key2704, -1), (key2614, 2), (key2608, 2), (key2614, 2), (key2807, -1), (key2801, -1), (key2827, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2630, -1), (key2624, -1), (key2638, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2)]

theorem rawRowCheck15529 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form13 = rawRow15529 := by decide +kernel

def row15529 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -4), (key2704, -4), (key2724, -2), (key2752, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

theorem rowCheck15529 : row15529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15529 := by decide +kernel

theorem rowEval15529 (x : Key → ℝ) : Integer.Sparse.eval row15529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15529, Integer.Sparse.eval_collectBalanced, rawRowCheck15529]

def rawRow15530 : Integer.Sparse Key := [(key2669, 2), (key2669, 2), (key2663, 2), (key2752, -1), (key2752, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2614, 2), (key2614, 2), (key2608, 2), (key2827, -1), (key2827, -1), (key2807, -1), (key2807, -1), (key2801, -1), (key2801, -1), (key2638, -1), (key2638, -1), (key2630, -1), (key2630, -1), (key2624, -1), (key2624, -1), (key2724, -1), (key2724, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2)]

theorem rawRowCheck15530 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form13 = rawRow15530 := by decide +kernel

def row15530 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -4), (key2704, -4), (key2724, -2), (key2752, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

theorem rowCheck15530 : row15530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15530 := by decide +kernel

theorem rowEval15530 (x : Key → ℝ) : Integer.Sparse.eval row15530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15530, Integer.Sparse.eval_collectBalanced, rawRowCheck15530]

def rawRow15531 : Integer.Sparse Key := [(key2698, 2), (key2704, 2), (key2724, 2), (key2663, -1), (key2669, -1), (key2698, -1), (key2752, -1), (key2724, -1), (key2757, -1), (key2801, 2), (key2807, 2), (key2827, 2), (key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2698, -1), (key2704, -1), (key2851, -1), (key2858, -1), (key3021, -1), (key3022, -1), (key2624, -1), (key2630, -1), (key2851, -1), (key2868, -1), (key3021, -1), (key3025, -1), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2)]

theorem rawRowCheck15531 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form13 = rawRow15531 := by decide +kernel

def row15531 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2858, -1), (key2868, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck15531 : row15531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15531 := by decide +kernel

theorem rowEval15531 (x : Key → ℝ) : Integer.Sparse.eval row15531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15531, Integer.Sparse.eval_collectBalanced, rawRowCheck15531]

def rawRow15532 : Integer.Sparse Key := [(key2704, 2), (key2698, 2), (key2724, 2), (key2669, -1), (key2663, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2724, -1), (key2807, 2), (key2801, 2), (key2827, 2), (key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2704, -1), (key2698, -1), (key2858, -1), (key2851, -1), (key3022, -1), (key3021, -1), (key2630, -1), (key2624, -1), (key2868, -1), (key2851, -1), (key3025, -1), (key3021, -1), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2)]

theorem rawRowCheck15532 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form13 = rawRow15532 := by decide +kernel

def row15532 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2858, -1), (key2868, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck15532 : row15532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15532 := by decide +kernel

theorem rowEval15532 (x : Key → ℝ) : Integer.Sparse.eval row15532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15532, Integer.Sparse.eval_collectBalanced, rawRowCheck15532]

def rawRow15533 : Integer.Sparse Key := [(key2698, 2), (key2724, 2), (key2704, 2), (key2698, -1), (key2724, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2801, 2), (key2827, 2), (key2807, 2), (key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2851, -1), (key3021, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2851, -1), (key3021, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2)]

theorem rawRowCheck15533 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form13 = rawRow15533 := by decide +kernel

def row15533 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck15533 : row15533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15533 := by decide +kernel

theorem rowEval15533 (x : Key → ℝ) : Integer.Sparse.eval row15533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15533, Integer.Sparse.eval_collectBalanced, rawRowCheck15533]

def rawRow15534 : Integer.Sparse Key := [(key2724, 2), (key2698, 2), (key2704, 2), (key2724, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2752, -1), (key2669, -1), (key2827, 2), (key2801, 2), (key2807, 2), (key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key3021, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key2858, -1), (key2704, -1), (key3021, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key2868, -1), (key2630, -1), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2)]

theorem rawRowCheck15534 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form13 = rawRow15534 := by decide +kernel

def row15534 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck15534 : row15534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15534 := by decide +kernel

theorem rowEval15534 (x : Key → ℝ) : Integer.Sparse.eval row15534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15534, Integer.Sparse.eval_collectBalanced, rawRowCheck15534]

def rawRow15535 : Integer.Sparse Key := [(key2704, 2), (key2724, 2), (key2698, 2), (key2752, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2663, -1), (key2698, -1), (key2807, 2), (key2827, 2), (key2801, 2), (key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2858, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2698, -1), (key2851, -1), (key2868, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2624, -1), (key2851, -1), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2)]

theorem rawRowCheck15535 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form13 = rawRow15535 := by decide +kernel

def row15535 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2858, -1), (key2868, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck15535 : row15535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15535 := by decide +kernel

theorem rowEval15535 (x : Key → ℝ) : Integer.Sparse.eval row15535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15535, Integer.Sparse.eval_collectBalanced, rawRowCheck15535]

def rawRow15536 : Integer.Sparse Key := [(key2724, 2), (key2704, 2), (key2698, 2), (key2757, -1), (key2752, -1), (key2724, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2827, 2), (key2807, 2), (key2801, 2), (key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key3022, -1), (key2858, -1), (key3021, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key3025, -1), (key2868, -1), (key3021, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2)]

theorem rawRowCheck15536 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form13 = rawRow15536 := by decide +kernel

def row15536 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2858, -1), (key2868, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck15536 : row15536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15536 := by decide +kernel

theorem rowEval15536 (x : Key → ℝ) : Integer.Sparse.eval row15536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15536, Integer.Sparse.eval_collectBalanced, rawRowCheck15536]

def rawRow15537 : Integer.Sparse Key := [(key2778, 2), (key2784, 2), (key2792, 2), (key2801, -1), (key2807, -1), (key2851, -1), (key2918, -1), (key2858, -1), (key2919, -1), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, -1), (key2704, -1), (key2851, -1), (key3021, -1), (key2858, -1), (key3022, -1), (key2608, -1), (key2614, -1), (key2624, -1), (key2638, -1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2)]

theorem rawRowCheck15537 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form13 = rawRow15537 := by decide +kernel

def row15537 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

theorem rowCheck15537 : row15537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15537 := by decide +kernel

theorem rowEval15537 (x : Key → ℝ) : Integer.Sparse.eval row15537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15537, Integer.Sparse.eval_collectBalanced, rawRowCheck15537]

def rawRow15538 : Integer.Sparse Key := [(key2784, 2), (key2778, 2), (key2792, 2), (key2807, -1), (key2801, -1), (key2918, -1), (key2851, -1), (key2919, -1), (key2858, -1), (key2630, 2), (key2624, 2), (key2638, 2), (key2704, -1), (key2698, -1), (key3021, -1), (key2851, -1), (key3022, -1), (key2858, -1), (key2614, -1), (key2608, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2657, -1), (key2669, -1), (key2663, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2752, -1), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2)]

theorem rawRowCheck15538 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form13 = rawRow15538 := by decide +kernel

def row15538 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

theorem rowCheck15538 : row15538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15538 := by decide +kernel

theorem rowEval15538 (x : Key → ℝ) : Integer.Sparse.eval row15538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15538, Integer.Sparse.eval_collectBalanced, rawRowCheck15538]

def rawRow15539 : Integer.Sparse Key := [(key2778, 2), (key2792, 2), (key2784, 2), (key2851, -1), (key2858, -1), (key2801, -1), (key2919, -1), (key2807, -1), (key2918, -1), (key2624, 2), (key2638, 2), (key2630, 2), (key2851, -1), (key2858, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2624, -1), (key2638, -1), (key2608, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2698, -1), (key2752, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2)]

theorem rawRowCheck15539 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form13 = rawRow15539 := by decide +kernel

def row15539 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

theorem rowCheck15539 : row15539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15539 := by decide +kernel

theorem rowEval15539 (x : Key → ℝ) : Integer.Sparse.eval row15539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15539, Integer.Sparse.eval_collectBalanced, rawRowCheck15539]

def rawRow15540 : Integer.Sparse Key := [(key2792, 2), (key2778, 2), (key2784, 2), (key2858, -1), (key2851, -1), (key2919, -1), (key2801, -1), (key2918, -1), (key2807, -1), (key2638, 2), (key2624, 2), (key2630, 2), (key2858, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key3021, -1), (key2704, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2608, -1), (key2638, -1), (key2614, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2724, -1), (key2669, -1), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2)]

theorem rawRowCheck15540 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form13 = rawRow15540 := by decide +kernel

def row15540 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

theorem rowCheck15540 : row15540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15540 := by decide +kernel

theorem rowEval15540 (x : Key → ℝ) : Integer.Sparse.eval row15540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck15540, Integer.Sparse.eval_collectBalanced, rawRowCheck15540]

def rawRow15541 : Integer.Sparse Key := [(key2784, 2), (key2792, 2), (key2778, 2), (key2918, -1), (key2919, -1), (key2807, -1), (key2858, -1), (key2801, -1), (key2851, -1), (key2630, 2), (key2638, 2), (key2624, 2), (key3021, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2698, -1), (key2851, -1), (key2657, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2608, -1), (key2624, -1), (key2724, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2663, -1), (key2698, -1), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2)]

theorem rawRowCheck15541 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form13 = rawRow15541 := by decide +kernel

def row15541 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

theorem rowCheck15541 : row15541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15541 := by decide +kernel

theorem rowEval15541 (x : Key → ℝ) : Integer.Sparse.eval row15541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15541, Integer.Sparse.eval_collectBalanced, rawRowCheck15541]

def rawRow15542 : Integer.Sparse Key := [(key2792, 2), (key2784, 2), (key2778, 2), (key2919, -1), (key2918, -1), (key2858, -1), (key2807, -1), (key2851, -1), (key2801, -1), (key2638, 2), (key2630, 2), (key2624, 2), (key3022, -1), (key3021, -1), (key2858, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key2659, -1), (key2657, -1), (key2638, -1), (key2614, -1), (key2624, -1), (key2608, -1), (key2757, -1), (key2724, -1), (key2752, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2)]

theorem rawRowCheck15542 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form13 = rawRow15542 := by decide +kernel

def row15542 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

theorem rowCheck15542 : row15542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15542 := by decide +kernel

theorem rowEval15542 (x : Key → ℝ) : Integer.Sparse.eval row15542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck15542, Integer.Sparse.eval_collectBalanced, rawRowCheck15542]

def rawRow15543 : Integer.Sparse Key := [(key2801, 2), (key2807, 2), (key2827, 2), (key2778, -1), (key2784, -1), (key2851, -1), (key2918, -1), (key2868, -1), (key2922, -1), (key2698, 2), (key2704, 2), (key2724, 2), (key2624, -1), (key2630, -1), (key2851, -1), (key3021, -1), (key2868, -1), (key3025, -1), (key2663, -1), (key2669, -1), (key2698, -1), (key2752, -1), (key2724, -1), (key2757, -1), (key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2)]

theorem rawRowCheck15543 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form13 = rawRow15543 := by decide +kernel

def row15543 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

theorem rowCheck15543 : row15543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15543 := by decide +kernel

theorem rowEval15543 (x : Key → ℝ) : Integer.Sparse.eval row15543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15543, Integer.Sparse.eval_collectBalanced, rawRowCheck15543]

def rawRow15544 : Integer.Sparse Key := [(key2807, 2), (key2801, 2), (key2827, 2), (key2784, -1), (key2778, -1), (key2918, -1), (key2851, -1), (key2922, -1), (key2868, -1), (key2704, 2), (key2698, 2), (key2724, 2), (key2630, -1), (key2624, -1), (key3021, -1), (key2851, -1), (key3025, -1), (key2868, -1), (key2669, -1), (key2663, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2724, -1), (key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2)]

theorem rawRowCheck15544 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form13 = rawRow15544 := by decide +kernel

def row15544 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

theorem rowCheck15544 : row15544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15544 := by decide +kernel

theorem rowEval15544 (x : Key → ℝ) : Integer.Sparse.eval row15544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15544, Integer.Sparse.eval_collectBalanced, rawRowCheck15544]

def rawRow15545 : Integer.Sparse Key := [(key2801, 2), (key2827, 2), (key2807, 2), (key2851, -1), (key2868, -1), (key2778, -1), (key2922, -1), (key2784, -1), (key2918, -1), (key2698, 2), (key2724, 2), (key2704, 2), (key2851, -1), (key2868, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2698, -1), (key2724, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2)]

theorem rawRowCheck15545 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form13 = rawRow15545 := by decide +kernel

def row15545 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

theorem rowCheck15545 : row15545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15545 := by decide +kernel

theorem rowEval15545 (x : Key → ℝ) : Integer.Sparse.eval row15545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15545, Integer.Sparse.eval_collectBalanced, rawRowCheck15545]

def rawRow15546 : Integer.Sparse Key := [(key2827, 2), (key2801, 2), (key2807, 2), (key2868, -1), (key2851, -1), (key2922, -1), (key2778, -1), (key2918, -1), (key2784, -1), (key2724, 2), (key2698, 2), (key2704, 2), (key2868, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key3021, -1), (key2630, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2752, -1), (key2669, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2)]

theorem rawRowCheck15546 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form13 = rawRow15546 := by decide +kernel

def row15546 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

theorem rowCheck15546 : row15546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15546 := by decide +kernel

theorem rowEval15546 (x : Key → ℝ) : Integer.Sparse.eval row15546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15546, Integer.Sparse.eval_collectBalanced, rawRowCheck15546]

def rawRow15547 : Integer.Sparse Key := [(key2807, 2), (key2827, 2), (key2801, 2), (key2918, -1), (key2922, -1), (key2784, -1), (key2868, -1), (key2778, -1), (key2851, -1), (key2704, 2), (key2724, 2), (key2698, 2), (key3021, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2624, -1), (key2851, -1), (key2752, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2663, -1), (key2698, -1), (key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2)]

theorem rawRowCheck15547 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form13 = rawRow15547 := by decide +kernel

def row15547 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

theorem rowCheck15547 : row15547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15547 := by decide +kernel

theorem rowEval15547 (x : Key → ℝ) : Integer.Sparse.eval row15547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15547, Integer.Sparse.eval_collectBalanced, rawRowCheck15547]

def rawRow15548 : Integer.Sparse Key := [(key2827, 2), (key2807, 2), (key2801, 2), (key2922, -1), (key2918, -1), (key2868, -1), (key2784, -1), (key2851, -1), (key2778, -1), (key2724, 2), (key2704, 2), (key2698, 2), (key3025, -1), (key3021, -1), (key2868, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key2757, -1), (key2752, -1), (key2724, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2)]

theorem rawRowCheck15548 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form13 = rawRow15548 := by decide +kernel

def row15548 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

theorem rowCheck15548 : row15548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15548 := by decide +kernel

theorem rowEval15548 (x : Key → ℝ) : Integer.Sparse.eval row15548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15548, Integer.Sparse.eval_collectBalanced, rawRowCheck15548]

def rawRow15549 : Integer.Sparse Key := [(key2851, 2), (key2858, 2), (key2868, 2), (key2778, -1), (key2792, -1), (key2801, -1), (key2919, -1), (key2827, -1), (key2922, -1), (key2851, 2), (key2858, 2), (key2868, 2), (key2624, -1), (key2638, -1), (key2698, -1), (key3022, -1), (key2724, -1), (key3025, -1), (key2778, -1), (key2792, -1), (key2801, -1), (key2919, -1), (key2827, -1), (key2922, -1), (key2624, -1), (key2638, -1), (key2698, -1), (key3022, -1), (key2724, -1), (key3025, -1), (key2608, 2), (key2659, 2), (key2663, 2), (key2757, 2), (key3009, 2), (key3016, 2)]

theorem rawRowCheck15549 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form13 = rawRow15549 := by decide +kernel

def row15549 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 2), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3009, 2), (key3016, 2), (key3022, -2), (key3025, -2)]

theorem rowCheck15549 : row15549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15549 := by decide +kernel

theorem rowEval15549 (x : Key → ℝ) : Integer.Sparse.eval row15549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15549, Integer.Sparse.eval_collectBalanced, rawRowCheck15549]

def rawRow15550 : Integer.Sparse Key := [(key2858, 2), (key2851, 2), (key2868, 2), (key2792, -1), (key2778, -1), (key2919, -1), (key2801, -1), (key2922, -1), (key2827, -1), (key2858, 2), (key2851, 2), (key2868, 2), (key2638, -1), (key2624, -1), (key3022, -1), (key2698, -1), (key3025, -1), (key2724, -1), (key2792, -1), (key2778, -1), (key2919, -1), (key2801, -1), (key2922, -1), (key2827, -1), (key2638, -1), (key2624, -1), (key3022, -1), (key2698, -1), (key3025, -1), (key2724, -1), (key2659, 2), (key2608, 2), (key2757, 2), (key2663, 2), (key3016, 2), (key3009, 2)]

theorem rawRowCheck15550 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form13 = rawRow15550 := by decide +kernel

def row15550 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 2), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3009, 2), (key3016, 2), (key3022, -2), (key3025, -2)]

theorem rowCheck15550 : row15550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15550 := by decide +kernel

theorem rowEval15550 (x : Key → ℝ) : Integer.Sparse.eval row15550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck15550, Integer.Sparse.eval_collectBalanced, rawRowCheck15550]

def rawRow15551 : Integer.Sparse Key := [(key2851, 2), (key2868, 2), (key2858, 2), (key2801, -1), (key2827, -1), (key2778, -1), (key2922, -1), (key2792, -1), (key2919, -1), (key2851, 2), (key2868, 2), (key2858, 2), (key2698, -1), (key2724, -1), (key2624, -1), (key3025, -1), (key2638, -1), (key3022, -1), (key2801, -1), (key2827, -1), (key2778, -1), (key2922, -1), (key2792, -1), (key2919, -1), (key2698, -1), (key2724, -1), (key2624, -1), (key3025, -1), (key2638, -1), (key3022, -1), (key2663, 2), (key2757, 2), (key2608, 2), (key3016, 2), (key2659, 2), (key2757, 2)]

theorem rawRowCheck15551 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form13 = rawRow15551 := by decide +kernel

def row15551 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 4), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3016, 2), (key3022, -2), (key3025, -2)]

theorem rowCheck15551 : row15551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15551 := by decide +kernel

theorem rowEval15551 (x : Key → ℝ) : Integer.Sparse.eval row15551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15551, Integer.Sparse.eval_collectBalanced, rawRowCheck15551]

def rawRow15552 : Integer.Sparse Key := [(key2868, 2), (key2851, 2), (key2858, 2), (key2827, -1), (key2801, -1), (key2922, -1), (key2778, -1), (key2919, -1), (key2792, -1), (key2868, 2), (key2851, 2), (key2858, 2), (key2724, -1), (key2698, -1), (key3025, -1), (key2624, -1), (key3022, -1), (key2638, -1), (key2827, -1), (key2801, -1), (key2922, -1), (key2778, -1), (key2919, -1), (key2792, -1), (key2724, -1), (key2698, -1), (key3025, -1), (key2624, -1), (key3022, -1), (key2638, -1), (key2757, 2), (key2663, 2), (key3016, 2), (key2608, 2), (key2757, 2), (key2659, 2)]

theorem rawRowCheck15552 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form13 = rawRow15552 := by decide +kernel

def row15552 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 4), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3016, 2), (key3022, -2), (key3025, -2)]

theorem rowCheck15552 : row15552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15552 := by decide +kernel

theorem rowEval15552 (x : Key → ℝ) : Integer.Sparse.eval row15552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15552, Integer.Sparse.eval_collectBalanced, rawRowCheck15552]

def rawRow15553 : Integer.Sparse Key := [(key2858, 2), (key2868, 2), (key2851, 2), (key2919, -1), (key2922, -1), (key2792, -1), (key2827, -1), (key2778, -1), (key2801, -1), (key2858, 2), (key2868, 2), (key2851, 2), (key3022, -1), (key3025, -1), (key2638, -1), (key2724, -1), (key2624, -1), (key2698, -1), (key2919, -1), (key2922, -1), (key2792, -1), (key2827, -1), (key2778, -1), (key2801, -1), (key3022, -1), (key3025, -1), (key2638, -1), (key2724, -1), (key2624, -1), (key2698, -1), (key3009, 2), (key3016, 2), (key2659, 2), (key2757, 2), (key2608, 2), (key2663, 2)]

theorem rawRowCheck15553 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form13 = rawRow15553 := by decide +kernel

def row15553 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 2), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3009, 2), (key3016, 2), (key3022, -2), (key3025, -2)]

theorem rowCheck15553 : row15553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15553 := by decide +kernel

theorem rowEval15553 (x : Key → ℝ) : Integer.Sparse.eval row15553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck15553, Integer.Sparse.eval_collectBalanced, rawRowCheck15553]

def rawRow15554 : Integer.Sparse Key := [(key2868, 2), (key2858, 2), (key2851, 2), (key2922, -1), (key2919, -1), (key2827, -1), (key2792, -1), (key2801, -1), (key2778, -1), (key2868, 2), (key2858, 2), (key2851, 2), (key3025, -1), (key3022, -1), (key2724, -1), (key2638, -1), (key2698, -1), (key2624, -1), (key2922, -1), (key2919, -1), (key2827, -1), (key2792, -1), (key2801, -1), (key2778, -1), (key3025, -1), (key3022, -1), (key2724, -1), (key2638, -1), (key2698, -1), (key2624, -1), (key3016, 2), (key3009, 2), (key2757, 2), (key2659, 2), (key2663, 2), (key2608, 2)]

theorem rawRowCheck15554 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form13 = rawRow15554 := by decide +kernel

def row15554 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 2), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3009, 2), (key3016, 2), (key3022, -2), (key3025, -2)]

theorem rowCheck15554 : row15554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15554 := by decide +kernel

theorem rowEval15554 (x : Key → ℝ) : Integer.Sparse.eval row15554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15554, Integer.Sparse.eval_collectBalanced, rawRowCheck15554]

def rawRow15555 : Integer.Sparse Key := [(key2772, 4), (key2889, 4), (key2889, 4), (key2766, -2), (key2766, -2), (key2843, -2), (key2843, -2), (key2887, -2), (key2887, -2), (key2931, -2), (key2931, -2), (key2968, -2), (key2968, -2), (key2995, -2), (key2995, -2), (key2929, 4), (key2966, 4), (key2966, 4)]

theorem rawRowCheck15555 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form0 = rawRow15555 := by decide +kernel

def row15555 : Integer.Sparse Key := [(key2766, -4), (key2772, 4), (key2843, -4), (key2887, -4), (key2889, 8), (key2929, 4), (key2931, -4), (key2966, 8), (key2968, -4), (key2995, -4)]

theorem rowCheck15555 : row15555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15555 := by decide +kernel

theorem rowEval15555 (x : Key → ℝ) : Integer.Sparse.eval row15555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15555, Integer.Sparse.eval_collectBalanced, rawRowCheck15555]

def rawRow15556 : Integer.Sparse Key := [(key2889, 4), (key2772, 4), (key2889, 4), (key2843, -2), (key2887, -2), (key2766, -2), (key2887, -2), (key2766, -2), (key2843, -2), (key2968, -2), (key2995, -2), (key2931, -2), (key2995, -2), (key2931, -2), (key2968, -2), (key2966, 4), (key2929, 4), (key2966, 4)]

theorem rawRowCheck15556 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form0 = rawRow15556 := by decide +kernel

def row15556 : Integer.Sparse Key := [(key2766, -4), (key2772, 4), (key2843, -4), (key2887, -4), (key2889, 8), (key2929, 4), (key2931, -4), (key2966, 8), (key2968, -4), (key2995, -4)]

theorem rowCheck15556 : row15556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15556 := by decide +kernel

theorem rowEval15556 (x : Key → ℝ) : Integer.Sparse.eval row15556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15556, Integer.Sparse.eval_collectBalanced, rawRowCheck15556]

def rawRow15557 : Integer.Sparse Key := [(key2889, 4), (key2889, 4), (key2772, 4), (key2887, -2), (key2843, -2), (key2887, -2), (key2766, -2), (key2843, -2), (key2766, -2), (key2995, -2), (key2968, -2), (key2995, -2), (key2931, -2), (key2968, -2), (key2931, -2), (key2966, 4), (key2966, 4), (key2929, 4)]

theorem rawRowCheck15557 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form0 = rawRow15557 := by decide +kernel

def row15557 : Integer.Sparse Key := [(key2766, -4), (key2772, 4), (key2843, -4), (key2887, -4), (key2889, 8), (key2929, 4), (key2931, -4), (key2966, 8), (key2968, -4), (key2995, -4)]

theorem rowCheck15557 : row15557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15557 := by decide +kernel

theorem rowEval15557 (x : Key → ℝ) : Integer.Sparse.eval row15557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15557, Integer.Sparse.eval_collectBalanced, rawRowCheck15557]

def rawRow15558 : Integer.Sparse Key := [(key2411, 4), (key2484, 4), (key2484, 4), (key2443, -2), (key2443, -2), (key2509, -2), (key2509, -2), (key2524, -2), (key2524, -2), (key2406, -2), (key2406, -2), (key2472, -2), (key2472, -2), (key2480, -2), (key2480, -2), (key2437, 4), (key2503, 4), (key2503, 4)]

theorem rawRowCheck15558 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form0 = rawRow15558 := by decide +kernel

def row15558 : Integer.Sparse Key := [(key2406, -4), (key2411, 4), (key2437, 4), (key2443, -4), (key2472, -4), (key2480, -4), (key2484, 8), (key2503, 8), (key2509, -4), (key2524, -4)]

theorem rowCheck15558 : row15558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15558 := by decide +kernel

theorem rowEval15558 (x : Key → ℝ) : Integer.Sparse.eval row15558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15558, Integer.Sparse.eval_collectBalanced, rawRowCheck15558]

def rawRow15559 : Integer.Sparse Key := [(key2484, 4), (key2411, 4), (key2484, 4), (key2509, -2), (key2524, -2), (key2443, -2), (key2524, -2), (key2443, -2), (key2509, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2503, 4), (key2437, 4), (key2503, 4)]

theorem rawRowCheck15559 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form0 = rawRow15559 := by decide +kernel

def row15559 : Integer.Sparse Key := [(key2406, -4), (key2411, 4), (key2437, 4), (key2443, -4), (key2472, -4), (key2480, -4), (key2484, 8), (key2503, 8), (key2509, -4), (key2524, -4)]

theorem rowCheck15559 : row15559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15559 := by decide +kernel

theorem rowEval15559 (x : Key → ℝ) : Integer.Sparse.eval row15559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15559, Integer.Sparse.eval_collectBalanced, rawRowCheck15559]

def rawRow15560 : Integer.Sparse Key := [(key2484, 4), (key2484, 4), (key2411, 4), (key2524, -2), (key2509, -2), (key2524, -2), (key2443, -2), (key2509, -2), (key2443, -2), (key2480, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2406, -2), (key2503, 4), (key2503, 4), (key2437, 4)]

theorem rawRowCheck15560 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form0 = rawRow15560 := by decide +kernel

def row15560 : Integer.Sparse Key := [(key2406, -4), (key2411, 4), (key2437, 4), (key2443, -4), (key2472, -4), (key2480, -4), (key2484, 8), (key2503, 8), (key2509, -4), (key2524, -4)]

theorem rowCheck15560 : row15560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15560 := by decide +kernel

theorem rowEval15560 (x : Key → ℝ) : Integer.Sparse.eval row15560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15560, Integer.Sparse.eval_collectBalanced, rawRowCheck15560]

def rawRow15561 : Integer.Sparse Key := [(key1001, -2), (key1001, -2), (key1015, -2), (key993, 6), (key1232, -2), (key1232, -2), (key1235, -2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1123, 2), (key1123, 2), (key1028, -2), (key1106, -2), (key1106, -2), (key1242, 6), (key1071, -2), (key1150, -2), (key1150, -2)]

theorem rawRowCheck15561 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form1 = rawRow15561 := by decide +kernel

def row15561 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

theorem rowCheck15561 : row15561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15561 := by decide +kernel

theorem rowEval15561 (x : Key → ℝ) : Integer.Sparse.eval row15561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15561, Integer.Sparse.eval_collectBalanced, rawRowCheck15561]

def rawRow15562 : Integer.Sparse Key := [(key1001, -2), (key1015, -2), (key1001, -2), (key993, 6), (key1232, -2), (key1235, -2), (key1232, -2), (key1114, 2), (key1123, 2), (key1036, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1106, -2), (key1028, -2), (key1106, -2), (key1242, 6), (key1150, -2), (key1071, -2), (key1150, -2)]

theorem rawRowCheck15562 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form1 = rawRow15562 := by decide +kernel

def row15562 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

theorem rowCheck15562 : row15562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15562 := by decide +kernel

theorem rowEval15562 (x : Key → ℝ) : Integer.Sparse.eval row15562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15562, Integer.Sparse.eval_collectBalanced, rawRowCheck15562]

def rawRow15563 : Integer.Sparse Key := [(key1015, -2), (key1001, -2), (key1001, -2), (key993, 6), (key1235, -2), (key1232, -2), (key1232, -2), (key1123, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1106, -2), (key1106, -2), (key1028, -2), (key1242, 6), (key1150, -2), (key1150, -2), (key1071, -2)]

theorem rawRowCheck15563 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form1 = rawRow15563 := by decide +kernel

def row15563 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

theorem rowCheck15563 : row15563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15563 := by decide +kernel

theorem rowEval15563 (x : Key → ℝ) : Integer.Sparse.eval row15563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15563, Integer.Sparse.eval_collectBalanced, rawRowCheck15563]

def rawRow15564 : Integer.Sparse Key := [(key1232, -2), (key1232, -2), (key1235, -2), (key1242, 6), (key1001, -2), (key1001, -2), (key1015, -2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1123, 2), (key1123, 2), (key1071, -2), (key1150, -2), (key1150, -2), (key993, 6), (key1028, -2), (key1106, -2), (key1106, -2)]

theorem rawRowCheck15564 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form1 = rawRow15564 := by decide +kernel

def row15564 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

theorem rowCheck15564 : row15564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15564 := by decide +kernel

theorem rowEval15564 (x : Key → ℝ) : Integer.Sparse.eval row15564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15564, Integer.Sparse.eval_collectBalanced, rawRowCheck15564]

def rawRow15565 : Integer.Sparse Key := [(key1232, -2), (key1235, -2), (key1232, -2), (key1242, 6), (key1001, -2), (key1015, -2), (key1001, -2), (key1114, 2), (key1123, 2), (key1036, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1150, -2), (key1071, -2), (key1150, -2), (key993, 6), (key1106, -2), (key1028, -2), (key1106, -2)]

theorem rawRowCheck15565 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form1 = rawRow15565 := by decide +kernel

def row15565 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

theorem rowCheck15565 : row15565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15565 := by decide +kernel

theorem rowEval15565 (x : Key → ℝ) : Integer.Sparse.eval row15565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15565, Integer.Sparse.eval_collectBalanced, rawRowCheck15565]

def rawRow15566 : Integer.Sparse Key := [(key1235, -2), (key1232, -2), (key1232, -2), (key1242, 6), (key1015, -2), (key1001, -2), (key1001, -2), (key1123, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1150, -2), (key1150, -2), (key1071, -2), (key993, 6), (key1106, -2), (key1106, -2), (key1028, -2)]

theorem rawRowCheck15566 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form1 = rawRow15566 := by decide +kernel

def row15566 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

theorem rowCheck15566 : row15566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15566 := by decide +kernel

theorem rowEval15566 (x : Key → ℝ) : Integer.Sparse.eval row15566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15566, Integer.Sparse.eval_collectBalanced, rawRowCheck15566]

def rawRow15567 : Integer.Sparse Key := [(key2376, -2), (key2376, -2), (key2388, -2), (key2370, 6), (key2876, -2), (key2876, -2), (key2925, -2), (key2768, 2), (key2768, 2), (key2845, 2), (key2845, 2), (key2916, 2), (key2916, 2), (key2762, -2), (key2839, -2), (key2839, -2), (key3028, 6), (key3005, -2), (key3019, -2), (key3019, -2)]

theorem rawRowCheck15567 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form2 = rawRow15567 := by decide +kernel

def row15567 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2762, -2), (key2768, 4), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, 4), (key2925, -2), (key3005, -2), (key3019, -4), (key3028, 6)]

theorem rowCheck15567 : row15567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15567 := by decide +kernel

theorem rowEval15567 (x : Key → ℝ) : Integer.Sparse.eval row15567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15567, Integer.Sparse.eval_collectBalanced, rawRowCheck15567]

def rawRow15568 : Integer.Sparse Key := [(key2376, -2), (key2388, -2), (key2376, -2), (key2370, 6), (key2876, -2), (key2925, -2), (key2876, -2), (key2845, 2), (key2916, 2), (key2768, 2), (key2916, 2), (key2768, 2), (key2845, 2), (key2839, -2), (key2762, -2), (key2839, -2), (key3028, 6), (key3019, -2), (key3005, -2), (key3019, -2)]

theorem rawRowCheck15568 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form2 = rawRow15568 := by decide +kernel

def row15568 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2762, -2), (key2768, 4), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, 4), (key2925, -2), (key3005, -2), (key3019, -4), (key3028, 6)]

theorem rowCheck15568 : row15568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15568 := by decide +kernel

theorem rowEval15568 (x : Key → ℝ) : Integer.Sparse.eval row15568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15568, Integer.Sparse.eval_collectBalanced, rawRowCheck15568]

def rawRow15569 : Integer.Sparse Key := [(key2388, -2), (key2376, -2), (key2376, -2), (key2370, 6), (key2925, -2), (key2876, -2), (key2876, -2), (key2916, 2), (key2845, 2), (key2916, 2), (key2768, 2), (key2845, 2), (key2768, 2), (key2839, -2), (key2839, -2), (key2762, -2), (key3028, 6), (key3019, -2), (key3019, -2), (key3005, -2)]

theorem rawRowCheck15569 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form2 = rawRow15569 := by decide +kernel

def row15569 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2762, -2), (key2768, 4), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, 4), (key2925, -2), (key3005, -2), (key3019, -4), (key3028, 6)]

theorem rowCheck15569 : row15569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15569 := by decide +kernel

theorem rowEval15569 (x : Key → ℝ) : Integer.Sparse.eval row15569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15569, Integer.Sparse.eval_collectBalanced, rawRowCheck15569]

def rawRow15570 : Integer.Sparse Key := [(key2568, -2), (key2568, -2), (key2570, -2), (key2575, 6), (key2376, -2), (key2376, -2), (key2388, -2), (key2404, 2), (key2404, 2), (key2470, 2), (key2470, 2), (key2478, 2), (key2478, 2), (key2435, -2), (key2501, -2), (key2501, -2), (key2370, 6), (key2762, -2), (key2839, -2), (key2839, -2)]

theorem rawRowCheck15570 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form2 = rawRow15570 := by decide +kernel

def row15570 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2404, 4), (key2435, -2), (key2470, 4), (key2478, 4), (key2501, -4), (key2568, -4), (key2570, -2), (key2575, 6), (key2762, -2), (key2839, -4)]

theorem rowCheck15570 : row15570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15570 := by decide +kernel

theorem rowEval15570 (x : Key → ℝ) : Integer.Sparse.eval row15570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15570, Integer.Sparse.eval_collectBalanced, rawRowCheck15570]

def rawRow15571 : Integer.Sparse Key := [(key2568, -2), (key2570, -2), (key2568, -2), (key2575, 6), (key2376, -2), (key2388, -2), (key2376, -2), (key2470, 2), (key2478, 2), (key2404, 2), (key2478, 2), (key2404, 2), (key2470, 2), (key2501, -2), (key2435, -2), (key2501, -2), (key2370, 6), (key2839, -2), (key2762, -2), (key2839, -2)]

theorem rawRowCheck15571 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form2 = rawRow15571 := by decide +kernel

def row15571 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2404, 4), (key2435, -2), (key2470, 4), (key2478, 4), (key2501, -4), (key2568, -4), (key2570, -2), (key2575, 6), (key2762, -2), (key2839, -4)]

theorem rowCheck15571 : row15571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15571 := by decide +kernel

theorem rowEval15571 (x : Key → ℝ) : Integer.Sparse.eval row15571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15571, Integer.Sparse.eval_collectBalanced, rawRowCheck15571]

def rawRow15572 : Integer.Sparse Key := [(key2570, -2), (key2568, -2), (key2568, -2), (key2575, 6), (key2388, -2), (key2376, -2), (key2376, -2), (key2478, 2), (key2470, 2), (key2478, 2), (key2404, 2), (key2470, 2), (key2404, 2), (key2501, -2), (key2501, -2), (key2435, -2), (key2370, 6), (key2839, -2), (key2839, -2), (key2762, -2)]

theorem rawRowCheck15572 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form2 = rawRow15572 := by decide +kernel

def row15572 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2404, 4), (key2435, -2), (key2470, 4), (key2478, 4), (key2501, -4), (key2568, -4), (key2570, -2), (key2575, 6), (key2762, -2), (key2839, -4)]

theorem rowCheck15572 : row15572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15572 := by decide +kernel

theorem rowEval15572 (x : Key → ℝ) : Integer.Sparse.eval row15572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15572, Integer.Sparse.eval_collectBalanced, rawRowCheck15572]

def rawRow15573 : Integer.Sparse Key := [(key2635, 6), (key2610, -2), (key2626, -2), (key2626, -2), (key2721, 6), (key2665, -2), (key2700, -2), (key2700, -2), (key2824, -2), (key2865, -2), (key2865, -2), (key2789, -2), (key2855, -2), (key2855, -2), (key2780, 2), (key2780, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2)]

theorem rawRowCheck15573 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form3 = rawRow15573 := by decide +kernel

def row15573 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

theorem rowCheck15573 : row15573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15573 := by decide +kernel

theorem rowEval15573 (x : Key → ℝ) : Integer.Sparse.eval row15573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15573, Integer.Sparse.eval_collectBalanced, rawRowCheck15573]

def rawRow15574 : Integer.Sparse Key := [(key2635, 6), (key2626, -2), (key2610, -2), (key2626, -2), (key2721, 6), (key2700, -2), (key2665, -2), (key2700, -2), (key2865, -2), (key2824, -2), (key2865, -2), (key2855, -2), (key2789, -2), (key2855, -2), (key2803, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2803, 2)]

theorem rawRowCheck15574 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form3 = rawRow15574 := by decide +kernel

def row15574 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

theorem rowCheck15574 : row15574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15574 := by decide +kernel

theorem rowEval15574 (x : Key → ℝ) : Integer.Sparse.eval row15574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15574, Integer.Sparse.eval_collectBalanced, rawRowCheck15574]

def rawRow15575 : Integer.Sparse Key := [(key2635, 6), (key2626, -2), (key2626, -2), (key2610, -2), (key2721, 6), (key2700, -2), (key2700, -2), (key2665, -2), (key2865, -2), (key2865, -2), (key2824, -2), (key2855, -2), (key2855, -2), (key2789, -2), (key2853, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2780, 2)]

theorem rawRowCheck15575 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form3 = rawRow15575 := by decide +kernel

def row15575 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

theorem rowCheck15575 : row15575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15575 := by decide +kernel

theorem rowEval15575 (x : Key → ℝ) : Integer.Sparse.eval row15575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15575, Integer.Sparse.eval_collectBalanced, rawRowCheck15575]

def rawRow15576 : Integer.Sparse Key := [(key2721, 6), (key2824, -2), (key2865, -2), (key2865, -2), (key2635, 6), (key2789, -2), (key2855, -2), (key2855, -2), (key2610, -2), (key2626, -2), (key2626, -2), (key2665, -2), (key2700, -2), (key2700, -2), (key2780, 2), (key2780, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2)]

theorem rawRowCheck15576 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form3 = rawRow15576 := by decide +kernel

def row15576 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

theorem rowCheck15576 : row15576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15576 := by decide +kernel

theorem rowEval15576 (x : Key → ℝ) : Integer.Sparse.eval row15576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15576, Integer.Sparse.eval_collectBalanced, rawRowCheck15576]

def rawRow15577 : Integer.Sparse Key := [(key2721, 6), (key2865, -2), (key2824, -2), (key2865, -2), (key2635, 6), (key2855, -2), (key2789, -2), (key2855, -2), (key2626, -2), (key2610, -2), (key2626, -2), (key2700, -2), (key2665, -2), (key2700, -2), (key2803, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2803, 2)]

theorem rawRowCheck15577 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form3 = rawRow15577 := by decide +kernel

def row15577 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

theorem rowCheck15577 : row15577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15577 := by decide +kernel

theorem rowEval15577 (x : Key → ℝ) : Integer.Sparse.eval row15577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15577, Integer.Sparse.eval_collectBalanced, rawRowCheck15577]

def rawRow15578 : Integer.Sparse Key := [(key2721, 6), (key2865, -2), (key2865, -2), (key2824, -2), (key2635, 6), (key2855, -2), (key2855, -2), (key2789, -2), (key2626, -2), (key2626, -2), (key2610, -2), (key2700, -2), (key2700, -2), (key2665, -2), (key2853, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2780, 2)]

theorem rawRowCheck15578 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form3 = rawRow15578 := by decide +kernel

def row15578 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

theorem rowCheck15578 : row15578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15578 := by decide +kernel

theorem rowEval15578 (x : Key → ℝ) : Integer.Sparse.eval row15578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15578, Integer.Sparse.eval_collectBalanced, rawRowCheck15578]

def rawRow15579 : Integer.Sparse Key := [(key1000, -2), (key1000, -2), (key1014, -2), (key994, 6), (key1231, -2), (key1231, -2), (key1234, -2), (key1035, 2), (key1035, 2), (key1113, 2), (key1113, 2), (key1122, 2), (key1122, 2), (key1029, -2), (key1107, -2), (key1107, -2), (key1241, 6), (key1070, -2), (key1149, -2), (key1149, -2)]

theorem rawRowCheck15579 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form4 = rawRow15579 := by decide +kernel

def row15579 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

theorem rowCheck15579 : row15579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15579 := by decide +kernel

theorem rowEval15579 (x : Key → ℝ) : Integer.Sparse.eval row15579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15579, Integer.Sparse.eval_collectBalanced, rawRowCheck15579]

def rawRow15580 : Integer.Sparse Key := [(key1000, -2), (key1014, -2), (key1000, -2), (key994, 6), (key1231, -2), (key1234, -2), (key1231, -2), (key1113, 2), (key1122, 2), (key1035, 2), (key1122, 2), (key1035, 2), (key1113, 2), (key1107, -2), (key1029, -2), (key1107, -2), (key1241, 6), (key1149, -2), (key1070, -2), (key1149, -2)]

theorem rawRowCheck15580 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form4 = rawRow15580 := by decide +kernel

def row15580 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

theorem rowCheck15580 : row15580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15580 := by decide +kernel

theorem rowEval15580 (x : Key → ℝ) : Integer.Sparse.eval row15580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15580, Integer.Sparse.eval_collectBalanced, rawRowCheck15580]

def rawRow15581 : Integer.Sparse Key := [(key1014, -2), (key1000, -2), (key1000, -2), (key994, 6), (key1234, -2), (key1231, -2), (key1231, -2), (key1122, 2), (key1113, 2), (key1122, 2), (key1035, 2), (key1113, 2), (key1035, 2), (key1107, -2), (key1107, -2), (key1029, -2), (key1241, 6), (key1149, -2), (key1149, -2), (key1070, -2)]

theorem rawRowCheck15581 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form4 = rawRow15581 := by decide +kernel

def row15581 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

theorem rowCheck15581 : row15581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15581 := by decide +kernel

theorem rowEval15581 (x : Key → ℝ) : Integer.Sparse.eval row15581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15581, Integer.Sparse.eval_collectBalanced, rawRowCheck15581]

def rawRow15582 : Integer.Sparse Key := [(key1231, -2), (key1231, -2), (key1234, -2), (key1241, 6), (key1000, -2), (key1000, -2), (key1014, -2), (key1035, 2), (key1035, 2), (key1113, 2), (key1113, 2), (key1122, 2), (key1122, 2), (key1070, -2), (key1149, -2), (key1149, -2), (key994, 6), (key1029, -2), (key1107, -2), (key1107, -2)]

theorem rawRowCheck15582 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form4 = rawRow15582 := by decide +kernel

def row15582 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

theorem rowCheck15582 : row15582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15582 := by decide +kernel

theorem rowEval15582 (x : Key → ℝ) : Integer.Sparse.eval row15582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15582, Integer.Sparse.eval_collectBalanced, rawRowCheck15582]

def rawRow15583 : Integer.Sparse Key := [(key1231, -2), (key1234, -2), (key1231, -2), (key1241, 6), (key1000, -2), (key1014, -2), (key1000, -2), (key1113, 2), (key1122, 2), (key1035, 2), (key1122, 2), (key1035, 2), (key1113, 2), (key1149, -2), (key1070, -2), (key1149, -2), (key994, 6), (key1107, -2), (key1029, -2), (key1107, -2)]

theorem rawRowCheck15583 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form4 = rawRow15583 := by decide +kernel

def row15583 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

theorem rowCheck15583 : row15583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15583 := by decide +kernel

theorem rowEval15583 (x : Key → ℝ) : Integer.Sparse.eval row15583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15583, Integer.Sparse.eval_collectBalanced, rawRowCheck15583]

def rawRow15584 : Integer.Sparse Key := [(key1234, -2), (key1231, -2), (key1231, -2), (key1241, 6), (key1014, -2), (key1000, -2), (key1000, -2), (key1122, 2), (key1113, 2), (key1122, 2), (key1035, 2), (key1113, 2), (key1035, 2), (key1149, -2), (key1149, -2), (key1070, -2), (key994, 6), (key1107, -2), (key1107, -2), (key1029, -2)]

theorem rawRowCheck15584 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form4 = rawRow15584 := by decide +kernel

def row15584 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

theorem rowCheck15584 : row15584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15584 := by decide +kernel

theorem rowEval15584 (x : Key → ℝ) : Integer.Sparse.eval row15584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15584, Integer.Sparse.eval_collectBalanced, rawRowCheck15584]

def rawRow15585 : Integer.Sparse Key := [(key1044, 4), (key1130, 4), (key1130, 4), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1080, -2), (key1080, -2), (key1159, -2), (key1159, -2), (key1174, -2), (key1174, -2), (key1073, 4), (key1152, 4), (key1152, 4)]

theorem rawRowCheck15585 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form5 = rawRow15585 := by decide +kernel

def row15585 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

theorem rowCheck15585 : row15585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15585 := by decide +kernel

theorem rowEval15585 (x : Key → ℝ) : Integer.Sparse.eval row15585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15585, Integer.Sparse.eval_collectBalanced, rawRowCheck15585]

def rawRow15586 : Integer.Sparse Key := [(key1130, 4), (key1044, 4), (key1130, 4), (key1116, -2), (key1125, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1159, -2), (key1174, -2), (key1080, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1152, 4), (key1073, 4), (key1152, 4)]

theorem rawRowCheck15586 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form5 = rawRow15586 := by decide +kernel

def row15586 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

theorem rowCheck15586 : row15586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15586 := by decide +kernel

theorem rowEval15586 (x : Key → ℝ) : Integer.Sparse.eval row15586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15586, Integer.Sparse.eval_collectBalanced, rawRowCheck15586]

def rawRow15587 : Integer.Sparse Key := [(key1130, 4), (key1130, 4), (key1044, 4), (key1125, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1038, -2), (key1174, -2), (key1159, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1080, -2), (key1152, 4), (key1152, 4), (key1073, 4)]

theorem rawRowCheck15587 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form5 = rawRow15587 := by decide +kernel

def row15587 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

theorem rowCheck15587 : row15587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15587 := by decide +kernel

theorem rowEval15587 (x : Key → ℝ) : Integer.Sparse.eval row15587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15587, Integer.Sparse.eval_collectBalanced, rawRowCheck15587]

def rawRow15588 : Integer.Sparse Key := [(key1044, 4), (key1130, 4), (key1130, 4), (key1080, -2), (key1080, -2), (key1159, -2), (key1159, -2), (key1174, -2), (key1174, -2), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1073, 4), (key1152, 4), (key1152, 4)]

theorem rawRowCheck15588 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form5 = rawRow15588 := by decide +kernel

def row15588 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

theorem rowCheck15588 : row15588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15588 := by decide +kernel

theorem rowEval15588 (x : Key → ℝ) : Integer.Sparse.eval row15588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15588, Integer.Sparse.eval_collectBalanced, rawRowCheck15588]

def rawRow15589 : Integer.Sparse Key := [(key1130, 4), (key1044, 4), (key1130, 4), (key1159, -2), (key1174, -2), (key1080, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1152, 4), (key1073, 4), (key1152, 4)]

theorem rawRowCheck15589 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form5 = rawRow15589 := by decide +kernel

def row15589 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

theorem rowCheck15589 : row15589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15589 := by decide +kernel

theorem rowEval15589 (x : Key → ℝ) : Integer.Sparse.eval row15589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15589, Integer.Sparse.eval_collectBalanced, rawRowCheck15589]

def rawRow15590 : Integer.Sparse Key := [(key1130, 4), (key1130, 4), (key1044, 4), (key1174, -2), (key1159, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1080, -2), (key1125, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1038, -2), (key1152, 4), (key1152, 4), (key1073, 4)]

theorem rawRowCheck15590 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form5 = rawRow15590 := by decide +kernel

def row15590 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

theorem rowCheck15590 : row15590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15590 := by decide +kernel

theorem rowEval15590 (x : Key → ℝ) : Integer.Sparse.eval row15590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15590, Integer.Sparse.eval_collectBalanced, rawRowCheck15590]

def rawRow15591 : Integer.Sparse Key := [(key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2752, -1), (key2752, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2792, -1), (key2792, -1), (key2858, -1), (key2858, -1), (key2919, -1), (key2919, -1), (key2784, 2), (key2784, 2), (key2807, 2), (key2807, 2), (key2918, 2), (key2918, 2), (key2778, -1), (key2778, -1), (key2801, -1), (key2801, -1), (key2851, -1), (key2851, -1), (key3009, 2), (key3022, 2), (key3022, 2), (key3007, -1), (key3007, -1), (key3011, -1), (key3011, -1), (key3021, -1), (key3021, -1)]

theorem rawRowCheck15591 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form6 = rawRow15591 := by decide +kernel

def row15591 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2752, -2), (key2778, -2), (key2784, 4), (key2792, -2), (key2801, -2), (key2807, 4), (key2851, -2), (key2858, -2), (key2918, 4), (key2919, -2), (key3007, -2), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, 4)]

theorem rowCheck15591 : row15591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15591 := by decide +kernel

theorem rowEval15591 (x : Key → ℝ) : Integer.Sparse.eval row15591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15591, Integer.Sparse.eval_collectBalanced, rawRowCheck15591]

def rawRow15592 : Integer.Sparse Key := [(key2704, -1), (key2752, -1), (key2669, -1), (key2752, -1), (key2669, -1), (key2704, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2858, -1), (key2919, -1), (key2792, -1), (key2919, -1), (key2792, -1), (key2858, -1), (key2807, 2), (key2918, 2), (key2784, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2801, -1), (key2851, -1), (key2778, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key3022, 2), (key3009, 2), (key3022, 2), (key3011, -1), (key3021, -1), (key3007, -1), (key3021, -1), (key3007, -1), (key3011, -1)]

theorem rawRowCheck15592 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form6 = rawRow15592 := by decide +kernel

def row15592 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2752, -2), (key2778, -2), (key2784, 4), (key2792, -2), (key2801, -2), (key2807, 4), (key2851, -2), (key2858, -2), (key2918, 4), (key2919, -2), (key3007, -2), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, 4)]

theorem rowCheck15592 : row15592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15592 := by decide +kernel

theorem rowEval15592 (x : Key → ℝ) : Integer.Sparse.eval row15592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15592, Integer.Sparse.eval_collectBalanced, rawRowCheck15592]

def rawRow15593 : Integer.Sparse Key := [(key2752, -1), (key2704, -1), (key2752, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2919, -1), (key2858, -1), (key2919, -1), (key2792, -1), (key2858, -1), (key2792, -1), (key2918, 2), (key2807, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2784, 2), (key2851, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key2778, -1), (key3022, 2), (key3022, 2), (key3009, 2), (key3021, -1), (key3011, -1), (key3021, -1), (key3007, -1), (key3011, -1), (key3007, -1)]

theorem rawRowCheck15593 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form6 = rawRow15593 := by decide +kernel

def row15593 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2752, -2), (key2778, -2), (key2784, 4), (key2792, -2), (key2801, -2), (key2807, 4), (key2851, -2), (key2858, -2), (key2918, 4), (key2919, -2), (key3007, -2), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, 4)]

theorem rowCheck15593 : row15593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15593 := by decide +kernel

theorem rowEval15593 (x : Key → ℝ) : Integer.Sparse.eval row15593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15593, Integer.Sparse.eval_collectBalanced, rawRowCheck15593]

def rawRow15594 : Integer.Sparse Key := [(key2752, -1), (key2752, -1), (key2918, -1), (key2918, -1), (key2919, -1), (key2919, -1), (key2757, 2), (key2922, 2), (key2922, 2), (key2669, -1), (key2669, -1), (key2784, -1), (key2784, -1), (key2792, -1), (key2792, -1), (key2704, 2), (key2704, 2), (key2807, 2), (key2807, 2), (key2858, 2), (key2858, 2), (key2724, -1), (key2724, -1), (key2827, -1), (key2827, -1), (key2868, -1), (key2868, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2778, -1), (key2778, -1), (key2801, -1), (key2801, -1), (key2851, -1), (key2851, -1)]

theorem rawRowCheck15594 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form6 = rawRow15594 := by decide +kernel

def row15594 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, 4), (key2724, -2), (key2752, -2), (key2757, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, 4), (key2827, -2), (key2851, -2), (key2858, 4), (key2868, -2), (key2918, -2), (key2919, -2), (key2922, 4)]

theorem rowCheck15594 : row15594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15594 := by decide +kernel

theorem rowEval15594 (x : Key → ℝ) : Integer.Sparse.eval row15594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15594, Integer.Sparse.eval_collectBalanced, rawRowCheck15594]

def rawRow15595 : Integer.Sparse Key := [(key2918, -1), (key2919, -1), (key2752, -1), (key2919, -1), (key2752, -1), (key2918, -1), (key2922, 2), (key2757, 2), (key2922, 2), (key2784, -1), (key2792, -1), (key2669, -1), (key2792, -1), (key2669, -1), (key2784, -1), (key2807, 2), (key2858, 2), (key2704, 2), (key2858, 2), (key2704, 2), (key2807, 2), (key2827, -1), (key2868, -1), (key2724, -1), (key2868, -1), (key2724, -1), (key2827, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, -1), (key2851, -1), (key2778, -1), (key2851, -1), (key2778, -1), (key2801, -1)]

theorem rawRowCheck15595 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form6 = rawRow15595 := by decide +kernel

def row15595 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, 4), (key2724, -2), (key2752, -2), (key2757, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, 4), (key2827, -2), (key2851, -2), (key2858, 4), (key2868, -2), (key2918, -2), (key2919, -2), (key2922, 4)]

theorem rowCheck15595 : row15595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15595 := by decide +kernel

theorem rowEval15595 (x : Key → ℝ) : Integer.Sparse.eval row15595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15595, Integer.Sparse.eval_collectBalanced, rawRowCheck15595]

def rawRow15596 : Integer.Sparse Key := [(key2919, -1), (key2918, -1), (key2919, -1), (key2752, -1), (key2918, -1), (key2752, -1), (key2922, 2), (key2922, 2), (key2757, 2), (key2792, -1), (key2784, -1), (key2792, -1), (key2669, -1), (key2784, -1), (key2669, -1), (key2858, 2), (key2807, 2), (key2858, 2), (key2704, 2), (key2807, 2), (key2704, 2), (key2868, -1), (key2827, -1), (key2868, -1), (key2724, -1), (key2827, -1), (key2724, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2851, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key2778, -1)]

theorem rawRowCheck15596 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form6 = rawRow15596 := by decide +kernel

def row15596 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, 4), (key2724, -2), (key2752, -2), (key2757, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, 4), (key2827, -2), (key2851, -2), (key2858, 4), (key2868, -2), (key2918, -2), (key2919, -2), (key2922, 4)]

theorem rowCheck15596 : row15596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15596 := by decide +kernel

theorem rowEval15596 (x : Key → ℝ) : Integer.Sparse.eval row15596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15596, Integer.Sparse.eval_collectBalanced, rawRowCheck15596]

def rawRow15597 : Integer.Sparse Key := [(key2688, 4), (key2714, 4), (key2714, 4), (key2681, -4), (key2681, -4), (key2712, -4), (key2817, -4), (key2817, -4), (key2863, -4), (key2815, 12)]

theorem rawRowCheck15597 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form7 = rawRow15597 := by decide +kernel

def row15597 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

theorem rowCheck15597 : row15597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15597 := by decide +kernel

theorem rowEval15597 (x : Key → ℝ) : Integer.Sparse.eval row15597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15597, Integer.Sparse.eval_collectBalanced, rawRowCheck15597]

def rawRow15598 : Integer.Sparse Key := [(key2714, 4), (key2688, 4), (key2714, 4), (key2681, -4), (key2712, -4), (key2681, -4), (key2817, -4), (key2863, -4), (key2817, -4), (key2815, 12)]

theorem rawRowCheck15598 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form7 = rawRow15598 := by decide +kernel

def row15598 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

theorem rowCheck15598 : row15598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15598 := by decide +kernel

theorem rowEval15598 (x : Key → ℝ) : Integer.Sparse.eval row15598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15598, Integer.Sparse.eval_collectBalanced, rawRowCheck15598]

def rawRow15599 : Integer.Sparse Key := [(key2714, 4), (key2714, 4), (key2688, 4), (key2712, -4), (key2681, -4), (key2681, -4), (key2863, -4), (key2817, -4), (key2817, -4), (key2815, 12)]

theorem rawRowCheck15599 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form7 = rawRow15599 := by decide +kernel

def row15599 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

theorem rowCheck15599 : row15599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15599 := by decide +kernel

theorem rowEval15599 (x : Key → ℝ) : Integer.Sparse.eval row15599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15599, Integer.Sparse.eval_collectBalanced, rawRowCheck15599]

def rawRow15600 : Integer.Sparse Key := [(key2688, 4), (key2817, 4), (key2817, 4), (key2681, -4), (key2681, -4), (key2815, -4), (key2714, -4), (key2714, -4), (key2863, -4), (key2712, 12)]

theorem rawRowCheck15600 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form7 = rawRow15600 := by decide +kernel

def row15600 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15600 : row15600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15600 := by decide +kernel

theorem rowEval15600 (x : Key → ℝ) : Integer.Sparse.eval row15600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15600, Integer.Sparse.eval_collectBalanced, rawRowCheck15600]

def rawRow15601 : Integer.Sparse Key := [(key2817, 4), (key2688, 4), (key2817, 4), (key2681, -4), (key2815, -4), (key2681, -4), (key2714, -4), (key2863, -4), (key2714, -4), (key2712, 12)]

theorem rawRowCheck15601 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form7 = rawRow15601 := by decide +kernel

def row15601 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15601 : row15601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15601 := by decide +kernel

theorem rowEval15601 (x : Key → ℝ) : Integer.Sparse.eval row15601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15601, Integer.Sparse.eval_collectBalanced, rawRowCheck15601]

def rawRow15602 : Integer.Sparse Key := [(key2817, 4), (key2817, 4), (key2688, 4), (key2815, -4), (key2681, -4), (key2681, -4), (key2863, -4), (key2714, -4), (key2714, -4), (key2712, 12)]

theorem rawRowCheck15602 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form7 = rawRow15602 := by decide +kernel

def row15602 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15602 : row15602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15602 := by decide +kernel

theorem rowEval15602 (x : Key → ℝ) : Integer.Sparse.eval row15602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15602, Integer.Sparse.eval_collectBalanced, rawRowCheck15602]

def rawRow15603 : Integer.Sparse Key := [(key2688, 4), (key2714, 4), (key2714, 4), (key2817, -4), (key2817, -4), (key2863, -4), (key2681, -4), (key2681, -4), (key2712, -4), (key2815, 12)]

theorem rawRowCheck15603 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form7 = rawRow15603 := by decide +kernel

def row15603 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

theorem rowCheck15603 : row15603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15603 := by decide +kernel

theorem rowEval15603 (x : Key → ℝ) : Integer.Sparse.eval row15603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15603, Integer.Sparse.eval_collectBalanced, rawRowCheck15603]

def rawRow15604 : Integer.Sparse Key := [(key2714, 4), (key2688, 4), (key2714, 4), (key2817, -4), (key2863, -4), (key2817, -4), (key2681, -4), (key2712, -4), (key2681, -4), (key2815, 12)]

theorem rawRowCheck15604 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form7 = rawRow15604 := by decide +kernel

def row15604 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

theorem rowCheck15604 : row15604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15604 := by decide +kernel

theorem rowEval15604 (x : Key → ℝ) : Integer.Sparse.eval row15604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15604, Integer.Sparse.eval_collectBalanced, rawRowCheck15604]

def rawRow15605 : Integer.Sparse Key := [(key2714, 4), (key2714, 4), (key2688, 4), (key2863, -4), (key2817, -4), (key2817, -4), (key2712, -4), (key2681, -4), (key2681, -4), (key2815, 12)]

theorem rawRowCheck15605 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form7 = rawRow15605 := by decide +kernel

def row15605 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

theorem rowCheck15605 : row15605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15605 := by decide +kernel

theorem rowEval15605 (x : Key → ℝ) : Integer.Sparse.eval row15605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15605, Integer.Sparse.eval_collectBalanced, rawRowCheck15605]

def rawRow15606 : Integer.Sparse Key := [(key2688, 4), (key2817, 4), (key2817, 4), (key2714, -4), (key2714, -4), (key2863, -4), (key2681, -4), (key2681, -4), (key2815, -4), (key2712, 12)]

theorem rawRowCheck15606 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form7 = rawRow15606 := by decide +kernel

def row15606 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15606 : row15606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15606 := by decide +kernel

theorem rowEval15606 (x : Key → ℝ) : Integer.Sparse.eval row15606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15606, Integer.Sparse.eval_collectBalanced, rawRowCheck15606]

def rawRow15607 : Integer.Sparse Key := [(key2817, 4), (key2688, 4), (key2817, 4), (key2714, -4), (key2863, -4), (key2714, -4), (key2681, -4), (key2815, -4), (key2681, -4), (key2712, 12)]

theorem rawRowCheck15607 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form7 = rawRow15607 := by decide +kernel

def row15607 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15607 : row15607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15607 := by decide +kernel

theorem rowEval15607 (x : Key → ℝ) : Integer.Sparse.eval row15607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15607, Integer.Sparse.eval_collectBalanced, rawRowCheck15607]

def rawRow15608 : Integer.Sparse Key := [(key2817, 4), (key2817, 4), (key2688, 4), (key2863, -4), (key2714, -4), (key2714, -4), (key2815, -4), (key2681, -4), (key2681, -4), (key2712, 12)]

theorem rawRowCheck15608 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form7 = rawRow15608 := by decide +kernel

def row15608 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15608 : row15608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15608 := by decide +kernel

theorem rowEval15608 (x : Key → ℝ) : Integer.Sparse.eval row15608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15608, Integer.Sparse.eval_collectBalanced, rawRowCheck15608]

def rawRow15609 : Integer.Sparse Key := [(key2588, -2), (key2588, -2), (key2599, -2), (key2584, 6), (key2875, -2), (key2875, -2), (key2909, -2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2888, 2), (key2888, 2), (key2763, -2), (key2840, -2), (key2840, -2), (key2988, 6), (key2930, -2), (key2967, -2), (key2967, -2)]

theorem rawRowCheck15609 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form8 = rawRow15609 := by decide +kernel

def row15609 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

theorem rowCheck15609 : row15609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15609 := by decide +kernel

theorem rowEval15609 (x : Key → ℝ) : Integer.Sparse.eval row15609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15609, Integer.Sparse.eval_collectBalanced, rawRowCheck15609]

def rawRow15610 : Integer.Sparse Key := [(key2588, -2), (key2599, -2), (key2588, -2), (key2584, 6), (key2875, -2), (key2909, -2), (key2875, -2), (key2844, 2), (key2888, 2), (key2767, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2840, -2), (key2763, -2), (key2840, -2), (key2988, 6), (key2967, -2), (key2930, -2), (key2967, -2)]

theorem rawRowCheck15610 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form8 = rawRow15610 := by decide +kernel

def row15610 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

theorem rowCheck15610 : row15610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15610 := by decide +kernel

theorem rowEval15610 (x : Key → ℝ) : Integer.Sparse.eval row15610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15610, Integer.Sparse.eval_collectBalanced, rawRowCheck15610]

def rawRow15611 : Integer.Sparse Key := [(key2599, -2), (key2588, -2), (key2588, -2), (key2584, 6), (key2909, -2), (key2875, -2), (key2875, -2), (key2888, 2), (key2844, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2767, 2), (key2840, -2), (key2840, -2), (key2763, -2), (key2988, 6), (key2967, -2), (key2967, -2), (key2930, -2)]

theorem rawRowCheck15611 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form8 = rawRow15611 := by decide +kernel

def row15611 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

theorem rowCheck15611 : row15611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15611 := by decide +kernel

theorem rowEval15611 (x : Key → ℝ) : Integer.Sparse.eval row15611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15611, Integer.Sparse.eval_collectBalanced, rawRowCheck15611]

def rawRow15612 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2930, -2), (key2763, 6), (key2875, -2), (key2875, -2), (key2988, -2), (key2588, 2), (key2588, 2), (key2844, 2), (key2844, 2), (key2967, 2), (key2967, 2), (key2584, -2), (key2840, -2), (key2840, -2), (key2909, 6), (key2599, -2), (key2888, -2), (key2888, -2)]

theorem rawRowCheck15612 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form8 = rawRow15612 := by decide +kernel

def row15612 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15612 : row15612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15612 := by decide +kernel

theorem rowEval15612 (x : Key → ℝ) : Integer.Sparse.eval row15612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15612, Integer.Sparse.eval_collectBalanced, rawRowCheck15612]

def rawRow15613 : Integer.Sparse Key := [(key2767, -2), (key2930, -2), (key2767, -2), (key2763, 6), (key2875, -2), (key2988, -2), (key2875, -2), (key2844, 2), (key2967, 2), (key2588, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2840, -2), (key2584, -2), (key2840, -2), (key2909, 6), (key2888, -2), (key2599, -2), (key2888, -2)]

theorem rawRowCheck15613 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form8 = rawRow15613 := by decide +kernel

def row15613 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15613 : row15613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15613 := by decide +kernel

theorem rowEval15613 (x : Key → ℝ) : Integer.Sparse.eval row15613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15613, Integer.Sparse.eval_collectBalanced, rawRowCheck15613]

def rawRow15614 : Integer.Sparse Key := [(key2930, -2), (key2767, -2), (key2767, -2), (key2763, 6), (key2988, -2), (key2875, -2), (key2875, -2), (key2967, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2840, -2), (key2840, -2), (key2584, -2), (key2909, 6), (key2888, -2), (key2888, -2), (key2599, -2)]

theorem rawRowCheck15614 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form8 = rawRow15614 := by decide +kernel

def row15614 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15614 : row15614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15614 := by decide +kernel

theorem rowEval15614 (x : Key → ℝ) : Integer.Sparse.eval row15614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15614, Integer.Sparse.eval_collectBalanced, rawRowCheck15614]

def rawRow15615 : Integer.Sparse Key := [(key2875, -2), (key2875, -2), (key2909, -2), (key2988, 6), (key2588, -2), (key2588, -2), (key2599, -2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2888, 2), (key2888, 2), (key2930, -2), (key2967, -2), (key2967, -2), (key2584, 6), (key2763, -2), (key2840, -2), (key2840, -2)]

theorem rawRowCheck15615 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form8 = rawRow15615 := by decide +kernel

def row15615 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

theorem rowCheck15615 : row15615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15615 := by decide +kernel

theorem rowEval15615 (x : Key → ℝ) : Integer.Sparse.eval row15615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15615, Integer.Sparse.eval_collectBalanced, rawRowCheck15615]

end MUB6.Certificate.GramRows

end OAI
