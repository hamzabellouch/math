import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
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

def rawRow7552 : Integer.Sparse Key := [(key2466, -6), (key2466, -6), (key2498, -6), (key2372, -6), (key2466, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2475, 2), (key2400, 2), (key2498, 2), (key2372, 2), (key2432, 2), (key2385, 2)]

theorem rawRowCheck7552 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form3 = rawRow7552 := by decide +kernel

def row7552 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

theorem rowCheck7552 : row7552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7552 := by decide +kernel

theorem rowEval7552 (x : Key → ℝ) : Integer.Sparse.eval row7552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck7552, Integer.Sparse.eval_collectBalanced, rawRowCheck7552]

def rawRow7553 : Integer.Sparse Key := [(key2466, -6), (key2498, -6), (key2372, -6), (key2466, -6), (key2475, 2), (key2400, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2432, 2), (key2498, 2), (key2385, 2), (key2475, 2), (key2372, 2), (key2400, 2)]

theorem rawRowCheck7553 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form3 = rawRow7553 := by decide +kernel

def row7553 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

theorem rowCheck7553 : row7553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7553 := by decide +kernel

theorem rowEval7553 (x : Key → ℝ) : Integer.Sparse.eval row7553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7553, Integer.Sparse.eval_collectBalanced, rawRowCheck7553]

def rawRow7554 : Integer.Sparse Key := [(key2466, -6), (key2498, -6), (key2466, -6), (key2372, -6), (key2475, 2), (key2466, 2), (key2400, 2), (key2498, 2), (key2466, 2), (key2372, 2), (key2498, 2), (key2432, 2), (key2475, 2), (key2385, 2), (key2400, 2), (key2372, 2)]

theorem rawRowCheck7554 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form3 = rawRow7554 := by decide +kernel

def row7554 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

theorem rowCheck7554 : row7554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7554 := by decide +kernel

theorem rowEval7554 (x : Key → ℝ) : Integer.Sparse.eval row7554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck7554, Integer.Sparse.eval_collectBalanced, rawRowCheck7554]

def rawRow7555 : Integer.Sparse Key := [(key2498, -6), (key2372, -6), (key2466, -6), (key2466, -6), (key2432, 2), (key2498, 2), (key2498, 2), (key2385, 2), (key2475, 2), (key2475, 2), (key2372, 2), (key2372, 2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2)]

theorem rawRowCheck7555 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form3 = rawRow7555 := by decide +kernel

def row7555 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

theorem rowCheck7555 : row7555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7555 := by decide +kernel

theorem rowEval7555 (x : Key → ℝ) : Integer.Sparse.eval row7555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7555, Integer.Sparse.eval_collectBalanced, rawRowCheck7555]

def rawRow7556 : Integer.Sparse Key := [(key2498, -6), (key2466, -6), (key2372, -6), (key2466, -6), (key2498, 2), (key2432, 2), (key2498, 2), (key2475, 2), (key2385, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2372, 2), (key2400, 2)]

theorem rawRowCheck7556 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form3 = rawRow7556 := by decide +kernel

def row7556 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

theorem rowCheck7556 : row7556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7556 := by decide +kernel

theorem rowEval7556 (x : Key → ℝ) : Integer.Sparse.eval row7556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7556, Integer.Sparse.eval_collectBalanced, rawRowCheck7556]

def rawRow7557 : Integer.Sparse Key := [(key2498, -6), (key2466, -6), (key2466, -6), (key2372, -6), (key2498, 2), (key2498, 2), (key2432, 2), (key2475, 2), (key2475, 2), (key2385, 2), (key2466, 2), (key2400, 2), (key2466, 2), (key2372, 2), (key2400, 2), (key2372, 2)]

theorem rawRowCheck7557 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form3 = rawRow7557 := by decide +kernel

def row7557 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

theorem rowCheck7557 : row7557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7557 := by decide +kernel

theorem rowEval7557 (x : Key → ℝ) : Integer.Sparse.eval row7557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck7557, Integer.Sparse.eval_collectBalanced, rawRowCheck7557]

def rawRow7558 : Integer.Sparse Key := [(key2353, -6), (key2359, -6), (key2359, -6), (key2359, -6), (key2448, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2515, 2)]

theorem rawRowCheck7558 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form4 = rawRow7558 := by decide +kernel

def row7558 : Integer.Sparse Key := [(key2353, -6), (key2359, -18), (key2448, 6), (key2454, 12), (key2515, 6)]

theorem rowCheck7558 : row7558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7558 := by decide +kernel

theorem rowEval7558 (x : Key → ℝ) : Integer.Sparse.eval row7558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7558, Integer.Sparse.eval_collectBalanced, rawRowCheck7558]

def rawRow7559 : Integer.Sparse Key := [(key2359, -6), (key2353, -6), (key2359, -6), (key2359, -6), (key2454, 2), (key2448, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2454, 2)]

theorem rawRowCheck7559 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form4 = rawRow7559 := by decide +kernel

def row7559 : Integer.Sparse Key := [(key2353, -6), (key2359, -18), (key2448, 6), (key2454, 12), (key2515, 6)]

theorem rowCheck7559 : row7559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7559 := by decide +kernel

theorem rowEval7559 (x : Key → ℝ) : Integer.Sparse.eval row7559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7559, Integer.Sparse.eval_collectBalanced, rawRowCheck7559]

def rawRow7560 : Integer.Sparse Key := [(key2359, -6), (key2359, -6), (key2353, -6), (key2359, -6), (key2454, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2454, 2)]

theorem rawRowCheck7560 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form4 = rawRow7560 := by decide +kernel

def row7560 : Integer.Sparse Key := [(key2353, -6), (key2359, -18), (key2448, 6), (key2454, 12), (key2515, 6)]

theorem rowCheck7560 : row7560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7560 := by decide +kernel

theorem rowEval7560 (x : Key → ℝ) : Integer.Sparse.eval row7560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7560, Integer.Sparse.eval_collectBalanced, rawRowCheck7560]

def rawRow7561 : Integer.Sparse Key := [(key2359, -6), (key2359, -6), (key2359, -6), (key2353, -6), (key2515, 2), (key2515, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2448, 2), (key2448, 2)]

theorem rawRowCheck7561 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow7561 := by decide +kernel

def row7561 : Integer.Sparse Key := [(key2353, -6), (key2359, -18), (key2448, 6), (key2454, 12), (key2515, 6)]

theorem rowCheck7561 : row7561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7561 := by decide +kernel

theorem rowEval7561 (x : Key → ℝ) : Integer.Sparse.eval row7561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7561, Integer.Sparse.eval_collectBalanced, rawRowCheck7561]

def rawRow7562 : Integer.Sparse Key := [(key2448, -6), (key2454, -6), (key2454, -6), (key2515, -6), (key2353, 2), (key2359, 2), (key2359, 2), (key2448, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2566, 2), (key2566, 2), (key2578, 2)]

theorem rawRowCheck7562 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form4 = rawRow7562 := by decide +kernel

def row7562 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

theorem rowCheck7562 : row7562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7562 := by decide +kernel

theorem rowEval7562 (x : Key → ℝ) : Integer.Sparse.eval row7562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7562, Integer.Sparse.eval_collectBalanced, rawRowCheck7562]

def rawRow7563 : Integer.Sparse Key := [(key2454, -6), (key2448, -6), (key2454, -6), (key2515, -6), (key2359, 2), (key2353, 2), (key2359, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2566, 2), (key2578, 2), (key2566, 2)]

theorem rawRowCheck7563 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form4 = rawRow7563 := by decide +kernel

def row7563 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

theorem rowCheck7563 : row7563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7563 := by decide +kernel

theorem rowEval7563 (x : Key → ℝ) : Integer.Sparse.eval row7563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7563, Integer.Sparse.eval_collectBalanced, rawRowCheck7563]

def rawRow7564 : Integer.Sparse Key := [(key2454, -6), (key2454, -6), (key2448, -6), (key2515, -6), (key2359, 2), (key2359, 2), (key2353, 2), (key2515, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2448, 2), (key2578, 2), (key2566, 2), (key2566, 2)]

theorem rawRowCheck7564 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form4 = rawRow7564 := by decide +kernel

def row7564 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

theorem rowCheck7564 : row7564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7564 := by decide +kernel

theorem rowEval7564 (x : Key → ℝ) : Integer.Sparse.eval row7564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7564, Integer.Sparse.eval_collectBalanced, rawRowCheck7564]

def rawRow7565 : Integer.Sparse Key := [(key2448, -6), (key2454, -6), (key2515, -6), (key2454, -6), (key2448, 2), (key2454, 2), (key2515, 2), (key2353, 2), (key2359, 2), (key2448, 2), (key2515, 2), (key2566, 2), (key2578, 2), (key2359, 2), (key2454, 2), (key2515, 2)]

theorem rawRowCheck7565 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form4 = rawRow7565 := by decide +kernel

def row7565 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2566, 2), (key2578, 2)]

theorem rowCheck7565 : row7565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7565 := by decide +kernel

theorem rowEval7565 (x : Key → ℝ) : Integer.Sparse.eval row7565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7565, Integer.Sparse.eval_collectBalanced, rawRowCheck7565]

def rawRow7566 : Integer.Sparse Key := [(key2454, -6), (key2448, -6), (key2515, -6), (key2454, -6), (key2454, 2), (key2448, 2), (key2515, 2), (key2359, 2), (key2353, 2), (key2515, 2), (key2448, 2), (key2578, 2), (key2566, 2), (key2359, 2), (key2515, 2), (key2454, 2)]

theorem rawRowCheck7566 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form4 = rawRow7566 := by decide +kernel

def row7566 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2566, 2), (key2578, 2)]

theorem rowCheck7566 : row7566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7566 := by decide +kernel

theorem rowEval7566 (x : Key → ℝ) : Integer.Sparse.eval row7566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7566, Integer.Sparse.eval_collectBalanced, rawRowCheck7566]

def rawRow7567 : Integer.Sparse Key := [(key2448, -6), (key2515, -6), (key2454, -6), (key2454, -6), (key2448, 2), (key2515, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2353, 2), (key2578, 2), (key2359, 2), (key2515, 2), (key2454, 2), (key2359, 2), (key2515, 2)]

theorem rawRowCheck7567 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form4 = rawRow7567 := by decide +kernel

def row7567 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, 2), (key2578, 2)]

theorem rowCheck7567 : row7567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7567 := by decide +kernel

theorem rowEval7567 (x : Key → ℝ) : Integer.Sparse.eval row7567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7567, Integer.Sparse.eval_collectBalanced, rawRowCheck7567]

def rawRow7568 : Integer.Sparse Key := [(key2515, -6), (key2448, -6), (key2454, -6), (key2454, -6), (key2515, 2), (key2448, 2), (key2454, 2), (key2515, 2), (key2448, 2), (key2578, 2), (key2353, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2515, 2), (key2359, 2)]

theorem rawRowCheck7568 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form4 = rawRow7568 := by decide +kernel

def row7568 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, 2), (key2578, 2)]

theorem rowCheck7568 : row7568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7568 := by decide +kernel

theorem rowEval7568 (x : Key → ℝ) : Integer.Sparse.eval row7568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck7568, Integer.Sparse.eval_collectBalanced, rawRowCheck7568]

def rawRow7569 : Integer.Sparse Key := [(key2454, -6), (key2515, -6), (key2448, -6), (key2454, -6), (key2454, 2), (key2515, 2), (key2448, 2), (key2566, 2), (key2578, 2), (key2359, 2), (key2515, 2), (key2353, 2), (key2448, 2), (key2515, 2), (key2359, 2), (key2454, 2)]

theorem rawRowCheck7569 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form4 = rawRow7569 := by decide +kernel

def row7569 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2566, 2), (key2578, 2)]

theorem rowCheck7569 : row7569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7569 := by decide +kernel

theorem rowEval7569 (x : Key → ℝ) : Integer.Sparse.eval row7569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7569, Integer.Sparse.eval_collectBalanced, rawRowCheck7569]

def rawRow7570 : Integer.Sparse Key := [(key2515, -6), (key2454, -6), (key2448, -6), (key2454, -6), (key2515, 2), (key2454, 2), (key2448, 2), (key2578, 2), (key2566, 2), (key2515, 2), (key2359, 2), (key2448, 2), (key2353, 2), (key2515, 2), (key2454, 2), (key2359, 2)]

theorem rawRowCheck7570 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form4 = rawRow7570 := by decide +kernel

def row7570 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2566, 2), (key2578, 2)]

theorem rowCheck7570 : row7570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7570 := by decide +kernel

theorem rowEval7570 (x : Key → ℝ) : Integer.Sparse.eval row7570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck7570, Integer.Sparse.eval_collectBalanced, rawRowCheck7570]

def rawRow7571 : Integer.Sparse Key := [(key2454, -6), (key2454, -6), (key2515, -6), (key2448, -6), (key2566, 2), (key2566, 2), (key2578, 2), (key2359, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2515, 2), (key2353, 2), (key2448, 2), (key2448, 2)]

theorem rawRowCheck7571 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form4 = rawRow7571 := by decide +kernel

def row7571 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

theorem rowCheck7571 : row7571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7571 := by decide +kernel

theorem rowEval7571 (x : Key → ℝ) : Integer.Sparse.eval row7571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7571, Integer.Sparse.eval_collectBalanced, rawRowCheck7571]

def rawRow7572 : Integer.Sparse Key := [(key2454, -6), (key2515, -6), (key2454, -6), (key2448, -6), (key2566, 2), (key2578, 2), (key2566, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2448, 2), (key2353, 2), (key2448, 2)]

theorem rawRowCheck7572 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form4 = rawRow7572 := by decide +kernel

def row7572 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

theorem rowCheck7572 : row7572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7572 := by decide +kernel

theorem rowEval7572 (x : Key → ℝ) : Integer.Sparse.eval row7572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7572, Integer.Sparse.eval_collectBalanced, rawRowCheck7572]

def rawRow7573 : Integer.Sparse Key := [(key2515, -6), (key2454, -6), (key2454, -6), (key2448, -6), (key2578, 2), (key2566, 2), (key2566, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2359, 2), (key2448, 2), (key2448, 2), (key2353, 2)]

theorem rawRowCheck7573 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form4 = rawRow7573 := by decide +kernel

def row7573 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

theorem rowCheck7573 : row7573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7573 := by decide +kernel

theorem rowEval7573 (x : Key → ℝ) : Integer.Sparse.eval row7573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck7573, Integer.Sparse.eval_collectBalanced, rawRowCheck7573]

def rawRow7574 : Integer.Sparse Key := [(key2587, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2843, 2), (key2880, 2), (key2966, 2), (key2968, 2), (key2966, 2), (key2989, 2), (key2968, 2), (key2989, 2), (key2598, -2), (key2600, -2), (key2600, -2), (key2887, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2910, -2), (key2995, -2), (key2995, -2), (key3002, -2)]

theorem rawRowCheck7574 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form0 = rawRow7574 := by decide +kernel

def row7574 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

theorem rowCheck7574 : row7574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7574 := by decide +kernel

theorem rowEval7574 (x : Key → ℝ) : Integer.Sparse.eval row7574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7574, Integer.Sparse.eval_collectBalanced, rawRowCheck7574]

def rawRow7575 : Integer.Sparse Key := [(key2587, 2), (key2593, 2), (key2587, 2), (key2843, 2), (key2880, 2), (key2843, 2), (key2968, 2), (key2966, 2), (key2989, 2), (key2966, 2), (key2989, 2), (key2968, 2), (key2600, -2), (key2598, -2), (key2600, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2995, -2), (key3002, -2), (key2995, -2)]

theorem rawRowCheck7575 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form0 = rawRow7575 := by decide +kernel

def row7575 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

theorem rowCheck7575 : row7575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7575 := by decide +kernel

theorem rowEval7575 (x : Key → ℝ) : Integer.Sparse.eval row7575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7575, Integer.Sparse.eval_collectBalanced, rawRowCheck7575]

def rawRow7576 : Integer.Sparse Key := [(key2593, 2), (key2587, 2), (key2587, 2), (key2880, 2), (key2843, 2), (key2843, 2), (key2989, 2), (key2989, 2), (key2968, 2), (key2968, 2), (key2966, 2), (key2966, 2), (key2600, -2), (key2600, -2), (key2598, -2), (key2910, -2), (key2910, -2), (key2889, -2), (key2889, -2), (key2887, -2), (key2887, -2), (key3002, -2), (key2995, -2), (key2995, -2)]

theorem rawRowCheck7576 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form0 = rawRow7576 := by decide +kernel

def row7576 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

theorem rowCheck7576 : row7576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7576 := by decide +kernel

theorem rowEval7576 (x : Key → ℝ) : Integer.Sparse.eval row7576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7576, Integer.Sparse.eval_collectBalanced, rawRowCheck7576]

def rawRow7577 : Integer.Sparse Key := [(key2843, 2), (key2966, 2), (key2968, 2), (key2587, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2880, 2), (key2968, 2), (key2989, 2), (key2887, -2), (key2889, -2), (key2995, -2), (key2598, -2), (key2600, -2), (key2887, -2), (key2910, -2), (key2995, -2), (key3002, -2), (key2600, -2), (key2889, -2), (key2910, -2)]

theorem rawRowCheck7577 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form0 = rawRow7577 := by decide +kernel

def row7577 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

theorem rowCheck7577 : row7577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7577 := by decide +kernel

theorem rowEval7577 (x : Key → ℝ) : Integer.Sparse.eval row7577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7577, Integer.Sparse.eval_collectBalanced, rawRowCheck7577]

def rawRow7578 : Integer.Sparse Key := [(key2843, 2), (key2968, 2), (key2966, 2), (key2587, 2), (key2989, 2), (key2966, 2), (key2593, 2), (key2587, 2), (key2880, 2), (key2843, 2), (key2989, 2), (key2968, 2), (key2889, -2), (key2887, -2), (key2995, -2), (key2600, -2), (key2598, -2), (key2910, -2), (key2887, -2), (key3002, -2), (key2995, -2), (key2600, -2), (key2910, -2), (key2889, -2)]

theorem rawRowCheck7578 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form0 = rawRow7578 := by decide +kernel

def row7578 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

theorem rowCheck7578 : row7578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7578 := by decide +kernel

theorem rowEval7578 (x : Key → ℝ) : Integer.Sparse.eval row7578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7578, Integer.Sparse.eval_collectBalanced, rawRowCheck7578]

def rawRow7579 : Integer.Sparse Key := [(key2966, 2), (key2843, 2), (key2968, 2), (key2966, 2), (key2587, 2), (key2989, 2), (key2843, 2), (key2968, 2), (key2587, 2), (key2989, 2), (key2593, 2), (key2880, 2), (key2887, -2), (key2995, -2), (key2889, -2), (key2887, -2), (key2995, -2), (key2598, -2), (key3002, -2), (key2600, -2), (key2910, -2), (key2889, -2), (key2600, -2), (key2910, -2)]

theorem rawRowCheck7579 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form0 = rawRow7579 := by decide +kernel

def row7579 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

theorem rowCheck7579 : row7579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7579 := by decide +kernel

theorem rowEval7579 (x : Key → ℝ) : Integer.Sparse.eval row7579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7579, Integer.Sparse.eval_collectBalanced, rawRowCheck7579]

def rawRow7580 : Integer.Sparse Key := [(key2966, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2968, 2), (key2843, 2), (key2989, 2), (key2587, 2), (key2880, 2), (key2593, 2), (key2995, -2), (key2887, -2), (key2889, -2), (key2995, -2), (key2887, -2), (key3002, -2), (key2598, -2), (key2910, -2), (key2600, -2), (key2889, -2), (key2910, -2), (key2600, -2)]

theorem rawRowCheck7580 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form0 = rawRow7580 := by decide +kernel

def row7580 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

theorem rowCheck7580 : row7580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7580 := by decide +kernel

theorem rowEval7580 (x : Key → ℝ) : Integer.Sparse.eval row7580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7580, Integer.Sparse.eval_collectBalanced, rawRowCheck7580]

def rawRow7581 : Integer.Sparse Key := [(key2968, 2), (key2843, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2880, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2587, 2), (key2843, 2), (key2889, -2), (key2995, -2), (key2887, -2), (key2910, -2), (key3002, -2), (key2600, -2), (key2995, -2), (key2598, -2), (key2887, -2), (key2910, -2), (key2600, -2), (key2889, -2)]

theorem rawRowCheck7581 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form0 = rawRow7581 := by decide +kernel

def row7581 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

theorem rowCheck7581 : row7581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7581 := by decide +kernel

theorem rowEval7581 (x : Key → ℝ) : Integer.Sparse.eval row7581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7581, Integer.Sparse.eval_collectBalanced, rawRowCheck7581]

def rawRow7582 : Integer.Sparse Key := [(key2968, 2), (key2966, 2), (key2843, 2), (key2989, 2), (key2966, 2), (key2587, 2), (key2989, 2), (key2880, 2), (key2968, 2), (key2593, 2), (key2843, 2), (key2587, 2), (key2995, -2), (key2889, -2), (key2887, -2), (key3002, -2), (key2910, -2), (key2995, -2), (key2600, -2), (key2887, -2), (key2598, -2), (key2910, -2), (key2889, -2), (key2600, -2)]

theorem rawRowCheck7582 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form0 = rawRow7582 := by decide +kernel

def row7582 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

theorem rowCheck7582 : row7582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7582 := by decide +kernel

theorem rowEval7582 (x : Key → ℝ) : Integer.Sparse.eval row7582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7582, Integer.Sparse.eval_collectBalanced, rawRowCheck7582]

def rawRow7583 : Integer.Sparse Key := [(key2880, 2), (key2989, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2968, 2), (key2587, 2), (key2587, 2), (key2843, 2), (key2843, 2), (key2966, 2), (key2966, 2), (key2910, -2), (key2910, -2), (key3002, -2), (key2600, -2), (key2600, -2), (key2889, -2), (key2889, -2), (key2995, -2), (key2995, -2), (key2598, -2), (key2887, -2), (key2887, -2)]

theorem rawRowCheck7583 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form0 = rawRow7583 := by decide +kernel

def row7583 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

theorem rowCheck7583 : row7583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7583 := by decide +kernel

theorem rowEval7583 (x : Key → ℝ) : Integer.Sparse.eval row7583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7583, Integer.Sparse.eval_collectBalanced, rawRowCheck7583]

def rawRow7584 : Integer.Sparse Key := [(key2989, 2), (key2880, 2), (key2989, 2), (key2968, 2), (key2593, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2587, 2), (key2966, 2), (key2587, 2), (key2843, 2), (key2910, -2), (key3002, -2), (key2910, -2), (key2889, -2), (key2995, -2), (key2600, -2), (key2995, -2), (key2600, -2), (key2889, -2), (key2887, -2), (key2598, -2), (key2887, -2)]

theorem rawRowCheck7584 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form0 = rawRow7584 := by decide +kernel

def row7584 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

theorem rowCheck7584 : row7584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7584 := by decide +kernel

theorem rowEval7584 (x : Key → ℝ) : Integer.Sparse.eval row7584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7584, Integer.Sparse.eval_collectBalanced, rawRowCheck7584]

def rawRow7585 : Integer.Sparse Key := [(key2989, 2), (key2989, 2), (key2880, 2), (key2968, 2), (key2968, 2), (key2593, 2), (key2966, 2), (key2843, 2), (key2966, 2), (key2587, 2), (key2843, 2), (key2587, 2), (key3002, -2), (key2910, -2), (key2910, -2), (key2995, -2), (key2889, -2), (key2995, -2), (key2600, -2), (key2889, -2), (key2600, -2), (key2887, -2), (key2887, -2), (key2598, -2)]

theorem rawRowCheck7585 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form0 = rawRow7585 := by decide +kernel

def row7585 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

theorem rowCheck7585 : row7585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7585 := by decide +kernel

theorem rowEval7585 (x : Key → ℝ) : Integer.Sparse.eval row7585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7585, Integer.Sparse.eval_collectBalanced, rawRowCheck7585]

def rawRow7586 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2766, 2), (key2887, 2), (key2910, 2), (key2929, 2), (key2931, 2), (key2966, 2), (key2989, 2), (key2995, 2), (key3002, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

theorem rawRowCheck7586 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form0 = rawRow7586 := by decide +kernel

def row7586 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck7586 : row7586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7586 := by decide +kernel

theorem rowEval7586 (x : Key → ℝ) : Integer.Sparse.eval row7586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7586, Integer.Sparse.eval_collectBalanced, rawRowCheck7586]

def rawRow7587 : Integer.Sparse Key := [(key2378, 2), (key2394, 2), (key2390, 2), (key2766, 2), (key2910, 2), (key2887, 2), (key2931, 2), (key2929, 2), (key2989, 2), (key2966, 2), (key3002, 2), (key2995, 2), (key2593, -2), (key2587, -2), (key2600, -2), (key2772, -2), (key2766, -2), (key2880, -2), (key2843, -2), (key2910, -2), (key2889, -2), (key2931, -2), (key2989, -2), (key2968, -2)]

theorem rawRowCheck7587 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form0 = rawRow7587 := by decide +kernel

def row7587 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck7587 : row7587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7587 := by decide +kernel

theorem rowEval7587 (x : Key → ℝ) : Integer.Sparse.eval row7587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7587, Integer.Sparse.eval_collectBalanced, rawRowCheck7587]

def rawRow7588 : Integer.Sparse Key := [(key2390, 2), (key2378, 2), (key2394, 2), (key2887, 2), (key2766, 2), (key2910, 2), (key2966, 2), (key2995, 2), (key2929, 2), (key3002, 2), (key2931, 2), (key2989, 2), (key2587, -2), (key2600, -2), (key2593, -2), (key2843, -2), (key2889, -2), (key2766, -2), (key2910, -2), (key2772, -2), (key2880, -2), (key2968, -2), (key2931, -2), (key2989, -2)]

theorem rawRowCheck7588 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form0 = rawRow7588 := by decide +kernel

def row7588 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck7588 : row7588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7588 := by decide +kernel

theorem rowEval7588 (x : Key → ℝ) : Integer.Sparse.eval row7588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7588, Integer.Sparse.eval_collectBalanced, rawRowCheck7588]

def rawRow7589 : Integer.Sparse Key := [(key2390, 2), (key2394, 2), (key2378, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2995, 2), (key2966, 2), (key3002, 2), (key2929, 2), (key2989, 2), (key2931, 2), (key2600, -2), (key2587, -2), (key2593, -2), (key2889, -2), (key2843, -2), (key2910, -2), (key2766, -2), (key2880, -2), (key2772, -2), (key2968, -2), (key2989, -2), (key2931, -2)]

theorem rawRowCheck7589 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form0 = rawRow7589 := by decide +kernel

def row7589 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck7589 : row7589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7589 := by decide +kernel

theorem rowEval7589 (x : Key → ℝ) : Integer.Sparse.eval row7589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7589, Integer.Sparse.eval_collectBalanced, rawRowCheck7589]

def rawRow7590 : Integer.Sparse Key := [(key2394, 2), (key2378, 2), (key2390, 2), (key2910, 2), (key2766, 2), (key2887, 2), (key2989, 2), (key3002, 2), (key2931, 2), (key2995, 2), (key2929, 2), (key2966, 2), (key2593, -2), (key2600, -2), (key2587, -2), (key2880, -2), (key2910, -2), (key2772, -2), (key2889, -2), (key2766, -2), (key2843, -2), (key2989, -2), (key2931, -2), (key2968, -2)]

theorem rawRowCheck7590 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form0 = rawRow7590 := by decide +kernel

def row7590 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck7590 : row7590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7590 := by decide +kernel

theorem rowEval7590 (x : Key → ℝ) : Integer.Sparse.eval row7590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7590, Integer.Sparse.eval_collectBalanced, rawRowCheck7590]

def rawRow7591 : Integer.Sparse Key := [(key2394, 2), (key2390, 2), (key2378, 2), (key2910, 2), (key2887, 2), (key2766, 2), (key3002, 2), (key2989, 2), (key2995, 2), (key2931, 2), (key2966, 2), (key2929, 2), (key2600, -2), (key2593, -2), (key2587, -2), (key2910, -2), (key2880, -2), (key2889, -2), (key2772, -2), (key2843, -2), (key2766, -2), (key2989, -2), (key2968, -2), (key2931, -2)]

theorem rawRowCheck7591 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form0 = rawRow7591 := by decide +kernel

def row7591 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck7591 : row7591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7591 := by decide +kernel

theorem rowEval7591 (x : Key → ℝ) : Integer.Sparse.eval row7591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7591, Integer.Sparse.eval_collectBalanced, rawRowCheck7591]

def rawRow7592 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2587, 2), (key2966, 2), (key2989, 2), (key2598, 2), (key2600, 2), (key2887, 2), (key2910, 2), (key2995, 2), (key3002, 2), (key2766, -2), (key2772, -2), (key2931, -2), (key2587, -2), (key2593, -2), (key2843, -2), (key2880, -2), (key2968, -2), (key2989, -2), (key2600, -2), (key2889, -2), (key2910, -2)]

theorem rawRowCheck7592 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form0 = rawRow7592 := by decide +kernel

def row7592 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck7592 : row7592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7592 := by decide +kernel

theorem rowEval7592 (x : Key → ℝ) : Integer.Sparse.eval row7592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7592, Integer.Sparse.eval_collectBalanced, rawRowCheck7592]

def rawRow7593 : Integer.Sparse Key := [(key2406, 2), (key2443, 2), (key2437, 2), (key2587, 2), (key2989, 2), (key2966, 2), (key2600, 2), (key2598, 2), (key2910, 2), (key2887, 2), (key3002, 2), (key2995, 2), (key2772, -2), (key2766, -2), (key2931, -2), (key2593, -2), (key2587, -2), (key2880, -2), (key2843, -2), (key2989, -2), (key2968, -2), (key2600, -2), (key2910, -2), (key2889, -2)]

theorem rawRowCheck7593 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form0 = rawRow7593 := by decide +kernel

def row7593 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck7593 : row7593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7593 := by decide +kernel

theorem rowEval7593 (x : Key → ℝ) : Integer.Sparse.eval row7593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7593, Integer.Sparse.eval_collectBalanced, rawRowCheck7593]

def rawRow7594 : Integer.Sparse Key := [(key2437, 2), (key2406, 2), (key2443, 2), (key2966, 2), (key2587, 2), (key2989, 2), (key2887, 2), (key2995, 2), (key2598, 2), (key3002, 2), (key2600, 2), (key2910, 2), (key2766, -2), (key2931, -2), (key2772, -2), (key2843, -2), (key2968, -2), (key2587, -2), (key2989, -2), (key2593, -2), (key2880, -2), (key2889, -2), (key2600, -2), (key2910, -2)]

theorem rawRowCheck7594 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form0 = rawRow7594 := by decide +kernel

def row7594 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck7594 : row7594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7594 := by decide +kernel

theorem rowEval7594 (x : Key → ℝ) : Integer.Sparse.eval row7594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7594, Integer.Sparse.eval_collectBalanced, rawRowCheck7594]

def rawRow7595 : Integer.Sparse Key := [(key2437, 2), (key2443, 2), (key2406, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2995, 2), (key2887, 2), (key3002, 2), (key2598, 2), (key2910, 2), (key2600, 2), (key2931, -2), (key2766, -2), (key2772, -2), (key2968, -2), (key2843, -2), (key2989, -2), (key2587, -2), (key2880, -2), (key2593, -2), (key2889, -2), (key2910, -2), (key2600, -2)]

theorem rawRowCheck7595 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form0 = rawRow7595 := by decide +kernel

def row7595 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck7595 : row7595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7595 := by decide +kernel

theorem rowEval7595 (x : Key → ℝ) : Integer.Sparse.eval row7595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7595, Integer.Sparse.eval_collectBalanced, rawRowCheck7595]

def rawRow7596 : Integer.Sparse Key := [(key2443, 2), (key2406, 2), (key2437, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2910, 2), (key3002, 2), (key2600, 2), (key2995, 2), (key2598, 2), (key2887, 2), (key2772, -2), (key2931, -2), (key2766, -2), (key2880, -2), (key2989, -2), (key2593, -2), (key2968, -2), (key2587, -2), (key2843, -2), (key2910, -2), (key2600, -2), (key2889, -2)]

theorem rawRowCheck7596 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form0 = rawRow7596 := by decide +kernel

def row7596 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck7596 : row7596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7596 := by decide +kernel

theorem rowEval7596 (x : Key → ℝ) : Integer.Sparse.eval row7596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7596, Integer.Sparse.eval_collectBalanced, rawRowCheck7596]

def rawRow7597 : Integer.Sparse Key := [(key2443, 2), (key2437, 2), (key2406, 2), (key2989, 2), (key2966, 2), (key2587, 2), (key3002, 2), (key2910, 2), (key2995, 2), (key2600, 2), (key2887, 2), (key2598, 2), (key2931, -2), (key2772, -2), (key2766, -2), (key2989, -2), (key2880, -2), (key2968, -2), (key2593, -2), (key2843, -2), (key2587, -2), (key2910, -2), (key2889, -2), (key2600, -2)]

theorem rawRowCheck7597 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form0 = rawRow7597 := by decide +kernel

def row7597 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck7597 : row7597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7597 := by decide +kernel

theorem rowEval7597 (x : Key → ℝ) : Integer.Sparse.eval row7597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7597, Integer.Sparse.eval_collectBalanced, rawRowCheck7597]

def rawRow7598 : Integer.Sparse Key := [(key2480, 2), (key2503, 2), (key2524, 2), (key2390, 2), (key2929, 2), (key3002, 2), (key2587, 2), (key2600, 2), (key2766, 2), (key2910, 2), (key2931, 2), (key2989, 2), (key2843, -2), (key2889, -2), (key2968, -2), (key2587, -2), (key2600, -2), (key2766, -2), (key2910, -2), (key2931, -2), (key2989, -2), (key2593, -2), (key2772, -2), (key2880, -2)]

theorem rawRowCheck7598 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form0 = rawRow7598 := by decide +kernel

def row7598 : Integer.Sparse Key := [(key2390, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2593, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2929, 2), (key2968, -2), (key3002, 2)]

theorem rowCheck7598 : row7598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7598 := by decide +kernel

theorem rowEval7598 (x : Key → ℝ) : Integer.Sparse.eval row7598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7598, Integer.Sparse.eval_collectBalanced, rawRowCheck7598]

def rawRow7599 : Integer.Sparse Key := [(key2480, 2), (key2524, 2), (key2503, 2), (key2390, 2), (key3002, 2), (key2929, 2), (key2600, 2), (key2587, 2), (key2910, 2), (key2766, 2), (key2989, 2), (key2931, 2), (key2889, -2), (key2843, -2), (key2968, -2), (key2600, -2), (key2587, -2), (key2910, -2), (key2766, -2), (key2989, -2), (key2931, -2), (key2593, -2), (key2880, -2), (key2772, -2)]

theorem rawRowCheck7599 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form0 = rawRow7599 := by decide +kernel

def row7599 : Integer.Sparse Key := [(key2390, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2593, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2929, 2), (key2968, -2), (key3002, 2)]

theorem rowCheck7599 : row7599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7599 := by decide +kernel

theorem rowEval7599 (x : Key → ℝ) : Integer.Sparse.eval row7599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7599, Integer.Sparse.eval_collectBalanced, rawRowCheck7599]

def rawRow7600 : Integer.Sparse Key := [(key2503, 2), (key2480, 2), (key2524, 2), (key2437, 2), (key2598, 2), (key3002, 2), (key2766, 2), (key2931, 2), (key2587, 2), (key2989, 2), (key2600, 2), (key2910, 2), (key2843, -2), (key2968, -2), (key2889, -2), (key2766, -2), (key2931, -2), (key2587, -2), (key2989, -2), (key2600, -2), (key2910, -2), (key2772, -2), (key2593, -2), (key2880, -2)]

theorem rawRowCheck7600 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form0 = rawRow7600 := by decide +kernel

def row7600 : Integer.Sparse Key := [(key2437, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2593, -2), (key2598, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2968, -2), (key3002, 2)]

theorem rowCheck7600 : row7600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7600 := by decide +kernel

theorem rowEval7600 (x : Key → ℝ) : Integer.Sparse.eval row7600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7600, Integer.Sparse.eval_collectBalanced, rawRowCheck7600]

def rawRow7601 : Integer.Sparse Key := [(key2503, 2), (key2524, 2), (key2480, 2), (key2437, 2), (key3002, 2), (key2598, 2), (key2931, 2), (key2766, 2), (key2989, 2), (key2587, 2), (key2910, 2), (key2600, 2), (key2968, -2), (key2843, -2), (key2889, -2), (key2931, -2), (key2766, -2), (key2989, -2), (key2587, -2), (key2910, -2), (key2600, -2), (key2772, -2), (key2880, -2), (key2593, -2)]

theorem rawRowCheck7601 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form0 = rawRow7601 := by decide +kernel

def row7601 : Integer.Sparse Key := [(key2437, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2593, -2), (key2598, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2968, -2), (key3002, 2)]

theorem rowCheck7601 : row7601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7601 := by decide +kernel

theorem rowEval7601 (x : Key → ℝ) : Integer.Sparse.eval row7601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7601, Integer.Sparse.eval_collectBalanced, rawRowCheck7601]

def rawRow7602 : Integer.Sparse Key := [(key2524, 2), (key2480, 2), (key2503, 2), (key2580, 2), (key2390, 2), (key2437, 2), (key2910, 2), (key2989, 2), (key2600, 2), (key2931, 2), (key2587, 2), (key2766, 2), (key2889, -2), (key2968, -2), (key2843, -2), (key2910, -2), (key2989, -2), (key2600, -2), (key2931, -2), (key2587, -2), (key2766, -2), (key2880, -2), (key2593, -2), (key2772, -2)]

theorem rawRowCheck7602 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form0 = rawRow7602 := by decide +kernel

def row7602 : Integer.Sparse Key := [(key2390, 2), (key2437, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2580, 2), (key2593, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2968, -2)]

theorem rowCheck7602 : row7602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7602 := by decide +kernel

theorem rowEval7602 (x : Key → ℝ) : Integer.Sparse.eval row7602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7602, Integer.Sparse.eval_collectBalanced, rawRowCheck7602]

def rawRow7603 : Integer.Sparse Key := [(key2524, 2), (key2503, 2), (key2480, 2), (key2580, 2), (key2437, 2), (key2390, 2), (key2989, 2), (key2910, 2), (key2931, 2), (key2600, 2), (key2766, 2), (key2587, 2), (key2968, -2), (key2889, -2), (key2843, -2), (key2989, -2), (key2910, -2), (key2931, -2), (key2600, -2), (key2766, -2), (key2587, -2), (key2880, -2), (key2772, -2), (key2593, -2)]

theorem rawRowCheck7603 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form0 = rawRow7603 := by decide +kernel

def row7603 : Integer.Sparse Key := [(key2390, 2), (key2437, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2580, 2), (key2593, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2968, -2)]

theorem rowCheck7603 : row7603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7603 := by decide +kernel

theorem rowEval7603 (x : Key → ℝ) : Integer.Sparse.eval row7603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7603, Integer.Sparse.eval_collectBalanced, rawRowCheck7603]

def rawRow7604 : Integer.Sparse Key := [(key2571, 2), (key2576, 2), (key2580, 2), (key2394, 2), (key2443, 2), (key2524, 2), (key2378, 2), (key2390, 2), (key2406, 2), (key2480, 2), (key2437, 2), (key2503, 2), (key2880, -2), (key2910, -2), (key2989, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2889, -2), (key2931, -2), (key2968, -2), (key2587, -2), (key2766, -2), (key2843, -2)]

theorem rawRowCheck7604 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form0 = rawRow7604 := by decide +kernel

def row7604 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

theorem rowCheck7604 : row7604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7604 := by decide +kernel

theorem rowEval7604 (x : Key → ℝ) : Integer.Sparse.eval row7604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7604, Integer.Sparse.eval_collectBalanced, rawRowCheck7604]

def rawRow7605 : Integer.Sparse Key := [(key2571, 2), (key2580, 2), (key2576, 2), (key2394, 2), (key2524, 2), (key2443, 2), (key2390, 2), (key2378, 2), (key2480, 2), (key2406, 2), (key2503, 2), (key2437, 2), (key2910, -2), (key2880, -2), (key2989, -2), (key2600, -2), (key2593, -2), (key2889, -2), (key2772, -2), (key2968, -2), (key2931, -2), (key2587, -2), (key2843, -2), (key2766, -2)]

theorem rawRowCheck7605 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form0 = rawRow7605 := by decide +kernel

def row7605 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

theorem rowCheck7605 : row7605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7605 := by decide +kernel

theorem rowEval7605 (x : Key → ℝ) : Integer.Sparse.eval row7605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7605, Integer.Sparse.eval_collectBalanced, rawRowCheck7605]

def rawRow7606 : Integer.Sparse Key := [(key2576, 2), (key2571, 2), (key2580, 2), (key2443, 2), (key2394, 2), (key2524, 2), (key2406, 2), (key2437, 2), (key2378, 2), (key2503, 2), (key2390, 2), (key2480, 2), (key2880, -2), (key2989, -2), (key2910, -2), (key2772, -2), (key2931, -2), (key2593, -2), (key2968, -2), (key2600, -2), (key2889, -2), (key2766, -2), (key2587, -2), (key2843, -2)]

theorem rawRowCheck7606 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form0 = rawRow7606 := by decide +kernel

def row7606 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

theorem rowCheck7606 : row7606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7606 := by decide +kernel

theorem rowEval7606 (x : Key → ℝ) : Integer.Sparse.eval row7606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7606, Integer.Sparse.eval_collectBalanced, rawRowCheck7606]

def rawRow7607 : Integer.Sparse Key := [(key2576, 2), (key2580, 2), (key2571, 2), (key2443, 2), (key2524, 2), (key2394, 2), (key2437, 2), (key2406, 2), (key2503, 2), (key2378, 2), (key2480, 2), (key2390, 2), (key2989, -2), (key2880, -2), (key2910, -2), (key2931, -2), (key2772, -2), (key2968, -2), (key2593, -2), (key2889, -2), (key2600, -2), (key2766, -2), (key2843, -2), (key2587, -2)]

theorem rawRowCheck7607 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form0 = rawRow7607 := by decide +kernel

def row7607 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

theorem rowCheck7607 : row7607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7607 := by decide +kernel

theorem rowEval7607 (x : Key → ℝ) : Integer.Sparse.eval row7607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7607, Integer.Sparse.eval_collectBalanced, rawRowCheck7607]

def rawRow7608 : Integer.Sparse Key := [(key2580, 2), (key2571, 2), (key2576, 2), (key2524, 2), (key2394, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2390, 2), (key2437, 2), (key2378, 2), (key2406, 2), (key2910, -2), (key2989, -2), (key2880, -2), (key2889, -2), (key2968, -2), (key2600, -2), (key2931, -2), (key2593, -2), (key2772, -2), (key2843, -2), (key2587, -2), (key2766, -2)]

theorem rawRowCheck7608 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form0 = rawRow7608 := by decide +kernel

def row7608 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

theorem rowCheck7608 : row7608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7608 := by decide +kernel

theorem rowEval7608 (x : Key → ℝ) : Integer.Sparse.eval row7608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7608, Integer.Sparse.eval_collectBalanced, rawRowCheck7608]

def rawRow7609 : Integer.Sparse Key := [(key2580, 2), (key2576, 2), (key2571, 2), (key2524, 2), (key2443, 2), (key2394, 2), (key2503, 2), (key2480, 2), (key2437, 2), (key2390, 2), (key2406, 2), (key2378, 2), (key2989, -2), (key2910, -2), (key2880, -2), (key2968, -2), (key2889, -2), (key2931, -2), (key2600, -2), (key2772, -2), (key2593, -2), (key2843, -2), (key2766, -2), (key2587, -2)]

theorem rawRowCheck7609 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form0 = rawRow7609 := by decide +kernel

def row7609 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

theorem rowCheck7609 : row7609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7609 := by decide +kernel

theorem rowEval7609 (x : Key → ℝ) : Integer.Sparse.eval row7609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7609, Integer.Sparse.eval_collectBalanced, rawRowCheck7609]

def rawRow7610 : Integer.Sparse Key := [(key1026, -24), (key991, 6), (key1104, 6), (key1104, 6), (key1230, 6)]

theorem rawRowCheck7610 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7610 := by decide +kernel

def row7610 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

theorem rowCheck7610 : row7610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7610 := by decide +kernel

theorem rowEval7610 (x : Key → ℝ) : Integer.Sparse.eval row7610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7610, Integer.Sparse.eval_collectBalanced, rawRowCheck7610]

def rawRow7611 : Integer.Sparse Key := [(key1026, -24), (key991, 6), (key1104, 6), (key1230, 6), (key1104, 6)]

theorem rawRowCheck7611 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7611 := by decide +kernel

def row7611 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

theorem rowCheck7611 : row7611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7611 := by decide +kernel

theorem rowEval7611 (x : Key → ℝ) : Integer.Sparse.eval row7611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7611, Integer.Sparse.eval_collectBalanced, rawRowCheck7611]

def rawRow7612 : Integer.Sparse Key := [(key1026, -24), (key991, 6), (key1230, 6), (key1104, 6), (key1104, 6)]

theorem rawRowCheck7612 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7612 := by decide +kernel

def row7612 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

theorem rowCheck7612 : row7612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7612 := by decide +kernel

theorem rowEval7612 (x : Key → ℝ) : Integer.Sparse.eval row7612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7612, Integer.Sparse.eval_collectBalanced, rawRowCheck7612]

def rawRow7613 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key991, 6), (key1104, 6), (key1230, 6)]

theorem rawRowCheck7613 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form1 = rawRow7613 := by decide +kernel

def row7613 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

theorem rowCheck7613 : row7613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7613 := by decide +kernel

theorem rowEval7613 (x : Key → ℝ) : Integer.Sparse.eval row7613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7613, Integer.Sparse.eval_collectBalanced, rawRowCheck7613]

def rawRow7614 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key991, 6), (key1230, 6), (key1104, 6)]

theorem rawRowCheck7614 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form1 = rawRow7614 := by decide +kernel

def row7614 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

theorem rowCheck7614 : row7614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7614 := by decide +kernel

theorem rowEval7614 (x : Key → ℝ) : Integer.Sparse.eval row7614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7614, Integer.Sparse.eval_collectBalanced, rawRowCheck7614]

def rawRow7615 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key1104, 6), (key991, 6), (key1230, 6)]

theorem rawRowCheck7615 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form1 = rawRow7615 := by decide +kernel

def row7615 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

theorem rowCheck7615 : row7615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7615 := by decide +kernel

theorem rowEval7615 (x : Key → ℝ) : Integer.Sparse.eval row7615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7615, Integer.Sparse.eval_collectBalanced, rawRowCheck7615]

def rawRow7616 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key1104, 6), (key1230, 6), (key991, 6)]

theorem rawRowCheck7616 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form1 = rawRow7616 := by decide +kernel

def row7616 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

theorem rowCheck7616 : row7616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7616 := by decide +kernel

theorem rowEval7616 (x : Key → ℝ) : Integer.Sparse.eval row7616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7616, Integer.Sparse.eval_collectBalanced, rawRowCheck7616]

def rawRow7617 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key1230, 6), (key991, 6), (key1104, 6)]

theorem rawRowCheck7617 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form1 = rawRow7617 := by decide +kernel

def row7617 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

theorem rowCheck7617 : row7617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7617 := by decide +kernel

theorem rowEval7617 (x : Key → ℝ) : Integer.Sparse.eval row7617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7617, Integer.Sparse.eval_collectBalanced, rawRowCheck7617]

def rawRow7618 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key1230, 6), (key1104, 6), (key991, 6)]

theorem rawRowCheck7618 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form1 = rawRow7618 := by decide +kernel

def row7618 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

theorem rowCheck7618 : row7618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7618 := by decide +kernel

theorem rowEval7618 (x : Key → ℝ) : Integer.Sparse.eval row7618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7618, Integer.Sparse.eval_collectBalanced, rawRowCheck7618]

def rawRow7619 : Integer.Sparse Key := [(key1026, -24), (key1230, 6), (key991, 6), (key1104, 6), (key1104, 6)]

theorem rawRowCheck7619 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form1 = rawRow7619 := by decide +kernel

def row7619 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

theorem rowCheck7619 : row7619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7619 := by decide +kernel

theorem rowEval7619 (x : Key → ℝ) : Integer.Sparse.eval row7619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7619, Integer.Sparse.eval_collectBalanced, rawRowCheck7619]

def rawRow7620 : Integer.Sparse Key := [(key1026, -24), (key1230, 6), (key1104, 6), (key991, 6), (key1104, 6)]

theorem rawRowCheck7620 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form1 = rawRow7620 := by decide +kernel

def row7620 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

theorem rowCheck7620 : row7620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7620 := by decide +kernel

theorem rowEval7620 (x : Key → ℝ) : Integer.Sparse.eval row7620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7620, Integer.Sparse.eval_collectBalanced, rawRowCheck7620]

def rawRow7621 : Integer.Sparse Key := [(key1026, -24), (key1230, 6), (key1104, 6), (key1104, 6), (key991, 6)]

theorem rawRowCheck7621 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form1 = rawRow7621 := by decide +kernel

def row7621 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

theorem rowCheck7621 : row7621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7621 := by decide +kernel

theorem rowEval7621 (x : Key → ℝ) : Integer.Sparse.eval row7621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7621, Integer.Sparse.eval_collectBalanced, rawRowCheck7621]

def rawRow7622 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1026, 6), (key1104, 6), (key1230, 6)]

theorem rawRowCheck7622 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form1 = rawRow7622 := by decide +kernel

def row7622 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7622 : row7622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7622 := by decide +kernel

theorem rowEval7622 (x : Key → ℝ) : Integer.Sparse.eval row7622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7622, Integer.Sparse.eval_collectBalanced, rawRowCheck7622]

def rawRow7623 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1026, 6), (key1230, 6), (key1104, 6)]

theorem rawRowCheck7623 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form1 = rawRow7623 := by decide +kernel

def row7623 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7623 : row7623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7623 := by decide +kernel

theorem rowEval7623 (x : Key → ℝ) : Integer.Sparse.eval row7623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7623, Integer.Sparse.eval_collectBalanced, rawRowCheck7623]

def rawRow7624 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1104, 6), (key1026, 6), (key1230, 6)]

theorem rawRowCheck7624 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form1 = rawRow7624 := by decide +kernel

def row7624 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7624 : row7624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7624 := by decide +kernel

theorem rowEval7624 (x : Key → ℝ) : Integer.Sparse.eval row7624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7624, Integer.Sparse.eval_collectBalanced, rawRowCheck7624]

def rawRow7625 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1104, 6), (key1230, 6), (key1026, 6)]

theorem rawRowCheck7625 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form1 = rawRow7625 := by decide +kernel

def row7625 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7625 : row7625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7625 := by decide +kernel

theorem rowEval7625 (x : Key → ℝ) : Integer.Sparse.eval row7625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7625, Integer.Sparse.eval_collectBalanced, rawRowCheck7625]

def rawRow7626 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1230, 6), (key1026, 6), (key1104, 6)]

theorem rawRowCheck7626 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form1 = rawRow7626 := by decide +kernel

def row7626 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7626 : row7626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7626 := by decide +kernel

theorem rowEval7626 (x : Key → ℝ) : Integer.Sparse.eval row7626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7626, Integer.Sparse.eval_collectBalanced, rawRowCheck7626]

def rawRow7627 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1230, 6), (key1104, 6), (key1026, 6)]

theorem rawRowCheck7627 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form1 = rawRow7627 := by decide +kernel

def row7627 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7627 : row7627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7627 := by decide +kernel

theorem rowEval7627 (x : Key → ℝ) : Integer.Sparse.eval row7627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7627, Integer.Sparse.eval_collectBalanced, rawRowCheck7627]

def rawRow7628 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key991, 6), (key1104, 6), (key1230, 6)]

theorem rawRowCheck7628 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form1 = rawRow7628 := by decide +kernel

def row7628 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7628 : row7628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7628 := by decide +kernel

theorem rowEval7628 (x : Key → ℝ) : Integer.Sparse.eval row7628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7628, Integer.Sparse.eval_collectBalanced, rawRowCheck7628]

def rawRow7629 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key991, 6), (key1230, 6), (key1104, 6)]

theorem rawRowCheck7629 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form1 = rawRow7629 := by decide +kernel

def row7629 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7629 : row7629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7629 := by decide +kernel

theorem rowEval7629 (x : Key → ℝ) : Integer.Sparse.eval row7629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7629, Integer.Sparse.eval_collectBalanced, rawRowCheck7629]

def rawRow7630 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key1104, 6), (key991, 6), (key1230, 6)]

theorem rawRowCheck7630 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form1 = rawRow7630 := by decide +kernel

def row7630 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7630 : row7630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7630 := by decide +kernel

theorem rowEval7630 (x : Key → ℝ) : Integer.Sparse.eval row7630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7630, Integer.Sparse.eval_collectBalanced, rawRowCheck7630]

def rawRow7631 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key1104, 6), (key1230, 6), (key991, 6)]

theorem rawRowCheck7631 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form1 = rawRow7631 := by decide +kernel

def row7631 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7631 : row7631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7631 := by decide +kernel

theorem rowEval7631 (x : Key → ℝ) : Integer.Sparse.eval row7631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7631, Integer.Sparse.eval_collectBalanced, rawRowCheck7631]

def rawRow7632 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key1230, 6), (key991, 6), (key1104, 6)]

theorem rawRowCheck7632 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form1 = rawRow7632 := by decide +kernel

def row7632 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7632 : row7632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7632 := by decide +kernel

theorem rowEval7632 (x : Key → ℝ) : Integer.Sparse.eval row7632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7632, Integer.Sparse.eval_collectBalanced, rawRowCheck7632]

def rawRow7633 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key1230, 6), (key1104, 6), (key991, 6)]

theorem rawRowCheck7633 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form1 = rawRow7633 := by decide +kernel

def row7633 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7633 : row7633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7633 := by decide +kernel

theorem rowEval7633 (x : Key → ℝ) : Integer.Sparse.eval row7633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7633, Integer.Sparse.eval_collectBalanced, rawRowCheck7633]

def rawRow7634 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key991, 6), (key1026, 6), (key1230, 6)]

theorem rawRowCheck7634 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form1 = rawRow7634 := by decide +kernel

def row7634 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7634 : row7634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7634 := by decide +kernel

theorem rowEval7634 (x : Key → ℝ) : Integer.Sparse.eval row7634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7634, Integer.Sparse.eval_collectBalanced, rawRowCheck7634]

def rawRow7635 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key991, 6), (key1230, 6), (key1026, 6)]

theorem rawRowCheck7635 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form1 = rawRow7635 := by decide +kernel

def row7635 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7635 : row7635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7635 := by decide +kernel

theorem rowEval7635 (x : Key → ℝ) : Integer.Sparse.eval row7635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7635, Integer.Sparse.eval_collectBalanced, rawRowCheck7635]

def rawRow7636 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key1026, 6), (key991, 6), (key1230, 6)]

theorem rawRowCheck7636 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form1 = rawRow7636 := by decide +kernel

def row7636 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7636 : row7636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7636 := by decide +kernel

theorem rowEval7636 (x : Key → ℝ) : Integer.Sparse.eval row7636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7636, Integer.Sparse.eval_collectBalanced, rawRowCheck7636]

def rawRow7637 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key1026, 6), (key1230, 6), (key991, 6)]

theorem rawRowCheck7637 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form1 = rawRow7637 := by decide +kernel

def row7637 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7637 : row7637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7637 := by decide +kernel

theorem rowEval7637 (x : Key → ℝ) : Integer.Sparse.eval row7637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7637, Integer.Sparse.eval_collectBalanced, rawRowCheck7637]

def rawRow7638 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key1230, 6), (key991, 6), (key1026, 6)]

theorem rawRowCheck7638 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form1 = rawRow7638 := by decide +kernel

def row7638 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7638 : row7638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7638 := by decide +kernel

theorem rowEval7638 (x : Key → ℝ) : Integer.Sparse.eval row7638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7638, Integer.Sparse.eval_collectBalanced, rawRowCheck7638]

def rawRow7639 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key1230, 6), (key1026, 6), (key991, 6)]

theorem rawRowCheck7639 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form1 = rawRow7639 := by decide +kernel

def row7639 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7639 : row7639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7639 := by decide +kernel

theorem rowEval7639 (x : Key → ℝ) : Integer.Sparse.eval row7639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7639, Integer.Sparse.eval_collectBalanced, rawRowCheck7639]

def rawRow7640 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key991, 6), (key1026, 6), (key1104, 6)]

theorem rawRowCheck7640 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form1 = rawRow7640 := by decide +kernel

def row7640 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7640 : row7640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7640 := by decide +kernel

theorem rowEval7640 (x : Key → ℝ) : Integer.Sparse.eval row7640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7640, Integer.Sparse.eval_collectBalanced, rawRowCheck7640]

def rawRow7641 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key991, 6), (key1104, 6), (key1026, 6)]

theorem rawRowCheck7641 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form1 = rawRow7641 := by decide +kernel

def row7641 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7641 : row7641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7641 := by decide +kernel

theorem rowEval7641 (x : Key → ℝ) : Integer.Sparse.eval row7641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7641, Integer.Sparse.eval_collectBalanced, rawRowCheck7641]

def rawRow7642 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key1026, 6), (key991, 6), (key1104, 6)]

theorem rawRowCheck7642 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form1 = rawRow7642 := by decide +kernel

def row7642 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7642 : row7642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7642 := by decide +kernel

theorem rowEval7642 (x : Key → ℝ) : Integer.Sparse.eval row7642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7642, Integer.Sparse.eval_collectBalanced, rawRowCheck7642]

def rawRow7643 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key1026, 6), (key1104, 6), (key991, 6)]

theorem rawRowCheck7643 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form1 = rawRow7643 := by decide +kernel

def row7643 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7643 : row7643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7643 := by decide +kernel

theorem rowEval7643 (x : Key → ℝ) : Integer.Sparse.eval row7643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7643, Integer.Sparse.eval_collectBalanced, rawRowCheck7643]

def rawRow7644 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key1104, 6), (key991, 6), (key1026, 6)]

theorem rawRowCheck7644 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form1 = rawRow7644 := by decide +kernel

def row7644 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7644 : row7644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7644 := by decide +kernel

theorem rowEval7644 (x : Key → ℝ) : Integer.Sparse.eval row7644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7644, Integer.Sparse.eval_collectBalanced, rawRowCheck7644]

def rawRow7645 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key1104, 6), (key1026, 6), (key991, 6)]

theorem rawRowCheck7645 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form1 = rawRow7645 := by decide +kernel

def row7645 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

theorem rowCheck7645 : row7645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7645 := by decide +kernel

theorem rowEval7645 (x : Key → ℝ) : Integer.Sparse.eval row7645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7645, Integer.Sparse.eval_collectBalanced, rawRowCheck7645]

def rawRow7646 : Integer.Sparse Key := [(key1028, -6), (key1036, -6), (key1036, -6), (key1071, -6), (key993, 2), (key1001, 2), (key1001, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1150, 2), (key1150, 2), (key1242, 2)]

theorem rawRowCheck7646 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form2 = rawRow7646 := by decide +kernel

def row7646 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

theorem rowCheck7646 : row7646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7646 := by decide +kernel

theorem rowEval7646 (x : Key → ℝ) : Integer.Sparse.eval row7646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7646, Integer.Sparse.eval_collectBalanced, rawRowCheck7646]

def rawRow7647 : Integer.Sparse Key := [(key1036, -6), (key1028, -6), (key1036, -6), (key1071, -6), (key1001, 2), (key993, 2), (key1001, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1150, 2), (key1242, 2), (key1150, 2)]

theorem rawRowCheck7647 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form2 = rawRow7647 := by decide +kernel

def row7647 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

theorem rowCheck7647 : row7647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7647 := by decide +kernel

theorem rowEval7647 (x : Key → ℝ) : Integer.Sparse.eval row7647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7647, Integer.Sparse.eval_collectBalanced, rawRowCheck7647]

def rawRow7648 : Integer.Sparse Key := [(key1036, -6), (key1036, -6), (key1028, -6), (key1071, -6), (key1001, 2), (key1001, 2), (key993, 2), (key1232, 2), (key1232, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1150, 2)]

theorem rawRowCheck7648 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form2 = rawRow7648 := by decide +kernel

def row7648 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

theorem rowCheck7648 : row7648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7648 := by decide +kernel

theorem rowEval7648 (x : Key → ℝ) : Integer.Sparse.eval row7648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7648, Integer.Sparse.eval_collectBalanced, rawRowCheck7648]

def rawRow7649 : Integer.Sparse Key := [(key1028, -6), (key1036, -6), (key1071, -6), (key1036, -6), (key1106, 2), (key1114, 2), (key1150, 2), (key993, 2), (key1001, 2), (key1106, 2), (key1232, 2), (key1150, 2), (key1242, 2), (key1001, 2), (key1114, 2), (key1232, 2)]

theorem rawRowCheck7649 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form2 = rawRow7649 := by decide +kernel

def row7649 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

theorem rowCheck7649 : row7649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7649 := by decide +kernel

theorem rowEval7649 (x : Key → ℝ) : Integer.Sparse.eval row7649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7649, Integer.Sparse.eval_collectBalanced, rawRowCheck7649]

def rawRow7650 : Integer.Sparse Key := [(key1036, -6), (key1028, -6), (key1071, -6), (key1036, -6), (key1114, 2), (key1106, 2), (key1150, 2), (key1001, 2), (key993, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1001, 2), (key1232, 2), (key1114, 2)]

theorem rawRowCheck7650 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form2 = rawRow7650 := by decide +kernel

def row7650 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

theorem rowCheck7650 : row7650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7650 := by decide +kernel

theorem rowEval7650 (x : Key → ℝ) : Integer.Sparse.eval row7650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7650, Integer.Sparse.eval_collectBalanced, rawRowCheck7650]

def rawRow7651 : Integer.Sparse Key := [(key1028, -6), (key1071, -6), (key1036, -6), (key1036, -6), (key1106, 2), (key1150, 2), (key1114, 2), (key1106, 2), (key1150, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key1114, 2), (key1001, 2), (key1232, 2)]

theorem rawRowCheck7651 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form2 = rawRow7651 := by decide +kernel

def row7651 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

theorem rowCheck7651 : row7651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7651 := by decide +kernel

theorem rowEval7651 (x : Key → ℝ) : Integer.Sparse.eval row7651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7651, Integer.Sparse.eval_collectBalanced, rawRowCheck7651]

def rawRow7652 : Integer.Sparse Key := [(key1071, -6), (key1028, -6), (key1036, -6), (key1036, -6), (key1150, 2), (key1106, 2), (key1114, 2), (key1150, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1232, 2), (key1001, 2), (key1114, 2), (key1232, 2), (key1001, 2)]

theorem rawRowCheck7652 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form2 = rawRow7652 := by decide +kernel

def row7652 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

theorem rowCheck7652 : row7652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7652 := by decide +kernel

theorem rowEval7652 (x : Key → ℝ) : Integer.Sparse.eval row7652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7652, Integer.Sparse.eval_collectBalanced, rawRowCheck7652]

def rawRow7653 : Integer.Sparse Key := [(key1036, -6), (key1071, -6), (key1028, -6), (key1036, -6), (key1114, 2), (key1150, 2), (key1106, 2), (key1232, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key993, 2), (key1106, 2), (key1232, 2), (key1001, 2), (key1114, 2)]

theorem rawRowCheck7653 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form2 = rawRow7653 := by decide +kernel

def row7653 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

theorem rowCheck7653 : row7653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7653 := by decide +kernel

theorem rowEval7653 (x : Key → ℝ) : Integer.Sparse.eval row7653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7653, Integer.Sparse.eval_collectBalanced, rawRowCheck7653]

def rawRow7654 : Integer.Sparse Key := [(key1071, -6), (key1036, -6), (key1028, -6), (key1036, -6), (key1150, 2), (key1114, 2), (key1106, 2), (key1242, 2), (key1232, 2), (key1150, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1232, 2), (key1114, 2), (key1001, 2)]

theorem rawRowCheck7654 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form2 = rawRow7654 := by decide +kernel

def row7654 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

theorem rowCheck7654 : row7654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7654 := by decide +kernel

theorem rowEval7654 (x : Key → ℝ) : Integer.Sparse.eval row7654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7654, Integer.Sparse.eval_collectBalanced, rawRowCheck7654]

def rawRow7655 : Integer.Sparse Key := [(key1036, -6), (key1036, -6), (key1071, -6), (key1028, -6), (key1232, 2), (key1232, 2), (key1242, 2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1150, 2), (key1150, 2), (key993, 2), (key1106, 2), (key1106, 2)]

theorem rawRowCheck7655 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form2 = rawRow7655 := by decide +kernel

def row7655 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

theorem rowCheck7655 : row7655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7655 := by decide +kernel

theorem rowEval7655 (x : Key → ℝ) : Integer.Sparse.eval row7655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7655, Integer.Sparse.eval_collectBalanced, rawRowCheck7655]

def rawRow7656 : Integer.Sparse Key := [(key1036, -6), (key1071, -6), (key1036, -6), (key1028, -6), (key1232, 2), (key1242, 2), (key1232, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1106, 2), (key993, 2), (key1106, 2)]

theorem rawRowCheck7656 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form2 = rawRow7656 := by decide +kernel

def row7656 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

theorem rowCheck7656 : row7656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7656 := by decide +kernel

theorem rowEval7656 (x : Key → ℝ) : Integer.Sparse.eval row7656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7656, Integer.Sparse.eval_collectBalanced, rawRowCheck7656]

def rawRow7657 : Integer.Sparse Key := [(key1071, -6), (key1036, -6), (key1036, -6), (key1028, -6), (key1242, 2), (key1232, 2), (key1232, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1106, 2), (key1106, 2), (key993, 2)]

theorem rawRowCheck7657 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form2 = rawRow7657 := by decide +kernel

def row7657 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

theorem rowCheck7657 : row7657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7657 := by decide +kernel

theorem rowEval7657 (x : Key → ℝ) : Integer.Sparse.eval row7657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7657, Integer.Sparse.eval_collectBalanced, rawRowCheck7657]

def rawRow7658 : Integer.Sparse Key := [(key1106, -6), (key1114, -6), (key1123, -6), (key1150, -6), (key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1106, 2), (key1232, 2), (key1123, 2), (key1235, 2), (key1071, 2), (key1150, 2), (key1242, 2)]

theorem rawRowCheck7658 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form2 = rawRow7658 := by decide +kernel

def row7658 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7658 : row7658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7658 := by decide +kernel

theorem rowEval7658 (x : Key → ℝ) : Integer.Sparse.eval row7658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7658, Integer.Sparse.eval_collectBalanced, rawRowCheck7658]

def rawRow7659 : Integer.Sparse Key := [(key1114, -6), (key1106, -6), (key1123, -6), (key1150, -6), (key1001, 2), (key993, 2), (key1015, 2), (key1036, 2), (key1028, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1071, 2), (key1242, 2), (key1150, 2)]

theorem rawRowCheck7659 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form2 = rawRow7659 := by decide +kernel

def row7659 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7659 : row7659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7659 := by decide +kernel

theorem rowEval7659 (x : Key → ℝ) : Integer.Sparse.eval row7659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7659, Integer.Sparse.eval_collectBalanced, rawRowCheck7659]

def rawRow7660 : Integer.Sparse Key := [(key1106, -6), (key1123, -6), (key1114, -6), (key1150, -6), (key993, 2), (key1015, 2), (key1001, 2), (key1106, 2), (key1123, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1150, 2), (key1071, 2), (key1242, 2)]

theorem rawRowCheck7660 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form2 = rawRow7660 := by decide +kernel

def row7660 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7660 : row7660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7660 := by decide +kernel

theorem rowEval7660 (x : Key → ℝ) : Integer.Sparse.eval row7660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7660, Integer.Sparse.eval_collectBalanced, rawRowCheck7660]

def rawRow7661 : Integer.Sparse Key := [(key1123, -6), (key1106, -6), (key1114, -6), (key1150, -6), (key1015, 2), (key993, 2), (key1001, 2), (key1123, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1232, 2), (key1036, 2), (key1150, 2), (key1242, 2), (key1071, 2)]

theorem rawRowCheck7661 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form2 = rawRow7661 := by decide +kernel

def row7661 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7661 : row7661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7661 := by decide +kernel

theorem rowEval7661 (x : Key → ℝ) : Integer.Sparse.eval row7661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7661, Integer.Sparse.eval_collectBalanced, rawRowCheck7661]

def rawRow7662 : Integer.Sparse Key := [(key1114, -6), (key1123, -6), (key1106, -6), (key1150, -6), (key1001, 2), (key1015, 2), (key993, 2), (key1232, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1028, 2), (key1106, 2), (key1242, 2), (key1071, 2), (key1150, 2)]

theorem rawRowCheck7662 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form2 = rawRow7662 := by decide +kernel

def row7662 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7662 : row7662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7662 := by decide +kernel

theorem rowEval7662 (x : Key → ℝ) : Integer.Sparse.eval row7662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7662, Integer.Sparse.eval_collectBalanced, rawRowCheck7662]

def rawRow7663 : Integer.Sparse Key := [(key1123, -6), (key1114, -6), (key1106, -6), (key1150, -6), (key1015, 2), (key1001, 2), (key993, 2), (key1235, 2), (key1232, 2), (key1123, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1242, 2), (key1150, 2), (key1071, 2)]

theorem rawRowCheck7663 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form2 = rawRow7663 := by decide +kernel

def row7663 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7663 : row7663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7663 := by decide +kernel

theorem rowEval7663 (x : Key → ℝ) : Integer.Sparse.eval row7663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7663, Integer.Sparse.eval_collectBalanced, rawRowCheck7663]

def rawRow7664 : Integer.Sparse Key := [(key1106, -6), (key1114, -6), (key1150, -6), (key1123, -6), (key1028, 2), (key1036, 2), (key1071, 2), (key993, 2), (key1001, 2), (key1106, 2), (key1232, 2), (key1150, 2), (key1242, 2), (key1015, 2), (key1123, 2), (key1235, 2)]

theorem rawRowCheck7664 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form2 = rawRow7664 := by decide +kernel

def row7664 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7664 : row7664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7664 := by decide +kernel

theorem rowEval7664 (x : Key → ℝ) : Integer.Sparse.eval row7664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7664, Integer.Sparse.eval_collectBalanced, rawRowCheck7664]

def rawRow7665 : Integer.Sparse Key := [(key1114, -6), (key1106, -6), (key1150, -6), (key1123, -6), (key1036, 2), (key1028, 2), (key1071, 2), (key1001, 2), (key993, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1015, 2), (key1235, 2), (key1123, 2)]

theorem rawRowCheck7665 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form2 = rawRow7665 := by decide +kernel

def row7665 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7665 : row7665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7665 := by decide +kernel

theorem rowEval7665 (x : Key → ℝ) : Integer.Sparse.eval row7665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7665, Integer.Sparse.eval_collectBalanced, rawRowCheck7665]

def rawRow7666 : Integer.Sparse Key := [(key1106, -6), (key1150, -6), (key1114, -6), (key1123, -6), (key1028, 2), (key1071, 2), (key1036, 2), (key1106, 2), (key1150, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key1123, 2), (key1015, 2), (key1235, 2)]

theorem rawRowCheck7666 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form2 = rawRow7666 := by decide +kernel

def row7666 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7666 : row7666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7666 := by decide +kernel

theorem rowEval7666 (x : Key → ℝ) : Integer.Sparse.eval row7666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7666, Integer.Sparse.eval_collectBalanced, rawRowCheck7666]

def rawRow7667 : Integer.Sparse Key := [(key1150, -6), (key1106, -6), (key1114, -6), (key1123, -6), (key1071, 2), (key1028, 2), (key1036, 2), (key1150, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1232, 2), (key1001, 2), (key1123, 2), (key1235, 2), (key1015, 2)]

theorem rawRowCheck7667 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form2 = rawRow7667 := by decide +kernel

def row7667 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7667 : row7667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7667 := by decide +kernel

theorem rowEval7667 (x : Key → ℝ) : Integer.Sparse.eval row7667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7667, Integer.Sparse.eval_collectBalanced, rawRowCheck7667]

def rawRow7668 : Integer.Sparse Key := [(key1114, -6), (key1150, -6), (key1106, -6), (key1123, -6), (key1036, 2), (key1071, 2), (key1028, 2), (key1232, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key993, 2), (key1106, 2), (key1235, 2), (key1015, 2), (key1123, 2)]

theorem rawRowCheck7668 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form2 = rawRow7668 := by decide +kernel

def row7668 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7668 : row7668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7668 := by decide +kernel

theorem rowEval7668 (x : Key → ℝ) : Integer.Sparse.eval row7668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7668, Integer.Sparse.eval_collectBalanced, rawRowCheck7668]

def rawRow7669 : Integer.Sparse Key := [(key1150, -6), (key1114, -6), (key1106, -6), (key1123, -6), (key1071, 2), (key1036, 2), (key1028, 2), (key1242, 2), (key1232, 2), (key1150, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1235, 2), (key1123, 2), (key1015, 2)]

theorem rawRowCheck7669 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form2 = rawRow7669 := by decide +kernel

def row7669 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7669 : row7669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7669 := by decide +kernel

theorem rowEval7669 (x : Key → ℝ) : Integer.Sparse.eval row7669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7669, Integer.Sparse.eval_collectBalanced, rawRowCheck7669]

def rawRow7670 : Integer.Sparse Key := [(key1106, -6), (key1123, -6), (key1150, -6), (key1114, -6), (key1106, 2), (key1123, 2), (key1150, 2), (key993, 2), (key1015, 2), (key1028, 2), (key1235, 2), (key1071, 2), (key1242, 2), (key1001, 2), (key1036, 2), (key1232, 2)]

theorem rawRowCheck7670 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form2 = rawRow7670 := by decide +kernel

def row7670 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7670 : row7670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7670 := by decide +kernel

theorem rowEval7670 (x : Key → ℝ) : Integer.Sparse.eval row7670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7670, Integer.Sparse.eval_collectBalanced, rawRowCheck7670]

def rawRow7671 : Integer.Sparse Key := [(key1123, -6), (key1106, -6), (key1150, -6), (key1114, -6), (key1123, 2), (key1106, 2), (key1150, 2), (key1015, 2), (key993, 2), (key1235, 2), (key1028, 2), (key1242, 2), (key1071, 2), (key1001, 2), (key1232, 2), (key1036, 2)]

theorem rawRowCheck7671 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form2 = rawRow7671 := by decide +kernel

def row7671 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7671 : row7671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7671 := by decide +kernel

theorem rowEval7671 (x : Key → ℝ) : Integer.Sparse.eval row7671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7671, Integer.Sparse.eval_collectBalanced, rawRowCheck7671]

def rawRow7672 : Integer.Sparse Key := [(key1106, -6), (key1150, -6), (key1123, -6), (key1114, -6), (key1106, 2), (key1150, 2), (key1123, 2), (key1028, 2), (key1071, 2), (key993, 2), (key1242, 2), (key1015, 2), (key1235, 2), (key1036, 2), (key1001, 2), (key1232, 2)]

theorem rawRowCheck7672 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form2 = rawRow7672 := by decide +kernel

def row7672 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7672 : row7672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7672 := by decide +kernel

theorem rowEval7672 (x : Key → ℝ) : Integer.Sparse.eval row7672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7672, Integer.Sparse.eval_collectBalanced, rawRowCheck7672]

def rawRow7673 : Integer.Sparse Key := [(key1150, -6), (key1106, -6), (key1123, -6), (key1114, -6), (key1150, 2), (key1106, 2), (key1123, 2), (key1071, 2), (key1028, 2), (key1242, 2), (key993, 2), (key1235, 2), (key1015, 2), (key1036, 2), (key1232, 2), (key1001, 2)]

theorem rawRowCheck7673 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form2 = rawRow7673 := by decide +kernel

def row7673 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7673 : row7673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7673 := by decide +kernel

theorem rowEval7673 (x : Key → ℝ) : Integer.Sparse.eval row7673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7673, Integer.Sparse.eval_collectBalanced, rawRowCheck7673]

def rawRow7674 : Integer.Sparse Key := [(key1123, -6), (key1150, -6), (key1106, -6), (key1114, -6), (key1123, 2), (key1150, 2), (key1106, 2), (key1235, 2), (key1242, 2), (key1015, 2), (key1071, 2), (key993, 2), (key1028, 2), (key1232, 2), (key1001, 2), (key1036, 2)]

theorem rawRowCheck7674 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form2 = rawRow7674 := by decide +kernel

def row7674 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7674 : row7674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7674 := by decide +kernel

theorem rowEval7674 (x : Key → ℝ) : Integer.Sparse.eval row7674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7674, Integer.Sparse.eval_collectBalanced, rawRowCheck7674]

def rawRow7675 : Integer.Sparse Key := [(key1150, -6), (key1123, -6), (key1106, -6), (key1114, -6), (key1150, 2), (key1123, 2), (key1106, 2), (key1242, 2), (key1235, 2), (key1071, 2), (key1015, 2), (key1028, 2), (key993, 2), (key1232, 2), (key1036, 2), (key1001, 2)]

theorem rawRowCheck7675 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form2 = rawRow7675 := by decide +kernel

def row7675 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7675 : row7675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7675 := by decide +kernel

theorem rowEval7675 (x : Key → ℝ) : Integer.Sparse.eval row7675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7675, Integer.Sparse.eval_collectBalanced, rawRowCheck7675]

def rawRow7676 : Integer.Sparse Key := [(key1114, -6), (key1123, -6), (key1150, -6), (key1106, -6), (key1232, 2), (key1235, 2), (key1242, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1123, 2), (key1071, 2), (key1150, 2), (key993, 2), (key1028, 2), (key1106, 2)]

theorem rawRowCheck7676 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form2 = rawRow7676 := by decide +kernel

def row7676 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7676 : row7676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7676 := by decide +kernel

theorem rowEval7676 (x : Key → ℝ) : Integer.Sparse.eval row7676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7676, Integer.Sparse.eval_collectBalanced, rawRowCheck7676]

def rawRow7677 : Integer.Sparse Key := [(key1123, -6), (key1114, -6), (key1150, -6), (key1106, -6), (key1235, 2), (key1232, 2), (key1242, 2), (key1015, 2), (key1001, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1071, 2), (key993, 2), (key1106, 2), (key1028, 2)]

theorem rawRowCheck7677 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form2 = rawRow7677 := by decide +kernel

def row7677 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7677 : row7677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7677 := by decide +kernel

theorem rowEval7677 (x : Key → ℝ) : Integer.Sparse.eval row7677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7677, Integer.Sparse.eval_collectBalanced, rawRowCheck7677]

def rawRow7678 : Integer.Sparse Key := [(key1114, -6), (key1150, -6), (key1123, -6), (key1106, -6), (key1232, 2), (key1242, 2), (key1235, 2), (key1036, 2), (key1071, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1028, 2), (key993, 2), (key1106, 2)]

theorem rawRowCheck7678 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form2 = rawRow7678 := by decide +kernel

def row7678 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7678 : row7678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7678 := by decide +kernel

theorem rowEval7678 (x : Key → ℝ) : Integer.Sparse.eval row7678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7678, Integer.Sparse.eval_collectBalanced, rawRowCheck7678]

def rawRow7679 : Integer.Sparse Key := [(key1150, -6), (key1114, -6), (key1123, -6), (key1106, -6), (key1242, 2), (key1232, 2), (key1235, 2), (key1071, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1123, 2), (key1015, 2), (key1028, 2), (key1106, 2), (key993, 2)]

theorem rawRowCheck7679 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form2 = rawRow7679 := by decide +kernel

def row7679 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7679 : row7679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7679 := by decide +kernel

theorem rowEval7679 (x : Key → ℝ) : Integer.Sparse.eval row7679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7679, Integer.Sparse.eval_collectBalanced, rawRowCheck7679]

end MUB6.Certificate.GramRows

end OAI
