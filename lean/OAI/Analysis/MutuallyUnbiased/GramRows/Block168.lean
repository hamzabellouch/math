import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
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

def rawRow18432 : Integer.Sparse Key := [(key2359, 6), (key2359, 6), (key2359, 6), (key2353, 6), (key2515, 6), (key2515, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2448, 6), (key2448, 6), (key2578, 6), (key2566, 6), (key2566, 6), (key2566, 6)]

theorem rawRowCheck18432 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18432 := by decide +kernel

def row18432 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

theorem rowCheck18432 : row18432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18432 := by decide +kernel

theorem rowEval18432 (x : Key → ℝ) : Integer.Sparse.eval row18432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18432, Integer.Sparse.eval_collectBalanced, rawRowCheck18432]

def rawRow18433 : Integer.Sparse Key := [(key2448, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2353, 6), (key2359, 6), (key2359, 6), (key2448, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2515, 6), (key2566, 6), (key2566, 6), (key2578, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2515, 6)]

theorem rawRowCheck18433 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form0 = rawRow18433 := by decide +kernel

def row18433 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 24), (key2566, 12), (key2578, 6)]

theorem rowCheck18433 : row18433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18433 := by decide +kernel

theorem rowEval18433 (x : Key → ℝ) : Integer.Sparse.eval row18433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18433, Integer.Sparse.eval_collectBalanced, rawRowCheck18433]

def rawRow18434 : Integer.Sparse Key := [(key2454, 6), (key2448, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2353, 6), (key2359, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2566, 6), (key2578, 6), (key2566, 6), (key2359, 6), (key2454, 6), (key2515, 6), (key2454, 6)]

theorem rawRowCheck18434 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form0 = rawRow18434 := by decide +kernel

def row18434 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 24), (key2566, 12), (key2578, 6)]

theorem rowCheck18434 : row18434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18434 := by decide +kernel

theorem rowEval18434 (x : Key → ℝ) : Integer.Sparse.eval row18434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18434, Integer.Sparse.eval_collectBalanced, rawRowCheck18434]

def rawRow18435 : Integer.Sparse Key := [(key2454, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2359, 6), (key2359, 6), (key2353, 6), (key2515, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2448, 6), (key2578, 6), (key2566, 6), (key2566, 6), (key2359, 6), (key2515, 6), (key2454, 6), (key2454, 6)]

theorem rawRowCheck18435 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form0 = rawRow18435 := by decide +kernel

def row18435 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 24), (key2566, 12), (key2578, 6)]

theorem rowCheck18435 : row18435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18435 := by decide +kernel

theorem rowEval18435 (x : Key → ℝ) : Integer.Sparse.eval row18435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18435, Integer.Sparse.eval_collectBalanced, rawRowCheck18435]

def rawRow18436 : Integer.Sparse Key := [(key2448, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2448, 6), (key2454, 6), (key2515, 6), (key2353, 6), (key2359, 6), (key2448, 6), (key2515, 6), (key2566, 6), (key2578, 6), (key2359, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2359, 6), (key2454, 6), (key2515, 6)]

theorem rawRowCheck18436 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form0 = rawRow18436 := by decide +kernel

def row18436 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 30), (key2566, 6), (key2578, 6)]

theorem rowCheck18436 : row18436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18436 := by decide +kernel

theorem rowEval18436 (x : Key → ℝ) : Integer.Sparse.eval row18436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18436, Integer.Sparse.eval_collectBalanced, rawRowCheck18436]

def rawRow18437 : Integer.Sparse Key := [(key2454, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2359, 6), (key2353, 6), (key2515, 6), (key2448, 6), (key2578, 6), (key2566, 6), (key2359, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2359, 6), (key2515, 6), (key2454, 6)]

theorem rawRowCheck18437 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form0 = rawRow18437 := by decide +kernel

def row18437 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 30), (key2566, 6), (key2578, 6)]

theorem rowCheck18437 : row18437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18437 := by decide +kernel

theorem rowEval18437 (x : Key → ℝ) : Integer.Sparse.eval row18437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18437, Integer.Sparse.eval_collectBalanced, rawRowCheck18437]

def rawRow18438 : Integer.Sparse Key := [(key2448, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2353, 6), (key2578, 6), (key2359, 6), (key2515, 6), (key2454, 6), (key2359, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2359, 6), (key2515, 6)]

theorem rawRowCheck18438 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form0 = rawRow18438 := by decide +kernel

def row18438 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 36), (key2578, 6)]

theorem rowCheck18438 : row18438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18438 := by decide +kernel

theorem rowEval18438 (x : Key → ℝ) : Integer.Sparse.eval row18438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18438, Integer.Sparse.eval_collectBalanced, rawRowCheck18438]

def rawRow18439 : Integer.Sparse Key := [(key2515, 6), (key2448, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2448, 6), (key2454, 6), (key2515, 6), (key2448, 6), (key2578, 6), (key2353, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2359, 6)]

theorem rawRowCheck18439 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form0 = rawRow18439 := by decide +kernel

def row18439 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 36), (key2578, 6)]

theorem rowCheck18439 : row18439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18439 := by decide +kernel

theorem rowEval18439 (x : Key → ℝ) : Integer.Sparse.eval row18439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18439, Integer.Sparse.eval_collectBalanced, rawRowCheck18439]

def rawRow18440 : Integer.Sparse Key := [(key2454, 6), (key2515, 6), (key2448, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2448, 6), (key2566, 6), (key2578, 6), (key2359, 6), (key2515, 6), (key2353, 6), (key2448, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2454, 6)]

theorem rawRowCheck18440 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form0 = rawRow18440 := by decide +kernel

def row18440 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 30), (key2566, 6), (key2578, 6)]

theorem rowCheck18440 : row18440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18440 := by decide +kernel

theorem rowEval18440 (x : Key → ℝ) : Integer.Sparse.eval row18440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18440, Integer.Sparse.eval_collectBalanced, rawRowCheck18440]

def rawRow18441 : Integer.Sparse Key := [(key2515, 6), (key2454, 6), (key2448, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2448, 6), (key2578, 6), (key2566, 6), (key2515, 6), (key2359, 6), (key2448, 6), (key2353, 6), (key2515, 6), (key2454, 6), (key2359, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2359, 6)]

theorem rawRowCheck18441 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form0 = rawRow18441 := by decide +kernel

def row18441 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 30), (key2566, 6), (key2578, 6)]

theorem rowCheck18441 : row18441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18441 := by decide +kernel

theorem rowEval18441 (x : Key → ℝ) : Integer.Sparse.eval row18441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18441, Integer.Sparse.eval_collectBalanced, rawRowCheck18441]

def rawRow18442 : Integer.Sparse Key := [(key2454, 6), (key2454, 6), (key2515, 6), (key2448, 6), (key2566, 6), (key2566, 6), (key2578, 6), (key2359, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2515, 6), (key2353, 6), (key2448, 6), (key2448, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2454, 6)]

theorem rawRowCheck18442 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18442 := by decide +kernel

def row18442 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 24), (key2566, 12), (key2578, 6)]

theorem rowCheck18442 : row18442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18442 := by decide +kernel

theorem rowEval18442 (x : Key → ℝ) : Integer.Sparse.eval row18442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18442, Integer.Sparse.eval_collectBalanced, rawRowCheck18442]

def rawRow18443 : Integer.Sparse Key := [(key2454, 6), (key2515, 6), (key2454, 6), (key2448, 6), (key2566, 6), (key2578, 6), (key2566, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2448, 6), (key2353, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2359, 6), (key2454, 6)]

theorem rawRowCheck18443 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18443 := by decide +kernel

def row18443 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 24), (key2566, 12), (key2578, 6)]

theorem rowCheck18443 : row18443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18443 := by decide +kernel

theorem rowEval18443 (x : Key → ℝ) : Integer.Sparse.eval row18443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18443, Integer.Sparse.eval_collectBalanced, rawRowCheck18443]

def rawRow18444 : Integer.Sparse Key := [(key2515, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2578, 6), (key2566, 6), (key2566, 6), (key2515, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2359, 6), (key2448, 6), (key2448, 6), (key2353, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2359, 6)]

theorem rawRowCheck18444 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18444 := by decide +kernel

def row18444 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 24), (key2566, 12), (key2578, 6)]

theorem rowCheck18444 : row18444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18444 := by decide +kernel

theorem rowEval18444 (x : Key → ℝ) : Integer.Sparse.eval row18444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18444, Integer.Sparse.eval_collectBalanced, rawRowCheck18444]

def rawRow18445 : Integer.Sparse Key := [(key2566, 6), (key2566, 6), (key2566, 6), (key2578, 6), (key2359, 6), (key2359, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2515, 6), (key2515, 6), (key2353, 6), (key2448, 6), (key2448, 6), (key2448, 6)]

theorem rawRowCheck18445 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18445 := by decide +kernel

def row18445 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

theorem rowCheck18445 : row18445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18445 := by decide +kernel

theorem rowEval18445 (x : Key → ℝ) : Integer.Sparse.eval row18445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18445, Integer.Sparse.eval_collectBalanced, rawRowCheck18445]

def rawRow18446 : Integer.Sparse Key := [(key2566, 6), (key2566, 6), (key2578, 6), (key2566, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2353, 6), (key2448, 6), (key2448, 6)]

theorem rawRowCheck18446 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18446 := by decide +kernel

def row18446 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

theorem rowCheck18446 : row18446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18446 := by decide +kernel

theorem rowEval18446 (x : Key → ℝ) : Integer.Sparse.eval row18446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18446, Integer.Sparse.eval_collectBalanced, rawRowCheck18446]

def rawRow18447 : Integer.Sparse Key := [(key2566, 6), (key2578, 6), (key2566, 6), (key2566, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2359, 6), (key2454, 6), (key2448, 6), (key2448, 6), (key2353, 6), (key2448, 6)]

theorem rawRowCheck18447 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18447 := by decide +kernel

def row18447 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

theorem rowCheck18447 : row18447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18447 := by decide +kernel

theorem rowEval18447 (x : Key → ℝ) : Integer.Sparse.eval row18447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18447, Integer.Sparse.eval_collectBalanced, rawRowCheck18447]

def rawRow18448 : Integer.Sparse Key := [(key2578, 6), (key2566, 6), (key2566, 6), (key2566, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2359, 6), (key2448, 6), (key2448, 6), (key2448, 6), (key2353, 6)]

theorem rawRowCheck18448 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18448 := by decide +kernel

def row18448 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

theorem rowCheck18448 : row18448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18448 := by decide +kernel

theorem rowEval18448 (x : Key → ℝ) : Integer.Sparse.eval row18448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18448, Integer.Sparse.eval_collectBalanced, rawRowCheck18448]

def rawRow18449 : Integer.Sparse Key := [(key970, 6), (key970, 6), (key970, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1226, 6), (key1226, 6), (key1226, 6)]

theorem rawRowCheck18449 : GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18449 := by decide +kernel

def row18449 : Integer.Sparse Key := [(key970, 24), (key1084, 72), (key1226, 24)]

theorem rowCheck18449 : row18449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18449 := by decide +kernel

theorem rowEval18449 (x : Key → ℝ) : Integer.Sparse.eval row18449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18449, Integer.Sparse.eval_collectBalanced, rawRowCheck18449]

def rawRow18450 : Integer.Sparse Key := [(key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key970, 6), (key970, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1226, 6), (key1226, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6)]

theorem rawRowCheck18450 : GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18450 := by decide +kernel

def row18450 : Integer.Sparse Key := [(key970, 24), (key1084, 72), (key1226, 24)]

theorem rowCheck18450 : row18450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18450 := by decide +kernel

theorem rowEval18450 (x : Key → ℝ) : Integer.Sparse.eval row18450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18450, Integer.Sparse.eval_collectBalanced, rawRowCheck18450]

def rawRow18451 : Integer.Sparse Key := [(key1084, 6), (key1084, 6), (key1226, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key970, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1226, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key970, 6), (key1084, 6), (key1084, 6)]

theorem rawRowCheck18451 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18451 := by decide +kernel

def row18451 : Integer.Sparse Key := [(key970, 24), (key1084, 72), (key1226, 24)]

theorem rowCheck18451 : row18451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18451 := by decide +kernel

theorem rowEval18451 (x : Key → ℝ) : Integer.Sparse.eval row18451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18451, Integer.Sparse.eval_collectBalanced, rawRowCheck18451]

def rawRow18452 : Integer.Sparse Key := [(key1084, 6), (key1226, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key970, 6), (key1226, 6), (key970, 6), (key1084, 6), (key1084, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key970, 6), (key1084, 6)]

theorem rawRowCheck18452 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18452 := by decide +kernel

def row18452 : Integer.Sparse Key := [(key970, 24), (key1084, 72), (key1226, 24)]

theorem rowCheck18452 : row18452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18452 := by decide +kernel

theorem rowEval18452 (x : Key → ℝ) : Integer.Sparse.eval row18452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18452, Integer.Sparse.eval_collectBalanced, rawRowCheck18452]

def rawRow18453 : Integer.Sparse Key := [(key1226, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1084, 6), (key1226, 6), (key970, 6), (key1084, 6), (key970, 6), (key1084, 6), (key1084, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key970, 6)]

theorem rawRowCheck18453 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18453 := by decide +kernel

def row18453 : Integer.Sparse Key := [(key970, 24), (key1084, 72), (key1226, 24)]

theorem rowCheck18453 : row18453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18453 := by decide +kernel

theorem rowEval18453 (x : Key → ℝ) : Integer.Sparse.eval row18453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18453, Integer.Sparse.eval_collectBalanced, rawRowCheck18453]

def rawRow18454 : Integer.Sparse Key := [(key0, 24), (key83, 24), (key83, 24), (key83, 24), (key83, 24)]

theorem rawRowCheck18454 : GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18454 := by decide +kernel

def row18454 : Integer.Sparse Key := [(key0, 24), (key83, 96)]

theorem rowCheck18454 : row18454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18454 := by decide +kernel

theorem rowEval18454 (x : Key → ℝ) : Integer.Sparse.eval row18454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18454, Integer.Sparse.eval_collectBalanced, rawRowCheck18454]

def rawRow18455 : Integer.Sparse Key := [(key83, 24), (key0, 24), (key83, 24), (key83, 24), (key83, 24)]

theorem rawRowCheck18455 : GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18455 := by decide +kernel

def row18455 : Integer.Sparse Key := [(key0, 24), (key83, 96)]

theorem rowCheck18455 : row18455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18455 := by decide +kernel

theorem rowEval18455 (x : Key → ℝ) : Integer.Sparse.eval row18455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18455, Integer.Sparse.eval_collectBalanced, rawRowCheck18455]

def rawRow18456 : Integer.Sparse Key := [(key83, 24), (key83, 24), (key0, 24), (key83, 24), (key83, 24)]

theorem rawRowCheck18456 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18456 := by decide +kernel

def row18456 : Integer.Sparse Key := [(key0, 24), (key83, 96)]

theorem rowCheck18456 : row18456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18456 := by decide +kernel

theorem rowEval18456 (x : Key → ℝ) : Integer.Sparse.eval row18456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18456, Integer.Sparse.eval_collectBalanced, rawRowCheck18456]

def rawRow18457 : Integer.Sparse Key := [(key83, 24), (key83, 24), (key83, 24), (key0, 24), (key83, 24)]

theorem rawRowCheck18457 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18457 := by decide +kernel

def row18457 : Integer.Sparse Key := [(key0, 24), (key83, 96)]

theorem rowCheck18457 : row18457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18457 := by decide +kernel

theorem rowEval18457 (x : Key → ℝ) : Integer.Sparse.eval row18457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18457, Integer.Sparse.eval_collectBalanced, rawRowCheck18457]

def rawRow18458 : Integer.Sparse Key := [(key83, 24), (key83, 24), (key83, 24), (key83, 24), (key0, 24)]

theorem rawRowCheck18458 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18458 := by decide +kernel

def row18458 : Integer.Sparse Key := [(key0, 24), (key83, 96)]

theorem rowCheck18458 : row18458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18458 := by decide +kernel

theorem rowEval18458 (x : Key → ℝ) : Integer.Sparse.eval row18458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18458, Integer.Sparse.eval_collectBalanced, rawRowCheck18458]

def rawRow18459 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2376, 6), (key2388, 6), (key2762, 6), (key2768, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2839, 6), (key2876, 6), (key2845, 6), (key2876, 6), (key2916, 6), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3019, 6), (key3028, 6)]

theorem rawRowCheck18459 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form0 = rawRow18459 := by decide +kernel

def row18459 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18459 : row18459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18459 := by decide +kernel

theorem rowEval18459 (x : Key → ℝ) : Integer.Sparse.eval row18459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18459, Integer.Sparse.eval_collectBalanced, rawRowCheck18459]

def rawRow18460 : Integer.Sparse Key := [(key2376, 6), (key2370, 6), (key2376, 6), (key2388, 6), (key2768, 6), (key2762, 6), (key2768, 6), (key2845, 6), (key2839, 6), (key2876, 6), (key2839, 6), (key2876, 6), (key2845, 6), (key2916, 6), (key2925, 6), (key2916, 6), (key3005, 6), (key3019, 6), (key3028, 6), (key3019, 6)]

theorem rawRowCheck18460 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form0 = rawRow18460 := by decide +kernel

def row18460 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18460 : row18460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18460 := by decide +kernel

theorem rowEval18460 (x : Key → ℝ) : Integer.Sparse.eval row18460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18460, Integer.Sparse.eval_collectBalanced, rawRowCheck18460]

def rawRow18461 : Integer.Sparse Key := [(key2376, 6), (key2376, 6), (key2370, 6), (key2388, 6), (key2768, 6), (key2768, 6), (key2762, 6), (key2876, 6), (key2876, 6), (key2845, 6), (key2845, 6), (key2839, 6), (key2839, 6), (key2925, 6), (key2916, 6), (key2916, 6), (key3005, 6), (key3028, 6), (key3019, 6), (key3019, 6)]

theorem rawRowCheck18461 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form0 = rawRow18461 := by decide +kernel

def row18461 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18461 : row18461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18461 := by decide +kernel

theorem rowEval18461 (x : Key → ℝ) : Integer.Sparse.eval row18461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18461, Integer.Sparse.eval_collectBalanced, rawRowCheck18461]

def rawRow18462 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2376, 6), (key2839, 6), (key2845, 6), (key2916, 6), (key2762, 6), (key2768, 6), (key2839, 6), (key2876, 6), (key2916, 6), (key2925, 6), (key2768, 6), (key2845, 6), (key2876, 6), (key3019, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

theorem rawRowCheck18462 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form0 = rawRow18462 := by decide +kernel

def row18462 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18462 : row18462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18462 := by decide +kernel

theorem rowEval18462 (x : Key → ℝ) : Integer.Sparse.eval row18462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18462, Integer.Sparse.eval_collectBalanced, rawRowCheck18462]

def rawRow18463 : Integer.Sparse Key := [(key2376, 6), (key2370, 6), (key2388, 6), (key2376, 6), (key2845, 6), (key2839, 6), (key2916, 6), (key2768, 6), (key2762, 6), (key2876, 6), (key2839, 6), (key2925, 6), (key2916, 6), (key2768, 6), (key2876, 6), (key2845, 6), (key3019, 6), (key3005, 6), (key3028, 6), (key3019, 6)]

theorem rawRowCheck18463 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form0 = rawRow18463 := by decide +kernel

def row18463 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18463 : row18463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18463 := by decide +kernel

theorem rowEval18463 (x : Key → ℝ) : Integer.Sparse.eval row18463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18463, Integer.Sparse.eval_collectBalanced, rawRowCheck18463]

def rawRow18464 : Integer.Sparse Key := [(key2370, 6), (key2388, 6), (key2376, 6), (key2376, 6), (key2839, 6), (key2916, 6), (key2845, 6), (key2839, 6), (key2916, 6), (key2762, 6), (key2925, 6), (key2768, 6), (key2876, 6), (key2845, 6), (key2768, 6), (key2876, 6), (key3019, 6), (key3019, 6), (key3005, 6), (key3028, 6)]

theorem rawRowCheck18464 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form0 = rawRow18464 := by decide +kernel

def row18464 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18464 : row18464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18464 := by decide +kernel

theorem rowEval18464 (x : Key → ℝ) : Integer.Sparse.eval row18464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18464, Integer.Sparse.eval_collectBalanced, rawRowCheck18464]

def rawRow18465 : Integer.Sparse Key := [(key2388, 6), (key2370, 6), (key2376, 6), (key2376, 6), (key2916, 6), (key2839, 6), (key2845, 6), (key2916, 6), (key2839, 6), (key2925, 6), (key2762, 6), (key2876, 6), (key2768, 6), (key2845, 6), (key2876, 6), (key2768, 6), (key3019, 6), (key3019, 6), (key3028, 6), (key3005, 6)]

theorem rawRowCheck18465 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form0 = rawRow18465 := by decide +kernel

def row18465 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18465 : row18465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18465 := by decide +kernel

theorem rowEval18465 (x : Key → ℝ) : Integer.Sparse.eval row18465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18465, Integer.Sparse.eval_collectBalanced, rawRowCheck18465]

def rawRow18466 : Integer.Sparse Key := [(key2376, 6), (key2388, 6), (key2370, 6), (key2376, 6), (key2845, 6), (key2916, 6), (key2839, 6), (key2876, 6), (key2925, 6), (key2768, 6), (key2916, 6), (key2762, 6), (key2839, 6), (key2876, 6), (key2768, 6), (key2845, 6), (key3019, 6), (key3028, 6), (key3005, 6), (key3019, 6)]

theorem rawRowCheck18466 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form0 = rawRow18466 := by decide +kernel

def row18466 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18466 : row18466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18466 := by decide +kernel

theorem rowEval18466 (x : Key → ℝ) : Integer.Sparse.eval row18466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18466, Integer.Sparse.eval_collectBalanced, rawRowCheck18466]

def rawRow18467 : Integer.Sparse Key := [(key2388, 6), (key2376, 6), (key2370, 6), (key2376, 6), (key2916, 6), (key2845, 6), (key2839, 6), (key2925, 6), (key2876, 6), (key2916, 6), (key2768, 6), (key2839, 6), (key2762, 6), (key2876, 6), (key2845, 6), (key2768, 6), (key3019, 6), (key3028, 6), (key3019, 6), (key3005, 6)]

theorem rawRowCheck18467 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form0 = rawRow18467 := by decide +kernel

def row18467 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18467 : row18467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18467 := by decide +kernel

theorem rowEval18467 (x : Key → ℝ) : Integer.Sparse.eval row18467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18467, Integer.Sparse.eval_collectBalanced, rawRowCheck18467]

def rawRow18468 : Integer.Sparse Key := [(key2376, 6), (key2376, 6), (key2388, 6), (key2370, 6), (key2876, 6), (key2876, 6), (key2925, 6), (key2768, 6), (key2768, 6), (key2845, 6), (key2845, 6), (key2916, 6), (key2916, 6), (key2762, 6), (key2839, 6), (key2839, 6), (key3028, 6), (key3005, 6), (key3019, 6), (key3019, 6)]

theorem rawRowCheck18468 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form0 = rawRow18468 := by decide +kernel

def row18468 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18468 : row18468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18468 := by decide +kernel

theorem rowEval18468 (x : Key → ℝ) : Integer.Sparse.eval row18468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18468, Integer.Sparse.eval_collectBalanced, rawRowCheck18468]

def rawRow18469 : Integer.Sparse Key := [(key2376, 6), (key2388, 6), (key2376, 6), (key2370, 6), (key2876, 6), (key2925, 6), (key2876, 6), (key2845, 6), (key2916, 6), (key2768, 6), (key2916, 6), (key2768, 6), (key2845, 6), (key2839, 6), (key2762, 6), (key2839, 6), (key3028, 6), (key3019, 6), (key3005, 6), (key3019, 6)]

theorem rawRowCheck18469 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form0 = rawRow18469 := by decide +kernel

def row18469 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18469 : row18469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18469 := by decide +kernel

theorem rowEval18469 (x : Key → ℝ) : Integer.Sparse.eval row18469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18469, Integer.Sparse.eval_collectBalanced, rawRowCheck18469]

def rawRow18470 : Integer.Sparse Key := [(key2388, 6), (key2376, 6), (key2376, 6), (key2370, 6), (key2925, 6), (key2876, 6), (key2876, 6), (key2916, 6), (key2845, 6), (key2916, 6), (key2768, 6), (key2845, 6), (key2768, 6), (key2839, 6), (key2839, 6), (key2762, 6), (key3028, 6), (key3019, 6), (key3019, 6), (key3005, 6)]

theorem rawRowCheck18470 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form0 = rawRow18470 := by decide +kernel

def row18470 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18470 : row18470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18470 := by decide +kernel

theorem rowEval18470 (x : Key → ℝ) : Integer.Sparse.eval row18470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18470, Integer.Sparse.eval_collectBalanced, rawRowCheck18470]

def rawRow18471 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2404, 6), (key2435, 6), (key2583, 6), (key2589, 6), (key2589, 6), (key2839, 6), (key2845, 6), (key2839, 6), (key2876, 6), (key2845, 6), (key2876, 6), (key3019, 6), (key3019, 6), (key3028, 6), (key2604, 6), (key2916, 6), (key2916, 6), (key2925, 6)]

theorem rawRowCheck18471 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form0 = rawRow18471 := by decide +kernel

def row18471 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18471 : row18471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18471 := by decide +kernel

theorem rowEval18471 (x : Key → ℝ) : Integer.Sparse.eval row18471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18471, Integer.Sparse.eval_collectBalanced, rawRowCheck18471]

def rawRow18472 : Integer.Sparse Key := [(key2404, 6), (key2398, 6), (key2404, 6), (key2435, 6), (key2589, 6), (key2583, 6), (key2589, 6), (key2845, 6), (key2839, 6), (key2876, 6), (key2839, 6), (key2876, 6), (key2845, 6), (key3019, 6), (key3028, 6), (key3019, 6), (key2604, 6), (key2916, 6), (key2925, 6), (key2916, 6)]

theorem rawRowCheck18472 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form0 = rawRow18472 := by decide +kernel

def row18472 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18472 : row18472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18472 := by decide +kernel

theorem rowEval18472 (x : Key → ℝ) : Integer.Sparse.eval row18472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18472, Integer.Sparse.eval_collectBalanced, rawRowCheck18472]

def rawRow18473 : Integer.Sparse Key := [(key2404, 6), (key2404, 6), (key2398, 6), (key2435, 6), (key2589, 6), (key2589, 6), (key2583, 6), (key2876, 6), (key2876, 6), (key2845, 6), (key2845, 6), (key2839, 6), (key2839, 6), (key3028, 6), (key3019, 6), (key3019, 6), (key2604, 6), (key2925, 6), (key2916, 6), (key2916, 6)]

theorem rawRowCheck18473 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form0 = rawRow18473 := by decide +kernel

def row18473 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18473 : row18473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18473 := by decide +kernel

theorem rowEval18473 (x : Key → ℝ) : Integer.Sparse.eval row18473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18473, Integer.Sparse.eval_collectBalanced, rawRowCheck18473]

def rawRow18474 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2404, 6), (key2839, 6), (key2845, 6), (key3019, 6), (key2583, 6), (key2589, 6), (key2839, 6), (key2876, 6), (key3019, 6), (key3028, 6), (key2589, 6), (key2845, 6), (key2876, 6), (key2916, 6), (key2604, 6), (key2916, 6), (key2925, 6)]

theorem rawRowCheck18474 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form0 = rawRow18474 := by decide +kernel

def row18474 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18474 : row18474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18474 := by decide +kernel

theorem rowEval18474 (x : Key → ℝ) : Integer.Sparse.eval row18474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18474, Integer.Sparse.eval_collectBalanced, rawRowCheck18474]

def rawRow18475 : Integer.Sparse Key := [(key2404, 6), (key2398, 6), (key2435, 6), (key2404, 6), (key2845, 6), (key2839, 6), (key3019, 6), (key2589, 6), (key2583, 6), (key2876, 6), (key2839, 6), (key3028, 6), (key3019, 6), (key2589, 6), (key2876, 6), (key2845, 6), (key2916, 6), (key2604, 6), (key2925, 6), (key2916, 6)]

theorem rawRowCheck18475 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form0 = rawRow18475 := by decide +kernel

def row18475 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18475 : row18475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18475 := by decide +kernel

theorem rowEval18475 (x : Key → ℝ) : Integer.Sparse.eval row18475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18475, Integer.Sparse.eval_collectBalanced, rawRowCheck18475]

def rawRow18476 : Integer.Sparse Key := [(key2398, 6), (key2435, 6), (key2404, 6), (key2404, 6), (key2839, 6), (key3019, 6), (key2845, 6), (key2839, 6), (key3019, 6), (key2583, 6), (key3028, 6), (key2589, 6), (key2876, 6), (key2845, 6), (key2589, 6), (key2876, 6), (key2916, 6), (key2916, 6), (key2604, 6), (key2925, 6)]

theorem rawRowCheck18476 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form0 = rawRow18476 := by decide +kernel

def row18476 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18476 : row18476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18476 := by decide +kernel

theorem rowEval18476 (x : Key → ℝ) : Integer.Sparse.eval row18476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18476, Integer.Sparse.eval_collectBalanced, rawRowCheck18476]

def rawRow18477 : Integer.Sparse Key := [(key2435, 6), (key2398, 6), (key2404, 6), (key2404, 6), (key3019, 6), (key2839, 6), (key2845, 6), (key3019, 6), (key2839, 6), (key3028, 6), (key2583, 6), (key2876, 6), (key2589, 6), (key2845, 6), (key2876, 6), (key2589, 6), (key2916, 6), (key2916, 6), (key2925, 6), (key2604, 6)]

theorem rawRowCheck18477 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form0 = rawRow18477 := by decide +kernel

def row18477 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18477 : row18477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18477 := by decide +kernel

theorem rowEval18477 (x : Key → ℝ) : Integer.Sparse.eval row18477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18477, Integer.Sparse.eval_collectBalanced, rawRowCheck18477]

def rawRow18478 : Integer.Sparse Key := [(key2404, 6), (key2435, 6), (key2398, 6), (key2404, 6), (key2845, 6), (key3019, 6), (key2839, 6), (key2876, 6), (key3028, 6), (key2589, 6), (key3019, 6), (key2583, 6), (key2839, 6), (key2876, 6), (key2589, 6), (key2845, 6), (key2916, 6), (key2925, 6), (key2604, 6), (key2916, 6)]

theorem rawRowCheck18478 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form0 = rawRow18478 := by decide +kernel

def row18478 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18478 : row18478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18478 := by decide +kernel

theorem rowEval18478 (x : Key → ℝ) : Integer.Sparse.eval row18478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18478, Integer.Sparse.eval_collectBalanced, rawRowCheck18478]

def rawRow18479 : Integer.Sparse Key := [(key2435, 6), (key2404, 6), (key2398, 6), (key2404, 6), (key3019, 6), (key2845, 6), (key2839, 6), (key3028, 6), (key2876, 6), (key3019, 6), (key2589, 6), (key2839, 6), (key2583, 6), (key2876, 6), (key2845, 6), (key2589, 6), (key2916, 6), (key2925, 6), (key2916, 6), (key2604, 6)]

theorem rawRowCheck18479 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form0 = rawRow18479 := by decide +kernel

def row18479 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18479 : row18479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18479 := by decide +kernel

theorem rowEval18479 (x : Key → ℝ) : Integer.Sparse.eval row18479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18479, Integer.Sparse.eval_collectBalanced, rawRowCheck18479]

def rawRow18480 : Integer.Sparse Key := [(key2404, 6), (key2404, 6), (key2435, 6), (key2398, 6), (key2876, 6), (key2876, 6), (key3028, 6), (key2589, 6), (key2589, 6), (key2845, 6), (key2845, 6), (key3019, 6), (key3019, 6), (key2583, 6), (key2839, 6), (key2839, 6), (key2925, 6), (key2604, 6), (key2916, 6), (key2916, 6)]

theorem rawRowCheck18480 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form0 = rawRow18480 := by decide +kernel

def row18480 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18480 : row18480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18480 := by decide +kernel

theorem rowEval18480 (x : Key → ℝ) : Integer.Sparse.eval row18480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18480, Integer.Sparse.eval_collectBalanced, rawRowCheck18480]

def rawRow18481 : Integer.Sparse Key := [(key2404, 6), (key2435, 6), (key2404, 6), (key2398, 6), (key2876, 6), (key3028, 6), (key2876, 6), (key2845, 6), (key3019, 6), (key2589, 6), (key3019, 6), (key2589, 6), (key2845, 6), (key2839, 6), (key2583, 6), (key2839, 6), (key2925, 6), (key2916, 6), (key2604, 6), (key2916, 6)]

theorem rawRowCheck18481 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form0 = rawRow18481 := by decide +kernel

def row18481 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18481 : row18481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18481 := by decide +kernel

theorem rowEval18481 (x : Key → ℝ) : Integer.Sparse.eval row18481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18481, Integer.Sparse.eval_collectBalanced, rawRowCheck18481]

def rawRow18482 : Integer.Sparse Key := [(key2435, 6), (key2404, 6), (key2404, 6), (key2398, 6), (key3028, 6), (key2876, 6), (key2876, 6), (key3019, 6), (key2845, 6), (key3019, 6), (key2589, 6), (key2845, 6), (key2589, 6), (key2839, 6), (key2839, 6), (key2583, 6), (key2925, 6), (key2916, 6), (key2916, 6), (key2604, 6)]

theorem rawRowCheck18482 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form0 = rawRow18482 := by decide +kernel

def row18482 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

theorem rowCheck18482 : row18482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18482 := by decide +kernel

theorem rowEval18482 (x : Key → ℝ) : Integer.Sparse.eval row18482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18482, Integer.Sparse.eval_collectBalanced, rawRowCheck18482]

def rawRow18483 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2370, 6), (key2376, 6), (key2388, 6), (key2762, 6), (key2768, 6), (key2839, 6), (key2876, 6), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6), (key2589, 6), (key2768, 6), (key2845, 6), (key2876, 6)]

theorem rawRowCheck18483 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form0 = rawRow18483 := by decide +kernel

def row18483 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

theorem rowCheck18483 : row18483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18483 := by decide +kernel

theorem rowEval18483 (x : Key → ℝ) : Integer.Sparse.eval row18483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18483, Integer.Sparse.eval_collectBalanced, rawRowCheck18483]

def rawRow18484 : Integer.Sparse Key := [(key2470, 6), (key2464, 6), (key2478, 6), (key2501, 6), (key2376, 6), (key2370, 6), (key2388, 6), (key2768, 6), (key2762, 6), (key2876, 6), (key2839, 6), (key2925, 6), (key2916, 6), (key3005, 6), (key3028, 6), (key3019, 6), (key2589, 6), (key2768, 6), (key2876, 6), (key2845, 6)]

theorem rawRowCheck18484 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form0 = rawRow18484 := by decide +kernel

def row18484 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

theorem rowCheck18484 : row18484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18484 := by decide +kernel

theorem rowEval18484 (x : Key → ℝ) : Integer.Sparse.eval row18484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18484, Integer.Sparse.eval_collectBalanced, rawRowCheck18484]

def rawRow18485 : Integer.Sparse Key := [(key2464, 6), (key2478, 6), (key2470, 6), (key2501, 6), (key2370, 6), (key2388, 6), (key2376, 6), (key2839, 6), (key2916, 6), (key2762, 6), (key2925, 6), (key2768, 6), (key2876, 6), (key3019, 6), (key3005, 6), (key3028, 6), (key2589, 6), (key2845, 6), (key2768, 6), (key2876, 6)]

theorem rawRowCheck18485 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form0 = rawRow18485 := by decide +kernel

def row18485 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

theorem rowCheck18485 : row18485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18485 := by decide +kernel

theorem rowEval18485 (x : Key → ℝ) : Integer.Sparse.eval row18485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18485, Integer.Sparse.eval_collectBalanced, rawRowCheck18485]

def rawRow18486 : Integer.Sparse Key := [(key2478, 6), (key2464, 6), (key2470, 6), (key2501, 6), (key2388, 6), (key2370, 6), (key2376, 6), (key2916, 6), (key2839, 6), (key2925, 6), (key2762, 6), (key2876, 6), (key2768, 6), (key3019, 6), (key3028, 6), (key3005, 6), (key2589, 6), (key2845, 6), (key2876, 6), (key2768, 6)]

theorem rawRowCheck18486 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form0 = rawRow18486 := by decide +kernel

def row18486 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

theorem rowCheck18486 : row18486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18486 := by decide +kernel

theorem rowEval18486 (x : Key → ℝ) : Integer.Sparse.eval row18486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18486, Integer.Sparse.eval_collectBalanced, rawRowCheck18486]

def rawRow18487 : Integer.Sparse Key := [(key2470, 6), (key2478, 6), (key2464, 6), (key2501, 6), (key2376, 6), (key2388, 6), (key2370, 6), (key2876, 6), (key2925, 6), (key2768, 6), (key2916, 6), (key2762, 6), (key2839, 6), (key3028, 6), (key3005, 6), (key3019, 6), (key2589, 6), (key2876, 6), (key2768, 6), (key2845, 6)]

theorem rawRowCheck18487 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form0 = rawRow18487 := by decide +kernel

def row18487 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

theorem rowCheck18487 : row18487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18487 := by decide +kernel

theorem rowEval18487 (x : Key → ℝ) : Integer.Sparse.eval row18487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18487, Integer.Sparse.eval_collectBalanced, rawRowCheck18487]

def rawRow18488 : Integer.Sparse Key := [(key2478, 6), (key2470, 6), (key2464, 6), (key2501, 6), (key2388, 6), (key2376, 6), (key2370, 6), (key2925, 6), (key2876, 6), (key2916, 6), (key2768, 6), (key2839, 6), (key2762, 6), (key3028, 6), (key3019, 6), (key3005, 6), (key2589, 6), (key2876, 6), (key2845, 6), (key2768, 6)]

theorem rawRowCheck18488 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form0 = rawRow18488 := by decide +kernel

def row18488 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

theorem rowCheck18488 : row18488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18488 := by decide +kernel

theorem rowEval18488 (x : Key → ℝ) : Integer.Sparse.eval row18488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18488, Integer.Sparse.eval_collectBalanced, rawRowCheck18488]

def rawRow18489 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2501, 6), (key2478, 6), (key2398, 6), (key2404, 6), (key2435, 6), (key2583, 6), (key2589, 6), (key2839, 6), (key2876, 6), (key3019, 6), (key3028, 6), (key2604, 6), (key2916, 6), (key2925, 6), (key2768, 6), (key2589, 6), (key2845, 6), (key2876, 6)]

theorem rawRowCheck18489 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form0 = rawRow18489 := by decide +kernel

def row18489 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

theorem rowCheck18489 : row18489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18489 := by decide +kernel

theorem rowEval18489 (x : Key → ℝ) : Integer.Sparse.eval row18489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18489, Integer.Sparse.eval_collectBalanced, rawRowCheck18489]

def rawRow18490 : Integer.Sparse Key := [(key2470, 6), (key2464, 6), (key2501, 6), (key2478, 6), (key2404, 6), (key2398, 6), (key2435, 6), (key2589, 6), (key2583, 6), (key2876, 6), (key2839, 6), (key3028, 6), (key3019, 6), (key2604, 6), (key2925, 6), (key2916, 6), (key2768, 6), (key2589, 6), (key2876, 6), (key2845, 6)]

theorem rawRowCheck18490 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form0 = rawRow18490 := by decide +kernel

def row18490 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

theorem rowCheck18490 : row18490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18490 := by decide +kernel

theorem rowEval18490 (x : Key → ℝ) : Integer.Sparse.eval row18490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18490, Integer.Sparse.eval_collectBalanced, rawRowCheck18490]

def rawRow18491 : Integer.Sparse Key := [(key2464, 6), (key2501, 6), (key2470, 6), (key2478, 6), (key2398, 6), (key2435, 6), (key2404, 6), (key2839, 6), (key3019, 6), (key2583, 6), (key3028, 6), (key2589, 6), (key2876, 6), (key2916, 6), (key2604, 6), (key2925, 6), (key2768, 6), (key2845, 6), (key2589, 6), (key2876, 6)]

theorem rawRowCheck18491 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form0 = rawRow18491 := by decide +kernel

def row18491 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

theorem rowCheck18491 : row18491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18491 := by decide +kernel

theorem rowEval18491 (x : Key → ℝ) : Integer.Sparse.eval row18491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18491, Integer.Sparse.eval_collectBalanced, rawRowCheck18491]

def rawRow18492 : Integer.Sparse Key := [(key2501, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2435, 6), (key2398, 6), (key2404, 6), (key3019, 6), (key2839, 6), (key3028, 6), (key2583, 6), (key2876, 6), (key2589, 6), (key2916, 6), (key2925, 6), (key2604, 6), (key2768, 6), (key2845, 6), (key2876, 6), (key2589, 6)]

theorem rawRowCheck18492 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form0 = rawRow18492 := by decide +kernel

def row18492 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

theorem rowCheck18492 : row18492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18492 := by decide +kernel

theorem rowEval18492 (x : Key → ℝ) : Integer.Sparse.eval row18492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18492, Integer.Sparse.eval_collectBalanced, rawRowCheck18492]

def rawRow18493 : Integer.Sparse Key := [(key2470, 6), (key2501, 6), (key2464, 6), (key2478, 6), (key2404, 6), (key2435, 6), (key2398, 6), (key2876, 6), (key3028, 6), (key2589, 6), (key3019, 6), (key2583, 6), (key2839, 6), (key2925, 6), (key2604, 6), (key2916, 6), (key2768, 6), (key2876, 6), (key2589, 6), (key2845, 6)]

theorem rawRowCheck18493 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form0 = rawRow18493 := by decide +kernel

def row18493 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

theorem rowCheck18493 : row18493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18493 := by decide +kernel

theorem rowEval18493 (x : Key → ℝ) : Integer.Sparse.eval row18493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18493, Integer.Sparse.eval_collectBalanced, rawRowCheck18493]

def rawRow18494 : Integer.Sparse Key := [(key2501, 6), (key2470, 6), (key2464, 6), (key2478, 6), (key2435, 6), (key2404, 6), (key2398, 6), (key3028, 6), (key2876, 6), (key3019, 6), (key2589, 6), (key2839, 6), (key2583, 6), (key2925, 6), (key2916, 6), (key2604, 6), (key2768, 6), (key2876, 6), (key2845, 6), (key2589, 6)]

theorem rawRowCheck18494 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form0 = rawRow18494 := by decide +kernel

def row18494 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

theorem rowCheck18494 : row18494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18494 := by decide +kernel

theorem rowEval18494 (x : Key → ℝ) : Integer.Sparse.eval row18494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18494, Integer.Sparse.eval_collectBalanced, rawRowCheck18494]

def rawRow18495 : Integer.Sparse Key := [(key2464, 6), (key2478, 6), (key2501, 6), (key2470, 6), (key2464, 6), (key2478, 6), (key2501, 6), (key2370, 6), (key2388, 6), (key2762, 6), (key2925, 6), (key3005, 6), (key3028, 6), (key2589, 6), (key2768, 6), (key2876, 6), (key2845, 6), (key2589, 6), (key2768, 6), (key2876, 6)]

theorem rawRowCheck18495 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form0 = rawRow18495 := by decide +kernel

def row18495 : Integer.Sparse Key := [(key2370, 6), (key2388, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2589, 12), (key2762, 6), (key2768, 12), (key2845, 6), (key2876, 12), (key2925, 6), (key3005, 6), (key3028, 6)]

theorem rowCheck18495 : row18495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18495 := by decide +kernel

theorem rowEval18495 (x : Key → ℝ) : Integer.Sparse.eval row18495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18495, Integer.Sparse.eval_collectBalanced, rawRowCheck18495]

def rawRow18496 : Integer.Sparse Key := [(key2478, 6), (key2464, 6), (key2501, 6), (key2470, 6), (key2478, 6), (key2464, 6), (key2501, 6), (key2388, 6), (key2370, 6), (key2925, 6), (key2762, 6), (key3028, 6), (key3005, 6), (key2589, 6), (key2876, 6), (key2768, 6), (key2845, 6), (key2589, 6), (key2876, 6), (key2768, 6)]

theorem rawRowCheck18496 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form0 = rawRow18496 := by decide +kernel

def row18496 : Integer.Sparse Key := [(key2370, 6), (key2388, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2589, 12), (key2762, 6), (key2768, 12), (key2845, 6), (key2876, 12), (key2925, 6), (key3005, 6), (key3028, 6)]

theorem rowCheck18496 : row18496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18496 := by decide +kernel

theorem rowEval18496 (x : Key → ℝ) : Integer.Sparse.eval row18496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18496, Integer.Sparse.eval_collectBalanced, rawRowCheck18496]

def rawRow18497 : Integer.Sparse Key := [(key2464, 6), (key2501, 6), (key2478, 6), (key2470, 6), (key2464, 6), (key2501, 6), (key2478, 6), (key2398, 6), (key2435, 6), (key2583, 6), (key3028, 6), (key2604, 6), (key2925, 6), (key2768, 6), (key2589, 6), (key2876, 6), (key2845, 6), (key2768, 6), (key2589, 6), (key2876, 6)]

theorem rawRowCheck18497 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form0 = rawRow18497 := by decide +kernel

def row18497 : Integer.Sparse Key := [(key2398, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 12), (key2845, 6), (key2876, 12), (key2925, 6), (key3028, 6)]

theorem rowCheck18497 : row18497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18497 := by decide +kernel

theorem rowEval18497 (x : Key → ℝ) : Integer.Sparse.eval row18497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18497, Integer.Sparse.eval_collectBalanced, rawRowCheck18497]

def rawRow18498 : Integer.Sparse Key := [(key2501, 6), (key2464, 6), (key2478, 6), (key2470, 6), (key2501, 6), (key2464, 6), (key2478, 6), (key2435, 6), (key2398, 6), (key3028, 6), (key2583, 6), (key2925, 6), (key2604, 6), (key2768, 6), (key2876, 6), (key2589, 6), (key2845, 6), (key2768, 6), (key2876, 6), (key2589, 6)]

theorem rawRowCheck18498 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form0 = rawRow18498 := by decide +kernel

def row18498 : Integer.Sparse Key := [(key2398, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 12), (key2845, 6), (key2876, 12), (key2925, 6), (key3028, 6)]

theorem rowCheck18498 : row18498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18498 := by decide +kernel

theorem rowEval18498 (x : Key → ℝ) : Integer.Sparse.eval row18498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18498, Integer.Sparse.eval_collectBalanced, rawRowCheck18498]

def rawRow18499 : Integer.Sparse Key := [(key2478, 6), (key2501, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2464, 6), (key2570, 6), (key2575, 6), (key2388, 6), (key2435, 6), (key2370, 6), (key2762, 6), (key2876, 6), (key2589, 6), (key2768, 6), (key2845, 6), (key2876, 6), (key2589, 6), (key2768, 6)]

theorem rawRowCheck18499 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form0 = rawRow18499 := by decide +kernel

def row18499 : Integer.Sparse Key := [(key2370, 6), (key2388, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2570, 6), (key2575, 6), (key2589, 12), (key2762, 6), (key2768, 12), (key2845, 6), (key2876, 12)]

theorem rowCheck18499 : row18499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18499 := by decide +kernel

theorem rowEval18499 (x : Key → ℝ) : Integer.Sparse.eval row18499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18499, Integer.Sparse.eval_collectBalanced, rawRowCheck18499]

def rawRow18500 : Integer.Sparse Key := [(key2501, 6), (key2478, 6), (key2464, 6), (key2470, 6), (key2501, 6), (key2478, 6), (key2464, 6), (key2575, 6), (key2570, 6), (key2435, 6), (key2388, 6), (key2398, 6), (key2583, 6), (key2876, 6), (key2768, 6), (key2589, 6), (key2845, 6), (key2876, 6), (key2768, 6), (key2589, 6)]

theorem rawRowCheck18500 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form0 = rawRow18500 := by decide +kernel

def row18500 : Integer.Sparse Key := [(key2388, 6), (key2398, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2589, 12), (key2768, 12), (key2845, 6), (key2876, 12)]

theorem rowCheck18500 : row18500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18500 := by decide +kernel

theorem rowEval18500 (x : Key → ℝ) : Integer.Sparse.eval row18500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18500, Integer.Sparse.eval_collectBalanced, rawRowCheck18500]

def rawRow18501 : Integer.Sparse Key := [(key2470, 6), (key2478, 6), (key2501, 6), (key2464, 6), (key2568, 6), (key2570, 6), (key2575, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2478, 6), (key2435, 6), (key2501, 6), (key2370, 6), (key2762, 6), (key2839, 6), (key2876, 6), (key2589, 6), (key2768, 6), (key2845, 6)]

theorem rawRowCheck18501 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form0 = rawRow18501 := by decide +kernel

def row18501 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2589, 6), (key2762, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 6)]

theorem rowCheck18501 : row18501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18501 := by decide +kernel

theorem rowEval18501 (x : Key → ℝ) : Integer.Sparse.eval row18501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18501, Integer.Sparse.eval_collectBalanced, rawRowCheck18501]

def rawRow18502 : Integer.Sparse Key := [(key2478, 6), (key2470, 6), (key2501, 6), (key2464, 6), (key2570, 6), (key2568, 6), (key2575, 6), (key2388, 6), (key2376, 6), (key2478, 6), (key2404, 6), (key2501, 6), (key2435, 6), (key2370, 6), (key2839, 6), (key2762, 6), (key2876, 6), (key2589, 6), (key2845, 6), (key2768, 6)]

theorem rawRowCheck18502 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form0 = rawRow18502 := by decide +kernel

def row18502 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2589, 6), (key2762, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 6)]

theorem rowCheck18502 : row18502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18502 := by decide +kernel

theorem rowEval18502 (x : Key → ℝ) : Integer.Sparse.eval row18502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18502, Integer.Sparse.eval_collectBalanced, rawRowCheck18502]

def rawRow18503 : Integer.Sparse Key := [(key2470, 6), (key2501, 6), (key2478, 6), (key2464, 6), (key2568, 6), (key2575, 6), (key2570, 6), (key2404, 6), (key2435, 6), (key2376, 6), (key2501, 6), (key2388, 6), (key2478, 6), (key2398, 6), (key2583, 6), (key2839, 6), (key2876, 6), (key2768, 6), (key2589, 6), (key2845, 6)]

theorem rawRowCheck18503 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form0 = rawRow18503 := by decide +kernel

def row18503 : Integer.Sparse Key := [(key2376, 6), (key2388, 6), (key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2583, 6), (key2589, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 6)]

theorem rowCheck18503 : row18503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18503 := by decide +kernel

theorem rowEval18503 (x : Key → ℝ) : Integer.Sparse.eval row18503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18503, Integer.Sparse.eval_collectBalanced, rawRowCheck18503]

def rawRow18504 : Integer.Sparse Key := [(key2501, 6), (key2470, 6), (key2478, 6), (key2464, 6), (key2575, 6), (key2568, 6), (key2570, 6), (key2435, 6), (key2404, 6), (key2501, 6), (key2376, 6), (key2478, 6), (key2388, 6), (key2398, 6), (key2839, 6), (key2583, 6), (key2876, 6), (key2768, 6), (key2845, 6), (key2589, 6)]

theorem rawRowCheck18504 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form0 = rawRow18504 := by decide +kernel

def row18504 : Integer.Sparse Key := [(key2376, 6), (key2388, 6), (key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2583, 6), (key2589, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 6)]

theorem rowCheck18504 : row18504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18504 := by decide +kernel

theorem rowEval18504 (x : Key → ℝ) : Integer.Sparse.eval row18504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18504, Integer.Sparse.eval_collectBalanced, rawRowCheck18504]

def rawRow18505 : Integer.Sparse Key := [(key2478, 6), (key2501, 6), (key2470, 6), (key2464, 6), (key2570, 6), (key2575, 6), (key2568, 6), (key2478, 6), (key2501, 6), (key2388, 6), (key2435, 6), (key2376, 6), (key2404, 6), (key2464, 6), (key2370, 6), (key2762, 6), (key2876, 6), (key2845, 6), (key2589, 6), (key2768, 6)]

theorem rawRowCheck18505 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form0 = rawRow18505 := by decide +kernel

def row18505 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2589, 6), (key2762, 6), (key2768, 6), (key2845, 6), (key2876, 6)]

theorem rowCheck18505 : row18505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18505 := by decide +kernel

theorem rowEval18505 (x : Key → ℝ) : Integer.Sparse.eval row18505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18505, Integer.Sparse.eval_collectBalanced, rawRowCheck18505]

def rawRow18506 : Integer.Sparse Key := [(key2501, 6), (key2478, 6), (key2470, 6), (key2464, 6), (key2575, 6), (key2570, 6), (key2568, 6), (key2501, 6), (key2478, 6), (key2435, 6), (key2388, 6), (key2404, 6), (key2376, 6), (key2464, 6), (key2398, 6), (key2583, 6), (key2876, 6), (key2845, 6), (key2768, 6), (key2589, 6)]

theorem rawRowCheck18506 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form0 = rawRow18506 := by decide +kernel

def row18506 : Integer.Sparse Key := [(key2376, 6), (key2388, 6), (key2398, 6), (key2404, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2583, 6), (key2589, 6), (key2768, 6), (key2845, 6), (key2876, 6)]

theorem rowCheck18506 : row18506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18506 := by decide +kernel

theorem rowEval18506 (x : Key → ℝ) : Integer.Sparse.eval row18506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18506, Integer.Sparse.eval_collectBalanced, rawRowCheck18506]

def rawRow18507 : Integer.Sparse Key := [(key2568, 6), (key2568, 6), (key2570, 6), (key2575, 6), (key2376, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2404, 6), (key2470, 6), (key2470, 6), (key2478, 6), (key2478, 6), (key2435, 6), (key2501, 6), (key2501, 6), (key2370, 6), (key2762, 6), (key2839, 6), (key2839, 6)]

theorem rawRowCheck18507 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form0 = rawRow18507 := by decide +kernel

def row18507 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6), (key2839, 12)]

theorem rowCheck18507 : row18507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18507 := by decide +kernel

theorem rowEval18507 (x : Key → ℝ) : Integer.Sparse.eval row18507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18507, Integer.Sparse.eval_collectBalanced, rawRowCheck18507]

def rawRow18508 : Integer.Sparse Key := [(key2568, 6), (key2570, 6), (key2568, 6), (key2575, 6), (key2376, 6), (key2388, 6), (key2376, 6), (key2470, 6), (key2478, 6), (key2404, 6), (key2478, 6), (key2404, 6), (key2470, 6), (key2501, 6), (key2435, 6), (key2501, 6), (key2370, 6), (key2839, 6), (key2762, 6), (key2839, 6)]

theorem rawRowCheck18508 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form0 = rawRow18508 := by decide +kernel

def row18508 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6), (key2839, 12)]

theorem rowCheck18508 : row18508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18508 := by decide +kernel

theorem rowEval18508 (x : Key → ℝ) : Integer.Sparse.eval row18508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18508, Integer.Sparse.eval_collectBalanced, rawRowCheck18508]

def rawRow18509 : Integer.Sparse Key := [(key2570, 6), (key2568, 6), (key2568, 6), (key2575, 6), (key2388, 6), (key2376, 6), (key2376, 6), (key2478, 6), (key2470, 6), (key2478, 6), (key2404, 6), (key2470, 6), (key2404, 6), (key2501, 6), (key2501, 6), (key2435, 6), (key2370, 6), (key2839, 6), (key2839, 6), (key2762, 6)]

theorem rawRowCheck18509 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form0 = rawRow18509 := by decide +kernel

def row18509 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6), (key2839, 12)]

theorem rowCheck18509 : row18509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18509 := by decide +kernel

theorem rowEval18509 (x : Key → ℝ) : Integer.Sparse.eval row18509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18509, Integer.Sparse.eval_collectBalanced, rawRowCheck18509]

def rawRow18510 : Integer.Sparse Key := [(key2568, 6), (key2568, 6), (key2575, 6), (key2570, 6), (key2404, 6), (key2404, 6), (key2435, 6), (key2376, 6), (key2376, 6), (key2470, 6), (key2470, 6), (key2501, 6), (key2501, 6), (key2388, 6), (key2478, 6), (key2478, 6), (key2398, 6), (key2583, 6), (key2839, 6), (key2839, 6)]

theorem rawRowCheck18510 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form0 = rawRow18510 := by decide +kernel

def row18510 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2839, 12)]

theorem rowCheck18510 : row18510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18510 := by decide +kernel

theorem rowEval18510 (x : Key → ℝ) : Integer.Sparse.eval row18510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18510, Integer.Sparse.eval_collectBalanced, rawRowCheck18510]

def rawRow18511 : Integer.Sparse Key := [(key2568, 6), (key2575, 6), (key2568, 6), (key2570, 6), (key2404, 6), (key2435, 6), (key2404, 6), (key2470, 6), (key2501, 6), (key2376, 6), (key2501, 6), (key2376, 6), (key2470, 6), (key2478, 6), (key2388, 6), (key2478, 6), (key2398, 6), (key2839, 6), (key2583, 6), (key2839, 6)]

theorem rawRowCheck18511 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form0 = rawRow18511 := by decide +kernel

def row18511 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2839, 12)]

theorem rowCheck18511 : row18511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18511 := by decide +kernel

theorem rowEval18511 (x : Key → ℝ) : Integer.Sparse.eval row18511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18511, Integer.Sparse.eval_collectBalanced, rawRowCheck18511]

def rawRow18512 : Integer.Sparse Key := [(key2575, 6), (key2568, 6), (key2568, 6), (key2570, 6), (key2435, 6), (key2404, 6), (key2404, 6), (key2501, 6), (key2470, 6), (key2501, 6), (key2376, 6), (key2470, 6), (key2376, 6), (key2478, 6), (key2478, 6), (key2388, 6), (key2398, 6), (key2839, 6), (key2839, 6), (key2583, 6)]

theorem rawRowCheck18512 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form0 = rawRow18512 := by decide +kernel

def row18512 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2839, 12)]

theorem rowCheck18512 : row18512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18512 := by decide +kernel

theorem rowEval18512 (x : Key → ℝ) : Integer.Sparse.eval row18512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18512, Integer.Sparse.eval_collectBalanced, rawRowCheck18512]

def rawRow18513 : Integer.Sparse Key := [(key2568, 6), (key2570, 6), (key2575, 6), (key2568, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2478, 6), (key2435, 6), (key2501, 6), (key2376, 6), (key2404, 6), (key2470, 6), (key2464, 6), (key2370, 6), (key2762, 6), (key2839, 6)]

theorem rawRowCheck18513 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form0 = rawRow18513 := by decide +kernel

def row18513 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2464, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6), (key2839, 6)]

theorem rowCheck18513 : row18513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18513 := by decide +kernel

theorem rowEval18513 (x : Key → ℝ) : Integer.Sparse.eval row18513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18513, Integer.Sparse.eval_collectBalanced, rawRowCheck18513]

def rawRow18514 : Integer.Sparse Key := [(key2570, 6), (key2568, 6), (key2575, 6), (key2568, 6), (key2478, 6), (key2470, 6), (key2501, 6), (key2388, 6), (key2376, 6), (key2478, 6), (key2404, 6), (key2501, 6), (key2435, 6), (key2376, 6), (key2470, 6), (key2404, 6), (key2464, 6), (key2370, 6), (key2839, 6), (key2762, 6)]

theorem rawRowCheck18514 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form0 = rawRow18514 := by decide +kernel

def row18514 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2464, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6), (key2839, 6)]

theorem rowCheck18514 : row18514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18514 := by decide +kernel

theorem rowEval18514 (x : Key → ℝ) : Integer.Sparse.eval row18514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18514, Integer.Sparse.eval_collectBalanced, rawRowCheck18514]

def rawRow18515 : Integer.Sparse Key := [(key2568, 6), (key2575, 6), (key2570, 6), (key2568, 6), (key2470, 6), (key2501, 6), (key2478, 6), (key2404, 6), (key2435, 6), (key2376, 6), (key2501, 6), (key2388, 6), (key2478, 6), (key2404, 6), (key2376, 6), (key2470, 6), (key2464, 6), (key2398, 6), (key2583, 6), (key2839, 6)]

theorem rawRowCheck18515 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form0 = rawRow18515 := by decide +kernel

def row18515 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2464, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2839, 6)]

theorem rowCheck18515 : row18515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18515 := by decide +kernel

theorem rowEval18515 (x : Key → ℝ) : Integer.Sparse.eval row18515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18515, Integer.Sparse.eval_collectBalanced, rawRowCheck18515]

def rawRow18516 : Integer.Sparse Key := [(key2575, 6), (key2568, 6), (key2570, 6), (key2568, 6), (key2501, 6), (key2470, 6), (key2478, 6), (key2435, 6), (key2404, 6), (key2501, 6), (key2376, 6), (key2478, 6), (key2388, 6), (key2404, 6), (key2470, 6), (key2376, 6), (key2464, 6), (key2398, 6), (key2839, 6), (key2583, 6)]

theorem rawRowCheck18516 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form0 = rawRow18516 := by decide +kernel

def row18516 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2464, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2839, 6)]

theorem rowCheck18516 : row18516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18516 := by decide +kernel

theorem rowEval18516 (x : Key → ℝ) : Integer.Sparse.eval row18516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18516, Integer.Sparse.eval_collectBalanced, rawRowCheck18516]

def rawRow18517 : Integer.Sparse Key := [(key2570, 6), (key2575, 6), (key2568, 6), (key2568, 6), (key2478, 6), (key2501, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2388, 6), (key2435, 6), (key2376, 6), (key2404, 6), (key2470, 6), (key2376, 6), (key2404, 6), (key2464, 6), (key2464, 6), (key2370, 6), (key2762, 6)]

theorem rawRowCheck18517 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form0 = rawRow18517 := by decide +kernel

def row18517 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2464, 12), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6)]

theorem rowCheck18517 : row18517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18517 := by decide +kernel

theorem rowEval18517 (x : Key → ℝ) : Integer.Sparse.eval row18517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18517, Integer.Sparse.eval_collectBalanced, rawRowCheck18517]

def rawRow18518 : Integer.Sparse Key := [(key2575, 6), (key2570, 6), (key2568, 6), (key2568, 6), (key2501, 6), (key2478, 6), (key2470, 6), (key2501, 6), (key2478, 6), (key2435, 6), (key2388, 6), (key2404, 6), (key2376, 6), (key2470, 6), (key2404, 6), (key2376, 6), (key2464, 6), (key2464, 6), (key2398, 6), (key2583, 6)]

theorem rawRowCheck18518 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form0 = rawRow18518 := by decide +kernel

def row18518 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2464, 12), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6)]

theorem rowCheck18518 : row18518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18518 := by decide +kernel

theorem rowEval18518 (x : Key → ℝ) : Integer.Sparse.eval row18518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18518, Integer.Sparse.eval_collectBalanced, rawRowCheck18518]

def rawRow18519 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 24), (key1104, 24), (key1230, 24)]

theorem rawRowCheck18519 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form1 = rawRow18519 := by decide +kernel

def row18519 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18519 : row18519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18519 := by decide +kernel

theorem rowEval18519 (x : Key → ℝ) : Integer.Sparse.eval row18519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18519, Integer.Sparse.eval_collectBalanced, rawRowCheck18519]

def rawRow18520 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 24), (key1230, 24), (key1104, 24)]

theorem rawRowCheck18520 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form1 = rawRow18520 := by decide +kernel

def row18520 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18520 : row18520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18520 := by decide +kernel

theorem rowEval18520 (x : Key → ℝ) : Integer.Sparse.eval row18520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18520, Integer.Sparse.eval_collectBalanced, rawRowCheck18520]

def rawRow18521 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1230, 24), (key1104, 24), (key1104, 24)]

theorem rawRowCheck18521 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form1 = rawRow18521 := by decide +kernel

def row18521 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18521 : row18521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18521 := by decide +kernel

theorem rowEval18521 (x : Key → ℝ) : Integer.Sparse.eval row18521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18521, Integer.Sparse.eval_collectBalanced, rawRowCheck18521]

def rawRow18522 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1026, 24), (key1104, 24), (key1230, 24)]

theorem rawRowCheck18522 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form1 = rawRow18522 := by decide +kernel

def row18522 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18522 : row18522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18522 := by decide +kernel

theorem rowEval18522 (x : Key → ℝ) : Integer.Sparse.eval row18522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18522, Integer.Sparse.eval_collectBalanced, rawRowCheck18522]

def rawRow18523 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1026, 24), (key1230, 24), (key1104, 24)]

theorem rawRowCheck18523 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form1 = rawRow18523 := by decide +kernel

def row18523 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18523 : row18523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18523 := by decide +kernel

theorem rowEval18523 (x : Key → ℝ) : Integer.Sparse.eval row18523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18523, Integer.Sparse.eval_collectBalanced, rawRowCheck18523]

def rawRow18524 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1104, 24), (key1026, 24), (key1230, 24)]

theorem rawRowCheck18524 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form1 = rawRow18524 := by decide +kernel

def row18524 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18524 : row18524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18524 := by decide +kernel

theorem rowEval18524 (x : Key → ℝ) : Integer.Sparse.eval row18524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18524, Integer.Sparse.eval_collectBalanced, rawRowCheck18524]

def rawRow18525 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1104, 24), (key1230, 24), (key1026, 24)]

theorem rawRowCheck18525 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form1 = rawRow18525 := by decide +kernel

def row18525 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18525 : row18525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18525 := by decide +kernel

theorem rowEval18525 (x : Key → ℝ) : Integer.Sparse.eval row18525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18525, Integer.Sparse.eval_collectBalanced, rawRowCheck18525]

def rawRow18526 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1230, 24), (key1026, 24), (key1104, 24)]

theorem rawRowCheck18526 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form1 = rawRow18526 := by decide +kernel

def row18526 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18526 : row18526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18526 := by decide +kernel

theorem rowEval18526 (x : Key → ℝ) : Integer.Sparse.eval row18526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18526, Integer.Sparse.eval_collectBalanced, rawRowCheck18526]

def rawRow18527 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1230, 24), (key1104, 24), (key1026, 24)]

theorem rawRowCheck18527 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form1 = rawRow18527 := by decide +kernel

def row18527 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18527 : row18527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18527 := by decide +kernel

theorem rowEval18527 (x : Key → ℝ) : Integer.Sparse.eval row18527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18527, Integer.Sparse.eval_collectBalanced, rawRowCheck18527]

def rawRow18528 : Integer.Sparse Key := [(key991, 24), (key1230, 24), (key1026, 24), (key1104, 24), (key1104, 24)]

theorem rawRowCheck18528 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form1 = rawRow18528 := by decide +kernel

def row18528 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18528 : row18528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18528 := by decide +kernel

theorem rowEval18528 (x : Key → ℝ) : Integer.Sparse.eval row18528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18528, Integer.Sparse.eval_collectBalanced, rawRowCheck18528]

def rawRow18529 : Integer.Sparse Key := [(key991, 24), (key1230, 24), (key1104, 24), (key1026, 24), (key1104, 24)]

theorem rawRowCheck18529 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form1 = rawRow18529 := by decide +kernel

def row18529 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18529 : row18529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18529 := by decide +kernel

theorem rowEval18529 (x : Key → ℝ) : Integer.Sparse.eval row18529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18529, Integer.Sparse.eval_collectBalanced, rawRowCheck18529]

def rawRow18530 : Integer.Sparse Key := [(key991, 24), (key1230, 24), (key1104, 24), (key1104, 24), (key1026, 24)]

theorem rawRowCheck18530 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form1 = rawRow18530 := by decide +kernel

def row18530 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18530 : row18530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18530 := by decide +kernel

theorem rowEval18530 (x : Key → ℝ) : Integer.Sparse.eval row18530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18530, Integer.Sparse.eval_collectBalanced, rawRowCheck18530]

def rawRow18531 : Integer.Sparse Key := [(key1026, 24), (key991, 24), (key1104, 24), (key1104, 24), (key1230, 24)]

theorem rawRowCheck18531 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form1 = rawRow18531 := by decide +kernel

def row18531 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18531 : row18531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18531 := by decide +kernel

theorem rowEval18531 (x : Key → ℝ) : Integer.Sparse.eval row18531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18531, Integer.Sparse.eval_collectBalanced, rawRowCheck18531]

def rawRow18532 : Integer.Sparse Key := [(key1026, 24), (key991, 24), (key1104, 24), (key1230, 24), (key1104, 24)]

theorem rawRowCheck18532 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form1 = rawRow18532 := by decide +kernel

def row18532 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18532 : row18532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18532 := by decide +kernel

theorem rowEval18532 (x : Key → ℝ) : Integer.Sparse.eval row18532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18532, Integer.Sparse.eval_collectBalanced, rawRowCheck18532]

def rawRow18533 : Integer.Sparse Key := [(key1026, 24), (key991, 24), (key1230, 24), (key1104, 24), (key1104, 24)]

theorem rawRowCheck18533 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form1 = rawRow18533 := by decide +kernel

def row18533 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18533 : row18533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18533 := by decide +kernel

theorem rowEval18533 (x : Key → ℝ) : Integer.Sparse.eval row18533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18533, Integer.Sparse.eval_collectBalanced, rawRowCheck18533]

def rawRow18534 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key991, 24), (key1104, 24), (key1230, 24)]

theorem rawRowCheck18534 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form1 = rawRow18534 := by decide +kernel

def row18534 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18534 : row18534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18534 := by decide +kernel

theorem rowEval18534 (x : Key → ℝ) : Integer.Sparse.eval row18534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18534, Integer.Sparse.eval_collectBalanced, rawRowCheck18534]

def rawRow18535 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key991, 24), (key1230, 24), (key1104, 24)]

theorem rawRowCheck18535 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form1 = rawRow18535 := by decide +kernel

def row18535 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18535 : row18535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18535 := by decide +kernel

theorem rowEval18535 (x : Key → ℝ) : Integer.Sparse.eval row18535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18535, Integer.Sparse.eval_collectBalanced, rawRowCheck18535]

def rawRow18536 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key1104, 24), (key991, 24), (key1230, 24)]

theorem rawRowCheck18536 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form1 = rawRow18536 := by decide +kernel

def row18536 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18536 : row18536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18536 := by decide +kernel

theorem rowEval18536 (x : Key → ℝ) : Integer.Sparse.eval row18536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18536, Integer.Sparse.eval_collectBalanced, rawRowCheck18536]

def rawRow18537 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key1104, 24), (key1230, 24), (key991, 24)]

theorem rawRowCheck18537 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form1 = rawRow18537 := by decide +kernel

def row18537 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18537 : row18537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18537 := by decide +kernel

theorem rowEval18537 (x : Key → ℝ) : Integer.Sparse.eval row18537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18537, Integer.Sparse.eval_collectBalanced, rawRowCheck18537]

def rawRow18538 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key1230, 24), (key991, 24), (key1104, 24)]

theorem rawRowCheck18538 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form1 = rawRow18538 := by decide +kernel

def row18538 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18538 : row18538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18538 := by decide +kernel

theorem rowEval18538 (x : Key → ℝ) : Integer.Sparse.eval row18538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18538, Integer.Sparse.eval_collectBalanced, rawRowCheck18538]

def rawRow18539 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key1230, 24), (key1104, 24), (key991, 24)]

theorem rawRowCheck18539 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form1 = rawRow18539 := by decide +kernel

def row18539 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18539 : row18539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18539 := by decide +kernel

theorem rowEval18539 (x : Key → ℝ) : Integer.Sparse.eval row18539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18539, Integer.Sparse.eval_collectBalanced, rawRowCheck18539]

def rawRow18540 : Integer.Sparse Key := [(key1026, 24), (key1230, 24), (key991, 24), (key1104, 24), (key1104, 24)]

theorem rawRowCheck18540 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form1 = rawRow18540 := by decide +kernel

def row18540 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18540 : row18540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18540 := by decide +kernel

theorem rowEval18540 (x : Key → ℝ) : Integer.Sparse.eval row18540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18540, Integer.Sparse.eval_collectBalanced, rawRowCheck18540]

def rawRow18541 : Integer.Sparse Key := [(key1026, 24), (key1230, 24), (key1104, 24), (key991, 24), (key1104, 24)]

theorem rawRowCheck18541 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form1 = rawRow18541 := by decide +kernel

def row18541 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18541 : row18541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18541 := by decide +kernel

theorem rowEval18541 (x : Key → ℝ) : Integer.Sparse.eval row18541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18541, Integer.Sparse.eval_collectBalanced, rawRowCheck18541]

def rawRow18542 : Integer.Sparse Key := [(key1026, 24), (key1230, 24), (key1104, 24), (key1104, 24), (key991, 24)]

theorem rawRowCheck18542 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form1 = rawRow18542 := by decide +kernel

def row18542 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18542 : row18542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18542 := by decide +kernel

theorem rowEval18542 (x : Key → ℝ) : Integer.Sparse.eval row18542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18542, Integer.Sparse.eval_collectBalanced, rawRowCheck18542]

def rawRow18543 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1026, 24), (key1104, 24), (key1230, 24)]

theorem rawRowCheck18543 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form1 = rawRow18543 := by decide +kernel

def row18543 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18543 : row18543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18543 := by decide +kernel

theorem rowEval18543 (x : Key → ℝ) : Integer.Sparse.eval row18543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18543, Integer.Sparse.eval_collectBalanced, rawRowCheck18543]

def rawRow18544 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1026, 24), (key1230, 24), (key1104, 24)]

theorem rawRowCheck18544 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form1 = rawRow18544 := by decide +kernel

def row18544 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18544 : row18544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18544 := by decide +kernel

theorem rowEval18544 (x : Key → ℝ) : Integer.Sparse.eval row18544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18544, Integer.Sparse.eval_collectBalanced, rawRowCheck18544]

def rawRow18545 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1104, 24), (key1026, 24), (key1230, 24)]

theorem rawRowCheck18545 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form1 = rawRow18545 := by decide +kernel

def row18545 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18545 : row18545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18545 := by decide +kernel

theorem rowEval18545 (x : Key → ℝ) : Integer.Sparse.eval row18545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18545, Integer.Sparse.eval_collectBalanced, rawRowCheck18545]

def rawRow18546 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1104, 24), (key1230, 24), (key1026, 24)]

theorem rawRowCheck18546 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form1 = rawRow18546 := by decide +kernel

def row18546 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18546 : row18546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18546 := by decide +kernel

theorem rowEval18546 (x : Key → ℝ) : Integer.Sparse.eval row18546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18546, Integer.Sparse.eval_collectBalanced, rawRowCheck18546]

def rawRow18547 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1230, 24), (key1026, 24), (key1104, 24)]

theorem rawRowCheck18547 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form1 = rawRow18547 := by decide +kernel

def row18547 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18547 : row18547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18547 := by decide +kernel

theorem rowEval18547 (x : Key → ℝ) : Integer.Sparse.eval row18547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18547, Integer.Sparse.eval_collectBalanced, rawRowCheck18547]

def rawRow18548 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1230, 24), (key1104, 24), (key1026, 24)]

theorem rawRowCheck18548 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form1 = rawRow18548 := by decide +kernel

def row18548 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18548 : row18548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18548 := by decide +kernel

theorem rowEval18548 (x : Key → ℝ) : Integer.Sparse.eval row18548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18548, Integer.Sparse.eval_collectBalanced, rawRowCheck18548]

def rawRow18549 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key991, 24), (key1104, 24), (key1230, 24)]

theorem rawRowCheck18549 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form1 = rawRow18549 := by decide +kernel

def row18549 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18549 : row18549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18549 := by decide +kernel

theorem rowEval18549 (x : Key → ℝ) : Integer.Sparse.eval row18549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18549, Integer.Sparse.eval_collectBalanced, rawRowCheck18549]

def rawRow18550 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key991, 24), (key1230, 24), (key1104, 24)]

theorem rawRowCheck18550 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form1 = rawRow18550 := by decide +kernel

def row18550 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18550 : row18550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18550 := by decide +kernel

theorem rowEval18550 (x : Key → ℝ) : Integer.Sparse.eval row18550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18550, Integer.Sparse.eval_collectBalanced, rawRowCheck18550]

def rawRow18551 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key1104, 24), (key991, 24), (key1230, 24)]

theorem rawRowCheck18551 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form1 = rawRow18551 := by decide +kernel

def row18551 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18551 : row18551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18551 := by decide +kernel

theorem rowEval18551 (x : Key → ℝ) : Integer.Sparse.eval row18551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18551, Integer.Sparse.eval_collectBalanced, rawRowCheck18551]

def rawRow18552 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key1104, 24), (key1230, 24), (key991, 24)]

theorem rawRowCheck18552 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form1 = rawRow18552 := by decide +kernel

def row18552 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18552 : row18552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18552 := by decide +kernel

theorem rowEval18552 (x : Key → ℝ) : Integer.Sparse.eval row18552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18552, Integer.Sparse.eval_collectBalanced, rawRowCheck18552]

def rawRow18553 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key1230, 24), (key991, 24), (key1104, 24)]

theorem rawRowCheck18553 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form1 = rawRow18553 := by decide +kernel

def row18553 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18553 : row18553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18553 := by decide +kernel

theorem rowEval18553 (x : Key → ℝ) : Integer.Sparse.eval row18553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18553, Integer.Sparse.eval_collectBalanced, rawRowCheck18553]

def rawRow18554 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key1230, 24), (key1104, 24), (key991, 24)]

theorem rawRowCheck18554 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form1 = rawRow18554 := by decide +kernel

def row18554 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18554 : row18554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18554 := by decide +kernel

theorem rowEval18554 (x : Key → ℝ) : Integer.Sparse.eval row18554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18554, Integer.Sparse.eval_collectBalanced, rawRowCheck18554]

def rawRow18555 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key991, 24), (key1026, 24), (key1230, 24)]

theorem rawRowCheck18555 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form1 = rawRow18555 := by decide +kernel

def row18555 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18555 : row18555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18555 := by decide +kernel

theorem rowEval18555 (x : Key → ℝ) : Integer.Sparse.eval row18555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18555, Integer.Sparse.eval_collectBalanced, rawRowCheck18555]

def rawRow18556 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key991, 24), (key1230, 24), (key1026, 24)]

theorem rawRowCheck18556 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form1 = rawRow18556 := by decide +kernel

def row18556 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18556 : row18556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18556 := by decide +kernel

theorem rowEval18556 (x : Key → ℝ) : Integer.Sparse.eval row18556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18556, Integer.Sparse.eval_collectBalanced, rawRowCheck18556]

def rawRow18557 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key1026, 24), (key991, 24), (key1230, 24)]

theorem rawRowCheck18557 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form1 = rawRow18557 := by decide +kernel

def row18557 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18557 : row18557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18557 := by decide +kernel

theorem rowEval18557 (x : Key → ℝ) : Integer.Sparse.eval row18557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18557, Integer.Sparse.eval_collectBalanced, rawRowCheck18557]

def rawRow18558 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key1026, 24), (key1230, 24), (key991, 24)]

theorem rawRowCheck18558 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form1 = rawRow18558 := by decide +kernel

def row18558 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18558 : row18558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18558 := by decide +kernel

theorem rowEval18558 (x : Key → ℝ) : Integer.Sparse.eval row18558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18558, Integer.Sparse.eval_collectBalanced, rawRowCheck18558]

def rawRow18559 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key1230, 24), (key991, 24), (key1026, 24)]

theorem rawRowCheck18559 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form1 = rawRow18559 := by decide +kernel

def row18559 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18559 : row18559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18559 := by decide +kernel

theorem rowEval18559 (x : Key → ℝ) : Integer.Sparse.eval row18559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18559, Integer.Sparse.eval_collectBalanced, rawRowCheck18559]

end MUB6.Certificate.GramRows

end OAI
