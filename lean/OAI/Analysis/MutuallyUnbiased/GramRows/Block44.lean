import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
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

def rawRow2560 : Integer.Sparse Key := [(key2182, -2), (key2185, -2), (key2185, -2), (key2183, 2), (key2185, 2), (key2185, 2), (key2284, 2), (key2285, 2), (key2285, 2), (key2285, -6), (key2345, -2), (key2346, -2), (key2346, -2), (key2346, 6)]

theorem rawRowCheck2560 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form6 = rawRow2560 := by decide +kernel

def row2560 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

theorem rowCheck2560 : row2560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2560 := by decide +kernel

theorem rowEval2560 (x : Key → ℝ) : Integer.Sparse.eval row2560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck2560, Integer.Sparse.eval_collectBalanced, rawRowCheck2560]

def rawRow2561 : Integer.Sparse Key := [(key2185, -2), (key2182, -2), (key2185, -2), (key2185, 2), (key2183, 2), (key2185, 2), (key2285, 2), (key2284, 2), (key2285, 2), (key2285, -6), (key2346, -2), (key2345, -2), (key2346, -2), (key2346, 6)]

theorem rawRowCheck2561 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form6 = rawRow2561 := by decide +kernel

def row2561 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

theorem rowCheck2561 : row2561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2561 := by decide +kernel

theorem rowEval2561 (x : Key → ℝ) : Integer.Sparse.eval row2561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2561, Integer.Sparse.eval_collectBalanced, rawRowCheck2561]

def rawRow2562 : Integer.Sparse Key := [(key2185, -2), (key2185, -2), (key2182, -2), (key2185, 2), (key2185, 2), (key2183, 2), (key2285, 2), (key2285, 2), (key2284, 2), (key2285, -6), (key2346, -2), (key2346, -2), (key2345, -2), (key2346, 6)]

theorem rawRowCheck2562 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form6 = rawRow2562 := by decide +kernel

def row2562 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

theorem rowCheck2562 : row2562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2562 := by decide +kernel

theorem rowEval2562 (x : Key → ℝ) : Integer.Sparse.eval row2562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2562, Integer.Sparse.eval_collectBalanced, rawRowCheck2562]

def rawRow2563 : Integer.Sparse Key := [(key2183, -2), (key2183, -2), (key2183, -2), (key2182, 2), (key2182, 2), (key2182, 2), (key2285, 2), (key2285, 2), (key2285, 2), (key2284, -6), (key2346, -2), (key2346, -2), (key2346, -2), (key2345, 6)]

theorem rawRowCheck2563 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form6 = rawRow2563 := by decide +kernel

def row2563 : Integer.Sparse Key := [(key2182, 6), (key2183, -6), (key2284, -6), (key2285, 6), (key2345, 6), (key2346, -6)]

theorem rowCheck2563 : row2563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2563 := by decide +kernel

theorem rowEval2563 (x : Key → ℝ) : Integer.Sparse.eval row2563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2563, Integer.Sparse.eval_collectBalanced, rawRowCheck2563]

def rawRow2564 : Integer.Sparse Key := [(key2284, -2), (key2285, -2), (key2285, -2), (key2345, 2), (key2346, 2), (key2346, 2), (key2182, 2), (key2185, 2), (key2185, 2), (key2346, -6), (key2183, -2), (key2185, -2), (key2185, -2), (key2285, 6)]

theorem rawRowCheck2564 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form6 = rawRow2564 := by decide +kernel

def row2564 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

theorem rowCheck2564 : row2564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2564 := by decide +kernel

theorem rowEval2564 (x : Key → ℝ) : Integer.Sparse.eval row2564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck2564, Integer.Sparse.eval_collectBalanced, rawRowCheck2564]

def rawRow2565 : Integer.Sparse Key := [(key2285, -2), (key2284, -2), (key2285, -2), (key2346, 2), (key2345, 2), (key2346, 2), (key2185, 2), (key2182, 2), (key2185, 2), (key2346, -6), (key2185, -2), (key2183, -2), (key2185, -2), (key2285, 6)]

theorem rawRowCheck2565 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form6 = rawRow2565 := by decide +kernel

def row2565 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

theorem rowCheck2565 : row2565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2565 := by decide +kernel

theorem rowEval2565 (x : Key → ℝ) : Integer.Sparse.eval row2565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2565, Integer.Sparse.eval_collectBalanced, rawRowCheck2565]

def rawRow2566 : Integer.Sparse Key := [(key2285, -2), (key2285, -2), (key2284, -2), (key2346, 2), (key2346, 2), (key2345, 2), (key2185, 2), (key2185, 2), (key2182, 2), (key2346, -6), (key2185, -2), (key2185, -2), (key2183, -2), (key2285, 6)]

theorem rawRowCheck2566 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form6 = rawRow2566 := by decide +kernel

def row2566 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

theorem rowCheck2566 : row2566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2566 := by decide +kernel

theorem rowEval2566 (x : Key → ℝ) : Integer.Sparse.eval row2566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2566, Integer.Sparse.eval_collectBalanced, rawRowCheck2566]

def rawRow2567 : Integer.Sparse Key := [(key2183, -2), (key2183, -2), (key2345, -2), (key2182, 2), (key2182, 2), (key2284, 2), (key2185, 2), (key2185, 2), (key2346, 2), (key2182, -6), (key2185, -2), (key2185, -2), (key2285, -2), (key2183, 6)]

theorem rawRowCheck2567 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form6 = rawRow2567 := by decide +kernel

def row2567 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

theorem rowCheck2567 : row2567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2567 := by decide +kernel

theorem rowEval2567 (x : Key → ℝ) : Integer.Sparse.eval row2567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2567, Integer.Sparse.eval_collectBalanced, rawRowCheck2567]

def rawRow2568 : Integer.Sparse Key := [(key2183, -2), (key2345, -2), (key2183, -2), (key2182, 2), (key2284, 2), (key2182, 2), (key2185, 2), (key2346, 2), (key2185, 2), (key2182, -6), (key2185, -2), (key2285, -2), (key2185, -2), (key2183, 6)]

theorem rawRowCheck2568 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form6 = rawRow2568 := by decide +kernel

def row2568 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

theorem rowCheck2568 : row2568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2568 := by decide +kernel

theorem rowEval2568 (x : Key → ℝ) : Integer.Sparse.eval row2568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2568, Integer.Sparse.eval_collectBalanced, rawRowCheck2568]

def rawRow2569 : Integer.Sparse Key := [(key2345, -2), (key2183, -2), (key2183, -2), (key2284, 2), (key2182, 2), (key2182, 2), (key2346, 2), (key2185, 2), (key2185, 2), (key2182, -6), (key2285, -2), (key2185, -2), (key2185, -2), (key2183, 6)]

theorem rawRowCheck2569 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form6 = rawRow2569 := by decide +kernel

def row2569 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

theorem rowCheck2569 : row2569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2569 := by decide +kernel

theorem rowEval2569 (x : Key → ℝ) : Integer.Sparse.eval row2569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2569, Integer.Sparse.eval_collectBalanced, rawRowCheck2569]

def rawRow2570 : Integer.Sparse Key := [(key2285, -2), (key2285, -2), (key2285, -2), (key2346, 2), (key2346, 2), (key2346, 2), (key2183, 2), (key2183, 2), (key2183, 2), (key2345, -6), (key2182, -2), (key2182, -2), (key2182, -2), (key2284, 6)]

theorem rawRowCheck2570 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form6 = rawRow2570 := by decide +kernel

def row2570 : Integer.Sparse Key := [(key2182, -6), (key2183, 6), (key2284, 6), (key2285, -6), (key2345, -6), (key2346, 6)]

theorem rowCheck2570 : row2570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2570 := by decide +kernel

theorem rowEval2570 (x : Key → ℝ) : Integer.Sparse.eval row2570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2570, Integer.Sparse.eval_collectBalanced, rawRowCheck2570]

def rawRow2571 : Integer.Sparse Key := [(key2185, -2), (key2185, -2), (key2346, -2), (key2185, 2), (key2185, 2), (key2285, 2), (key2183, 2), (key2183, 2), (key2345, 2), (key2183, -6), (key2182, -2), (key2182, -2), (key2284, -2), (key2182, 6)]

theorem rawRowCheck2571 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form6 = rawRow2571 := by decide +kernel

def row2571 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

theorem rowCheck2571 : row2571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2571 := by decide +kernel

theorem rowEval2571 (x : Key → ℝ) : Integer.Sparse.eval row2571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2571, Integer.Sparse.eval_collectBalanced, rawRowCheck2571]

def rawRow2572 : Integer.Sparse Key := [(key2185, -2), (key2346, -2), (key2185, -2), (key2185, 2), (key2285, 2), (key2185, 2), (key2183, 2), (key2345, 2), (key2183, 2), (key2183, -6), (key2182, -2), (key2284, -2), (key2182, -2), (key2182, 6)]

theorem rawRowCheck2572 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form6 = rawRow2572 := by decide +kernel

def row2572 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

theorem rowCheck2572 : row2572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2572 := by decide +kernel

theorem rowEval2572 (x : Key → ℝ) : Integer.Sparse.eval row2572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2572, Integer.Sparse.eval_collectBalanced, rawRowCheck2572]

def rawRow2573 : Integer.Sparse Key := [(key2346, -2), (key2185, -2), (key2185, -2), (key2285, 2), (key2185, 2), (key2185, 2), (key2345, 2), (key2183, 2), (key2183, 2), (key2183, -6), (key2284, -2), (key2182, -2), (key2182, -2), (key2182, 6)]

theorem rawRowCheck2573 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form6 = rawRow2573 := by decide +kernel

def row2573 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

theorem rowCheck2573 : row2573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2573 := by decide +kernel

theorem rowEval2573 (x : Key → ℝ) : Integer.Sparse.eval row2573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2573, Integer.Sparse.eval_collectBalanced, rawRowCheck2573]

def rawRow2574 : Integer.Sparse Key := [(key737, -2), (key738, -2), (key738, -2), (key737, 1), (key738, 1), (key737, 1), (key743, 1), (key738, 1), (key743, 1), (key817, 2), (key818, 2), (key818, 2), (key817, -1), (key818, -1), (key817, -1), (key825, -1), (key818, -1), (key825, -1), (key897, -1), (key898, -1), (key897, -1), (key902, -1), (key898, -1), (key902, -1), (key897, 1), (key898, 1), (key897, 1), (key908, 1), (key898, 1), (key908, 1)]

theorem rawRowCheck2574 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form7 = rawRow2574 := by decide +kernel

def row2574 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

theorem rowCheck2574 : row2574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2574 := by decide +kernel

theorem rowEval2574 (x : Key → ℝ) : Integer.Sparse.eval row2574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck2574, Integer.Sparse.eval_collectBalanced, rawRowCheck2574]

def rawRow2575 : Integer.Sparse Key := [(key738, -2), (key737, -2), (key738, -2), (key738, 1), (key737, 1), (key743, 1), (key737, 1), (key743, 1), (key738, 1), (key818, 2), (key817, 2), (key818, 2), (key818, -1), (key817, -1), (key825, -1), (key817, -1), (key825, -1), (key818, -1), (key898, -1), (key897, -1), (key902, -1), (key897, -1), (key902, -1), (key898, -1), (key898, 1), (key897, 1), (key908, 1), (key897, 1), (key908, 1), (key898, 1)]

theorem rawRowCheck2575 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form7 = rawRow2575 := by decide +kernel

def row2575 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

theorem rowCheck2575 : row2575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2575 := by decide +kernel

theorem rowEval2575 (x : Key → ℝ) : Integer.Sparse.eval row2575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2575, Integer.Sparse.eval_collectBalanced, rawRowCheck2575]

def rawRow2576 : Integer.Sparse Key := [(key738, -2), (key738, -2), (key737, -2), (key743, 1), (key743, 1), (key738, 1), (key738, 1), (key737, 1), (key737, 1), (key818, 2), (key818, 2), (key817, 2), (key825, -1), (key825, -1), (key818, -1), (key818, -1), (key817, -1), (key817, -1), (key902, -1), (key902, -1), (key898, -1), (key898, -1), (key897, -1), (key897, -1), (key908, 1), (key908, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1)]

theorem rawRowCheck2576 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form7 = rawRow2576 := by decide +kernel

def row2576 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

theorem rowCheck2576 : row2576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2576 := by decide +kernel

theorem rowEval2576 (x : Key → ℝ) : Integer.Sparse.eval row2576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2576, Integer.Sparse.eval_collectBalanced, rawRowCheck2576]

def rawRow2577 : Integer.Sparse Key := [(key743, -2), (key743, -2), (key743, -2), (key738, 1), (key738, 1), (key738, 1), (key738, 1), (key738, 1), (key738, 1), (key825, 2), (key825, 2), (key825, 2), (key818, -1), (key818, -1), (key818, -1), (key818, -1), (key818, -1), (key818, -1), (key908, -1), (key908, -1), (key908, -1), (key908, -1), (key908, -1), (key908, -1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1)]

theorem rawRowCheck2577 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form7 = rawRow2577 := by decide +kernel

def row2577 : Integer.Sparse Key := [(key738, 6), (key743, -6), (key818, -6), (key825, 6), (key902, 6), (key908, -6)]

theorem rowCheck2577 : row2577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2577 := by decide +kernel

theorem rowEval2577 (x : Key → ℝ) : Integer.Sparse.eval row2577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2577, Integer.Sparse.eval_collectBalanced, rawRowCheck2577]

def rawRow2578 : Integer.Sparse Key := [(key817, -2), (key818, -2), (key818, -2), (key897, 1), (key898, 1), (key897, 1), (key902, 1), (key898, 1), (key902, 1), (key737, 2), (key738, 2), (key738, 2), (key897, -1), (key898, -1), (key897, -1), (key908, -1), (key898, -1), (key908, -1), (key737, -1), (key738, -1), (key737, -1), (key743, -1), (key738, -1), (key743, -1), (key817, 1), (key818, 1), (key817, 1), (key825, 1), (key818, 1), (key825, 1)]

theorem rawRowCheck2578 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form7 = rawRow2578 := by decide +kernel

def row2578 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

theorem rowCheck2578 : row2578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2578 := by decide +kernel

theorem rowEval2578 (x : Key → ℝ) : Integer.Sparse.eval row2578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck2578, Integer.Sparse.eval_collectBalanced, rawRowCheck2578]

def rawRow2579 : Integer.Sparse Key := [(key818, -2), (key817, -2), (key818, -2), (key898, 1), (key897, 1), (key902, 1), (key897, 1), (key902, 1), (key898, 1), (key738, 2), (key737, 2), (key738, 2), (key898, -1), (key897, -1), (key908, -1), (key897, -1), (key908, -1), (key898, -1), (key738, -1), (key737, -1), (key743, -1), (key737, -1), (key743, -1), (key738, -1), (key818, 1), (key817, 1), (key825, 1), (key817, 1), (key825, 1), (key818, 1)]

theorem rawRowCheck2579 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form7 = rawRow2579 := by decide +kernel

def row2579 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

theorem rowCheck2579 : row2579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2579 := by decide +kernel

theorem rowEval2579 (x : Key → ℝ) : Integer.Sparse.eval row2579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2579, Integer.Sparse.eval_collectBalanced, rawRowCheck2579]

def rawRow2580 : Integer.Sparse Key := [(key818, -2), (key818, -2), (key817, -2), (key902, 1), (key902, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1), (key738, 2), (key738, 2), (key737, 2), (key908, -1), (key908, -1), (key898, -1), (key898, -1), (key897, -1), (key897, -1), (key743, -1), (key743, -1), (key738, -1), (key738, -1), (key737, -1), (key737, -1), (key825, 1), (key825, 1), (key818, 1), (key818, 1), (key817, 1), (key817, 1)]

theorem rawRowCheck2580 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form7 = rawRow2580 := by decide +kernel

def row2580 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

theorem rowCheck2580 : row2580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2580 := by decide +kernel

theorem rowEval2580 (x : Key → ℝ) : Integer.Sparse.eval row2580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2580, Integer.Sparse.eval_collectBalanced, rawRowCheck2580]

def rawRow2581 : Integer.Sparse Key := [(key902, -2), (key902, -2), (key962, -2), (key818, 1), (key818, 1), (key898, 1), (key898, 1), (key960, 1), (key960, 1), (key908, 2), (key908, 2), (key964, 2), (key738, -1), (key738, -1), (key898, -1), (key898, -1), (key960, -1), (key960, -1), (key825, -1), (key825, -1), (key908, -1), (key908, -1), (key964, -1), (key964, -1), (key743, 1), (key743, 1), (key902, 1), (key902, 1), (key962, 1), (key962, 1)]

theorem rawRowCheck2581 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form7 = rawRow2581 := by decide +kernel

def row2581 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

theorem rowCheck2581 : row2581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2581 := by decide +kernel

theorem rowEval2581 (x : Key → ℝ) : Integer.Sparse.eval row2581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2581, Integer.Sparse.eval_collectBalanced, rawRowCheck2581]

def rawRow2582 : Integer.Sparse Key := [(key902, -2), (key962, -2), (key902, -2), (key898, 1), (key960, 1), (key818, 1), (key960, 1), (key818, 1), (key898, 1), (key908, 2), (key964, 2), (key908, 2), (key898, -1), (key960, -1), (key738, -1), (key960, -1), (key738, -1), (key898, -1), (key908, -1), (key964, -1), (key825, -1), (key964, -1), (key825, -1), (key908, -1), (key902, 1), (key962, 1), (key743, 1), (key962, 1), (key743, 1), (key902, 1)]

theorem rawRowCheck2582 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form7 = rawRow2582 := by decide +kernel

def row2582 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

theorem rowCheck2582 : row2582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2582 := by decide +kernel

theorem rowEval2582 (x : Key → ℝ) : Integer.Sparse.eval row2582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2582, Integer.Sparse.eval_collectBalanced, rawRowCheck2582]

def rawRow2583 : Integer.Sparse Key := [(key962, -2), (key902, -2), (key902, -2), (key960, 1), (key898, 1), (key960, 1), (key818, 1), (key898, 1), (key818, 1), (key964, 2), (key908, 2), (key908, 2), (key960, -1), (key898, -1), (key960, -1), (key738, -1), (key898, -1), (key738, -1), (key964, -1), (key908, -1), (key964, -1), (key825, -1), (key908, -1), (key825, -1), (key962, 1), (key902, 1), (key962, 1), (key743, 1), (key902, 1), (key743, 1)]

theorem rawRowCheck2583 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form7 = rawRow2583 := by decide +kernel

def row2583 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

theorem rowCheck2583 : row2583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2583 := by decide +kernel

theorem rowEval2583 (x : Key → ℝ) : Integer.Sparse.eval row2583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2583, Integer.Sparse.eval_collectBalanced, rawRowCheck2583]

def rawRow2584 : Integer.Sparse Key := [(key825, -2), (key825, -2), (key825, -2), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key743, 2), (key743, 2), (key743, 2), (key902, -1), (key902, -1), (key902, -1), (key902, -1), (key902, -1), (key902, -1), (key738, -1), (key738, -1), (key738, -1), (key738, -1), (key738, -1), (key738, -1), (key818, 1), (key818, 1), (key818, 1), (key818, 1), (key818, 1), (key818, 1)]

theorem rawRowCheck2584 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form7 = rawRow2584 := by decide +kernel

def row2584 : Integer.Sparse Key := [(key738, -6), (key743, 6), (key818, 6), (key825, -6), (key902, -6), (key908, 6)]

theorem rowCheck2584 : row2584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2584 := by decide +kernel

theorem rowEval2584 (x : Key → ℝ) : Integer.Sparse.eval row2584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2584, Integer.Sparse.eval_collectBalanced, rawRowCheck2584]

def rawRow2585 : Integer.Sparse Key := [(key908, -2), (key908, -2), (key964, -2), (key825, 1), (key825, 1), (key908, 1), (key908, 1), (key964, 1), (key964, 1), (key902, 2), (key902, 2), (key962, 2), (key743, -1), (key743, -1), (key902, -1), (key902, -1), (key962, -1), (key962, -1), (key818, -1), (key818, -1), (key898, -1), (key898, -1), (key960, -1), (key960, -1), (key738, 1), (key738, 1), (key898, 1), (key898, 1), (key960, 1), (key960, 1)]

theorem rawRowCheck2585 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form7 = rawRow2585 := by decide +kernel

def row2585 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

theorem rowCheck2585 : row2585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2585 := by decide +kernel

theorem rowEval2585 (x : Key → ℝ) : Integer.Sparse.eval row2585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2585, Integer.Sparse.eval_collectBalanced, rawRowCheck2585]

def rawRow2586 : Integer.Sparse Key := [(key908, -2), (key964, -2), (key908, -2), (key908, 1), (key964, 1), (key825, 1), (key964, 1), (key825, 1), (key908, 1), (key902, 2), (key962, 2), (key902, 2), (key902, -1), (key962, -1), (key743, -1), (key962, -1), (key743, -1), (key902, -1), (key898, -1), (key960, -1), (key818, -1), (key960, -1), (key818, -1), (key898, -1), (key898, 1), (key960, 1), (key738, 1), (key960, 1), (key738, 1), (key898, 1)]

theorem rawRowCheck2586 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form7 = rawRow2586 := by decide +kernel

def row2586 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

theorem rowCheck2586 : row2586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2586 := by decide +kernel

theorem rowEval2586 (x : Key → ℝ) : Integer.Sparse.eval row2586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2586, Integer.Sparse.eval_collectBalanced, rawRowCheck2586]

def rawRow2587 : Integer.Sparse Key := [(key964, -2), (key908, -2), (key908, -2), (key964, 1), (key908, 1), (key964, 1), (key825, 1), (key908, 1), (key825, 1), (key962, 2), (key902, 2), (key902, 2), (key962, -1), (key902, -1), (key962, -1), (key743, -1), (key902, -1), (key743, -1), (key960, -1), (key898, -1), (key960, -1), (key818, -1), (key898, -1), (key818, -1), (key960, 1), (key898, 1), (key960, 1), (key738, 1), (key898, 1), (key738, 1)]

theorem rawRowCheck2587 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form7 = rawRow2587 := by decide +kernel

def row2587 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

theorem rowCheck2587 : row2587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2587 := by decide +kernel

theorem rowEval2587 (x : Key → ℝ) : Integer.Sparse.eval row2587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2587, Integer.Sparse.eval_collectBalanced, rawRowCheck2587]

def rawRow2588 : Integer.Sparse Key := [(key721, -2), (key722, -2), (key722, -2), (key722, 6), (key921, 2), (key922, 2), (key922, 2), (key922, -2), (key922, -2), (key939, -2), (key959, -6), (key959, 2), (key959, 2), (key966, 2)]

theorem rawRowCheck2588 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form8 = rawRow2588 := by decide +kernel

def row2588 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

theorem rowCheck2588 : row2588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2588 := by decide +kernel

theorem rowEval2588 (x : Key → ℝ) : Integer.Sparse.eval row2588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form8) x := by
  rw [rowCheck2588, Integer.Sparse.eval_collectBalanced, rawRowCheck2588]

def rawRow2589 : Integer.Sparse Key := [(key722, -2), (key721, -2), (key722, -2), (key722, 6), (key922, 2), (key921, 2), (key922, 2), (key922, -2), (key939, -2), (key922, -2), (key959, -6), (key959, 2), (key966, 2), (key959, 2)]

theorem rawRowCheck2589 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form8 = rawRow2589 := by decide +kernel

def row2589 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

theorem rowCheck2589 : row2589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2589 := by decide +kernel

theorem rowEval2589 (x : Key → ℝ) : Integer.Sparse.eval row2589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2589, Integer.Sparse.eval_collectBalanced, rawRowCheck2589]

def rawRow2590 : Integer.Sparse Key := [(key722, -2), (key722, -2), (key721, -2), (key722, 6), (key922, 2), (key922, 2), (key921, 2), (key939, -2), (key922, -2), (key922, -2), (key959, -6), (key966, 2), (key959, 2), (key959, 2)]

theorem rawRowCheck2590 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form8 = rawRow2590 := by decide +kernel

def row2590 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

theorem rowCheck2590 : row2590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2590 := by decide +kernel

theorem rowEval2590 (x : Key → ℝ) : Integer.Sparse.eval row2590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2590, Integer.Sparse.eval_collectBalanced, rawRowCheck2590]

def rawRow2591 : Integer.Sparse Key := [(key722, -2), (key722, -2), (key722, -2), (key721, 6), (key939, 2), (key939, 2), (key939, 2), (key921, -2), (key921, -2), (key921, -2), (key966, -6), (key959, 2), (key959, 2), (key959, 2)]

theorem rawRowCheck2591 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form8 = rawRow2591 := by decide +kernel

def row2591 : Integer.Sparse Key := [(key721, 6), (key722, -6), (key921, -6), (key939, 6), (key959, 6), (key966, -6)]

theorem rowCheck2591 : row2591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2591 := by decide +kernel

theorem rowEval2591 (x : Key → ℝ) : Integer.Sparse.eval row2591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2591, Integer.Sparse.eval_collectBalanced, rawRowCheck2591]

def rawRow2592 : Integer.Sparse Key := [(key921, -2), (key922, -2), (key922, -2), (key959, 6), (key721, 2), (key722, 2), (key722, 2), (key959, -2), (key959, -2), (key966, -2), (key722, -6), (key922, 2), (key922, 2), (key939, 2)]

theorem rawRowCheck2592 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form8 = rawRow2592 := by decide +kernel

def row2592 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

theorem rowCheck2592 : row2592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2592 := by decide +kernel

theorem rowEval2592 (x : Key → ℝ) : Integer.Sparse.eval row2592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form8) x := by
  rw [rowCheck2592, Integer.Sparse.eval_collectBalanced, rawRowCheck2592]

def rawRow2593 : Integer.Sparse Key := [(key922, -2), (key921, -2), (key922, -2), (key959, 6), (key722, 2), (key721, 2), (key722, 2), (key959, -2), (key966, -2), (key959, -2), (key722, -6), (key922, 2), (key939, 2), (key922, 2)]

theorem rawRowCheck2593 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form8 = rawRow2593 := by decide +kernel

def row2593 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

theorem rowCheck2593 : row2593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2593 := by decide +kernel

theorem rowEval2593 (x : Key → ℝ) : Integer.Sparse.eval row2593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2593, Integer.Sparse.eval_collectBalanced, rawRowCheck2593]

def rawRow2594 : Integer.Sparse Key := [(key922, -2), (key922, -2), (key921, -2), (key959, 6), (key722, 2), (key722, 2), (key721, 2), (key966, -2), (key959, -2), (key959, -2), (key722, -6), (key939, 2), (key922, 2), (key922, 2)]

theorem rawRowCheck2594 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form8 = rawRow2594 := by decide +kernel

def row2594 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

theorem rowCheck2594 : row2594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2594 := by decide +kernel

theorem rowEval2594 (x : Key → ℝ) : Integer.Sparse.eval row2594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2594, Integer.Sparse.eval_collectBalanced, rawRowCheck2594]

def rawRow2595 : Integer.Sparse Key := [(key922, -2), (key922, -2), (key959, -2), (key921, 6), (key939, 2), (key939, 2), (key966, 2), (key721, -2), (key921, -2), (key921, -2), (key939, -6), (key722, 2), (key922, 2), (key922, 2)]

theorem rawRowCheck2595 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form8 = rawRow2595 := by decide +kernel

def row2595 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

theorem rowCheck2595 : row2595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2595 := by decide +kernel

theorem rowEval2595 (x : Key → ℝ) : Integer.Sparse.eval row2595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2595, Integer.Sparse.eval_collectBalanced, rawRowCheck2595]

def rawRow2596 : Integer.Sparse Key := [(key922, -2), (key959, -2), (key922, -2), (key921, 6), (key939, 2), (key966, 2), (key939, 2), (key921, -2), (key721, -2), (key921, -2), (key939, -6), (key922, 2), (key722, 2), (key922, 2)]

theorem rawRowCheck2596 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form8 = rawRow2596 := by decide +kernel

def row2596 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

theorem rowCheck2596 : row2596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2596 := by decide +kernel

theorem rowEval2596 (x : Key → ℝ) : Integer.Sparse.eval row2596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2596, Integer.Sparse.eval_collectBalanced, rawRowCheck2596]

def rawRow2597 : Integer.Sparse Key := [(key959, -2), (key922, -2), (key922, -2), (key921, 6), (key966, 2), (key939, 2), (key939, 2), (key921, -2), (key921, -2), (key721, -2), (key939, -6), (key922, 2), (key922, 2), (key722, 2)]

theorem rawRowCheck2597 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form8 = rawRow2597 := by decide +kernel

def row2597 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

theorem rowCheck2597 : row2597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2597 := by decide +kernel

theorem rowEval2597 (x : Key → ℝ) : Integer.Sparse.eval row2597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2597, Integer.Sparse.eval_collectBalanced, rawRowCheck2597]

def rawRow2598 : Integer.Sparse Key := [(key939, -2), (key939, -2), (key939, -2), (key966, 6), (key722, 2), (key722, 2), (key722, 2), (key959, -2), (key959, -2), (key959, -2), (key721, -6), (key921, 2), (key921, 2), (key921, 2)]

theorem rawRowCheck2598 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form8 = rawRow2598 := by decide +kernel

def row2598 : Integer.Sparse Key := [(key721, -6), (key722, 6), (key921, 6), (key939, -6), (key959, -6), (key966, 6)]

theorem rowCheck2598 : row2598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2598 := by decide +kernel

theorem rowEval2598 (x : Key → ℝ) : Integer.Sparse.eval row2598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2598, Integer.Sparse.eval_collectBalanced, rawRowCheck2598]

def rawRow2599 : Integer.Sparse Key := [(key939, -2), (key939, -2), (key966, -2), (key939, 6), (key922, 2), (key922, 2), (key959, 2), (key722, -2), (key922, -2), (key922, -2), (key921, -6), (key721, 2), (key921, 2), (key921, 2)]

theorem rawRowCheck2599 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form8 = rawRow2599 := by decide +kernel

def row2599 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

theorem rowCheck2599 : row2599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2599 := by decide +kernel

theorem rowEval2599 (x : Key → ℝ) : Integer.Sparse.eval row2599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2599, Integer.Sparse.eval_collectBalanced, rawRowCheck2599]

def rawRow2600 : Integer.Sparse Key := [(key939, -2), (key966, -2), (key939, -2), (key939, 6), (key922, 2), (key959, 2), (key922, 2), (key922, -2), (key722, -2), (key922, -2), (key921, -6), (key921, 2), (key721, 2), (key921, 2)]

theorem rawRowCheck2600 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form8 = rawRow2600 := by decide +kernel

def row2600 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

theorem rowCheck2600 : row2600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2600 := by decide +kernel

theorem rowEval2600 (x : Key → ℝ) : Integer.Sparse.eval row2600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2600, Integer.Sparse.eval_collectBalanced, rawRowCheck2600]

def rawRow2601 : Integer.Sparse Key := [(key966, -2), (key939, -2), (key939, -2), (key939, 6), (key959, 2), (key922, 2), (key922, 2), (key922, -2), (key922, -2), (key722, -2), (key921, -6), (key921, 2), (key921, 2), (key721, 2)]

theorem rawRowCheck2601 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form8 = rawRow2601 := by decide +kernel

def row2601 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

theorem rowCheck2601 : row2601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2601 := by decide +kernel

theorem rowEval2601 (x : Key → ℝ) : Integer.Sparse.eval row2601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2601, Integer.Sparse.eval_collectBalanced, rawRowCheck2601]

def rawRow2602 : Integer.Sparse Key := [(key2078, -2), (key2078, -2), (key2087, -2), (key2078, 1), (key2082, 1), (key2078, 1), (key2087, 1), (key2082, 1), (key2087, 1), (key2275, 2), (key2275, 2), (key2281, 2), (key2275, -1), (key2281, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2289, -1), (key2327, -1), (key2328, -1), (key2327, -1), (key2330, -1), (key2328, -1), (key2330, -1), (key2327, 1), (key2330, 1), (key2327, 1), (key2333, 1), (key2330, 1), (key2333, 1)]

theorem rawRowCheck2602 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form9 = rawRow2602 := by decide +kernel

def row2602 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

theorem rowCheck2602 : row2602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2602 := by decide +kernel

theorem rowEval2602 (x : Key → ℝ) : Integer.Sparse.eval row2602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form9) x := by
  rw [rowCheck2602, Integer.Sparse.eval_collectBalanced, rawRowCheck2602]

def rawRow2603 : Integer.Sparse Key := [(key2078, -2), (key2087, -2), (key2078, -2), (key2082, 1), (key2078, 1), (key2087, 1), (key2078, 1), (key2087, 1), (key2082, 1), (key2275, 2), (key2281, 2), (key2275, 2), (key2281, -1), (key2275, -1), (key2289, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2328, -1), (key2327, -1), (key2330, -1), (key2327, -1), (key2330, -1), (key2328, -1), (key2330, 1), (key2327, 1), (key2333, 1), (key2327, 1), (key2333, 1), (key2330, 1)]

theorem rawRowCheck2603 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form9 = rawRow2603 := by decide +kernel

def row2603 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

theorem rowCheck2603 : row2603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2603 := by decide +kernel

theorem rowEval2603 (x : Key → ℝ) : Integer.Sparse.eval row2603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2603, Integer.Sparse.eval_collectBalanced, rawRowCheck2603]

def rawRow2604 : Integer.Sparse Key := [(key2087, -2), (key2078, -2), (key2078, -2), (key2087, 1), (key2087, 1), (key2082, 1), (key2082, 1), (key2078, 1), (key2078, 1), (key2281, 2), (key2275, 2), (key2275, 2), (key2289, -1), (key2289, -1), (key2281, -1), (key2281, -1), (key2275, -1), (key2275, -1), (key2330, -1), (key2330, -1), (key2328, -1), (key2328, -1), (key2327, -1), (key2327, -1), (key2333, 1), (key2333, 1), (key2330, 1), (key2330, 1), (key2327, 1), (key2327, 1)]

theorem rawRowCheck2604 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form9 = rawRow2604 := by decide +kernel

def row2604 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

theorem rowCheck2604 : row2604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2604 := by decide +kernel

theorem rowEval2604 (x : Key → ℝ) : Integer.Sparse.eval row2604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2604, Integer.Sparse.eval_collectBalanced, rawRowCheck2604]

def rawRow2605 : Integer.Sparse Key := [(key2082, -2), (key2082, -2), (key2082, -2), (key2078, 1), (key2078, 1), (key2078, 1), (key2078, 1), (key2078, 1), (key2078, 1), (key2289, 2), (key2289, 2), (key2289, 2), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2333, -1), (key2333, -1), (key2333, -1), (key2333, -1), (key2333, -1), (key2333, -1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1)]

theorem rawRowCheck2605 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form9 = rawRow2605 := by decide +kernel

def row2605 : Integer.Sparse Key := [(key2078, 6), (key2082, -6), (key2275, -6), (key2289, 6), (key2328, 6), (key2333, -6)]

theorem rowCheck2605 : row2605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2605 := by decide +kernel

theorem rowEval2605 (x : Key → ℝ) : Integer.Sparse.eval row2605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2605, Integer.Sparse.eval_collectBalanced, rawRowCheck2605]

def rawRow2606 : Integer.Sparse Key := [(key2275, -2), (key2275, -2), (key2281, -2), (key2327, 1), (key2328, 1), (key2327, 1), (key2330, 1), (key2328, 1), (key2330, 1), (key2078, 2), (key2078, 2), (key2087, 2), (key2327, -1), (key2330, -1), (key2327, -1), (key2333, -1), (key2330, -1), (key2333, -1), (key2078, -1), (key2082, -1), (key2078, -1), (key2087, -1), (key2082, -1), (key2087, -1), (key2275, 1), (key2281, 1), (key2275, 1), (key2289, 1), (key2281, 1), (key2289, 1)]

theorem rawRowCheck2606 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form9 = rawRow2606 := by decide +kernel

def row2606 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

theorem rowCheck2606 : row2606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2606 := by decide +kernel

theorem rowEval2606 (x : Key → ℝ) : Integer.Sparse.eval row2606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form9) x := by
  rw [rowCheck2606, Integer.Sparse.eval_collectBalanced, rawRowCheck2606]

def rawRow2607 : Integer.Sparse Key := [(key2275, -2), (key2281, -2), (key2275, -2), (key2328, 1), (key2327, 1), (key2330, 1), (key2327, 1), (key2330, 1), (key2328, 1), (key2078, 2), (key2087, 2), (key2078, 2), (key2330, -1), (key2327, -1), (key2333, -1), (key2327, -1), (key2333, -1), (key2330, -1), (key2082, -1), (key2078, -1), (key2087, -1), (key2078, -1), (key2087, -1), (key2082, -1), (key2281, 1), (key2275, 1), (key2289, 1), (key2275, 1), (key2289, 1), (key2281, 1)]

theorem rawRowCheck2607 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form9 = rawRow2607 := by decide +kernel

def row2607 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

theorem rowCheck2607 : row2607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2607 := by decide +kernel

theorem rowEval2607 (x : Key → ℝ) : Integer.Sparse.eval row2607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2607, Integer.Sparse.eval_collectBalanced, rawRowCheck2607]

def rawRow2608 : Integer.Sparse Key := [(key2281, -2), (key2275, -2), (key2275, -2), (key2330, 1), (key2330, 1), (key2328, 1), (key2328, 1), (key2327, 1), (key2327, 1), (key2087, 2), (key2078, 2), (key2078, 2), (key2333, -1), (key2333, -1), (key2330, -1), (key2330, -1), (key2327, -1), (key2327, -1), (key2087, -1), (key2087, -1), (key2082, -1), (key2082, -1), (key2078, -1), (key2078, -1), (key2289, 1), (key2289, 1), (key2281, 1), (key2281, 1), (key2275, 1), (key2275, 1)]

theorem rawRowCheck2608 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form9 = rawRow2608 := by decide +kernel

def row2608 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

theorem rowCheck2608 : row2608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2608 := by decide +kernel

theorem rowEval2608 (x : Key → ℝ) : Integer.Sparse.eval row2608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2608, Integer.Sparse.eval_collectBalanced, rawRowCheck2608]

def rawRow2609 : Integer.Sparse Key := [(key2179, -2), (key2328, -2), (key2328, -2), (key2175, 1), (key2175, 1), (key2275, 1), (key2275, 1), (key2327, 1), (key2327, 1), (key2189, 2), (key2333, 2), (key2333, 2), (key2078, -1), (key2078, -1), (key2175, -1), (key2175, -1), (key2327, -1), (key2327, -1), (key2189, -1), (key2189, -1), (key2289, -1), (key2289, -1), (key2333, -1), (key2333, -1), (key2082, 1), (key2082, 1), (key2179, 1), (key2179, 1), (key2328, 1), (key2328, 1)]

theorem rawRowCheck2609 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form9 = rawRow2609 := by decide +kernel

def row2609 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

theorem rowCheck2609 : row2609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2609 := by decide +kernel

theorem rowEval2609 (x : Key → ℝ) : Integer.Sparse.eval row2609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2609, Integer.Sparse.eval_collectBalanced, rawRowCheck2609]

def rawRow2610 : Integer.Sparse Key := [(key2328, -2), (key2179, -2), (key2328, -2), (key2275, 1), (key2327, 1), (key2175, 1), (key2327, 1), (key2175, 1), (key2275, 1), (key2333, 2), (key2189, 2), (key2333, 2), (key2175, -1), (key2327, -1), (key2078, -1), (key2327, -1), (key2078, -1), (key2175, -1), (key2289, -1), (key2333, -1), (key2189, -1), (key2333, -1), (key2189, -1), (key2289, -1), (key2179, 1), (key2328, 1), (key2082, 1), (key2328, 1), (key2082, 1), (key2179, 1)]

theorem rawRowCheck2610 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form9 = rawRow2610 := by decide +kernel

def row2610 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

theorem rowCheck2610 : row2610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2610 := by decide +kernel

theorem rowEval2610 (x : Key → ℝ) : Integer.Sparse.eval row2610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2610, Integer.Sparse.eval_collectBalanced, rawRowCheck2610]

def rawRow2611 : Integer.Sparse Key := [(key2328, -2), (key2328, -2), (key2179, -2), (key2327, 1), (key2275, 1), (key2327, 1), (key2175, 1), (key2275, 1), (key2175, 1), (key2333, 2), (key2333, 2), (key2189, 2), (key2327, -1), (key2175, -1), (key2327, -1), (key2078, -1), (key2175, -1), (key2078, -1), (key2333, -1), (key2289, -1), (key2333, -1), (key2189, -1), (key2289, -1), (key2189, -1), (key2328, 1), (key2179, 1), (key2328, 1), (key2082, 1), (key2179, 1), (key2082, 1)]

theorem rawRowCheck2611 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form9 = rawRow2611 := by decide +kernel

def row2611 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

theorem rowCheck2611 : row2611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2611 := by decide +kernel

theorem rowEval2611 (x : Key → ℝ) : Integer.Sparse.eval row2611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2611, Integer.Sparse.eval_collectBalanced, rawRowCheck2611]

def rawRow2612 : Integer.Sparse Key := [(key2289, -2), (key2289, -2), (key2289, -2), (key2333, 1), (key2333, 1), (key2333, 1), (key2333, 1), (key2333, 1), (key2333, 1), (key2082, 2), (key2082, 2), (key2082, 2), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2078, -1), (key2078, -1), (key2078, -1), (key2078, -1), (key2078, -1), (key2078, -1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1)]

theorem rawRowCheck2612 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form9 = rawRow2612 := by decide +kernel

def row2612 : Integer.Sparse Key := [(key2078, -6), (key2082, 6), (key2275, 6), (key2289, -6), (key2328, -6), (key2333, 6)]

theorem rowCheck2612 : row2612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2612 := by decide +kernel

theorem rowEval2612 (x : Key → ℝ) : Integer.Sparse.eval row2612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2612, Integer.Sparse.eval_collectBalanced, rawRowCheck2612]

def rawRow2613 : Integer.Sparse Key := [(key2189, -2), (key2333, -2), (key2333, -2), (key2189, 1), (key2189, 1), (key2289, 1), (key2289, 1), (key2333, 1), (key2333, 1), (key2179, 2), (key2328, 2), (key2328, 2), (key2082, -1), (key2082, -1), (key2179, -1), (key2179, -1), (key2328, -1), (key2328, -1), (key2175, -1), (key2175, -1), (key2275, -1), (key2275, -1), (key2327, -1), (key2327, -1), (key2078, 1), (key2078, 1), (key2175, 1), (key2175, 1), (key2327, 1), (key2327, 1)]

theorem rawRowCheck2613 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form9 = rawRow2613 := by decide +kernel

def row2613 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

theorem rowCheck2613 : row2613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2613 := by decide +kernel

theorem rowEval2613 (x : Key → ℝ) : Integer.Sparse.eval row2613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2613, Integer.Sparse.eval_collectBalanced, rawRowCheck2613]

def rawRow2614 : Integer.Sparse Key := [(key2333, -2), (key2189, -2), (key2333, -2), (key2289, 1), (key2333, 1), (key2189, 1), (key2333, 1), (key2189, 1), (key2289, 1), (key2328, 2), (key2179, 2), (key2328, 2), (key2179, -1), (key2328, -1), (key2082, -1), (key2328, -1), (key2082, -1), (key2179, -1), (key2275, -1), (key2327, -1), (key2175, -1), (key2327, -1), (key2175, -1), (key2275, -1), (key2175, 1), (key2327, 1), (key2078, 1), (key2327, 1), (key2078, 1), (key2175, 1)]

theorem rawRowCheck2614 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form9 = rawRow2614 := by decide +kernel

def row2614 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

theorem rowCheck2614 : row2614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2614 := by decide +kernel

theorem rowEval2614 (x : Key → ℝ) : Integer.Sparse.eval row2614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2614, Integer.Sparse.eval_collectBalanced, rawRowCheck2614]

def rawRow2615 : Integer.Sparse Key := [(key2333, -2), (key2333, -2), (key2189, -2), (key2333, 1), (key2289, 1), (key2333, 1), (key2189, 1), (key2289, 1), (key2189, 1), (key2328, 2), (key2328, 2), (key2179, 2), (key2328, -1), (key2179, -1), (key2328, -1), (key2082, -1), (key2179, -1), (key2082, -1), (key2327, -1), (key2275, -1), (key2327, -1), (key2175, -1), (key2275, -1), (key2175, -1), (key2327, 1), (key2175, 1), (key2327, 1), (key2078, 1), (key2175, 1), (key2078, 1)]

theorem rawRowCheck2615 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form9 = rawRow2615 := by decide +kernel

def row2615 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

theorem rowCheck2615 : row2615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2615 := by decide +kernel

theorem rowEval2615 (x : Key → ℝ) : Integer.Sparse.eval row2615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2615, Integer.Sparse.eval_collectBalanced, rawRowCheck2615]

def rawRow2616 : Integer.Sparse Key := [(key1998, -2), (key2000, -2), (key2000, -2), (key2000, 6), (key2267, 2), (key2269, 2), (key2269, 2), (key2269, -2), (key2269, -2), (key2292, -2), (key2340, -6), (key2340, 2), (key2340, 2), (key2349, 2)]

theorem rawRowCheck2616 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form10 = rawRow2616 := by decide +kernel

def row2616 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

theorem rowCheck2616 : row2616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2616 := by decide +kernel

theorem rowEval2616 (x : Key → ℝ) : Integer.Sparse.eval row2616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form10) x := by
  rw [rowCheck2616, Integer.Sparse.eval_collectBalanced, rawRowCheck2616]

def rawRow2617 : Integer.Sparse Key := [(key2000, -2), (key1998, -2), (key2000, -2), (key2000, 6), (key2269, 2), (key2267, 2), (key2269, 2), (key2269, -2), (key2292, -2), (key2269, -2), (key2340, -6), (key2340, 2), (key2349, 2), (key2340, 2)]

theorem rawRowCheck2617 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form10 = rawRow2617 := by decide +kernel

def row2617 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

theorem rowCheck2617 : row2617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2617 := by decide +kernel

theorem rowEval2617 (x : Key → ℝ) : Integer.Sparse.eval row2617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2617, Integer.Sparse.eval_collectBalanced, rawRowCheck2617]

def rawRow2618 : Integer.Sparse Key := [(key2000, -2), (key2000, -2), (key1998, -2), (key2000, 6), (key2269, 2), (key2269, 2), (key2267, 2), (key2292, -2), (key2269, -2), (key2269, -2), (key2340, -6), (key2349, 2), (key2340, 2), (key2340, 2)]

theorem rawRowCheck2618 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form10 = rawRow2618 := by decide +kernel

def row2618 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

theorem rowCheck2618 : row2618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2618 := by decide +kernel

theorem rowEval2618 (x : Key → ℝ) : Integer.Sparse.eval row2618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2618, Integer.Sparse.eval_collectBalanced, rawRowCheck2618]

def rawRow2619 : Integer.Sparse Key := [(key2000, -2), (key2000, -2), (key2000, -2), (key1998, 6), (key2292, 2), (key2292, 2), (key2292, 2), (key2267, -2), (key2267, -2), (key2267, -2), (key2349, -6), (key2340, 2), (key2340, 2), (key2340, 2)]

theorem rawRowCheck2619 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form10 = rawRow2619 := by decide +kernel

def row2619 : Integer.Sparse Key := [(key1998, 6), (key2000, -6), (key2267, -6), (key2292, 6), (key2340, 6), (key2349, -6)]

theorem rowCheck2619 : row2619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2619 := by decide +kernel

theorem rowEval2619 (x : Key → ℝ) : Integer.Sparse.eval row2619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2619, Integer.Sparse.eval_collectBalanced, rawRowCheck2619]

def rawRow2620 : Integer.Sparse Key := [(key2267, -2), (key2269, -2), (key2269, -2), (key2340, 6), (key1998, 2), (key2000, 2), (key2000, 2), (key2340, -2), (key2340, -2), (key2349, -2), (key2000, -6), (key2269, 2), (key2269, 2), (key2292, 2)]

theorem rawRowCheck2620 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form10 = rawRow2620 := by decide +kernel

def row2620 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

theorem rowCheck2620 : row2620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2620 := by decide +kernel

theorem rowEval2620 (x : Key → ℝ) : Integer.Sparse.eval row2620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form10) x := by
  rw [rowCheck2620, Integer.Sparse.eval_collectBalanced, rawRowCheck2620]

def rawRow2621 : Integer.Sparse Key := [(key2269, -2), (key2267, -2), (key2269, -2), (key2340, 6), (key2000, 2), (key1998, 2), (key2000, 2), (key2340, -2), (key2349, -2), (key2340, -2), (key2000, -6), (key2269, 2), (key2292, 2), (key2269, 2)]

theorem rawRowCheck2621 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form10 = rawRow2621 := by decide +kernel

def row2621 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

theorem rowCheck2621 : row2621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2621 := by decide +kernel

theorem rowEval2621 (x : Key → ℝ) : Integer.Sparse.eval row2621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2621, Integer.Sparse.eval_collectBalanced, rawRowCheck2621]

def rawRow2622 : Integer.Sparse Key := [(key2269, -2), (key2269, -2), (key2267, -2), (key2340, 6), (key2000, 2), (key2000, 2), (key1998, 2), (key2349, -2), (key2340, -2), (key2340, -2), (key2000, -6), (key2292, 2), (key2269, 2), (key2269, 2)]

theorem rawRowCheck2622 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form10 = rawRow2622 := by decide +kernel

def row2622 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

theorem rowCheck2622 : row2622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2622 := by decide +kernel

theorem rowEval2622 (x : Key → ℝ) : Integer.Sparse.eval row2622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2622, Integer.Sparse.eval_collectBalanced, rawRowCheck2622]

def rawRow2623 : Integer.Sparse Key := [(key2269, -2), (key2269, -2), (key2340, -2), (key2267, 6), (key2292, 2), (key2292, 2), (key2349, 2), (key1998, -2), (key2267, -2), (key2267, -2), (key2292, -6), (key2000, 2), (key2269, 2), (key2269, 2)]

theorem rawRowCheck2623 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form10 = rawRow2623 := by decide +kernel

def row2623 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

theorem rowCheck2623 : row2623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2623 := by decide +kernel

theorem rowEval2623 (x : Key → ℝ) : Integer.Sparse.eval row2623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2623, Integer.Sparse.eval_collectBalanced, rawRowCheck2623]

def rawRow2624 : Integer.Sparse Key := [(key2269, -2), (key2340, -2), (key2269, -2), (key2267, 6), (key2292, 2), (key2349, 2), (key2292, 2), (key2267, -2), (key1998, -2), (key2267, -2), (key2292, -6), (key2269, 2), (key2000, 2), (key2269, 2)]

theorem rawRowCheck2624 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form10 = rawRow2624 := by decide +kernel

def row2624 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

theorem rowCheck2624 : row2624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2624 := by decide +kernel

theorem rowEval2624 (x : Key → ℝ) : Integer.Sparse.eval row2624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2624, Integer.Sparse.eval_collectBalanced, rawRowCheck2624]

def rawRow2625 : Integer.Sparse Key := [(key2340, -2), (key2269, -2), (key2269, -2), (key2267, 6), (key2349, 2), (key2292, 2), (key2292, 2), (key2267, -2), (key2267, -2), (key1998, -2), (key2292, -6), (key2269, 2), (key2269, 2), (key2000, 2)]

theorem rawRowCheck2625 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form10 = rawRow2625 := by decide +kernel

def row2625 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

theorem rowCheck2625 : row2625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2625 := by decide +kernel

theorem rowEval2625 (x : Key → ℝ) : Integer.Sparse.eval row2625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2625, Integer.Sparse.eval_collectBalanced, rawRowCheck2625]

def rawRow2626 : Integer.Sparse Key := [(key2292, -2), (key2292, -2), (key2292, -2), (key2349, 6), (key2000, 2), (key2000, 2), (key2000, 2), (key2340, -2), (key2340, -2), (key2340, -2), (key1998, -6), (key2267, 2), (key2267, 2), (key2267, 2)]

theorem rawRowCheck2626 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form10 = rawRow2626 := by decide +kernel

def row2626 : Integer.Sparse Key := [(key1998, -6), (key2000, 6), (key2267, 6), (key2292, -6), (key2340, -6), (key2349, 6)]

theorem rowCheck2626 : row2626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2626 := by decide +kernel

theorem rowEval2626 (x : Key → ℝ) : Integer.Sparse.eval row2626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2626, Integer.Sparse.eval_collectBalanced, rawRowCheck2626]

def rawRow2627 : Integer.Sparse Key := [(key2292, -2), (key2292, -2), (key2349, -2), (key2292, 6), (key2269, 2), (key2269, 2), (key2340, 2), (key2000, -2), (key2269, -2), (key2269, -2), (key2267, -6), (key1998, 2), (key2267, 2), (key2267, 2)]

theorem rawRowCheck2627 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form10 = rawRow2627 := by decide +kernel

def row2627 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

theorem rowCheck2627 : row2627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2627 := by decide +kernel

theorem rowEval2627 (x : Key → ℝ) : Integer.Sparse.eval row2627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2627, Integer.Sparse.eval_collectBalanced, rawRowCheck2627]

def rawRow2628 : Integer.Sparse Key := [(key2292, -2), (key2349, -2), (key2292, -2), (key2292, 6), (key2269, 2), (key2340, 2), (key2269, 2), (key2269, -2), (key2000, -2), (key2269, -2), (key2267, -6), (key2267, 2), (key1998, 2), (key2267, 2)]

theorem rawRowCheck2628 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form10 = rawRow2628 := by decide +kernel

def row2628 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

theorem rowCheck2628 : row2628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2628 := by decide +kernel

theorem rowEval2628 (x : Key → ℝ) : Integer.Sparse.eval row2628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2628, Integer.Sparse.eval_collectBalanced, rawRowCheck2628]

def rawRow2629 : Integer.Sparse Key := [(key2349, -2), (key2292, -2), (key2292, -2), (key2292, 6), (key2340, 2), (key2269, 2), (key2269, 2), (key2269, -2), (key2269, -2), (key2000, -2), (key2267, -6), (key2267, 2), (key2267, 2), (key1998, 2)]

theorem rawRowCheck2629 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form10 = rawRow2629 := by decide +kernel

def row2629 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

theorem rowCheck2629 : row2629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2629 := by decide +kernel

theorem rowEval2629 (x : Key → ℝ) : Integer.Sparse.eval row2629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2629, Integer.Sparse.eval_collectBalanced, rawRowCheck2629]

def rawRow2630 : Integer.Sparse Key := [(key2006, -2), (key2007, -2), (key2007, -2), (key2007, 6), (key2299, 2), (key2300, 2), (key2300, 2), (key2300, -2), (key2300, -2), (key2313, -2), (key2340, -6), (key2340, 2), (key2340, 2), (key2349, 2)]

theorem rawRowCheck2630 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form11 = rawRow2630 := by decide +kernel

def row2630 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

theorem rowCheck2630 : row2630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2630 := by decide +kernel

theorem rowEval2630 (x : Key → ℝ) : Integer.Sparse.eval row2630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form11) x := by
  rw [rowCheck2630, Integer.Sparse.eval_collectBalanced, rawRowCheck2630]

def rawRow2631 : Integer.Sparse Key := [(key2007, -2), (key2006, -2), (key2007, -2), (key2007, 6), (key2300, 2), (key2299, 2), (key2300, 2), (key2300, -2), (key2313, -2), (key2300, -2), (key2340, -6), (key2340, 2), (key2349, 2), (key2340, 2)]

theorem rawRowCheck2631 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form11 = rawRow2631 := by decide +kernel

def row2631 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

theorem rowCheck2631 : row2631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2631 := by decide +kernel

theorem rowEval2631 (x : Key → ℝ) : Integer.Sparse.eval row2631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2631, Integer.Sparse.eval_collectBalanced, rawRowCheck2631]

def rawRow2632 : Integer.Sparse Key := [(key2007, -2), (key2007, -2), (key2006, -2), (key2007, 6), (key2300, 2), (key2300, 2), (key2299, 2), (key2313, -2), (key2300, -2), (key2300, -2), (key2340, -6), (key2349, 2), (key2340, 2), (key2340, 2)]

theorem rawRowCheck2632 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form11 = rawRow2632 := by decide +kernel

def row2632 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

theorem rowCheck2632 : row2632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2632 := by decide +kernel

theorem rowEval2632 (x : Key → ℝ) : Integer.Sparse.eval row2632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2632, Integer.Sparse.eval_collectBalanced, rawRowCheck2632]

def rawRow2633 : Integer.Sparse Key := [(key2007, -2), (key2007, -2), (key2007, -2), (key2006, 6), (key2313, 2), (key2313, 2), (key2313, 2), (key2299, -2), (key2299, -2), (key2299, -2), (key2349, -6), (key2340, 2), (key2340, 2), (key2340, 2)]

theorem rawRowCheck2633 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form11 = rawRow2633 := by decide +kernel

def row2633 : Integer.Sparse Key := [(key2006, 6), (key2007, -6), (key2299, -6), (key2313, 6), (key2340, 6), (key2349, -6)]

theorem rowCheck2633 : row2633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2633 := by decide +kernel

theorem rowEval2633 (x : Key → ℝ) : Integer.Sparse.eval row2633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2633, Integer.Sparse.eval_collectBalanced, rawRowCheck2633]

def rawRow2634 : Integer.Sparse Key := [(key2299, -2), (key2300, -2), (key2300, -2), (key2340, 6), (key2006, 2), (key2007, 2), (key2007, 2), (key2340, -2), (key2340, -2), (key2349, -2), (key2007, -6), (key2300, 2), (key2300, 2), (key2313, 2)]

theorem rawRowCheck2634 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form11 = rawRow2634 := by decide +kernel

def row2634 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

theorem rowCheck2634 : row2634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2634 := by decide +kernel

theorem rowEval2634 (x : Key → ℝ) : Integer.Sparse.eval row2634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form11) x := by
  rw [rowCheck2634, Integer.Sparse.eval_collectBalanced, rawRowCheck2634]

def rawRow2635 : Integer.Sparse Key := [(key2300, -2), (key2299, -2), (key2300, -2), (key2340, 6), (key2007, 2), (key2006, 2), (key2007, 2), (key2340, -2), (key2349, -2), (key2340, -2), (key2007, -6), (key2300, 2), (key2313, 2), (key2300, 2)]

theorem rawRowCheck2635 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form11 = rawRow2635 := by decide +kernel

def row2635 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

theorem rowCheck2635 : row2635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2635 := by decide +kernel

theorem rowEval2635 (x : Key → ℝ) : Integer.Sparse.eval row2635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2635, Integer.Sparse.eval_collectBalanced, rawRowCheck2635]

def rawRow2636 : Integer.Sparse Key := [(key2300, -2), (key2300, -2), (key2299, -2), (key2340, 6), (key2007, 2), (key2007, 2), (key2006, 2), (key2349, -2), (key2340, -2), (key2340, -2), (key2007, -6), (key2313, 2), (key2300, 2), (key2300, 2)]

theorem rawRowCheck2636 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form11 = rawRow2636 := by decide +kernel

def row2636 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

theorem rowCheck2636 : row2636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2636 := by decide +kernel

theorem rowEval2636 (x : Key → ℝ) : Integer.Sparse.eval row2636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2636, Integer.Sparse.eval_collectBalanced, rawRowCheck2636]

def rawRow2637 : Integer.Sparse Key := [(key2300, -2), (key2300, -2), (key2340, -2), (key2299, 6), (key2313, 2), (key2313, 2), (key2349, 2), (key2006, -2), (key2299, -2), (key2299, -2), (key2313, -6), (key2007, 2), (key2300, 2), (key2300, 2)]

theorem rawRowCheck2637 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form11 = rawRow2637 := by decide +kernel

def row2637 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

theorem rowCheck2637 : row2637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2637 := by decide +kernel

theorem rowEval2637 (x : Key → ℝ) : Integer.Sparse.eval row2637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2637, Integer.Sparse.eval_collectBalanced, rawRowCheck2637]

def rawRow2638 : Integer.Sparse Key := [(key2300, -2), (key2340, -2), (key2300, -2), (key2299, 6), (key2313, 2), (key2349, 2), (key2313, 2), (key2299, -2), (key2006, -2), (key2299, -2), (key2313, -6), (key2300, 2), (key2007, 2), (key2300, 2)]

theorem rawRowCheck2638 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form11 = rawRow2638 := by decide +kernel

def row2638 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

theorem rowCheck2638 : row2638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2638 := by decide +kernel

theorem rowEval2638 (x : Key → ℝ) : Integer.Sparse.eval row2638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2638, Integer.Sparse.eval_collectBalanced, rawRowCheck2638]

def rawRow2639 : Integer.Sparse Key := [(key2340, -2), (key2300, -2), (key2300, -2), (key2299, 6), (key2349, 2), (key2313, 2), (key2313, 2), (key2299, -2), (key2299, -2), (key2006, -2), (key2313, -6), (key2300, 2), (key2300, 2), (key2007, 2)]

theorem rawRowCheck2639 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form11 = rawRow2639 := by decide +kernel

def row2639 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

theorem rowCheck2639 : row2639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2639 := by decide +kernel

theorem rowEval2639 (x : Key → ℝ) : Integer.Sparse.eval row2639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2639, Integer.Sparse.eval_collectBalanced, rawRowCheck2639]

def rawRow2640 : Integer.Sparse Key := [(key2313, -2), (key2313, -2), (key2313, -2), (key2349, 6), (key2007, 2), (key2007, 2), (key2007, 2), (key2340, -2), (key2340, -2), (key2340, -2), (key2006, -6), (key2299, 2), (key2299, 2), (key2299, 2)]

theorem rawRowCheck2640 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form11 = rawRow2640 := by decide +kernel

def row2640 : Integer.Sparse Key := [(key2006, -6), (key2007, 6), (key2299, 6), (key2313, -6), (key2340, -6), (key2349, 6)]

theorem rowCheck2640 : row2640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2640 := by decide +kernel

theorem rowEval2640 (x : Key → ℝ) : Integer.Sparse.eval row2640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2640, Integer.Sparse.eval_collectBalanced, rawRowCheck2640]

def rawRow2641 : Integer.Sparse Key := [(key2313, -2), (key2313, -2), (key2349, -2), (key2313, 6), (key2300, 2), (key2300, 2), (key2340, 2), (key2007, -2), (key2300, -2), (key2300, -2), (key2299, -6), (key2006, 2), (key2299, 2), (key2299, 2)]

theorem rawRowCheck2641 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form11 = rawRow2641 := by decide +kernel

def row2641 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

theorem rowCheck2641 : row2641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2641 := by decide +kernel

theorem rowEval2641 (x : Key → ℝ) : Integer.Sparse.eval row2641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2641, Integer.Sparse.eval_collectBalanced, rawRowCheck2641]

def rawRow2642 : Integer.Sparse Key := [(key2313, -2), (key2349, -2), (key2313, -2), (key2313, 6), (key2300, 2), (key2340, 2), (key2300, 2), (key2300, -2), (key2007, -2), (key2300, -2), (key2299, -6), (key2299, 2), (key2006, 2), (key2299, 2)]

theorem rawRowCheck2642 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form11 = rawRow2642 := by decide +kernel

def row2642 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

theorem rowCheck2642 : row2642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2642 := by decide +kernel

theorem rowEval2642 (x : Key → ℝ) : Integer.Sparse.eval row2642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2642, Integer.Sparse.eval_collectBalanced, rawRowCheck2642]

def rawRow2643 : Integer.Sparse Key := [(key2349, -2), (key2313, -2), (key2313, -2), (key2313, 6), (key2340, 2), (key2300, 2), (key2300, 2), (key2300, -2), (key2300, -2), (key2007, -2), (key2299, -6), (key2299, 2), (key2299, 2), (key2006, 2)]

theorem rawRowCheck2643 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form11 = rawRow2643 := by decide +kernel

def row2643 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

theorem rowCheck2643 : row2643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2643 := by decide +kernel

theorem rowEval2643 (x : Key → ℝ) : Integer.Sparse.eval row2643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2643, Integer.Sparse.eval_collectBalanced, rawRowCheck2643]

def rawRow2644 : Integer.Sparse Key := [(key2091, -2), (key2092, -2), (key2092, -2), (key2091, 1), (key2092, 1), (key2091, 1), (key2095, 1), (key2092, 1), (key2095, 1), (key2193, 2), (key2194, 2), (key2194, 2), (key2193, -1), (key2194, -1), (key2193, -1), (key2200, -1), (key2194, -1), (key2200, -1), (key2302, -1), (key2303, -1), (key2302, -1), (key2305, -1), (key2303, -1), (key2305, -1), (key2302, 1), (key2303, 1), (key2302, 1), (key2310, 1), (key2303, 1), (key2310, 1)]

theorem rawRowCheck2644 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form12 = rawRow2644 := by decide +kernel

def row2644 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

theorem rowCheck2644 : row2644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2644 := by decide +kernel

theorem rowEval2644 (x : Key → ℝ) : Integer.Sparse.eval row2644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form12) x := by
  rw [rowCheck2644, Integer.Sparse.eval_collectBalanced, rawRowCheck2644]

def rawRow2645 : Integer.Sparse Key := [(key2092, -2), (key2091, -2), (key2092, -2), (key2092, 1), (key2091, 1), (key2095, 1), (key2091, 1), (key2095, 1), (key2092, 1), (key2194, 2), (key2193, 2), (key2194, 2), (key2194, -1), (key2193, -1), (key2200, -1), (key2193, -1), (key2200, -1), (key2194, -1), (key2303, -1), (key2302, -1), (key2305, -1), (key2302, -1), (key2305, -1), (key2303, -1), (key2303, 1), (key2302, 1), (key2310, 1), (key2302, 1), (key2310, 1), (key2303, 1)]

theorem rawRowCheck2645 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form12 = rawRow2645 := by decide +kernel

def row2645 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

theorem rowCheck2645 : row2645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2645 := by decide +kernel

theorem rowEval2645 (x : Key → ℝ) : Integer.Sparse.eval row2645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2645, Integer.Sparse.eval_collectBalanced, rawRowCheck2645]

def rawRow2646 : Integer.Sparse Key := [(key2092, -2), (key2092, -2), (key2091, -2), (key2095, 1), (key2095, 1), (key2092, 1), (key2092, 1), (key2091, 1), (key2091, 1), (key2194, 2), (key2194, 2), (key2193, 2), (key2200, -1), (key2200, -1), (key2194, -1), (key2194, -1), (key2193, -1), (key2193, -1), (key2305, -1), (key2305, -1), (key2303, -1), (key2303, -1), (key2302, -1), (key2302, -1), (key2310, 1), (key2310, 1), (key2303, 1), (key2303, 1), (key2302, 1), (key2302, 1)]

theorem rawRowCheck2646 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form12 = rawRow2646 := by decide +kernel

def row2646 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

theorem rowCheck2646 : row2646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2646 := by decide +kernel

theorem rowEval2646 (x : Key → ℝ) : Integer.Sparse.eval row2646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2646, Integer.Sparse.eval_collectBalanced, rawRowCheck2646]

def rawRow2647 : Integer.Sparse Key := [(key2095, -2), (key2095, -2), (key2095, -2), (key2092, 1), (key2092, 1), (key2092, 1), (key2092, 1), (key2092, 1), (key2092, 1), (key2200, 2), (key2200, 2), (key2200, 2), (key2194, -1), (key2194, -1), (key2194, -1), (key2194, -1), (key2194, -1), (key2194, -1), (key2310, -1), (key2310, -1), (key2310, -1), (key2310, -1), (key2310, -1), (key2310, -1), (key2305, 1), (key2305, 1), (key2305, 1), (key2305, 1), (key2305, 1), (key2305, 1)]

theorem rawRowCheck2647 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form12 = rawRow2647 := by decide +kernel

def row2647 : Integer.Sparse Key := [(key2092, 6), (key2095, -6), (key2194, -6), (key2200, 6), (key2305, 6), (key2310, -6)]

theorem rowCheck2647 : row2647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2647 := by decide +kernel

theorem rowEval2647 (x : Key → ℝ) : Integer.Sparse.eval row2647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2647, Integer.Sparse.eval_collectBalanced, rawRowCheck2647]

def rawRow2648 : Integer.Sparse Key := [(key2193, -2), (key2194, -2), (key2194, -2), (key2302, 1), (key2303, 1), (key2302, 1), (key2305, 1), (key2303, 1), (key2305, 1), (key2091, 2), (key2092, 2), (key2092, 2), (key2302, -1), (key2303, -1), (key2302, -1), (key2310, -1), (key2303, -1), (key2310, -1), (key2091, -1), (key2092, -1), (key2091, -1), (key2095, -1), (key2092, -1), (key2095, -1), (key2193, 1), (key2194, 1), (key2193, 1), (key2200, 1), (key2194, 1), (key2200, 1)]

theorem rawRowCheck2648 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form12 = rawRow2648 := by decide +kernel

def row2648 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

theorem rowCheck2648 : row2648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2648 := by decide +kernel

theorem rowEval2648 (x : Key → ℝ) : Integer.Sparse.eval row2648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form12) x := by
  rw [rowCheck2648, Integer.Sparse.eval_collectBalanced, rawRowCheck2648]

def rawRow2649 : Integer.Sparse Key := [(key2194, -2), (key2193, -2), (key2194, -2), (key2303, 1), (key2302, 1), (key2305, 1), (key2302, 1), (key2305, 1), (key2303, 1), (key2092, 2), (key2091, 2), (key2092, 2), (key2303, -1), (key2302, -1), (key2310, -1), (key2302, -1), (key2310, -1), (key2303, -1), (key2092, -1), (key2091, -1), (key2095, -1), (key2091, -1), (key2095, -1), (key2092, -1), (key2194, 1), (key2193, 1), (key2200, 1), (key2193, 1), (key2200, 1), (key2194, 1)]

theorem rawRowCheck2649 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form12 = rawRow2649 := by decide +kernel

def row2649 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

theorem rowCheck2649 : row2649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2649 := by decide +kernel

theorem rowEval2649 (x : Key → ℝ) : Integer.Sparse.eval row2649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2649, Integer.Sparse.eval_collectBalanced, rawRowCheck2649]

def rawRow2650 : Integer.Sparse Key := [(key2194, -2), (key2194, -2), (key2193, -2), (key2305, 1), (key2305, 1), (key2303, 1), (key2303, 1), (key2302, 1), (key2302, 1), (key2092, 2), (key2092, 2), (key2091, 2), (key2310, -1), (key2310, -1), (key2303, -1), (key2303, -1), (key2302, -1), (key2302, -1), (key2095, -1), (key2095, -1), (key2092, -1), (key2092, -1), (key2091, -1), (key2091, -1), (key2200, 1), (key2200, 1), (key2194, 1), (key2194, 1), (key2193, 1), (key2193, 1)]

theorem rawRowCheck2650 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form12 = rawRow2650 := by decide +kernel

def row2650 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

theorem rowCheck2650 : row2650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2650 := by decide +kernel

theorem rowEval2650 (x : Key → ℝ) : Integer.Sparse.eval row2650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2650, Integer.Sparse.eval_collectBalanced, rawRowCheck2650]

def rawRow2651 : Integer.Sparse Key := [(key2305, -2), (key2305, -2), (key2343, -2), (key2194, 1), (key2194, 1), (key2303, 1), (key2303, 1), (key2341, 1), (key2341, 1), (key2310, 2), (key2310, 2), (key2347, 2), (key2092, -1), (key2092, -1), (key2303, -1), (key2303, -1), (key2341, -1), (key2341, -1), (key2200, -1), (key2200, -1), (key2310, -1), (key2310, -1), (key2347, -1), (key2347, -1), (key2095, 1), (key2095, 1), (key2305, 1), (key2305, 1), (key2343, 1), (key2343, 1)]

theorem rawRowCheck2651 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form12 = rawRow2651 := by decide +kernel

def row2651 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

theorem rowCheck2651 : row2651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2651 := by decide +kernel

theorem rowEval2651 (x : Key → ℝ) : Integer.Sparse.eval row2651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2651, Integer.Sparse.eval_collectBalanced, rawRowCheck2651]

def rawRow2652 : Integer.Sparse Key := [(key2305, -2), (key2343, -2), (key2305, -2), (key2303, 1), (key2341, 1), (key2194, 1), (key2341, 1), (key2194, 1), (key2303, 1), (key2310, 2), (key2347, 2), (key2310, 2), (key2303, -1), (key2341, -1), (key2092, -1), (key2341, -1), (key2092, -1), (key2303, -1), (key2310, -1), (key2347, -1), (key2200, -1), (key2347, -1), (key2200, -1), (key2310, -1), (key2305, 1), (key2343, 1), (key2095, 1), (key2343, 1), (key2095, 1), (key2305, 1)]

theorem rawRowCheck2652 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form12 = rawRow2652 := by decide +kernel

def row2652 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

theorem rowCheck2652 : row2652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2652 := by decide +kernel

theorem rowEval2652 (x : Key → ℝ) : Integer.Sparse.eval row2652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2652, Integer.Sparse.eval_collectBalanced, rawRowCheck2652]

def rawRow2653 : Integer.Sparse Key := [(key2343, -2), (key2305, -2), (key2305, -2), (key2341, 1), (key2303, 1), (key2341, 1), (key2194, 1), (key2303, 1), (key2194, 1), (key2347, 2), (key2310, 2), (key2310, 2), (key2341, -1), (key2303, -1), (key2341, -1), (key2092, -1), (key2303, -1), (key2092, -1), (key2347, -1), (key2310, -1), (key2347, -1), (key2200, -1), (key2310, -1), (key2200, -1), (key2343, 1), (key2305, 1), (key2343, 1), (key2095, 1), (key2305, 1), (key2095, 1)]

theorem rawRowCheck2653 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form12 = rawRow2653 := by decide +kernel

def row2653 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

theorem rowCheck2653 : row2653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2653 := by decide +kernel

theorem rowEval2653 (x : Key → ℝ) : Integer.Sparse.eval row2653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2653, Integer.Sparse.eval_collectBalanced, rawRowCheck2653]

def rawRow2654 : Integer.Sparse Key := [(key2200, -2), (key2200, -2), (key2200, -2), (key2310, 1), (key2310, 1), (key2310, 1), (key2310, 1), (key2310, 1), (key2310, 1), (key2095, 2), (key2095, 2), (key2095, 2), (key2305, -1), (key2305, -1), (key2305, -1), (key2305, -1), (key2305, -1), (key2305, -1), (key2092, -1), (key2092, -1), (key2092, -1), (key2092, -1), (key2092, -1), (key2092, -1), (key2194, 1), (key2194, 1), (key2194, 1), (key2194, 1), (key2194, 1), (key2194, 1)]

theorem rawRowCheck2654 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form12 = rawRow2654 := by decide +kernel

def row2654 : Integer.Sparse Key := [(key2092, -6), (key2095, 6), (key2194, 6), (key2200, -6), (key2305, -6), (key2310, 6)]

theorem rowCheck2654 : row2654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2654 := by decide +kernel

theorem rowEval2654 (x : Key → ℝ) : Integer.Sparse.eval row2654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2654, Integer.Sparse.eval_collectBalanced, rawRowCheck2654]

def rawRow2655 : Integer.Sparse Key := [(key2310, -2), (key2310, -2), (key2347, -2), (key2200, 1), (key2200, 1), (key2310, 1), (key2310, 1), (key2347, 1), (key2347, 1), (key2305, 2), (key2305, 2), (key2343, 2), (key2095, -1), (key2095, -1), (key2305, -1), (key2305, -1), (key2343, -1), (key2343, -1), (key2194, -1), (key2194, -1), (key2303, -1), (key2303, -1), (key2341, -1), (key2341, -1), (key2092, 1), (key2092, 1), (key2303, 1), (key2303, 1), (key2341, 1), (key2341, 1)]

theorem rawRowCheck2655 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form12 = rawRow2655 := by decide +kernel

def row2655 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

theorem rowCheck2655 : row2655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2655 := by decide +kernel

theorem rowEval2655 (x : Key → ℝ) : Integer.Sparse.eval row2655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2655, Integer.Sparse.eval_collectBalanced, rawRowCheck2655]

def rawRow2656 : Integer.Sparse Key := [(key2310, -2), (key2347, -2), (key2310, -2), (key2310, 1), (key2347, 1), (key2200, 1), (key2347, 1), (key2200, 1), (key2310, 1), (key2305, 2), (key2343, 2), (key2305, 2), (key2305, -1), (key2343, -1), (key2095, -1), (key2343, -1), (key2095, -1), (key2305, -1), (key2303, -1), (key2341, -1), (key2194, -1), (key2341, -1), (key2194, -1), (key2303, -1), (key2303, 1), (key2341, 1), (key2092, 1), (key2341, 1), (key2092, 1), (key2303, 1)]

theorem rawRowCheck2656 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form12 = rawRow2656 := by decide +kernel

def row2656 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

theorem rowCheck2656 : row2656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2656 := by decide +kernel

theorem rowEval2656 (x : Key → ℝ) : Integer.Sparse.eval row2656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2656, Integer.Sparse.eval_collectBalanced, rawRowCheck2656]

def rawRow2657 : Integer.Sparse Key := [(key2347, -2), (key2310, -2), (key2310, -2), (key2347, 1), (key2310, 1), (key2347, 1), (key2200, 1), (key2310, 1), (key2200, 1), (key2343, 2), (key2305, 2), (key2305, 2), (key2343, -1), (key2305, -1), (key2343, -1), (key2095, -1), (key2305, -1), (key2095, -1), (key2341, -1), (key2303, -1), (key2341, -1), (key2194, -1), (key2303, -1), (key2194, -1), (key2341, 1), (key2303, 1), (key2341, 1), (key2092, 1), (key2303, 1), (key2092, 1)]

theorem rawRowCheck2657 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form12 = rawRow2657 := by decide +kernel

def row2657 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

theorem rowCheck2657 : row2657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2657 := by decide +kernel

theorem rowEval2657 (x : Key → ℝ) : Integer.Sparse.eval row2657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2657, Integer.Sparse.eval_collectBalanced, rawRowCheck2657]

def rawRow2658 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key778, -2), (key778, 6), (key801, 2), (key803, 2), (key803, 2), (key803, -2), (key803, -2), (key811, -2), (key836, -6), (key836, 2), (key836, 2), (key839, 2)]

theorem rawRowCheck2658 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form13 = rawRow2658 := by decide +kernel

def row2658 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -2), (key836, -2), (key839, 2)]

theorem rowCheck2658 : row2658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2658 := by decide +kernel

theorem rowEval2658 (x : Key → ℝ) : Integer.Sparse.eval row2658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form13) x := by
  rw [rowCheck2658, Integer.Sparse.eval_collectBalanced, rawRowCheck2658]

def rawRow2659 : Integer.Sparse Key := [(key778, -2), (key776, -2), (key778, -2), (key778, 6), (key803, 2), (key801, 2), (key803, 2), (key803, -2), (key811, -2), (key803, -2), (key836, -6), (key836, 2), (key839, 2), (key836, 2)]

theorem rawRowCheck2659 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form13 = rawRow2659 := by decide +kernel

def row2659 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -2), (key836, -2), (key839, 2)]

theorem rowCheck2659 : row2659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2659 := by decide +kernel

theorem rowEval2659 (x : Key → ℝ) : Integer.Sparse.eval row2659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2659, Integer.Sparse.eval_collectBalanced, rawRowCheck2659]

def rawRow2660 : Integer.Sparse Key := [(key778, -2), (key778, -2), (key776, -2), (key778, 6), (key803, 2), (key803, 2), (key801, 2), (key811, -2), (key803, -2), (key803, -2), (key836, -6), (key839, 2), (key836, 2), (key836, 2)]

theorem rawRowCheck2660 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form13 = rawRow2660 := by decide +kernel

def row2660 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -2), (key836, -2), (key839, 2)]

theorem rowCheck2660 : row2660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2660 := by decide +kernel

theorem rowEval2660 (x : Key → ℝ) : Integer.Sparse.eval row2660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2660, Integer.Sparse.eval_collectBalanced, rawRowCheck2660]

def rawRow2661 : Integer.Sparse Key := [(key778, -2), (key778, -2), (key778, -2), (key776, 6), (key811, 2), (key811, 2), (key811, 2), (key801, -2), (key801, -2), (key801, -2), (key839, -6), (key836, 2), (key836, 2), (key836, 2)]

theorem rawRowCheck2661 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form13 = rawRow2661 := by decide +kernel

def row2661 : Integer.Sparse Key := [(key776, 6), (key778, -6), (key801, -6), (key811, 6), (key836, 6), (key839, -6)]

theorem rowCheck2661 : row2661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2661 := by decide +kernel

theorem rowEval2661 (x : Key → ℝ) : Integer.Sparse.eval row2661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2661, Integer.Sparse.eval_collectBalanced, rawRowCheck2661]

def rawRow2662 : Integer.Sparse Key := [(key801, -2), (key803, -2), (key803, -2), (key811, 6), (key776, 2), (key778, 2), (key778, 2), (key836, -2), (key836, -2), (key839, -2), (key778, -6), (key803, 2), (key803, 2), (key811, 2)]

theorem rawRowCheck2662 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form13 = rawRow2662 := by decide +kernel

def row2662 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 8), (key836, -4), (key839, -2)]

theorem rowCheck2662 : row2662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2662 := by decide +kernel

theorem rowEval2662 (x : Key → ℝ) : Integer.Sparse.eval row2662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form13) x := by
  rw [rowCheck2662, Integer.Sparse.eval_collectBalanced, rawRowCheck2662]

def rawRow2663 : Integer.Sparse Key := [(key803, -2), (key801, -2), (key803, -2), (key811, 6), (key778, 2), (key776, 2), (key778, 2), (key836, -2), (key839, -2), (key836, -2), (key778, -6), (key803, 2), (key811, 2), (key803, 2)]

theorem rawRowCheck2663 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form13 = rawRow2663 := by decide +kernel

def row2663 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 8), (key836, -4), (key839, -2)]

theorem rowCheck2663 : row2663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2663 := by decide +kernel

theorem rowEval2663 (x : Key → ℝ) : Integer.Sparse.eval row2663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2663, Integer.Sparse.eval_collectBalanced, rawRowCheck2663]

def rawRow2664 : Integer.Sparse Key := [(key803, -2), (key803, -2), (key801, -2), (key811, 6), (key778, 2), (key778, 2), (key776, 2), (key839, -2), (key836, -2), (key836, -2), (key778, -6), (key811, 2), (key803, 2), (key803, 2)]

theorem rawRowCheck2664 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form13 = rawRow2664 := by decide +kernel

def row2664 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 8), (key836, -4), (key839, -2)]

theorem rowCheck2664 : row2664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2664 := by decide +kernel

theorem rowEval2664 (x : Key → ℝ) : Integer.Sparse.eval row2664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2664, Integer.Sparse.eval_collectBalanced, rawRowCheck2664]

def rawRow2665 : Integer.Sparse Key := [(key803, -2), (key803, -2), (key811, -2), (key801, 6), (key836, 2), (key836, 2), (key839, 2), (key776, -2), (key801, -2), (key801, -2), (key811, -6), (key778, 2), (key803, 2), (key803, 2)]

theorem rawRowCheck2665 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form13 = rawRow2665 := by decide +kernel

def row2665 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -8), (key836, 4), (key839, 2)]

theorem rowCheck2665 : row2665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2665 := by decide +kernel

theorem rowEval2665 (x : Key → ℝ) : Integer.Sparse.eval row2665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2665, Integer.Sparse.eval_collectBalanced, rawRowCheck2665]

def rawRow2666 : Integer.Sparse Key := [(key803, -2), (key811, -2), (key803, -2), (key801, 6), (key836, 2), (key839, 2), (key836, 2), (key801, -2), (key776, -2), (key801, -2), (key811, -6), (key803, 2), (key778, 2), (key803, 2)]

theorem rawRowCheck2666 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form13 = rawRow2666 := by decide +kernel

def row2666 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -8), (key836, 4), (key839, 2)]

theorem rowCheck2666 : row2666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2666 := by decide +kernel

theorem rowEval2666 (x : Key → ℝ) : Integer.Sparse.eval row2666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2666, Integer.Sparse.eval_collectBalanced, rawRowCheck2666]

def rawRow2667 : Integer.Sparse Key := [(key811, -2), (key803, -2), (key803, -2), (key801, 6), (key839, 2), (key836, 2), (key836, 2), (key801, -2), (key801, -2), (key776, -2), (key811, -6), (key803, 2), (key803, 2), (key778, 2)]

theorem rawRowCheck2667 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form13 = rawRow2667 := by decide +kernel

def row2667 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -8), (key836, 4), (key839, 2)]

theorem rowCheck2667 : row2667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2667 := by decide +kernel

theorem rowEval2667 (x : Key → ℝ) : Integer.Sparse.eval row2667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2667, Integer.Sparse.eval_collectBalanced, rawRowCheck2667]

def rawRow2668 : Integer.Sparse Key := [(key836, -2), (key836, -2), (key836, -2), (key839, 6), (key778, 2), (key778, 2), (key778, 2), (key811, -2), (key811, -2), (key811, -2), (key776, -6), (key801, 2), (key801, 2), (key801, 2)]

theorem rawRowCheck2668 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form13 = rawRow2668 := by decide +kernel

def row2668 : Integer.Sparse Key := [(key776, -6), (key778, 6), (key801, 6), (key811, -6), (key836, -6), (key839, 6)]

theorem rowCheck2668 : row2668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2668 := by decide +kernel

theorem rowEval2668 (x : Key → ℝ) : Integer.Sparse.eval row2668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2668, Integer.Sparse.eval_collectBalanced, rawRowCheck2668]

def rawRow2669 : Integer.Sparse Key := [(key836, -2), (key836, -2), (key839, -2), (key836, 6), (key803, 2), (key803, 2), (key811, 2), (key778, -2), (key803, -2), (key803, -2), (key801, -6), (key776, 2), (key801, 2), (key801, 2)]

theorem rawRowCheck2669 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form13 = rawRow2669 := by decide +kernel

def row2669 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 2), (key836, 2), (key839, -2)]

theorem rowCheck2669 : row2669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2669 := by decide +kernel

theorem rowEval2669 (x : Key → ℝ) : Integer.Sparse.eval row2669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2669, Integer.Sparse.eval_collectBalanced, rawRowCheck2669]

def rawRow2670 : Integer.Sparse Key := [(key836, -2), (key839, -2), (key836, -2), (key836, 6), (key803, 2), (key811, 2), (key803, 2), (key803, -2), (key778, -2), (key803, -2), (key801, -6), (key801, 2), (key776, 2), (key801, 2)]

theorem rawRowCheck2670 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form13 = rawRow2670 := by decide +kernel

def row2670 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 2), (key836, 2), (key839, -2)]

theorem rowCheck2670 : row2670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2670 := by decide +kernel

theorem rowEval2670 (x : Key → ℝ) : Integer.Sparse.eval row2670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2670, Integer.Sparse.eval_collectBalanced, rawRowCheck2670]

def rawRow2671 : Integer.Sparse Key := [(key839, -2), (key836, -2), (key836, -2), (key836, 6), (key811, 2), (key803, 2), (key803, 2), (key803, -2), (key803, -2), (key778, -2), (key801, -6), (key801, 2), (key801, 2), (key776, 2)]

theorem rawRowCheck2671 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form13 = rawRow2671 := by decide +kernel

def row2671 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 2), (key836, 2), (key839, -2)]

theorem rowCheck2671 : row2671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2671 := by decide +kernel

theorem rowEval2671 (x : Key → ℝ) : Integer.Sparse.eval row2671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2671, Integer.Sparse.eval_collectBalanced, rawRowCheck2671]

def rawRow2672 : Integer.Sparse Key := [(key2407, -2), (key2441, -2), (key2441, -2), (key2410, 1), (key2410, 1), (key2441, 1), (key2441, 1), (key2445, 1), (key2445, 1), (key2473, 2), (key2507, 2), (key2507, 2), (key2483, -1), (key2483, -1), (key2507, -1), (key2507, -1), (key2526, -1), (key2526, -1), (key2539, -1), (key2539, -1), (key2555, -1), (key2555, -1), (key2557, -1), (key2557, -1), (key2544, 1), (key2544, 1), (key2555, 1), (key2555, 1), (key2565, 1), (key2565, 1)]

theorem rawRowCheck2672 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form0 = rawRow2672 := by decide +kernel

def row2672 : Integer.Sparse Key := [(key2407, -2), (key2410, 2), (key2441, -2), (key2445, 2), (key2473, 2), (key2483, -2), (key2507, 2), (key2526, -2), (key2539, -2), (key2544, 2), (key2557, -2), (key2565, 2)]

theorem rowCheck2672 : row2672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2672 := by decide +kernel

theorem rowEval2672 (x : Key → ℝ) : Integer.Sparse.eval row2672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2672, Integer.Sparse.eval_collectBalanced, rawRowCheck2672]

def rawRow2673 : Integer.Sparse Key := [(key2441, -2), (key2407, -2), (key2441, -2), (key2441, 1), (key2445, 1), (key2410, 1), (key2445, 1), (key2410, 1), (key2441, 1), (key2507, 2), (key2473, 2), (key2507, 2), (key2507, -1), (key2526, -1), (key2483, -1), (key2526, -1), (key2483, -1), (key2507, -1), (key2555, -1), (key2557, -1), (key2539, -1), (key2557, -1), (key2539, -1), (key2555, -1), (key2555, 1), (key2565, 1), (key2544, 1), (key2565, 1), (key2544, 1), (key2555, 1)]

theorem rawRowCheck2673 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form0 = rawRow2673 := by decide +kernel

def row2673 : Integer.Sparse Key := [(key2407, -2), (key2410, 2), (key2441, -2), (key2445, 2), (key2473, 2), (key2483, -2), (key2507, 2), (key2526, -2), (key2539, -2), (key2544, 2), (key2557, -2), (key2565, 2)]

theorem rowCheck2673 : row2673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2673 := by decide +kernel

theorem rowEval2673 (x : Key → ℝ) : Integer.Sparse.eval row2673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2673, Integer.Sparse.eval_collectBalanced, rawRowCheck2673]

def rawRow2674 : Integer.Sparse Key := [(key2441, -2), (key2441, -2), (key2407, -2), (key2445, 1), (key2441, 1), (key2445, 1), (key2410, 1), (key2441, 1), (key2410, 1), (key2507, 2), (key2507, 2), (key2473, 2), (key2526, -1), (key2507, -1), (key2526, -1), (key2483, -1), (key2507, -1), (key2483, -1), (key2557, -1), (key2555, -1), (key2557, -1), (key2539, -1), (key2555, -1), (key2539, -1), (key2565, 1), (key2555, 1), (key2565, 1), (key2544, 1), (key2555, 1), (key2544, 1)]

theorem rawRowCheck2674 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form0 = rawRow2674 := by decide +kernel

def row2674 : Integer.Sparse Key := [(key2407, -2), (key2410, 2), (key2441, -2), (key2445, 2), (key2473, 2), (key2483, -2), (key2507, 2), (key2526, -2), (key2539, -2), (key2544, 2), (key2557, -2), (key2565, 2)]

theorem rowCheck2674 : row2674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2674 := by decide +kernel

theorem rowEval2674 (x : Key → ℝ) : Integer.Sparse.eval row2674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2674, Integer.Sparse.eval_collectBalanced, rawRowCheck2674]

def rawRow2675 : Integer.Sparse Key := [(key2410, -2), (key2410, -2), (key2445, -2), (key2407, 1), (key2410, 1), (key2407, 1), (key2441, 1), (key2410, 1), (key2441, 1), (key2483, 2), (key2483, 2), (key2526, 2), (key2473, -1), (key2483, -1), (key2473, -1), (key2507, -1), (key2483, -1), (key2507, -1), (key2544, -1), (key2545, -1), (key2544, -1), (key2565, -1), (key2545, -1), (key2565, -1), (key2539, 1), (key2545, 1), (key2539, 1), (key2557, 1), (key2545, 1), (key2557, 1)]

theorem rawRowCheck2675 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form0 = rawRow2675 := by decide +kernel

def row2675 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2473, -2), (key2483, 2), (key2507, -2), (key2526, 2), (key2539, 2), (key2544, -2), (key2557, 2), (key2565, -2)]

theorem rowCheck2675 : row2675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2675 := by decide +kernel

theorem rowEval2675 (x : Key → ℝ) : Integer.Sparse.eval row2675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2675, Integer.Sparse.eval_collectBalanced, rawRowCheck2675]

def rawRow2676 : Integer.Sparse Key := [(key2410, -2), (key2445, -2), (key2410, -2), (key2410, 1), (key2407, 1), (key2441, 1), (key2407, 1), (key2441, 1), (key2410, 1), (key2483, 2), (key2526, 2), (key2483, 2), (key2483, -1), (key2473, -1), (key2507, -1), (key2473, -1), (key2507, -1), (key2483, -1), (key2545, -1), (key2544, -1), (key2565, -1), (key2544, -1), (key2565, -1), (key2545, -1), (key2545, 1), (key2539, 1), (key2557, 1), (key2539, 1), (key2557, 1), (key2545, 1)]

theorem rawRowCheck2676 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form0 = rawRow2676 := by decide +kernel

def row2676 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2473, -2), (key2483, 2), (key2507, -2), (key2526, 2), (key2539, 2), (key2544, -2), (key2557, 2), (key2565, -2)]

theorem rowCheck2676 : row2676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2676 := by decide +kernel

theorem rowEval2676 (x : Key → ℝ) : Integer.Sparse.eval row2676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2676, Integer.Sparse.eval_collectBalanced, rawRowCheck2676]

def rawRow2677 : Integer.Sparse Key := [(key2445, -2), (key2410, -2), (key2410, -2), (key2441, 1), (key2441, 1), (key2410, 1), (key2410, 1), (key2407, 1), (key2407, 1), (key2526, 2), (key2483, 2), (key2483, 2), (key2507, -1), (key2507, -1), (key2483, -1), (key2483, -1), (key2473, -1), (key2473, -1), (key2565, -1), (key2565, -1), (key2545, -1), (key2545, -1), (key2544, -1), (key2544, -1), (key2557, 1), (key2557, 1), (key2545, 1), (key2545, 1), (key2539, 1), (key2539, 1)]

theorem rawRowCheck2677 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form0 = rawRow2677 := by decide +kernel

def row2677 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2473, -2), (key2483, 2), (key2507, -2), (key2526, 2), (key2539, 2), (key2544, -2), (key2557, 2), (key2565, -2)]

theorem rowCheck2677 : row2677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2677 := by decide +kernel

theorem rowEval2677 (x : Key → ℝ) : Integer.Sparse.eval row2677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2677, Integer.Sparse.eval_collectBalanced, rawRowCheck2677]

def rawRow2678 : Integer.Sparse Key := [(key2848, -2), (key2970, -2), (key2970, -2), (key2882, 1), (key2882, 1), (key2991, 1), (key2991, 1), (key2993, 1), (key2993, 1), (key2407, 2), (key2441, 2), (key2441, 2), (key2544, -1), (key2544, -1), (key2555, -1), (key2555, -1), (key2565, -1), (key2565, -1), (key2410, -1), (key2410, -1), (key2441, -1), (key2441, -1), (key2445, -1), (key2445, -1), (key2483, 1), (key2483, 1), (key2507, 1), (key2507, 1), (key2526, 1), (key2526, 1)]

theorem rawRowCheck2678 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form0 = rawRow2678 := by decide +kernel

def row2678 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2970, -4), (key2991, 2), (key2993, 2)]

theorem rowCheck2678 : row2678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2678 := by decide +kernel

theorem rowEval2678 (x : Key → ℝ) : Integer.Sparse.eval row2678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2678, Integer.Sparse.eval_collectBalanced, rawRowCheck2678]

def rawRow2679 : Integer.Sparse Key := [(key2970, -2), (key2848, -2), (key2970, -2), (key2991, 1), (key2993, 1), (key2882, 1), (key2993, 1), (key2882, 1), (key2991, 1), (key2441, 2), (key2407, 2), (key2441, 2), (key2555, -1), (key2565, -1), (key2544, -1), (key2565, -1), (key2544, -1), (key2555, -1), (key2441, -1), (key2445, -1), (key2410, -1), (key2445, -1), (key2410, -1), (key2441, -1), (key2507, 1), (key2526, 1), (key2483, 1), (key2526, 1), (key2483, 1), (key2507, 1)]

theorem rawRowCheck2679 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form0 = rawRow2679 := by decide +kernel

def row2679 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2970, -4), (key2991, 2), (key2993, 2)]

theorem rowCheck2679 : row2679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2679 := by decide +kernel

theorem rowEval2679 (x : Key → ℝ) : Integer.Sparse.eval row2679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2679, Integer.Sparse.eval_collectBalanced, rawRowCheck2679]

def rawRow2680 : Integer.Sparse Key := [(key2970, -2), (key2970, -2), (key2848, -2), (key2993, 1), (key2991, 1), (key2993, 1), (key2882, 1), (key2991, 1), (key2882, 1), (key2441, 2), (key2441, 2), (key2407, 2), (key2565, -1), (key2555, -1), (key2565, -1), (key2544, -1), (key2555, -1), (key2544, -1), (key2445, -1), (key2441, -1), (key2445, -1), (key2410, -1), (key2441, -1), (key2410, -1), (key2526, 1), (key2507, 1), (key2526, 1), (key2483, 1), (key2507, 1), (key2483, 1)]

theorem rawRowCheck2680 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form0 = rawRow2680 := by decide +kernel

def row2680 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2970, -4), (key2991, 2), (key2993, 2)]

theorem rowCheck2680 : row2680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2680 := by decide +kernel

theorem rowEval2680 (x : Key → ℝ) : Integer.Sparse.eval row2680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2680, Integer.Sparse.eval_collectBalanced, rawRowCheck2680]

def rawRow2681 : Integer.Sparse Key := [(key2595, -2), (key2882, -2), (key2993, -2), (key2592, 1), (key2595, 1), (key2848, 1), (key2970, 1), (key2882, 1), (key2991, 1), (key2602, 2), (key2912, 2), (key3003, 2), (key2379, -1), (key2393, -1), (key2407, -1), (key2441, -1), (key2544, -1), (key2555, -1), (key2393, -1), (key2395, -1), (key2483, -1), (key2526, -1), (key2545, -1), (key2565, -1), (key2382, 1), (key2395, 1), (key2410, 1), (key2445, 1), (key2545, 1), (key2557, 1)]

theorem rawRowCheck2681 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form0 = rawRow2681 := by decide +kernel

def row2681 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, -2), (key2407, -1), (key2410, 1), (key2441, -1), (key2445, 1), (key2483, -1), (key2526, -1), (key2544, -1), (key2555, -1), (key2557, 1), (key2565, -1), (key2592, 1), (key2595, -1), (key2602, 2), (key2848, 1), (key2882, -1), (key2912, 2), (key2970, 1), (key2991, 1), (key2993, -2), (key3003, 2)]

theorem rowCheck2681 : row2681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2681 := by decide +kernel

theorem rowEval2681 (x : Key → ℝ) : Integer.Sparse.eval row2681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2681, Integer.Sparse.eval_collectBalanced, rawRowCheck2681]

def rawRow2682 : Integer.Sparse Key := [(key2595, -2), (key2993, -2), (key2882, -2), (key2595, 1), (key2592, 1), (key2970, 1), (key2848, 1), (key2991, 1), (key2882, 1), (key2602, 2), (key3003, 2), (key2912, 2), (key2393, -1), (key2379, -1), (key2441, -1), (key2407, -1), (key2555, -1), (key2544, -1), (key2395, -1), (key2393, -1), (key2526, -1), (key2483, -1), (key2565, -1), (key2545, -1), (key2395, 1), (key2382, 1), (key2445, 1), (key2410, 1), (key2557, 1), (key2545, 1)]

theorem rawRowCheck2682 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form0 = rawRow2682 := by decide +kernel

def row2682 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, -2), (key2407, -1), (key2410, 1), (key2441, -1), (key2445, 1), (key2483, -1), (key2526, -1), (key2544, -1), (key2555, -1), (key2557, 1), (key2565, -1), (key2592, 1), (key2595, -1), (key2602, 2), (key2848, 1), (key2882, -1), (key2912, 2), (key2970, 1), (key2991, 1), (key2993, -2), (key3003, 2)]

theorem rowCheck2682 : row2682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2682 := by decide +kernel

theorem rowEval2682 (x : Key → ℝ) : Integer.Sparse.eval row2682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2682, Integer.Sparse.eval_collectBalanced, rawRowCheck2682]

def rawRow2683 : Integer.Sparse Key := [(key2882, -2), (key2595, -2), (key2993, -2), (key2848, 1), (key2882, 1), (key2592, 1), (key2991, 1), (key2595, 1), (key2970, 1), (key2912, 2), (key2602, 2), (key3003, 2), (key2771, -1), (key2912, -1), (key2592, -1), (key2991, -1), (key2393, -1), (key2441, -1), (key2483, -1), (key2545, -1), (key2393, -1), (key2565, -1), (key2395, -1), (key2526, -1), (key2410, 1), (key2545, 1), (key2382, 1), (key2557, 1), (key2395, 1), (key2445, 1)]

theorem rawRowCheck2683 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form0 = rawRow2683 := by decide +kernel

def row2683 : Integer.Sparse Key := [(key2382, 1), (key2393, -2), (key2410, 1), (key2441, -1), (key2445, 1), (key2483, -1), (key2526, -1), (key2557, 1), (key2565, -1), (key2595, -1), (key2602, 2), (key2771, -1), (key2848, 1), (key2882, -1), (key2912, 1), (key2970, 1), (key2993, -2), (key3003, 2)]

theorem rowCheck2683 : row2683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2683 := by decide +kernel

theorem rowEval2683 (x : Key → ℝ) : Integer.Sparse.eval row2683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2683, Integer.Sparse.eval_collectBalanced, rawRowCheck2683]

def rawRow2684 : Integer.Sparse Key := [(key2882, -2), (key2993, -2), (key2595, -2), (key2882, 1), (key2848, 1), (key2991, 1), (key2592, 1), (key2970, 1), (key2595, 1), (key2912, 2), (key3003, 2), (key2602, 2), (key2912, -1), (key2771, -1), (key2991, -1), (key2592, -1), (key2441, -1), (key2393, -1), (key2545, -1), (key2483, -1), (key2565, -1), (key2393, -1), (key2526, -1), (key2395, -1), (key2545, 1), (key2410, 1), (key2557, 1), (key2382, 1), (key2445, 1), (key2395, 1)]

theorem rawRowCheck2684 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form0 = rawRow2684 := by decide +kernel

def row2684 : Integer.Sparse Key := [(key2382, 1), (key2393, -2), (key2410, 1), (key2441, -1), (key2445, 1), (key2483, -1), (key2526, -1), (key2557, 1), (key2565, -1), (key2595, -1), (key2602, 2), (key2771, -1), (key2848, 1), (key2882, -1), (key2912, 1), (key2970, 1), (key2993, -2), (key3003, 2)]

theorem rowCheck2684 : row2684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2684 := by decide +kernel

theorem rowEval2684 (x : Key → ℝ) : Integer.Sparse.eval row2684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck2684, Integer.Sparse.eval_collectBalanced, rawRowCheck2684]

def rawRow2685 : Integer.Sparse Key := [(key2993, -2), (key2595, -2), (key2882, -2), (key2970, 1), (key2991, 1), (key2595, 1), (key2882, 1), (key2592, 1), (key2848, 1), (key3003, 2), (key2602, 2), (key2912, 2), (key2933, -1), (key2991, -1), (key2602, -1), (key2912, -1), (key2379, -1), (key2407, -1), (key2526, -1), (key2565, -1), (key2395, -1), (key2545, -1), (key2393, -1), (key2483, -1), (key2445, 1), (key2557, 1), (key2395, 1), (key2545, 1), (key2382, 1), (key2410, 1)]

theorem rawRowCheck2685 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form0 = rawRow2685 := by decide +kernel

def row2685 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, -1), (key2407, -1), (key2410, 1), (key2445, 1), (key2483, -1), (key2526, -1), (key2557, 1), (key2565, -1), (key2592, 1), (key2595, -1), (key2602, 1), (key2848, 1), (key2882, -1), (key2912, 1), (key2933, -1), (key2970, 1), (key2993, -2), (key3003, 2)]

theorem rowCheck2685 : row2685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2685 := by decide +kernel

theorem rowEval2685 (x : Key → ℝ) : Integer.Sparse.eval row2685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2685, Integer.Sparse.eval_collectBalanced, rawRowCheck2685]

def rawRow2686 : Integer.Sparse Key := [(key2993, -2), (key2882, -2), (key2595, -2), (key2991, 1), (key2970, 1), (key2882, 1), (key2595, 1), (key2848, 1), (key2592, 1), (key3003, 2), (key2912, 2), (key2602, 2), (key2991, -1), (key2933, -1), (key2912, -1), (key2602, -1), (key2771, -1), (key2592, -1), (key2565, -1), (key2526, -1), (key2545, -1), (key2395, -1), (key2483, -1), (key2393, -1), (key2557, 1), (key2445, 1), (key2545, 1), (key2395, 1), (key2410, 1), (key2382, 1)]

theorem rawRowCheck2686 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form0 = rawRow2686 := by decide +kernel

def row2686 : Integer.Sparse Key := [(key2382, 1), (key2393, -1), (key2410, 1), (key2445, 1), (key2483, -1), (key2526, -1), (key2557, 1), (key2565, -1), (key2595, -1), (key2602, 1), (key2771, -1), (key2848, 1), (key2882, -1), (key2912, 1), (key2933, -1), (key2970, 1), (key2993, -2), (key3003, 2)]

theorem rowCheck2686 : row2686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2686 := by decide +kernel

theorem rowEval2686 (x : Key → ℝ) : Integer.Sparse.eval row2686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck2686, Integer.Sparse.eval_collectBalanced, rawRowCheck2686]

def rawRow2687 : Integer.Sparse Key := [(key2891, -2), (key2891, -2), (key2996, -2), (key2912, 1), (key2914, 1), (key2912, 1), (key3003, 1), (key2914, 1), (key3003, 1), (key2774, 2), (key2774, 2), (key2934, 2), (key2882, -1), (key2914, -1), (key2882, -1), (key2993, -1), (key2914, -1), (key2993, -1), (key2407, -1), (key2410, -1), (key2407, -1), (key2441, -1), (key2410, -1), (key2441, -1), (key2473, 1), (key2483, 1), (key2473, 1), (key2507, 1), (key2483, 1), (key2507, 1)]

theorem rawRowCheck2687 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form0 = rawRow2687 := by decide +kernel

def row2687 : Integer.Sparse Key := [(key2407, -2), (key2410, -2), (key2441, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2774, 4), (key2882, -2), (key2891, -4), (key2912, 2), (key2934, 2), (key2993, -2), (key2996, -2), (key3003, 2)]

theorem rowCheck2687 : row2687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2687 := by decide +kernel

theorem rowEval2687 (x : Key → ℝ) : Integer.Sparse.eval row2687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2687, Integer.Sparse.eval_collectBalanced, rawRowCheck2687]

end MUB6.Certificate.GramRows

end OAI
