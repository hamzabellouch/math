import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8320 : Integer.Sparse Key := [(key2568, -6), (key2568, -6), (key2575, -6), (key2570, -6), (key2404, 2), (key2404, 2), (key2435, 2), (key2376, 2), (key2376, 2), (key2470, 2), (key2470, 2), (key2501, 2), (key2501, 2), (key2388, 2), (key2478, 2), (key2478, 2)]

theorem rawRowCheck8320 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form4 = rawRow8320 := by decide +kernel

def row8320 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8320 : row8320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8320 := by decide +kernel

theorem rowEval8320 (x : Key → ℝ) : Integer.Sparse.eval row8320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8320, Integer.Sparse.eval_collectBalanced, rawRowCheck8320]

def rawRow8321 : Integer.Sparse Key := [(key2568, -6), (key2575, -6), (key2568, -6), (key2570, -6), (key2404, 2), (key2435, 2), (key2404, 2), (key2470, 2), (key2501, 2), (key2376, 2), (key2501, 2), (key2376, 2), (key2470, 2), (key2478, 2), (key2388, 2), (key2478, 2)]

theorem rawRowCheck8321 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form4 = rawRow8321 := by decide +kernel

def row8321 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8321 : row8321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8321 := by decide +kernel

theorem rowEval8321 (x : Key → ℝ) : Integer.Sparse.eval row8321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8321, Integer.Sparse.eval_collectBalanced, rawRowCheck8321]

def rawRow8322 : Integer.Sparse Key := [(key2575, -6), (key2568, -6), (key2568, -6), (key2570, -6), (key2435, 2), (key2404, 2), (key2404, 2), (key2501, 2), (key2470, 2), (key2501, 2), (key2376, 2), (key2470, 2), (key2376, 2), (key2478, 2), (key2478, 2), (key2388, 2)]

theorem rawRowCheck8322 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form4 = rawRow8322 := by decide +kernel

def row8322 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8322 : row8322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8322 := by decide +kernel

theorem rowEval8322 (x : Key → ℝ) : Integer.Sparse.eval row8322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8322, Integer.Sparse.eval_collectBalanced, rawRowCheck8322]

def rawRow8323 : Integer.Sparse Key := [(key2568, -6), (key2570, -6), (key2575, -6), (key2568, -6), (key2470, 2), (key2478, 2), (key2501, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2478, 2), (key2435, 2), (key2501, 2), (key2376, 2), (key2404, 2), (key2470, 2)]

theorem rawRowCheck8323 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form4 = rawRow8323 := by decide +kernel

def row8323 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8323 : row8323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8323 := by decide +kernel

theorem rowEval8323 (x : Key → ℝ) : Integer.Sparse.eval row8323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8323, Integer.Sparse.eval_collectBalanced, rawRowCheck8323]

def rawRow8324 : Integer.Sparse Key := [(key2570, -6), (key2568, -6), (key2575, -6), (key2568, -6), (key2478, 2), (key2470, 2), (key2501, 2), (key2388, 2), (key2376, 2), (key2478, 2), (key2404, 2), (key2501, 2), (key2435, 2), (key2376, 2), (key2470, 2), (key2404, 2)]

theorem rawRowCheck8324 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form4 = rawRow8324 := by decide +kernel

def row8324 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8324 : row8324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8324 := by decide +kernel

theorem rowEval8324 (x : Key → ℝ) : Integer.Sparse.eval row8324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8324, Integer.Sparse.eval_collectBalanced, rawRowCheck8324]

def rawRow8325 : Integer.Sparse Key := [(key2568, -6), (key2575, -6), (key2570, -6), (key2568, -6), (key2470, 2), (key2501, 2), (key2478, 2), (key2404, 2), (key2435, 2), (key2376, 2), (key2501, 2), (key2388, 2), (key2478, 2), (key2404, 2), (key2376, 2), (key2470, 2)]

theorem rawRowCheck8325 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form4 = rawRow8325 := by decide +kernel

def row8325 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8325 : row8325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8325 := by decide +kernel

theorem rowEval8325 (x : Key → ℝ) : Integer.Sparse.eval row8325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8325, Integer.Sparse.eval_collectBalanced, rawRowCheck8325]

def rawRow8326 : Integer.Sparse Key := [(key2575, -6), (key2568, -6), (key2570, -6), (key2568, -6), (key2501, 2), (key2470, 2), (key2478, 2), (key2435, 2), (key2404, 2), (key2501, 2), (key2376, 2), (key2478, 2), (key2388, 2), (key2404, 2), (key2470, 2), (key2376, 2)]

theorem rawRowCheck8326 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form4 = rawRow8326 := by decide +kernel

def row8326 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8326 : row8326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8326 := by decide +kernel

theorem rowEval8326 (x : Key → ℝ) : Integer.Sparse.eval row8326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8326, Integer.Sparse.eval_collectBalanced, rawRowCheck8326]

def rawRow8327 : Integer.Sparse Key := [(key2570, -6), (key2575, -6), (key2568, -6), (key2568, -6), (key2478, 2), (key2501, 2), (key2470, 2), (key2478, 2), (key2501, 2), (key2388, 2), (key2435, 2), (key2376, 2), (key2404, 2), (key2470, 2), (key2376, 2), (key2404, 2)]

theorem rawRowCheck8327 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form4 = rawRow8327 := by decide +kernel

def row8327 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8327 : row8327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8327 := by decide +kernel

theorem rowEval8327 (x : Key → ℝ) : Integer.Sparse.eval row8327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8327, Integer.Sparse.eval_collectBalanced, rawRowCheck8327]

def rawRow8328 : Integer.Sparse Key := [(key2575, -6), (key2570, -6), (key2568, -6), (key2568, -6), (key2501, 2), (key2478, 2), (key2470, 2), (key2501, 2), (key2478, 2), (key2435, 2), (key2388, 2), (key2404, 2), (key2376, 2), (key2470, 2), (key2404, 2), (key2376, 2)]

theorem rawRowCheck8328 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form4 = rawRow8328 := by decide +kernel

def row8328 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8328 : row8328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8328 := by decide +kernel

theorem rowEval8328 (x : Key → ℝ) : Integer.Sparse.eval row8328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8328, Integer.Sparse.eval_collectBalanced, rawRowCheck8328]

def rawRow8329 : Integer.Sparse Key := [(key2657, -2), (key2657, -2), (key2659, -2), (key2752, -2), (key2752, -2), (key2918, -2), (key2918, -2), (key2919, -2), (key2919, -2), (key2757, -2), (key2922, -2), (key2922, -2), (key2614, 1), (key2614, 1), (key2630, 1), (key2630, 1), (key2638, 1), (key2638, 1), (key2669, 1), (key2669, 1), (key2784, 1), (key2784, 1), (key2792, 1), (key2792, 1), (key2704, 1), (key2704, 1), (key2807, 1), (key2807, 1), (key2858, 1), (key2858, 1), (key2724, 1), (key2724, 1), (key2827, 1), (key2827, 1), (key2868, 1), (key2868, 1)]

theorem rawRowCheck8329 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form5 = rawRow8329 := by decide +kernel

def row8329 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

theorem rowCheck8329 : row8329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8329 := by decide +kernel

theorem rowEval8329 (x : Key → ℝ) : Integer.Sparse.eval row8329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8329, Integer.Sparse.eval_collectBalanced, rawRowCheck8329]

def rawRow8330 : Integer.Sparse Key := [(key2657, -2), (key2659, -2), (key2657, -2), (key2918, -2), (key2919, -2), (key2752, -2), (key2919, -2), (key2752, -2), (key2918, -2), (key2922, -2), (key2757, -2), (key2922, -2), (key2630, 1), (key2638, 1), (key2614, 1), (key2638, 1), (key2614, 1), (key2630, 1), (key2784, 1), (key2792, 1), (key2669, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2807, 1), (key2858, 1), (key2704, 1), (key2858, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2868, 1), (key2724, 1), (key2868, 1), (key2724, 1), (key2827, 1)]

theorem rawRowCheck8330 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form5 = rawRow8330 := by decide +kernel

def row8330 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

theorem rowCheck8330 : row8330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8330 := by decide +kernel

theorem rowEval8330 (x : Key → ℝ) : Integer.Sparse.eval row8330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8330, Integer.Sparse.eval_collectBalanced, rawRowCheck8330]

def rawRow8331 : Integer.Sparse Key := [(key2659, -2), (key2657, -2), (key2657, -2), (key2919, -2), (key2918, -2), (key2919, -2), (key2752, -2), (key2918, -2), (key2752, -2), (key2922, -2), (key2922, -2), (key2757, -2), (key2638, 1), (key2630, 1), (key2638, 1), (key2614, 1), (key2630, 1), (key2614, 1), (key2792, 1), (key2784, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2669, 1), (key2858, 1), (key2807, 1), (key2858, 1), (key2704, 1), (key2807, 1), (key2704, 1), (key2868, 1), (key2827, 1), (key2868, 1), (key2724, 1), (key2827, 1), (key2724, 1)]

theorem rawRowCheck8331 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form5 = rawRow8331 := by decide +kernel

def row8331 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

theorem rowCheck8331 : row8331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8331 := by decide +kernel

theorem rowEval8331 (x : Key → ℝ) : Integer.Sparse.eval row8331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8331, Integer.Sparse.eval_collectBalanced, rawRowCheck8331]

def rawRow8332 : Integer.Sparse Key := [(key2752, -2), (key2752, -2), (key2757, -2), (key2657, -2), (key2657, -2), (key2918, -2), (key2918, -2), (key2922, -2), (key2922, -2), (key2659, -2), (key2919, -2), (key2919, -2), (key2669, 1), (key2669, 1), (key2704, 1), (key2704, 1), (key2724, 1), (key2724, 1), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1), (key2630, 1), (key2630, 1), (key2784, 1), (key2784, 1), (key2868, 1), (key2868, 1), (key2638, 1), (key2638, 1), (key2792, 1), (key2792, 1), (key2858, 1), (key2858, 1)]

theorem rawRowCheck8332 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form5 = rawRow8332 := by decide +kernel

def row8332 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

theorem rowCheck8332 : row8332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8332 := by decide +kernel

theorem rowEval8332 (x : Key → ℝ) : Integer.Sparse.eval row8332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8332, Integer.Sparse.eval_collectBalanced, rawRowCheck8332]

def rawRow8333 : Integer.Sparse Key := [(key2752, -2), (key2757, -2), (key2752, -2), (key2918, -2), (key2922, -2), (key2657, -2), (key2922, -2), (key2657, -2), (key2918, -2), (key2919, -2), (key2659, -2), (key2919, -2), (key2704, 1), (key2724, 1), (key2669, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2784, 1), (key2868, 1), (key2630, 1), (key2868, 1), (key2630, 1), (key2784, 1), (key2792, 1), (key2858, 1), (key2638, 1), (key2858, 1), (key2638, 1), (key2792, 1)]

theorem rawRowCheck8333 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form5 = rawRow8333 := by decide +kernel

def row8333 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

theorem rowCheck8333 : row8333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8333 := by decide +kernel

theorem rowEval8333 (x : Key → ℝ) : Integer.Sparse.eval row8333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8333, Integer.Sparse.eval_collectBalanced, rawRowCheck8333]

def rawRow8334 : Integer.Sparse Key := [(key2757, -2), (key2752, -2), (key2752, -2), (key2922, -2), (key2918, -2), (key2922, -2), (key2657, -2), (key2918, -2), (key2657, -2), (key2919, -2), (key2919, -2), (key2659, -2), (key2724, 1), (key2704, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key2669, 1), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1), (key2868, 1), (key2784, 1), (key2868, 1), (key2630, 1), (key2784, 1), (key2630, 1), (key2858, 1), (key2792, 1), (key2858, 1), (key2638, 1), (key2792, 1), (key2638, 1)]

theorem rawRowCheck8334 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form5 = rawRow8334 := by decide +kernel

def row8334 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

theorem rowCheck8334 : row8334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8334 := by decide +kernel

theorem rowEval8334 (x : Key → ℝ) : Integer.Sparse.eval row8334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8334, Integer.Sparse.eval_collectBalanced, rawRowCheck8334]

def rawRow8335 : Integer.Sparse Key := [(key2918, -2), (key2919, -2), (key2922, -2), (key2657, -2), (key2659, -2), (key2752, -2), (key2919, -2), (key2757, -2), (key2922, -2), (key2657, -2), (key2752, -2), (key2918, -2), (key2784, 1), (key2792, 1), (key2807, 1), (key2858, 1), (key2827, 1), (key2868, 1), (key2630, 1), (key2638, 1), (key2704, 1), (key2858, 1), (key2724, 1), (key2868, 1), (key2614, 1), (key2638, 1), (key2669, 1), (key2792, 1), (key2724, 1), (key2827, 1), (key2614, 1), (key2630, 1), (key2669, 1), (key2784, 1), (key2704, 1), (key2807, 1)]

theorem rawRowCheck8335 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form5 = rawRow8335 := by decide +kernel

def row8335 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

theorem rowCheck8335 : row8335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8335 := by decide +kernel

theorem rowEval8335 (x : Key → ℝ) : Integer.Sparse.eval row8335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8335, Integer.Sparse.eval_collectBalanced, rawRowCheck8335]

def rawRow8336 : Integer.Sparse Key := [(key2919, -2), (key2918, -2), (key2922, -2), (key2659, -2), (key2657, -2), (key2919, -2), (key2752, -2), (key2922, -2), (key2757, -2), (key2657, -2), (key2918, -2), (key2752, -2), (key2792, 1), (key2784, 1), (key2858, 1), (key2807, 1), (key2868, 1), (key2827, 1), (key2638, 1), (key2630, 1), (key2858, 1), (key2704, 1), (key2868, 1), (key2724, 1), (key2638, 1), (key2614, 1), (key2792, 1), (key2669, 1), (key2827, 1), (key2724, 1), (key2630, 1), (key2614, 1), (key2784, 1), (key2669, 1), (key2807, 1), (key2704, 1)]

theorem rawRowCheck8336 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form5 = rawRow8336 := by decide +kernel

def row8336 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

theorem rowCheck8336 : row8336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8336 := by decide +kernel

theorem rowEval8336 (x : Key → ℝ) : Integer.Sparse.eval row8336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8336, Integer.Sparse.eval_collectBalanced, rawRowCheck8336]

def rawRow8337 : Integer.Sparse Key := [(key2918, -2), (key2922, -2), (key2919, -2), (key2752, -2), (key2757, -2), (key2657, -2), (key2922, -2), (key2659, -2), (key2919, -2), (key2752, -2), (key2657, -2), (key2918, -2), (key2807, 1), (key2827, 1), (key2784, 1), (key2868, 1), (key2792, 1), (key2858, 1), (key2704, 1), (key2724, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2858, 1), (key2669, 1), (key2724, 1), (key2614, 1), (key2827, 1), (key2638, 1), (key2792, 1), (key2669, 1), (key2704, 1), (key2614, 1), (key2807, 1), (key2630, 1), (key2784, 1)]

theorem rawRowCheck8337 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form5 = rawRow8337 := by decide +kernel

def row8337 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

theorem rowCheck8337 : row8337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8337 := by decide +kernel

theorem rowEval8337 (x : Key → ℝ) : Integer.Sparse.eval row8337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8337, Integer.Sparse.eval_collectBalanced, rawRowCheck8337]

def rawRow8338 : Integer.Sparse Key := [(key2922, -2), (key2918, -2), (key2919, -2), (key2757, -2), (key2752, -2), (key2922, -2), (key2657, -2), (key2919, -2), (key2659, -2), (key2752, -2), (key2918, -2), (key2657, -2), (key2827, 1), (key2807, 1), (key2868, 1), (key2784, 1), (key2858, 1), (key2792, 1), (key2724, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2858, 1), (key2638, 1), (key2724, 1), (key2669, 1), (key2827, 1), (key2614, 1), (key2792, 1), (key2638, 1), (key2704, 1), (key2669, 1), (key2807, 1), (key2614, 1), (key2784, 1), (key2630, 1)]

theorem rawRowCheck8338 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form5 = rawRow8338 := by decide +kernel

def row8338 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

theorem rowCheck8338 : row8338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8338 := by decide +kernel

theorem rowEval8338 (x : Key → ℝ) : Integer.Sparse.eval row8338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8338, Integer.Sparse.eval_collectBalanced, rawRowCheck8338]

def rawRow8339 : Integer.Sparse Key := [(key2919, -2), (key2922, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key2659, -2), (key2757, -2), (key2657, -2), (key2752, -2), (key2918, -2), (key2657, -2), (key2752, -2), (key2858, 1), (key2868, 1), (key2792, 1), (key2827, 1), (key2784, 1), (key2807, 1), (key2858, 1), (key2868, 1), (key2638, 1), (key2724, 1), (key2630, 1), (key2704, 1), (key2792, 1), (key2827, 1), (key2638, 1), (key2724, 1), (key2614, 1), (key2669, 1), (key2784, 1), (key2807, 1), (key2630, 1), (key2704, 1), (key2614, 1), (key2669, 1)]

theorem rawRowCheck8339 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form5 = rawRow8339 := by decide +kernel

def row8339 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

theorem rowCheck8339 : row8339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8339 := by decide +kernel

theorem rowEval8339 (x : Key → ℝ) : Integer.Sparse.eval row8339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8339, Integer.Sparse.eval_collectBalanced, rawRowCheck8339]

def rawRow8340 : Integer.Sparse Key := [(key2922, -2), (key2919, -2), (key2918, -2), (key2922, -2), (key2919, -2), (key2757, -2), (key2659, -2), (key2752, -2), (key2657, -2), (key2918, -2), (key2752, -2), (key2657, -2), (key2868, 1), (key2858, 1), (key2827, 1), (key2792, 1), (key2807, 1), (key2784, 1), (key2868, 1), (key2858, 1), (key2724, 1), (key2638, 1), (key2704, 1), (key2630, 1), (key2827, 1), (key2792, 1), (key2724, 1), (key2638, 1), (key2669, 1), (key2614, 1), (key2807, 1), (key2784, 1), (key2704, 1), (key2630, 1), (key2669, 1), (key2614, 1)]

theorem rawRowCheck8340 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form5 = rawRow8340 := by decide +kernel

def row8340 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

theorem rowCheck8340 : row8340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8340 := by decide +kernel

theorem rowEval8340 (x : Key → ℝ) : Integer.Sparse.eval row8340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8340, Integer.Sparse.eval_collectBalanced, rawRowCheck8340]

def rawRow8341 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2764, 6), (key2841, 6), (key2873, 6)]

theorem rawRowCheck8341 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form6 = rawRow8341 := by decide +kernel

def row8341 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8341 : row8341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8341 := by decide +kernel

theorem rowEval8341 (x : Key → ℝ) : Integer.Sparse.eval row8341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8341, Integer.Sparse.eval_collectBalanced, rawRowCheck8341]

def rawRow8342 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2764, 6), (key2873, 6), (key2841, 6)]

theorem rawRowCheck8342 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form6 = rawRow8342 := by decide +kernel

def row8342 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8342 : row8342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8342 := by decide +kernel

theorem rowEval8342 (x : Key → ℝ) : Integer.Sparse.eval row8342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8342, Integer.Sparse.eval_collectBalanced, rawRowCheck8342]

def rawRow8343 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2841, 6), (key2764, 6), (key2873, 6)]

theorem rawRowCheck8343 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form6 = rawRow8343 := by decide +kernel

def row8343 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8343 : row8343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8343 := by decide +kernel

theorem rowEval8343 (x : Key → ℝ) : Integer.Sparse.eval row8343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8343, Integer.Sparse.eval_collectBalanced, rawRowCheck8343]

def rawRow8344 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2841, 6), (key2873, 6), (key2764, 6)]

theorem rawRowCheck8344 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form6 = rawRow8344 := by decide +kernel

def row8344 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8344 : row8344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8344 := by decide +kernel

theorem rowEval8344 (x : Key → ℝ) : Integer.Sparse.eval row8344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8344, Integer.Sparse.eval_collectBalanced, rawRowCheck8344]

def rawRow8345 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2873, 6), (key2764, 6), (key2841, 6)]

theorem rawRowCheck8345 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form6 = rawRow8345 := by decide +kernel

def row8345 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8345 : row8345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8345 := by decide +kernel

theorem rowEval8345 (x : Key → ℝ) : Integer.Sparse.eval row8345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8345, Integer.Sparse.eval_collectBalanced, rawRowCheck8345]

def rawRow8346 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2873, 6), (key2841, 6), (key2764, 6)]

theorem rawRowCheck8346 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form6 = rawRow8346 := by decide +kernel

def row8346 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8346 : row8346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8346 := by decide +kernel

theorem rowEval8346 (x : Key → ℝ) : Integer.Sparse.eval row8346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8346, Integer.Sparse.eval_collectBalanced, rawRowCheck8346]

def rawRow8347 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2585, 6), (key2841, 6), (key2873, 6)]

theorem rawRowCheck8347 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form6 = rawRow8347 := by decide +kernel

def row8347 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8347 : row8347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8347 := by decide +kernel

theorem rowEval8347 (x : Key → ℝ) : Integer.Sparse.eval row8347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8347, Integer.Sparse.eval_collectBalanced, rawRowCheck8347]

def rawRow8348 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2585, 6), (key2873, 6), (key2841, 6)]

theorem rawRowCheck8348 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form6 = rawRow8348 := by decide +kernel

def row8348 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8348 : row8348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8348 := by decide +kernel

theorem rowEval8348 (x : Key → ℝ) : Integer.Sparse.eval row8348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8348, Integer.Sparse.eval_collectBalanced, rawRowCheck8348]

def rawRow8349 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2841, 6), (key2585, 6), (key2873, 6)]

theorem rawRowCheck8349 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form6 = rawRow8349 := by decide +kernel

def row8349 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8349 : row8349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8349 := by decide +kernel

theorem rowEval8349 (x : Key → ℝ) : Integer.Sparse.eval row8349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8349, Integer.Sparse.eval_collectBalanced, rawRowCheck8349]

def rawRow8350 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2841, 6), (key2873, 6), (key2585, 6)]

theorem rawRowCheck8350 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form6 = rawRow8350 := by decide +kernel

def row8350 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8350 : row8350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8350 := by decide +kernel

theorem rowEval8350 (x : Key → ℝ) : Integer.Sparse.eval row8350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8350, Integer.Sparse.eval_collectBalanced, rawRowCheck8350]

def rawRow8351 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2873, 6), (key2585, 6), (key2841, 6)]

theorem rawRowCheck8351 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form6 = rawRow8351 := by decide +kernel

def row8351 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8351 : row8351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8351 := by decide +kernel

theorem rowEval8351 (x : Key → ℝ) : Integer.Sparse.eval row8351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8351, Integer.Sparse.eval_collectBalanced, rawRowCheck8351]

def rawRow8352 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2873, 6), (key2841, 6), (key2585, 6)]

theorem rawRowCheck8352 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form6 = rawRow8352 := by decide +kernel

def row8352 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8352 : row8352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8352 := by decide +kernel

theorem rowEval8352 (x : Key → ℝ) : Integer.Sparse.eval row8352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8352, Integer.Sparse.eval_collectBalanced, rawRowCheck8352]

def rawRow8353 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2585, 6), (key2764, 6), (key2873, 6)]

theorem rawRowCheck8353 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form6 = rawRow8353 := by decide +kernel

def row8353 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8353 : row8353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8353 := by decide +kernel

theorem rowEval8353 (x : Key → ℝ) : Integer.Sparse.eval row8353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8353, Integer.Sparse.eval_collectBalanced, rawRowCheck8353]

def rawRow8354 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2585, 6), (key2873, 6), (key2764, 6)]

theorem rawRowCheck8354 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form6 = rawRow8354 := by decide +kernel

def row8354 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8354 : row8354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8354 := by decide +kernel

theorem rowEval8354 (x : Key → ℝ) : Integer.Sparse.eval row8354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8354, Integer.Sparse.eval_collectBalanced, rawRowCheck8354]

def rawRow8355 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2764, 6), (key2585, 6), (key2873, 6)]

theorem rawRowCheck8355 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form6 = rawRow8355 := by decide +kernel

def row8355 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8355 : row8355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8355 := by decide +kernel

theorem rowEval8355 (x : Key → ℝ) : Integer.Sparse.eval row8355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8355, Integer.Sparse.eval_collectBalanced, rawRowCheck8355]

def rawRow8356 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2764, 6), (key2873, 6), (key2585, 6)]

theorem rawRowCheck8356 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form6 = rawRow8356 := by decide +kernel

def row8356 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8356 : row8356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8356 := by decide +kernel

theorem rowEval8356 (x : Key → ℝ) : Integer.Sparse.eval row8356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8356, Integer.Sparse.eval_collectBalanced, rawRowCheck8356]

def rawRow8357 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2873, 6), (key2585, 6), (key2764, 6)]

theorem rawRowCheck8357 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form6 = rawRow8357 := by decide +kernel

def row8357 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8357 : row8357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8357 := by decide +kernel

theorem rowEval8357 (x : Key → ℝ) : Integer.Sparse.eval row8357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8357, Integer.Sparse.eval_collectBalanced, rawRowCheck8357]

def rawRow8358 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2873, 6), (key2764, 6), (key2585, 6)]

theorem rawRowCheck8358 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form6 = rawRow8358 := by decide +kernel

def row8358 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8358 : row8358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8358 := by decide +kernel

theorem rowEval8358 (x : Key → ℝ) : Integer.Sparse.eval row8358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8358, Integer.Sparse.eval_collectBalanced, rawRowCheck8358]

def rawRow8359 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2585, 6), (key2764, 6), (key2841, 6)]

theorem rawRowCheck8359 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form6 = rawRow8359 := by decide +kernel

def row8359 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8359 : row8359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8359 := by decide +kernel

theorem rowEval8359 (x : Key → ℝ) : Integer.Sparse.eval row8359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8359, Integer.Sparse.eval_collectBalanced, rawRowCheck8359]

def rawRow8360 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2585, 6), (key2841, 6), (key2764, 6)]

theorem rawRowCheck8360 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form6 = rawRow8360 := by decide +kernel

def row8360 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8360 : row8360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8360 := by decide +kernel

theorem rowEval8360 (x : Key → ℝ) : Integer.Sparse.eval row8360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8360, Integer.Sparse.eval_collectBalanced, rawRowCheck8360]

def rawRow8361 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2764, 6), (key2585, 6), (key2841, 6)]

theorem rawRowCheck8361 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form6 = rawRow8361 := by decide +kernel

def row8361 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8361 : row8361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8361 := by decide +kernel

theorem rowEval8361 (x : Key → ℝ) : Integer.Sparse.eval row8361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8361, Integer.Sparse.eval_collectBalanced, rawRowCheck8361]

def rawRow8362 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2764, 6), (key2841, 6), (key2585, 6)]

theorem rawRowCheck8362 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form6 = rawRow8362 := by decide +kernel

def row8362 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8362 : row8362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8362 := by decide +kernel

theorem rowEval8362 (x : Key → ℝ) : Integer.Sparse.eval row8362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8362, Integer.Sparse.eval_collectBalanced, rawRowCheck8362]

def rawRow8363 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2841, 6), (key2585, 6), (key2764, 6)]

theorem rawRowCheck8363 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form6 = rawRow8363 := by decide +kernel

def row8363 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8363 : row8363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8363 := by decide +kernel

theorem rowEval8363 (x : Key → ℝ) : Integer.Sparse.eval row8363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8363, Integer.Sparse.eval_collectBalanced, rawRowCheck8363]

def rawRow8364 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2841, 6), (key2764, 6), (key2585, 6)]

theorem rawRowCheck8364 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form6 = rawRow8364 := by decide +kernel

def row8364 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

theorem rowCheck8364 : row8364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8364 := by decide +kernel

theorem rowEval8364 (x : Key → ℝ) : Integer.Sparse.eval row8364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8364, Integer.Sparse.eval_collectBalanced, rawRowCheck8364]

def rawRow8365 : Integer.Sparse Key := [(key2873, -24), (key2585, 6), (key2764, 6), (key2841, 6), (key2841, 6)]

theorem rawRowCheck8365 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form6 = rawRow8365 := by decide +kernel

def row8365 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

theorem rowCheck8365 : row8365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8365 := by decide +kernel

theorem rowEval8365 (x : Key → ℝ) : Integer.Sparse.eval row8365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8365, Integer.Sparse.eval_collectBalanced, rawRowCheck8365]

def rawRow8366 : Integer.Sparse Key := [(key2873, -24), (key2585, 6), (key2841, 6), (key2764, 6), (key2841, 6)]

theorem rawRowCheck8366 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form6 = rawRow8366 := by decide +kernel

def row8366 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

theorem rowCheck8366 : row8366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8366 := by decide +kernel

theorem rowEval8366 (x : Key → ℝ) : Integer.Sparse.eval row8366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8366, Integer.Sparse.eval_collectBalanced, rawRowCheck8366]

def rawRow8367 : Integer.Sparse Key := [(key2873, -24), (key2585, 6), (key2841, 6), (key2841, 6), (key2764, 6)]

theorem rawRowCheck8367 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form6 = rawRow8367 := by decide +kernel

def row8367 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

theorem rowCheck8367 : row8367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8367 := by decide +kernel

theorem rowEval8367 (x : Key → ℝ) : Integer.Sparse.eval row8367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8367, Integer.Sparse.eval_collectBalanced, rawRowCheck8367]

def rawRow8368 : Integer.Sparse Key := [(key2873, -24), (key2764, 6), (key2585, 6), (key2841, 6), (key2841, 6)]

theorem rawRowCheck8368 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form6 = rawRow8368 := by decide +kernel

def row8368 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

theorem rowCheck8368 : row8368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8368 := by decide +kernel

theorem rowEval8368 (x : Key → ℝ) : Integer.Sparse.eval row8368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8368, Integer.Sparse.eval_collectBalanced, rawRowCheck8368]

def rawRow8369 : Integer.Sparse Key := [(key2873, -24), (key2764, 6), (key2841, 6), (key2585, 6), (key2841, 6)]

theorem rawRowCheck8369 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form6 = rawRow8369 := by decide +kernel

def row8369 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

theorem rowCheck8369 : row8369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8369 := by decide +kernel

theorem rowEval8369 (x : Key → ℝ) : Integer.Sparse.eval row8369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8369, Integer.Sparse.eval_collectBalanced, rawRowCheck8369]

def rawRow8370 : Integer.Sparse Key := [(key2873, -24), (key2764, 6), (key2841, 6), (key2841, 6), (key2585, 6)]

theorem rawRowCheck8370 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form6 = rawRow8370 := by decide +kernel

def row8370 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

theorem rowCheck8370 : row8370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8370 := by decide +kernel

theorem rowEval8370 (x : Key → ℝ) : Integer.Sparse.eval row8370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8370, Integer.Sparse.eval_collectBalanced, rawRowCheck8370]

def rawRow8371 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2585, 6), (key2764, 6), (key2841, 6)]

theorem rawRowCheck8371 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form6 = rawRow8371 := by decide +kernel

def row8371 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

theorem rowCheck8371 : row8371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8371 := by decide +kernel

theorem rowEval8371 (x : Key → ℝ) : Integer.Sparse.eval row8371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8371, Integer.Sparse.eval_collectBalanced, rawRowCheck8371]

def rawRow8372 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2585, 6), (key2841, 6), (key2764, 6)]

theorem rawRowCheck8372 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form6 = rawRow8372 := by decide +kernel

def row8372 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

theorem rowCheck8372 : row8372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8372 := by decide +kernel

theorem rowEval8372 (x : Key → ℝ) : Integer.Sparse.eval row8372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8372, Integer.Sparse.eval_collectBalanced, rawRowCheck8372]

def rawRow8373 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2764, 6), (key2585, 6), (key2841, 6)]

theorem rawRowCheck8373 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form6 = rawRow8373 := by decide +kernel

def row8373 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

theorem rowCheck8373 : row8373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8373 := by decide +kernel

theorem rowEval8373 (x : Key → ℝ) : Integer.Sparse.eval row8373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8373, Integer.Sparse.eval_collectBalanced, rawRowCheck8373]

def rawRow8374 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2764, 6), (key2841, 6), (key2585, 6)]

theorem rawRowCheck8374 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form6 = rawRow8374 := by decide +kernel

def row8374 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

theorem rowCheck8374 : row8374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8374 := by decide +kernel

theorem rowEval8374 (x : Key → ℝ) : Integer.Sparse.eval row8374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8374, Integer.Sparse.eval_collectBalanced, rawRowCheck8374]

def rawRow8375 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2841, 6), (key2585, 6), (key2764, 6)]

theorem rawRowCheck8375 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form6 = rawRow8375 := by decide +kernel

def row8375 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

theorem rowCheck8375 : row8375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8375 := by decide +kernel

theorem rowEval8375 (x : Key → ℝ) : Integer.Sparse.eval row8375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8375, Integer.Sparse.eval_collectBalanced, rawRowCheck8375]

def rawRow8376 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2841, 6), (key2764, 6), (key2585, 6)]

theorem rawRowCheck8376 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form6 = rawRow8376 := by decide +kernel

def row8376 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

theorem rowCheck8376 : row8376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8376 := by decide +kernel

theorem rowEval8376 (x : Key → ℝ) : Integer.Sparse.eval row8376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8376, Integer.Sparse.eval_collectBalanced, rawRowCheck8376]

def rawRow8377 : Integer.Sparse Key := [(key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2851, -2), (key2918, -2), (key2858, -2), (key2919, -2), (key2827, -2), (key2868, -2), (key2922, -2), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2851, 2), (key3021, 2), (key2858, 2), (key3022, 2), (key2724, 2), (key2868, 2), (key3025, 2)]

theorem rawRowCheck8377 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form7 = rawRow8377 := by decide +kernel

def row8377 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8377 : row8377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8377 := by decide +kernel

theorem rowEval8377 (x : Key → ℝ) : Integer.Sparse.eval row8377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8377, Integer.Sparse.eval_collectBalanced, rawRowCheck8377]

def rawRow8378 : Integer.Sparse Key := [(key2784, -2), (key2778, -2), (key2792, -2), (key2807, -2), (key2801, -2), (key2918, -2), (key2851, -2), (key2919, -2), (key2858, -2), (key2827, -2), (key2922, -2), (key2868, -2), (key2630, 2), (key2624, 2), (key2638, 2), (key2704, 2), (key2698, 2), (key3021, 2), (key2851, 2), (key3022, 2), (key2858, 2), (key2724, 2), (key3025, 2), (key2868, 2)]

theorem rawRowCheck8378 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form7 = rawRow8378 := by decide +kernel

def row8378 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8378 : row8378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8378 := by decide +kernel

theorem rowEval8378 (x : Key → ℝ) : Integer.Sparse.eval row8378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8378, Integer.Sparse.eval_collectBalanced, rawRowCheck8378]

def rawRow8379 : Integer.Sparse Key := [(key2778, -2), (key2792, -2), (key2784, -2), (key2851, -2), (key2858, -2), (key2801, -2), (key2919, -2), (key2807, -2), (key2918, -2), (key2868, -2), (key2827, -2), (key2922, -2), (key2624, 2), (key2638, 2), (key2630, 2), (key2851, 2), (key2858, 2), (key2698, 2), (key3022, 2), (key2704, 2), (key3021, 2), (key2868, 2), (key2724, 2), (key3025, 2)]

theorem rawRowCheck8379 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form7 = rawRow8379 := by decide +kernel

def row8379 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8379 : row8379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8379 := by decide +kernel

theorem rowEval8379 (x : Key → ℝ) : Integer.Sparse.eval row8379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8379, Integer.Sparse.eval_collectBalanced, rawRowCheck8379]

def rawRow8380 : Integer.Sparse Key := [(key2792, -2), (key2778, -2), (key2784, -2), (key2858, -2), (key2851, -2), (key2919, -2), (key2801, -2), (key2918, -2), (key2807, -2), (key2868, -2), (key2922, -2), (key2827, -2), (key2638, 2), (key2624, 2), (key2630, 2), (key2858, 2), (key2851, 2), (key3022, 2), (key2698, 2), (key3021, 2), (key2704, 2), (key2868, 2), (key3025, 2), (key2724, 2)]

theorem rawRowCheck8380 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form7 = rawRow8380 := by decide +kernel

def row8380 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8380 : row8380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8380 := by decide +kernel

theorem rowEval8380 (x : Key → ℝ) : Integer.Sparse.eval row8380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8380, Integer.Sparse.eval_collectBalanced, rawRowCheck8380]

def rawRow8381 : Integer.Sparse Key := [(key2784, -2), (key2792, -2), (key2778, -2), (key2918, -2), (key2919, -2), (key2807, -2), (key2858, -2), (key2801, -2), (key2851, -2), (key2922, -2), (key2827, -2), (key2868, -2), (key2630, 2), (key2638, 2), (key2624, 2), (key3021, 2), (key3022, 2), (key2704, 2), (key2858, 2), (key2698, 2), (key2851, 2), (key3025, 2), (key2724, 2), (key2868, 2)]

theorem rawRowCheck8381 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form7 = rawRow8381 := by decide +kernel

def row8381 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8381 : row8381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8381 := by decide +kernel

theorem rowEval8381 (x : Key → ℝ) : Integer.Sparse.eval row8381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8381, Integer.Sparse.eval_collectBalanced, rawRowCheck8381]

def rawRow8382 : Integer.Sparse Key := [(key2792, -2), (key2784, -2), (key2778, -2), (key2919, -2), (key2918, -2), (key2858, -2), (key2807, -2), (key2851, -2), (key2801, -2), (key2922, -2), (key2868, -2), (key2827, -2), (key2638, 2), (key2630, 2), (key2624, 2), (key3022, 2), (key3021, 2), (key2858, 2), (key2704, 2), (key2851, 2), (key2698, 2), (key3025, 2), (key2868, 2), (key2724, 2)]

theorem rawRowCheck8382 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form7 = rawRow8382 := by decide +kernel

def row8382 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8382 : row8382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8382 := by decide +kernel

theorem rowEval8382 (x : Key → ℝ) : Integer.Sparse.eval row8382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8382, Integer.Sparse.eval_collectBalanced, rawRowCheck8382]

def rawRow8383 : Integer.Sparse Key := [(key2801, -2), (key2807, -2), (key2827, -2), (key2778, -2), (key2784, -2), (key2851, -2), (key2918, -2), (key2868, -2), (key2922, -2), (key2792, -2), (key2858, -2), (key2919, -2), (key2698, 2), (key2704, 2), (key2724, 2), (key2624, 2), (key2630, 2), (key2851, 2), (key3021, 2), (key2868, 2), (key3025, 2), (key2638, 2), (key2858, 2), (key3022, 2)]

theorem rawRowCheck8383 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form7 = rawRow8383 := by decide +kernel

def row8383 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8383 : row8383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8383 := by decide +kernel

theorem rowEval8383 (x : Key → ℝ) : Integer.Sparse.eval row8383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8383, Integer.Sparse.eval_collectBalanced, rawRowCheck8383]

def rawRow8384 : Integer.Sparse Key := [(key2807, -2), (key2801, -2), (key2827, -2), (key2784, -2), (key2778, -2), (key2918, -2), (key2851, -2), (key2922, -2), (key2868, -2), (key2792, -2), (key2919, -2), (key2858, -2), (key2704, 2), (key2698, 2), (key2724, 2), (key2630, 2), (key2624, 2), (key3021, 2), (key2851, 2), (key3025, 2), (key2868, 2), (key2638, 2), (key3022, 2), (key2858, 2)]

theorem rawRowCheck8384 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form7 = rawRow8384 := by decide +kernel

def row8384 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8384 : row8384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8384 := by decide +kernel

theorem rowEval8384 (x : Key → ℝ) : Integer.Sparse.eval row8384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8384, Integer.Sparse.eval_collectBalanced, rawRowCheck8384]

def rawRow8385 : Integer.Sparse Key := [(key2801, -2), (key2827, -2), (key2807, -2), (key2851, -2), (key2868, -2), (key2778, -2), (key2922, -2), (key2784, -2), (key2918, -2), (key2858, -2), (key2792, -2), (key2919, -2), (key2698, 2), (key2724, 2), (key2704, 2), (key2851, 2), (key2868, 2), (key2624, 2), (key3025, 2), (key2630, 2), (key3021, 2), (key2858, 2), (key2638, 2), (key3022, 2)]

theorem rawRowCheck8385 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form7 = rawRow8385 := by decide +kernel

def row8385 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8385 : row8385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8385 := by decide +kernel

theorem rowEval8385 (x : Key → ℝ) : Integer.Sparse.eval row8385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8385, Integer.Sparse.eval_collectBalanced, rawRowCheck8385]

def rawRow8386 : Integer.Sparse Key := [(key2827, -2), (key2801, -2), (key2807, -2), (key2868, -2), (key2851, -2), (key2922, -2), (key2778, -2), (key2918, -2), (key2784, -2), (key2858, -2), (key2919, -2), (key2792, -2), (key2724, 2), (key2698, 2), (key2704, 2), (key2868, 2), (key2851, 2), (key3025, 2), (key2624, 2), (key3021, 2), (key2630, 2), (key2858, 2), (key3022, 2), (key2638, 2)]

theorem rawRowCheck8386 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form7 = rawRow8386 := by decide +kernel

def row8386 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8386 : row8386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8386 := by decide +kernel

theorem rowEval8386 (x : Key → ℝ) : Integer.Sparse.eval row8386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8386, Integer.Sparse.eval_collectBalanced, rawRowCheck8386]

def rawRow8387 : Integer.Sparse Key := [(key2807, -2), (key2827, -2), (key2801, -2), (key2918, -2), (key2922, -2), (key2784, -2), (key2868, -2), (key2778, -2), (key2851, -2), (key2919, -2), (key2792, -2), (key2858, -2), (key2704, 2), (key2724, 2), (key2698, 2), (key3021, 2), (key3025, 2), (key2630, 2), (key2868, 2), (key2624, 2), (key2851, 2), (key3022, 2), (key2638, 2), (key2858, 2)]

theorem rawRowCheck8387 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form7 = rawRow8387 := by decide +kernel

def row8387 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8387 : row8387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8387 := by decide +kernel

theorem rowEval8387 (x : Key → ℝ) : Integer.Sparse.eval row8387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8387, Integer.Sparse.eval_collectBalanced, rawRowCheck8387]

def rawRow8388 : Integer.Sparse Key := [(key2827, -2), (key2807, -2), (key2801, -2), (key2922, -2), (key2918, -2), (key2868, -2), (key2784, -2), (key2851, -2), (key2778, -2), (key2919, -2), (key2858, -2), (key2792, -2), (key2724, 2), (key2704, 2), (key2698, 2), (key3025, 2), (key3021, 2), (key2868, 2), (key2630, 2), (key2851, 2), (key2624, 2), (key3022, 2), (key2858, 2), (key2638, 2)]

theorem rawRowCheck8388 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form7 = rawRow8388 := by decide +kernel

def row8388 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8388 : row8388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8388 := by decide +kernel

theorem rowEval8388 (x : Key → ℝ) : Integer.Sparse.eval row8388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8388, Integer.Sparse.eval_collectBalanced, rawRowCheck8388]

def rawRow8389 : Integer.Sparse Key := [(key2851, -2), (key2858, -2), (key2868, -2), (key2778, -2), (key2792, -2), (key2801, -2), (key2919, -2), (key2827, -2), (key2922, -2), (key2784, -2), (key2807, -2), (key2918, -2), (key2851, 2), (key2858, 2), (key2868, 2), (key2624, 2), (key2638, 2), (key2698, 2), (key3022, 2), (key2724, 2), (key3025, 2), (key2630, 2), (key2704, 2), (key3021, 2)]

theorem rawRowCheck8389 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form7 = rawRow8389 := by decide +kernel

def row8389 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8389 : row8389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8389 := by decide +kernel

theorem rowEval8389 (x : Key → ℝ) : Integer.Sparse.eval row8389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8389, Integer.Sparse.eval_collectBalanced, rawRowCheck8389]

def rawRow8390 : Integer.Sparse Key := [(key2858, -2), (key2851, -2), (key2868, -2), (key2792, -2), (key2778, -2), (key2919, -2), (key2801, -2), (key2922, -2), (key2827, -2), (key2784, -2), (key2918, -2), (key2807, -2), (key2858, 2), (key2851, 2), (key2868, 2), (key2638, 2), (key2624, 2), (key3022, 2), (key2698, 2), (key3025, 2), (key2724, 2), (key2630, 2), (key3021, 2), (key2704, 2)]

theorem rawRowCheck8390 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form7 = rawRow8390 := by decide +kernel

def row8390 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8390 : row8390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8390 := by decide +kernel

theorem rowEval8390 (x : Key → ℝ) : Integer.Sparse.eval row8390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8390, Integer.Sparse.eval_collectBalanced, rawRowCheck8390]

def rawRow8391 : Integer.Sparse Key := [(key2851, -2), (key2868, -2), (key2858, -2), (key2801, -2), (key2827, -2), (key2778, -2), (key2922, -2), (key2792, -2), (key2919, -2), (key2807, -2), (key2784, -2), (key2918, -2), (key2851, 2), (key2868, 2), (key2858, 2), (key2698, 2), (key2724, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2704, 2), (key2630, 2), (key3021, 2)]

theorem rawRowCheck8391 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form7 = rawRow8391 := by decide +kernel

def row8391 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8391 : row8391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8391 := by decide +kernel

theorem rowEval8391 (x : Key → ℝ) : Integer.Sparse.eval row8391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8391, Integer.Sparse.eval_collectBalanced, rawRowCheck8391]

def rawRow8392 : Integer.Sparse Key := [(key2868, -2), (key2851, -2), (key2858, -2), (key2827, -2), (key2801, -2), (key2922, -2), (key2778, -2), (key2919, -2), (key2792, -2), (key2807, -2), (key2918, -2), (key2784, -2), (key2868, 2), (key2851, 2), (key2858, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key3022, 2), (key2638, 2), (key2704, 2), (key3021, 2), (key2630, 2)]

theorem rawRowCheck8392 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form7 = rawRow8392 := by decide +kernel

def row8392 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8392 : row8392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8392 := by decide +kernel

theorem rowEval8392 (x : Key → ℝ) : Integer.Sparse.eval row8392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8392, Integer.Sparse.eval_collectBalanced, rawRowCheck8392]

def rawRow8393 : Integer.Sparse Key := [(key2858, -2), (key2868, -2), (key2851, -2), (key2919, -2), (key2922, -2), (key2792, -2), (key2827, -2), (key2778, -2), (key2801, -2), (key2918, -2), (key2784, -2), (key2807, -2), (key2858, 2), (key2868, 2), (key2851, 2), (key3022, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2624, 2), (key2698, 2), (key3021, 2), (key2630, 2), (key2704, 2)]

theorem rawRowCheck8393 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form7 = rawRow8393 := by decide +kernel

def row8393 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8393 : row8393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8393 := by decide +kernel

theorem rowEval8393 (x : Key → ℝ) : Integer.Sparse.eval row8393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8393, Integer.Sparse.eval_collectBalanced, rawRowCheck8393]

def rawRow8394 : Integer.Sparse Key := [(key2868, -2), (key2858, -2), (key2851, -2), (key2922, -2), (key2919, -2), (key2827, -2), (key2792, -2), (key2801, -2), (key2778, -2), (key2918, -2), (key2807, -2), (key2784, -2), (key2868, 2), (key2858, 2), (key2851, 2), (key3025, 2), (key3022, 2), (key2724, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key3021, 2), (key2704, 2), (key2630, 2)]

theorem rawRowCheck8394 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form7 = rawRow8394 := by decide +kernel

def row8394 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8394 : row8394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8394 := by decide +kernel

theorem rowEval8394 (x : Key → ℝ) : Integer.Sparse.eval row8394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8394, Integer.Sparse.eval_collectBalanced, rawRowCheck8394]

def rawRow8395 : Integer.Sparse Key := [(key2918, -2), (key2919, -2), (key2922, -2), (key2784, -2), (key2792, -2), (key2807, -2), (key2858, -2), (key2827, -2), (key2868, -2), (key2778, -2), (key2801, -2), (key2851, -2), (key3021, 2), (key3022, 2), (key3025, 2), (key2630, 2), (key2638, 2), (key2704, 2), (key2858, 2), (key2724, 2), (key2868, 2), (key2624, 2), (key2698, 2), (key2851, 2)]

theorem rawRowCheck8395 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form7 = rawRow8395 := by decide +kernel

def row8395 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8395 : row8395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8395 := by decide +kernel

theorem rowEval8395 (x : Key → ℝ) : Integer.Sparse.eval row8395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8395, Integer.Sparse.eval_collectBalanced, rawRowCheck8395]

def rawRow8396 : Integer.Sparse Key := [(key2919, -2), (key2918, -2), (key2922, -2), (key2792, -2), (key2784, -2), (key2858, -2), (key2807, -2), (key2868, -2), (key2827, -2), (key2778, -2), (key2851, -2), (key2801, -2), (key3022, 2), (key3021, 2), (key3025, 2), (key2638, 2), (key2630, 2), (key2858, 2), (key2704, 2), (key2868, 2), (key2724, 2), (key2624, 2), (key2851, 2), (key2698, 2)]

theorem rawRowCheck8396 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form7 = rawRow8396 := by decide +kernel

def row8396 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8396 : row8396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8396 := by decide +kernel

theorem rowEval8396 (x : Key → ℝ) : Integer.Sparse.eval row8396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8396, Integer.Sparse.eval_collectBalanced, rawRowCheck8396]

def rawRow8397 : Integer.Sparse Key := [(key2918, -2), (key2922, -2), (key2919, -2), (key2807, -2), (key2827, -2), (key2784, -2), (key2868, -2), (key2792, -2), (key2858, -2), (key2801, -2), (key2778, -2), (key2851, -2), (key3021, 2), (key3025, 2), (key3022, 2), (key2704, 2), (key2724, 2), (key2630, 2), (key2868, 2), (key2638, 2), (key2858, 2), (key2698, 2), (key2624, 2), (key2851, 2)]

theorem rawRowCheck8397 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form7 = rawRow8397 := by decide +kernel

def row8397 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8397 : row8397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8397 := by decide +kernel

theorem rowEval8397 (x : Key → ℝ) : Integer.Sparse.eval row8397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8397, Integer.Sparse.eval_collectBalanced, rawRowCheck8397]

def rawRow8398 : Integer.Sparse Key := [(key2922, -2), (key2918, -2), (key2919, -2), (key2827, -2), (key2807, -2), (key2868, -2), (key2784, -2), (key2858, -2), (key2792, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key3025, 2), (key3021, 2), (key3022, 2), (key2724, 2), (key2704, 2), (key2868, 2), (key2630, 2), (key2858, 2), (key2638, 2), (key2698, 2), (key2851, 2), (key2624, 2)]

theorem rawRowCheck8398 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form7 = rawRow8398 := by decide +kernel

def row8398 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8398 : row8398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8398 := by decide +kernel

theorem rowEval8398 (x : Key → ℝ) : Integer.Sparse.eval row8398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8398, Integer.Sparse.eval_collectBalanced, rawRowCheck8398]

def rawRow8399 : Integer.Sparse Key := [(key2919, -2), (key2922, -2), (key2918, -2), (key2858, -2), (key2868, -2), (key2792, -2), (key2827, -2), (key2784, -2), (key2807, -2), (key2851, -2), (key2778, -2), (key2801, -2), (key3022, 2), (key3025, 2), (key3021, 2), (key2858, 2), (key2868, 2), (key2638, 2), (key2724, 2), (key2630, 2), (key2704, 2), (key2851, 2), (key2624, 2), (key2698, 2)]

theorem rawRowCheck8399 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form7 = rawRow8399 := by decide +kernel

def row8399 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8399 : row8399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8399 := by decide +kernel

theorem rowEval8399 (x : Key → ℝ) : Integer.Sparse.eval row8399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8399, Integer.Sparse.eval_collectBalanced, rawRowCheck8399]

def rawRow8400 : Integer.Sparse Key := [(key2922, -2), (key2919, -2), (key2918, -2), (key2868, -2), (key2858, -2), (key2827, -2), (key2792, -2), (key2807, -2), (key2784, -2), (key2851, -2), (key2801, -2), (key2778, -2), (key3025, 2), (key3022, 2), (key3021, 2), (key2868, 2), (key2858, 2), (key2724, 2), (key2638, 2), (key2704, 2), (key2630, 2), (key2851, 2), (key2698, 2), (key2624, 2)]

theorem rawRowCheck8400 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form7 = rawRow8400 := by decide +kernel

def row8400 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck8400 : row8400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8400 := by decide +kernel

theorem rowEval8400 (x : Key → ℝ) : Integer.Sparse.eval row8400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8400, Integer.Sparse.eval_collectBalanced, rawRowCheck8400]

def rawRow8401 : Integer.Sparse Key := [(key3007, -2), (key3007, -2), (key3009, -2), (key3011, -2), (key3011, -2), (key3021, -2), (key3021, -2), (key3022, -2), (key3022, -2), (key3016, -2), (key3025, -2), (key3025, -2), (key2657, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2752, 2), (key2918, 2), (key2918, 2), (key2919, 2), (key2919, 2), (key2757, 2), (key2922, 2), (key2922, 2)]

theorem rawRowCheck8401 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form7 = rawRow8401 := by decide +kernel

def row8401 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

theorem rowCheck8401 : row8401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8401 := by decide +kernel

theorem rowEval8401 (x : Key → ℝ) : Integer.Sparse.eval row8401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8401, Integer.Sparse.eval_collectBalanced, rawRowCheck8401]

def rawRow8402 : Integer.Sparse Key := [(key3007, -2), (key3009, -2), (key3007, -2), (key3021, -2), (key3022, -2), (key3011, -2), (key3022, -2), (key3011, -2), (key3021, -2), (key3025, -2), (key3016, -2), (key3025, -2), (key2657, 2), (key2659, 2), (key2657, 2), (key2918, 2), (key2919, 2), (key2752, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2922, 2), (key2757, 2), (key2922, 2)]

theorem rawRowCheck8402 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form7 = rawRow8402 := by decide +kernel

def row8402 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

theorem rowCheck8402 : row8402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8402 := by decide +kernel

theorem rowEval8402 (x : Key → ℝ) : Integer.Sparse.eval row8402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8402, Integer.Sparse.eval_collectBalanced, rawRowCheck8402]

def rawRow8403 : Integer.Sparse Key := [(key3009, -2), (key3007, -2), (key3007, -2), (key3022, -2), (key3021, -2), (key3022, -2), (key3011, -2), (key3021, -2), (key3011, -2), (key3025, -2), (key3025, -2), (key3016, -2), (key2659, 2), (key2657, 2), (key2657, 2), (key2919, 2), (key2918, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2752, 2), (key2922, 2), (key2922, 2), (key2757, 2)]

theorem rawRowCheck8403 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form7 = rawRow8403 := by decide +kernel

def row8403 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

theorem rowCheck8403 : row8403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8403 := by decide +kernel

theorem rowEval8403 (x : Key → ℝ) : Integer.Sparse.eval row8403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8403, Integer.Sparse.eval_collectBalanced, rawRowCheck8403]

def rawRow8404 : Integer.Sparse Key := [(key3011, -2), (key3011, -2), (key3016, -2), (key3007, -2), (key3007, -2), (key3021, -2), (key3021, -2), (key3025, -2), (key3025, -2), (key3009, -2), (key3022, -2), (key3022, -2), (key2752, 2), (key2752, 2), (key2757, 2), (key2657, 2), (key2657, 2), (key2918, 2), (key2918, 2), (key2922, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2919, 2)]

theorem rawRowCheck8404 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form7 = rawRow8404 := by decide +kernel

def row8404 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

theorem rowCheck8404 : row8404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8404 := by decide +kernel

theorem rowEval8404 (x : Key → ℝ) : Integer.Sparse.eval row8404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8404, Integer.Sparse.eval_collectBalanced, rawRowCheck8404]

def rawRow8405 : Integer.Sparse Key := [(key3011, -2), (key3016, -2), (key3011, -2), (key3021, -2), (key3025, -2), (key3007, -2), (key3025, -2), (key3007, -2), (key3021, -2), (key3022, -2), (key3009, -2), (key3022, -2), (key2752, 2), (key2757, 2), (key2752, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2922, 2), (key2657, 2), (key2918, 2), (key2919, 2), (key2659, 2), (key2919, 2)]

theorem rawRowCheck8405 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form7 = rawRow8405 := by decide +kernel

def row8405 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

theorem rowCheck8405 : row8405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8405 := by decide +kernel

theorem rowEval8405 (x : Key → ℝ) : Integer.Sparse.eval row8405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8405, Integer.Sparse.eval_collectBalanced, rawRowCheck8405]

def rawRow8406 : Integer.Sparse Key := [(key3016, -2), (key3011, -2), (key3011, -2), (key3025, -2), (key3021, -2), (key3025, -2), (key3007, -2), (key3021, -2), (key3007, -2), (key3022, -2), (key3022, -2), (key3009, -2), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2918, 2), (key2657, 2), (key2919, 2), (key2919, 2), (key2659, 2)]

theorem rawRowCheck8406 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form7 = rawRow8406 := by decide +kernel

def row8406 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

theorem rowCheck8406 : row8406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8406 := by decide +kernel

theorem rowEval8406 (x : Key → ℝ) : Integer.Sparse.eval row8406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8406, Integer.Sparse.eval_collectBalanced, rawRowCheck8406]

def rawRow8407 : Integer.Sparse Key := [(key3021, -2), (key3022, -2), (key3025, -2), (key3007, -2), (key3009, -2), (key3011, -2), (key3022, -2), (key3016, -2), (key3025, -2), (key3007, -2), (key3011, -2), (key3021, -2), (key2918, 2), (key2919, 2), (key2922, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2919, 2), (key2757, 2), (key2922, 2), (key2657, 2), (key2752, 2), (key2918, 2)]

theorem rawRowCheck8407 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form7 = rawRow8407 := by decide +kernel

def row8407 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

theorem rowCheck8407 : row8407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8407 := by decide +kernel

theorem rowEval8407 (x : Key → ℝ) : Integer.Sparse.eval row8407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8407, Integer.Sparse.eval_collectBalanced, rawRowCheck8407]

def rawRow8408 : Integer.Sparse Key := [(key3022, -2), (key3021, -2), (key3025, -2), (key3009, -2), (key3007, -2), (key3022, -2), (key3011, -2), (key3025, -2), (key3016, -2), (key3007, -2), (key3021, -2), (key3011, -2), (key2919, 2), (key2918, 2), (key2922, 2), (key2659, 2), (key2657, 2), (key2919, 2), (key2752, 2), (key2922, 2), (key2757, 2), (key2657, 2), (key2918, 2), (key2752, 2)]

theorem rawRowCheck8408 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form7 = rawRow8408 := by decide +kernel

def row8408 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

theorem rowCheck8408 : row8408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8408 := by decide +kernel

theorem rowEval8408 (x : Key → ℝ) : Integer.Sparse.eval row8408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8408, Integer.Sparse.eval_collectBalanced, rawRowCheck8408]

def rawRow8409 : Integer.Sparse Key := [(key3021, -2), (key3025, -2), (key3022, -2), (key3011, -2), (key3016, -2), (key3007, -2), (key3025, -2), (key3009, -2), (key3022, -2), (key3011, -2), (key3007, -2), (key3021, -2), (key2918, 2), (key2922, 2), (key2919, 2), (key2752, 2), (key2757, 2), (key2657, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2752, 2), (key2657, 2), (key2918, 2)]

theorem rawRowCheck8409 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form7 = rawRow8409 := by decide +kernel

def row8409 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

theorem rowCheck8409 : row8409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8409 := by decide +kernel

theorem rowEval8409 (x : Key → ℝ) : Integer.Sparse.eval row8409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8409, Integer.Sparse.eval_collectBalanced, rawRowCheck8409]

def rawRow8410 : Integer.Sparse Key := [(key3025, -2), (key3021, -2), (key3022, -2), (key3016, -2), (key3011, -2), (key3025, -2), (key3007, -2), (key3022, -2), (key3009, -2), (key3011, -2), (key3021, -2), (key3007, -2), (key2922, 2), (key2918, 2), (key2919, 2), (key2757, 2), (key2752, 2), (key2922, 2), (key2657, 2), (key2919, 2), (key2659, 2), (key2752, 2), (key2918, 2), (key2657, 2)]

theorem rawRowCheck8410 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form7 = rawRow8410 := by decide +kernel

def row8410 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

theorem rowCheck8410 : row8410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8410 := by decide +kernel

theorem rowEval8410 (x : Key → ℝ) : Integer.Sparse.eval row8410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8410, Integer.Sparse.eval_collectBalanced, rawRowCheck8410]

def rawRow8411 : Integer.Sparse Key := [(key3022, -2), (key3025, -2), (key3021, -2), (key3022, -2), (key3025, -2), (key3009, -2), (key3016, -2), (key3007, -2), (key3011, -2), (key3021, -2), (key3007, -2), (key3011, -2), (key2919, 2), (key2922, 2), (key2918, 2), (key2919, 2), (key2922, 2), (key2659, 2), (key2757, 2), (key2657, 2), (key2752, 2), (key2918, 2), (key2657, 2), (key2752, 2)]

theorem rawRowCheck8411 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form7 = rawRow8411 := by decide +kernel

def row8411 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

theorem rowCheck8411 : row8411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8411 := by decide +kernel

theorem rowEval8411 (x : Key → ℝ) : Integer.Sparse.eval row8411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8411, Integer.Sparse.eval_collectBalanced, rawRowCheck8411]

def rawRow8412 : Integer.Sparse Key := [(key3025, -2), (key3022, -2), (key3021, -2), (key3025, -2), (key3022, -2), (key3016, -2), (key3009, -2), (key3011, -2), (key3007, -2), (key3021, -2), (key3011, -2), (key3007, -2), (key2922, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2919, 2), (key2757, 2), (key2659, 2), (key2752, 2), (key2657, 2), (key2918, 2), (key2752, 2), (key2657, 2)]

theorem rawRowCheck8412 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form7 = rawRow8412 := by decide +kernel

def row8412 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

theorem rowCheck8412 : row8412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8412 := by decide +kernel

theorem rowEval8412 (x : Key → ℝ) : Integer.Sparse.eval row8412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8412, Integer.Sparse.eval_collectBalanced, rawRowCheck8412]

def rawRow8413 : Integer.Sparse Key := [(key1311, -2), (key1319, -2), (key1327, -2), (key1419, -2), (key1427, -2), (key1617, -2), (key1919, -2), (key1625, -2), (key1921, -2), (key1445, -2), (key1634, -2), (key1927, -2), (key1291, 1), (key1299, 1), (key1311, 1), (key1352, 1), (key1327, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1541, 1), (key1897, 1), (key1557, 1), (key1900, 1), (key1419, 1), (key1473, 1), (key1568, 1), (key1904, 1), (key1684, 1), (key1921, 1), (key1445, 1), (key1481, 1), (key1594, 1), (key1912, 1), (key1690, 1), (key1927, 1)]

theorem rawRowCheck8413 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form8 = rawRow8413 := by decide +kernel

def row8413 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8413 : row8413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8413 := by decide +kernel

theorem rowEval8413 (x : Key → ℝ) : Integer.Sparse.eval row8413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8413, Integer.Sparse.eval_collectBalanced, rawRowCheck8413]

def rawRow8414 : Integer.Sparse Key := [(key1319, -2), (key1311, -2), (key1327, -2), (key1427, -2), (key1419, -2), (key1919, -2), (key1617, -2), (key1921, -2), (key1625, -2), (key1445, -2), (key1927, -2), (key1634, -2), (key1299, 1), (key1291, 1), (key1352, 1), (key1311, 1), (key1355, 1), (key1327, 1), (key1394, 1), (key1386, 1), (key1897, 1), (key1541, 1), (key1900, 1), (key1557, 1), (key1473, 1), (key1419, 1), (key1904, 1), (key1568, 1), (key1921, 1), (key1684, 1), (key1481, 1), (key1445, 1), (key1912, 1), (key1594, 1), (key1927, 1), (key1690, 1)]

theorem rawRowCheck8414 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form8 = rawRow8414 := by decide +kernel

def row8414 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8414 : row8414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8414 := by decide +kernel

theorem rowEval8414 (x : Key → ℝ) : Integer.Sparse.eval row8414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8414, Integer.Sparse.eval_collectBalanced, rawRowCheck8414]

def rawRow8415 : Integer.Sparse Key := [(key1311, -2), (key1327, -2), (key1319, -2), (key1617, -2), (key1625, -2), (key1419, -2), (key1921, -2), (key1427, -2), (key1919, -2), (key1634, -2), (key1445, -2), (key1927, -2), (key1311, 1), (key1327, 1), (key1291, 1), (key1355, 1), (key1299, 1), (key1352, 1), (key1541, 1), (key1557, 1), (key1386, 1), (key1900, 1), (key1394, 1), (key1897, 1), (key1568, 1), (key1684, 1), (key1419, 1), (key1921, 1), (key1473, 1), (key1904, 1), (key1594, 1), (key1690, 1), (key1445, 1), (key1927, 1), (key1481, 1), (key1912, 1)]

theorem rawRowCheck8415 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form8 = rawRow8415 := by decide +kernel

def row8415 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8415 : row8415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8415 := by decide +kernel

theorem rowEval8415 (x : Key → ℝ) : Integer.Sparse.eval row8415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8415, Integer.Sparse.eval_collectBalanced, rawRowCheck8415]

def rawRow8416 : Integer.Sparse Key := [(key1327, -2), (key1311, -2), (key1319, -2), (key1625, -2), (key1617, -2), (key1921, -2), (key1419, -2), (key1919, -2), (key1427, -2), (key1634, -2), (key1927, -2), (key1445, -2), (key1327, 1), (key1311, 1), (key1355, 1), (key1291, 1), (key1352, 1), (key1299, 1), (key1557, 1), (key1541, 1), (key1900, 1), (key1386, 1), (key1897, 1), (key1394, 1), (key1684, 1), (key1568, 1), (key1921, 1), (key1419, 1), (key1904, 1), (key1473, 1), (key1690, 1), (key1594, 1), (key1927, 1), (key1445, 1), (key1912, 1), (key1481, 1)]

theorem rawRowCheck8416 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form8 = rawRow8416 := by decide +kernel

def row8416 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8416 : row8416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8416 := by decide +kernel

theorem rowEval8416 (x : Key → ℝ) : Integer.Sparse.eval row8416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8416, Integer.Sparse.eval_collectBalanced, rawRowCheck8416]

def rawRow8417 : Integer.Sparse Key := [(key1319, -2), (key1327, -2), (key1311, -2), (key1919, -2), (key1921, -2), (key1427, -2), (key1625, -2), (key1419, -2), (key1617, -2), (key1927, -2), (key1445, -2), (key1634, -2), (key1352, 1), (key1355, 1), (key1299, 1), (key1327, 1), (key1291, 1), (key1311, 1), (key1897, 1), (key1900, 1), (key1394, 1), (key1557, 1), (key1386, 1), (key1541, 1), (key1904, 1), (key1921, 1), (key1473, 1), (key1684, 1), (key1419, 1), (key1568, 1), (key1912, 1), (key1927, 1), (key1481, 1), (key1690, 1), (key1445, 1), (key1594, 1)]

theorem rawRowCheck8417 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form8 = rawRow8417 := by decide +kernel

def row8417 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8417 : row8417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8417 := by decide +kernel

theorem rowEval8417 (x : Key → ℝ) : Integer.Sparse.eval row8417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8417, Integer.Sparse.eval_collectBalanced, rawRowCheck8417]

def rawRow8418 : Integer.Sparse Key := [(key1327, -2), (key1319, -2), (key1311, -2), (key1921, -2), (key1919, -2), (key1625, -2), (key1427, -2), (key1617, -2), (key1419, -2), (key1927, -2), (key1634, -2), (key1445, -2), (key1355, 1), (key1352, 1), (key1327, 1), (key1299, 1), (key1311, 1), (key1291, 1), (key1900, 1), (key1897, 1), (key1557, 1), (key1394, 1), (key1541, 1), (key1386, 1), (key1921, 1), (key1904, 1), (key1684, 1), (key1473, 1), (key1568, 1), (key1419, 1), (key1927, 1), (key1912, 1), (key1690, 1), (key1481, 1), (key1594, 1), (key1445, 1)]

theorem rawRowCheck8418 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form8 = rawRow8418 := by decide +kernel

def row8418 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8418 : row8418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8418 := by decide +kernel

theorem rowEval8418 (x : Key → ℝ) : Integer.Sparse.eval row8418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8418, Integer.Sparse.eval_collectBalanced, rawRowCheck8418]

def rawRow8419 : Integer.Sparse Key := [(key1419, -2), (key1427, -2), (key1445, -2), (key1311, -2), (key1319, -2), (key1617, -2), (key1919, -2), (key1634, -2), (key1927, -2), (key1327, -2), (key1625, -2), (key1921, -2), (key1386, 1), (key1394, 1), (key1419, 1), (key1473, 1), (key1445, 1), (key1481, 1), (key1291, 1), (key1299, 1), (key1568, 1), (key1904, 1), (key1594, 1), (key1912, 1), (key1311, 1), (key1352, 1), (key1541, 1), (key1897, 1), (key1690, 1), (key1927, 1), (key1327, 1), (key1355, 1), (key1557, 1), (key1900, 1), (key1684, 1), (key1921, 1)]

theorem rawRowCheck8419 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form8 = rawRow8419 := by decide +kernel

def row8419 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8419 : row8419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8419 := by decide +kernel

theorem rowEval8419 (x : Key → ℝ) : Integer.Sparse.eval row8419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8419, Integer.Sparse.eval_collectBalanced, rawRowCheck8419]

def rawRow8420 : Integer.Sparse Key := [(key1427, -2), (key1419, -2), (key1445, -2), (key1319, -2), (key1311, -2), (key1919, -2), (key1617, -2), (key1927, -2), (key1634, -2), (key1327, -2), (key1921, -2), (key1625, -2), (key1394, 1), (key1386, 1), (key1473, 1), (key1419, 1), (key1481, 1), (key1445, 1), (key1299, 1), (key1291, 1), (key1904, 1), (key1568, 1), (key1912, 1), (key1594, 1), (key1352, 1), (key1311, 1), (key1897, 1), (key1541, 1), (key1927, 1), (key1690, 1), (key1355, 1), (key1327, 1), (key1900, 1), (key1557, 1), (key1921, 1), (key1684, 1)]

theorem rawRowCheck8420 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form8 = rawRow8420 := by decide +kernel

def row8420 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8420 : row8420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8420 := by decide +kernel

theorem rowEval8420 (x : Key → ℝ) : Integer.Sparse.eval row8420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8420, Integer.Sparse.eval_collectBalanced, rawRowCheck8420]

def rawRow8421 : Integer.Sparse Key := [(key1419, -2), (key1445, -2), (key1427, -2), (key1617, -2), (key1634, -2), (key1311, -2), (key1927, -2), (key1319, -2), (key1919, -2), (key1625, -2), (key1327, -2), (key1921, -2), (key1419, 1), (key1445, 1), (key1386, 1), (key1481, 1), (key1394, 1), (key1473, 1), (key1568, 1), (key1594, 1), (key1291, 1), (key1912, 1), (key1299, 1), (key1904, 1), (key1541, 1), (key1690, 1), (key1311, 1), (key1927, 1), (key1352, 1), (key1897, 1), (key1557, 1), (key1684, 1), (key1327, 1), (key1921, 1), (key1355, 1), (key1900, 1)]

theorem rawRowCheck8421 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form8 = rawRow8421 := by decide +kernel

def row8421 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8421 : row8421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8421 := by decide +kernel

theorem rowEval8421 (x : Key → ℝ) : Integer.Sparse.eval row8421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8421, Integer.Sparse.eval_collectBalanced, rawRowCheck8421]

def rawRow8422 : Integer.Sparse Key := [(key1445, -2), (key1419, -2), (key1427, -2), (key1634, -2), (key1617, -2), (key1927, -2), (key1311, -2), (key1919, -2), (key1319, -2), (key1625, -2), (key1921, -2), (key1327, -2), (key1445, 1), (key1419, 1), (key1481, 1), (key1386, 1), (key1473, 1), (key1394, 1), (key1594, 1), (key1568, 1), (key1912, 1), (key1291, 1), (key1904, 1), (key1299, 1), (key1690, 1), (key1541, 1), (key1927, 1), (key1311, 1), (key1897, 1), (key1352, 1), (key1684, 1), (key1557, 1), (key1921, 1), (key1327, 1), (key1900, 1), (key1355, 1)]

theorem rawRowCheck8422 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form8 = rawRow8422 := by decide +kernel

def row8422 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8422 : row8422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8422 := by decide +kernel

theorem rowEval8422 (x : Key → ℝ) : Integer.Sparse.eval row8422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8422, Integer.Sparse.eval_collectBalanced, rawRowCheck8422]

def rawRow8423 : Integer.Sparse Key := [(key1427, -2), (key1445, -2), (key1419, -2), (key1919, -2), (key1927, -2), (key1319, -2), (key1634, -2), (key1311, -2), (key1617, -2), (key1921, -2), (key1327, -2), (key1625, -2), (key1473, 1), (key1481, 1), (key1394, 1), (key1445, 1), (key1386, 1), (key1419, 1), (key1904, 1), (key1912, 1), (key1299, 1), (key1594, 1), (key1291, 1), (key1568, 1), (key1897, 1), (key1927, 1), (key1352, 1), (key1690, 1), (key1311, 1), (key1541, 1), (key1900, 1), (key1921, 1), (key1355, 1), (key1684, 1), (key1327, 1), (key1557, 1)]

theorem rawRowCheck8423 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form8 = rawRow8423 := by decide +kernel

def row8423 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8423 : row8423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8423 := by decide +kernel

theorem rowEval8423 (x : Key → ℝ) : Integer.Sparse.eval row8423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8423, Integer.Sparse.eval_collectBalanced, rawRowCheck8423]

def rawRow8424 : Integer.Sparse Key := [(key1445, -2), (key1427, -2), (key1419, -2), (key1927, -2), (key1919, -2), (key1634, -2), (key1319, -2), (key1617, -2), (key1311, -2), (key1921, -2), (key1625, -2), (key1327, -2), (key1481, 1), (key1473, 1), (key1445, 1), (key1394, 1), (key1419, 1), (key1386, 1), (key1912, 1), (key1904, 1), (key1594, 1), (key1299, 1), (key1568, 1), (key1291, 1), (key1927, 1), (key1897, 1), (key1690, 1), (key1352, 1), (key1541, 1), (key1311, 1), (key1921, 1), (key1900, 1), (key1684, 1), (key1355, 1), (key1557, 1), (key1327, 1)]

theorem rawRowCheck8424 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form8 = rawRow8424 := by decide +kernel

def row8424 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8424 : row8424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8424 := by decide +kernel

theorem rowEval8424 (x : Key → ℝ) : Integer.Sparse.eval row8424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8424, Integer.Sparse.eval_collectBalanced, rawRowCheck8424]

def rawRow8425 : Integer.Sparse Key := [(key1617, -2), (key1625, -2), (key1634, -2), (key1311, -2), (key1327, -2), (key1419, -2), (key1921, -2), (key1445, -2), (key1927, -2), (key1319, -2), (key1427, -2), (key1919, -2), (key1541, 1), (key1557, 1), (key1568, 1), (key1684, 1), (key1594, 1), (key1690, 1), (key1311, 1), (key1327, 1), (key1419, 1), (key1921, 1), (key1445, 1), (key1927, 1), (key1291, 1), (key1355, 1), (key1386, 1), (key1900, 1), (key1481, 1), (key1912, 1), (key1299, 1), (key1352, 1), (key1394, 1), (key1897, 1), (key1473, 1), (key1904, 1)]

theorem rawRowCheck8425 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form8 = rawRow8425 := by decide +kernel

def row8425 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8425 : row8425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8425 := by decide +kernel

theorem rowEval8425 (x : Key → ℝ) : Integer.Sparse.eval row8425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8425, Integer.Sparse.eval_collectBalanced, rawRowCheck8425]

def rawRow8426 : Integer.Sparse Key := [(key1625, -2), (key1617, -2), (key1634, -2), (key1327, -2), (key1311, -2), (key1921, -2), (key1419, -2), (key1927, -2), (key1445, -2), (key1319, -2), (key1919, -2), (key1427, -2), (key1557, 1), (key1541, 1), (key1684, 1), (key1568, 1), (key1690, 1), (key1594, 1), (key1327, 1), (key1311, 1), (key1921, 1), (key1419, 1), (key1927, 1), (key1445, 1), (key1355, 1), (key1291, 1), (key1900, 1), (key1386, 1), (key1912, 1), (key1481, 1), (key1352, 1), (key1299, 1), (key1897, 1), (key1394, 1), (key1904, 1), (key1473, 1)]

theorem rawRowCheck8426 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form8 = rawRow8426 := by decide +kernel

def row8426 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8426 : row8426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8426 := by decide +kernel

theorem rowEval8426 (x : Key → ℝ) : Integer.Sparse.eval row8426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8426, Integer.Sparse.eval_collectBalanced, rawRowCheck8426]

def rawRow8427 : Integer.Sparse Key := [(key1617, -2), (key1634, -2), (key1625, -2), (key1419, -2), (key1445, -2), (key1311, -2), (key1927, -2), (key1327, -2), (key1921, -2), (key1427, -2), (key1319, -2), (key1919, -2), (key1568, 1), (key1594, 1), (key1541, 1), (key1690, 1), (key1557, 1), (key1684, 1), (key1419, 1), (key1445, 1), (key1311, 1), (key1927, 1), (key1327, 1), (key1921, 1), (key1386, 1), (key1481, 1), (key1291, 1), (key1912, 1), (key1355, 1), (key1900, 1), (key1394, 1), (key1473, 1), (key1299, 1), (key1904, 1), (key1352, 1), (key1897, 1)]

theorem rawRowCheck8427 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form8 = rawRow8427 := by decide +kernel

def row8427 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8427 : row8427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8427 := by decide +kernel

theorem rowEval8427 (x : Key → ℝ) : Integer.Sparse.eval row8427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8427, Integer.Sparse.eval_collectBalanced, rawRowCheck8427]

def rawRow8428 : Integer.Sparse Key := [(key1634, -2), (key1617, -2), (key1625, -2), (key1445, -2), (key1419, -2), (key1927, -2), (key1311, -2), (key1921, -2), (key1327, -2), (key1427, -2), (key1919, -2), (key1319, -2), (key1594, 1), (key1568, 1), (key1690, 1), (key1541, 1), (key1684, 1), (key1557, 1), (key1445, 1), (key1419, 1), (key1927, 1), (key1311, 1), (key1921, 1), (key1327, 1), (key1481, 1), (key1386, 1), (key1912, 1), (key1291, 1), (key1900, 1), (key1355, 1), (key1473, 1), (key1394, 1), (key1904, 1), (key1299, 1), (key1897, 1), (key1352, 1)]

theorem rawRowCheck8428 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form8 = rawRow8428 := by decide +kernel

def row8428 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8428 : row8428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8428 := by decide +kernel

theorem rowEval8428 (x : Key → ℝ) : Integer.Sparse.eval row8428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8428, Integer.Sparse.eval_collectBalanced, rawRowCheck8428]

def rawRow8429 : Integer.Sparse Key := [(key1625, -2), (key1634, -2), (key1617, -2), (key1921, -2), (key1927, -2), (key1327, -2), (key1445, -2), (key1311, -2), (key1419, -2), (key1919, -2), (key1319, -2), (key1427, -2), (key1684, 1), (key1690, 1), (key1557, 1), (key1594, 1), (key1541, 1), (key1568, 1), (key1921, 1), (key1927, 1), (key1327, 1), (key1445, 1), (key1311, 1), (key1419, 1), (key1900, 1), (key1912, 1), (key1355, 1), (key1481, 1), (key1291, 1), (key1386, 1), (key1897, 1), (key1904, 1), (key1352, 1), (key1473, 1), (key1299, 1), (key1394, 1)]

theorem rawRowCheck8429 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form8 = rawRow8429 := by decide +kernel

def row8429 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8429 : row8429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8429 := by decide +kernel

theorem rowEval8429 (x : Key → ℝ) : Integer.Sparse.eval row8429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8429, Integer.Sparse.eval_collectBalanced, rawRowCheck8429]

def rawRow8430 : Integer.Sparse Key := [(key1634, -2), (key1625, -2), (key1617, -2), (key1927, -2), (key1921, -2), (key1445, -2), (key1327, -2), (key1419, -2), (key1311, -2), (key1919, -2), (key1427, -2), (key1319, -2), (key1690, 1), (key1684, 1), (key1594, 1), (key1557, 1), (key1568, 1), (key1541, 1), (key1927, 1), (key1921, 1), (key1445, 1), (key1327, 1), (key1419, 1), (key1311, 1), (key1912, 1), (key1900, 1), (key1481, 1), (key1355, 1), (key1386, 1), (key1291, 1), (key1904, 1), (key1897, 1), (key1473, 1), (key1352, 1), (key1394, 1), (key1299, 1)]

theorem rawRowCheck8430 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form8 = rawRow8430 := by decide +kernel

def row8430 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8430 : row8430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8430 := by decide +kernel

theorem rowEval8430 (x : Key → ℝ) : Integer.Sparse.eval row8430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8430, Integer.Sparse.eval_collectBalanced, rawRowCheck8430]

def rawRow8431 : Integer.Sparse Key := [(key1919, -2), (key1921, -2), (key1927, -2), (key1319, -2), (key1327, -2), (key1427, -2), (key1625, -2), (key1445, -2), (key1634, -2), (key1311, -2), (key1419, -2), (key1617, -2), (key1897, 1), (key1900, 1), (key1904, 1), (key1921, 1), (key1912, 1), (key1927, 1), (key1352, 1), (key1355, 1), (key1473, 1), (key1684, 1), (key1481, 1), (key1690, 1), (key1299, 1), (key1327, 1), (key1394, 1), (key1557, 1), (key1445, 1), (key1594, 1), (key1291, 1), (key1311, 1), (key1386, 1), (key1541, 1), (key1419, 1), (key1568, 1)]

theorem rawRowCheck8431 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form8 = rawRow8431 := by decide +kernel

def row8431 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8431 : row8431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8431 := by decide +kernel

theorem rowEval8431 (x : Key → ℝ) : Integer.Sparse.eval row8431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8431, Integer.Sparse.eval_collectBalanced, rawRowCheck8431]

def rawRow8432 : Integer.Sparse Key := [(key1921, -2), (key1919, -2), (key1927, -2), (key1327, -2), (key1319, -2), (key1625, -2), (key1427, -2), (key1634, -2), (key1445, -2), (key1311, -2), (key1617, -2), (key1419, -2), (key1900, 1), (key1897, 1), (key1921, 1), (key1904, 1), (key1927, 1), (key1912, 1), (key1355, 1), (key1352, 1), (key1684, 1), (key1473, 1), (key1690, 1), (key1481, 1), (key1327, 1), (key1299, 1), (key1557, 1), (key1394, 1), (key1594, 1), (key1445, 1), (key1311, 1), (key1291, 1), (key1541, 1), (key1386, 1), (key1568, 1), (key1419, 1)]

theorem rawRowCheck8432 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form8 = rawRow8432 := by decide +kernel

def row8432 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8432 : row8432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8432 := by decide +kernel

theorem rowEval8432 (x : Key → ℝ) : Integer.Sparse.eval row8432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8432, Integer.Sparse.eval_collectBalanced, rawRowCheck8432]

def rawRow8433 : Integer.Sparse Key := [(key1919, -2), (key1927, -2), (key1921, -2), (key1427, -2), (key1445, -2), (key1319, -2), (key1634, -2), (key1327, -2), (key1625, -2), (key1419, -2), (key1311, -2), (key1617, -2), (key1904, 1), (key1912, 1), (key1897, 1), (key1927, 1), (key1900, 1), (key1921, 1), (key1473, 1), (key1481, 1), (key1352, 1), (key1690, 1), (key1355, 1), (key1684, 1), (key1394, 1), (key1445, 1), (key1299, 1), (key1594, 1), (key1327, 1), (key1557, 1), (key1386, 1), (key1419, 1), (key1291, 1), (key1568, 1), (key1311, 1), (key1541, 1)]

theorem rawRowCheck8433 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form8 = rawRow8433 := by decide +kernel

def row8433 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8433 : row8433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8433 := by decide +kernel

theorem rowEval8433 (x : Key → ℝ) : Integer.Sparse.eval row8433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8433, Integer.Sparse.eval_collectBalanced, rawRowCheck8433]

def rawRow8434 : Integer.Sparse Key := [(key1927, -2), (key1919, -2), (key1921, -2), (key1445, -2), (key1427, -2), (key1634, -2), (key1319, -2), (key1625, -2), (key1327, -2), (key1419, -2), (key1617, -2), (key1311, -2), (key1912, 1), (key1904, 1), (key1927, 1), (key1897, 1), (key1921, 1), (key1900, 1), (key1481, 1), (key1473, 1), (key1690, 1), (key1352, 1), (key1684, 1), (key1355, 1), (key1445, 1), (key1394, 1), (key1594, 1), (key1299, 1), (key1557, 1), (key1327, 1), (key1419, 1), (key1386, 1), (key1568, 1), (key1291, 1), (key1541, 1), (key1311, 1)]

theorem rawRowCheck8434 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form8 = rawRow8434 := by decide +kernel

def row8434 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8434 : row8434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8434 := by decide +kernel

theorem rowEval8434 (x : Key → ℝ) : Integer.Sparse.eval row8434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8434, Integer.Sparse.eval_collectBalanced, rawRowCheck8434]

def rawRow8435 : Integer.Sparse Key := [(key1921, -2), (key1927, -2), (key1919, -2), (key1625, -2), (key1634, -2), (key1327, -2), (key1445, -2), (key1319, -2), (key1427, -2), (key1617, -2), (key1311, -2), (key1419, -2), (key1921, 1), (key1927, 1), (key1900, 1), (key1912, 1), (key1897, 1), (key1904, 1), (key1684, 1), (key1690, 1), (key1355, 1), (key1481, 1), (key1352, 1), (key1473, 1), (key1557, 1), (key1594, 1), (key1327, 1), (key1445, 1), (key1299, 1), (key1394, 1), (key1541, 1), (key1568, 1), (key1311, 1), (key1419, 1), (key1291, 1), (key1386, 1)]

theorem rawRowCheck8435 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form8 = rawRow8435 := by decide +kernel

def row8435 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8435 : row8435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8435 := by decide +kernel

theorem rowEval8435 (x : Key → ℝ) : Integer.Sparse.eval row8435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8435, Integer.Sparse.eval_collectBalanced, rawRowCheck8435]

def rawRow8436 : Integer.Sparse Key := [(key1927, -2), (key1921, -2), (key1919, -2), (key1634, -2), (key1625, -2), (key1445, -2), (key1327, -2), (key1427, -2), (key1319, -2), (key1617, -2), (key1419, -2), (key1311, -2), (key1927, 1), (key1921, 1), (key1912, 1), (key1900, 1), (key1904, 1), (key1897, 1), (key1690, 1), (key1684, 1), (key1481, 1), (key1355, 1), (key1473, 1), (key1352, 1), (key1594, 1), (key1557, 1), (key1445, 1), (key1327, 1), (key1394, 1), (key1299, 1), (key1568, 1), (key1541, 1), (key1419, 1), (key1311, 1), (key1386, 1), (key1291, 1)]

theorem rawRowCheck8436 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form8 = rawRow8436 := by decide +kernel

def row8436 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck8436 : row8436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8436 := by decide +kernel

theorem rowEval8436 (x : Key → ℝ) : Integer.Sparse.eval row8436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8436, Integer.Sparse.eval_collectBalanced, rawRowCheck8436]

def rawRow8437 : Integer.Sparse Key := [(key1352, -2), (key1352, -2), (key1355, -2), (key1473, -2), (key1473, -2), (key1682, -2), (key1682, -2), (key1684, -2), (key1684, -2), (key1481, -2), (key1690, -2), (key1690, -2), (key1299, 1), (key1299, 1), (key1319, 1), (key1319, 1), (key1327, 1), (key1327, 1), (key1394, 1), (key1394, 1), (key1549, 1), (key1549, 1), (key1557, 1), (key1557, 1), (key1427, 1), (key1427, 1), (key1576, 1), (key1576, 1), (key1625, 1), (key1625, 1), (key1445, 1), (key1445, 1), (key1594, 1), (key1594, 1), (key1634, 1), (key1634, 1)]

theorem rawRowCheck8437 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form8 = rawRow8437 := by decide +kernel

def row8437 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

theorem rowCheck8437 : row8437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8437 := by decide +kernel

theorem rowEval8437 (x : Key → ℝ) : Integer.Sparse.eval row8437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8437, Integer.Sparse.eval_collectBalanced, rawRowCheck8437]

def rawRow8438 : Integer.Sparse Key := [(key1352, -2), (key1355, -2), (key1352, -2), (key1682, -2), (key1684, -2), (key1473, -2), (key1684, -2), (key1473, -2), (key1682, -2), (key1690, -2), (key1481, -2), (key1690, -2), (key1319, 1), (key1327, 1), (key1299, 1), (key1327, 1), (key1299, 1), (key1319, 1), (key1549, 1), (key1557, 1), (key1394, 1), (key1557, 1), (key1394, 1), (key1549, 1), (key1576, 1), (key1625, 1), (key1427, 1), (key1625, 1), (key1427, 1), (key1576, 1), (key1594, 1), (key1634, 1), (key1445, 1), (key1634, 1), (key1445, 1), (key1594, 1)]

theorem rawRowCheck8438 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form8 = rawRow8438 := by decide +kernel

def row8438 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

theorem rowCheck8438 : row8438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8438 := by decide +kernel

theorem rowEval8438 (x : Key → ℝ) : Integer.Sparse.eval row8438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8438, Integer.Sparse.eval_collectBalanced, rawRowCheck8438]

def rawRow8439 : Integer.Sparse Key := [(key1355, -2), (key1352, -2), (key1352, -2), (key1684, -2), (key1682, -2), (key1684, -2), (key1473, -2), (key1682, -2), (key1473, -2), (key1690, -2), (key1690, -2), (key1481, -2), (key1327, 1), (key1319, 1), (key1327, 1), (key1299, 1), (key1319, 1), (key1299, 1), (key1557, 1), (key1549, 1), (key1557, 1), (key1394, 1), (key1549, 1), (key1394, 1), (key1625, 1), (key1576, 1), (key1625, 1), (key1427, 1), (key1576, 1), (key1427, 1), (key1634, 1), (key1594, 1), (key1634, 1), (key1445, 1), (key1594, 1), (key1445, 1)]

theorem rawRowCheck8439 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form8 = rawRow8439 := by decide +kernel

def row8439 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

theorem rowCheck8439 : row8439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8439 := by decide +kernel

theorem rowEval8439 (x : Key → ℝ) : Integer.Sparse.eval row8439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8439, Integer.Sparse.eval_collectBalanced, rawRowCheck8439]

def rawRow8440 : Integer.Sparse Key := [(key1473, -2), (key1473, -2), (key1481, -2), (key1352, -2), (key1352, -2), (key1682, -2), (key1682, -2), (key1690, -2), (key1690, -2), (key1355, -2), (key1684, -2), (key1684, -2), (key1394, 1), (key1394, 1), (key1427, 1), (key1427, 1), (key1445, 1), (key1445, 1), (key1299, 1), (key1299, 1), (key1576, 1), (key1576, 1), (key1594, 1), (key1594, 1), (key1319, 1), (key1319, 1), (key1549, 1), (key1549, 1), (key1634, 1), (key1634, 1), (key1327, 1), (key1327, 1), (key1557, 1), (key1557, 1), (key1625, 1), (key1625, 1)]

theorem rawRowCheck8440 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form8 = rawRow8440 := by decide +kernel

def row8440 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

theorem rowCheck8440 : row8440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8440 := by decide +kernel

theorem rowEval8440 (x : Key → ℝ) : Integer.Sparse.eval row8440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8440, Integer.Sparse.eval_collectBalanced, rawRowCheck8440]

def rawRow8441 : Integer.Sparse Key := [(key1473, -2), (key1481, -2), (key1473, -2), (key1682, -2), (key1690, -2), (key1352, -2), (key1690, -2), (key1352, -2), (key1682, -2), (key1684, -2), (key1355, -2), (key1684, -2), (key1427, 1), (key1445, 1), (key1394, 1), (key1445, 1), (key1394, 1), (key1427, 1), (key1576, 1), (key1594, 1), (key1299, 1), (key1594, 1), (key1299, 1), (key1576, 1), (key1549, 1), (key1634, 1), (key1319, 1), (key1634, 1), (key1319, 1), (key1549, 1), (key1557, 1), (key1625, 1), (key1327, 1), (key1625, 1), (key1327, 1), (key1557, 1)]

theorem rawRowCheck8441 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form8 = rawRow8441 := by decide +kernel

def row8441 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

theorem rowCheck8441 : row8441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8441 := by decide +kernel

theorem rowEval8441 (x : Key → ℝ) : Integer.Sparse.eval row8441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8441, Integer.Sparse.eval_collectBalanced, rawRowCheck8441]

def rawRow8442 : Integer.Sparse Key := [(key1481, -2), (key1473, -2), (key1473, -2), (key1690, -2), (key1682, -2), (key1690, -2), (key1352, -2), (key1682, -2), (key1352, -2), (key1684, -2), (key1684, -2), (key1355, -2), (key1445, 1), (key1427, 1), (key1445, 1), (key1394, 1), (key1427, 1), (key1394, 1), (key1594, 1), (key1576, 1), (key1594, 1), (key1299, 1), (key1576, 1), (key1299, 1), (key1634, 1), (key1549, 1), (key1634, 1), (key1319, 1), (key1549, 1), (key1319, 1), (key1625, 1), (key1557, 1), (key1625, 1), (key1327, 1), (key1557, 1), (key1327, 1)]

theorem rawRowCheck8442 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form8 = rawRow8442 := by decide +kernel

def row8442 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

theorem rowCheck8442 : row8442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8442 := by decide +kernel

theorem rowEval8442 (x : Key → ℝ) : Integer.Sparse.eval row8442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8442, Integer.Sparse.eval_collectBalanced, rawRowCheck8442]

def rawRow8443 : Integer.Sparse Key := [(key1682, -2), (key1684, -2), (key1690, -2), (key1352, -2), (key1355, -2), (key1473, -2), (key1684, -2), (key1481, -2), (key1690, -2), (key1352, -2), (key1473, -2), (key1682, -2), (key1549, 1), (key1557, 1), (key1576, 1), (key1625, 1), (key1594, 1), (key1634, 1), (key1319, 1), (key1327, 1), (key1427, 1), (key1625, 1), (key1445, 1), (key1634, 1), (key1299, 1), (key1327, 1), (key1394, 1), (key1557, 1), (key1445, 1), (key1594, 1), (key1299, 1), (key1319, 1), (key1394, 1), (key1549, 1), (key1427, 1), (key1576, 1)]

theorem rawRowCheck8443 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form8 = rawRow8443 := by decide +kernel

def row8443 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

theorem rowCheck8443 : row8443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8443 := by decide +kernel

theorem rowEval8443 (x : Key → ℝ) : Integer.Sparse.eval row8443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8443, Integer.Sparse.eval_collectBalanced, rawRowCheck8443]

def rawRow8444 : Integer.Sparse Key := [(key1684, -2), (key1682, -2), (key1690, -2), (key1355, -2), (key1352, -2), (key1684, -2), (key1473, -2), (key1690, -2), (key1481, -2), (key1352, -2), (key1682, -2), (key1473, -2), (key1557, 1), (key1549, 1), (key1625, 1), (key1576, 1), (key1634, 1), (key1594, 1), (key1327, 1), (key1319, 1), (key1625, 1), (key1427, 1), (key1634, 1), (key1445, 1), (key1327, 1), (key1299, 1), (key1557, 1), (key1394, 1), (key1594, 1), (key1445, 1), (key1319, 1), (key1299, 1), (key1549, 1), (key1394, 1), (key1576, 1), (key1427, 1)]

theorem rawRowCheck8444 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form8 = rawRow8444 := by decide +kernel

def row8444 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

theorem rowCheck8444 : row8444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8444 := by decide +kernel

theorem rowEval8444 (x : Key → ℝ) : Integer.Sparse.eval row8444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8444, Integer.Sparse.eval_collectBalanced, rawRowCheck8444]

def rawRow8445 : Integer.Sparse Key := [(key1682, -2), (key1690, -2), (key1684, -2), (key1473, -2), (key1481, -2), (key1352, -2), (key1690, -2), (key1355, -2), (key1684, -2), (key1473, -2), (key1352, -2), (key1682, -2), (key1576, 1), (key1594, 1), (key1549, 1), (key1634, 1), (key1557, 1), (key1625, 1), (key1427, 1), (key1445, 1), (key1319, 1), (key1634, 1), (key1327, 1), (key1625, 1), (key1394, 1), (key1445, 1), (key1299, 1), (key1594, 1), (key1327, 1), (key1557, 1), (key1394, 1), (key1427, 1), (key1299, 1), (key1576, 1), (key1319, 1), (key1549, 1)]

theorem rawRowCheck8445 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form8 = rawRow8445 := by decide +kernel

def row8445 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

theorem rowCheck8445 : row8445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8445 := by decide +kernel

theorem rowEval8445 (x : Key → ℝ) : Integer.Sparse.eval row8445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8445, Integer.Sparse.eval_collectBalanced, rawRowCheck8445]

def rawRow8446 : Integer.Sparse Key := [(key1690, -2), (key1682, -2), (key1684, -2), (key1481, -2), (key1473, -2), (key1690, -2), (key1352, -2), (key1684, -2), (key1355, -2), (key1473, -2), (key1682, -2), (key1352, -2), (key1594, 1), (key1576, 1), (key1634, 1), (key1549, 1), (key1625, 1), (key1557, 1), (key1445, 1), (key1427, 1), (key1634, 1), (key1319, 1), (key1625, 1), (key1327, 1), (key1445, 1), (key1394, 1), (key1594, 1), (key1299, 1), (key1557, 1), (key1327, 1), (key1427, 1), (key1394, 1), (key1576, 1), (key1299, 1), (key1549, 1), (key1319, 1)]

theorem rawRowCheck8446 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form8 = rawRow8446 := by decide +kernel

def row8446 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

theorem rowCheck8446 : row8446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8446 := by decide +kernel

theorem rowEval8446 (x : Key → ℝ) : Integer.Sparse.eval row8446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8446, Integer.Sparse.eval_collectBalanced, rawRowCheck8446]

def rawRow8447 : Integer.Sparse Key := [(key1684, -2), (key1690, -2), (key1682, -2), (key1684, -2), (key1690, -2), (key1355, -2), (key1481, -2), (key1352, -2), (key1473, -2), (key1682, -2), (key1352, -2), (key1473, -2), (key1625, 1), (key1634, 1), (key1557, 1), (key1594, 1), (key1549, 1), (key1576, 1), (key1625, 1), (key1634, 1), (key1327, 1), (key1445, 1), (key1319, 1), (key1427, 1), (key1557, 1), (key1594, 1), (key1327, 1), (key1445, 1), (key1299, 1), (key1394, 1), (key1549, 1), (key1576, 1), (key1319, 1), (key1427, 1), (key1299, 1), (key1394, 1)]

theorem rawRowCheck8447 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form8 = rawRow8447 := by decide +kernel

def row8447 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

theorem rowCheck8447 : row8447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8447 := by decide +kernel

theorem rowEval8447 (x : Key → ℝ) : Integer.Sparse.eval row8447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8447, Integer.Sparse.eval_collectBalanced, rawRowCheck8447]

end MUB6.Certificate.GramRows

end OAI
