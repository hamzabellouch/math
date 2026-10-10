import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
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

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8448 : Integer.Sparse Key := [(key1690, -2), (key1684, -2), (key1682, -2), (key1690, -2), (key1684, -2), (key1481, -2), (key1355, -2), (key1473, -2), (key1352, -2), (key1682, -2), (key1473, -2), (key1352, -2), (key1634, 1), (key1625, 1), (key1594, 1), (key1557, 1), (key1576, 1), (key1549, 1), (key1634, 1), (key1625, 1), (key1445, 1), (key1327, 1), (key1427, 1), (key1319, 1), (key1594, 1), (key1557, 1), (key1445, 1), (key1327, 1), (key1394, 1), (key1299, 1), (key1576, 1), (key1549, 1), (key1427, 1), (key1319, 1), (key1394, 1), (key1299, 1)]

theorem rawRowCheck8448 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form8 = rawRow8448 := by decide +kernel

def row8448 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

theorem rowCheck8448 : row8448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8448 := by decide +kernel

theorem rowEval8448 (x : Key → ℝ) : Integer.Sparse.eval row8448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8448, Integer.Sparse.eval_collectBalanced, rawRowCheck8448]

def rawRow8449 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, 1), (key2638, 1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, 1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1), (key2614, -2), (key2630, -2), (key2638, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2784, -2), (key2792, -2), (key2807, -2), (key2827, -2), (key2858, -2), (key2868, -2)]

theorem rawRowCheck8449 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form9 = rawRow8449 := by decide +kernel

def row8449 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8449 : row8449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8449 := by decide +kernel

theorem rowEval8449 (x : Key → ℝ) : Integer.Sparse.eval row8449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8449, Integer.Sparse.eval_collectBalanced, rawRowCheck8449]

def rawRow8450 : Integer.Sparse Key := [(key2614, 1), (key2608, 1), (key2638, 1), (key2624, 1), (key2659, 1), (key2657, 1), (key2669, 1), (key2663, 1), (key2724, 1), (key2698, 1), (key2757, 1), (key2752, 1), (key2792, 1), (key2778, 1), (key2827, 1), (key2801, 1), (key2922, 1), (key2919, 1), (key3009, 1), (key3007, 1), (key3016, 1), (key3011, 1), (key3025, 1), (key3022, 1), (key2614, -2), (key2638, -2), (key2630, -2), (key2669, -2), (key2724, -2), (key2704, -2), (key2792, -2), (key2784, -2), (key2827, -2), (key2807, -2), (key2868, -2), (key2858, -2)]

theorem rawRowCheck8450 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form9 = rawRow8450 := by decide +kernel

def row8450 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8450 : row8450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8450 := by decide +kernel

theorem rowEval8450 (x : Key → ℝ) : Integer.Sparse.eval row8450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8450, Integer.Sparse.eval_collectBalanced, rawRowCheck8450]

def rawRow8451 : Integer.Sparse Key := [(key2624, 1), (key2638, 1), (key2608, 1), (key2659, 1), (key2614, 1), (key2638, 1), (key2698, 1), (key2752, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2801, 1), (key2919, 1), (key2778, 1), (key2922, 1), (key2792, 1), (key2827, 1), (key3011, 1), (key3022, 1), (key3007, 1), (key3025, 1), (key3009, 1), (key3016, 1), (key2630, -2), (key2614, -2), (key2638, -2), (key2704, -2), (key2669, -2), (key2724, -2), (key2807, -2), (key2858, -2), (key2784, -2), (key2868, -2), (key2792, -2), (key2827, -2)]

theorem rawRowCheck8451 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form9 = rawRow8451 := by decide +kernel

def row8451 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8451 : row8451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8451 := by decide +kernel

theorem rowEval8451 (x : Key → ℝ) : Integer.Sparse.eval row8451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8451, Integer.Sparse.eval_collectBalanced, rawRowCheck8451]

def rawRow8452 : Integer.Sparse Key := [(key2638, 1), (key2624, 1), (key2659, 1), (key2608, 1), (key2638, 1), (key2614, 1), (key2752, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2724, 1), (key2669, 1), (key2919, 1), (key2801, 1), (key2922, 1), (key2778, 1), (key2827, 1), (key2792, 1), (key3022, 1), (key3011, 1), (key3025, 1), (key3007, 1), (key3016, 1), (key3009, 1), (key2630, -2), (key2638, -2), (key2614, -2), (key2704, -2), (key2724, -2), (key2669, -2), (key2858, -2), (key2807, -2), (key2868, -2), (key2784, -2), (key2827, -2), (key2792, -2)]

theorem rawRowCheck8452 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form9 = rawRow8452 := by decide +kernel

def row8452 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8452 : row8452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8452 := by decide +kernel

theorem rowEval8452 (x : Key → ℝ) : Integer.Sparse.eval row8452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8452, Integer.Sparse.eval_collectBalanced, rawRowCheck8452]

def rawRow8453 : Integer.Sparse Key := [(key2657, 1), (key2659, 1), (key2614, 1), (key2638, 1), (key2608, 1), (key2624, 1), (key2724, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2663, 1), (key2698, 1), (key2827, 1), (key2922, 1), (key2792, 1), (key2919, 1), (key2778, 1), (key2801, 1), (key3016, 1), (key3025, 1), (key3009, 1), (key3022, 1), (key3007, 1), (key3011, 1), (key2638, -2), (key2614, -2), (key2630, -2), (key2724, -2), (key2669, -2), (key2704, -2), (key2827, -2), (key2868, -2), (key2792, -2), (key2858, -2), (key2784, -2), (key2807, -2)]

theorem rawRowCheck8453 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form9 = rawRow8453 := by decide +kernel

def row8453 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8453 : row8453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8453 := by decide +kernel

theorem rowEval8453 (x : Key → ℝ) : Integer.Sparse.eval row8453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8453, Integer.Sparse.eval_collectBalanced, rawRowCheck8453]

def rawRow8454 : Integer.Sparse Key := [(key2659, 1), (key2657, 1), (key2638, 1), (key2614, 1), (key2624, 1), (key2608, 1), (key2757, 1), (key2724, 1), (key2752, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key2922, 1), (key2827, 1), (key2919, 1), (key2792, 1), (key2801, 1), (key2778, 1), (key3025, 1), (key3016, 1), (key3022, 1), (key3009, 1), (key3011, 1), (key3007, 1), (key2638, -2), (key2630, -2), (key2614, -2), (key2724, -2), (key2704, -2), (key2669, -2), (key2868, -2), (key2827, -2), (key2858, -2), (key2792, -2), (key2807, -2), (key2784, -2)]

theorem rawRowCheck8454 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form9 = rawRow8454 := by decide +kernel

def row8454 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8454 : row8454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8454 := by decide +kernel

theorem rowEval8454 (x : Key → ℝ) : Integer.Sparse.eval row8454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8454, Integer.Sparse.eval_collectBalanced, rawRowCheck8454]

def rawRow8455 : Integer.Sparse Key := [(key2663, 1), (key2669, 1), (key2698, 1), (key2752, 1), (key2724, 1), (key2757, 1), (key2608, 1), (key2614, 1), (key2801, 1), (key2827, 1), (key3011, 1), (key3016, 1), (key2624, 1), (key2638, 1), (key2698, 1), (key2724, 1), (key3022, 1), (key3025, 1), (key2657, 1), (key2659, 1), (key2752, 1), (key2757, 1), (key2919, 1), (key2922, 1), (key2669, -2), (key2784, -2), (key2792, -2), (key2614, -2), (key2807, -2), (key2827, -2), (key2630, -2), (key2638, -2), (key2704, -2), (key2724, -2), (key2858, -2), (key2868, -2)]

theorem rawRowCheck8455 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form9 = rawRow8455 := by decide +kernel

def row8455 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8455 : row8455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8455 := by decide +kernel

theorem rowEval8455 (x : Key → ℝ) : Integer.Sparse.eval row8455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8455, Integer.Sparse.eval_collectBalanced, rawRowCheck8455]

def rawRow8456 : Integer.Sparse Key := [(key2669, 1), (key2663, 1), (key2752, 1), (key2698, 1), (key2757, 1), (key2724, 1), (key2614, 1), (key2608, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key3011, 1), (key2638, 1), (key2624, 1), (key2724, 1), (key2698, 1), (key3025, 1), (key3022, 1), (key2659, 1), (key2657, 1), (key2757, 1), (key2752, 1), (key2922, 1), (key2919, 1), (key2669, -2), (key2792, -2), (key2784, -2), (key2614, -2), (key2827, -2), (key2807, -2), (key2638, -2), (key2630, -2), (key2724, -2), (key2704, -2), (key2868, -2), (key2858, -2)]

theorem rawRowCheck8456 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form9 = rawRow8456 := by decide +kernel

def row8456 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8456 : row8456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8456 := by decide +kernel

theorem rowEval8456 (x : Key → ℝ) : Integer.Sparse.eval row8456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8456, Integer.Sparse.eval_collectBalanced, rawRowCheck8456]

def rawRow8457 : Integer.Sparse Key := [(key2698, 1), (key2724, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2801, 1), (key2827, 1), (key2608, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2698, 1), (key3022, 1), (key2624, 1), (key3025, 1), (key2638, 1), (key2724, 1), (key2752, 1), (key2919, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2757, 1), (key2784, -2), (key2669, -2), (key2792, -2), (key2807, -2), (key2614, -2), (key2827, -2), (key2704, -2), (key2858, -2), (key2630, -2), (key2868, -2), (key2638, -2), (key2724, -2)]

theorem rawRowCheck8457 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form9 = rawRow8457 := by decide +kernel

def row8457 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8457 : row8457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8457 := by decide +kernel

theorem rowEval8457 (x : Key → ℝ) : Integer.Sparse.eval row8457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8457, Integer.Sparse.eval_collectBalanced, rawRowCheck8457]

def rawRow8458 : Integer.Sparse Key := [(key2724, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2752, 1), (key2669, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key2608, 1), (key2827, 1), (key2614, 1), (key3022, 1), (key2698, 1), (key3025, 1), (key2624, 1), (key2724, 1), (key2638, 1), (key2919, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2757, 1), (key2659, 1), (key2784, -2), (key2792, -2), (key2669, -2), (key2807, -2), (key2827, -2), (key2614, -2), (key2858, -2), (key2704, -2), (key2868, -2), (key2630, -2), (key2724, -2), (key2638, -2)]

theorem rawRowCheck8458 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form9 = rawRow8458 := by decide +kernel

def row8458 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8458 : row8458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8458 := by decide +kernel

theorem rowEval8458 (x : Key → ℝ) : Integer.Sparse.eval row8458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8458, Integer.Sparse.eval_collectBalanced, rawRowCheck8458]

def rawRow8459 : Integer.Sparse Key := [(key2752, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2663, 1), (key2698, 1), (key3011, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2608, 1), (key2801, 1), (key2724, 1), (key3025, 1), (key2638, 1), (key3022, 1), (key2624, 1), (key2698, 1), (key2757, 1), (key2922, 1), (key2659, 1), (key2919, 1), (key2657, 1), (key2752, 1), (key2792, -2), (key2669, -2), (key2784, -2), (key2827, -2), (key2614, -2), (key2807, -2), (key2724, -2), (key2868, -2), (key2638, -2), (key2858, -2), (key2630, -2), (key2704, -2)]

theorem rawRowCheck8459 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form9 = rawRow8459 := by decide +kernel

def row8459 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8459 : row8459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8459 := by decide +kernel

theorem rowEval8459 (x : Key → ℝ) : Integer.Sparse.eval row8459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8459, Integer.Sparse.eval_collectBalanced, rawRowCheck8459]

def rawRow8460 : Integer.Sparse Key := [(key2757, 1), (key2752, 1), (key2724, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key3016, 1), (key3011, 1), (key2827, 1), (key2614, 1), (key2801, 1), (key2608, 1), (key3025, 1), (key2724, 1), (key3022, 1), (key2638, 1), (key2698, 1), (key2624, 1), (key2922, 1), (key2757, 1), (key2919, 1), (key2659, 1), (key2752, 1), (key2657, 1), (key2792, -2), (key2784, -2), (key2669, -2), (key2827, -2), (key2807, -2), (key2614, -2), (key2868, -2), (key2724, -2), (key2858, -2), (key2638, -2), (key2704, -2), (key2630, -2)]

theorem rawRowCheck8460 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form9 = rawRow8460 := by decide +kernel

def row8460 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8460 : row8460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8460 := by decide +kernel

theorem rowEval8460 (x : Key → ℝ) : Integer.Sparse.eval row8460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8460, Integer.Sparse.eval_collectBalanced, rawRowCheck8460]

def rawRow8461 : Integer.Sparse Key := [(key2778, 1), (key2792, 1), (key2801, 1), (key2919, 1), (key2827, 1), (key2922, 1), (key2624, 1), (key2638, 1), (key2698, 1), (key3022, 1), (key2724, 1), (key3025, 1), (key2608, 1), (key2659, 1), (key2663, 1), (key2757, 1), (key3009, 1), (key3016, 1), (key2614, 1), (key2638, 1), (key2669, 1), (key2724, 1), (key2792, 1), (key2827, 1), (key2704, -2), (key2807, -2), (key2858, -2), (key2630, -2), (key2784, -2), (key2868, -2), (key2614, -2), (key2638, -2), (key2669, -2), (key2724, -2), (key2792, -2), (key2827, -2)]

theorem rawRowCheck8461 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form9 = rawRow8461 := by decide +kernel

def row8461 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 1), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8461 : row8461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8461 := by decide +kernel

theorem rowEval8461 (x : Key → ℝ) : Integer.Sparse.eval row8461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8461, Integer.Sparse.eval_collectBalanced, rawRowCheck8461]

def rawRow8462 : Integer.Sparse Key := [(key2792, 1), (key2778, 1), (key2919, 1), (key2801, 1), (key2922, 1), (key2827, 1), (key2638, 1), (key2624, 1), (key3022, 1), (key2698, 1), (key3025, 1), (key2724, 1), (key2659, 1), (key2608, 1), (key2757, 1), (key2663, 1), (key3016, 1), (key3009, 1), (key2638, 1), (key2614, 1), (key2724, 1), (key2669, 1), (key2827, 1), (key2792, 1), (key2704, -2), (key2858, -2), (key2807, -2), (key2630, -2), (key2868, -2), (key2784, -2), (key2638, -2), (key2614, -2), (key2724, -2), (key2669, -2), (key2827, -2), (key2792, -2)]

theorem rawRowCheck8462 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form9 = rawRow8462 := by decide +kernel

def row8462 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 1), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8462 : row8462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8462 := by decide +kernel

theorem rowEval8462 (x : Key → ℝ) : Integer.Sparse.eval row8462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8462, Integer.Sparse.eval_collectBalanced, rawRowCheck8462]

def rawRow8463 : Integer.Sparse Key := [(key2801, 1), (key2827, 1), (key2778, 1), (key2922, 1), (key2792, 1), (key2919, 1), (key2698, 1), (key2724, 1), (key2624, 1), (key3025, 1), (key2638, 1), (key3022, 1), (key2663, 1), (key2757, 1), (key2608, 1), (key3016, 1), (key2659, 1), (key2757, 1), (key2669, 1), (key2792, 1), (key2614, 1), (key2827, 1), (key2638, 1), (key2724, 1), (key2807, -2), (key2704, -2), (key2858, -2), (key2784, -2), (key2630, -2), (key2868, -2), (key2669, -2), (key2792, -2), (key2614, -2), (key2827, -2), (key2638, -2), (key2724, -2)]

theorem rawRowCheck8463 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form9 = rawRow8463 := by decide +kernel

def row8463 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 2), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8463 : row8463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8463 := by decide +kernel

theorem rowEval8463 (x : Key → ℝ) : Integer.Sparse.eval row8463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8463, Integer.Sparse.eval_collectBalanced, rawRowCheck8463]

def rawRow8464 : Integer.Sparse Key := [(key2827, 1), (key2801, 1), (key2922, 1), (key2778, 1), (key2919, 1), (key2792, 1), (key2724, 1), (key2698, 1), (key3025, 1), (key2624, 1), (key3022, 1), (key2638, 1), (key2757, 1), (key2663, 1), (key3016, 1), (key2608, 1), (key2757, 1), (key2659, 1), (key2792, 1), (key2669, 1), (key2827, 1), (key2614, 1), (key2724, 1), (key2638, 1), (key2807, -2), (key2858, -2), (key2704, -2), (key2784, -2), (key2868, -2), (key2630, -2), (key2792, -2), (key2669, -2), (key2827, -2), (key2614, -2), (key2724, -2), (key2638, -2)]

theorem rawRowCheck8464 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form9 = rawRow8464 := by decide +kernel

def row8464 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 2), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8464 : row8464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8464 := by decide +kernel

theorem rowEval8464 (x : Key → ℝ) : Integer.Sparse.eval row8464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8464, Integer.Sparse.eval_collectBalanced, rawRowCheck8464]

def rawRow8465 : Integer.Sparse Key := [(key2919, 1), (key2922, 1), (key2792, 1), (key2827, 1), (key2778, 1), (key2801, 1), (key3022, 1), (key3025, 1), (key2638, 1), (key2724, 1), (key2624, 1), (key2698, 1), (key3009, 1), (key3016, 1), (key2659, 1), (key2757, 1), (key2608, 1), (key2663, 1), (key2724, 1), (key2827, 1), (key2638, 1), (key2792, 1), (key2614, 1), (key2669, 1), (key2858, -2), (key2704, -2), (key2807, -2), (key2868, -2), (key2630, -2), (key2784, -2), (key2724, -2), (key2827, -2), (key2638, -2), (key2792, -2), (key2614, -2), (key2669, -2)]

theorem rawRowCheck8465 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form9 = rawRow8465 := by decide +kernel

def row8465 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 1), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8465 : row8465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8465 := by decide +kernel

theorem rowEval8465 (x : Key → ℝ) : Integer.Sparse.eval row8465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8465, Integer.Sparse.eval_collectBalanced, rawRowCheck8465]

def rawRow8466 : Integer.Sparse Key := [(key2922, 1), (key2919, 1), (key2827, 1), (key2792, 1), (key2801, 1), (key2778, 1), (key3025, 1), (key3022, 1), (key2724, 1), (key2638, 1), (key2698, 1), (key2624, 1), (key3016, 1), (key3009, 1), (key2757, 1), (key2659, 1), (key2663, 1), (key2608, 1), (key2827, 1), (key2724, 1), (key2792, 1), (key2638, 1), (key2669, 1), (key2614, 1), (key2858, -2), (key2807, -2), (key2704, -2), (key2868, -2), (key2784, -2), (key2630, -2), (key2827, -2), (key2724, -2), (key2792, -2), (key2638, -2), (key2669, -2), (key2614, -2)]

theorem rawRowCheck8466 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form9 = rawRow8466 := by decide +kernel

def row8466 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 1), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8466 : row8466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8466 := by decide +kernel

theorem rowEval8466 (x : Key → ℝ) : Integer.Sparse.eval row8466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8466, Integer.Sparse.eval_collectBalanced, rawRowCheck8466]

def rawRow8467 : Integer.Sparse Key := [(key3007, 1), (key3009, 1), (key3011, 1), (key3022, 1), (key3016, 1), (key3025, 1), (key2657, 1), (key2659, 1), (key2752, 1), (key2919, 1), (key2757, 1), (key2922, 1), (key2614, 1), (key2638, 1), (key2669, 1), (key2792, 1), (key2724, 1), (key2827, 1), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1), (key2724, -2), (key2827, -2), (key2868, -2), (key2638, -2), (key2792, -2), (key2858, -2), (key2614, -2), (key2630, -2), (key2669, -2), (key2704, -2), (key2784, -2), (key2807, -2)]

theorem rawRowCheck8467 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form9 = rawRow8467 := by decide +kernel

def row8467 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8467 : row8467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8467 := by decide +kernel

theorem rowEval8467 (x : Key → ℝ) : Integer.Sparse.eval row8467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8467, Integer.Sparse.eval_collectBalanced, rawRowCheck8467]

def rawRow8468 : Integer.Sparse Key := [(key3009, 1), (key3007, 1), (key3022, 1), (key3011, 1), (key3025, 1), (key3016, 1), (key2659, 1), (key2657, 1), (key2919, 1), (key2752, 1), (key2922, 1), (key2757, 1), (key2638, 1), (key2614, 1), (key2792, 1), (key2669, 1), (key2827, 1), (key2724, 1), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1), (key2724, -2), (key2868, -2), (key2827, -2), (key2638, -2), (key2858, -2), (key2792, -2), (key2630, -2), (key2614, -2), (key2704, -2), (key2669, -2), (key2807, -2), (key2784, -2)]

theorem rawRowCheck8468 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form9 = rawRow8468 := by decide +kernel

def row8468 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8468 : row8468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8468 := by decide +kernel

theorem rowEval8468 (x : Key → ℝ) : Integer.Sparse.eval row8468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8468, Integer.Sparse.eval_collectBalanced, rawRowCheck8468]

def rawRow8469 : Integer.Sparse Key := [(key3011, 1), (key3016, 1), (key3007, 1), (key3025, 1), (key3009, 1), (key3022, 1), (key2752, 1), (key2757, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2919, 1), (key2669, 1), (key2724, 1), (key2614, 1), (key2827, 1), (key2638, 1), (key2792, 1), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2827, -2), (key2724, -2), (key2868, -2), (key2792, -2), (key2638, -2), (key2858, -2), (key2669, -2), (key2784, -2), (key2614, -2), (key2807, -2), (key2630, -2), (key2704, -2)]

theorem rawRowCheck8469 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form9 = rawRow8469 := by decide +kernel

def row8469 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8469 : row8469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8469 := by decide +kernel

theorem rowEval8469 (x : Key → ℝ) : Integer.Sparse.eval row8469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8469, Integer.Sparse.eval_collectBalanced, rawRowCheck8469]

def rawRow8470 : Integer.Sparse Key := [(key3016, 1), (key3011, 1), (key3025, 1), (key3007, 1), (key3022, 1), (key3009, 1), (key2757, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2919, 1), (key2659, 1), (key2724, 1), (key2669, 1), (key2827, 1), (key2614, 1), (key2792, 1), (key2638, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1), (key2827, -2), (key2868, -2), (key2724, -2), (key2792, -2), (key2858, -2), (key2638, -2), (key2784, -2), (key2669, -2), (key2807, -2), (key2614, -2), (key2704, -2), (key2630, -2)]

theorem rawRowCheck8470 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form9 = rawRow8470 := by decide +kernel

def row8470 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8470 : row8470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8470 := by decide +kernel

theorem rowEval8470 (x : Key → ℝ) : Integer.Sparse.eval row8470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8470, Integer.Sparse.eval_collectBalanced, rawRowCheck8470]

def rawRow8471 : Integer.Sparse Key := [(key3022, 1), (key3025, 1), (key3009, 1), (key3016, 1), (key3007, 1), (key3011, 1), (key2919, 1), (key2922, 1), (key2659, 1), (key2757, 1), (key2657, 1), (key2752, 1), (key2792, 1), (key2827, 1), (key2638, 1), (key2724, 1), (key2614, 1), (key2669, 1), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1), (key2868, -2), (key2724, -2), (key2827, -2), (key2858, -2), (key2638, -2), (key2792, -2), (key2704, -2), (key2807, -2), (key2630, -2), (key2784, -2), (key2614, -2), (key2669, -2)]

theorem rawRowCheck8471 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form9 = rawRow8471 := by decide +kernel

def row8471 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8471 : row8471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8471 := by decide +kernel

theorem rowEval8471 (x : Key → ℝ) : Integer.Sparse.eval row8471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8471, Integer.Sparse.eval_collectBalanced, rawRowCheck8471]

def rawRow8472 : Integer.Sparse Key := [(key3025, 1), (key3022, 1), (key3016, 1), (key3009, 1), (key3011, 1), (key3007, 1), (key2922, 1), (key2919, 1), (key2757, 1), (key2659, 1), (key2752, 1), (key2657, 1), (key2827, 1), (key2792, 1), (key2724, 1), (key2638, 1), (key2669, 1), (key2614, 1), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1), (key2868, -2), (key2827, -2), (key2724, -2), (key2858, -2), (key2792, -2), (key2638, -2), (key2807, -2), (key2704, -2), (key2784, -2), (key2630, -2), (key2669, -2), (key2614, -2)]

theorem rawRowCheck8472 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form9 = rawRow8472 := by decide +kernel

def row8472 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rowCheck8472 : row8472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8472 := by decide +kernel

theorem rowEval8472 (x : Key → ℝ) : Integer.Sparse.eval row8472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8472, Integer.Sparse.eval_collectBalanced, rawRowCheck8472]

def rawRow8473 : Integer.Sparse Key := [(key2614, 1), (key2614, 1), (key2630, 1), (key2630, 1), (key2638, 1), (key2638, 1), (key2669, 1), (key2669, 1), (key2784, 1), (key2784, 1), (key2792, 1), (key2792, 1), (key2704, 1), (key2704, 1), (key2807, 1), (key2807, 1), (key2858, 1), (key2858, 1), (key2724, 1), (key2724, 1), (key2827, 1), (key2827, 1), (key2868, 1), (key2868, 1), (key2608, -2), (key2624, -2), (key2624, -2), (key2663, -2), (key2698, -2), (key2698, -2), (key2778, -2), (key2778, -2), (key2801, -2), (key2801, -2), (key2851, -2), (key2851, -2)]

theorem rawRowCheck8473 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form9 = rawRow8473 := by decide +kernel

def row8473 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

theorem rowCheck8473 : row8473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8473 := by decide +kernel

theorem rowEval8473 (x : Key → ℝ) : Integer.Sparse.eval row8473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8473, Integer.Sparse.eval_collectBalanced, rawRowCheck8473]

def rawRow8474 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2614, 1), (key2638, 1), (key2614, 1), (key2630, 1), (key2784, 1), (key2792, 1), (key2669, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2807, 1), (key2858, 1), (key2704, 1), (key2858, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2868, 1), (key2724, 1), (key2868, 1), (key2724, 1), (key2827, 1), (key2624, -2), (key2608, -2), (key2624, -2), (key2698, -2), (key2663, -2), (key2698, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key2851, -2), (key2778, -2), (key2801, -2)]

theorem rawRowCheck8474 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form9 = rawRow8474 := by decide +kernel

def row8474 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

theorem rowCheck8474 : row8474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8474 := by decide +kernel

theorem rowEval8474 (x : Key → ℝ) : Integer.Sparse.eval row8474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8474, Integer.Sparse.eval_collectBalanced, rawRowCheck8474]

def rawRow8475 : Integer.Sparse Key := [(key2638, 1), (key2630, 1), (key2638, 1), (key2614, 1), (key2630, 1), (key2614, 1), (key2792, 1), (key2784, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2669, 1), (key2858, 1), (key2807, 1), (key2858, 1), (key2704, 1), (key2807, 1), (key2704, 1), (key2868, 1), (key2827, 1), (key2868, 1), (key2724, 1), (key2827, 1), (key2724, 1), (key2624, -2), (key2624, -2), (key2608, -2), (key2698, -2), (key2698, -2), (key2663, -2), (key2851, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key2801, -2), (key2778, -2)]

theorem rawRowCheck8475 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form9 = rawRow8475 := by decide +kernel

def row8475 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

theorem rowCheck8475 : row8475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8475 := by decide +kernel

theorem rowEval8475 (x : Key → ℝ) : Integer.Sparse.eval row8475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8475, Integer.Sparse.eval_collectBalanced, rawRowCheck8475]

def rawRow8476 : Integer.Sparse Key := [(key2669, 1), (key2669, 1), (key2704, 1), (key2704, 1), (key2724, 1), (key2724, 1), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1), (key2630, 1), (key2630, 1), (key2784, 1), (key2784, 1), (key2868, 1), (key2868, 1), (key2638, 1), (key2638, 1), (key2792, 1), (key2792, 1), (key2858, 1), (key2858, 1), (key2663, -2), (key2698, -2), (key2698, -2), (key2608, -2), (key2801, -2), (key2801, -2), (key2624, -2), (key2624, -2), (key2698, -2), (key2698, -2), (key2851, -2), (key2851, -2)]

theorem rawRowCheck8476 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form9 = rawRow8476 := by decide +kernel

def row8476 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -8), (key2704, 2), (key2724, 2), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

theorem rowCheck8476 : row8476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8476 := by decide +kernel

theorem rowEval8476 (x : Key → ℝ) : Integer.Sparse.eval row8476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8476, Integer.Sparse.eval_collectBalanced, rawRowCheck8476]

def rawRow8477 : Integer.Sparse Key := [(key2704, 1), (key2724, 1), (key2669, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2784, 1), (key2868, 1), (key2630, 1), (key2868, 1), (key2630, 1), (key2784, 1), (key2792, 1), (key2858, 1), (key2638, 1), (key2858, 1), (key2638, 1), (key2792, 1), (key2698, -2), (key2663, -2), (key2698, -2), (key2801, -2), (key2608, -2), (key2801, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2851, -2), (key2624, -2), (key2698, -2)]

theorem rawRowCheck8477 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form9 = rawRow8477 := by decide +kernel

def row8477 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -8), (key2704, 2), (key2724, 2), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

theorem rowCheck8477 : row8477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8477 := by decide +kernel

theorem rowEval8477 (x : Key → ℝ) : Integer.Sparse.eval row8477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8477, Integer.Sparse.eval_collectBalanced, rawRowCheck8477]

def rawRow8478 : Integer.Sparse Key := [(key2724, 1), (key2704, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key2669, 1), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1), (key2868, 1), (key2784, 1), (key2868, 1), (key2630, 1), (key2784, 1), (key2630, 1), (key2858, 1), (key2792, 1), (key2858, 1), (key2638, 1), (key2792, 1), (key2638, 1), (key2698, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2801, -2), (key2608, -2), (key2851, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2624, -2)]

theorem rawRowCheck8478 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form9 = rawRow8478 := by decide +kernel

def row8478 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -8), (key2704, 2), (key2724, 2), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

theorem rowCheck8478 : row8478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8478 := by decide +kernel

theorem rowEval8478 (x : Key → ℝ) : Integer.Sparse.eval row8478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8478, Integer.Sparse.eval_collectBalanced, rawRowCheck8478]

def rawRow8479 : Integer.Sparse Key := [(key2784, 1), (key2792, 1), (key2807, 1), (key2858, 1), (key2827, 1), (key2868, 1), (key2630, 1), (key2638, 1), (key2704, 1), (key2858, 1), (key2724, 1), (key2868, 1), (key2614, 1), (key2638, 1), (key2669, 1), (key2792, 1), (key2724, 1), (key2827, 1), (key2614, 1), (key2630, 1), (key2669, 1), (key2784, 1), (key2704, 1), (key2807, 1), (key2778, -2), (key2801, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2851, -2), (key2608, -2), (key2624, -2), (key2663, -2), (key2698, -2), (key2778, -2), (key2801, -2)]

theorem rawRowCheck8479 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form9 = rawRow8479 := by decide +kernel

def row8479 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

theorem rowCheck8479 : row8479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8479 := by decide +kernel

theorem rowEval8479 (x : Key → ℝ) : Integer.Sparse.eval row8479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8479, Integer.Sparse.eval_collectBalanced, rawRowCheck8479]

def rawRow8480 : Integer.Sparse Key := [(key2792, 1), (key2784, 1), (key2858, 1), (key2807, 1), (key2868, 1), (key2827, 1), (key2638, 1), (key2630, 1), (key2858, 1), (key2704, 1), (key2868, 1), (key2724, 1), (key2638, 1), (key2614, 1), (key2792, 1), (key2669, 1), (key2827, 1), (key2724, 1), (key2630, 1), (key2614, 1), (key2784, 1), (key2669, 1), (key2807, 1), (key2704, 1), (key2778, -2), (key2851, -2), (key2801, -2), (key2624, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2608, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2778, -2)]

theorem rawRowCheck8480 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form9 = rawRow8480 := by decide +kernel

def row8480 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

theorem rowCheck8480 : row8480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8480 := by decide +kernel

theorem rowEval8480 (x : Key → ℝ) : Integer.Sparse.eval row8480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8480, Integer.Sparse.eval_collectBalanced, rawRowCheck8480]

def rawRow8481 : Integer.Sparse Key := [(key2807, 1), (key2827, 1), (key2784, 1), (key2868, 1), (key2792, 1), (key2858, 1), (key2704, 1), (key2724, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2858, 1), (key2669, 1), (key2724, 1), (key2614, 1), (key2827, 1), (key2638, 1), (key2792, 1), (key2669, 1), (key2704, 1), (key2614, 1), (key2807, 1), (key2630, 1), (key2784, 1), (key2801, -2), (key2778, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2851, -2), (key2663, -2), (key2698, -2), (key2608, -2), (key2801, -2), (key2624, -2), (key2698, -2)]

theorem rawRowCheck8481 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form9 = rawRow8481 := by decide +kernel

def row8481 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -6), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

theorem rowCheck8481 : row8481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8481 := by decide +kernel

theorem rowEval8481 (x : Key → ℝ) : Integer.Sparse.eval row8481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8481, Integer.Sparse.eval_collectBalanced, rawRowCheck8481]

def rawRow8482 : Integer.Sparse Key := [(key2827, 1), (key2807, 1), (key2868, 1), (key2784, 1), (key2858, 1), (key2792, 1), (key2724, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2858, 1), (key2638, 1), (key2724, 1), (key2669, 1), (key2827, 1), (key2614, 1), (key2792, 1), (key2638, 1), (key2704, 1), (key2669, 1), (key2807, 1), (key2614, 1), (key2784, 1), (key2630, 1), (key2801, -2), (key2851, -2), (key2778, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2608, -2), (key2698, -2), (key2624, -2)]

theorem rawRowCheck8482 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form9 = rawRow8482 := by decide +kernel

def row8482 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -6), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

theorem rowCheck8482 : row8482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8482 := by decide +kernel

theorem rowEval8482 (x : Key → ℝ) : Integer.Sparse.eval row8482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8482, Integer.Sparse.eval_collectBalanced, rawRowCheck8482]

def rawRow8483 : Integer.Sparse Key := [(key2858, 1), (key2868, 1), (key2792, 1), (key2827, 1), (key2784, 1), (key2807, 1), (key2858, 1), (key2868, 1), (key2638, 1), (key2724, 1), (key2630, 1), (key2704, 1), (key2792, 1), (key2827, 1), (key2638, 1), (key2724, 1), (key2614, 1), (key2669, 1), (key2784, 1), (key2807, 1), (key2630, 1), (key2704, 1), (key2614, 1), (key2669, 1), (key2851, -2), (key2778, -2), (key2801, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2778, -2), (key2801, -2), (key2624, -2), (key2698, -2), (key2608, -2), (key2663, -2)]

theorem rawRowCheck8483 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form9 = rawRow8483 := by decide +kernel

def row8483 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

theorem rowCheck8483 : row8483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8483 := by decide +kernel

theorem rowEval8483 (x : Key → ℝ) : Integer.Sparse.eval row8483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8483, Integer.Sparse.eval_collectBalanced, rawRowCheck8483]

def rawRow8484 : Integer.Sparse Key := [(key2868, 1), (key2858, 1), (key2827, 1), (key2792, 1), (key2807, 1), (key2784, 1), (key2868, 1), (key2858, 1), (key2724, 1), (key2638, 1), (key2704, 1), (key2630, 1), (key2827, 1), (key2792, 1), (key2724, 1), (key2638, 1), (key2669, 1), (key2614, 1), (key2807, 1), (key2784, 1), (key2704, 1), (key2630, 1), (key2669, 1), (key2614, 1), (key2851, -2), (key2801, -2), (key2778, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2801, -2), (key2778, -2), (key2698, -2), (key2624, -2), (key2663, -2), (key2608, -2)]

theorem rawRowCheck8484 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form9 = rawRow8484 := by decide +kernel

def row8484 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

theorem rowCheck8484 : row8484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8484 := by decide +kernel

theorem rowEval8484 (x : Key → ℝ) : Integer.Sparse.eval row8484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8484, Integer.Sparse.eval_collectBalanced, rawRowCheck8484]

def rawRow8485 : Integer.Sparse Key := [(key1254, 2), (key1254, 2), (key1254, 2), (key1607, 2), (key1607, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1804, 2), (key1804, 2), (key1804, 2), (key1804, 2), (key1263, -2), (key1263, -2), (key1263, -2), (key1646, -2), (key1646, -2), (key1646, -2), (key1646, -2), (key1646, -2), (key1646, -2), (key1835, -2), (key1835, -2), (key1835, -2)]

theorem rawRowCheck8485 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow8485 := by decide +kernel

def row8485 : Integer.Sparse Key := [(key1254, 6), (key1263, -6), (key1607, 6), (key1646, -12), (key1804, 12), (key1835, -6)]

theorem rowCheck8485 : row8485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8485 := by decide +kernel

theorem rowEval8485 (x : Key → ℝ) : Integer.Sparse.eval row8485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8485, Integer.Sparse.eval_collectBalanced, rawRowCheck8485]

def rawRow8486 : Integer.Sparse Key := [(key1607, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1254, 2), (key1607, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1646, -2), (key1646, -2), (key1835, -2), (key1263, -2), (key1263, -2), (key1646, -2), (key1646, -2), (key1835, -2), (key1835, -2), (key1263, -2), (key1646, -2), (key1646, -2)]

theorem rawRowCheck8486 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form0 = rawRow8486 := by decide +kernel

def row8486 : Integer.Sparse Key := [(key1254, 6), (key1263, -6), (key1607, 6), (key1646, -12), (key1804, 12), (key1835, -6)]

theorem rowCheck8486 : row8486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8486 := by decide +kernel

theorem rowEval8486 (x : Key → ℝ) : Integer.Sparse.eval row8486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8486, Integer.Sparse.eval_collectBalanced, rawRowCheck8486]

def rawRow8487 : Integer.Sparse Key := [(key1804, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1607, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1254, 2), (key1607, 2), (key1646, -2), (key1835, -2), (key1646, -2), (key1646, -2), (key1835, -2), (key1263, -2), (key1835, -2), (key1263, -2), (key1646, -2), (key1646, -2), (key1263, -2), (key1646, -2)]

theorem rawRowCheck8487 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form0 = rawRow8487 := by decide +kernel

def row8487 : Integer.Sparse Key := [(key1254, 6), (key1263, -6), (key1607, 6), (key1646, -12), (key1804, 12), (key1835, -6)]

theorem rowCheck8487 : row8487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8487 := by decide +kernel

theorem rowEval8487 (x : Key → ℝ) : Integer.Sparse.eval row8487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8487, Integer.Sparse.eval_collectBalanced, rawRowCheck8487]

def rawRow8488 : Integer.Sparse Key := [(key1804, 2), (key1804, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1607, 2), (key1804, 2), (key1254, 2), (key1607, 2), (key1254, 2), (key1835, -2), (key1646, -2), (key1646, -2), (key1835, -2), (key1646, -2), (key1835, -2), (key1263, -2), (key1646, -2), (key1263, -2), (key1646, -2), (key1646, -2), (key1263, -2)]

theorem rawRowCheck8488 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form0 = rawRow8488 := by decide +kernel

def row8488 : Integer.Sparse Key := [(key1254, 6), (key1263, -6), (key1607, 6), (key1646, -12), (key1804, 12), (key1835, -6)]

theorem rowCheck8488 : row8488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8488 := by decide +kernel

theorem rowEval8488 (x : Key → ℝ) : Integer.Sparse.eval row8488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8488, Integer.Sparse.eval_collectBalanced, rawRowCheck8488]

def rawRow8489 : Integer.Sparse Key := [(key1254, 2), (key1263, 2), (key1263, 2), (key1529, 2), (key1646, 2), (key1646, 2), (key1763, 2), (key1763, 2), (key1804, 2), (key1804, 2), (key1835, 2), (key1835, 2), (key1254, -2), (key1254, -2), (key1263, -2), (key1529, -2), (key1529, -2), (key1607, -2), (key1607, -2), (key1646, -2), (key1646, -2), (key1763, -2), (key1804, -2), (key1804, -2)]

theorem rawRowCheck8489 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form0 = rawRow8489 := by decide +kernel

def row8489 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

theorem rowCheck8489 : row8489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8489 := by decide +kernel

theorem rowEval8489 (x : Key → ℝ) : Integer.Sparse.eval row8489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8489, Integer.Sparse.eval_collectBalanced, rawRowCheck8489]

def rawRow8490 : Integer.Sparse Key := [(key1263, 2), (key1254, 2), (key1263, 2), (key1646, 2), (key1529, 2), (key1646, 2), (key1804, 2), (key1835, 2), (key1763, 2), (key1835, 2), (key1763, 2), (key1804, 2), (key1254, -2), (key1263, -2), (key1254, -2), (key1607, -2), (key1646, -2), (key1529, -2), (key1646, -2), (key1529, -2), (key1607, -2), (key1804, -2), (key1763, -2), (key1804, -2)]

theorem rawRowCheck8490 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form0 = rawRow8490 := by decide +kernel

def row8490 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

theorem rowCheck8490 : row8490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8490 := by decide +kernel

theorem rowEval8490 (x : Key → ℝ) : Integer.Sparse.eval row8490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8490, Integer.Sparse.eval_collectBalanced, rawRowCheck8490]

def rawRow8491 : Integer.Sparse Key := [(key1263, 2), (key1263, 2), (key1254, 2), (key1646, 2), (key1646, 2), (key1529, 2), (key1835, 2), (key1804, 2), (key1835, 2), (key1763, 2), (key1804, 2), (key1763, 2), (key1263, -2), (key1254, -2), (key1254, -2), (key1646, -2), (key1607, -2), (key1646, -2), (key1529, -2), (key1607, -2), (key1529, -2), (key1804, -2), (key1804, -2), (key1763, -2)]

theorem rawRowCheck8491 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form0 = rawRow8491 := by decide +kernel

def row8491 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

theorem rowCheck8491 : row8491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8491 := by decide +kernel

theorem rowEval8491 (x : Key → ℝ) : Integer.Sparse.eval row8491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8491, Integer.Sparse.eval_collectBalanced, rawRowCheck8491]

def rawRow8492 : Integer.Sparse Key := [(key1529, 2), (key1763, 2), (key1763, 2), (key1254, 2), (key1804, 2), (key1804, 2), (key1263, 2), (key1263, 2), (key1646, 2), (key1646, 2), (key1835, 2), (key1835, 2), (key1529, -2), (key1529, -2), (key1763, -2), (key1254, -2), (key1254, -2), (key1607, -2), (key1607, -2), (key1804, -2), (key1804, -2), (key1263, -2), (key1646, -2), (key1646, -2)]

theorem rawRowCheck8492 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form0 = rawRow8492 := by decide +kernel

def row8492 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

theorem rowCheck8492 : row8492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8492 := by decide +kernel

theorem rowEval8492 (x : Key → ℝ) : Integer.Sparse.eval row8492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8492, Integer.Sparse.eval_collectBalanced, rawRowCheck8492]

def rawRow8493 : Integer.Sparse Key := [(key1763, 2), (key1529, 2), (key1763, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1646, 2), (key1835, 2), (key1263, 2), (key1835, 2), (key1263, 2), (key1646, 2), (key1529, -2), (key1763, -2), (key1529, -2), (key1607, -2), (key1804, -2), (key1254, -2), (key1804, -2), (key1254, -2), (key1607, -2), (key1646, -2), (key1263, -2), (key1646, -2)]

theorem rawRowCheck8493 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form0 = rawRow8493 := by decide +kernel

def row8493 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

theorem rowCheck8493 : row8493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8493 := by decide +kernel

theorem rowEval8493 (x : Key → ℝ) : Integer.Sparse.eval row8493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8493, Integer.Sparse.eval_collectBalanced, rawRowCheck8493]

def rawRow8494 : Integer.Sparse Key := [(key1763, 2), (key1763, 2), (key1529, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1835, 2), (key1646, 2), (key1835, 2), (key1263, 2), (key1646, 2), (key1263, 2), (key1763, -2), (key1529, -2), (key1529, -2), (key1804, -2), (key1607, -2), (key1804, -2), (key1254, -2), (key1607, -2), (key1254, -2), (key1646, -2), (key1646, -2), (key1263, -2)]

theorem rawRowCheck8494 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form0 = rawRow8494 := by decide +kernel

def row8494 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

theorem rowCheck8494 : row8494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8494 := by decide +kernel

theorem rowEval8494 (x : Key → ℝ) : Integer.Sparse.eval row8494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8494, Integer.Sparse.eval_collectBalanced, rawRowCheck8494]

def rawRow8495 : Integer.Sparse Key := [(key1646, 2), (key1804, 2), (key1835, 2), (key1263, 2), (key1763, 2), (key1835, 2), (key1254, 2), (key1263, 2), (key1529, 2), (key1646, 2), (key1763, 2), (key1804, 2), (key1607, -2), (key1646, -2), (key1804, -2), (key1254, -2), (key1263, -2), (key1529, -2), (key1646, -2), (key1763, -2), (key1804, -2), (key1254, -2), (key1529, -2), (key1607, -2)]

theorem rawRowCheck8495 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form0 = rawRow8495 := by decide +kernel

def row8495 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

theorem rowCheck8495 : row8495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8495 := by decide +kernel

theorem rowEval8495 (x : Key → ℝ) : Integer.Sparse.eval row8495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8495, Integer.Sparse.eval_collectBalanced, rawRowCheck8495]

def rawRow8496 : Integer.Sparse Key := [(key1646, 2), (key1835, 2), (key1804, 2), (key1263, 2), (key1835, 2), (key1763, 2), (key1263, 2), (key1254, 2), (key1646, 2), (key1529, 2), (key1804, 2), (key1763, 2), (key1646, -2), (key1607, -2), (key1804, -2), (key1263, -2), (key1254, -2), (key1646, -2), (key1529, -2), (key1804, -2), (key1763, -2), (key1254, -2), (key1607, -2), (key1529, -2)]

theorem rawRowCheck8496 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form0 = rawRow8496 := by decide +kernel

def row8496 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

theorem rowCheck8496 : row8496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8496 := by decide +kernel

theorem rowEval8496 (x : Key → ℝ) : Integer.Sparse.eval row8496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8496, Integer.Sparse.eval_collectBalanced, rawRowCheck8496]

def rawRow8497 : Integer.Sparse Key := [(key1804, 2), (key1646, 2), (key1835, 2), (key1763, 2), (key1263, 2), (key1835, 2), (key1529, 2), (key1763, 2), (key1254, 2), (key1804, 2), (key1263, 2), (key1646, 2), (key1607, -2), (key1804, -2), (key1646, -2), (key1529, -2), (key1763, -2), (key1254, -2), (key1804, -2), (key1263, -2), (key1646, -2), (key1529, -2), (key1254, -2), (key1607, -2)]

theorem rawRowCheck8497 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form0 = rawRow8497 := by decide +kernel

def row8497 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

theorem rowCheck8497 : row8497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8497 := by decide +kernel

theorem rowEval8497 (x : Key → ℝ) : Integer.Sparse.eval row8497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8497, Integer.Sparse.eval_collectBalanced, rawRowCheck8497]

def rawRow8498 : Integer.Sparse Key := [(key1804, 2), (key1835, 2), (key1646, 2), (key1763, 2), (key1835, 2), (key1263, 2), (key1763, 2), (key1529, 2), (key1804, 2), (key1254, 2), (key1646, 2), (key1263, 2), (key1804, -2), (key1607, -2), (key1646, -2), (key1763, -2), (key1529, -2), (key1804, -2), (key1254, -2), (key1646, -2), (key1263, -2), (key1529, -2), (key1607, -2), (key1254, -2)]

theorem rawRowCheck8498 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form0 = rawRow8498 := by decide +kernel

def row8498 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

theorem rowCheck8498 : row8498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8498 := by decide +kernel

theorem rowEval8498 (x : Key → ℝ) : Integer.Sparse.eval row8498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8498, Integer.Sparse.eval_collectBalanced, rawRowCheck8498]

def rawRow8499 : Integer.Sparse Key := [(key1835, 2), (key1646, 2), (key1804, 2), (key1835, 2), (key1263, 2), (key1763, 2), (key1646, 2), (key1804, 2), (key1263, 2), (key1763, 2), (key1254, 2), (key1529, 2), (key1646, -2), (key1804, -2), (key1607, -2), (key1646, -2), (key1804, -2), (key1263, -2), (key1763, -2), (key1254, -2), (key1529, -2), (key1607, -2), (key1254, -2), (key1529, -2)]

theorem rawRowCheck8499 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form0 = rawRow8499 := by decide +kernel

def row8499 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

theorem rowCheck8499 : row8499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8499 := by decide +kernel

theorem rowEval8499 (x : Key → ℝ) : Integer.Sparse.eval row8499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8499, Integer.Sparse.eval_collectBalanced, rawRowCheck8499]

def rawRow8500 : Integer.Sparse Key := [(key1835, 2), (key1804, 2), (key1646, 2), (key1835, 2), (key1763, 2), (key1263, 2), (key1804, 2), (key1646, 2), (key1763, 2), (key1263, 2), (key1529, 2), (key1254, 2), (key1804, -2), (key1646, -2), (key1607, -2), (key1804, -2), (key1646, -2), (key1763, -2), (key1263, -2), (key1529, -2), (key1254, -2), (key1607, -2), (key1529, -2), (key1254, -2)]

theorem rawRowCheck8500 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form0 = rawRow8500 := by decide +kernel

def row8500 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

theorem rowCheck8500 : row8500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8500 := by decide +kernel

theorem rowEval8500 (x : Key → ℝ) : Integer.Sparse.eval row8500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8500, Integer.Sparse.eval_collectBalanced, rawRowCheck8500]

def rawRow8501 : Integer.Sparse Key := [(key41, -24), (key205, 6), (key425, 6), (key425, 6), (key425, 6)]

theorem rawRowCheck8501 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow8501 := by decide +kernel

def row8501 : Integer.Sparse Key := [(key41, -24), (key205, 6), (key425, 18)]

theorem rowCheck8501 : row8501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8501 := by decide +kernel

theorem rowEval8501 (x : Key → ℝ) : Integer.Sparse.eval row8501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8501, Integer.Sparse.eval_collectBalanced, rawRowCheck8501]

def rawRow8502 : Integer.Sparse Key := [(key41, -24), (key425, 6), (key205, 6), (key425, 6), (key425, 6)]

theorem rawRowCheck8502 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form1 = rawRow8502 := by decide +kernel

def row8502 : Integer.Sparse Key := [(key41, -24), (key205, 6), (key425, 18)]

theorem rowCheck8502 : row8502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8502 := by decide +kernel

theorem rowEval8502 (x : Key → ℝ) : Integer.Sparse.eval row8502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8502, Integer.Sparse.eval_collectBalanced, rawRowCheck8502]

def rawRow8503 : Integer.Sparse Key := [(key41, -24), (key425, 6), (key425, 6), (key205, 6), (key425, 6)]

theorem rawRowCheck8503 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form1 = rawRow8503 := by decide +kernel

def row8503 : Integer.Sparse Key := [(key41, -24), (key205, 6), (key425, 18)]

theorem rowCheck8503 : row8503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8503 := by decide +kernel

theorem rowEval8503 (x : Key → ℝ) : Integer.Sparse.eval row8503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8503, Integer.Sparse.eval_collectBalanced, rawRowCheck8503]

def rawRow8504 : Integer.Sparse Key := [(key41, -24), (key425, 6), (key425, 6), (key425, 6), (key205, 6)]

theorem rawRowCheck8504 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form1 = rawRow8504 := by decide +kernel

def row8504 : Integer.Sparse Key := [(key41, -24), (key205, 6), (key425, 18)]

theorem rowCheck8504 : row8504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8504 := by decide +kernel

theorem rowEval8504 (x : Key → ℝ) : Integer.Sparse.eval row8504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8504, Integer.Sparse.eval_collectBalanced, rawRowCheck8504]

def rawRow8505 : Integer.Sparse Key := [(key98, -24), (key16, 6), (key374, 6), (key425, 6), (key425, 6)]

theorem rawRowCheck8505 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form1 = rawRow8505 := by decide +kernel

def row8505 : Integer.Sparse Key := [(key16, 6), (key98, -24), (key374, 6), (key425, 12)]

theorem rowCheck8505 : row8505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8505 := by decide +kernel

theorem rowEval8505 (x : Key → ℝ) : Integer.Sparse.eval row8505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8505, Integer.Sparse.eval_collectBalanced, rawRowCheck8505]

def rawRow8506 : Integer.Sparse Key := [(key98, -24), (key16, 6), (key425, 6), (key374, 6), (key425, 6)]

theorem rawRowCheck8506 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form1 = rawRow8506 := by decide +kernel

def row8506 : Integer.Sparse Key := [(key16, 6), (key98, -24), (key374, 6), (key425, 12)]

theorem rowCheck8506 : row8506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8506 := by decide +kernel

theorem rowEval8506 (x : Key → ℝ) : Integer.Sparse.eval row8506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8506, Integer.Sparse.eval_collectBalanced, rawRowCheck8506]

def rawRow8507 : Integer.Sparse Key := [(key98, -24), (key16, 6), (key425, 6), (key425, 6), (key374, 6)]

theorem rawRowCheck8507 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form1 = rawRow8507 := by decide +kernel

def row8507 : Integer.Sparse Key := [(key16, 6), (key98, -24), (key374, 6), (key425, 12)]

theorem rowCheck8507 : row8507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8507 := by decide +kernel

theorem rowEval8507 (x : Key → ℝ) : Integer.Sparse.eval row8507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8507, Integer.Sparse.eval_collectBalanced, rawRowCheck8507]

def rawRow8508 : Integer.Sparse Key := [(key98, -24), (key41, 6), (key205, 6), (key425, 6), (key425, 6)]

theorem rawRowCheck8508 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form1 = rawRow8508 := by decide +kernel

def row8508 : Integer.Sparse Key := [(key41, 6), (key98, -24), (key205, 6), (key425, 12)]

theorem rowCheck8508 : row8508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8508 := by decide +kernel

theorem rowEval8508 (x : Key → ℝ) : Integer.Sparse.eval row8508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8508, Integer.Sparse.eval_collectBalanced, rawRowCheck8508]

def rawRow8509 : Integer.Sparse Key := [(key98, -24), (key41, 6), (key425, 6), (key205, 6), (key425, 6)]

theorem rawRowCheck8509 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form1 = rawRow8509 := by decide +kernel

def row8509 : Integer.Sparse Key := [(key41, 6), (key98, -24), (key205, 6), (key425, 12)]

theorem rowCheck8509 : row8509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8509 := by decide +kernel

theorem rowEval8509 (x : Key → ℝ) : Integer.Sparse.eval row8509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8509, Integer.Sparse.eval_collectBalanced, rawRowCheck8509]

def rawRow8510 : Integer.Sparse Key := [(key98, -24), (key41, 6), (key425, 6), (key425, 6), (key205, 6)]

theorem rawRowCheck8510 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form1 = rawRow8510 := by decide +kernel

def row8510 : Integer.Sparse Key := [(key41, 6), (key98, -24), (key205, 6), (key425, 12)]

theorem rowCheck8510 : row8510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8510 := by decide +kernel

theorem rowEval8510 (x : Key → ℝ) : Integer.Sparse.eval row8510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8510, Integer.Sparse.eval_collectBalanced, rawRowCheck8510]

def rawRow8511 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key16, 6), (key374, 6), (key425, 6)]

theorem rawRowCheck8511 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form1 = rawRow8511 := by decide +kernel

def row8511 : Integer.Sparse Key := [(key16, 6), (key98, -18), (key374, 6), (key425, 6)]

theorem rowCheck8511 : row8511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8511 := by decide +kernel

theorem rowEval8511 (x : Key → ℝ) : Integer.Sparse.eval row8511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8511, Integer.Sparse.eval_collectBalanced, rawRowCheck8511]

def rawRow8512 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key16, 6), (key425, 6), (key374, 6)]

theorem rawRowCheck8512 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form1 = rawRow8512 := by decide +kernel

def row8512 : Integer.Sparse Key := [(key16, 6), (key98, -18), (key374, 6), (key425, 6)]

theorem rowCheck8512 : row8512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8512 := by decide +kernel

theorem rowEval8512 (x : Key → ℝ) : Integer.Sparse.eval row8512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8512, Integer.Sparse.eval_collectBalanced, rawRowCheck8512]

def rawRow8513 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key41, 6), (key205, 6), (key425, 6)]

theorem rawRowCheck8513 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form1 = rawRow8513 := by decide +kernel

def row8513 : Integer.Sparse Key := [(key41, 6), (key98, -18), (key205, 6), (key425, 6)]

theorem rowCheck8513 : row8513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8513 := by decide +kernel

theorem rowEval8513 (x : Key → ℝ) : Integer.Sparse.eval row8513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8513, Integer.Sparse.eval_collectBalanced, rawRowCheck8513]

def rawRow8514 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key41, 6), (key425, 6), (key205, 6)]

theorem rawRowCheck8514 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form1 = rawRow8514 := by decide +kernel

def row8514 : Integer.Sparse Key := [(key41, 6), (key98, -18), (key205, 6), (key425, 6)]

theorem rowCheck8514 : row8514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8514 := by decide +kernel

theorem rowEval8514 (x : Key → ℝ) : Integer.Sparse.eval row8514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8514, Integer.Sparse.eval_collectBalanced, rawRowCheck8514]

def rawRow8515 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key98, 6), (key16, 6), (key374, 6)]

theorem rawRowCheck8515 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form1 = rawRow8515 := by decide +kernel

def row8515 : Integer.Sparse Key := [(key16, 6), (key98, -12), (key374, 6)]

theorem rowCheck8515 : row8515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8515 := by decide +kernel

theorem rowEval8515 (x : Key → ℝ) : Integer.Sparse.eval row8515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8515, Integer.Sparse.eval_collectBalanced, rawRowCheck8515]

def rawRow8516 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key98, 6), (key41, 6), (key205, 6)]

theorem rawRowCheck8516 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form1 = rawRow8516 := by decide +kernel

def row8516 : Integer.Sparse Key := [(key41, 6), (key98, -12), (key205, 6)]

theorem rowCheck8516 : row8516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8516 := by decide +kernel

theorem rowEval8516 (x : Key → ℝ) : Integer.Sparse.eval row8516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8516, Integer.Sparse.eval_collectBalanced, rawRowCheck8516]

def rawRow8517 : Integer.Sparse Key := [(key45, -6), (key45, -6), (key45, -6), (key70, -6), (key20, 2), (key20, 2), (key20, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key133, 2), (key133, 2), (key133, 2)]

theorem rawRowCheck8517 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow8517 := by decide +kernel

def row8517 : Integer.Sparse Key := [(key20, 6), (key45, -18), (key70, -6), (key102, 12), (key133, 6)]

theorem rowCheck8517 : row8517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8517 := by decide +kernel

theorem rowEval8517 (x : Key → ℝ) : Integer.Sparse.eval row8517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8517, Integer.Sparse.eval_collectBalanced, rawRowCheck8517]

def rawRow8518 : Integer.Sparse Key := [(key45, -6), (key45, -6), (key70, -6), (key45, -6), (key102, 2), (key102, 2), (key133, 2), (key20, 2), (key20, 2), (key102, 2), (key102, 2), (key133, 2), (key133, 2), (key20, 2), (key102, 2), (key102, 2)]

theorem rawRowCheck8518 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form2 = rawRow8518 := by decide +kernel

def row8518 : Integer.Sparse Key := [(key20, 6), (key45, -18), (key70, -6), (key102, 12), (key133, 6)]

theorem rowCheck8518 : row8518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8518 := by decide +kernel

theorem rowEval8518 (x : Key → ℝ) : Integer.Sparse.eval row8518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8518, Integer.Sparse.eval_collectBalanced, rawRowCheck8518]

def rawRow8519 : Integer.Sparse Key := [(key45, -6), (key70, -6), (key45, -6), (key45, -6), (key102, 2), (key133, 2), (key102, 2), (key102, 2), (key133, 2), (key20, 2), (key133, 2), (key20, 2), (key102, 2), (key102, 2), (key20, 2), (key102, 2)]

theorem rawRowCheck8519 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form2 = rawRow8519 := by decide +kernel

def row8519 : Integer.Sparse Key := [(key20, 6), (key45, -18), (key70, -6), (key102, 12), (key133, 6)]

theorem rowCheck8519 : row8519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8519 := by decide +kernel

theorem rowEval8519 (x : Key → ℝ) : Integer.Sparse.eval row8519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8519, Integer.Sparse.eval_collectBalanced, rawRowCheck8519]

def rawRow8520 : Integer.Sparse Key := [(key70, -6), (key45, -6), (key45, -6), (key45, -6), (key133, 2), (key102, 2), (key102, 2), (key133, 2), (key102, 2), (key133, 2), (key20, 2), (key102, 2), (key20, 2), (key102, 2), (key102, 2), (key20, 2)]

theorem rawRowCheck8520 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form2 = rawRow8520 := by decide +kernel

def row8520 : Integer.Sparse Key := [(key20, 6), (key45, -18), (key70, -6), (key102, 12), (key133, 6)]

theorem rowCheck8520 : row8520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8520 := by decide +kernel

theorem rowEval8520 (x : Key → ℝ) : Integer.Sparse.eval row8520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8520, Integer.Sparse.eval_collectBalanced, rawRowCheck8520]

def rawRow8521 : Integer.Sparse Key := [(key102, -6), (key102, -6), (key111, -6), (key133, -6), (key20, 2), (key20, 2), (key31, 2), (key45, 2), (key45, 2), (key102, 2), (key102, 2), (key111, 2), (key111, 2), (key70, 2), (key133, 2), (key133, 2)]

theorem rawRowCheck8521 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form2 = rawRow8521 := by decide +kernel

def row8521 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

theorem rowCheck8521 : row8521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8521 := by decide +kernel

theorem rowEval8521 (x : Key → ℝ) : Integer.Sparse.eval row8521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8521, Integer.Sparse.eval_collectBalanced, rawRowCheck8521]

def rawRow8522 : Integer.Sparse Key := [(key102, -6), (key111, -6), (key102, -6), (key133, -6), (key20, 2), (key31, 2), (key20, 2), (key102, 2), (key111, 2), (key45, 2), (key111, 2), (key45, 2), (key102, 2), (key133, 2), (key70, 2), (key133, 2)]

theorem rawRowCheck8522 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form2 = rawRow8522 := by decide +kernel

def row8522 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

theorem rowCheck8522 : row8522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8522 := by decide +kernel

theorem rowEval8522 (x : Key → ℝ) : Integer.Sparse.eval row8522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8522, Integer.Sparse.eval_collectBalanced, rawRowCheck8522]

def rawRow8523 : Integer.Sparse Key := [(key111, -6), (key102, -6), (key102, -6), (key133, -6), (key31, 2), (key20, 2), (key20, 2), (key111, 2), (key102, 2), (key111, 2), (key45, 2), (key102, 2), (key45, 2), (key133, 2), (key133, 2), (key70, 2)]

theorem rawRowCheck8523 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form2 = rawRow8523 := by decide +kernel

def row8523 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

theorem rowCheck8523 : row8523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8523 := by decide +kernel

theorem rowEval8523 (x : Key → ℝ) : Integer.Sparse.eval row8523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8523, Integer.Sparse.eval_collectBalanced, rawRowCheck8523]

def rawRow8524 : Integer.Sparse Key := [(key102, -6), (key102, -6), (key133, -6), (key111, -6), (key45, 2), (key45, 2), (key70, 2), (key20, 2), (key20, 2), (key102, 2), (key102, 2), (key133, 2), (key133, 2), (key31, 2), (key111, 2), (key111, 2)]

theorem rawRowCheck8524 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form2 = rawRow8524 := by decide +kernel

def row8524 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

theorem rowCheck8524 : row8524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8524 := by decide +kernel

theorem rowEval8524 (x : Key → ℝ) : Integer.Sparse.eval row8524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8524, Integer.Sparse.eval_collectBalanced, rawRowCheck8524]

def rawRow8525 : Integer.Sparse Key := [(key102, -6), (key133, -6), (key102, -6), (key111, -6), (key45, 2), (key70, 2), (key45, 2), (key102, 2), (key133, 2), (key20, 2), (key133, 2), (key20, 2), (key102, 2), (key111, 2), (key31, 2), (key111, 2)]

theorem rawRowCheck8525 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form2 = rawRow8525 := by decide +kernel

def row8525 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

theorem rowCheck8525 : row8525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8525 := by decide +kernel

theorem rowEval8525 (x : Key → ℝ) : Integer.Sparse.eval row8525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8525, Integer.Sparse.eval_collectBalanced, rawRowCheck8525]

def rawRow8526 : Integer.Sparse Key := [(key133, -6), (key102, -6), (key102, -6), (key111, -6), (key70, 2), (key45, 2), (key45, 2), (key133, 2), (key102, 2), (key133, 2), (key20, 2), (key102, 2), (key20, 2), (key111, 2), (key111, 2), (key31, 2)]

theorem rawRowCheck8526 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form2 = rawRow8526 := by decide +kernel

def row8526 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

theorem rowCheck8526 : row8526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8526 := by decide +kernel

theorem rowEval8526 (x : Key → ℝ) : Integer.Sparse.eval row8526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8526, Integer.Sparse.eval_collectBalanced, rawRowCheck8526]

def rawRow8527 : Integer.Sparse Key := [(key102, -6), (key111, -6), (key133, -6), (key102, -6), (key102, 2), (key111, 2), (key133, 2), (key20, 2), (key31, 2), (key45, 2), (key111, 2), (key70, 2), (key133, 2), (key20, 2), (key45, 2), (key102, 2)]

theorem rawRowCheck8527 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form2 = rawRow8527 := by decide +kernel

def row8527 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

theorem rowCheck8527 : row8527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8527 := by decide +kernel

theorem rowEval8527 (x : Key → ℝ) : Integer.Sparse.eval row8527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8527, Integer.Sparse.eval_collectBalanced, rawRowCheck8527]

def rawRow8528 : Integer.Sparse Key := [(key111, -6), (key102, -6), (key133, -6), (key102, -6), (key111, 2), (key102, 2), (key133, 2), (key31, 2), (key20, 2), (key111, 2), (key45, 2), (key133, 2), (key70, 2), (key20, 2), (key102, 2), (key45, 2)]

theorem rawRowCheck8528 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form2 = rawRow8528 := by decide +kernel

def row8528 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

theorem rowCheck8528 : row8528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8528 := by decide +kernel

theorem rowEval8528 (x : Key → ℝ) : Integer.Sparse.eval row8528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8528, Integer.Sparse.eval_collectBalanced, rawRowCheck8528]

def rawRow8529 : Integer.Sparse Key := [(key102, -6), (key133, -6), (key111, -6), (key102, -6), (key102, 2), (key133, 2), (key111, 2), (key45, 2), (key70, 2), (key20, 2), (key133, 2), (key31, 2), (key111, 2), (key45, 2), (key20, 2), (key102, 2)]

theorem rawRowCheck8529 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form2 = rawRow8529 := by decide +kernel

def row8529 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

theorem rowCheck8529 : row8529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8529 := by decide +kernel

theorem rowEval8529 (x : Key → ℝ) : Integer.Sparse.eval row8529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8529, Integer.Sparse.eval_collectBalanced, rawRowCheck8529]

def rawRow8530 : Integer.Sparse Key := [(key133, -6), (key102, -6), (key111, -6), (key102, -6), (key133, 2), (key102, 2), (key111, 2), (key70, 2), (key45, 2), (key133, 2), (key20, 2), (key111, 2), (key31, 2), (key45, 2), (key102, 2), (key20, 2)]

theorem rawRowCheck8530 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form2 = rawRow8530 := by decide +kernel

def row8530 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

theorem rowCheck8530 : row8530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8530 := by decide +kernel

theorem rowEval8530 (x : Key → ℝ) : Integer.Sparse.eval row8530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8530, Integer.Sparse.eval_collectBalanced, rawRowCheck8530]

def rawRow8531 : Integer.Sparse Key := [(key111, -6), (key133, -6), (key102, -6), (key102, -6), (key111, 2), (key133, 2), (key102, 2), (key111, 2), (key133, 2), (key31, 2), (key70, 2), (key20, 2), (key45, 2), (key102, 2), (key20, 2), (key45, 2)]

theorem rawRowCheck8531 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form2 = rawRow8531 := by decide +kernel

def row8531 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

theorem rowCheck8531 : row8531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8531 := by decide +kernel

theorem rowEval8531 (x : Key → ℝ) : Integer.Sparse.eval row8531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8531, Integer.Sparse.eval_collectBalanced, rawRowCheck8531]

def rawRow8532 : Integer.Sparse Key := [(key133, -6), (key111, -6), (key102, -6), (key102, -6), (key133, 2), (key111, 2), (key102, 2), (key133, 2), (key111, 2), (key70, 2), (key31, 2), (key45, 2), (key20, 2), (key102, 2), (key45, 2), (key20, 2)]

theorem rawRowCheck8532 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form2 = rawRow8532 := by decide +kernel

def row8532 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

theorem rowCheck8532 : row8532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8532 := by decide +kernel

theorem rowEval8532 (x : Key → ℝ) : Integer.Sparse.eval row8532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8532, Integer.Sparse.eval_collectBalanced, rawRowCheck8532]

def rawRow8533 : Integer.Sparse Key := [(key1287, -6), (key1564, -6), (key1564, -6), (key1564, -6), (key1307, 2), (key1307, 2), (key1307, 2), (key1415, 2), (key1415, 2), (key1415, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2)]

theorem rawRowCheck8533 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow8533 := by decide +kernel

def row8533 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1415, 6), (key1564, -18), (key1613, 12)]

theorem rowCheck8533 : row8533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8533 := by decide +kernel

theorem rowEval8533 (x : Key → ℝ) : Integer.Sparse.eval row8533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8533, Integer.Sparse.eval_collectBalanced, rawRowCheck8533]

def rawRow8534 : Integer.Sparse Key := [(key1564, -6), (key1287, -6), (key1564, -6), (key1564, -6), (key1415, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1307, 2), (key1415, 2), (key1415, 2), (key1613, 2), (key1613, 2)]

theorem rawRowCheck8534 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form3 = rawRow8534 := by decide +kernel

def row8534 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1415, 6), (key1564, -18), (key1613, 12)]

theorem rowCheck8534 : row8534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8534 := by decide +kernel

theorem rowEval8534 (x : Key → ℝ) : Integer.Sparse.eval row8534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8534, Integer.Sparse.eval_collectBalanced, rawRowCheck8534]

def rawRow8535 : Integer.Sparse Key := [(key1564, -6), (key1564, -6), (key1287, -6), (key1564, -6), (key1613, 2), (key1415, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1307, 2), (key1415, 2)]

theorem rawRowCheck8535 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form3 = rawRow8535 := by decide +kernel

def row8535 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1415, 6), (key1564, -18), (key1613, 12)]

theorem rowCheck8535 : row8535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8535 := by decide +kernel

theorem rowEval8535 (x : Key → ℝ) : Integer.Sparse.eval row8535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8535, Integer.Sparse.eval_collectBalanced, rawRowCheck8535]

def rawRow8536 : Integer.Sparse Key := [(key1564, -6), (key1564, -6), (key1564, -6), (key1287, -6), (key1613, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1307, 2), (key1415, 2), (key1307, 2)]

theorem rawRowCheck8536 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form3 = rawRow8536 := by decide +kernel

def row8536 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1415, 6), (key1564, -18), (key1613, 12)]

theorem rowCheck8536 : row8536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8536 := by decide +kernel

theorem rowEval8536 (x : Key → ℝ) : Integer.Sparse.eval row8536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8536, Integer.Sparse.eval_collectBalanced, rawRowCheck8536]

def rawRow8537 : Integer.Sparse Key := [(key1307, -6), (key1537, -6), (key1613, -6), (key1613, -6), (key1287, 2), (key1307, 2), (key1307, 2), (key1382, 2), (key1415, 2), (key1415, 2), (key1537, 2), (key1537, 2), (key1564, 2), (key1564, 2), (key1613, 2), (key1613, 2)]

theorem rawRowCheck8537 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form3 = rawRow8537 := by decide +kernel

def row8537 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

theorem rowCheck8537 : row8537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8537 := by decide +kernel

theorem rowEval8537 (x : Key → ℝ) : Integer.Sparse.eval row8537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8537, Integer.Sparse.eval_collectBalanced, rawRowCheck8537]

def rawRow8538 : Integer.Sparse Key := [(key1307, -6), (key1613, -6), (key1537, -6), (key1613, -6), (key1307, 2), (key1287, 2), (key1307, 2), (key1415, 2), (key1382, 2), (key1415, 2), (key1564, 2), (key1613, 2), (key1537, 2), (key1613, 2), (key1537, 2), (key1564, 2)]

theorem rawRowCheck8538 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form3 = rawRow8538 := by decide +kernel

def row8538 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

theorem rowCheck8538 : row8538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8538 := by decide +kernel

theorem rowEval8538 (x : Key → ℝ) : Integer.Sparse.eval row8538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8538, Integer.Sparse.eval_collectBalanced, rawRowCheck8538]

def rawRow8539 : Integer.Sparse Key := [(key1307, -6), (key1613, -6), (key1613, -6), (key1537, -6), (key1307, 2), (key1307, 2), (key1287, 2), (key1415, 2), (key1415, 2), (key1382, 2), (key1613, 2), (key1564, 2), (key1613, 2), (key1537, 2), (key1564, 2), (key1537, 2)]

theorem rawRowCheck8539 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form3 = rawRow8539 := by decide +kernel

def row8539 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

theorem rowCheck8539 : row8539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8539 := by decide +kernel

theorem rowEval8539 (x : Key → ℝ) : Integer.Sparse.eval row8539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8539, Integer.Sparse.eval_collectBalanced, rawRowCheck8539]

def rawRow8540 : Integer.Sparse Key := [(key1537, -6), (key1307, -6), (key1613, -6), (key1613, -6), (key1382, 2), (key1537, 2), (key1537, 2), (key1287, 2), (key1564, 2), (key1564, 2), (key1307, 2), (key1307, 2), (key1415, 2), (key1415, 2), (key1613, 2), (key1613, 2)]

theorem rawRowCheck8540 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form3 = rawRow8540 := by decide +kernel

def row8540 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

theorem rowCheck8540 : row8540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8540 := by decide +kernel

theorem rowEval8540 (x : Key → ℝ) : Integer.Sparse.eval row8540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8540, Integer.Sparse.eval_collectBalanced, rawRowCheck8540]

def rawRow8541 : Integer.Sparse Key := [(key1537, -6), (key1613, -6), (key1307, -6), (key1613, -6), (key1537, 2), (key1382, 2), (key1537, 2), (key1564, 2), (key1287, 2), (key1564, 2), (key1415, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1307, 2), (key1415, 2)]

theorem rawRowCheck8541 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form3 = rawRow8541 := by decide +kernel

def row8541 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

theorem rowCheck8541 : row8541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8541 := by decide +kernel

theorem rowEval8541 (x : Key → ℝ) : Integer.Sparse.eval row8541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8541, Integer.Sparse.eval_collectBalanced, rawRowCheck8541]

def rawRow8542 : Integer.Sparse Key := [(key1537, -6), (key1613, -6), (key1613, -6), (key1307, -6), (key1537, 2), (key1537, 2), (key1382, 2), (key1564, 2), (key1564, 2), (key1287, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1307, 2), (key1415, 2), (key1307, 2)]

theorem rawRowCheck8542 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form3 = rawRow8542 := by decide +kernel

def row8542 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

theorem rowCheck8542 : row8542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8542 := by decide +kernel

theorem rowEval8542 (x : Key → ℝ) : Integer.Sparse.eval row8542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8542, Integer.Sparse.eval_collectBalanced, rawRowCheck8542]

def rawRow8543 : Integer.Sparse Key := [(key1613, -6), (key1307, -6), (key1537, -6), (key1613, -6), (key1415, 2), (key1564, 2), (key1613, 2), (key1307, 2), (key1537, 2), (key1613, 2), (key1287, 2), (key1307, 2), (key1382, 2), (key1415, 2), (key1537, 2), (key1564, 2)]

theorem rawRowCheck8543 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form3 = rawRow8543 := by decide +kernel

def row8543 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

theorem rowCheck8543 : row8543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8543 := by decide +kernel

theorem rowEval8543 (x : Key → ℝ) : Integer.Sparse.eval row8543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8543, Integer.Sparse.eval_collectBalanced, rawRowCheck8543]

def rawRow8544 : Integer.Sparse Key := [(key1613, -6), (key1307, -6), (key1613, -6), (key1537, -6), (key1415, 2), (key1613, 2), (key1564, 2), (key1307, 2), (key1613, 2), (key1537, 2), (key1307, 2), (key1287, 2), (key1415, 2), (key1382, 2), (key1564, 2), (key1537, 2)]

theorem rawRowCheck8544 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form3 = rawRow8544 := by decide +kernel

def row8544 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

theorem rowCheck8544 : row8544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8544 := by decide +kernel

theorem rowEval8544 (x : Key → ℝ) : Integer.Sparse.eval row8544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8544, Integer.Sparse.eval_collectBalanced, rawRowCheck8544]

def rawRow8545 : Integer.Sparse Key := [(key1613, -6), (key1537, -6), (key1307, -6), (key1613, -6), (key1564, 2), (key1415, 2), (key1613, 2), (key1537, 2), (key1307, 2), (key1613, 2), (key1382, 2), (key1537, 2), (key1287, 2), (key1564, 2), (key1307, 2), (key1415, 2)]

theorem rawRowCheck8545 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form3 = rawRow8545 := by decide +kernel

def row8545 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

theorem rowCheck8545 : row8545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8545 := by decide +kernel

theorem rowEval8545 (x : Key → ℝ) : Integer.Sparse.eval row8545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8545, Integer.Sparse.eval_collectBalanced, rawRowCheck8545]

def rawRow8546 : Integer.Sparse Key := [(key1613, -6), (key1537, -6), (key1613, -6), (key1307, -6), (key1564, 2), (key1613, 2), (key1415, 2), (key1537, 2), (key1613, 2), (key1307, 2), (key1537, 2), (key1382, 2), (key1564, 2), (key1287, 2), (key1415, 2), (key1307, 2)]

theorem rawRowCheck8546 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form3 = rawRow8546 := by decide +kernel

def row8546 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

theorem rowCheck8546 : row8546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8546 := by decide +kernel

theorem rowEval8546 (x : Key → ℝ) : Integer.Sparse.eval row8546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8546, Integer.Sparse.eval_collectBalanced, rawRowCheck8546]

def rawRow8547 : Integer.Sparse Key := [(key1613, -6), (key1613, -6), (key1307, -6), (key1537, -6), (key1613, 2), (key1415, 2), (key1564, 2), (key1613, 2), (key1307, 2), (key1537, 2), (key1415, 2), (key1564, 2), (key1307, 2), (key1537, 2), (key1287, 2), (key1382, 2)]

theorem rawRowCheck8547 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form3 = rawRow8547 := by decide +kernel

def row8547 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

theorem rowCheck8547 : row8547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8547 := by decide +kernel

theorem rowEval8547 (x : Key → ℝ) : Integer.Sparse.eval row8547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8547, Integer.Sparse.eval_collectBalanced, rawRowCheck8547]

def rawRow8548 : Integer.Sparse Key := [(key1613, -6), (key1613, -6), (key1537, -6), (key1307, -6), (key1613, 2), (key1564, 2), (key1415, 2), (key1613, 2), (key1537, 2), (key1307, 2), (key1564, 2), (key1415, 2), (key1537, 2), (key1307, 2), (key1382, 2), (key1287, 2)]

theorem rawRowCheck8548 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form3 = rawRow8548 := by decide +kernel

def row8548 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

theorem rowCheck8548 : row8548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8548 := by decide +kernel

theorem rowEval8548 (x : Key → ℝ) : Integer.Sparse.eval row8548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8548, Integer.Sparse.eval_collectBalanced, rawRowCheck8548]

def rawRow8549 : Integer.Sparse Key := [(key1525, -6), (key1525, -6), (key1525, -6), (key1892, -6), (key1250, 2), (key1250, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1914, 2), (key1914, 2)]

theorem rawRowCheck8549 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow8549 := by decide +kernel

def row8549 : Integer.Sparse Key := [(key1250, 6), (key1525, -18), (key1603, 12), (key1892, -6), (key1914, 6)]

theorem rowCheck8549 : row8549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8549 := by decide +kernel

theorem rowEval8549 (x : Key → ℝ) : Integer.Sparse.eval row8549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8549, Integer.Sparse.eval_collectBalanced, rawRowCheck8549]

def rawRow8550 : Integer.Sparse Key := [(key1525, -6), (key1525, -6), (key1892, -6), (key1525, -6), (key1603, 2), (key1603, 2), (key1914, 2), (key1250, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1914, 2), (key1250, 2), (key1603, 2), (key1603, 2)]

theorem rawRowCheck8550 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form4 = rawRow8550 := by decide +kernel

def row8550 : Integer.Sparse Key := [(key1250, 6), (key1525, -18), (key1603, 12), (key1892, -6), (key1914, 6)]

theorem rowCheck8550 : row8550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8550 := by decide +kernel

theorem rowEval8550 (x : Key → ℝ) : Integer.Sparse.eval row8550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8550, Integer.Sparse.eval_collectBalanced, rawRowCheck8550]

def rawRow8551 : Integer.Sparse Key := [(key1525, -6), (key1892, -6), (key1525, -6), (key1525, -6), (key1603, 2), (key1914, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1250, 2), (key1914, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1250, 2), (key1603, 2)]

theorem rawRowCheck8551 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form4 = rawRow8551 := by decide +kernel

def row8551 : Integer.Sparse Key := [(key1250, 6), (key1525, -18), (key1603, 12), (key1892, -6), (key1914, 6)]

theorem rowCheck8551 : row8551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8551 := by decide +kernel

theorem rowEval8551 (x : Key → ℝ) : Integer.Sparse.eval row8551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8551, Integer.Sparse.eval_collectBalanced, rawRowCheck8551]

def rawRow8552 : Integer.Sparse Key := [(key1892, -6), (key1525, -6), (key1525, -6), (key1525, -6), (key1914, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1603, 2), (key1914, 2), (key1250, 2), (key1603, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1250, 2)]

theorem rawRowCheck8552 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form4 = rawRow8552 := by decide +kernel

def row8552 : Integer.Sparse Key := [(key1250, 6), (key1525, -18), (key1603, 12), (key1892, -6), (key1914, 6)]

theorem rowCheck8552 : row8552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8552 := by decide +kernel

theorem rowEval8552 (x : Key → ℝ) : Integer.Sparse.eval row8552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8552, Integer.Sparse.eval_collectBalanced, rawRowCheck8552]

def rawRow8553 : Integer.Sparse Key := [(key1603, -6), (key1603, -6), (key1677, -6), (key1914, -6), (key1250, 2), (key1250, 2), (key1269, 2), (key1525, 2), (key1525, 2), (key1603, 2), (key1603, 2), (key1677, 2), (key1677, 2), (key1892, 2), (key1914, 2), (key1914, 2)]

theorem rawRowCheck8553 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form4 = rawRow8553 := by decide +kernel

def row8553 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

theorem rowCheck8553 : row8553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8553 := by decide +kernel

theorem rowEval8553 (x : Key → ℝ) : Integer.Sparse.eval row8553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8553, Integer.Sparse.eval_collectBalanced, rawRowCheck8553]

def rawRow8554 : Integer.Sparse Key := [(key1603, -6), (key1677, -6), (key1603, -6), (key1914, -6), (key1250, 2), (key1269, 2), (key1250, 2), (key1603, 2), (key1677, 2), (key1525, 2), (key1677, 2), (key1525, 2), (key1603, 2), (key1914, 2), (key1892, 2), (key1914, 2)]

theorem rawRowCheck8554 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form4 = rawRow8554 := by decide +kernel

def row8554 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

theorem rowCheck8554 : row8554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8554 := by decide +kernel

theorem rowEval8554 (x : Key → ℝ) : Integer.Sparse.eval row8554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8554, Integer.Sparse.eval_collectBalanced, rawRowCheck8554]

def rawRow8555 : Integer.Sparse Key := [(key1677, -6), (key1603, -6), (key1603, -6), (key1914, -6), (key1269, 2), (key1250, 2), (key1250, 2), (key1677, 2), (key1603, 2), (key1677, 2), (key1525, 2), (key1603, 2), (key1525, 2), (key1914, 2), (key1914, 2), (key1892, 2)]

theorem rawRowCheck8555 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form4 = rawRow8555 := by decide +kernel

def row8555 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

theorem rowCheck8555 : row8555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8555 := by decide +kernel

theorem rowEval8555 (x : Key → ℝ) : Integer.Sparse.eval row8555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8555, Integer.Sparse.eval_collectBalanced, rawRowCheck8555]

def rawRow8556 : Integer.Sparse Key := [(key1603, -6), (key1603, -6), (key1914, -6), (key1677, -6), (key1525, 2), (key1525, 2), (key1892, 2), (key1250, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1914, 2), (key1269, 2), (key1677, 2), (key1677, 2)]

theorem rawRowCheck8556 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form4 = rawRow8556 := by decide +kernel

def row8556 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

theorem rowCheck8556 : row8556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8556 := by decide +kernel

theorem rowEval8556 (x : Key → ℝ) : Integer.Sparse.eval row8556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8556, Integer.Sparse.eval_collectBalanced, rawRowCheck8556]

def rawRow8557 : Integer.Sparse Key := [(key1603, -6), (key1914, -6), (key1603, -6), (key1677, -6), (key1525, 2), (key1892, 2), (key1525, 2), (key1603, 2), (key1914, 2), (key1250, 2), (key1914, 2), (key1250, 2), (key1603, 2), (key1677, 2), (key1269, 2), (key1677, 2)]

theorem rawRowCheck8557 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form4 = rawRow8557 := by decide +kernel

def row8557 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

theorem rowCheck8557 : row8557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8557 := by decide +kernel

theorem rowEval8557 (x : Key → ℝ) : Integer.Sparse.eval row8557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8557, Integer.Sparse.eval_collectBalanced, rawRowCheck8557]

def rawRow8558 : Integer.Sparse Key := [(key1914, -6), (key1603, -6), (key1603, -6), (key1677, -6), (key1892, 2), (key1525, 2), (key1525, 2), (key1914, 2), (key1603, 2), (key1914, 2), (key1250, 2), (key1603, 2), (key1250, 2), (key1677, 2), (key1677, 2), (key1269, 2)]

theorem rawRowCheck8558 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form4 = rawRow8558 := by decide +kernel

def row8558 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

theorem rowCheck8558 : row8558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8558 := by decide +kernel

theorem rowEval8558 (x : Key → ℝ) : Integer.Sparse.eval row8558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8558, Integer.Sparse.eval_collectBalanced, rawRowCheck8558]

def rawRow8559 : Integer.Sparse Key := [(key1603, -6), (key1677, -6), (key1914, -6), (key1603, -6), (key1603, 2), (key1677, 2), (key1914, 2), (key1250, 2), (key1269, 2), (key1525, 2), (key1677, 2), (key1892, 2), (key1914, 2), (key1250, 2), (key1525, 2), (key1603, 2)]

theorem rawRowCheck8559 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form4 = rawRow8559 := by decide +kernel

def row8559 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

theorem rowCheck8559 : row8559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8559 := by decide +kernel

theorem rowEval8559 (x : Key → ℝ) : Integer.Sparse.eval row8559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8559, Integer.Sparse.eval_collectBalanced, rawRowCheck8559]

def rawRow8560 : Integer.Sparse Key := [(key1677, -6), (key1603, -6), (key1914, -6), (key1603, -6), (key1677, 2), (key1603, 2), (key1914, 2), (key1269, 2), (key1250, 2), (key1677, 2), (key1525, 2), (key1914, 2), (key1892, 2), (key1250, 2), (key1603, 2), (key1525, 2)]

theorem rawRowCheck8560 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form4 = rawRow8560 := by decide +kernel

def row8560 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

theorem rowCheck8560 : row8560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8560 := by decide +kernel

theorem rowEval8560 (x : Key → ℝ) : Integer.Sparse.eval row8560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8560, Integer.Sparse.eval_collectBalanced, rawRowCheck8560]

def rawRow8561 : Integer.Sparse Key := [(key1603, -6), (key1914, -6), (key1677, -6), (key1603, -6), (key1603, 2), (key1914, 2), (key1677, 2), (key1525, 2), (key1892, 2), (key1250, 2), (key1914, 2), (key1269, 2), (key1677, 2), (key1525, 2), (key1250, 2), (key1603, 2)]

theorem rawRowCheck8561 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form4 = rawRow8561 := by decide +kernel

def row8561 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

theorem rowCheck8561 : row8561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8561 := by decide +kernel

theorem rowEval8561 (x : Key → ℝ) : Integer.Sparse.eval row8561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8561, Integer.Sparse.eval_collectBalanced, rawRowCheck8561]

def rawRow8562 : Integer.Sparse Key := [(key1914, -6), (key1603, -6), (key1677, -6), (key1603, -6), (key1914, 2), (key1603, 2), (key1677, 2), (key1892, 2), (key1525, 2), (key1914, 2), (key1250, 2), (key1677, 2), (key1269, 2), (key1525, 2), (key1603, 2), (key1250, 2)]

theorem rawRowCheck8562 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form4 = rawRow8562 := by decide +kernel

def row8562 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

theorem rowCheck8562 : row8562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8562 := by decide +kernel

theorem rowEval8562 (x : Key → ℝ) : Integer.Sparse.eval row8562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8562, Integer.Sparse.eval_collectBalanced, rawRowCheck8562]

def rawRow8563 : Integer.Sparse Key := [(key1677, -6), (key1914, -6), (key1603, -6), (key1603, -6), (key1677, 2), (key1914, 2), (key1603, 2), (key1677, 2), (key1914, 2), (key1269, 2), (key1892, 2), (key1250, 2), (key1525, 2), (key1603, 2), (key1250, 2), (key1525, 2)]

theorem rawRowCheck8563 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form4 = rawRow8563 := by decide +kernel

def row8563 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

theorem rowCheck8563 : row8563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8563 := by decide +kernel

theorem rowEval8563 (x : Key → ℝ) : Integer.Sparse.eval row8563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8563, Integer.Sparse.eval_collectBalanced, rawRowCheck8563]

def rawRow8564 : Integer.Sparse Key := [(key1914, -6), (key1677, -6), (key1603, -6), (key1603, -6), (key1914, 2), (key1677, 2), (key1603, 2), (key1914, 2), (key1677, 2), (key1892, 2), (key1269, 2), (key1525, 2), (key1250, 2), (key1603, 2), (key1525, 2), (key1250, 2)]

theorem rawRowCheck8564 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form4 = rawRow8564 := by decide +kernel

def row8564 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

theorem rowCheck8564 : row8564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8564 := by decide +kernel

theorem rowEval8564 (x : Key → ℝ) : Integer.Sparse.eval row8564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8564, Integer.Sparse.eval_collectBalanced, rawRowCheck8564]

def rawRow8565 : Integer.Sparse Key := [(key1289, -2), (key1289, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1566, -2), (key1566, -2), (key1566, -2), (key1566, -2), (key1902, -2), (key1902, -2), (key1902, -2), (key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1)]

theorem rawRowCheck8565 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form5 = rawRow8565 := by decide +kernel

def row8565 : Integer.Sparse Key := [(key1289, -6), (key1309, 6), (key1417, 6), (key1566, -12), (key1615, 6), (key1902, -6), (key1917, 6)]

theorem rowCheck8565 : row8565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8565 := by decide +kernel

theorem rowEval8565 (x : Key → ℝ) : Integer.Sparse.eval row8565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8565, Integer.Sparse.eval_collectBalanced, rawRowCheck8565]

def rawRow8566 : Integer.Sparse Key := [(key1566, -2), (key1566, -2), (key1902, -2), (key1289, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1902, -2), (key1902, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1)]

theorem rawRowCheck8566 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form5 = rawRow8566 := by decide +kernel

def row8566 : Integer.Sparse Key := [(key1289, -6), (key1309, 6), (key1417, 6), (key1566, -12), (key1615, 6), (key1902, -6), (key1917, 6)]

theorem rowCheck8566 : row8566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8566 := by decide +kernel

theorem rowEval8566 (x : Key → ℝ) : Integer.Sparse.eval row8566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8566, Integer.Sparse.eval_collectBalanced, rawRowCheck8566]

def rawRow8567 : Integer.Sparse Key := [(key1566, -2), (key1902, -2), (key1566, -2), (key1566, -2), (key1902, -2), (key1289, -2), (key1902, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1289, -2), (key1566, -2), (key1615, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1615, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1309, 1), (key1615, 1), (key1309, 1), (key1417, 1)]

theorem rawRowCheck8567 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form5 = rawRow8567 := by decide +kernel

def row8567 : Integer.Sparse Key := [(key1289, -6), (key1309, 6), (key1417, 6), (key1566, -12), (key1615, 6), (key1902, -6), (key1917, 6)]

theorem rowCheck8567 : row8567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8567 := by decide +kernel

theorem rowEval8567 (x : Key → ℝ) : Integer.Sparse.eval row8567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8567, Integer.Sparse.eval_collectBalanced, rawRowCheck8567]

def rawRow8568 : Integer.Sparse Key := [(key1902, -2), (key1566, -2), (key1566, -2), (key1902, -2), (key1566, -2), (key1902, -2), (key1289, -2), (key1566, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1289, -2), (key1917, 1), (key1615, 1), (key1917, 1), (key1417, 1), (key1615, 1), (key1417, 1), (key1917, 1), (key1615, 1), (key1917, 1), (key1309, 1), (key1615, 1), (key1309, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1309, 1), (key1615, 1), (key1417, 1), (key1615, 1), (key1309, 1), (key1417, 1), (key1309, 1)]

theorem rawRowCheck8568 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form5 = rawRow8568 := by decide +kernel

def row8568 : Integer.Sparse Key := [(key1289, -6), (key1309, 6), (key1417, 6), (key1566, -12), (key1615, 6), (key1902, -6), (key1917, 6)]

theorem rowCheck8568 : row8568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8568 := by decide +kernel

theorem rowEval8568 (x : Key → ℝ) : Integer.Sparse.eval row8568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8568, Integer.Sparse.eval_collectBalanced, rawRowCheck8568]

def rawRow8569 : Integer.Sparse Key := [(key1309, -2), (key1309, -2), (key1350, -2), (key1539, -2), (key1539, -2), (key1615, -2), (key1615, -2), (key1680, -2), (key1680, -2), (key1895, -2), (key1917, -2), (key1917, -2), (key1289, 1), (key1289, 1), (key1309, 1), (key1309, 1), (key1350, 1), (key1350, 1), (key1384, 1), (key1384, 1), (key1417, 1), (key1417, 1), (key1471, 1), (key1471, 1), (key1539, 1), (key1539, 1), (key1566, 1), (key1566, 1), (key1680, 1), (key1680, 1), (key1895, 1), (key1895, 1), (key1902, 1), (key1902, 1), (key1917, 1), (key1917, 1)]

theorem rawRowCheck8569 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form5 = rawRow8569 := by decide +kernel

def row8569 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

theorem rowCheck8569 : row8569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8569 := by decide +kernel

theorem rowEval8569 (x : Key → ℝ) : Integer.Sparse.eval row8569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8569, Integer.Sparse.eval_collectBalanced, rawRowCheck8569]

def rawRow8570 : Integer.Sparse Key := [(key1309, -2), (key1350, -2), (key1309, -2), (key1615, -2), (key1680, -2), (key1539, -2), (key1680, -2), (key1539, -2), (key1615, -2), (key1917, -2), (key1895, -2), (key1917, -2), (key1309, 1), (key1350, 1), (key1289, 1), (key1350, 1), (key1289, 1), (key1309, 1), (key1417, 1), (key1471, 1), (key1384, 1), (key1471, 1), (key1384, 1), (key1417, 1), (key1566, 1), (key1680, 1), (key1539, 1), (key1680, 1), (key1539, 1), (key1566, 1), (key1902, 1), (key1917, 1), (key1895, 1), (key1917, 1), (key1895, 1), (key1902, 1)]

theorem rawRowCheck8570 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form5 = rawRow8570 := by decide +kernel

def row8570 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

theorem rowCheck8570 : row8570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8570 := by decide +kernel

theorem rowEval8570 (x : Key → ℝ) : Integer.Sparse.eval row8570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8570, Integer.Sparse.eval_collectBalanced, rawRowCheck8570]

def rawRow8571 : Integer.Sparse Key := [(key1350, -2), (key1309, -2), (key1309, -2), (key1680, -2), (key1615, -2), (key1680, -2), (key1539, -2), (key1615, -2), (key1539, -2), (key1917, -2), (key1917, -2), (key1895, -2), (key1350, 1), (key1309, 1), (key1350, 1), (key1289, 1), (key1309, 1), (key1289, 1), (key1471, 1), (key1417, 1), (key1471, 1), (key1384, 1), (key1417, 1), (key1384, 1), (key1680, 1), (key1566, 1), (key1680, 1), (key1539, 1), (key1566, 1), (key1539, 1), (key1917, 1), (key1902, 1), (key1917, 1), (key1895, 1), (key1902, 1), (key1895, 1)]

theorem rawRowCheck8571 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form5 = rawRow8571 := by decide +kernel

def row8571 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

theorem rowCheck8571 : row8571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8571 := by decide +kernel

theorem rowEval8571 (x : Key → ℝ) : Integer.Sparse.eval row8571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8571, Integer.Sparse.eval_collectBalanced, rawRowCheck8571]

def rawRow8572 : Integer.Sparse Key := [(key1539, -2), (key1539, -2), (key1895, -2), (key1309, -2), (key1309, -2), (key1615, -2), (key1615, -2), (key1917, -2), (key1917, -2), (key1350, -2), (key1680, -2), (key1680, -2), (key1384, 1), (key1384, 1), (key1539, 1), (key1539, 1), (key1895, 1), (key1895, 1), (key1289, 1), (key1289, 1), (key1566, 1), (key1566, 1), (key1902, 1), (key1902, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1917, 1), (key1917, 1), (key1350, 1), (key1350, 1), (key1471, 1), (key1471, 1), (key1680, 1), (key1680, 1)]

theorem rawRowCheck8572 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form5 = rawRow8572 := by decide +kernel

def row8572 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

theorem rowCheck8572 : row8572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8572 := by decide +kernel

theorem rowEval8572 (x : Key → ℝ) : Integer.Sparse.eval row8572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8572, Integer.Sparse.eval_collectBalanced, rawRowCheck8572]

def rawRow8573 : Integer.Sparse Key := [(key1539, -2), (key1895, -2), (key1539, -2), (key1615, -2), (key1917, -2), (key1309, -2), (key1917, -2), (key1309, -2), (key1615, -2), (key1680, -2), (key1350, -2), (key1680, -2), (key1539, 1), (key1895, 1), (key1384, 1), (key1895, 1), (key1384, 1), (key1539, 1), (key1566, 1), (key1902, 1), (key1289, 1), (key1902, 1), (key1289, 1), (key1566, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1471, 1), (key1680, 1), (key1350, 1), (key1680, 1), (key1350, 1), (key1471, 1)]

theorem rawRowCheck8573 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form5 = rawRow8573 := by decide +kernel

def row8573 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

theorem rowCheck8573 : row8573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8573 := by decide +kernel

theorem rowEval8573 (x : Key → ℝ) : Integer.Sparse.eval row8573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8573, Integer.Sparse.eval_collectBalanced, rawRowCheck8573]

def rawRow8574 : Integer.Sparse Key := [(key1895, -2), (key1539, -2), (key1539, -2), (key1917, -2), (key1615, -2), (key1917, -2), (key1309, -2), (key1615, -2), (key1309, -2), (key1680, -2), (key1680, -2), (key1350, -2), (key1895, 1), (key1539, 1), (key1895, 1), (key1384, 1), (key1539, 1), (key1384, 1), (key1902, 1), (key1566, 1), (key1902, 1), (key1289, 1), (key1566, 1), (key1289, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1309, 1), (key1680, 1), (key1471, 1), (key1680, 1), (key1350, 1), (key1471, 1), (key1350, 1)]

theorem rawRowCheck8574 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form5 = rawRow8574 := by decide +kernel

def row8574 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

theorem rowCheck8574 : row8574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8574 := by decide +kernel

theorem rowEval8574 (x : Key → ℝ) : Integer.Sparse.eval row8574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8574, Integer.Sparse.eval_collectBalanced, rawRowCheck8574]

def rawRow8575 : Integer.Sparse Key := [(key1615, -2), (key1680, -2), (key1917, -2), (key1309, -2), (key1350, -2), (key1539, -2), (key1680, -2), (key1895, -2), (key1917, -2), (key1309, -2), (key1539, -2), (key1615, -2), (key1417, 1), (key1471, 1), (key1566, 1), (key1680, 1), (key1902, 1), (key1917, 1), (key1309, 1), (key1350, 1), (key1539, 1), (key1680, 1), (key1895, 1), (key1917, 1), (key1289, 1), (key1350, 1), (key1384, 1), (key1471, 1), (key1895, 1), (key1902, 1), (key1289, 1), (key1309, 1), (key1384, 1), (key1417, 1), (key1539, 1), (key1566, 1)]

theorem rawRowCheck8575 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form5 = rawRow8575 := by decide +kernel

def row8575 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

theorem rowCheck8575 : row8575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8575 := by decide +kernel

theorem rowEval8575 (x : Key → ℝ) : Integer.Sparse.eval row8575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8575, Integer.Sparse.eval_collectBalanced, rawRowCheck8575]

end MUB6.Certificate.GramRows

end OAI
