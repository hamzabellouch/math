import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2688 : Integer.Sparse Key := [(key2891, -2), (key2996, -2), (key2891, -2), (key2914, 1), (key2912, 1), (key3003, 1), (key2912, 1), (key3003, 1), (key2914, 1), (key2774, 2), (key2934, 2), (key2774, 2), (key2914, -1), (key2882, -1), (key2993, -1), (key2882, -1), (key2993, -1), (key2914, -1), (key2410, -1), (key2407, -1), (key2441, -1), (key2407, -1), (key2441, -1), (key2410, -1), (key2483, 1), (key2473, 1), (key2507, 1), (key2473, 1), (key2507, 1), (key2483, 1)]

theorem rawRowCheck2688 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form0 = rawRow2688 := by decide +kernel

def row2688 : Integer.Sparse Key := [(key2407, -2), (key2410, -2), (key2441, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2774, 4), (key2882, -2), (key2891, -4), (key2912, 2), (key2934, 2), (key2993, -2), (key2996, -2), (key3003, 2)]

theorem rowCheck2688 : row2688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2688 := by decide +kernel

theorem rowEval2688 (x : Key → ℝ) : Integer.Sparse.eval row2688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2688, Integer.Sparse.eval_collectBalanced, rawRowCheck2688]

def rawRow2689 : Integer.Sparse Key := [(key2996, -2), (key2891, -2), (key2891, -2), (key3003, 1), (key3003, 1), (key2914, 1), (key2914, 1), (key2912, 1), (key2912, 1), (key2934, 2), (key2774, 2), (key2774, 2), (key2993, -1), (key2993, -1), (key2914, -1), (key2914, -1), (key2882, -1), (key2882, -1), (key2441, -1), (key2441, -1), (key2410, -1), (key2410, -1), (key2407, -1), (key2407, -1), (key2507, 1), (key2507, 1), (key2483, 1), (key2483, 1), (key2473, 1), (key2473, 1)]

theorem rawRowCheck2689 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form0 = rawRow2689 := by decide +kernel

def row2689 : Integer.Sparse Key := [(key2407, -2), (key2410, -2), (key2441, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2774, 4), (key2882, -2), (key2891, -4), (key2912, 2), (key2934, 2), (key2993, -2), (key2996, -2), (key3003, 2)]

theorem rowCheck2689 : row2689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2689 := by decide +kernel

theorem rowEval2689 (x : Key → ℝ) : Integer.Sparse.eval row2689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2689, Integer.Sparse.eval_collectBalanced, rawRowCheck2689]

def rawRow2690 : Integer.Sparse Key := [(key2602, -2), (key2912, -2), (key3003, -2), (key2602, 1), (key2603, 1), (key2891, 1), (key2996, 1), (key2914, 1), (key3003, 1), (key2595, 2), (key2882, 2), (key2993, 2), (key2595, -1), (key2603, -1), (key2774, -1), (key2934, -1), (key2914, -1), (key2993, -1), (key2592, -1), (key2595, -1), (key2848, -1), (key2970, -1), (key2882, -1), (key2991, -1), (key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1)]

theorem rawRowCheck2690 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form0 = rawRow2690 := by decide +kernel

def row2690 : Integer.Sparse Key := [(key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1), (key2592, -1), (key2602, -1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2934, -1), (key2970, -1), (key2991, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

theorem rowCheck2690 : row2690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2690 := by decide +kernel

theorem rowEval2690 (x : Key → ℝ) : Integer.Sparse.eval row2690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2690, Integer.Sparse.eval_collectBalanced, rawRowCheck2690]

def rawRow2691 : Integer.Sparse Key := [(key2602, -2), (key3003, -2), (key2912, -2), (key2603, 1), (key2602, 1), (key2996, 1), (key2891, 1), (key3003, 1), (key2914, 1), (key2595, 2), (key2993, 2), (key2882, 2), (key2603, -1), (key2595, -1), (key2934, -1), (key2774, -1), (key2993, -1), (key2914, -1), (key2595, -1), (key2592, -1), (key2970, -1), (key2848, -1), (key2991, -1), (key2882, -1), (key2393, 1), (key2379, 1), (key2441, 1), (key2407, 1), (key2555, 1), (key2544, 1)]

theorem rawRowCheck2691 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form0 = rawRow2691 := by decide +kernel

def row2691 : Integer.Sparse Key := [(key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1), (key2592, -1), (key2602, -1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2934, -1), (key2970, -1), (key2991, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

theorem rowCheck2691 : row2691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2691 := by decide +kernel

theorem rowEval2691 (x : Key → ℝ) : Integer.Sparse.eval row2691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2691, Integer.Sparse.eval_collectBalanced, rawRowCheck2691]

def rawRow2692 : Integer.Sparse Key := [(key2912, -2), (key2602, -2), (key3003, -2), (key2891, 1), (key2914, 1), (key2602, 1), (key3003, 1), (key2603, 1), (key2996, 1), (key2882, 2), (key2595, 2), (key2993, 2), (key2774, -1), (key2914, -1), (key2595, -1), (key2993, -1), (key2603, -1), (key2934, -1), (key2848, -1), (key2882, -1), (key2592, -1), (key2991, -1), (key2595, -1), (key2970, -1), (key2771, 1), (key2912, 1), (key2592, 1), (key2991, 1), (key2393, 1), (key2441, 1)]

theorem rawRowCheck2692 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form0 = rawRow2692 := by decide +kernel

def row2692 : Integer.Sparse Key := [(key2393, 1), (key2441, 1), (key2602, -1), (key2771, 1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -1), (key2934, -1), (key2970, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

theorem rowCheck2692 : row2692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2692 := by decide +kernel

theorem rowEval2692 (x : Key → ℝ) : Integer.Sparse.eval row2692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2692, Integer.Sparse.eval_collectBalanced, rawRowCheck2692]

def rawRow2693 : Integer.Sparse Key := [(key2912, -2), (key3003, -2), (key2602, -2), (key2914, 1), (key2891, 1), (key3003, 1), (key2602, 1), (key2996, 1), (key2603, 1), (key2882, 2), (key2993, 2), (key2595, 2), (key2914, -1), (key2774, -1), (key2993, -1), (key2595, -1), (key2934, -1), (key2603, -1), (key2882, -1), (key2848, -1), (key2991, -1), (key2592, -1), (key2970, -1), (key2595, -1), (key2912, 1), (key2771, 1), (key2991, 1), (key2592, 1), (key2441, 1), (key2393, 1)]

theorem rawRowCheck2693 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form0 = rawRow2693 := by decide +kernel

def row2693 : Integer.Sparse Key := [(key2393, 1), (key2441, 1), (key2602, -1), (key2771, 1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -1), (key2934, -1), (key2970, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

theorem rowCheck2693 : row2693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2693 := by decide +kernel

theorem rowEval2693 (x : Key → ℝ) : Integer.Sparse.eval row2693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck2693, Integer.Sparse.eval_collectBalanced, rawRowCheck2693]

def rawRow2694 : Integer.Sparse Key := [(key3003, -2), (key2602, -2), (key2912, -2), (key2996, 1), (key3003, 1), (key2603, 1), (key2914, 1), (key2602, 1), (key2891, 1), (key2993, 2), (key2595, 2), (key2882, 2), (key2934, -1), (key2993, -1), (key2603, -1), (key2914, -1), (key2595, -1), (key2774, -1), (key2970, -1), (key2991, -1), (key2595, -1), (key2882, -1), (key2592, -1), (key2848, -1), (key2933, 1), (key2991, 1), (key2602, 1), (key2912, 1), (key2379, 1), (key2407, 1)]

theorem rawRowCheck2694 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form0 = rawRow2694 := by decide +kernel

def row2694 : Integer.Sparse Key := [(key2379, 1), (key2407, 1), (key2592, -1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -1), (key2933, 1), (key2934, -1), (key2970, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

theorem rowCheck2694 : row2694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2694 := by decide +kernel

theorem rowEval2694 (x : Key → ℝ) : Integer.Sparse.eval row2694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2694, Integer.Sparse.eval_collectBalanced, rawRowCheck2694]

def rawRow2695 : Integer.Sparse Key := [(key3003, -2), (key2912, -2), (key2602, -2), (key3003, 1), (key2996, 1), (key2914, 1), (key2603, 1), (key2891, 1), (key2602, 1), (key2993, 2), (key2882, 2), (key2595, 2), (key2993, -1), (key2934, -1), (key2914, -1), (key2603, -1), (key2774, -1), (key2595, -1), (key2991, -1), (key2970, -1), (key2882, -1), (key2595, -1), (key2848, -1), (key2592, -1), (key2991, 1), (key2933, 1), (key2912, 1), (key2602, 1), (key2771, 1), (key2592, 1)]

theorem rawRowCheck2695 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form0 = rawRow2695 := by decide +kernel

def row2695 : Integer.Sparse Key := [(key2771, 1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -1), (key2933, 1), (key2934, -1), (key2970, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

theorem rowCheck2695 : row2695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2695 := by decide +kernel

theorem rowEval2695 (x : Key → ℝ) : Integer.Sparse.eval row2695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck2695, Integer.Sparse.eval_collectBalanced, rawRowCheck2695]

def rawRow2696 : Integer.Sparse Key := [(key1254, -6), (key1254, 2), (key1263, 2), (key1263, 2), (key1529, 6), (key1529, -2), (key1763, -2), (key1763, -2), (key1607, -2), (key1646, -2), (key1646, -2), (key1607, 2), (key1804, 2), (key1804, 2)]

theorem rawRowCheck2696 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form1 = rawRow2696 := by decide +kernel

def row2696 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

theorem rowCheck2696 : row2696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2696 := by decide +kernel

theorem rowEval2696 (x : Key → ℝ) : Integer.Sparse.eval row2696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2696, Integer.Sparse.eval_collectBalanced, rawRowCheck2696]

def rawRow2697 : Integer.Sparse Key := [(key1254, -6), (key1263, 2), (key1254, 2), (key1263, 2), (key1529, 6), (key1763, -2), (key1529, -2), (key1763, -2), (key1646, -2), (key1607, -2), (key1646, -2), (key1804, 2), (key1607, 2), (key1804, 2)]

theorem rawRowCheck2697 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form1 = rawRow2697 := by decide +kernel

def row2697 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

theorem rowCheck2697 : row2697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2697 := by decide +kernel

theorem rowEval2697 (x : Key → ℝ) : Integer.Sparse.eval row2697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2697, Integer.Sparse.eval_collectBalanced, rawRowCheck2697]

def rawRow2698 : Integer.Sparse Key := [(key1254, -6), (key1263, 2), (key1263, 2), (key1254, 2), (key1529, 6), (key1763, -2), (key1763, -2), (key1529, -2), (key1646, -2), (key1646, -2), (key1607, -2), (key1804, 2), (key1804, 2), (key1607, 2)]

theorem rawRowCheck2698 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form1 = rawRow2698 := by decide +kernel

def row2698 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

theorem rowCheck2698 : row2698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2698 := by decide +kernel

theorem rowEval2698 (x : Key → ℝ) : Integer.Sparse.eval row2698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2698, Integer.Sparse.eval_collectBalanced, rawRowCheck2698]

def rawRow2699 : Integer.Sparse Key := [(key1263, -6), (key1254, 2), (key1254, 2), (key1263, 2), (key1763, 6), (key1529, -2), (key1529, -2), (key1763, -2), (key1804, -2), (key1804, -2), (key1835, -2), (key1646, 2), (key1646, 2), (key1835, 2)]

theorem rawRowCheck2699 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form1 = rawRow2699 := by decide +kernel

def row2699 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

theorem rowCheck2699 : row2699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2699 := by decide +kernel

theorem rowEval2699 (x : Key → ℝ) : Integer.Sparse.eval row2699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2699, Integer.Sparse.eval_collectBalanced, rawRowCheck2699]

def rawRow2700 : Integer.Sparse Key := [(key1263, -6), (key1254, 2), (key1263, 2), (key1254, 2), (key1763, 6), (key1529, -2), (key1763, -2), (key1529, -2), (key1804, -2), (key1835, -2), (key1804, -2), (key1646, 2), (key1835, 2), (key1646, 2)]

theorem rawRowCheck2700 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form1 = rawRow2700 := by decide +kernel

def row2700 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

theorem rowCheck2700 : row2700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2700 := by decide +kernel

theorem rowEval2700 (x : Key → ℝ) : Integer.Sparse.eval row2700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2700, Integer.Sparse.eval_collectBalanced, rawRowCheck2700]

def rawRow2701 : Integer.Sparse Key := [(key1263, -6), (key1263, 2), (key1254, 2), (key1254, 2), (key1763, 6), (key1763, -2), (key1529, -2), (key1529, -2), (key1835, -2), (key1804, -2), (key1804, -2), (key1835, 2), (key1646, 2), (key1646, 2)]

theorem rawRowCheck2701 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form1 = rawRow2701 := by decide +kernel

def row2701 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

theorem rowCheck2701 : row2701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2701 := by decide +kernel

theorem rowEval2701 (x : Key → ℝ) : Integer.Sparse.eval row2701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2701, Integer.Sparse.eval_collectBalanced, rawRowCheck2701]

def rawRow2702 : Integer.Sparse Key := [(key1529, -6), (key1607, 2), (key1646, 2), (key1646, 2), (key1254, 6), (key1607, -2), (key1804, -2), (key1804, -2), (key1254, -2), (key1263, -2), (key1263, -2), (key1529, 2), (key1763, 2), (key1763, 2)]

theorem rawRowCheck2702 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form1 = rawRow2702 := by decide +kernel

def row2702 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

theorem rowCheck2702 : row2702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2702 := by decide +kernel

theorem rowEval2702 (x : Key → ℝ) : Integer.Sparse.eval row2702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2702, Integer.Sparse.eval_collectBalanced, rawRowCheck2702]

def rawRow2703 : Integer.Sparse Key := [(key1529, -6), (key1646, 2), (key1607, 2), (key1646, 2), (key1254, 6), (key1804, -2), (key1607, -2), (key1804, -2), (key1263, -2), (key1254, -2), (key1263, -2), (key1763, 2), (key1529, 2), (key1763, 2)]

theorem rawRowCheck2703 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form1 = rawRow2703 := by decide +kernel

def row2703 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

theorem rowCheck2703 : row2703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2703 := by decide +kernel

theorem rowEval2703 (x : Key → ℝ) : Integer.Sparse.eval row2703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2703, Integer.Sparse.eval_collectBalanced, rawRowCheck2703]

def rawRow2704 : Integer.Sparse Key := [(key1529, -6), (key1646, 2), (key1646, 2), (key1607, 2), (key1254, 6), (key1804, -2), (key1804, -2), (key1607, -2), (key1263, -2), (key1263, -2), (key1254, -2), (key1763, 2), (key1763, 2), (key1529, 2)]

theorem rawRowCheck2704 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form1 = rawRow2704 := by decide +kernel

def row2704 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

theorem rowCheck2704 : row2704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2704 := by decide +kernel

theorem rowEval2704 (x : Key → ℝ) : Integer.Sparse.eval row2704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2704, Integer.Sparse.eval_collectBalanced, rawRowCheck2704]

def rawRow2705 : Integer.Sparse Key := [(key1646, -6), (key1529, 2), (key1607, 2), (key1646, 2), (key1804, 6), (key1254, -2), (key1607, -2), (key1804, -2), (key1763, -2), (key1804, -2), (key1835, -2), (key1263, 2), (key1646, 2), (key1835, 2)]

theorem rawRowCheck2705 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form1 = rawRow2705 := by decide +kernel

def row2705 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

theorem rowCheck2705 : row2705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2705 := by decide +kernel

theorem rowEval2705 (x : Key → ℝ) : Integer.Sparse.eval row2705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2705, Integer.Sparse.eval_collectBalanced, rawRowCheck2705]

def rawRow2706 : Integer.Sparse Key := [(key1646, -6), (key1529, 2), (key1646, 2), (key1607, 2), (key1804, 6), (key1254, -2), (key1804, -2), (key1607, -2), (key1763, -2), (key1835, -2), (key1804, -2), (key1263, 2), (key1835, 2), (key1646, 2)]

theorem rawRowCheck2706 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form1 = rawRow2706 := by decide +kernel

def row2706 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

theorem rowCheck2706 : row2706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2706 := by decide +kernel

theorem rowEval2706 (x : Key → ℝ) : Integer.Sparse.eval row2706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2706, Integer.Sparse.eval_collectBalanced, rawRowCheck2706]

def rawRow2707 : Integer.Sparse Key := [(key1646, -6), (key1607, 2), (key1529, 2), (key1646, 2), (key1804, 6), (key1607, -2), (key1254, -2), (key1804, -2), (key1804, -2), (key1763, -2), (key1835, -2), (key1646, 2), (key1263, 2), (key1835, 2)]

theorem rawRowCheck2707 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form1 = rawRow2707 := by decide +kernel

def row2707 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

theorem rowCheck2707 : row2707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2707 := by decide +kernel

theorem rowEval2707 (x : Key → ℝ) : Integer.Sparse.eval row2707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2707, Integer.Sparse.eval_collectBalanced, rawRowCheck2707]

def rawRow2708 : Integer.Sparse Key := [(key1646, -6), (key1607, 2), (key1646, 2), (key1529, 2), (key1804, 6), (key1607, -2), (key1804, -2), (key1254, -2), (key1804, -2), (key1835, -2), (key1763, -2), (key1646, 2), (key1835, 2), (key1263, 2)]

theorem rawRowCheck2708 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form1 = rawRow2708 := by decide +kernel

def row2708 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

theorem rowCheck2708 : row2708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2708 := by decide +kernel

theorem rowEval2708 (x : Key → ℝ) : Integer.Sparse.eval row2708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck2708, Integer.Sparse.eval_collectBalanced, rawRowCheck2708]

def rawRow2709 : Integer.Sparse Key := [(key1646, -6), (key1646, 2), (key1529, 2), (key1607, 2), (key1804, 6), (key1804, -2), (key1254, -2), (key1607, -2), (key1835, -2), (key1763, -2), (key1804, -2), (key1835, 2), (key1263, 2), (key1646, 2)]

theorem rawRowCheck2709 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form1 = rawRow2709 := by decide +kernel

def row2709 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

theorem rowCheck2709 : row2709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2709 := by decide +kernel

theorem rowEval2709 (x : Key → ℝ) : Integer.Sparse.eval row2709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2709, Integer.Sparse.eval_collectBalanced, rawRowCheck2709]

def rawRow2710 : Integer.Sparse Key := [(key1646, -6), (key1646, 2), (key1607, 2), (key1529, 2), (key1804, 6), (key1804, -2), (key1607, -2), (key1254, -2), (key1835, -2), (key1804, -2), (key1763, -2), (key1835, 2), (key1646, 2), (key1263, 2)]

theorem rawRowCheck2710 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form1 = rawRow2710 := by decide +kernel

def row2710 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

theorem rowCheck2710 : row2710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2710 := by decide +kernel

theorem rowEval2710 (x : Key → ℝ) : Integer.Sparse.eval row2710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck2710, Integer.Sparse.eval_collectBalanced, rawRowCheck2710]

def rawRow2711 : Integer.Sparse Key := [(key1763, -6), (key1804, 2), (key1804, 2), (key1835, 2), (key1263, 6), (key1646, -2), (key1646, -2), (key1835, -2), (key1254, -2), (key1254, -2), (key1263, -2), (key1529, 2), (key1529, 2), (key1763, 2)]

theorem rawRowCheck2711 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form1 = rawRow2711 := by decide +kernel

def row2711 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

theorem rowCheck2711 : row2711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2711 := by decide +kernel

theorem rowEval2711 (x : Key → ℝ) : Integer.Sparse.eval row2711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2711, Integer.Sparse.eval_collectBalanced, rawRowCheck2711]

def rawRow2712 : Integer.Sparse Key := [(key1763, -6), (key1804, 2), (key1835, 2), (key1804, 2), (key1263, 6), (key1646, -2), (key1835, -2), (key1646, -2), (key1254, -2), (key1263, -2), (key1254, -2), (key1529, 2), (key1763, 2), (key1529, 2)]

theorem rawRowCheck2712 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form1 = rawRow2712 := by decide +kernel

def row2712 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

theorem rowCheck2712 : row2712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2712 := by decide +kernel

theorem rowEval2712 (x : Key → ℝ) : Integer.Sparse.eval row2712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2712, Integer.Sparse.eval_collectBalanced, rawRowCheck2712]

def rawRow2713 : Integer.Sparse Key := [(key1763, -6), (key1835, 2), (key1804, 2), (key1804, 2), (key1263, 6), (key1835, -2), (key1646, -2), (key1646, -2), (key1263, -2), (key1254, -2), (key1254, -2), (key1763, 2), (key1529, 2), (key1529, 2)]

theorem rawRowCheck2713 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form1 = rawRow2713 := by decide +kernel

def row2713 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

theorem rowCheck2713 : row2713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2713 := by decide +kernel

theorem rowEval2713 (x : Key → ℝ) : Integer.Sparse.eval row2713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2713, Integer.Sparse.eval_collectBalanced, rawRowCheck2713]

def rawRow2714 : Integer.Sparse Key := [(key1804, -6), (key1763, 2), (key1804, 2), (key1835, 2), (key1646, 6), (key1263, -2), (key1646, -2), (key1835, -2), (key1529, -2), (key1607, -2), (key1646, -2), (key1254, 2), (key1607, 2), (key1804, 2)]

theorem rawRowCheck2714 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form1 = rawRow2714 := by decide +kernel

def row2714 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

theorem rowCheck2714 : row2714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2714 := by decide +kernel

theorem rowEval2714 (x : Key → ℝ) : Integer.Sparse.eval row2714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2714, Integer.Sparse.eval_collectBalanced, rawRowCheck2714]

def rawRow2715 : Integer.Sparse Key := [(key1804, -6), (key1763, 2), (key1835, 2), (key1804, 2), (key1646, 6), (key1263, -2), (key1835, -2), (key1646, -2), (key1529, -2), (key1646, -2), (key1607, -2), (key1254, 2), (key1804, 2), (key1607, 2)]

theorem rawRowCheck2715 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form1 = rawRow2715 := by decide +kernel

def row2715 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

theorem rowCheck2715 : row2715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2715 := by decide +kernel

theorem rowEval2715 (x : Key → ℝ) : Integer.Sparse.eval row2715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2715, Integer.Sparse.eval_collectBalanced, rawRowCheck2715]

def rawRow2716 : Integer.Sparse Key := [(key1804, -6), (key1804, 2), (key1763, 2), (key1835, 2), (key1646, 6), (key1646, -2), (key1263, -2), (key1835, -2), (key1607, -2), (key1529, -2), (key1646, -2), (key1607, 2), (key1254, 2), (key1804, 2)]

theorem rawRowCheck2716 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form1 = rawRow2716 := by decide +kernel

def row2716 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

theorem rowCheck2716 : row2716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2716 := by decide +kernel

theorem rowEval2716 (x : Key → ℝ) : Integer.Sparse.eval row2716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2716, Integer.Sparse.eval_collectBalanced, rawRowCheck2716]

def rawRow2717 : Integer.Sparse Key := [(key1804, -6), (key1804, 2), (key1835, 2), (key1763, 2), (key1646, 6), (key1646, -2), (key1835, -2), (key1263, -2), (key1607, -2), (key1646, -2), (key1529, -2), (key1607, 2), (key1804, 2), (key1254, 2)]

theorem rawRowCheck2717 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form1 = rawRow2717 := by decide +kernel

def row2717 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

theorem rowCheck2717 : row2717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2717 := by decide +kernel

theorem rowEval2717 (x : Key → ℝ) : Integer.Sparse.eval row2717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck2717, Integer.Sparse.eval_collectBalanced, rawRowCheck2717]

def rawRow2718 : Integer.Sparse Key := [(key1804, -6), (key1835, 2), (key1763, 2), (key1804, 2), (key1646, 6), (key1835, -2), (key1263, -2), (key1646, -2), (key1646, -2), (key1529, -2), (key1607, -2), (key1804, 2), (key1254, 2), (key1607, 2)]

theorem rawRowCheck2718 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form1 = rawRow2718 := by decide +kernel

def row2718 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

theorem rowCheck2718 : row2718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2718 := by decide +kernel

theorem rowEval2718 (x : Key → ℝ) : Integer.Sparse.eval row2718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2718, Integer.Sparse.eval_collectBalanced, rawRowCheck2718]

def rawRow2719 : Integer.Sparse Key := [(key1804, -6), (key1835, 2), (key1804, 2), (key1763, 2), (key1646, 6), (key1835, -2), (key1646, -2), (key1263, -2), (key1646, -2), (key1607, -2), (key1529, -2), (key1804, 2), (key1607, 2), (key1254, 2)]

theorem rawRowCheck2719 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form1 = rawRow2719 := by decide +kernel

def row2719 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

theorem rowCheck2719 : row2719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2719 := by decide +kernel

theorem rowEval2719 (x : Key → ℝ) : Integer.Sparse.eval row2719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck2719, Integer.Sparse.eval_collectBalanced, rawRowCheck2719]

def rawRow2720 : Integer.Sparse Key := [(key2378, -2), (key2378, -2), (key2383, -2), (key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2394, 1), (key2394, 1), (key2406, 2), (key2406, 2), (key2411, 2), (key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2443, -1), (key2443, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2484, -1), (key2484, -1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2509, 1), (key2509, 1)]

theorem rawRowCheck2720 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form2 = rawRow2720 := by decide +kernel

def row2720 : Integer.Sparse Key := [(key2378, -2), (key2383, -2), (key2390, 2), (key2394, 2), (key2406, 2), (key2411, 2), (key2437, -2), (key2443, -2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2)]

theorem rowCheck2720 : row2720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2720 := by decide +kernel

theorem rowEval2720 (x : Key → ℝ) : Integer.Sparse.eval row2720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2720, Integer.Sparse.eval_collectBalanced, rawRowCheck2720]

def rawRow2721 : Integer.Sparse Key := [(key2378, -2), (key2383, -2), (key2378, -2), (key2390, 1), (key2394, 1), (key2378, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2406, 2), (key2411, 2), (key2406, 2), (key2437, -1), (key2443, -1), (key2406, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2484, -1), (key2472, -1), (key2484, -1), (key2472, -1), (key2480, -1), (key2503, 1), (key2509, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2503, 1)]

theorem rawRowCheck2721 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form2 = rawRow2721 := by decide +kernel

def row2721 : Integer.Sparse Key := [(key2378, -2), (key2383, -2), (key2390, 2), (key2394, 2), (key2406, 2), (key2411, 2), (key2437, -2), (key2443, -2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2)]

theorem rowCheck2721 : row2721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2721 := by decide +kernel

theorem rowEval2721 (x : Key → ℝ) : Integer.Sparse.eval row2721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2721, Integer.Sparse.eval_collectBalanced, rawRowCheck2721]

def rawRow2722 : Integer.Sparse Key := [(key2383, -2), (key2378, -2), (key2378, -2), (key2394, 1), (key2390, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2411, 2), (key2406, 2), (key2406, 2), (key2443, -1), (key2437, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2484, -1), (key2480, -1), (key2484, -1), (key2472, -1), (key2480, -1), (key2472, -1), (key2509, 1), (key2503, 1), (key2509, 1), (key2472, 1), (key2503, 1), (key2472, 1)]

theorem rawRowCheck2722 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form2 = rawRow2722 := by decide +kernel

def row2722 : Integer.Sparse Key := [(key2378, -2), (key2383, -2), (key2390, 2), (key2394, 2), (key2406, 2), (key2411, 2), (key2437, -2), (key2443, -2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2)]

theorem rowCheck2722 : row2722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2722 := by decide +kernel

theorem rowEval2722 (x : Key → ℝ) : Integer.Sparse.eval row2722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2722, Integer.Sparse.eval_collectBalanced, rawRowCheck2722]

def rawRow2723 : Integer.Sparse Key := [(key2390, -2), (key2394, -2), (key2394, -2), (key2378, 1), (key2383, 1), (key2378, 1), (key2394, 1), (key2383, 1), (key2394, 1), (key2437, 2), (key2443, 2), (key2443, 2), (key2406, -1), (key2411, -1), (key2406, -1), (key2443, -1), (key2411, -1), (key2443, -1), (key2503, -1), (key2509, -1), (key2503, -1), (key2524, -1), (key2509, -1), (key2524, -1), (key2480, 1), (key2484, 1), (key2480, 1), (key2524, 1), (key2484, 1), (key2524, 1)]

theorem rawRowCheck2723 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form2 = rawRow2723 := by decide +kernel

def row2723 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, -2), (key2394, -2), (key2406, -2), (key2411, -2), (key2437, 2), (key2443, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2)]

theorem rowCheck2723 : row2723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2723 := by decide +kernel

theorem rowEval2723 (x : Key → ℝ) : Integer.Sparse.eval row2723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2723, Integer.Sparse.eval_collectBalanced, rawRowCheck2723]

def rawRow2724 : Integer.Sparse Key := [(key2394, -2), (key2390, -2), (key2394, -2), (key2383, 1), (key2378, 1), (key2394, 1), (key2378, 1), (key2394, 1), (key2383, 1), (key2443, 2), (key2437, 2), (key2443, 2), (key2411, -1), (key2406, -1), (key2443, -1), (key2406, -1), (key2443, -1), (key2411, -1), (key2509, -1), (key2503, -1), (key2524, -1), (key2503, -1), (key2524, -1), (key2509, -1), (key2484, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2484, 1)]

theorem rawRowCheck2724 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form2 = rawRow2724 := by decide +kernel

def row2724 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, -2), (key2394, -2), (key2406, -2), (key2411, -2), (key2437, 2), (key2443, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2)]

theorem rowCheck2724 : row2724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2724 := by decide +kernel

theorem rowEval2724 (x : Key → ℝ) : Integer.Sparse.eval row2724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2724, Integer.Sparse.eval_collectBalanced, rawRowCheck2724]

def rawRow2725 : Integer.Sparse Key := [(key2394, -2), (key2394, -2), (key2390, -2), (key2394, 1), (key2394, 1), (key2383, 1), (key2383, 1), (key2378, 1), (key2378, 1), (key2443, 2), (key2443, 2), (key2437, 2), (key2443, -1), (key2443, -1), (key2411, -1), (key2411, -1), (key2406, -1), (key2406, -1), (key2524, -1), (key2524, -1), (key2509, -1), (key2509, -1), (key2503, -1), (key2503, -1), (key2524, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2480, 1), (key2480, 1)]

theorem rawRowCheck2725 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form2 = rawRow2725 := by decide +kernel

def row2725 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, -2), (key2394, -2), (key2406, -2), (key2411, -2), (key2437, 2), (key2443, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2)]

theorem rowCheck2725 : row2725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2725 := by decide +kernel

theorem rowEval2725 (x : Key → ℝ) : Integer.Sparse.eval row2725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2725, Integer.Sparse.eval_collectBalanced, rawRowCheck2725]

def rawRow2726 : Integer.Sparse Key := [(key2766, -2), (key2766, -2), (key2772, -2), (key2843, 1), (key2843, 1), (key2887, 1), (key2887, 1), (key2889, 1), (key2889, 1), (key2587, 2), (key2587, 2), (key2593, 2), (key2843, -1), (key2843, -1), (key2966, -1), (key2966, -1), (key2968, -1), (key2968, -1), (key2378, -1), (key2378, -1), (key2390, -1), (key2390, -1), (key2394, -1), (key2394, -1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2443, 1), (key2443, 1)]

theorem rawRowCheck2726 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form2 = rawRow2726 := by decide +kernel

def row2726 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, -2), (key2406, 2), (key2437, 2), (key2443, 2), (key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, 2), (key2889, 2), (key2966, -2), (key2968, -2)]

theorem rowCheck2726 : row2726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2726 := by decide +kernel

theorem rowEval2726 (x : Key → ℝ) : Integer.Sparse.eval row2726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2726, Integer.Sparse.eval_collectBalanced, rawRowCheck2726]

def rawRow2727 : Integer.Sparse Key := [(key2766, -2), (key2772, -2), (key2766, -2), (key2887, 1), (key2889, 1), (key2843, 1), (key2889, 1), (key2843, 1), (key2887, 1), (key2587, 2), (key2593, 2), (key2587, 2), (key2966, -1), (key2968, -1), (key2843, -1), (key2968, -1), (key2843, -1), (key2966, -1), (key2390, -1), (key2394, -1), (key2378, -1), (key2394, -1), (key2378, -1), (key2390, -1), (key2437, 1), (key2443, 1), (key2406, 1), (key2443, 1), (key2406, 1), (key2437, 1)]

theorem rawRowCheck2727 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form2 = rawRow2727 := by decide +kernel

def row2727 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, -2), (key2406, 2), (key2437, 2), (key2443, 2), (key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, 2), (key2889, 2), (key2966, -2), (key2968, -2)]

theorem rowCheck2727 : row2727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2727 := by decide +kernel

theorem rowEval2727 (x : Key → ℝ) : Integer.Sparse.eval row2727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2727, Integer.Sparse.eval_collectBalanced, rawRowCheck2727]

def rawRow2728 : Integer.Sparse Key := [(key2772, -2), (key2766, -2), (key2766, -2), (key2889, 1), (key2887, 1), (key2889, 1), (key2843, 1), (key2887, 1), (key2843, 1), (key2593, 2), (key2587, 2), (key2587, 2), (key2968, -1), (key2966, -1), (key2968, -1), (key2843, -1), (key2966, -1), (key2843, -1), (key2394, -1), (key2390, -1), (key2394, -1), (key2378, -1), (key2390, -1), (key2378, -1), (key2443, 1), (key2437, 1), (key2443, 1), (key2406, 1), (key2437, 1), (key2406, 1)]

theorem rawRowCheck2728 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form2 = rawRow2728 := by decide +kernel

def row2728 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, -2), (key2406, 2), (key2437, 2), (key2443, 2), (key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, 2), (key2889, 2), (key2966, -2), (key2968, -2)]

theorem rowCheck2728 : row2728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2728 := by decide +kernel

theorem rowEval2728 (x : Key → ℝ) : Integer.Sparse.eval row2728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2728, Integer.Sparse.eval_collectBalanced, rawRowCheck2728]

def rawRow2729 : Integer.Sparse Key := [(key2887, -2), (key2889, -2), (key2910, -2), (key2766, 1), (key2772, 1), (key2843, 1), (key2889, 1), (key2880, 1), (key2910, 1), (key2966, 2), (key2968, 2), (key2989, 2), (key2587, -1), (key2593, -1), (key2843, -1), (key2968, -1), (key2880, -1), (key2989, -1), (key2929, -1), (key2931, -1), (key2966, -1), (key2995, -1), (key2989, -1), (key3002, -1), (key2598, 1), (key2600, 1), (key2887, 1), (key2995, 1), (key2910, 1), (key3002, 1)]

theorem rawRowCheck2729 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form2 = rawRow2729 := by decide +kernel

def row2729 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

theorem rowCheck2729 : row2729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2729 := by decide +kernel

theorem rowEval2729 (x : Key → ℝ) : Integer.Sparse.eval row2729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2729, Integer.Sparse.eval_collectBalanced, rawRowCheck2729]

def rawRow2730 : Integer.Sparse Key := [(key2889, -2), (key2887, -2), (key2910, -2), (key2772, 1), (key2766, 1), (key2889, 1), (key2843, 1), (key2910, 1), (key2880, 1), (key2968, 2), (key2966, 2), (key2989, 2), (key2593, -1), (key2587, -1), (key2968, -1), (key2843, -1), (key2989, -1), (key2880, -1), (key2931, -1), (key2929, -1), (key2995, -1), (key2966, -1), (key3002, -1), (key2989, -1), (key2600, 1), (key2598, 1), (key2995, 1), (key2887, 1), (key3002, 1), (key2910, 1)]

theorem rawRowCheck2730 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form2 = rawRow2730 := by decide +kernel

def row2730 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

theorem rowCheck2730 : row2730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2730 := by decide +kernel

theorem rowEval2730 (x : Key → ℝ) : Integer.Sparse.eval row2730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2730, Integer.Sparse.eval_collectBalanced, rawRowCheck2730]

def rawRow2731 : Integer.Sparse Key := [(key2887, -2), (key2910, -2), (key2889, -2), (key2843, 1), (key2880, 1), (key2766, 1), (key2910, 1), (key2772, 1), (key2889, 1), (key2966, 2), (key2989, 2), (key2968, 2), (key2843, -1), (key2880, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2966, -1), (key2989, -1), (key2929, -1), (key3002, -1), (key2931, -1), (key2995, -1), (key2887, 1), (key2910, 1), (key2598, 1), (key3002, 1), (key2600, 1), (key2995, 1)]

theorem rawRowCheck2731 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form2 = rawRow2731 := by decide +kernel

def row2731 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

theorem rowCheck2731 : row2731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2731 := by decide +kernel

theorem rowEval2731 (x : Key → ℝ) : Integer.Sparse.eval row2731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2731, Integer.Sparse.eval_collectBalanced, rawRowCheck2731]

def rawRow2732 : Integer.Sparse Key := [(key2910, -2), (key2887, -2), (key2889, -2), (key2880, 1), (key2843, 1), (key2910, 1), (key2766, 1), (key2889, 1), (key2772, 1), (key2989, 2), (key2966, 2), (key2968, 2), (key2880, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2968, -1), (key2593, -1), (key2989, -1), (key2966, -1), (key3002, -1), (key2929, -1), (key2995, -1), (key2931, -1), (key2910, 1), (key2887, 1), (key3002, 1), (key2598, 1), (key2995, 1), (key2600, 1)]

theorem rawRowCheck2732 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form2 = rawRow2732 := by decide +kernel

def row2732 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

theorem rowCheck2732 : row2732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2732 := by decide +kernel

theorem rowEval2732 (x : Key → ℝ) : Integer.Sparse.eval row2732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck2732, Integer.Sparse.eval_collectBalanced, rawRowCheck2732]

def rawRow2733 : Integer.Sparse Key := [(key2889, -2), (key2910, -2), (key2887, -2), (key2889, 1), (key2910, 1), (key2772, 1), (key2880, 1), (key2766, 1), (key2843, 1), (key2968, 2), (key2989, 2), (key2966, 2), (key2968, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2587, -1), (key2843, -1), (key2995, -1), (key3002, -1), (key2931, -1), (key2989, -1), (key2929, -1), (key2966, -1), (key2995, 1), (key3002, 1), (key2600, 1), (key2910, 1), (key2598, 1), (key2887, 1)]

theorem rawRowCheck2733 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form2 = rawRow2733 := by decide +kernel

def row2733 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

theorem rowCheck2733 : row2733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2733 := by decide +kernel

theorem rowEval2733 (x : Key → ℝ) : Integer.Sparse.eval row2733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2733, Integer.Sparse.eval_collectBalanced, rawRowCheck2733]

def rawRow2734 : Integer.Sparse Key := [(key2910, -2), (key2889, -2), (key2887, -2), (key2910, 1), (key2889, 1), (key2880, 1), (key2772, 1), (key2843, 1), (key2766, 1), (key2989, 2), (key2968, 2), (key2966, 2), (key2989, -1), (key2968, -1), (key2880, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key3002, -1), (key2995, -1), (key2989, -1), (key2931, -1), (key2966, -1), (key2929, -1), (key3002, 1), (key2995, 1), (key2910, 1), (key2600, 1), (key2887, 1), (key2598, 1)]

theorem rawRowCheck2734 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form2 = rawRow2734 := by decide +kernel

def row2734 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

theorem rowCheck2734 : row2734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2734 := by decide +kernel

theorem rowEval2734 (x : Key → ℝ) : Integer.Sparse.eval row2734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck2734, Integer.Sparse.eval_collectBalanced, rawRowCheck2734]

def rawRow2735 : Integer.Sparse Key := [(key2929, -2), (key2931, -2), (key2931, -2), (key2966, 1), (key2968, 1), (key2966, 1), (key2995, 1), (key2968, 1), (key2995, 1), (key2598, 2), (key2600, 2), (key2600, 2), (key2887, -1), (key2889, -1), (key2887, -1), (key2995, -1), (key2889, -1), (key2995, -1), (key2587, -1), (key2593, -1), (key2587, -1), (key2600, -1), (key2593, -1), (key2600, -1), (key2766, 1), (key2772, 1), (key2766, 1), (key2931, 1), (key2772, 1), (key2931, 1)]

theorem rawRowCheck2735 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form2 = rawRow2735 := by decide +kernel

def row2735 : Integer.Sparse Key := [(key2587, -2), (key2593, -2), (key2598, 2), (key2600, 2), (key2766, 2), (key2772, 2), (key2887, -2), (key2889, -2), (key2929, -2), (key2931, -2), (key2966, 2), (key2968, 2)]

theorem rowCheck2735 : row2735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2735 := by decide +kernel

theorem rowEval2735 (x : Key → ℝ) : Integer.Sparse.eval row2735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2735, Integer.Sparse.eval_collectBalanced, rawRowCheck2735]

def rawRow2736 : Integer.Sparse Key := [(key2931, -2), (key2929, -2), (key2931, -2), (key2968, 1), (key2966, 1), (key2995, 1), (key2966, 1), (key2995, 1), (key2968, 1), (key2600, 2), (key2598, 2), (key2600, 2), (key2889, -1), (key2887, -1), (key2995, -1), (key2887, -1), (key2995, -1), (key2889, -1), (key2593, -1), (key2587, -1), (key2600, -1), (key2587, -1), (key2600, -1), (key2593, -1), (key2772, 1), (key2766, 1), (key2931, 1), (key2766, 1), (key2931, 1), (key2772, 1)]

theorem rawRowCheck2736 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form2 = rawRow2736 := by decide +kernel

def row2736 : Integer.Sparse Key := [(key2587, -2), (key2593, -2), (key2598, 2), (key2600, 2), (key2766, 2), (key2772, 2), (key2887, -2), (key2889, -2), (key2929, -2), (key2931, -2), (key2966, 2), (key2968, 2)]

theorem rowCheck2736 : row2736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2736 := by decide +kernel

theorem rowEval2736 (x : Key → ℝ) : Integer.Sparse.eval row2736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2736, Integer.Sparse.eval_collectBalanced, rawRowCheck2736]

def rawRow2737 : Integer.Sparse Key := [(key2931, -2), (key2931, -2), (key2929, -2), (key2995, 1), (key2995, 1), (key2968, 1), (key2968, 1), (key2966, 1), (key2966, 1), (key2600, 2), (key2600, 2), (key2598, 2), (key2995, -1), (key2995, -1), (key2889, -1), (key2889, -1), (key2887, -1), (key2887, -1), (key2600, -1), (key2600, -1), (key2593, -1), (key2593, -1), (key2587, -1), (key2587, -1), (key2931, 1), (key2931, 1), (key2772, 1), (key2772, 1), (key2766, 1), (key2766, 1)]

theorem rawRowCheck2737 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form2 = rawRow2737 := by decide +kernel

def row2737 : Integer.Sparse Key := [(key2587, -2), (key2593, -2), (key2598, 2), (key2600, 2), (key2766, 2), (key2772, 2), (key2887, -2), (key2889, -2), (key2929, -2), (key2931, -2), (key2966, 2), (key2968, 2)]

theorem rowCheck2737 : row2737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2737 := by decide +kernel

theorem rowEval2737 (x : Key → ℝ) : Integer.Sparse.eval row2737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2737, Integer.Sparse.eval_collectBalanced, rawRowCheck2737]

def rawRow2738 : Integer.Sparse Key := [(key2966, -2), (key2968, -2), (key2989, -2), (key2929, 1), (key2931, 1), (key2966, 1), (key2995, 1), (key2989, 1), (key3002, 1), (key2887, 2), (key2889, 2), (key2910, 2), (key2598, -1), (key2600, -1), (key2887, -1), (key2995, -1), (key2910, -1), (key3002, -1), (key2766, -1), (key2772, -1), (key2843, -1), (key2889, -1), (key2880, -1), (key2910, -1), (key2587, 1), (key2593, 1), (key2843, 1), (key2968, 1), (key2880, 1), (key2989, 1)]

theorem rawRowCheck2738 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form2 = rawRow2738 := by decide +kernel

def row2738 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

theorem rowCheck2738 : row2738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2738 := by decide +kernel

theorem rowEval2738 (x : Key → ℝ) : Integer.Sparse.eval row2738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2738, Integer.Sparse.eval_collectBalanced, rawRowCheck2738]

def rawRow2739 : Integer.Sparse Key := [(key2968, -2), (key2966, -2), (key2989, -2), (key2931, 1), (key2929, 1), (key2995, 1), (key2966, 1), (key3002, 1), (key2989, 1), (key2889, 2), (key2887, 2), (key2910, 2), (key2600, -1), (key2598, -1), (key2995, -1), (key2887, -1), (key3002, -1), (key2910, -1), (key2772, -1), (key2766, -1), (key2889, -1), (key2843, -1), (key2910, -1), (key2880, -1), (key2593, 1), (key2587, 1), (key2968, 1), (key2843, 1), (key2989, 1), (key2880, 1)]

theorem rawRowCheck2739 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form2 = rawRow2739 := by decide +kernel

def row2739 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

theorem rowCheck2739 : row2739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2739 := by decide +kernel

theorem rowEval2739 (x : Key → ℝ) : Integer.Sparse.eval row2739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2739, Integer.Sparse.eval_collectBalanced, rawRowCheck2739]

def rawRow2740 : Integer.Sparse Key := [(key2966, -2), (key2989, -2), (key2968, -2), (key2966, 1), (key2989, 1), (key2929, 1), (key3002, 1), (key2931, 1), (key2995, 1), (key2887, 2), (key2910, 2), (key2889, 2), (key2887, -1), (key2910, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2843, -1), (key2880, -1), (key2766, -1), (key2910, -1), (key2772, -1), (key2889, -1), (key2843, 1), (key2880, 1), (key2587, 1), (key2989, 1), (key2593, 1), (key2968, 1)]

theorem rawRowCheck2740 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form2 = rawRow2740 := by decide +kernel

def row2740 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

theorem rowCheck2740 : row2740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2740 := by decide +kernel

theorem rowEval2740 (x : Key → ℝ) : Integer.Sparse.eval row2740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2740, Integer.Sparse.eval_collectBalanced, rawRowCheck2740]

def rawRow2741 : Integer.Sparse Key := [(key2989, -2), (key2966, -2), (key2968, -2), (key2989, 1), (key2966, 1), (key3002, 1), (key2929, 1), (key2995, 1), (key2931, 1), (key2910, 2), (key2887, 2), (key2889, 2), (key2910, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2995, -1), (key2600, -1), (key2880, -1), (key2843, -1), (key2910, -1), (key2766, -1), (key2889, -1), (key2772, -1), (key2880, 1), (key2843, 1), (key2989, 1), (key2587, 1), (key2968, 1), (key2593, 1)]

theorem rawRowCheck2741 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form2 = rawRow2741 := by decide +kernel

def row2741 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

theorem rowCheck2741 : row2741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2741 := by decide +kernel

theorem rowEval2741 (x : Key → ℝ) : Integer.Sparse.eval row2741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck2741, Integer.Sparse.eval_collectBalanced, rawRowCheck2741]

def rawRow2742 : Integer.Sparse Key := [(key2968, -2), (key2989, -2), (key2966, -2), (key2995, 1), (key3002, 1), (key2931, 1), (key2989, 1), (key2929, 1), (key2966, 1), (key2889, 2), (key2910, 2), (key2887, 2), (key2995, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2598, -1), (key2887, -1), (key2889, -1), (key2910, -1), (key2772, -1), (key2880, -1), (key2766, -1), (key2843, -1), (key2968, 1), (key2989, 1), (key2593, 1), (key2880, 1), (key2587, 1), (key2843, 1)]

theorem rawRowCheck2742 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form2 = rawRow2742 := by decide +kernel

def row2742 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

theorem rowCheck2742 : row2742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2742 := by decide +kernel

theorem rowEval2742 (x : Key → ℝ) : Integer.Sparse.eval row2742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2742, Integer.Sparse.eval_collectBalanced, rawRowCheck2742]

def rawRow2743 : Integer.Sparse Key := [(key2989, -2), (key2968, -2), (key2966, -2), (key3002, 1), (key2995, 1), (key2989, 1), (key2931, 1), (key2966, 1), (key2929, 1), (key2910, 2), (key2889, 2), (key2887, 2), (key3002, -1), (key2995, -1), (key2910, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2910, -1), (key2889, -1), (key2880, -1), (key2772, -1), (key2843, -1), (key2766, -1), (key2989, 1), (key2968, 1), (key2880, 1), (key2593, 1), (key2843, 1), (key2587, 1)]

theorem rawRowCheck2743 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form2 = rawRow2743 := by decide +kernel

def row2743 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

theorem rowCheck2743 : row2743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2743 := by decide +kernel

theorem rowEval2743 (x : Key → ℝ) : Integer.Sparse.eval row2743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck2743, Integer.Sparse.eval_collectBalanced, rawRowCheck2743]

def rawRow2744 : Integer.Sparse Key := [(key976, -2), (key976, -2), (key984, -2), (key984, 6), (key1090, 2), (key1090, 2), (key1098, 2), (key1098, -2), (key1183, -2), (key1183, -2), (key1169, -6), (key1169, 2), (key1220, 2), (key1220, 2)]

theorem rawRowCheck2744 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form3 = rawRow2744 := by decide +kernel

def row2744 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

theorem rowCheck2744 : row2744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2744 := by decide +kernel

theorem rowEval2744 (x : Key → ℝ) : Integer.Sparse.eval row2744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2744, Integer.Sparse.eval_collectBalanced, rawRowCheck2744]

def rawRow2745 : Integer.Sparse Key := [(key976, -2), (key984, -2), (key976, -2), (key984, 6), (key1090, 2), (key1098, 2), (key1090, 2), (key1183, -2), (key1098, -2), (key1183, -2), (key1169, -6), (key1220, 2), (key1169, 2), (key1220, 2)]

theorem rawRowCheck2745 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form3 = rawRow2745 := by decide +kernel

def row2745 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

theorem rowCheck2745 : row2745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2745 := by decide +kernel

theorem rowEval2745 (x : Key → ℝ) : Integer.Sparse.eval row2745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2745, Integer.Sparse.eval_collectBalanced, rawRowCheck2745]

def rawRow2746 : Integer.Sparse Key := [(key984, -2), (key976, -2), (key976, -2), (key984, 6), (key1098, 2), (key1090, 2), (key1090, 2), (key1183, -2), (key1183, -2), (key1098, -2), (key1169, -6), (key1220, 2), (key1220, 2), (key1169, 2)]

theorem rawRowCheck2746 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form3 = rawRow2746 := by decide +kernel

def row2746 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

theorem rowCheck2746 : row2746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2746 := by decide +kernel

theorem rowEval2746 (x : Key → ℝ) : Integer.Sparse.eval row2746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2746, Integer.Sparse.eval_collectBalanced, rawRowCheck2746]

def rawRow2747 : Integer.Sparse Key := [(key976, -2), (key984, -2), (key984, -2), (key976, 6), (key1180, 2), (key1183, 2), (key1183, 2), (key1090, -2), (key1090, -2), (key1180, -2), (key1220, -6), (key1169, 2), (key1169, 2), (key1220, 2)]

theorem rawRowCheck2747 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form3 = rawRow2747 := by decide +kernel

def row2747 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

theorem rowCheck2747 : row2747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2747 := by decide +kernel

theorem rowEval2747 (x : Key → ℝ) : Integer.Sparse.eval row2747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2747, Integer.Sparse.eval_collectBalanced, rawRowCheck2747]

def rawRow2748 : Integer.Sparse Key := [(key984, -2), (key976, -2), (key984, -2), (key976, 6), (key1183, 2), (key1180, 2), (key1183, 2), (key1090, -2), (key1180, -2), (key1090, -2), (key1220, -6), (key1169, 2), (key1220, 2), (key1169, 2)]

theorem rawRowCheck2748 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form3 = rawRow2748 := by decide +kernel

def row2748 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

theorem rowCheck2748 : row2748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2748 := by decide +kernel

theorem rowEval2748 (x : Key → ℝ) : Integer.Sparse.eval row2748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2748, Integer.Sparse.eval_collectBalanced, rawRowCheck2748]

def rawRow2749 : Integer.Sparse Key := [(key984, -2), (key984, -2), (key976, -2), (key976, 6), (key1183, 2), (key1183, 2), (key1180, 2), (key1180, -2), (key1090, -2), (key1090, -2), (key1220, -6), (key1220, 2), (key1169, 2), (key1169, 2)]

theorem rawRowCheck2749 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form3 = rawRow2749 := by decide +kernel

def row2749 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

theorem rowCheck2749 : row2749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2749 := by decide +kernel

theorem rowEval2749 (x : Key → ℝ) : Integer.Sparse.eval row2749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2749, Integer.Sparse.eval_collectBalanced, rawRowCheck2749]

def rawRow2750 : Integer.Sparse Key := [(key1090, -2), (key1090, -2), (key1098, -2), (key1169, 6), (key976, 2), (key976, 2), (key984, 2), (key1169, -2), (key1220, -2), (key1220, -2), (key984, -6), (key1098, 2), (key1183, 2), (key1183, 2)]

theorem rawRowCheck2750 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form3 = rawRow2750 := by decide +kernel

def row2750 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

theorem rowCheck2750 : row2750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2750 := by decide +kernel

theorem rowEval2750 (x : Key → ℝ) : Integer.Sparse.eval row2750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2750, Integer.Sparse.eval_collectBalanced, rawRowCheck2750]

def rawRow2751 : Integer.Sparse Key := [(key1090, -2), (key1098, -2), (key1090, -2), (key1169, 6), (key976, 2), (key984, 2), (key976, 2), (key1220, -2), (key1169, -2), (key1220, -2), (key984, -6), (key1183, 2), (key1098, 2), (key1183, 2)]

theorem rawRowCheck2751 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form3 = rawRow2751 := by decide +kernel

def row2751 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

theorem rowCheck2751 : row2751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2751 := by decide +kernel

theorem rowEval2751 (x : Key → ℝ) : Integer.Sparse.eval row2751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2751, Integer.Sparse.eval_collectBalanced, rawRowCheck2751]

def rawRow2752 : Integer.Sparse Key := [(key1098, -2), (key1090, -2), (key1090, -2), (key1169, 6), (key984, 2), (key976, 2), (key976, 2), (key1220, -2), (key1220, -2), (key1169, -2), (key984, -6), (key1183, 2), (key1183, 2), (key1098, 2)]

theorem rawRowCheck2752 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form3 = rawRow2752 := by decide +kernel

def row2752 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

theorem rowCheck2752 : row2752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2752 := by decide +kernel

theorem rowEval2752 (x : Key → ℝ) : Integer.Sparse.eval row2752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2752, Integer.Sparse.eval_collectBalanced, rawRowCheck2752]

def rawRow2753 : Integer.Sparse Key := [(key1090, -2), (key1098, -2), (key1169, -2), (key1090, 6), (key1180, 2), (key1183, 2), (key1220, 2), (key976, -2), (key1090, -2), (key1180, -2), (key1183, -6), (key984, 2), (key1098, 2), (key1183, 2)]

theorem rawRowCheck2753 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form3 = rawRow2753 := by decide +kernel

def row2753 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

theorem rowCheck2753 : row2753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2753 := by decide +kernel

theorem rowEval2753 (x : Key → ℝ) : Integer.Sparse.eval row2753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2753, Integer.Sparse.eval_collectBalanced, rawRowCheck2753]

def rawRow2754 : Integer.Sparse Key := [(key1098, -2), (key1090, -2), (key1169, -2), (key1090, 6), (key1183, 2), (key1180, 2), (key1220, 2), (key976, -2), (key1180, -2), (key1090, -2), (key1183, -6), (key984, 2), (key1183, 2), (key1098, 2)]

theorem rawRowCheck2754 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form3 = rawRow2754 := by decide +kernel

def row2754 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

theorem rowCheck2754 : row2754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2754 := by decide +kernel

theorem rowEval2754 (x : Key → ℝ) : Integer.Sparse.eval row2754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2754, Integer.Sparse.eval_collectBalanced, rawRowCheck2754]

def rawRow2755 : Integer.Sparse Key := [(key1090, -2), (key1169, -2), (key1098, -2), (key1090, 6), (key1180, 2), (key1220, 2), (key1183, 2), (key1090, -2), (key976, -2), (key1180, -2), (key1183, -6), (key1098, 2), (key984, 2), (key1183, 2)]

theorem rawRowCheck2755 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form3 = rawRow2755 := by decide +kernel

def row2755 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

theorem rowCheck2755 : row2755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2755 := by decide +kernel

theorem rowEval2755 (x : Key → ℝ) : Integer.Sparse.eval row2755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2755, Integer.Sparse.eval_collectBalanced, rawRowCheck2755]

def rawRow2756 : Integer.Sparse Key := [(key1169, -2), (key1090, -2), (key1098, -2), (key1090, 6), (key1220, 2), (key1180, 2), (key1183, 2), (key1090, -2), (key1180, -2), (key976, -2), (key1183, -6), (key1098, 2), (key1183, 2), (key984, 2)]

theorem rawRowCheck2756 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form3 = rawRow2756 := by decide +kernel

def row2756 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

theorem rowCheck2756 : row2756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2756 := by decide +kernel

theorem rowEval2756 (x : Key → ℝ) : Integer.Sparse.eval row2756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck2756, Integer.Sparse.eval_collectBalanced, rawRowCheck2756]

def rawRow2757 : Integer.Sparse Key := [(key1098, -2), (key1169, -2), (key1090, -2), (key1090, 6), (key1183, 2), (key1220, 2), (key1180, 2), (key1180, -2), (key976, -2), (key1090, -2), (key1183, -6), (key1183, 2), (key984, 2), (key1098, 2)]

theorem rawRowCheck2757 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form3 = rawRow2757 := by decide +kernel

def row2757 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

theorem rowCheck2757 : row2757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2757 := by decide +kernel

theorem rowEval2757 (x : Key → ℝ) : Integer.Sparse.eval row2757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2757, Integer.Sparse.eval_collectBalanced, rawRowCheck2757]

def rawRow2758 : Integer.Sparse Key := [(key1169, -2), (key1098, -2), (key1090, -2), (key1090, 6), (key1220, 2), (key1183, 2), (key1180, 2), (key1180, -2), (key1090, -2), (key976, -2), (key1183, -6), (key1183, 2), (key1098, 2), (key984, 2)]

theorem rawRowCheck2758 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form3 = rawRow2758 := by decide +kernel

def row2758 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

theorem rowCheck2758 : row2758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2758 := by decide +kernel

theorem rowEval2758 (x : Key → ℝ) : Integer.Sparse.eval row2758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck2758, Integer.Sparse.eval_collectBalanced, rawRowCheck2758]

def rawRow2759 : Integer.Sparse Key := [(key1180, -2), (key1183, -2), (key1183, -2), (key1220, 6), (key976, 2), (key984, 2), (key984, 2), (key1169, -2), (key1169, -2), (key1220, -2), (key976, -6), (key1090, 2), (key1090, 2), (key1180, 2)]

theorem rawRowCheck2759 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form3 = rawRow2759 := by decide +kernel

def row2759 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

theorem rowCheck2759 : row2759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2759 := by decide +kernel

theorem rowEval2759 (x : Key → ℝ) : Integer.Sparse.eval row2759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2759, Integer.Sparse.eval_collectBalanced, rawRowCheck2759]

def rawRow2760 : Integer.Sparse Key := [(key1183, -2), (key1180, -2), (key1183, -2), (key1220, 6), (key984, 2), (key976, 2), (key984, 2), (key1169, -2), (key1220, -2), (key1169, -2), (key976, -6), (key1090, 2), (key1180, 2), (key1090, 2)]

theorem rawRowCheck2760 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form3 = rawRow2760 := by decide +kernel

def row2760 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

theorem rowCheck2760 : row2760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2760 := by decide +kernel

theorem rowEval2760 (x : Key → ℝ) : Integer.Sparse.eval row2760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2760, Integer.Sparse.eval_collectBalanced, rawRowCheck2760]

def rawRow2761 : Integer.Sparse Key := [(key1183, -2), (key1183, -2), (key1180, -2), (key1220, 6), (key984, 2), (key984, 2), (key976, 2), (key1220, -2), (key1169, -2), (key1169, -2), (key976, -6), (key1180, 2), (key1090, 2), (key1090, 2)]

theorem rawRowCheck2761 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form3 = rawRow2761 := by decide +kernel

def row2761 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

theorem rowCheck2761 : row2761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2761 := by decide +kernel

theorem rowEval2761 (x : Key → ℝ) : Integer.Sparse.eval row2761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2761, Integer.Sparse.eval_collectBalanced, rawRowCheck2761]

def rawRow2762 : Integer.Sparse Key := [(key1180, -2), (key1183, -2), (key1220, -2), (key1183, 6), (key1090, 2), (key1098, 2), (key1169, 2), (key984, -2), (key1098, -2), (key1183, -2), (key1090, -6), (key976, 2), (key1090, 2), (key1180, 2)]

theorem rawRowCheck2762 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form3 = rawRow2762 := by decide +kernel

def row2762 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

theorem rowCheck2762 : row2762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2762 := by decide +kernel

theorem rowEval2762 (x : Key → ℝ) : Integer.Sparse.eval row2762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2762, Integer.Sparse.eval_collectBalanced, rawRowCheck2762]

def rawRow2763 : Integer.Sparse Key := [(key1183, -2), (key1180, -2), (key1220, -2), (key1183, 6), (key1098, 2), (key1090, 2), (key1169, 2), (key984, -2), (key1183, -2), (key1098, -2), (key1090, -6), (key976, 2), (key1180, 2), (key1090, 2)]

theorem rawRowCheck2763 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form3 = rawRow2763 := by decide +kernel

def row2763 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

theorem rowCheck2763 : row2763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2763 := by decide +kernel

theorem rowEval2763 (x : Key → ℝ) : Integer.Sparse.eval row2763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2763, Integer.Sparse.eval_collectBalanced, rawRowCheck2763]

def rawRow2764 : Integer.Sparse Key := [(key1180, -2), (key1220, -2), (key1183, -2), (key1183, 6), (key1090, 2), (key1169, 2), (key1098, 2), (key1098, -2), (key984, -2), (key1183, -2), (key1090, -6), (key1090, 2), (key976, 2), (key1180, 2)]

theorem rawRowCheck2764 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form3 = rawRow2764 := by decide +kernel

def row2764 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

theorem rowCheck2764 : row2764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2764 := by decide +kernel

theorem rowEval2764 (x : Key → ℝ) : Integer.Sparse.eval row2764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2764, Integer.Sparse.eval_collectBalanced, rawRowCheck2764]

def rawRow2765 : Integer.Sparse Key := [(key1220, -2), (key1180, -2), (key1183, -2), (key1183, 6), (key1169, 2), (key1090, 2), (key1098, 2), (key1098, -2), (key1183, -2), (key984, -2), (key1090, -6), (key1090, 2), (key1180, 2), (key976, 2)]

theorem rawRowCheck2765 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form3 = rawRow2765 := by decide +kernel

def row2765 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

theorem rowCheck2765 : row2765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2765 := by decide +kernel

theorem rowEval2765 (x : Key → ℝ) : Integer.Sparse.eval row2765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck2765, Integer.Sparse.eval_collectBalanced, rawRowCheck2765]

def rawRow2766 : Integer.Sparse Key := [(key1183, -2), (key1220, -2), (key1180, -2), (key1183, 6), (key1098, 2), (key1169, 2), (key1090, 2), (key1183, -2), (key984, -2), (key1098, -2), (key1090, -6), (key1180, 2), (key976, 2), (key1090, 2)]

theorem rawRowCheck2766 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form3 = rawRow2766 := by decide +kernel

def row2766 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

theorem rowCheck2766 : row2766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2766 := by decide +kernel

theorem rowEval2766 (x : Key → ℝ) : Integer.Sparse.eval row2766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2766, Integer.Sparse.eval_collectBalanced, rawRowCheck2766]

def rawRow2767 : Integer.Sparse Key := [(key1220, -2), (key1183, -2), (key1180, -2), (key1183, 6), (key1169, 2), (key1098, 2), (key1090, 2), (key1183, -2), (key1098, -2), (key984, -2), (key1090, -6), (key1180, 2), (key1090, 2), (key976, 2)]

theorem rawRowCheck2767 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form3 = rawRow2767 := by decide +kernel

def row2767 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

theorem rowCheck2767 : row2767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2767 := by decide +kernel

theorem rowEval2767 (x : Key → ℝ) : Integer.Sparse.eval row2767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck2767, Integer.Sparse.eval_collectBalanced, rawRowCheck2767]

def rawRow2768 : Integer.Sparse Key := [(key2377, -6), (key2377, 2), (key2389, 2), (key2389, 2), (key2405, 6), (key2405, -2), (key2436, -2), (key2436, -2), (key2471, -2), (key2479, -2), (key2479, -2), (key2471, 2), (key2502, 2), (key2502, 2)]

theorem rawRowCheck2768 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form4 = rawRow2768 := by decide +kernel

def row2768 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

theorem rowCheck2768 : row2768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2768 := by decide +kernel

theorem rowEval2768 (x : Key → ℝ) : Integer.Sparse.eval row2768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2768, Integer.Sparse.eval_collectBalanced, rawRowCheck2768]

def rawRow2769 : Integer.Sparse Key := [(key2377, -6), (key2389, 2), (key2377, 2), (key2389, 2), (key2405, 6), (key2436, -2), (key2405, -2), (key2436, -2), (key2479, -2), (key2471, -2), (key2479, -2), (key2502, 2), (key2471, 2), (key2502, 2)]

theorem rawRowCheck2769 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form4 = rawRow2769 := by decide +kernel

def row2769 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

theorem rowCheck2769 : row2769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2769 := by decide +kernel

theorem rowEval2769 (x : Key → ℝ) : Integer.Sparse.eval row2769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2769, Integer.Sparse.eval_collectBalanced, rawRowCheck2769]

def rawRow2770 : Integer.Sparse Key := [(key2377, -6), (key2389, 2), (key2389, 2), (key2377, 2), (key2405, 6), (key2436, -2), (key2436, -2), (key2405, -2), (key2479, -2), (key2479, -2), (key2471, -2), (key2502, 2), (key2502, 2), (key2471, 2)]

theorem rawRowCheck2770 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form4 = rawRow2770 := by decide +kernel

def row2770 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

theorem rowCheck2770 : row2770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2770 := by decide +kernel

theorem rowEval2770 (x : Key → ℝ) : Integer.Sparse.eval row2770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2770, Integer.Sparse.eval_collectBalanced, rawRowCheck2770]

def rawRow2771 : Integer.Sparse Key := [(key2389, -6), (key2377, 2), (key2377, 2), (key2389, 2), (key2436, 6), (key2405, -2), (key2405, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2479, 2), (key2479, 2), (key2518, 2)]

theorem rawRowCheck2771 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form4 = rawRow2771 := by decide +kernel

def row2771 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

theorem rowCheck2771 : row2771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2771 := by decide +kernel

theorem rowEval2771 (x : Key → ℝ) : Integer.Sparse.eval row2771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2771, Integer.Sparse.eval_collectBalanced, rawRowCheck2771]

def rawRow2772 : Integer.Sparse Key := [(key2389, -6), (key2377, 2), (key2389, 2), (key2377, 2), (key2436, 6), (key2405, -2), (key2436, -2), (key2405, -2), (key2502, -2), (key2518, -2), (key2502, -2), (key2479, 2), (key2518, 2), (key2479, 2)]

theorem rawRowCheck2772 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form4 = rawRow2772 := by decide +kernel

def row2772 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

theorem rowCheck2772 : row2772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2772 := by decide +kernel

theorem rowEval2772 (x : Key → ℝ) : Integer.Sparse.eval row2772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2772, Integer.Sparse.eval_collectBalanced, rawRowCheck2772]

def rawRow2773 : Integer.Sparse Key := [(key2389, -6), (key2389, 2), (key2377, 2), (key2377, 2), (key2436, 6), (key2436, -2), (key2405, -2), (key2405, -2), (key2518, -2), (key2502, -2), (key2502, -2), (key2518, 2), (key2479, 2), (key2479, 2)]

theorem rawRowCheck2773 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form4 = rawRow2773 := by decide +kernel

def row2773 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

theorem rowCheck2773 : row2773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2773 := by decide +kernel

theorem rowEval2773 (x : Key → ℝ) : Integer.Sparse.eval row2773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2773, Integer.Sparse.eval_collectBalanced, rawRowCheck2773]

def rawRow2774 : Integer.Sparse Key := [(key2405, -6), (key2471, 2), (key2479, 2), (key2479, 2), (key2377, 6), (key2471, -2), (key2502, -2), (key2502, -2), (key2377, -2), (key2389, -2), (key2389, -2), (key2405, 2), (key2436, 2), (key2436, 2)]

theorem rawRowCheck2774 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form4 = rawRow2774 := by decide +kernel

def row2774 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

theorem rowCheck2774 : row2774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2774 := by decide +kernel

theorem rowEval2774 (x : Key → ℝ) : Integer.Sparse.eval row2774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2774, Integer.Sparse.eval_collectBalanced, rawRowCheck2774]

def rawRow2775 : Integer.Sparse Key := [(key2405, -6), (key2479, 2), (key2471, 2), (key2479, 2), (key2377, 6), (key2502, -2), (key2471, -2), (key2502, -2), (key2389, -2), (key2377, -2), (key2389, -2), (key2436, 2), (key2405, 2), (key2436, 2)]

theorem rawRowCheck2775 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form4 = rawRow2775 := by decide +kernel

def row2775 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

theorem rowCheck2775 : row2775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2775 := by decide +kernel

theorem rowEval2775 (x : Key → ℝ) : Integer.Sparse.eval row2775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2775, Integer.Sparse.eval_collectBalanced, rawRowCheck2775]

def rawRow2776 : Integer.Sparse Key := [(key2405, -6), (key2479, 2), (key2479, 2), (key2471, 2), (key2377, 6), (key2502, -2), (key2502, -2), (key2471, -2), (key2389, -2), (key2389, -2), (key2377, -2), (key2436, 2), (key2436, 2), (key2405, 2)]

theorem rawRowCheck2776 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form4 = rawRow2776 := by decide +kernel

def row2776 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

theorem rowCheck2776 : row2776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2776 := by decide +kernel

theorem rowEval2776 (x : Key → ℝ) : Integer.Sparse.eval row2776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2776, Integer.Sparse.eval_collectBalanced, rawRowCheck2776]

def rawRow2777 : Integer.Sparse Key := [(key2479, -6), (key2405, 2), (key2471, 2), (key2479, 2), (key2502, 6), (key2377, -2), (key2471, -2), (key2502, -2), (key2436, -2), (key2502, -2), (key2518, -2), (key2389, 2), (key2479, 2), (key2518, 2)]

theorem rawRowCheck2777 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form4 = rawRow2777 := by decide +kernel

def row2777 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

theorem rowCheck2777 : row2777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2777 := by decide +kernel

theorem rowEval2777 (x : Key → ℝ) : Integer.Sparse.eval row2777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2777, Integer.Sparse.eval_collectBalanced, rawRowCheck2777]

def rawRow2778 : Integer.Sparse Key := [(key2479, -6), (key2405, 2), (key2479, 2), (key2471, 2), (key2502, 6), (key2377, -2), (key2502, -2), (key2471, -2), (key2436, -2), (key2518, -2), (key2502, -2), (key2389, 2), (key2518, 2), (key2479, 2)]

theorem rawRowCheck2778 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form4 = rawRow2778 := by decide +kernel

def row2778 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

theorem rowCheck2778 : row2778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2778 := by decide +kernel

theorem rowEval2778 (x : Key → ℝ) : Integer.Sparse.eval row2778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2778, Integer.Sparse.eval_collectBalanced, rawRowCheck2778]

def rawRow2779 : Integer.Sparse Key := [(key2479, -6), (key2471, 2), (key2405, 2), (key2479, 2), (key2502, 6), (key2471, -2), (key2377, -2), (key2502, -2), (key2502, -2), (key2436, -2), (key2518, -2), (key2479, 2), (key2389, 2), (key2518, 2)]

theorem rawRowCheck2779 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form4 = rawRow2779 := by decide +kernel

def row2779 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

theorem rowCheck2779 : row2779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2779 := by decide +kernel

theorem rowEval2779 (x : Key → ℝ) : Integer.Sparse.eval row2779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2779, Integer.Sparse.eval_collectBalanced, rawRowCheck2779]

def rawRow2780 : Integer.Sparse Key := [(key2479, -6), (key2471, 2), (key2479, 2), (key2405, 2), (key2502, 6), (key2471, -2), (key2502, -2), (key2377, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2479, 2), (key2518, 2), (key2389, 2)]

theorem rawRowCheck2780 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form4 = rawRow2780 := by decide +kernel

def row2780 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

theorem rowCheck2780 : row2780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2780 := by decide +kernel

theorem rowEval2780 (x : Key → ℝ) : Integer.Sparse.eval row2780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck2780, Integer.Sparse.eval_collectBalanced, rawRowCheck2780]

def rawRow2781 : Integer.Sparse Key := [(key2479, -6), (key2479, 2), (key2405, 2), (key2471, 2), (key2502, 6), (key2502, -2), (key2377, -2), (key2471, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2518, 2), (key2389, 2), (key2479, 2)]

theorem rawRowCheck2781 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form4 = rawRow2781 := by decide +kernel

def row2781 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

theorem rowCheck2781 : row2781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2781 := by decide +kernel

theorem rowEval2781 (x : Key → ℝ) : Integer.Sparse.eval row2781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2781, Integer.Sparse.eval_collectBalanced, rawRowCheck2781]

def rawRow2782 : Integer.Sparse Key := [(key2479, -6), (key2479, 2), (key2471, 2), (key2405, 2), (key2502, 6), (key2502, -2), (key2471, -2), (key2377, -2), (key2518, -2), (key2502, -2), (key2436, -2), (key2518, 2), (key2479, 2), (key2389, 2)]

theorem rawRowCheck2782 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form4 = rawRow2782 := by decide +kernel

def row2782 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

theorem rowCheck2782 : row2782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2782 := by decide +kernel

theorem rowEval2782 (x : Key → ℝ) : Integer.Sparse.eval row2782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck2782, Integer.Sparse.eval_collectBalanced, rawRowCheck2782]

def rawRow2783 : Integer.Sparse Key := [(key2436, -6), (key2502, 2), (key2502, 2), (key2518, 2), (key2389, 6), (key2479, -2), (key2479, -2), (key2518, -2), (key2377, -2), (key2377, -2), (key2389, -2), (key2405, 2), (key2405, 2), (key2436, 2)]

theorem rawRowCheck2783 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form4 = rawRow2783 := by decide +kernel

def row2783 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

theorem rowCheck2783 : row2783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2783 := by decide +kernel

theorem rowEval2783 (x : Key → ℝ) : Integer.Sparse.eval row2783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2783, Integer.Sparse.eval_collectBalanced, rawRowCheck2783]

def rawRow2784 : Integer.Sparse Key := [(key2436, -6), (key2502, 2), (key2518, 2), (key2502, 2), (key2389, 6), (key2479, -2), (key2518, -2), (key2479, -2), (key2377, -2), (key2389, -2), (key2377, -2), (key2405, 2), (key2436, 2), (key2405, 2)]

theorem rawRowCheck2784 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form4 = rawRow2784 := by decide +kernel

def row2784 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

theorem rowCheck2784 : row2784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2784 := by decide +kernel

theorem rowEval2784 (x : Key → ℝ) : Integer.Sparse.eval row2784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2784, Integer.Sparse.eval_collectBalanced, rawRowCheck2784]

def rawRow2785 : Integer.Sparse Key := [(key2436, -6), (key2518, 2), (key2502, 2), (key2502, 2), (key2389, 6), (key2518, -2), (key2479, -2), (key2479, -2), (key2389, -2), (key2377, -2), (key2377, -2), (key2436, 2), (key2405, 2), (key2405, 2)]

theorem rawRowCheck2785 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form4 = rawRow2785 := by decide +kernel

def row2785 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

theorem rowCheck2785 : row2785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2785 := by decide +kernel

theorem rowEval2785 (x : Key → ℝ) : Integer.Sparse.eval row2785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2785, Integer.Sparse.eval_collectBalanced, rawRowCheck2785]

def rawRow2786 : Integer.Sparse Key := [(key2502, -6), (key2436, 2), (key2502, 2), (key2518, 2), (key2479, 6), (key2389, -2), (key2479, -2), (key2518, -2), (key2405, -2), (key2471, -2), (key2479, -2), (key2377, 2), (key2471, 2), (key2502, 2)]

theorem rawRowCheck2786 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form4 = rawRow2786 := by decide +kernel

def row2786 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

theorem rowCheck2786 : row2786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2786 := by decide +kernel

theorem rowEval2786 (x : Key → ℝ) : Integer.Sparse.eval row2786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2786, Integer.Sparse.eval_collectBalanced, rawRowCheck2786]

def rawRow2787 : Integer.Sparse Key := [(key2502, -6), (key2436, 2), (key2518, 2), (key2502, 2), (key2479, 6), (key2389, -2), (key2518, -2), (key2479, -2), (key2405, -2), (key2479, -2), (key2471, -2), (key2377, 2), (key2502, 2), (key2471, 2)]

theorem rawRowCheck2787 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form4 = rawRow2787 := by decide +kernel

def row2787 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

theorem rowCheck2787 : row2787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2787 := by decide +kernel

theorem rowEval2787 (x : Key → ℝ) : Integer.Sparse.eval row2787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2787, Integer.Sparse.eval_collectBalanced, rawRowCheck2787]

def rawRow2788 : Integer.Sparse Key := [(key2502, -6), (key2502, 2), (key2436, 2), (key2518, 2), (key2479, 6), (key2479, -2), (key2389, -2), (key2518, -2), (key2471, -2), (key2405, -2), (key2479, -2), (key2471, 2), (key2377, 2), (key2502, 2)]

theorem rawRowCheck2788 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form4 = rawRow2788 := by decide +kernel

def row2788 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

theorem rowCheck2788 : row2788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2788 := by decide +kernel

theorem rowEval2788 (x : Key → ℝ) : Integer.Sparse.eval row2788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2788, Integer.Sparse.eval_collectBalanced, rawRowCheck2788]

def rawRow2789 : Integer.Sparse Key := [(key2502, -6), (key2502, 2), (key2518, 2), (key2436, 2), (key2479, 6), (key2479, -2), (key2518, -2), (key2389, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2471, 2), (key2502, 2), (key2377, 2)]

theorem rawRowCheck2789 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form4 = rawRow2789 := by decide +kernel

def row2789 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

theorem rowCheck2789 : row2789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2789 := by decide +kernel

theorem rowEval2789 (x : Key → ℝ) : Integer.Sparse.eval row2789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck2789, Integer.Sparse.eval_collectBalanced, rawRowCheck2789]

def rawRow2790 : Integer.Sparse Key := [(key2502, -6), (key2518, 2), (key2436, 2), (key2502, 2), (key2479, 6), (key2518, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, 2), (key2377, 2), (key2471, 2)]

theorem rawRowCheck2790 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form4 = rawRow2790 := by decide +kernel

def row2790 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

theorem rowCheck2790 : row2790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2790 := by decide +kernel

theorem rowEval2790 (x : Key → ℝ) : Integer.Sparse.eval row2790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2790, Integer.Sparse.eval_collectBalanced, rawRowCheck2790]

def rawRow2791 : Integer.Sparse Key := [(key2502, -6), (key2518, 2), (key2502, 2), (key2436, 2), (key2479, 6), (key2518, -2), (key2479, -2), (key2389, -2), (key2479, -2), (key2471, -2), (key2405, -2), (key2502, 2), (key2471, 2), (key2377, 2)]

theorem rawRowCheck2791 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form4 = rawRow2791 := by decide +kernel

def row2791 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

theorem rowCheck2791 : row2791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2791 := by decide +kernel

theorem rowEval2791 (x : Key → ℝ) : Integer.Sparse.eval row2791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck2791, Integer.Sparse.eval_collectBalanced, rawRowCheck2791]

def rawRow2792 : Integer.Sparse Key := [(key1531, -1), (key1531, -1), (key1765, -1), (key1765, -1), (key1768, -1), (key1768, -1), (key1536, 2), (key1768, 2), (key1768, 2), (key1609, 1), (key1609, 1), (key1806, 1), (key1806, 1), (key1809, 1), (key1809, 1), (key1651, -1), (key1651, -1), (key1809, -1), (key1809, -1), (key1837, -1), (key1837, -1), (key1642, -2), (key1832, -2), (key1832, -2), (key1674, 1), (key1674, 1), (key1832, 1), (key1832, 1), (key1848, 1), (key1848, 1)]

theorem rawRowCheck2792 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form5 = rawRow2792 := by decide +kernel

def row2792 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

theorem rowCheck2792 : row2792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2792 := by decide +kernel

theorem rowEval2792 (x : Key → ℝ) : Integer.Sparse.eval row2792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2792, Integer.Sparse.eval_collectBalanced, rawRowCheck2792]

def rawRow2793 : Integer.Sparse Key := [(key1765, -1), (key1768, -1), (key1531, -1), (key1768, -1), (key1531, -1), (key1765, -1), (key1768, 2), (key1536, 2), (key1768, 2), (key1806, 1), (key1809, 1), (key1609, 1), (key1809, 1), (key1609, 1), (key1806, 1), (key1809, -1), (key1837, -1), (key1651, -1), (key1837, -1), (key1651, -1), (key1809, -1), (key1832, -2), (key1642, -2), (key1832, -2), (key1832, 1), (key1848, 1), (key1674, 1), (key1848, 1), (key1674, 1), (key1832, 1)]

theorem rawRowCheck2793 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form5 = rawRow2793 := by decide +kernel

def row2793 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

theorem rowCheck2793 : row2793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2793 := by decide +kernel

theorem rowEval2793 (x : Key → ℝ) : Integer.Sparse.eval row2793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2793, Integer.Sparse.eval_collectBalanced, rawRowCheck2793]

def rawRow2794 : Integer.Sparse Key := [(key1768, -1), (key1765, -1), (key1768, -1), (key1531, -1), (key1765, -1), (key1531, -1), (key1768, 2), (key1768, 2), (key1536, 2), (key1809, 1), (key1806, 1), (key1809, 1), (key1609, 1), (key1806, 1), (key1609, 1), (key1837, -1), (key1809, -1), (key1837, -1), (key1651, -1), (key1809, -1), (key1651, -1), (key1832, -2), (key1832, -2), (key1642, -2), (key1848, 1), (key1832, 1), (key1848, 1), (key1674, 1), (key1832, 1), (key1674, 1)]

theorem rawRowCheck2794 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form5 = rawRow2794 := by decide +kernel

def row2794 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

theorem rowCheck2794 : row2794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2794 := by decide +kernel

theorem rowEval2794 (x : Key → ℝ) : Integer.Sparse.eval row2794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2794, Integer.Sparse.eval_collectBalanced, rawRowCheck2794]

def rawRow2795 : Integer.Sparse Key := [(key1531, -1), (key1536, -1), (key1531, -1), (key1768, -1), (key1536, -1), (key1768, -1), (key1531, 2), (key1531, 2), (key1765, 2), (key1648, 1), (key1651, 1), (key1648, 1), (key1837, 1), (key1651, 1), (key1837, 1), (key1609, -1), (key1648, -1), (key1609, -1), (key1806, -1), (key1648, -1), (key1806, -1), (key1674, -2), (key1674, -2), (key1848, -2), (key1642, 1), (key1674, 1), (key1642, 1), (key1832, 1), (key1674, 1), (key1832, 1)]

theorem rawRowCheck2795 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form5 = rawRow2795 := by decide +kernel

def row2795 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

theorem rowCheck2795 : row2795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2795 := by decide +kernel

theorem rowEval2795 (x : Key → ℝ) : Integer.Sparse.eval row2795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2795, Integer.Sparse.eval_collectBalanced, rawRowCheck2795]

def rawRow2796 : Integer.Sparse Key := [(key1536, -1), (key1531, -1), (key1768, -1), (key1531, -1), (key1768, -1), (key1536, -1), (key1531, 2), (key1765, 2), (key1531, 2), (key1651, 1), (key1648, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1651, 1), (key1648, -1), (key1609, -1), (key1806, -1), (key1609, -1), (key1806, -1), (key1648, -1), (key1674, -2), (key1848, -2), (key1674, -2), (key1674, 1), (key1642, 1), (key1832, 1), (key1642, 1), (key1832, 1), (key1674, 1)]

theorem rawRowCheck2796 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form5 = rawRow2796 := by decide +kernel

def row2796 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

theorem rowCheck2796 : row2796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2796 := by decide +kernel

theorem rowEval2796 (x : Key → ℝ) : Integer.Sparse.eval row2796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2796, Integer.Sparse.eval_collectBalanced, rawRowCheck2796]

def rawRow2797 : Integer.Sparse Key := [(key1768, -1), (key1768, -1), (key1536, -1), (key1536, -1), (key1531, -1), (key1531, -1), (key1765, 2), (key1531, 2), (key1531, 2), (key1837, 1), (key1837, 1), (key1651, 1), (key1651, 1), (key1648, 1), (key1648, 1), (key1806, -1), (key1806, -1), (key1648, -1), (key1648, -1), (key1609, -1), (key1609, -1), (key1848, -2), (key1674, -2), (key1674, -2), (key1832, 1), (key1832, 1), (key1674, 1), (key1674, 1), (key1642, 1), (key1642, 1)]

theorem rawRowCheck2797 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form5 = rawRow2797 := by decide +kernel

def row2797 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

theorem rowCheck2797 : row2797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2797 := by decide +kernel

theorem rowEval2797 (x : Key → ℝ) : Integer.Sparse.eval row2797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2797, Integer.Sparse.eval_collectBalanced, rawRowCheck2797]

def rawRow2798 : Integer.Sparse Key := [(key1609, -1), (key1609, -1), (key1806, -1), (key1806, -1), (key1809, -1), (key1809, -1), (key1642, 2), (key1832, 2), (key1832, 2), (key1531, 1), (key1531, 1), (key1765, 1), (key1765, 1), (key1768, 1), (key1768, 1), (key1674, -1), (key1674, -1), (key1832, -1), (key1832, -1), (key1848, -1), (key1848, -1), (key1536, -2), (key1768, -2), (key1768, -2), (key1651, 1), (key1651, 1), (key1809, 1), (key1809, 1), (key1837, 1), (key1837, 1)]

theorem rawRowCheck2798 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form5 = rawRow2798 := by decide +kernel

def row2798 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

theorem rowCheck2798 : row2798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2798 := by decide +kernel

theorem rowEval2798 (x : Key → ℝ) : Integer.Sparse.eval row2798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2798, Integer.Sparse.eval_collectBalanced, rawRowCheck2798]

def rawRow2799 : Integer.Sparse Key := [(key1806, -1), (key1809, -1), (key1609, -1), (key1809, -1), (key1609, -1), (key1806, -1), (key1832, 2), (key1642, 2), (key1832, 2), (key1765, 1), (key1768, 1), (key1531, 1), (key1768, 1), (key1531, 1), (key1765, 1), (key1832, -1), (key1848, -1), (key1674, -1), (key1848, -1), (key1674, -1), (key1832, -1), (key1768, -2), (key1536, -2), (key1768, -2), (key1809, 1), (key1837, 1), (key1651, 1), (key1837, 1), (key1651, 1), (key1809, 1)]

theorem rawRowCheck2799 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form5 = rawRow2799 := by decide +kernel

def row2799 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

theorem rowCheck2799 : row2799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2799 := by decide +kernel

theorem rowEval2799 (x : Key → ℝ) : Integer.Sparse.eval row2799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2799, Integer.Sparse.eval_collectBalanced, rawRowCheck2799]

def rawRow2800 : Integer.Sparse Key := [(key1809, -1), (key1806, -1), (key1809, -1), (key1609, -1), (key1806, -1), (key1609, -1), (key1832, 2), (key1832, 2), (key1642, 2), (key1768, 1), (key1765, 1), (key1768, 1), (key1531, 1), (key1765, 1), (key1531, 1), (key1848, -1), (key1832, -1), (key1848, -1), (key1674, -1), (key1832, -1), (key1674, -1), (key1768, -2), (key1768, -2), (key1536, -2), (key1837, 1), (key1809, 1), (key1837, 1), (key1651, 1), (key1809, 1), (key1651, 1)]

theorem rawRowCheck2800 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form5 = rawRow2800 := by decide +kernel

def row2800 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

theorem rowCheck2800 : row2800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2800 := by decide +kernel

theorem rowEval2800 (x : Key → ℝ) : Integer.Sparse.eval row2800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2800, Integer.Sparse.eval_collectBalanced, rawRowCheck2800]

def rawRow2801 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1609, -1), (key1809, -1), (key1642, -1), (key1832, -1), (key1256, 2), (key1609, 2), (key1806, 2), (key1265, 1), (key1268, 1), (key1648, 1), (key1837, 1), (key1674, 1), (key1848, 1), (key1256, -1), (key1265, -1), (key1531, -1), (key1765, -1), (key1648, -1), (key1806, -1), (key1268, -2), (key1651, -2), (key1837, -2), (key1261, 1), (key1268, 1), (key1536, 1), (key1768, 1), (key1651, 1), (key1809, 1)]

theorem rawRowCheck2801 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form5 = rawRow2801 := by decide +kernel

def row2801 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

theorem rowCheck2801 : row2801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2801 := by decide +kernel

theorem rowEval2801 (x : Key → ℝ) : Integer.Sparse.eval row2801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2801, Integer.Sparse.eval_collectBalanced, rawRowCheck2801]

def rawRow2802 : Integer.Sparse Key := [(key1261, -1), (key1256, -1), (key1809, -1), (key1609, -1), (key1832, -1), (key1642, -1), (key1256, 2), (key1806, 2), (key1609, 2), (key1268, 1), (key1265, 1), (key1837, 1), (key1648, 1), (key1848, 1), (key1674, 1), (key1265, -1), (key1256, -1), (key1765, -1), (key1531, -1), (key1806, -1), (key1648, -1), (key1268, -2), (key1837, -2), (key1651, -2), (key1268, 1), (key1261, 1), (key1768, 1), (key1536, 1), (key1809, 1), (key1651, 1)]

theorem rawRowCheck2802 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form5 = rawRow2802 := by decide +kernel

def row2802 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

theorem rowCheck2802 : row2802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2802 := by decide +kernel

theorem rowEval2802 (x : Key → ℝ) : Integer.Sparse.eval row2802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2802, Integer.Sparse.eval_collectBalanced, rawRowCheck2802]

def rawRow2803 : Integer.Sparse Key := [(key1609, -1), (key1642, -1), (key1256, -1), (key1832, -1), (key1261, -1), (key1809, -1), (key1609, 2), (key1256, 2), (key1806, 2), (key1648, 1), (key1674, 1), (key1265, 1), (key1848, 1), (key1268, 1), (key1837, 1), (key1531, -1), (key1648, -1), (key1256, -1), (key1806, -1), (key1265, -1), (key1765, -1), (key1651, -2), (key1268, -2), (key1837, -2), (key1536, 1), (key1651, 1), (key1261, 1), (key1809, 1), (key1268, 1), (key1768, 1)]

theorem rawRowCheck2803 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form5 = rawRow2803 := by decide +kernel

def row2803 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

theorem rowCheck2803 : row2803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2803 := by decide +kernel

theorem rowEval2803 (x : Key → ℝ) : Integer.Sparse.eval row2803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2803, Integer.Sparse.eval_collectBalanced, rawRowCheck2803]

def rawRow2804 : Integer.Sparse Key := [(key1642, -1), (key1609, -1), (key1832, -1), (key1256, -1), (key1809, -1), (key1261, -1), (key1609, 2), (key1806, 2), (key1256, 2), (key1674, 1), (key1648, 1), (key1848, 1), (key1265, 1), (key1837, 1), (key1268, 1), (key1648, -1), (key1531, -1), (key1806, -1), (key1256, -1), (key1765, -1), (key1265, -1), (key1651, -2), (key1837, -2), (key1268, -2), (key1651, 1), (key1536, 1), (key1809, 1), (key1261, 1), (key1768, 1), (key1268, 1)]

theorem rawRowCheck2804 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form5 = rawRow2804 := by decide +kernel

def row2804 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

theorem rowCheck2804 : row2804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2804 := by decide +kernel

theorem rowEval2804 (x : Key → ℝ) : Integer.Sparse.eval row2804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck2804, Integer.Sparse.eval_collectBalanced, rawRowCheck2804]

def rawRow2805 : Integer.Sparse Key := [(key1809, -1), (key1832, -1), (key1261, -1), (key1642, -1), (key1256, -1), (key1609, -1), (key1806, 2), (key1256, 2), (key1609, 2), (key1837, 1), (key1848, 1), (key1268, 1), (key1674, 1), (key1265, 1), (key1648, 1), (key1765, -1), (key1806, -1), (key1265, -1), (key1648, -1), (key1256, -1), (key1531, -1), (key1837, -2), (key1268, -2), (key1651, -2), (key1768, 1), (key1809, 1), (key1268, 1), (key1651, 1), (key1261, 1), (key1536, 1)]

theorem rawRowCheck2805 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form5 = rawRow2805 := by decide +kernel

def row2805 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

theorem rowCheck2805 : row2805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2805 := by decide +kernel

theorem rowEval2805 (x : Key → ℝ) : Integer.Sparse.eval row2805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2805, Integer.Sparse.eval_collectBalanced, rawRowCheck2805]

def rawRow2806 : Integer.Sparse Key := [(key1832, -1), (key1809, -1), (key1642, -1), (key1261, -1), (key1609, -1), (key1256, -1), (key1806, 2), (key1609, 2), (key1256, 2), (key1848, 1), (key1837, 1), (key1674, 1), (key1268, 1), (key1648, 1), (key1265, 1), (key1806, -1), (key1765, -1), (key1648, -1), (key1265, -1), (key1531, -1), (key1256, -1), (key1837, -2), (key1651, -2), (key1268, -2), (key1809, 1), (key1768, 1), (key1651, 1), (key1268, 1), (key1536, 1), (key1261, 1)]

theorem rawRowCheck2806 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form5 = rawRow2806 := by decide +kernel

def row2806 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

theorem rowCheck2806 : row2806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2806 := by decide +kernel

theorem rowEval2806 (x : Key → ℝ) : Integer.Sparse.eval row2806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck2806, Integer.Sparse.eval_collectBalanced, rawRowCheck2806]

def rawRow2807 : Integer.Sparse Key := [(key1648, -1), (key1651, -1), (key1648, -1), (key1837, -1), (key1651, -1), (key1837, -1), (key1674, 2), (key1674, 2), (key1848, 2), (key1531, 1), (key1536, 1), (key1531, 1), (key1768, 1), (key1536, 1), (key1768, 1), (key1642, -1), (key1674, -1), (key1642, -1), (key1832, -1), (key1674, -1), (key1832, -1), (key1531, -2), (key1531, -2), (key1765, -2), (key1609, 1), (key1648, 1), (key1609, 1), (key1806, 1), (key1648, 1), (key1806, 1)]

theorem rawRowCheck2807 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form5 = rawRow2807 := by decide +kernel

def row2807 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

theorem rowCheck2807 : row2807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2807 := by decide +kernel

theorem rowEval2807 (x : Key → ℝ) : Integer.Sparse.eval row2807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2807, Integer.Sparse.eval_collectBalanced, rawRowCheck2807]

def rawRow2808 : Integer.Sparse Key := [(key1651, -1), (key1648, -1), (key1837, -1), (key1648, -1), (key1837, -1), (key1651, -1), (key1674, 2), (key1848, 2), (key1674, 2), (key1536, 1), (key1531, 1), (key1768, 1), (key1531, 1), (key1768, 1), (key1536, 1), (key1674, -1), (key1642, -1), (key1832, -1), (key1642, -1), (key1832, -1), (key1674, -1), (key1531, -2), (key1765, -2), (key1531, -2), (key1648, 1), (key1609, 1), (key1806, 1), (key1609, 1), (key1806, 1), (key1648, 1)]

theorem rawRowCheck2808 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form5 = rawRow2808 := by decide +kernel

def row2808 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

theorem rowCheck2808 : row2808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2808 := by decide +kernel

theorem rowEval2808 (x : Key → ℝ) : Integer.Sparse.eval row2808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2808, Integer.Sparse.eval_collectBalanced, rawRowCheck2808]

def rawRow2809 : Integer.Sparse Key := [(key1837, -1), (key1837, -1), (key1651, -1), (key1651, -1), (key1648, -1), (key1648, -1), (key1848, 2), (key1674, 2), (key1674, 2), (key1768, 1), (key1768, 1), (key1536, 1), (key1536, 1), (key1531, 1), (key1531, 1), (key1832, -1), (key1832, -1), (key1674, -1), (key1674, -1), (key1642, -1), (key1642, -1), (key1765, -2), (key1531, -2), (key1531, -2), (key1806, 1), (key1806, 1), (key1648, 1), (key1648, 1), (key1609, 1), (key1609, 1)]

theorem rawRowCheck2809 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form5 = rawRow2809 := by decide +kernel

def row2809 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

theorem rowCheck2809 : row2809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2809 := by decide +kernel

theorem rowEval2809 (x : Key → ℝ) : Integer.Sparse.eval row2809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2809, Integer.Sparse.eval_collectBalanced, rawRowCheck2809]

def rawRow2810 : Integer.Sparse Key := [(key1265, -1), (key1268, -1), (key1648, -1), (key1837, -1), (key1674, -1), (key1848, -1), (key1268, 2), (key1651, 2), (key1837, 2), (key1256, 1), (key1261, 1), (key1609, 1), (key1809, 1), (key1642, 1), (key1832, 1), (key1261, -1), (key1268, -1), (key1536, -1), (key1768, -1), (key1651, -1), (key1809, -1), (key1256, -2), (key1609, -2), (key1806, -2), (key1256, 1), (key1265, 1), (key1531, 1), (key1765, 1), (key1648, 1), (key1806, 1)]

theorem rawRowCheck2810 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form5 = rawRow2810 := by decide +kernel

def row2810 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

theorem rowCheck2810 : row2810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2810 := by decide +kernel

theorem rowEval2810 (x : Key → ℝ) : Integer.Sparse.eval row2810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2810, Integer.Sparse.eval_collectBalanced, rawRowCheck2810]

def rawRow2811 : Integer.Sparse Key := [(key1268, -1), (key1265, -1), (key1837, -1), (key1648, -1), (key1848, -1), (key1674, -1), (key1268, 2), (key1837, 2), (key1651, 2), (key1261, 1), (key1256, 1), (key1809, 1), (key1609, 1), (key1832, 1), (key1642, 1), (key1268, -1), (key1261, -1), (key1768, -1), (key1536, -1), (key1809, -1), (key1651, -1), (key1256, -2), (key1806, -2), (key1609, -2), (key1265, 1), (key1256, 1), (key1765, 1), (key1531, 1), (key1806, 1), (key1648, 1)]

theorem rawRowCheck2811 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form5 = rawRow2811 := by decide +kernel

def row2811 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

theorem rowCheck2811 : row2811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2811 := by decide +kernel

theorem rowEval2811 (x : Key → ℝ) : Integer.Sparse.eval row2811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2811, Integer.Sparse.eval_collectBalanced, rawRowCheck2811]

def rawRow2812 : Integer.Sparse Key := [(key1648, -1), (key1674, -1), (key1265, -1), (key1848, -1), (key1268, -1), (key1837, -1), (key1651, 2), (key1268, 2), (key1837, 2), (key1609, 1), (key1642, 1), (key1256, 1), (key1832, 1), (key1261, 1), (key1809, 1), (key1536, -1), (key1651, -1), (key1261, -1), (key1809, -1), (key1268, -1), (key1768, -1), (key1609, -2), (key1256, -2), (key1806, -2), (key1531, 1), (key1648, 1), (key1256, 1), (key1806, 1), (key1265, 1), (key1765, 1)]

theorem rawRowCheck2812 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form5 = rawRow2812 := by decide +kernel

def row2812 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

theorem rowCheck2812 : row2812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2812 := by decide +kernel

theorem rowEval2812 (x : Key → ℝ) : Integer.Sparse.eval row2812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2812, Integer.Sparse.eval_collectBalanced, rawRowCheck2812]

def rawRow2813 : Integer.Sparse Key := [(key1674, -1), (key1648, -1), (key1848, -1), (key1265, -1), (key1837, -1), (key1268, -1), (key1651, 2), (key1837, 2), (key1268, 2), (key1642, 1), (key1609, 1), (key1832, 1), (key1256, 1), (key1809, 1), (key1261, 1), (key1651, -1), (key1536, -1), (key1809, -1), (key1261, -1), (key1768, -1), (key1268, -1), (key1609, -2), (key1806, -2), (key1256, -2), (key1648, 1), (key1531, 1), (key1806, 1), (key1256, 1), (key1765, 1), (key1265, 1)]

theorem rawRowCheck2813 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form5 = rawRow2813 := by decide +kernel

def row2813 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

theorem rowCheck2813 : row2813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2813 := by decide +kernel

theorem rowEval2813 (x : Key → ℝ) : Integer.Sparse.eval row2813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck2813, Integer.Sparse.eval_collectBalanced, rawRowCheck2813]

def rawRow2814 : Integer.Sparse Key := [(key1837, -1), (key1848, -1), (key1268, -1), (key1674, -1), (key1265, -1), (key1648, -1), (key1837, 2), (key1268, 2), (key1651, 2), (key1809, 1), (key1832, 1), (key1261, 1), (key1642, 1), (key1256, 1), (key1609, 1), (key1768, -1), (key1809, -1), (key1268, -1), (key1651, -1), (key1261, -1), (key1536, -1), (key1806, -2), (key1256, -2), (key1609, -2), (key1765, 1), (key1806, 1), (key1265, 1), (key1648, 1), (key1256, 1), (key1531, 1)]

theorem rawRowCheck2814 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form5 = rawRow2814 := by decide +kernel

def row2814 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

theorem rowCheck2814 : row2814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2814 := by decide +kernel

theorem rowEval2814 (x : Key → ℝ) : Integer.Sparse.eval row2814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2814, Integer.Sparse.eval_collectBalanced, rawRowCheck2814]

def rawRow2815 : Integer.Sparse Key := [(key1848, -1), (key1837, -1), (key1674, -1), (key1268, -1), (key1648, -1), (key1265, -1), (key1837, 2), (key1651, 2), (key1268, 2), (key1832, 1), (key1809, 1), (key1642, 1), (key1261, 1), (key1609, 1), (key1256, 1), (key1809, -1), (key1768, -1), (key1651, -1), (key1268, -1), (key1536, -1), (key1261, -1), (key1806, -2), (key1609, -2), (key1256, -2), (key1806, 1), (key1765, 1), (key1648, 1), (key1265, 1), (key1531, 1), (key1256, 1)]

theorem rawRowCheck2815 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form5 = rawRow2815 := by decide +kernel

def row2815 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

theorem rowCheck2815 : row2815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2815 := by decide +kernel

theorem rowEval2815 (x : Key → ℝ) : Integer.Sparse.eval row2815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck2815, Integer.Sparse.eval_collectBalanced, rawRowCheck2815]

end MUB6.Certificate.GramRows

end OAI
