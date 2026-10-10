import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
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

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow5888 : Integer.Sparse Key := [(key2751, -2), (key2739, 1), (key2749, 1), (key3001, -2), (key2650, 1), (key2906, 1), (key2999, 1), (key3004, 1), (key2656, 1), (key2915, 1), (key2655, -2), (key2899, -2), (key2751, 2), (key2675, -1), (key2730, -1), (key2964, 2), (key2620, -1), (key2833, -1), (key2946, -1), (key2994, -1), (key2656, -1), (key2915, -1), (key2643, 2), (key2797, 2), (key2739, -1), (key2749, -1), (key2675, 1), (key2730, 1), (key2952, -1), (key2962, -1), (key2617, 1), (key2810, 1), (key2730, 1), (key2985, 1), (key2633, -1), (key2707, -1), (key2655, 1), (key2899, 1), (key2650, -1), (key2739, -1)]

theorem rawRowCheck5888 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block2.form5 = rawRow5888 := by decide +kernel

def row5888 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 2), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, -1), (key2797, 2), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

theorem rowCheck5888 : row5888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5888 := by decide +kernel

theorem rowEval5888 (x : Key → ℝ) : Integer.Sparse.eval row5888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck5888, Integer.Sparse.eval_collectBalanced, rawRowCheck5888]

def rawRow5889 : Integer.Sparse Key := [(key2751, -2), (key2749, 1), (key2739, 1), (key3001, -2), (key2906, 1), (key2650, 1), (key3004, 1), (key2999, 1), (key2915, 1), (key2656, 1), (key2899, -2), (key2655, -2), (key2751, 2), (key2730, -1), (key2675, -1), (key2964, 2), (key2833, -1), (key2620, -1), (key2994, -1), (key2946, -1), (key2915, -1), (key2656, -1), (key2797, 2), (key2643, 2), (key2749, -1), (key2739, -1), (key2730, 1), (key2675, 1), (key2962, -1), (key2952, -1), (key2810, 1), (key2617, 1), (key2985, 1), (key2730, 1), (key2707, -1), (key2633, -1), (key2899, 1), (key2655, 1), (key2739, -1), (key2650, -1)]

theorem rawRowCheck5889 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block2.form5 = rawRow5889 := by decide +kernel

def row5889 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 2), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, -1), (key2797, 2), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

theorem rowCheck5889 : row5889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5889 := by decide +kernel

theorem rowEval5889 (x : Key → ℝ) : Integer.Sparse.eval row5889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck5889, Integer.Sparse.eval_collectBalanced, rawRowCheck5889]

def rawRow5890 : Integer.Sparse Key := [(key2899, -2), (key2906, 1), (key2915, 1), (key2655, -2), (key2749, 1), (key3004, 1), (key2650, 1), (key2656, 1), (key2739, 1), (key2999, 1), (key2751, -2), (key3001, -2), (key2797, 2), (key2833, -1), (key2915, -1), (key2643, 2), (key2730, -1), (key2994, -1), (key2620, -1), (key2656, -1), (key2675, -1), (key2946, -1), (key2751, 2), (key2964, 2), (key2787, -1), (key2797, -1), (key2810, 1), (key2899, 1), (key2633, -1), (key2643, -1), (key2730, 1), (key2985, 1), (key2617, 1), (key2655, 1), (key2945, -1), (key2962, -1), (key2675, 1), (key2730, 1), (key2797, -1), (key2833, -1)]

theorem rawRowCheck5890 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block2.form5 = rawRow5890 := by decide +kernel

def row5890 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2730, 1), (key2739, 1), (key2749, 1), (key2787, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

theorem rowCheck5890 : row5890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5890 := by decide +kernel

theorem rowEval5890 (x : Key → ℝ) : Integer.Sparse.eval row5890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5890, Integer.Sparse.eval_collectBalanced, rawRowCheck5890]

def rawRow5891 : Integer.Sparse Key := [(key2899, -2), (key2915, 1), (key2906, 1), (key2655, -2), (key3004, 1), (key2749, 1), (key2656, 1), (key2650, 1), (key2999, 1), (key2739, 1), (key3001, -2), (key2751, -2), (key2797, 2), (key2915, -1), (key2833, -1), (key2643, 2), (key2994, -1), (key2730, -1), (key2656, -1), (key2620, -1), (key2946, -1), (key2675, -1), (key2964, 2), (key2751, 2), (key2797, -1), (key2787, -1), (key2899, 1), (key2810, 1), (key2643, -1), (key2633, -1), (key2985, 1), (key2730, 1), (key2655, 1), (key2617, 1), (key2962, -1), (key2945, -1), (key2730, 1), (key2675, 1), (key2833, -1), (key2797, -1)]

theorem rawRowCheck5891 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block2.form5 = rawRow5891 := by decide +kernel

def row5891 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2730, 1), (key2739, 1), (key2749, 1), (key2787, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

theorem rowCheck5891 : row5891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5891 := by decide +kernel

theorem rowEval5891 (x : Key → ℝ) : Integer.Sparse.eval row5891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5891, Integer.Sparse.eval_collectBalanced, rawRowCheck5891]

def rawRow5892 : Integer.Sparse Key := [(key2915, -2), (key2899, 1), (key2906, 1), (key3004, -2), (key2655, 1), (key2749, 1), (key2999, 1), (key3001, 1), (key2656, 1), (key2751, 1), (key2650, -2), (key2739, -2), (key2915, 2), (key2797, -1), (key2833, -1), (key2994, 2), (key2643, -1), (key2730, -1), (key2946, -1), (key2964, -1), (key2656, -1), (key2751, -1), (key2620, 2), (key2675, 2), (key2899, -1), (key2906, -1), (key2797, 1), (key2833, 1), (key2978, -1), (key2985, -1), (key2633, 1), (key2707, 1), (key2945, 1), (key2962, 1), (key2617, -1), (key2672, -1), (key2643, 1), (key2797, 1), (key2620, -1), (key2675, -1)]

theorem rawRowCheck5892 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form5 = rawRow5892 := by decide +kernel

def row5892 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -2), (key2749, 1), (key2797, 1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck5892 : row5892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5892 := by decide +kernel

theorem rowEval5892 (x : Key → ℝ) : Integer.Sparse.eval row5892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5892, Integer.Sparse.eval_collectBalanced, rawRowCheck5892]

def rawRow5893 : Integer.Sparse Key := [(key2915, -2), (key2906, 1), (key2899, 1), (key3004, -2), (key2749, 1), (key2655, 1), (key3001, 1), (key2999, 1), (key2751, 1), (key2656, 1), (key2739, -2), (key2650, -2), (key2915, 2), (key2833, -1), (key2797, -1), (key2994, 2), (key2730, -1), (key2643, -1), (key2964, -1), (key2946, -1), (key2751, -1), (key2656, -1), (key2675, 2), (key2620, 2), (key2906, -1), (key2899, -1), (key2833, 1), (key2797, 1), (key2985, -1), (key2978, -1), (key2707, 1), (key2633, 1), (key2962, 1), (key2945, 1), (key2672, -1), (key2617, -1), (key2797, 1), (key2643, 1), (key2675, -1), (key2620, -1)]

theorem rawRowCheck5893 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form5 = rawRow5893 := by decide +kernel

def row5893 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -2), (key2749, 1), (key2797, 1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck5893 : row5893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5893 := by decide +kernel

theorem rowEval5893 (x : Key → ℝ) : Integer.Sparse.eval row5893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck5893, Integer.Sparse.eval_collectBalanced, rawRowCheck5893]

def rawRow5894 : Integer.Sparse Key := [(key3001, -2), (key2999, 1), (key3004, 1), (key2751, -2), (key2656, 1), (key2915, 1), (key2739, 1), (key2749, 1), (key2650, 1), (key2906, 1), (key2655, -2), (key2899, -2), (key2964, 2), (key2946, -1), (key2994, -1), (key2751, 2), (key2656, -1), (key2915, -1), (key2675, -1), (key2730, -1), (key2620, -1), (key2833, -1), (key2643, 2), (key2797, 2), (key2952, -1), (key2962, -1), (key2940, 1), (key2985, 1), (key2739, -1), (key2749, -1), (key2655, 1), (key2899, 1), (key2675, 1), (key2730, 1), (key2643, -1), (key2797, -1), (key2617, 1), (key2810, 1), (key2633, -1), (key2707, -1)]

theorem rawRowCheck5894 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block2.form5 = rawRow5894 := by decide +kernel

def row5894 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

theorem rowCheck5894 : row5894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5894 := by decide +kernel

theorem rowEval5894 (x : Key → ℝ) : Integer.Sparse.eval row5894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck5894, Integer.Sparse.eval_collectBalanced, rawRowCheck5894]

def rawRow5895 : Integer.Sparse Key := [(key3001, -2), (key3004, 1), (key2999, 1), (key2751, -2), (key2915, 1), (key2656, 1), (key2749, 1), (key2739, 1), (key2906, 1), (key2650, 1), (key2899, -2), (key2655, -2), (key2964, 2), (key2994, -1), (key2946, -1), (key2751, 2), (key2915, -1), (key2656, -1), (key2730, -1), (key2675, -1), (key2833, -1), (key2620, -1), (key2797, 2), (key2643, 2), (key2962, -1), (key2952, -1), (key2985, 1), (key2940, 1), (key2749, -1), (key2739, -1), (key2899, 1), (key2655, 1), (key2730, 1), (key2675, 1), (key2797, -1), (key2643, -1), (key2810, 1), (key2617, 1), (key2707, -1), (key2633, -1)]

theorem rawRowCheck5895 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block2.form5 = rawRow5895 := by decide +kernel

def row5895 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

theorem rowCheck5895 : row5895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5895 := by decide +kernel

theorem rowEval5895 (x : Key → ℝ) : Integer.Sparse.eval row5895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck5895, Integer.Sparse.eval_collectBalanced, rawRowCheck5895]

def rawRow5896 : Integer.Sparse Key := [(key3004, -2), (key2999, 1), (key3001, 1), (key2915, -2), (key2656, 1), (key2751, 1), (key2899, 1), (key2906, 1), (key2655, 1), (key2749, 1), (key2650, -2), (key2739, -2), (key2994, 2), (key2946, -1), (key2964, -1), (key2915, 2), (key2656, -1), (key2751, -1), (key2797, -1), (key2833, -1), (key2643, -1), (key2730, -1), (key2620, 2), (key2675, 2), (key2978, -1), (key2985, -1), (key2945, 1), (key2962, 1), (key2899, -1), (key2906, -1), (key2650, 1), (key2739, 1), (key2797, 1), (key2833, 1), (key2620, -1), (key2675, -1), (key2633, 1), (key2707, 1), (key2617, -1), (key2672, -1)]

theorem rawRowCheck5896 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form5 = rawRow5896 := by decide +kernel

def row5896 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, 1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck5896 : row5896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5896 := by decide +kernel

theorem rowEval5896 (x : Key → ℝ) : Integer.Sparse.eval row5896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5896, Integer.Sparse.eval_collectBalanced, rawRowCheck5896]

def rawRow5897 : Integer.Sparse Key := [(key3004, -2), (key3001, 1), (key2999, 1), (key2915, -2), (key2751, 1), (key2656, 1), (key2906, 1), (key2899, 1), (key2749, 1), (key2655, 1), (key2739, -2), (key2650, -2), (key2994, 2), (key2964, -1), (key2946, -1), (key2915, 2), (key2751, -1), (key2656, -1), (key2833, -1), (key2797, -1), (key2730, -1), (key2643, -1), (key2675, 2), (key2620, 2), (key2985, -1), (key2978, -1), (key2962, 1), (key2945, 1), (key2906, -1), (key2899, -1), (key2739, 1), (key2650, 1), (key2833, 1), (key2797, 1), (key2675, -1), (key2620, -1), (key2707, 1), (key2633, 1), (key2672, -1), (key2617, -1)]

theorem rawRowCheck5897 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form5 = rawRow5897 := by decide +kernel

def row5897 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, 1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck5897 : row5897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5897 := by decide +kernel

theorem rowEval5897 (x : Key → ℝ) : Integer.Sparse.eval row5897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck5897, Integer.Sparse.eval_collectBalanced, rawRowCheck5897]

def rawRow5898 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1298, 2), (key1312, -1), (key1318, -1), (key1312, 2), (key1326, 2), (key1318, -1), (key1326, -1), (key1351, 2), (key1351, -1), (key1354, -1), (key1387, 1), (key1393, 1), (key1393, -2), (key1420, 1), (key1426, 1), (key1420, -2), (key1444, -2), (key1426, 1), (key1444, 1), (key1472, -2), (key1472, 1), (key1480, 1), (key1542, -1), (key1556, -1), (key1548, 1), (key1556, 1), (key1569, 1), (key1593, 1), (key1575, -1), (key1593, -1), (key1618, -1), (key1624, -1), (key1618, 1), (key1633, 1), (key1681, 1), (key1683, 1), (key1681, -1), (key1689, -1)]

theorem rawRowCheck5898 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form0 = rawRow5898 := by decide +kernel

def row5898 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5898 : row5898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5898 := by decide +kernel

theorem rowEval5898 (x : Key → ℝ) : Integer.Sparse.eval row5898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5898, Integer.Sparse.eval_collectBalanced, rawRowCheck5898]

def rawRow5899 : Integer.Sparse Key := [(key1298, -1), (key1292, -1), (key1298, 2), (key1318, -1), (key1312, -1), (key1326, 2), (key1312, 2), (key1326, -1), (key1318, -1), (key1351, 2), (key1354, -1), (key1351, -1), (key1393, 1), (key1387, 1), (key1393, -2), (key1426, 1), (key1420, 1), (key1444, -2), (key1420, -2), (key1444, 1), (key1426, 1), (key1472, -2), (key1480, 1), (key1472, 1), (key1556, -1), (key1542, -1), (key1556, 1), (key1548, 1), (key1593, 1), (key1569, 1), (key1593, -1), (key1575, -1), (key1624, -1), (key1618, -1), (key1633, 1), (key1618, 1), (key1683, 1), (key1681, 1), (key1689, -1), (key1681, -1)]

theorem rawRowCheck5899 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form0 = rawRow5899 := by decide +kernel

def row5899 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5899 : row5899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5899 := by decide +kernel

theorem rowEval5899 (x : Key → ℝ) : Integer.Sparse.eval row5899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5899, Integer.Sparse.eval_collectBalanced, rawRowCheck5899]

def rawRow5900 : Integer.Sparse Key := [(key1298, -1), (key1298, -1), (key1292, 2), (key1326, -1), (key1326, -1), (key1318, 2), (key1318, 2), (key1312, -1), (key1312, -1), (key1354, 2), (key1351, -1), (key1351, -1), (key1393, 1), (key1393, 1), (key1387, -2), (key1444, 1), (key1444, 1), (key1426, -2), (key1426, -2), (key1420, 1), (key1420, 1), (key1480, -2), (key1472, 1), (key1472, 1), (key1548, -1), (key1548, -1), (key1542, 1), (key1542, 1), (key1575, 1), (key1575, 1), (key1569, -1), (key1569, -1), (key1633, -1), (key1633, -1), (key1624, 1), (key1624, 1), (key1689, 1), (key1689, 1), (key1683, -1), (key1683, -1)]

theorem rawRowCheck5900 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form0 = rawRow5900 := by decide +kernel

def row5900 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1318, 4), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, -2), (key1393, 2), (key1420, 2), (key1426, -4), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, 2), (key1548, -2), (key1569, -2), (key1575, 2), (key1624, 2), (key1633, -2), (key1683, -2), (key1689, 2)]

theorem rowCheck5900 : row5900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5900 := by decide +kernel

theorem rowEval5900 (x : Key → ℝ) : Integer.Sparse.eval row5900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5900, Integer.Sparse.eval_collectBalanced, rawRowCheck5900]

def rawRow5901 : Integer.Sparse Key := [(key1312, -1), (key1318, -1), (key1351, 2), (key1292, -1), (key1298, -1), (key1312, 2), (key1326, 2), (key1351, -1), (key1354, -1), (key1298, 2), (key1318, -1), (key1326, -1), (key1420, 1), (key1426, 1), (key1472, -2), (key1387, 1), (key1393, 1), (key1420, -2), (key1444, -2), (key1472, 1), (key1480, 1), (key1393, -2), (key1426, 1), (key1444, 1), (key1618, -1), (key1624, -1), (key1681, 1), (key1683, 1), (key1618, 1), (key1633, 1), (key1681, -1), (key1689, -1), (key1542, -1), (key1556, -1), (key1569, 1), (key1593, 1), (key1548, 1), (key1556, 1), (key1575, -1), (key1593, -1)]

theorem rawRowCheck5901 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form0 = rawRow5901 := by decide +kernel

def row5901 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5901 : row5901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5901 := by decide +kernel

theorem rowEval5901 (x : Key → ℝ) : Integer.Sparse.eval row5901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5901, Integer.Sparse.eval_collectBalanced, rawRowCheck5901]

def rawRow5902 : Integer.Sparse Key := [(key1318, -1), (key1312, -1), (key1351, 2), (key1298, -1), (key1292, -1), (key1326, 2), (key1312, 2), (key1354, -1), (key1351, -1), (key1298, 2), (key1326, -1), (key1318, -1), (key1426, 1), (key1420, 1), (key1472, -2), (key1393, 1), (key1387, 1), (key1444, -2), (key1420, -2), (key1480, 1), (key1472, 1), (key1393, -2), (key1444, 1), (key1426, 1), (key1624, -1), (key1618, -1), (key1683, 1), (key1681, 1), (key1633, 1), (key1618, 1), (key1689, -1), (key1681, -1), (key1556, -1), (key1542, -1), (key1593, 1), (key1569, 1), (key1556, 1), (key1548, 1), (key1593, -1), (key1575, -1)]

theorem rawRowCheck5902 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form0 = rawRow5902 := by decide +kernel

def row5902 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5902 : row5902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5902 := by decide +kernel

theorem rowEval5902 (x : Key → ℝ) : Integer.Sparse.eval row5902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5902, Integer.Sparse.eval_collectBalanced, rawRowCheck5902]

def rawRow5903 : Integer.Sparse Key := [(key1312, -1), (key1351, -1), (key1318, 2), (key1312, -1), (key1351, -1), (key1292, 2), (key1354, 2), (key1298, -1), (key1326, -1), (key1318, 2), (key1298, -1), (key1326, -1), (key1420, 1), (key1472, 1), (key1426, -2), (key1420, 1), (key1472, 1), (key1387, -2), (key1480, -2), (key1393, 1), (key1444, 1), (key1426, -2), (key1393, 1), (key1444, 1), (key1569, -1), (key1683, -1), (key1575, 1), (key1624, 1), (key1542, 1), (key1689, 1), (key1548, -1), (key1633, -1), (key1569, -1), (key1683, -1), (key1542, 1), (key1689, 1), (key1575, 1), (key1624, 1), (key1548, -1), (key1633, -1)]

theorem rawRowCheck5903 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form0 = rawRow5903 := by decide +kernel

def row5903 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1318, 4), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, -2), (key1393, 2), (key1420, 2), (key1426, -4), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, 2), (key1548, -2), (key1569, -2), (key1575, 2), (key1624, 2), (key1633, -2), (key1683, -2), (key1689, 2)]

theorem rowCheck5903 : row5903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5903 := by decide +kernel

theorem rowEval5903 (x : Key → ℝ) : Integer.Sparse.eval row5903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5903, Integer.Sparse.eval_collectBalanced, rawRowCheck5903]

def rawRow5904 : Integer.Sparse Key := [(key1351, -1), (key1312, -1), (key1318, 2), (key1351, -1), (key1312, -1), (key1354, 2), (key1292, 2), (key1326, -1), (key1298, -1), (key1318, 2), (key1326, -1), (key1298, -1), (key1472, 1), (key1420, 1), (key1426, -2), (key1472, 1), (key1420, 1), (key1480, -2), (key1387, -2), (key1444, 1), (key1393, 1), (key1426, -2), (key1444, 1), (key1393, 1), (key1683, -1), (key1569, -1), (key1624, 1), (key1575, 1), (key1689, 1), (key1542, 1), (key1633, -1), (key1548, -1), (key1683, -1), (key1569, -1), (key1689, 1), (key1542, 1), (key1624, 1), (key1575, 1), (key1633, -1), (key1548, -1)]

theorem rawRowCheck5904 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form0 = rawRow5904 := by decide +kernel

def row5904 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1318, 4), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, -2), (key1393, 2), (key1420, 2), (key1426, -4), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, 2), (key1548, -2), (key1569, -2), (key1575, 2), (key1624, 2), (key1633, -2), (key1683, -2), (key1689, 2)]

theorem rowCheck5904 : row5904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5904 := by decide +kernel

theorem rowEval5904 (x : Key → ℝ) : Integer.Sparse.eval row5904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5904, Integer.Sparse.eval_collectBalanced, rawRowCheck5904]

def rawRow5905 : Integer.Sparse Key := [(key1318, -1), (key1351, -1), (key1312, 2), (key1326, -1), (key1354, -1), (key1298, 2), (key1351, 2), (key1292, -1), (key1312, -1), (key1326, 2), (key1298, -1), (key1318, -1), (key1426, 1), (key1472, 1), (key1420, -2), (key1444, 1), (key1480, 1), (key1393, -2), (key1472, -2), (key1387, 1), (key1420, 1), (key1444, -2), (key1393, 1), (key1426, 1), (key1575, -1), (key1681, -1), (key1569, 1), (key1618, 1), (key1548, 1), (key1681, 1), (key1542, -1), (key1618, -1), (key1593, -1), (key1689, -1), (key1556, 1), (key1683, 1), (key1593, 1), (key1633, 1), (key1556, -1), (key1624, -1)]

theorem rawRowCheck5905 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form0 = rawRow5905 := by decide +kernel

def row5905 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5905 : row5905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5905 := by decide +kernel

theorem rowEval5905 (x : Key → ℝ) : Integer.Sparse.eval row5905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5905, Integer.Sparse.eval_collectBalanced, rawRowCheck5905]

def rawRow5906 : Integer.Sparse Key := [(key1351, -1), (key1318, -1), (key1312, 2), (key1354, -1), (key1326, -1), (key1351, 2), (key1298, 2), (key1312, -1), (key1292, -1), (key1326, 2), (key1318, -1), (key1298, -1), (key1472, 1), (key1426, 1), (key1420, -2), (key1480, 1), (key1444, 1), (key1472, -2), (key1393, -2), (key1420, 1), (key1387, 1), (key1444, -2), (key1426, 1), (key1393, 1), (key1681, -1), (key1575, -1), (key1618, 1), (key1569, 1), (key1681, 1), (key1548, 1), (key1618, -1), (key1542, -1), (key1689, -1), (key1593, -1), (key1683, 1), (key1556, 1), (key1633, 1), (key1593, 1), (key1624, -1), (key1556, -1)]

theorem rawRowCheck5906 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form0 = rawRow5906 := by decide +kernel

def row5906 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5906 : row5906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5906 := by decide +kernel

theorem rowEval5906 (x : Key → ℝ) : Integer.Sparse.eval row5906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5906, Integer.Sparse.eval_collectBalanced, rawRowCheck5906]

def rawRow5907 : Integer.Sparse Key := [(key1326, -1), (key1326, -1), (key1354, 2), (key1298, -1), (key1298, -1), (key1318, 2), (key1318, 2), (key1351, -1), (key1351, -1), (key1292, 2), (key1312, -1), (key1312, -1), (key1444, 1), (key1444, 1), (key1480, -2), (key1393, 1), (key1393, 1), (key1426, -2), (key1426, -2), (key1472, 1), (key1472, 1), (key1387, -2), (key1420, 1), (key1420, 1), (key1633, -1), (key1633, -1), (key1689, 1), (key1689, 1), (key1624, 1), (key1624, 1), (key1683, -1), (key1683, -1), (key1548, -1), (key1548, -1), (key1575, 1), (key1575, 1), (key1542, 1), (key1542, 1), (key1569, -1), (key1569, -1)]

theorem rawRowCheck5907 : GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form0 = rawRow5907 := by decide +kernel

def row5907 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1318, 4), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, -2), (key1393, 2), (key1420, 2), (key1426, -4), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, 2), (key1548, -2), (key1569, -2), (key1575, 2), (key1624, 2), (key1633, -2), (key1683, -2), (key1689, 2)]

theorem rowCheck5907 : row5907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5907 := by decide +kernel

theorem rowEval5907 (x : Key → ℝ) : Integer.Sparse.eval row5907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5907, Integer.Sparse.eval_collectBalanced, rawRowCheck5907]

def rawRow5908 : Integer.Sparse Key := [(key1326, -1), (key1354, -1), (key1326, 2), (key1318, -1), (key1351, -1), (key1298, 2), (key1351, 2), (key1298, -1), (key1318, -1), (key1312, 2), (key1292, -1), (key1312, -1), (key1444, 1), (key1480, 1), (key1444, -2), (key1426, 1), (key1472, 1), (key1393, -2), (key1472, -2), (key1393, 1), (key1426, 1), (key1420, -2), (key1387, 1), (key1420, 1), (key1593, -1), (key1689, -1), (key1593, 1), (key1633, 1), (key1556, 1), (key1683, 1), (key1556, -1), (key1624, -1), (key1575, -1), (key1681, -1), (key1548, 1), (key1681, 1), (key1569, 1), (key1618, 1), (key1542, -1), (key1618, -1)]

theorem rawRowCheck5908 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form0 = rawRow5908 := by decide +kernel

def row5908 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5908 : row5908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5908 := by decide +kernel

theorem rowEval5908 (x : Key → ℝ) : Integer.Sparse.eval row5908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5908, Integer.Sparse.eval_collectBalanced, rawRowCheck5908]

def rawRow5909 : Integer.Sparse Key := [(key1354, -1), (key1326, -1), (key1326, 2), (key1351, -1), (key1318, -1), (key1351, 2), (key1298, 2), (key1318, -1), (key1298, -1), (key1312, 2), (key1312, -1), (key1292, -1), (key1480, 1), (key1444, 1), (key1444, -2), (key1472, 1), (key1426, 1), (key1472, -2), (key1393, -2), (key1426, 1), (key1393, 1), (key1420, -2), (key1420, 1), (key1387, 1), (key1689, -1), (key1593, -1), (key1633, 1), (key1593, 1), (key1683, 1), (key1556, 1), (key1624, -1), (key1556, -1), (key1681, -1), (key1575, -1), (key1681, 1), (key1548, 1), (key1618, 1), (key1569, 1), (key1618, -1), (key1542, -1)]

theorem rawRowCheck5909 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form0 = rawRow5909 := by decide +kernel

def row5909 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5909 : row5909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5909 := by decide +kernel

theorem rowEval5909 (x : Key → ℝ) : Integer.Sparse.eval row5909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5909, Integer.Sparse.eval_collectBalanced, rawRowCheck5909]

def rawRow5910 : Integer.Sparse Key := [(key1387, -1), (key1393, -1), (key1393, 2), (key1542, -1), (key1548, -1), (key1542, 2), (key1556, 2), (key1548, -1), (key1556, -1), (key1896, 2), (key1896, -1), (key1899, -1), (key1292, 1), (key1298, 1), (key1298, -2), (key1569, 1), (key1575, 1), (key1569, -2), (key1593, -2), (key1575, 1), (key1593, 1), (key1903, -2), (key1903, 1), (key1911, 1), (key1312, -1), (key1326, -1), (key1318, 1), (key1326, 1), (key1420, 1), (key1444, 1), (key1426, -1), (key1444, -1), (key1618, -1), (key1624, -1), (key1618, 1), (key1633, 1), (key1918, 1), (key1920, 1), (key1918, -1), (key1926, -1)]

theorem rawRowCheck5910 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form0 = rawRow5910 := by decide +kernel

def row5910 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5910 : row5910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5910 := by decide +kernel

theorem rowEval5910 (x : Key → ℝ) : Integer.Sparse.eval row5910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5910, Integer.Sparse.eval_collectBalanced, rawRowCheck5910]

def rawRow5911 : Integer.Sparse Key := [(key1393, -1), (key1387, -1), (key1393, 2), (key1548, -1), (key1542, -1), (key1556, 2), (key1542, 2), (key1556, -1), (key1548, -1), (key1896, 2), (key1899, -1), (key1896, -1), (key1298, 1), (key1292, 1), (key1298, -2), (key1575, 1), (key1569, 1), (key1593, -2), (key1569, -2), (key1593, 1), (key1575, 1), (key1903, -2), (key1911, 1), (key1903, 1), (key1326, -1), (key1312, -1), (key1326, 1), (key1318, 1), (key1444, 1), (key1420, 1), (key1444, -1), (key1426, -1), (key1624, -1), (key1618, -1), (key1633, 1), (key1618, 1), (key1920, 1), (key1918, 1), (key1926, -1), (key1918, -1)]

theorem rawRowCheck5911 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form0 = rawRow5911 := by decide +kernel

def row5911 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5911 : row5911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5911 := by decide +kernel

theorem rowEval5911 (x : Key → ℝ) : Integer.Sparse.eval row5911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5911, Integer.Sparse.eval_collectBalanced, rawRowCheck5911]

def rawRow5912 : Integer.Sparse Key := [(key1393, -1), (key1393, -1), (key1387, 2), (key1556, -1), (key1556, -1), (key1548, 2), (key1548, 2), (key1542, -1), (key1542, -1), (key1899, 2), (key1896, -1), (key1896, -1), (key1298, 1), (key1298, 1), (key1292, -2), (key1593, 1), (key1593, 1), (key1575, -2), (key1575, -2), (key1569, 1), (key1569, 1), (key1911, -2), (key1903, 1), (key1903, 1), (key1318, -1), (key1318, -1), (key1312, 1), (key1312, 1), (key1426, 1), (key1426, 1), (key1420, -1), (key1420, -1), (key1633, -1), (key1633, -1), (key1624, 1), (key1624, 1), (key1926, 1), (key1926, 1), (key1920, -1), (key1920, -1)]

theorem rawRowCheck5912 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form0 = rawRow5912 := by decide +kernel

def row5912 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 2), (key1542, -2), (key1548, 4), (key1556, -2), (key1569, 2), (key1575, -4), (key1593, 2), (key1624, 2), (key1633, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

theorem rowCheck5912 : row5912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5912 := by decide +kernel

theorem rowEval5912 (x : Key → ℝ) : Integer.Sparse.eval row5912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5912, Integer.Sparse.eval_collectBalanced, rawRowCheck5912]

def rawRow5913 : Integer.Sparse Key := [(key1542, -1), (key1548, -1), (key1896, 2), (key1387, -1), (key1393, -1), (key1542, 2), (key1556, 2), (key1896, -1), (key1899, -1), (key1393, 2), (key1548, -1), (key1556, -1), (key1569, 1), (key1575, 1), (key1903, -2), (key1292, 1), (key1298, 1), (key1569, -2), (key1593, -2), (key1903, 1), (key1911, 1), (key1298, -2), (key1575, 1), (key1593, 1), (key1618, -1), (key1624, -1), (key1918, 1), (key1920, 1), (key1618, 1), (key1633, 1), (key1918, -1), (key1926, -1), (key1312, -1), (key1326, -1), (key1420, 1), (key1444, 1), (key1318, 1), (key1326, 1), (key1426, -1), (key1444, -1)]

theorem rawRowCheck5913 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form0 = rawRow5913 := by decide +kernel

def row5913 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5913 : row5913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5913 := by decide +kernel

theorem rowEval5913 (x : Key → ℝ) : Integer.Sparse.eval row5913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5913, Integer.Sparse.eval_collectBalanced, rawRowCheck5913]

def rawRow5914 : Integer.Sparse Key := [(key1548, -1), (key1542, -1), (key1896, 2), (key1393, -1), (key1387, -1), (key1556, 2), (key1542, 2), (key1899, -1), (key1896, -1), (key1393, 2), (key1556, -1), (key1548, -1), (key1575, 1), (key1569, 1), (key1903, -2), (key1298, 1), (key1292, 1), (key1593, -2), (key1569, -2), (key1911, 1), (key1903, 1), (key1298, -2), (key1593, 1), (key1575, 1), (key1624, -1), (key1618, -1), (key1920, 1), (key1918, 1), (key1633, 1), (key1618, 1), (key1926, -1), (key1918, -1), (key1326, -1), (key1312, -1), (key1444, 1), (key1420, 1), (key1326, 1), (key1318, 1), (key1444, -1), (key1426, -1)]

theorem rawRowCheck5914 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form0 = rawRow5914 := by decide +kernel

def row5914 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5914 : row5914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5914 := by decide +kernel

theorem rowEval5914 (x : Key → ℝ) : Integer.Sparse.eval row5914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5914, Integer.Sparse.eval_collectBalanced, rawRowCheck5914]

def rawRow5915 : Integer.Sparse Key := [(key1542, -1), (key1896, -1), (key1548, 2), (key1542, -1), (key1896, -1), (key1387, 2), (key1899, 2), (key1393, -1), (key1556, -1), (key1548, 2), (key1393, -1), (key1556, -1), (key1569, 1), (key1903, 1), (key1575, -2), (key1569, 1), (key1903, 1), (key1292, -2), (key1911, -2), (key1298, 1), (key1593, 1), (key1575, -2), (key1298, 1), (key1593, 1), (key1420, -1), (key1920, -1), (key1426, 1), (key1624, 1), (key1312, 1), (key1926, 1), (key1318, -1), (key1633, -1), (key1420, -1), (key1920, -1), (key1312, 1), (key1926, 1), (key1426, 1), (key1624, 1), (key1318, -1), (key1633, -1)]

theorem rawRowCheck5915 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form0 = rawRow5915 := by decide +kernel

def row5915 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 2), (key1542, -2), (key1548, 4), (key1556, -2), (key1569, 2), (key1575, -4), (key1593, 2), (key1624, 2), (key1633, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

theorem rowCheck5915 : row5915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5915 := by decide +kernel

theorem rowEval5915 (x : Key → ℝ) : Integer.Sparse.eval row5915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5915, Integer.Sparse.eval_collectBalanced, rawRowCheck5915]

def rawRow5916 : Integer.Sparse Key := [(key1896, -1), (key1542, -1), (key1548, 2), (key1896, -1), (key1542, -1), (key1899, 2), (key1387, 2), (key1556, -1), (key1393, -1), (key1548, 2), (key1556, -1), (key1393, -1), (key1903, 1), (key1569, 1), (key1575, -2), (key1903, 1), (key1569, 1), (key1911, -2), (key1292, -2), (key1593, 1), (key1298, 1), (key1575, -2), (key1593, 1), (key1298, 1), (key1920, -1), (key1420, -1), (key1624, 1), (key1426, 1), (key1926, 1), (key1312, 1), (key1633, -1), (key1318, -1), (key1920, -1), (key1420, -1), (key1926, 1), (key1312, 1), (key1624, 1), (key1426, 1), (key1633, -1), (key1318, -1)]

theorem rawRowCheck5916 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form0 = rawRow5916 := by decide +kernel

def row5916 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 2), (key1542, -2), (key1548, 4), (key1556, -2), (key1569, 2), (key1575, -4), (key1593, 2), (key1624, 2), (key1633, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

theorem rowCheck5916 : row5916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5916 := by decide +kernel

theorem rowEval5916 (x : Key → ℝ) : Integer.Sparse.eval row5916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5916, Integer.Sparse.eval_collectBalanced, rawRowCheck5916]

def rawRow5917 : Integer.Sparse Key := [(key1548, -1), (key1896, -1), (key1542, 2), (key1556, -1), (key1899, -1), (key1393, 2), (key1896, 2), (key1387, -1), (key1542, -1), (key1556, 2), (key1393, -1), (key1548, -1), (key1575, 1), (key1903, 1), (key1569, -2), (key1593, 1), (key1911, 1), (key1298, -2), (key1903, -2), (key1292, 1), (key1569, 1), (key1593, -2), (key1298, 1), (key1575, 1), (key1426, -1), (key1918, -1), (key1420, 1), (key1618, 1), (key1318, 1), (key1918, 1), (key1312, -1), (key1618, -1), (key1444, -1), (key1926, -1), (key1326, 1), (key1920, 1), (key1444, 1), (key1633, 1), (key1326, -1), (key1624, -1)]

theorem rawRowCheck5917 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form0 = rawRow5917 := by decide +kernel

def row5917 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5917 : row5917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5917 := by decide +kernel

theorem rowEval5917 (x : Key → ℝ) : Integer.Sparse.eval row5917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5917, Integer.Sparse.eval_collectBalanced, rawRowCheck5917]

def rawRow5918 : Integer.Sparse Key := [(key1896, -1), (key1548, -1), (key1542, 2), (key1899, -1), (key1556, -1), (key1896, 2), (key1393, 2), (key1542, -1), (key1387, -1), (key1556, 2), (key1548, -1), (key1393, -1), (key1903, 1), (key1575, 1), (key1569, -2), (key1911, 1), (key1593, 1), (key1903, -2), (key1298, -2), (key1569, 1), (key1292, 1), (key1593, -2), (key1575, 1), (key1298, 1), (key1918, -1), (key1426, -1), (key1618, 1), (key1420, 1), (key1918, 1), (key1318, 1), (key1618, -1), (key1312, -1), (key1926, -1), (key1444, -1), (key1920, 1), (key1326, 1), (key1633, 1), (key1444, 1), (key1624, -1), (key1326, -1)]

theorem rawRowCheck5918 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form0 = rawRow5918 := by decide +kernel

def row5918 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5918 : row5918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5918 := by decide +kernel

theorem rowEval5918 (x : Key → ℝ) : Integer.Sparse.eval row5918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5918, Integer.Sparse.eval_collectBalanced, rawRowCheck5918]

def rawRow5919 : Integer.Sparse Key := [(key1556, -1), (key1556, -1), (key1899, 2), (key1393, -1), (key1393, -1), (key1548, 2), (key1548, 2), (key1896, -1), (key1896, -1), (key1387, 2), (key1542, -1), (key1542, -1), (key1593, 1), (key1593, 1), (key1911, -2), (key1298, 1), (key1298, 1), (key1575, -2), (key1575, -2), (key1903, 1), (key1903, 1), (key1292, -2), (key1569, 1), (key1569, 1), (key1633, -1), (key1633, -1), (key1926, 1), (key1926, 1), (key1624, 1), (key1624, 1), (key1920, -1), (key1920, -1), (key1318, -1), (key1318, -1), (key1426, 1), (key1426, 1), (key1312, 1), (key1312, 1), (key1420, -1), (key1420, -1)]

theorem rawRowCheck5919 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form0 = rawRow5919 := by decide +kernel

def row5919 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 2), (key1542, -2), (key1548, 4), (key1556, -2), (key1569, 2), (key1575, -4), (key1593, 2), (key1624, 2), (key1633, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

theorem rowCheck5919 : row5919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5919 := by decide +kernel

theorem rowEval5919 (x : Key → ℝ) : Integer.Sparse.eval row5919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5919, Integer.Sparse.eval_collectBalanced, rawRowCheck5919]

def rawRow5920 : Integer.Sparse Key := [(key1556, -1), (key1899, -1), (key1556, 2), (key1548, -1), (key1896, -1), (key1393, 2), (key1896, 2), (key1393, -1), (key1548, -1), (key1542, 2), (key1387, -1), (key1542, -1), (key1593, 1), (key1911, 1), (key1593, -2), (key1575, 1), (key1903, 1), (key1298, -2), (key1903, -2), (key1298, 1), (key1575, 1), (key1569, -2), (key1292, 1), (key1569, 1), (key1444, -1), (key1926, -1), (key1444, 1), (key1633, 1), (key1326, 1), (key1920, 1), (key1326, -1), (key1624, -1), (key1426, -1), (key1918, -1), (key1318, 1), (key1918, 1), (key1420, 1), (key1618, 1), (key1312, -1), (key1618, -1)]

theorem rawRowCheck5920 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form0 = rawRow5920 := by decide +kernel

def row5920 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5920 : row5920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5920 := by decide +kernel

theorem rowEval5920 (x : Key → ℝ) : Integer.Sparse.eval row5920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5920, Integer.Sparse.eval_collectBalanced, rawRowCheck5920]

def rawRow5921 : Integer.Sparse Key := [(key1899, -1), (key1556, -1), (key1556, 2), (key1896, -1), (key1548, -1), (key1896, 2), (key1393, 2), (key1548, -1), (key1393, -1), (key1542, 2), (key1542, -1), (key1387, -1), (key1911, 1), (key1593, 1), (key1593, -2), (key1903, 1), (key1575, 1), (key1903, -2), (key1298, -2), (key1575, 1), (key1298, 1), (key1569, -2), (key1569, 1), (key1292, 1), (key1926, -1), (key1444, -1), (key1633, 1), (key1444, 1), (key1920, 1), (key1326, 1), (key1624, -1), (key1326, -1), (key1918, -1), (key1426, -1), (key1918, 1), (key1318, 1), (key1618, 1), (key1420, 1), (key1618, -1), (key1312, -1)]

theorem rawRowCheck5921 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form0 = rawRow5921 := by decide +kernel

def row5921 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5921 : row5921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5921 := by decide +kernel

theorem rowEval5921 (x : Key → ℝ) : Integer.Sparse.eval row5921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5921, Integer.Sparse.eval_collectBalanced, rawRowCheck5921]

def rawRow5922 : Integer.Sparse Key := [(key1420, -1), (key1472, -1), (key1426, 2), (key1618, -1), (key1681, -1), (key1569, 2), (key1683, 2), (key1575, -1), (key1624, -1), (key1918, 2), (key1903, -1), (key1920, -1), (key1312, 1), (key1351, 1), (key1318, -2), (key1618, 1), (key1681, 1), (key1542, -2), (key1689, -2), (key1548, 1), (key1633, 1), (key1918, -2), (key1896, 1), (key1926, 1), (key1292, -1), (key1354, -1), (key1298, 1), (key1326, 1), (key1387, 1), (key1480, 1), (key1393, -1), (key1444, -1), (key1569, -1), (key1683, -1), (key1542, 1), (key1689, 1), (key1903, 1), (key1920, 1), (key1896, -1), (key1926, -1)]

theorem rawRowCheck5922 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form0 = rawRow5922 := by decide +kernel

def row5922 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5922 : row5922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5922 := by decide +kernel

theorem rowEval5922 (x : Key → ℝ) : Integer.Sparse.eval row5922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5922, Integer.Sparse.eval_collectBalanced, rawRowCheck5922]

def rawRow5923 : Integer.Sparse Key := [(key1472, -1), (key1420, -1), (key1426, 2), (key1681, -1), (key1618, -1), (key1683, 2), (key1569, 2), (key1624, -1), (key1575, -1), (key1918, 2), (key1920, -1), (key1903, -1), (key1351, 1), (key1312, 1), (key1318, -2), (key1681, 1), (key1618, 1), (key1689, -2), (key1542, -2), (key1633, 1), (key1548, 1), (key1918, -2), (key1926, 1), (key1896, 1), (key1354, -1), (key1292, -1), (key1326, 1), (key1298, 1), (key1480, 1), (key1387, 1), (key1444, -1), (key1393, -1), (key1683, -1), (key1569, -1), (key1689, 1), (key1542, 1), (key1920, 1), (key1903, 1), (key1926, -1), (key1896, -1)]

theorem rawRowCheck5923 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form0 = rawRow5923 := by decide +kernel

def row5923 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5923 : row5923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5923 := by decide +kernel

theorem rowEval5923 (x : Key → ℝ) : Integer.Sparse.eval row5923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5923, Integer.Sparse.eval_collectBalanced, rawRowCheck5923]

def rawRow5924 : Integer.Sparse Key := [(key1426, -1), (key1472, -1), (key1420, 2), (key1624, -1), (key1683, -1), (key1575, 2), (key1681, 2), (key1569, -1), (key1618, -1), (key1920, 2), (key1903, -1), (key1918, -1), (key1318, 1), (key1351, 1), (key1312, -2), (key1633, 1), (key1689, 1), (key1548, -2), (key1681, -2), (key1542, 1), (key1618, 1), (key1926, -2), (key1896, 1), (key1918, 1), (key1298, -1), (key1351, -1), (key1292, 1), (key1312, 1), (key1393, 1), (key1472, 1), (key1387, -1), (key1420, -1), (key1593, -1), (key1689, -1), (key1556, 1), (key1683, 1), (key1911, 1), (key1926, 1), (key1899, -1), (key1920, -1)]

theorem rawRowCheck5924 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form0 = rawRow5924 := by decide +kernel

def row5924 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5924 : row5924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5924 := by decide +kernel

theorem rowEval5924 (x : Key → ℝ) : Integer.Sparse.eval row5924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5924, Integer.Sparse.eval_collectBalanced, rawRowCheck5924]

def rawRow5925 : Integer.Sparse Key := [(key1472, -1), (key1426, -1), (key1420, 2), (key1683, -1), (key1624, -1), (key1681, 2), (key1575, 2), (key1618, -1), (key1569, -1), (key1920, 2), (key1918, -1), (key1903, -1), (key1351, 1), (key1318, 1), (key1312, -2), (key1689, 1), (key1633, 1), (key1681, -2), (key1548, -2), (key1618, 1), (key1542, 1), (key1926, -2), (key1918, 1), (key1896, 1), (key1351, -1), (key1298, -1), (key1312, 1), (key1292, 1), (key1472, 1), (key1393, 1), (key1420, -1), (key1387, -1), (key1689, -1), (key1593, -1), (key1683, 1), (key1556, 1), (key1926, 1), (key1911, 1), (key1920, -1), (key1899, -1)]

theorem rawRowCheck5925 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form0 = rawRow5925 := by decide +kernel

def row5925 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5925 : row5925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5925 := by decide +kernel

theorem rowEval5925 (x : Key → ℝ) : Integer.Sparse.eval row5925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5925, Integer.Sparse.eval_collectBalanced, rawRowCheck5925]

def rawRow5926 : Integer.Sparse Key := [(key1569, -1), (key1903, -1), (key1575, 2), (key1618, -1), (key1918, -1), (key1420, 2), (key1920, 2), (key1426, -1), (key1624, -1), (key1681, 2), (key1472, -1), (key1683, -1), (key1542, 1), (key1896, 1), (key1548, -2), (key1618, 1), (key1918, 1), (key1312, -2), (key1926, -2), (key1318, 1), (key1633, 1), (key1681, -2), (key1351, 1), (key1689, 1), (key1387, -1), (key1899, -1), (key1393, 1), (key1556, 1), (key1292, 1), (key1911, 1), (key1298, -1), (key1593, -1), (key1420, -1), (key1920, -1), (key1312, 1), (key1926, 1), (key1472, 1), (key1683, 1), (key1351, -1), (key1689, -1)]

theorem rawRowCheck5926 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form0 = rawRow5926 := by decide +kernel

def row5926 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5926 : row5926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5926 := by decide +kernel

theorem rowEval5926 (x : Key → ℝ) : Integer.Sparse.eval row5926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5926, Integer.Sparse.eval_collectBalanced, rawRowCheck5926]

def rawRow5927 : Integer.Sparse Key := [(key1903, -1), (key1569, -1), (key1575, 2), (key1918, -1), (key1618, -1), (key1920, 2), (key1420, 2), (key1624, -1), (key1426, -1), (key1681, 2), (key1683, -1), (key1472, -1), (key1896, 1), (key1542, 1), (key1548, -2), (key1918, 1), (key1618, 1), (key1926, -2), (key1312, -2), (key1633, 1), (key1318, 1), (key1681, -2), (key1689, 1), (key1351, 1), (key1899, -1), (key1387, -1), (key1556, 1), (key1393, 1), (key1911, 1), (key1292, 1), (key1593, -1), (key1298, -1), (key1920, -1), (key1420, -1), (key1926, 1), (key1312, 1), (key1683, 1), (key1472, 1), (key1689, -1), (key1351, -1)]

theorem rawRowCheck5927 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form0 = rawRow5927 := by decide +kernel

def row5927 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5927 : row5927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5927 := by decide +kernel

theorem rowEval5927 (x : Key → ℝ) : Integer.Sparse.eval row5927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5927, Integer.Sparse.eval_collectBalanced, rawRowCheck5927]

def rawRow5928 : Integer.Sparse Key := [(key1575, -1), (key1903, -1), (key1569, 2), (key1624, -1), (key1920, -1), (key1426, 2), (key1918, 2), (key1420, -1), (key1618, -1), (key1683, 2), (key1472, -1), (key1681, -1), (key1548, 1), (key1896, 1), (key1542, -2), (key1633, 1), (key1926, 1), (key1318, -2), (key1918, -2), (key1312, 1), (key1618, 1), (key1689, -2), (key1351, 1), (key1681, 1), (key1393, -1), (key1896, -1), (key1387, 1), (key1542, 1), (key1298, 1), (key1903, 1), (key1292, -1), (key1569, -1), (key1444, -1), (key1926, -1), (key1326, 1), (key1920, 1), (key1480, 1), (key1689, 1), (key1354, -1), (key1683, -1)]

theorem rawRowCheck5928 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form0 = rawRow5928 := by decide +kernel

def row5928 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5928 : row5928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5928 := by decide +kernel

theorem rowEval5928 (x : Key → ℝ) : Integer.Sparse.eval row5928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5928, Integer.Sparse.eval_collectBalanced, rawRowCheck5928]

def rawRow5929 : Integer.Sparse Key := [(key1903, -1), (key1575, -1), (key1569, 2), (key1920, -1), (key1624, -1), (key1918, 2), (key1426, 2), (key1618, -1), (key1420, -1), (key1683, 2), (key1681, -1), (key1472, -1), (key1896, 1), (key1548, 1), (key1542, -2), (key1926, 1), (key1633, 1), (key1918, -2), (key1318, -2), (key1618, 1), (key1312, 1), (key1689, -2), (key1681, 1), (key1351, 1), (key1896, -1), (key1393, -1), (key1542, 1), (key1387, 1), (key1903, 1), (key1298, 1), (key1569, -1), (key1292, -1), (key1926, -1), (key1444, -1), (key1920, 1), (key1326, 1), (key1689, 1), (key1480, 1), (key1683, -1), (key1354, -1)]

theorem rawRowCheck5929 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form0 = rawRow5929 := by decide +kernel

def row5929 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5929 : row5929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5929 := by decide +kernel

theorem rowEval5929 (x : Key → ℝ) : Integer.Sparse.eval row5929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5929, Integer.Sparse.eval_collectBalanced, rawRowCheck5929]

def rawRow5930 : Integer.Sparse Key := [(key1618, -1), (key1681, -1), (key1918, 2), (key1420, -1), (key1472, -1), (key1569, 2), (key1683, 2), (key1903, -1), (key1920, -1), (key1426, 2), (key1575, -1), (key1624, -1), (key1618, 1), (key1681, 1), (key1918, -2), (key1312, 1), (key1351, 1), (key1542, -2), (key1689, -2), (key1896, 1), (key1926, 1), (key1318, -2), (key1548, 1), (key1633, 1), (key1569, -1), (key1683, -1), (key1903, 1), (key1920, 1), (key1542, 1), (key1689, 1), (key1896, -1), (key1926, -1), (key1292, -1), (key1354, -1), (key1387, 1), (key1480, 1), (key1298, 1), (key1326, 1), (key1393, -1), (key1444, -1)]

theorem rawRowCheck5930 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form0 = rawRow5930 := by decide +kernel

def row5930 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5930 : row5930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5930 := by decide +kernel

theorem rowEval5930 (x : Key → ℝ) : Integer.Sparse.eval row5930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5930, Integer.Sparse.eval_collectBalanced, rawRowCheck5930]

def rawRow5931 : Integer.Sparse Key := [(key1681, -1), (key1618, -1), (key1918, 2), (key1472, -1), (key1420, -1), (key1683, 2), (key1569, 2), (key1920, -1), (key1903, -1), (key1426, 2), (key1624, -1), (key1575, -1), (key1681, 1), (key1618, 1), (key1918, -2), (key1351, 1), (key1312, 1), (key1689, -2), (key1542, -2), (key1926, 1), (key1896, 1), (key1318, -2), (key1633, 1), (key1548, 1), (key1683, -1), (key1569, -1), (key1920, 1), (key1903, 1), (key1689, 1), (key1542, 1), (key1926, -1), (key1896, -1), (key1354, -1), (key1292, -1), (key1480, 1), (key1387, 1), (key1326, 1), (key1298, 1), (key1444, -1), (key1393, -1)]

theorem rawRowCheck5931 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form0 = rawRow5931 := by decide +kernel

def row5931 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5931 : row5931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5931 := by decide +kernel

theorem rowEval5931 (x : Key → ℝ) : Integer.Sparse.eval row5931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5931, Integer.Sparse.eval_collectBalanced, rawRowCheck5931]

def rawRow5932 : Integer.Sparse Key := [(key1618, -1), (key1918, -1), (key1681, 2), (key1569, -1), (key1903, -1), (key1420, 2), (key1920, 2), (key1472, -1), (key1683, -1), (key1575, 2), (key1426, -1), (key1624, -1), (key1618, 1), (key1918, 1), (key1681, -2), (key1542, 1), (key1896, 1), (key1312, -2), (key1926, -2), (key1351, 1), (key1689, 1), (key1548, -2), (key1318, 1), (key1633, 1), (key1420, -1), (key1920, -1), (key1472, 1), (key1683, 1), (key1312, 1), (key1926, 1), (key1351, -1), (key1689, -1), (key1387, -1), (key1899, -1), (key1292, 1), (key1911, 1), (key1393, 1), (key1556, 1), (key1298, -1), (key1593, -1)]

theorem rawRowCheck5932 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form0 = rawRow5932 := by decide +kernel

def row5932 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5932 : row5932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5932 := by decide +kernel

theorem rowEval5932 (x : Key → ℝ) : Integer.Sparse.eval row5932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5932, Integer.Sparse.eval_collectBalanced, rawRowCheck5932]

def rawRow5933 : Integer.Sparse Key := [(key1918, -1), (key1618, -1), (key1681, 2), (key1903, -1), (key1569, -1), (key1920, 2), (key1420, 2), (key1683, -1), (key1472, -1), (key1575, 2), (key1624, -1), (key1426, -1), (key1918, 1), (key1618, 1), (key1681, -2), (key1896, 1), (key1542, 1), (key1926, -2), (key1312, -2), (key1689, 1), (key1351, 1), (key1548, -2), (key1633, 1), (key1318, 1), (key1920, -1), (key1420, -1), (key1683, 1), (key1472, 1), (key1926, 1), (key1312, 1), (key1689, -1), (key1351, -1), (key1899, -1), (key1387, -1), (key1911, 1), (key1292, 1), (key1556, 1), (key1393, 1), (key1593, -1), (key1298, -1)]

theorem rawRowCheck5933 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form0 = rawRow5933 := by decide +kernel

def row5933 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5933 : row5933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5933 := by decide +kernel

theorem rowEval5933 (x : Key → ℝ) : Integer.Sparse.eval row5933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5933, Integer.Sparse.eval_collectBalanced, rawRowCheck5933]

def rawRow5934 : Integer.Sparse Key := [(key1624, -1), (key1683, -1), (key1920, 2), (key1426, -1), (key1472, -1), (key1575, 2), (key1681, 2), (key1903, -1), (key1918, -1), (key1420, 2), (key1569, -1), (key1618, -1), (key1633, 1), (key1689, 1), (key1926, -2), (key1318, 1), (key1351, 1), (key1548, -2), (key1681, -2), (key1896, 1), (key1918, 1), (key1312, -2), (key1542, 1), (key1618, 1), (key1593, -1), (key1689, -1), (key1911, 1), (key1926, 1), (key1556, 1), (key1683, 1), (key1899, -1), (key1920, -1), (key1298, -1), (key1351, -1), (key1393, 1), (key1472, 1), (key1292, 1), (key1312, 1), (key1387, -1), (key1420, -1)]

theorem rawRowCheck5934 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form0 = rawRow5934 := by decide +kernel

def row5934 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5934 : row5934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5934 := by decide +kernel

theorem rowEval5934 (x : Key → ℝ) : Integer.Sparse.eval row5934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5934, Integer.Sparse.eval_collectBalanced, rawRowCheck5934]

def rawRow5935 : Integer.Sparse Key := [(key1683, -1), (key1624, -1), (key1920, 2), (key1472, -1), (key1426, -1), (key1681, 2), (key1575, 2), (key1918, -1), (key1903, -1), (key1420, 2), (key1618, -1), (key1569, -1), (key1689, 1), (key1633, 1), (key1926, -2), (key1351, 1), (key1318, 1), (key1681, -2), (key1548, -2), (key1918, 1), (key1896, 1), (key1312, -2), (key1618, 1), (key1542, 1), (key1689, -1), (key1593, -1), (key1926, 1), (key1911, 1), (key1683, 1), (key1556, 1), (key1920, -1), (key1899, -1), (key1351, -1), (key1298, -1), (key1472, 1), (key1393, 1), (key1312, 1), (key1292, 1), (key1420, -1), (key1387, -1)]

theorem rawRowCheck5935 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form0 = rawRow5935 := by decide +kernel

def row5935 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck5935 : row5935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5935 := by decide +kernel

theorem rowEval5935 (x : Key → ℝ) : Integer.Sparse.eval row5935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5935, Integer.Sparse.eval_collectBalanced, rawRowCheck5935]

def rawRow5936 : Integer.Sparse Key := [(key1624, -1), (key1920, -1), (key1683, 2), (key1575, -1), (key1903, -1), (key1426, 2), (key1918, 2), (key1472, -1), (key1681, -1), (key1569, 2), (key1420, -1), (key1618, -1), (key1633, 1), (key1926, 1), (key1689, -2), (key1548, 1), (key1896, 1), (key1318, -2), (key1918, -2), (key1351, 1), (key1681, 1), (key1542, -2), (key1312, 1), (key1618, 1), (key1444, -1), (key1926, -1), (key1480, 1), (key1689, 1), (key1326, 1), (key1920, 1), (key1354, -1), (key1683, -1), (key1393, -1), (key1896, -1), (key1298, 1), (key1903, 1), (key1387, 1), (key1542, 1), (key1292, -1), (key1569, -1)]

theorem rawRowCheck5936 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form0 = rawRow5936 := by decide +kernel

def row5936 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5936 : row5936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5936 := by decide +kernel

theorem rowEval5936 (x : Key → ℝ) : Integer.Sparse.eval row5936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5936, Integer.Sparse.eval_collectBalanced, rawRowCheck5936]

def rawRow5937 : Integer.Sparse Key := [(key1920, -1), (key1624, -1), (key1683, 2), (key1903, -1), (key1575, -1), (key1918, 2), (key1426, 2), (key1681, -1), (key1472, -1), (key1569, 2), (key1618, -1), (key1420, -1), (key1926, 1), (key1633, 1), (key1689, -2), (key1896, 1), (key1548, 1), (key1918, -2), (key1318, -2), (key1681, 1), (key1351, 1), (key1542, -2), (key1618, 1), (key1312, 1), (key1926, -1), (key1444, -1), (key1689, 1), (key1480, 1), (key1920, 1), (key1326, 1), (key1683, -1), (key1354, -1), (key1896, -1), (key1393, -1), (key1903, 1), (key1298, 1), (key1542, 1), (key1387, 1), (key1569, -1), (key1292, -1)]

theorem rawRowCheck5937 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form0 = rawRow5937 := by decide +kernel

def row5937 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

theorem rowCheck5937 : row5937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5937 := by decide +kernel

theorem rowEval5937 (x : Key → ℝ) : Integer.Sparse.eval row5937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5937, Integer.Sparse.eval_collectBalanced, rawRowCheck5937]

def rawRow5938 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key240, 2), (key249, -1), (key252, -1), (key249, 2), (key268, 2), (key252, -1), (key268, -1), (key262, 2), (key262, -1), (key273, -1), (key303, 1), (key306, 1), (key306, -2), (key386, 1), (key389, 1), (key386, -2), (key569, -2), (key389, 1), (key569, 1), (key399, -2), (key399, 1), (key574, 1), (key317, -1), (key336, -1), (key320, 1), (key336, 1), (key407, 1), (key579, 1), (key410, -1), (key579, -1), (key436, -1), (key468, -1), (key436, 1), (key594, 1), (key444, 1), (key471, 1), (key444, -1), (key597, -1)]

theorem rawRowCheck5938 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form1 = rawRow5938 := by decide +kernel

def row5938 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5938 : row5938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5938 := by decide +kernel

theorem rowEval5938 (x : Key → ℝ) : Integer.Sparse.eval row5938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5938, Integer.Sparse.eval_collectBalanced, rawRowCheck5938]

def rawRow5939 : Integer.Sparse Key := [(key240, -1), (key237, -1), (key240, 2), (key252, -1), (key249, -1), (key268, 2), (key249, 2), (key268, -1), (key252, -1), (key262, 2), (key273, -1), (key262, -1), (key306, 1), (key303, 1), (key306, -2), (key389, 1), (key386, 1), (key569, -2), (key386, -2), (key569, 1), (key389, 1), (key399, -2), (key574, 1), (key399, 1), (key336, -1), (key317, -1), (key336, 1), (key320, 1), (key579, 1), (key407, 1), (key579, -1), (key410, -1), (key468, -1), (key436, -1), (key594, 1), (key436, 1), (key471, 1), (key444, 1), (key597, -1), (key444, -1)]

theorem rawRowCheck5939 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form1 = rawRow5939 := by decide +kernel

def row5939 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5939 : row5939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5939 := by decide +kernel

theorem rowEval5939 (x : Key → ℝ) : Integer.Sparse.eval row5939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5939, Integer.Sparse.eval_collectBalanced, rawRowCheck5939]

def rawRow5940 : Integer.Sparse Key := [(key240, -1), (key240, -1), (key237, 2), (key268, -1), (key268, -1), (key252, 2), (key252, 2), (key249, -1), (key249, -1), (key273, 2), (key262, -1), (key262, -1), (key306, 1), (key306, 1), (key303, -2), (key569, 1), (key569, 1), (key389, -2), (key389, -2), (key386, 1), (key386, 1), (key574, -2), (key399, 1), (key399, 1), (key320, -1), (key320, -1), (key317, 1), (key317, 1), (key410, 1), (key410, 1), (key407, -1), (key407, -1), (key594, -1), (key594, -1), (key468, 1), (key468, 1), (key597, 1), (key597, 1), (key471, -1), (key471, -1)]

theorem rawRowCheck5940 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form1 = rawRow5940 := by decide +kernel

def row5940 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key252, 4), (key262, -2), (key268, -2), (key273, 2), (key303, -2), (key306, 2), (key317, 2), (key320, -2), (key386, 2), (key389, -4), (key399, 2), (key407, -2), (key410, 2), (key468, 2), (key471, -2), (key569, 2), (key574, -2), (key594, -2), (key597, 2)]

theorem rowCheck5940 : row5940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5940 := by decide +kernel

theorem rowEval5940 (x : Key → ℝ) : Integer.Sparse.eval row5940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5940, Integer.Sparse.eval_collectBalanced, rawRowCheck5940]

def rawRow5941 : Integer.Sparse Key := [(key249, -1), (key252, -1), (key262, 2), (key237, -1), (key240, -1), (key249, 2), (key268, 2), (key262, -1), (key273, -1), (key240, 2), (key252, -1), (key268, -1), (key386, 1), (key389, 1), (key399, -2), (key303, 1), (key306, 1), (key386, -2), (key569, -2), (key399, 1), (key574, 1), (key306, -2), (key389, 1), (key569, 1), (key436, -1), (key468, -1), (key444, 1), (key471, 1), (key436, 1), (key594, 1), (key444, -1), (key597, -1), (key317, -1), (key336, -1), (key407, 1), (key579, 1), (key320, 1), (key336, 1), (key410, -1), (key579, -1)]

theorem rawRowCheck5941 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form1 = rawRow5941 := by decide +kernel

def row5941 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5941 : row5941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5941 := by decide +kernel

theorem rowEval5941 (x : Key → ℝ) : Integer.Sparse.eval row5941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5941, Integer.Sparse.eval_collectBalanced, rawRowCheck5941]

def rawRow5942 : Integer.Sparse Key := [(key252, -1), (key249, -1), (key262, 2), (key240, -1), (key237, -1), (key268, 2), (key249, 2), (key273, -1), (key262, -1), (key240, 2), (key268, -1), (key252, -1), (key389, 1), (key386, 1), (key399, -2), (key306, 1), (key303, 1), (key569, -2), (key386, -2), (key574, 1), (key399, 1), (key306, -2), (key569, 1), (key389, 1), (key468, -1), (key436, -1), (key471, 1), (key444, 1), (key594, 1), (key436, 1), (key597, -1), (key444, -1), (key336, -1), (key317, -1), (key579, 1), (key407, 1), (key336, 1), (key320, 1), (key579, -1), (key410, -1)]

theorem rawRowCheck5942 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form1 = rawRow5942 := by decide +kernel

def row5942 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5942 : row5942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5942 := by decide +kernel

theorem rowEval5942 (x : Key → ℝ) : Integer.Sparse.eval row5942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5942, Integer.Sparse.eval_collectBalanced, rawRowCheck5942]

def rawRow5943 : Integer.Sparse Key := [(key249, -1), (key262, -1), (key252, 2), (key249, -1), (key262, -1), (key237, 2), (key273, 2), (key240, -1), (key268, -1), (key252, 2), (key240, -1), (key268, -1), (key386, 1), (key399, 1), (key389, -2), (key386, 1), (key399, 1), (key303, -2), (key574, -2), (key306, 1), (key569, 1), (key389, -2), (key306, 1), (key569, 1), (key407, -1), (key471, -1), (key410, 1), (key468, 1), (key317, 1), (key597, 1), (key320, -1), (key594, -1), (key407, -1), (key471, -1), (key317, 1), (key597, 1), (key410, 1), (key468, 1), (key320, -1), (key594, -1)]

theorem rawRowCheck5943 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form1 = rawRow5943 := by decide +kernel

def row5943 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key252, 4), (key262, -2), (key268, -2), (key273, 2), (key303, -2), (key306, 2), (key317, 2), (key320, -2), (key386, 2), (key389, -4), (key399, 2), (key407, -2), (key410, 2), (key468, 2), (key471, -2), (key569, 2), (key574, -2), (key594, -2), (key597, 2)]

theorem rowCheck5943 : row5943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5943 := by decide +kernel

theorem rowEval5943 (x : Key → ℝ) : Integer.Sparse.eval row5943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5943, Integer.Sparse.eval_collectBalanced, rawRowCheck5943]

def rawRow5944 : Integer.Sparse Key := [(key262, -1), (key249, -1), (key252, 2), (key262, -1), (key249, -1), (key273, 2), (key237, 2), (key268, -1), (key240, -1), (key252, 2), (key268, -1), (key240, -1), (key399, 1), (key386, 1), (key389, -2), (key399, 1), (key386, 1), (key574, -2), (key303, -2), (key569, 1), (key306, 1), (key389, -2), (key569, 1), (key306, 1), (key471, -1), (key407, -1), (key468, 1), (key410, 1), (key597, 1), (key317, 1), (key594, -1), (key320, -1), (key471, -1), (key407, -1), (key597, 1), (key317, 1), (key468, 1), (key410, 1), (key594, -1), (key320, -1)]

theorem rawRowCheck5944 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form1 = rawRow5944 := by decide +kernel

def row5944 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key252, 4), (key262, -2), (key268, -2), (key273, 2), (key303, -2), (key306, 2), (key317, 2), (key320, -2), (key386, 2), (key389, -4), (key399, 2), (key407, -2), (key410, 2), (key468, 2), (key471, -2), (key569, 2), (key574, -2), (key594, -2), (key597, 2)]

theorem rowCheck5944 : row5944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5944 := by decide +kernel

theorem rowEval5944 (x : Key → ℝ) : Integer.Sparse.eval row5944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5944, Integer.Sparse.eval_collectBalanced, rawRowCheck5944]

def rawRow5945 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key249, 2), (key268, -1), (key273, -1), (key240, 2), (key262, 2), (key237, -1), (key249, -1), (key268, 2), (key240, -1), (key252, -1), (key389, 1), (key399, 1), (key386, -2), (key569, 1), (key574, 1), (key306, -2), (key399, -2), (key303, 1), (key386, 1), (key569, -2), (key306, 1), (key389, 1), (key410, -1), (key444, -1), (key407, 1), (key436, 1), (key320, 1), (key444, 1), (key317, -1), (key436, -1), (key579, -1), (key597, -1), (key336, 1), (key471, 1), (key579, 1), (key594, 1), (key336, -1), (key468, -1)]

theorem rawRowCheck5945 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form1 = rawRow5945 := by decide +kernel

def row5945 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5945 : row5945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5945 := by decide +kernel

theorem rowEval5945 (x : Key → ℝ) : Integer.Sparse.eval row5945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5945, Integer.Sparse.eval_collectBalanced, rawRowCheck5945]

def rawRow5946 : Integer.Sparse Key := [(key262, -1), (key252, -1), (key249, 2), (key273, -1), (key268, -1), (key262, 2), (key240, 2), (key249, -1), (key237, -1), (key268, 2), (key252, -1), (key240, -1), (key399, 1), (key389, 1), (key386, -2), (key574, 1), (key569, 1), (key399, -2), (key306, -2), (key386, 1), (key303, 1), (key569, -2), (key389, 1), (key306, 1), (key444, -1), (key410, -1), (key436, 1), (key407, 1), (key444, 1), (key320, 1), (key436, -1), (key317, -1), (key597, -1), (key579, -1), (key471, 1), (key336, 1), (key594, 1), (key579, 1), (key468, -1), (key336, -1)]

theorem rawRowCheck5946 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form1 = rawRow5946 := by decide +kernel

def row5946 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5946 : row5946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5946 := by decide +kernel

theorem rowEval5946 (x : Key → ℝ) : Integer.Sparse.eval row5946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5946, Integer.Sparse.eval_collectBalanced, rawRowCheck5946]

def rawRow5947 : Integer.Sparse Key := [(key268, -1), (key268, -1), (key273, 2), (key240, -1), (key240, -1), (key252, 2), (key252, 2), (key262, -1), (key262, -1), (key237, 2), (key249, -1), (key249, -1), (key569, 1), (key569, 1), (key574, -2), (key306, 1), (key306, 1), (key389, -2), (key389, -2), (key399, 1), (key399, 1), (key303, -2), (key386, 1), (key386, 1), (key594, -1), (key594, -1), (key597, 1), (key597, 1), (key468, 1), (key468, 1), (key471, -1), (key471, -1), (key320, -1), (key320, -1), (key410, 1), (key410, 1), (key317, 1), (key317, 1), (key407, -1), (key407, -1)]

theorem rawRowCheck5947 : GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form1 = rawRow5947 := by decide +kernel

def row5947 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key252, 4), (key262, -2), (key268, -2), (key273, 2), (key303, -2), (key306, 2), (key317, 2), (key320, -2), (key386, 2), (key389, -4), (key399, 2), (key407, -2), (key410, 2), (key468, 2), (key471, -2), (key569, 2), (key574, -2), (key594, -2), (key597, 2)]

theorem rowCheck5947 : row5947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5947 := by decide +kernel

theorem rowEval5947 (x : Key → ℝ) : Integer.Sparse.eval row5947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5947, Integer.Sparse.eval_collectBalanced, rawRowCheck5947]

def rawRow5948 : Integer.Sparse Key := [(key268, -1), (key273, -1), (key268, 2), (key252, -1), (key262, -1), (key240, 2), (key262, 2), (key240, -1), (key252, -1), (key249, 2), (key237, -1), (key249, -1), (key569, 1), (key574, 1), (key569, -2), (key389, 1), (key399, 1), (key306, -2), (key399, -2), (key306, 1), (key389, 1), (key386, -2), (key303, 1), (key386, 1), (key579, -1), (key597, -1), (key579, 1), (key594, 1), (key336, 1), (key471, 1), (key336, -1), (key468, -1), (key410, -1), (key444, -1), (key320, 1), (key444, 1), (key407, 1), (key436, 1), (key317, -1), (key436, -1)]

theorem rawRowCheck5948 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form1 = rawRow5948 := by decide +kernel

def row5948 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5948 : row5948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5948 := by decide +kernel

theorem rowEval5948 (x : Key → ℝ) : Integer.Sparse.eval row5948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5948, Integer.Sparse.eval_collectBalanced, rawRowCheck5948]

def rawRow5949 : Integer.Sparse Key := [(key273, -1), (key268, -1), (key268, 2), (key262, -1), (key252, -1), (key262, 2), (key240, 2), (key252, -1), (key240, -1), (key249, 2), (key249, -1), (key237, -1), (key574, 1), (key569, 1), (key569, -2), (key399, 1), (key389, 1), (key399, -2), (key306, -2), (key389, 1), (key306, 1), (key386, -2), (key386, 1), (key303, 1), (key597, -1), (key579, -1), (key594, 1), (key579, 1), (key471, 1), (key336, 1), (key468, -1), (key336, -1), (key444, -1), (key410, -1), (key444, 1), (key320, 1), (key436, 1), (key407, 1), (key436, -1), (key317, -1)]

theorem rawRowCheck5949 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form1 = rawRow5949 := by decide +kernel

def row5949 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5949 : row5949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5949 := by decide +kernel

theorem rowEval5949 (x : Key → ℝ) : Integer.Sparse.eval row5949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5949, Integer.Sparse.eval_collectBalanced, rawRowCheck5949]

def rawRow5950 : Integer.Sparse Key := [(key303, -1), (key306, -1), (key306, 2), (key317, -1), (key320, -1), (key317, 2), (key336, 2), (key320, -1), (key336, -1), (key330, 2), (key330, -1), (key342, -1), (key237, 1), (key240, 1), (key240, -2), (key407, 1), (key410, 1), (key407, -2), (key579, -2), (key410, 1), (key579, 1), (key420, -2), (key420, 1), (key585, 1), (key249, -1), (key268, -1), (key252, 1), (key268, 1), (key386, 1), (key569, 1), (key389, -1), (key569, -1), (key436, -1), (key468, -1), (key436, 1), (key594, 1), (key452, 1), (key477, 1), (key452, -1), (key603, -1)]

theorem rawRowCheck5950 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form1 = rawRow5950 := by decide +kernel

def row5950 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5950 : row5950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5950 := by decide +kernel

theorem rowEval5950 (x : Key → ℝ) : Integer.Sparse.eval row5950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5950, Integer.Sparse.eval_collectBalanced, rawRowCheck5950]

def rawRow5951 : Integer.Sparse Key := [(key306, -1), (key303, -1), (key306, 2), (key320, -1), (key317, -1), (key336, 2), (key317, 2), (key336, -1), (key320, -1), (key330, 2), (key342, -1), (key330, -1), (key240, 1), (key237, 1), (key240, -2), (key410, 1), (key407, 1), (key579, -2), (key407, -2), (key579, 1), (key410, 1), (key420, -2), (key585, 1), (key420, 1), (key268, -1), (key249, -1), (key268, 1), (key252, 1), (key569, 1), (key386, 1), (key569, -1), (key389, -1), (key468, -1), (key436, -1), (key594, 1), (key436, 1), (key477, 1), (key452, 1), (key603, -1), (key452, -1)]

theorem rawRowCheck5951 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form1 = rawRow5951 := by decide +kernel

def row5951 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5951 : row5951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5951 := by decide +kernel

theorem rowEval5951 (x : Key → ℝ) : Integer.Sparse.eval row5951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5951, Integer.Sparse.eval_collectBalanced, rawRowCheck5951]

def rawRow5952 : Integer.Sparse Key := [(key306, -1), (key306, -1), (key303, 2), (key336, -1), (key336, -1), (key320, 2), (key320, 2), (key317, -1), (key317, -1), (key342, 2), (key330, -1), (key330, -1), (key240, 1), (key240, 1), (key237, -2), (key579, 1), (key579, 1), (key410, -2), (key410, -2), (key407, 1), (key407, 1), (key585, -2), (key420, 1), (key420, 1), (key252, -1), (key252, -1), (key249, 1), (key249, 1), (key389, 1), (key389, 1), (key386, -1), (key386, -1), (key594, -1), (key594, -1), (key468, 1), (key468, 1), (key603, 1), (key603, 1), (key477, -1), (key477, -1)]

theorem rawRowCheck5952 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form1 = rawRow5952 := by decide +kernel

def row5952 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key252, -2), (key303, 2), (key306, -2), (key317, -2), (key320, 4), (key330, -2), (key336, -2), (key342, 2), (key386, -2), (key389, 2), (key407, 2), (key410, -4), (key420, 2), (key468, 2), (key477, -2), (key579, 2), (key585, -2), (key594, -2), (key603, 2)]

theorem rowCheck5952 : row5952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5952 := by decide +kernel

theorem rowEval5952 (x : Key → ℝ) : Integer.Sparse.eval row5952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5952, Integer.Sparse.eval_collectBalanced, rawRowCheck5952]

def rawRow5953 : Integer.Sparse Key := [(key317, -1), (key320, -1), (key330, 2), (key303, -1), (key306, -1), (key317, 2), (key336, 2), (key330, -1), (key342, -1), (key306, 2), (key320, -1), (key336, -1), (key407, 1), (key410, 1), (key420, -2), (key237, 1), (key240, 1), (key407, -2), (key579, -2), (key420, 1), (key585, 1), (key240, -2), (key410, 1), (key579, 1), (key436, -1), (key468, -1), (key452, 1), (key477, 1), (key436, 1), (key594, 1), (key452, -1), (key603, -1), (key249, -1), (key268, -1), (key386, 1), (key569, 1), (key252, 1), (key268, 1), (key389, -1), (key569, -1)]

theorem rawRowCheck5953 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form1 = rawRow5953 := by decide +kernel

def row5953 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5953 : row5953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5953 := by decide +kernel

theorem rowEval5953 (x : Key → ℝ) : Integer.Sparse.eval row5953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5953, Integer.Sparse.eval_collectBalanced, rawRowCheck5953]

def rawRow5954 : Integer.Sparse Key := [(key320, -1), (key317, -1), (key330, 2), (key306, -1), (key303, -1), (key336, 2), (key317, 2), (key342, -1), (key330, -1), (key306, 2), (key336, -1), (key320, -1), (key410, 1), (key407, 1), (key420, -2), (key240, 1), (key237, 1), (key579, -2), (key407, -2), (key585, 1), (key420, 1), (key240, -2), (key579, 1), (key410, 1), (key468, -1), (key436, -1), (key477, 1), (key452, 1), (key594, 1), (key436, 1), (key603, -1), (key452, -1), (key268, -1), (key249, -1), (key569, 1), (key386, 1), (key268, 1), (key252, 1), (key569, -1), (key389, -1)]

theorem rawRowCheck5954 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form1 = rawRow5954 := by decide +kernel

def row5954 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5954 : row5954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5954 := by decide +kernel

theorem rowEval5954 (x : Key → ℝ) : Integer.Sparse.eval row5954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5954, Integer.Sparse.eval_collectBalanced, rawRowCheck5954]

def rawRow5955 : Integer.Sparse Key := [(key317, -1), (key330, -1), (key320, 2), (key317, -1), (key330, -1), (key303, 2), (key342, 2), (key306, -1), (key336, -1), (key320, 2), (key306, -1), (key336, -1), (key407, 1), (key420, 1), (key410, -2), (key407, 1), (key420, 1), (key237, -2), (key585, -2), (key240, 1), (key579, 1), (key410, -2), (key240, 1), (key579, 1), (key386, -1), (key477, -1), (key389, 1), (key468, 1), (key249, 1), (key603, 1), (key252, -1), (key594, -1), (key386, -1), (key477, -1), (key249, 1), (key603, 1), (key389, 1), (key468, 1), (key252, -1), (key594, -1)]

theorem rawRowCheck5955 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form1 = rawRow5955 := by decide +kernel

def row5955 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key252, -2), (key303, 2), (key306, -2), (key317, -2), (key320, 4), (key330, -2), (key336, -2), (key342, 2), (key386, -2), (key389, 2), (key407, 2), (key410, -4), (key420, 2), (key468, 2), (key477, -2), (key579, 2), (key585, -2), (key594, -2), (key603, 2)]

theorem rowCheck5955 : row5955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5955 := by decide +kernel

theorem rowEval5955 (x : Key → ℝ) : Integer.Sparse.eval row5955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5955, Integer.Sparse.eval_collectBalanced, rawRowCheck5955]

def rawRow5956 : Integer.Sparse Key := [(key330, -1), (key317, -1), (key320, 2), (key330, -1), (key317, -1), (key342, 2), (key303, 2), (key336, -1), (key306, -1), (key320, 2), (key336, -1), (key306, -1), (key420, 1), (key407, 1), (key410, -2), (key420, 1), (key407, 1), (key585, -2), (key237, -2), (key579, 1), (key240, 1), (key410, -2), (key579, 1), (key240, 1), (key477, -1), (key386, -1), (key468, 1), (key389, 1), (key603, 1), (key249, 1), (key594, -1), (key252, -1), (key477, -1), (key386, -1), (key603, 1), (key249, 1), (key468, 1), (key389, 1), (key594, -1), (key252, -1)]

theorem rawRowCheck5956 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form1 = rawRow5956 := by decide +kernel

def row5956 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key252, -2), (key303, 2), (key306, -2), (key317, -2), (key320, 4), (key330, -2), (key336, -2), (key342, 2), (key386, -2), (key389, 2), (key407, 2), (key410, -4), (key420, 2), (key468, 2), (key477, -2), (key579, 2), (key585, -2), (key594, -2), (key603, 2)]

theorem rowCheck5956 : row5956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5956 := by decide +kernel

theorem rowEval5956 (x : Key → ℝ) : Integer.Sparse.eval row5956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5956, Integer.Sparse.eval_collectBalanced, rawRowCheck5956]

def rawRow5957 : Integer.Sparse Key := [(key320, -1), (key330, -1), (key317, 2), (key336, -1), (key342, -1), (key306, 2), (key330, 2), (key303, -1), (key317, -1), (key336, 2), (key306, -1), (key320, -1), (key410, 1), (key420, 1), (key407, -2), (key579, 1), (key585, 1), (key240, -2), (key420, -2), (key237, 1), (key407, 1), (key579, -2), (key240, 1), (key410, 1), (key389, -1), (key452, -1), (key386, 1), (key436, 1), (key252, 1), (key452, 1), (key249, -1), (key436, -1), (key569, -1), (key603, -1), (key268, 1), (key477, 1), (key569, 1), (key594, 1), (key268, -1), (key468, -1)]

theorem rawRowCheck5957 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form1 = rawRow5957 := by decide +kernel

def row5957 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5957 : row5957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5957 := by decide +kernel

theorem rowEval5957 (x : Key → ℝ) : Integer.Sparse.eval row5957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5957, Integer.Sparse.eval_collectBalanced, rawRowCheck5957]

def rawRow5958 : Integer.Sparse Key := [(key330, -1), (key320, -1), (key317, 2), (key342, -1), (key336, -1), (key330, 2), (key306, 2), (key317, -1), (key303, -1), (key336, 2), (key320, -1), (key306, -1), (key420, 1), (key410, 1), (key407, -2), (key585, 1), (key579, 1), (key420, -2), (key240, -2), (key407, 1), (key237, 1), (key579, -2), (key410, 1), (key240, 1), (key452, -1), (key389, -1), (key436, 1), (key386, 1), (key452, 1), (key252, 1), (key436, -1), (key249, -1), (key603, -1), (key569, -1), (key477, 1), (key268, 1), (key594, 1), (key569, 1), (key468, -1), (key268, -1)]

theorem rawRowCheck5958 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form1 = rawRow5958 := by decide +kernel

def row5958 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5958 : row5958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5958 := by decide +kernel

theorem rowEval5958 (x : Key → ℝ) : Integer.Sparse.eval row5958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5958, Integer.Sparse.eval_collectBalanced, rawRowCheck5958]

def rawRow5959 : Integer.Sparse Key := [(key336, -1), (key336, -1), (key342, 2), (key306, -1), (key306, -1), (key320, 2), (key320, 2), (key330, -1), (key330, -1), (key303, 2), (key317, -1), (key317, -1), (key579, 1), (key579, 1), (key585, -2), (key240, 1), (key240, 1), (key410, -2), (key410, -2), (key420, 1), (key420, 1), (key237, -2), (key407, 1), (key407, 1), (key594, -1), (key594, -1), (key603, 1), (key603, 1), (key468, 1), (key468, 1), (key477, -1), (key477, -1), (key252, -1), (key252, -1), (key389, 1), (key389, 1), (key249, 1), (key249, 1), (key386, -1), (key386, -1)]

theorem rawRowCheck5959 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form1 = rawRow5959 := by decide +kernel

def row5959 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key252, -2), (key303, 2), (key306, -2), (key317, -2), (key320, 4), (key330, -2), (key336, -2), (key342, 2), (key386, -2), (key389, 2), (key407, 2), (key410, -4), (key420, 2), (key468, 2), (key477, -2), (key579, 2), (key585, -2), (key594, -2), (key603, 2)]

theorem rowCheck5959 : row5959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5959 := by decide +kernel

theorem rowEval5959 (x : Key → ℝ) : Integer.Sparse.eval row5959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5959, Integer.Sparse.eval_collectBalanced, rawRowCheck5959]

def rawRow5960 : Integer.Sparse Key := [(key336, -1), (key342, -1), (key336, 2), (key320, -1), (key330, -1), (key306, 2), (key330, 2), (key306, -1), (key320, -1), (key317, 2), (key303, -1), (key317, -1), (key579, 1), (key585, 1), (key579, -2), (key410, 1), (key420, 1), (key240, -2), (key420, -2), (key240, 1), (key410, 1), (key407, -2), (key237, 1), (key407, 1), (key569, -1), (key603, -1), (key569, 1), (key594, 1), (key268, 1), (key477, 1), (key268, -1), (key468, -1), (key389, -1), (key452, -1), (key252, 1), (key452, 1), (key386, 1), (key436, 1), (key249, -1), (key436, -1)]

theorem rawRowCheck5960 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form1 = rawRow5960 := by decide +kernel

def row5960 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5960 : row5960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5960 := by decide +kernel

theorem rowEval5960 (x : Key → ℝ) : Integer.Sparse.eval row5960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5960, Integer.Sparse.eval_collectBalanced, rawRowCheck5960]

def rawRow5961 : Integer.Sparse Key := [(key342, -1), (key336, -1), (key336, 2), (key330, -1), (key320, -1), (key330, 2), (key306, 2), (key320, -1), (key306, -1), (key317, 2), (key317, -1), (key303, -1), (key585, 1), (key579, 1), (key579, -2), (key420, 1), (key410, 1), (key420, -2), (key240, -2), (key410, 1), (key240, 1), (key407, -2), (key407, 1), (key237, 1), (key603, -1), (key569, -1), (key594, 1), (key569, 1), (key477, 1), (key268, 1), (key468, -1), (key268, -1), (key452, -1), (key389, -1), (key452, 1), (key252, 1), (key436, 1), (key386, 1), (key436, -1), (key249, -1)]

theorem rawRowCheck5961 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form1 = rawRow5961 := by decide +kernel

def row5961 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5961 : row5961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5961 := by decide +kernel

theorem rowEval5961 (x : Key → ℝ) : Integer.Sparse.eval row5961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5961, Integer.Sparse.eval_collectBalanced, rawRowCheck5961]

def rawRow5962 : Integer.Sparse Key := [(key386, -1), (key399, -1), (key389, 2), (key436, -1), (key444, -1), (key407, 2), (key471, 2), (key410, -1), (key468, -1), (key452, 2), (key420, -1), (key477, -1), (key249, 1), (key262, 1), (key252, -2), (key436, 1), (key444, 1), (key317, -2), (key597, -2), (key320, 1), (key594, 1), (key452, -2), (key330, 1), (key603, 1), (key237, -1), (key273, -1), (key240, 1), (key268, 1), (key303, 1), (key574, 1), (key306, -1), (key569, -1), (key407, -1), (key471, -1), (key317, 1), (key597, 1), (key420, 1), (key477, 1), (key330, -1), (key603, -1)]

theorem rawRowCheck5962 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form1 = rawRow5962 := by decide +kernel

def row5962 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5962 : row5962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5962 := by decide +kernel

theorem rowEval5962 (x : Key → ℝ) : Integer.Sparse.eval row5962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5962, Integer.Sparse.eval_collectBalanced, rawRowCheck5962]

def rawRow5963 : Integer.Sparse Key := [(key399, -1), (key386, -1), (key389, 2), (key444, -1), (key436, -1), (key471, 2), (key407, 2), (key468, -1), (key410, -1), (key452, 2), (key477, -1), (key420, -1), (key262, 1), (key249, 1), (key252, -2), (key444, 1), (key436, 1), (key597, -2), (key317, -2), (key594, 1), (key320, 1), (key452, -2), (key603, 1), (key330, 1), (key273, -1), (key237, -1), (key268, 1), (key240, 1), (key574, 1), (key303, 1), (key569, -1), (key306, -1), (key471, -1), (key407, -1), (key597, 1), (key317, 1), (key477, 1), (key420, 1), (key603, -1), (key330, -1)]

theorem rawRowCheck5963 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form1 = rawRow5963 := by decide +kernel

def row5963 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5963 : row5963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5963 := by decide +kernel

theorem rowEval5963 (x : Key → ℝ) : Integer.Sparse.eval row5963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5963, Integer.Sparse.eval_collectBalanced, rawRowCheck5963]

def rawRow5964 : Integer.Sparse Key := [(key389, -1), (key399, -1), (key386, 2), (key468, -1), (key471, -1), (key410, 2), (key444, 2), (key407, -1), (key436, -1), (key477, 2), (key420, -1), (key452, -1), (key252, 1), (key262, 1), (key249, -2), (key594, 1), (key597, 1), (key320, -2), (key444, -2), (key317, 1), (key436, 1), (key603, -2), (key330, 1), (key452, 1), (key240, -1), (key262, -1), (key237, 1), (key249, 1), (key306, 1), (key399, 1), (key303, -1), (key386, -1), (key579, -1), (key597, -1), (key336, 1), (key471, 1), (key585, 1), (key603, 1), (key342, -1), (key477, -1)]

theorem rawRowCheck5964 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form1 = rawRow5964 := by decide +kernel

def row5964 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5964 : row5964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5964 := by decide +kernel

theorem rowEval5964 (x : Key → ℝ) : Integer.Sparse.eval row5964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5964, Integer.Sparse.eval_collectBalanced, rawRowCheck5964]

def rawRow5965 : Integer.Sparse Key := [(key399, -1), (key389, -1), (key386, 2), (key471, -1), (key468, -1), (key444, 2), (key410, 2), (key436, -1), (key407, -1), (key477, 2), (key452, -1), (key420, -1), (key262, 1), (key252, 1), (key249, -2), (key597, 1), (key594, 1), (key444, -2), (key320, -2), (key436, 1), (key317, 1), (key603, -2), (key452, 1), (key330, 1), (key262, -1), (key240, -1), (key249, 1), (key237, 1), (key399, 1), (key306, 1), (key386, -1), (key303, -1), (key597, -1), (key579, -1), (key471, 1), (key336, 1), (key603, 1), (key585, 1), (key477, -1), (key342, -1)]

theorem rawRowCheck5965 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form1 = rawRow5965 := by decide +kernel

def row5965 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5965 : row5965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5965 := by decide +kernel

theorem rowEval5965 (x : Key → ℝ) : Integer.Sparse.eval row5965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5965, Integer.Sparse.eval_collectBalanced, rawRowCheck5965]

def rawRow5966 : Integer.Sparse Key := [(key407, -1), (key420, -1), (key410, 2), (key436, -1), (key452, -1), (key386, 2), (key477, 2), (key389, -1), (key468, -1), (key444, 2), (key399, -1), (key471, -1), (key317, 1), (key330, 1), (key320, -2), (key436, 1), (key452, 1), (key249, -2), (key603, -2), (key252, 1), (key594, 1), (key444, -2), (key262, 1), (key597, 1), (key303, -1), (key342, -1), (key306, 1), (key336, 1), (key237, 1), (key585, 1), (key240, -1), (key579, -1), (key386, -1), (key477, -1), (key249, 1), (key603, 1), (key399, 1), (key471, 1), (key262, -1), (key597, -1)]

theorem rawRowCheck5966 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form1 = rawRow5966 := by decide +kernel

def row5966 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5966 : row5966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5966 := by decide +kernel

theorem rowEval5966 (x : Key → ℝ) : Integer.Sparse.eval row5966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5966, Integer.Sparse.eval_collectBalanced, rawRowCheck5966]

def rawRow5967 : Integer.Sparse Key := [(key420, -1), (key407, -1), (key410, 2), (key452, -1), (key436, -1), (key477, 2), (key386, 2), (key468, -1), (key389, -1), (key444, 2), (key471, -1), (key399, -1), (key330, 1), (key317, 1), (key320, -2), (key452, 1), (key436, 1), (key603, -2), (key249, -2), (key594, 1), (key252, 1), (key444, -2), (key597, 1), (key262, 1), (key342, -1), (key303, -1), (key336, 1), (key306, 1), (key585, 1), (key237, 1), (key579, -1), (key240, -1), (key477, -1), (key386, -1), (key603, 1), (key249, 1), (key471, 1), (key399, 1), (key597, -1), (key262, -1)]

theorem rawRowCheck5967 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form1 = rawRow5967 := by decide +kernel

def row5967 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5967 : row5967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5967 := by decide +kernel

theorem rowEval5967 (x : Key → ℝ) : Integer.Sparse.eval row5967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5967, Integer.Sparse.eval_collectBalanced, rawRowCheck5967]

def rawRow5968 : Integer.Sparse Key := [(key410, -1), (key420, -1), (key407, 2), (key468, -1), (key477, -1), (key389, 2), (key452, 2), (key386, -1), (key436, -1), (key471, 2), (key399, -1), (key444, -1), (key320, 1), (key330, 1), (key317, -2), (key594, 1), (key603, 1), (key252, -2), (key452, -2), (key249, 1), (key436, 1), (key597, -2), (key262, 1), (key444, 1), (key306, -1), (key330, -1), (key303, 1), (key317, 1), (key240, 1), (key420, 1), (key237, -1), (key407, -1), (key569, -1), (key603, -1), (key268, 1), (key477, 1), (key574, 1), (key597, 1), (key273, -1), (key471, -1)]

theorem rawRowCheck5968 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form1 = rawRow5968 := by decide +kernel

def row5968 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5968 : row5968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5968 := by decide +kernel

theorem rowEval5968 (x : Key → ℝ) : Integer.Sparse.eval row5968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5968, Integer.Sparse.eval_collectBalanced, rawRowCheck5968]

def rawRow5969 : Integer.Sparse Key := [(key420, -1), (key410, -1), (key407, 2), (key477, -1), (key468, -1), (key452, 2), (key389, 2), (key436, -1), (key386, -1), (key471, 2), (key444, -1), (key399, -1), (key330, 1), (key320, 1), (key317, -2), (key603, 1), (key594, 1), (key452, -2), (key252, -2), (key436, 1), (key249, 1), (key597, -2), (key444, 1), (key262, 1), (key330, -1), (key306, -1), (key317, 1), (key303, 1), (key420, 1), (key240, 1), (key407, -1), (key237, -1), (key603, -1), (key569, -1), (key477, 1), (key268, 1), (key597, 1), (key574, 1), (key471, -1), (key273, -1)]

theorem rawRowCheck5969 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form1 = rawRow5969 := by decide +kernel

def row5969 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5969 : row5969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5969 := by decide +kernel

theorem rowEval5969 (x : Key → ℝ) : Integer.Sparse.eval row5969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5969, Integer.Sparse.eval_collectBalanced, rawRowCheck5969]

def rawRow5970 : Integer.Sparse Key := [(key436, -1), (key444, -1), (key452, 2), (key386, -1), (key399, -1), (key407, 2), (key471, 2), (key420, -1), (key477, -1), (key389, 2), (key410, -1), (key468, -1), (key436, 1), (key444, 1), (key452, -2), (key249, 1), (key262, 1), (key317, -2), (key597, -2), (key330, 1), (key603, 1), (key252, -2), (key320, 1), (key594, 1), (key407, -1), (key471, -1), (key420, 1), (key477, 1), (key317, 1), (key597, 1), (key330, -1), (key603, -1), (key237, -1), (key273, -1), (key303, 1), (key574, 1), (key240, 1), (key268, 1), (key306, -1), (key569, -1)]

theorem rawRowCheck5970 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form1 = rawRow5970 := by decide +kernel

def row5970 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5970 : row5970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5970 := by decide +kernel

theorem rowEval5970 (x : Key → ℝ) : Integer.Sparse.eval row5970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5970, Integer.Sparse.eval_collectBalanced, rawRowCheck5970]

def rawRow5971 : Integer.Sparse Key := [(key444, -1), (key436, -1), (key452, 2), (key399, -1), (key386, -1), (key471, 2), (key407, 2), (key477, -1), (key420, -1), (key389, 2), (key468, -1), (key410, -1), (key444, 1), (key436, 1), (key452, -2), (key262, 1), (key249, 1), (key597, -2), (key317, -2), (key603, 1), (key330, 1), (key252, -2), (key594, 1), (key320, 1), (key471, -1), (key407, -1), (key477, 1), (key420, 1), (key597, 1), (key317, 1), (key603, -1), (key330, -1), (key273, -1), (key237, -1), (key574, 1), (key303, 1), (key268, 1), (key240, 1), (key569, -1), (key306, -1)]

theorem rawRowCheck5971 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form1 = rawRow5971 := by decide +kernel

def row5971 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5971 : row5971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5971 := by decide +kernel

theorem rowEval5971 (x : Key → ℝ) : Integer.Sparse.eval row5971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5971, Integer.Sparse.eval_collectBalanced, rawRowCheck5971]

def rawRow5972 : Integer.Sparse Key := [(key436, -1), (key452, -1), (key444, 2), (key407, -1), (key420, -1), (key386, 2), (key477, 2), (key399, -1), (key471, -1), (key410, 2), (key389, -1), (key468, -1), (key436, 1), (key452, 1), (key444, -2), (key317, 1), (key330, 1), (key249, -2), (key603, -2), (key262, 1), (key597, 1), (key320, -2), (key252, 1), (key594, 1), (key386, -1), (key477, -1), (key399, 1), (key471, 1), (key249, 1), (key603, 1), (key262, -1), (key597, -1), (key303, -1), (key342, -1), (key237, 1), (key585, 1), (key306, 1), (key336, 1), (key240, -1), (key579, -1)]

theorem rawRowCheck5972 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form1 = rawRow5972 := by decide +kernel

def row5972 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5972 : row5972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5972 := by decide +kernel

theorem rowEval5972 (x : Key → ℝ) : Integer.Sparse.eval row5972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5972, Integer.Sparse.eval_collectBalanced, rawRowCheck5972]

def rawRow5973 : Integer.Sparse Key := [(key452, -1), (key436, -1), (key444, 2), (key420, -1), (key407, -1), (key477, 2), (key386, 2), (key471, -1), (key399, -1), (key410, 2), (key468, -1), (key389, -1), (key452, 1), (key436, 1), (key444, -2), (key330, 1), (key317, 1), (key603, -2), (key249, -2), (key597, 1), (key262, 1), (key320, -2), (key594, 1), (key252, 1), (key477, -1), (key386, -1), (key471, 1), (key399, 1), (key603, 1), (key249, 1), (key597, -1), (key262, -1), (key342, -1), (key303, -1), (key585, 1), (key237, 1), (key336, 1), (key306, 1), (key579, -1), (key240, -1)]

theorem rawRowCheck5973 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form1 = rawRow5973 := by decide +kernel

def row5973 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5973 : row5973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5973 := by decide +kernel

theorem rowEval5973 (x : Key → ℝ) : Integer.Sparse.eval row5973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5973, Integer.Sparse.eval_collectBalanced, rawRowCheck5973]

def rawRow5974 : Integer.Sparse Key := [(key468, -1), (key471, -1), (key477, 2), (key389, -1), (key399, -1), (key410, 2), (key444, 2), (key420, -1), (key452, -1), (key386, 2), (key407, -1), (key436, -1), (key594, 1), (key597, 1), (key603, -2), (key252, 1), (key262, 1), (key320, -2), (key444, -2), (key330, 1), (key452, 1), (key249, -2), (key317, 1), (key436, 1), (key579, -1), (key597, -1), (key585, 1), (key603, 1), (key336, 1), (key471, 1), (key342, -1), (key477, -1), (key240, -1), (key262, -1), (key306, 1), (key399, 1), (key237, 1), (key249, 1), (key303, -1), (key386, -1)]

theorem rawRowCheck5974 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form1 = rawRow5974 := by decide +kernel

def row5974 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5974 : row5974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5974 := by decide +kernel

theorem rowEval5974 (x : Key → ℝ) : Integer.Sparse.eval row5974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5974, Integer.Sparse.eval_collectBalanced, rawRowCheck5974]

def rawRow5975 : Integer.Sparse Key := [(key471, -1), (key468, -1), (key477, 2), (key399, -1), (key389, -1), (key444, 2), (key410, 2), (key452, -1), (key420, -1), (key386, 2), (key436, -1), (key407, -1), (key597, 1), (key594, 1), (key603, -2), (key262, 1), (key252, 1), (key444, -2), (key320, -2), (key452, 1), (key330, 1), (key249, -2), (key436, 1), (key317, 1), (key597, -1), (key579, -1), (key603, 1), (key585, 1), (key471, 1), (key336, 1), (key477, -1), (key342, -1), (key262, -1), (key240, -1), (key399, 1), (key306, 1), (key249, 1), (key237, 1), (key386, -1), (key303, -1)]

theorem rawRowCheck5975 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form1 = rawRow5975 := by decide +kernel

def row5975 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

theorem rowCheck5975 : row5975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5975 := by decide +kernel

theorem rowEval5975 (x : Key → ℝ) : Integer.Sparse.eval row5975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5975, Integer.Sparse.eval_collectBalanced, rawRowCheck5975]

def rawRow5976 : Integer.Sparse Key := [(key468, -1), (key477, -1), (key471, 2), (key410, -1), (key420, -1), (key389, 2), (key452, 2), (key399, -1), (key444, -1), (key407, 2), (key386, -1), (key436, -1), (key594, 1), (key603, 1), (key597, -2), (key320, 1), (key330, 1), (key252, -2), (key452, -2), (key262, 1), (key444, 1), (key317, -2), (key249, 1), (key436, 1), (key569, -1), (key603, -1), (key574, 1), (key597, 1), (key268, 1), (key477, 1), (key273, -1), (key471, -1), (key306, -1), (key330, -1), (key240, 1), (key420, 1), (key303, 1), (key317, 1), (key237, -1), (key407, -1)]

theorem rawRowCheck5976 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form1 = rawRow5976 := by decide +kernel

def row5976 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5976 : row5976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5976 := by decide +kernel

theorem rowEval5976 (x : Key → ℝ) : Integer.Sparse.eval row5976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5976, Integer.Sparse.eval_collectBalanced, rawRowCheck5976]

def rawRow5977 : Integer.Sparse Key := [(key477, -1), (key468, -1), (key471, 2), (key420, -1), (key410, -1), (key452, 2), (key389, 2), (key444, -1), (key399, -1), (key407, 2), (key436, -1), (key386, -1), (key603, 1), (key594, 1), (key597, -2), (key330, 1), (key320, 1), (key452, -2), (key252, -2), (key444, 1), (key262, 1), (key317, -2), (key436, 1), (key249, 1), (key603, -1), (key569, -1), (key597, 1), (key574, 1), (key477, 1), (key268, 1), (key471, -1), (key273, -1), (key330, -1), (key306, -1), (key420, 1), (key240, 1), (key317, 1), (key303, 1), (key407, -1), (key237, -1)]

theorem rawRowCheck5977 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form1 = rawRow5977 := by decide +kernel

def row5977 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

theorem rowCheck5977 : row5977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5977 := by decide +kernel

theorem rowEval5977 (x : Key → ℝ) : Integer.Sparse.eval row5977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5977, Integer.Sparse.eval_collectBalanced, rawRowCheck5977]

def rawRow5978 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1295, 2), (key1311, -1), (key1315, -1), (key1311, 2), (key1324, 2), (key1315, -1), (key1324, -1), (key1336, 2), (key1336, -1), (key1343, -1), (key1386, 1), (key1390, 1), (key1390, -2), (key1419, 1), (key1423, 1), (key1419, -2), (key1442, -2), (key1423, 1), (key1442, 1), (key1454, -2), (key1454, 1), (key1464, 1), (key1541, -1), (key1554, -1), (key1545, 1), (key1554, 1), (key1568, 1), (key1591, 1), (key1572, -1), (key1591, -1), (key1617, -1), (key1622, -1), (key1617, 1), (key1631, 1), (key1654, 1), (key1657, 1), (key1654, -1), (key1665, -1)]

theorem rawRowCheck5978 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form2 = rawRow5978 := by decide +kernel

def row5978 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck5978 : row5978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5978 := by decide +kernel

theorem rowEval5978 (x : Key → ℝ) : Integer.Sparse.eval row5978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5978, Integer.Sparse.eval_collectBalanced, rawRowCheck5978]

def rawRow5979 : Integer.Sparse Key := [(key1295, -1), (key1291, -1), (key1295, 2), (key1315, -1), (key1311, -1), (key1324, 2), (key1311, 2), (key1324, -1), (key1315, -1), (key1336, 2), (key1343, -1), (key1336, -1), (key1390, 1), (key1386, 1), (key1390, -2), (key1423, 1), (key1419, 1), (key1442, -2), (key1419, -2), (key1442, 1), (key1423, 1), (key1454, -2), (key1464, 1), (key1454, 1), (key1554, -1), (key1541, -1), (key1554, 1), (key1545, 1), (key1591, 1), (key1568, 1), (key1591, -1), (key1572, -1), (key1622, -1), (key1617, -1), (key1631, 1), (key1617, 1), (key1657, 1), (key1654, 1), (key1665, -1), (key1654, -1)]

theorem rawRowCheck5979 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form2 = rawRow5979 := by decide +kernel

def row5979 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck5979 : row5979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5979 := by decide +kernel

theorem rowEval5979 (x : Key → ℝ) : Integer.Sparse.eval row5979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5979, Integer.Sparse.eval_collectBalanced, rawRowCheck5979]

def rawRow5980 : Integer.Sparse Key := [(key1295, -1), (key1295, -1), (key1291, 2), (key1324, -1), (key1324, -1), (key1315, 2), (key1315, 2), (key1311, -1), (key1311, -1), (key1343, 2), (key1336, -1), (key1336, -1), (key1390, 1), (key1390, 1), (key1386, -2), (key1442, 1), (key1442, 1), (key1423, -2), (key1423, -2), (key1419, 1), (key1419, 1), (key1464, -2), (key1454, 1), (key1454, 1), (key1545, -1), (key1545, -1), (key1541, 1), (key1541, 1), (key1572, 1), (key1572, 1), (key1568, -1), (key1568, -1), (key1631, -1), (key1631, -1), (key1622, 1), (key1622, 1), (key1665, 1), (key1665, 1), (key1657, -1), (key1657, -1)]

theorem rawRowCheck5980 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form2 = rawRow5980 := by decide +kernel

def row5980 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1315, 4), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, -2), (key1390, 2), (key1419, 2), (key1423, -4), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, 2), (key1545, -2), (key1568, -2), (key1572, 2), (key1622, 2), (key1631, -2), (key1657, -2), (key1665, 2)]

theorem rowCheck5980 : row5980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5980 := by decide +kernel

theorem rowEval5980 (x : Key → ℝ) : Integer.Sparse.eval row5980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5980, Integer.Sparse.eval_collectBalanced, rawRowCheck5980]

def rawRow5981 : Integer.Sparse Key := [(key1311, -1), (key1315, -1), (key1336, 2), (key1291, -1), (key1295, -1), (key1311, 2), (key1324, 2), (key1336, -1), (key1343, -1), (key1295, 2), (key1315, -1), (key1324, -1), (key1419, 1), (key1423, 1), (key1454, -2), (key1386, 1), (key1390, 1), (key1419, -2), (key1442, -2), (key1454, 1), (key1464, 1), (key1390, -2), (key1423, 1), (key1442, 1), (key1617, -1), (key1622, -1), (key1654, 1), (key1657, 1), (key1617, 1), (key1631, 1), (key1654, -1), (key1665, -1), (key1541, -1), (key1554, -1), (key1568, 1), (key1591, 1), (key1545, 1), (key1554, 1), (key1572, -1), (key1591, -1)]

theorem rawRowCheck5981 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form2 = rawRow5981 := by decide +kernel

def row5981 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck5981 : row5981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5981 := by decide +kernel

theorem rowEval5981 (x : Key → ℝ) : Integer.Sparse.eval row5981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5981, Integer.Sparse.eval_collectBalanced, rawRowCheck5981]

def rawRow5982 : Integer.Sparse Key := [(key1315, -1), (key1311, -1), (key1336, 2), (key1295, -1), (key1291, -1), (key1324, 2), (key1311, 2), (key1343, -1), (key1336, -1), (key1295, 2), (key1324, -1), (key1315, -1), (key1423, 1), (key1419, 1), (key1454, -2), (key1390, 1), (key1386, 1), (key1442, -2), (key1419, -2), (key1464, 1), (key1454, 1), (key1390, -2), (key1442, 1), (key1423, 1), (key1622, -1), (key1617, -1), (key1657, 1), (key1654, 1), (key1631, 1), (key1617, 1), (key1665, -1), (key1654, -1), (key1554, -1), (key1541, -1), (key1591, 1), (key1568, 1), (key1554, 1), (key1545, 1), (key1591, -1), (key1572, -1)]

theorem rawRowCheck5982 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form2 = rawRow5982 := by decide +kernel

def row5982 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck5982 : row5982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5982 := by decide +kernel

theorem rowEval5982 (x : Key → ℝ) : Integer.Sparse.eval row5982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5982, Integer.Sparse.eval_collectBalanced, rawRowCheck5982]

def rawRow5983 : Integer.Sparse Key := [(key1311, -1), (key1336, -1), (key1315, 2), (key1311, -1), (key1336, -1), (key1291, 2), (key1343, 2), (key1295, -1), (key1324, -1), (key1315, 2), (key1295, -1), (key1324, -1), (key1419, 1), (key1454, 1), (key1423, -2), (key1419, 1), (key1454, 1), (key1386, -2), (key1464, -2), (key1390, 1), (key1442, 1), (key1423, -2), (key1390, 1), (key1442, 1), (key1568, -1), (key1657, -1), (key1572, 1), (key1622, 1), (key1541, 1), (key1665, 1), (key1545, -1), (key1631, -1), (key1568, -1), (key1657, -1), (key1541, 1), (key1665, 1), (key1572, 1), (key1622, 1), (key1545, -1), (key1631, -1)]

theorem rawRowCheck5983 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form2 = rawRow5983 := by decide +kernel

def row5983 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1315, 4), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, -2), (key1390, 2), (key1419, 2), (key1423, -4), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, 2), (key1545, -2), (key1568, -2), (key1572, 2), (key1622, 2), (key1631, -2), (key1657, -2), (key1665, 2)]

theorem rowCheck5983 : row5983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5983 := by decide +kernel

theorem rowEval5983 (x : Key → ℝ) : Integer.Sparse.eval row5983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5983, Integer.Sparse.eval_collectBalanced, rawRowCheck5983]

def rawRow5984 : Integer.Sparse Key := [(key1336, -1), (key1311, -1), (key1315, 2), (key1336, -1), (key1311, -1), (key1343, 2), (key1291, 2), (key1324, -1), (key1295, -1), (key1315, 2), (key1324, -1), (key1295, -1), (key1454, 1), (key1419, 1), (key1423, -2), (key1454, 1), (key1419, 1), (key1464, -2), (key1386, -2), (key1442, 1), (key1390, 1), (key1423, -2), (key1442, 1), (key1390, 1), (key1657, -1), (key1568, -1), (key1622, 1), (key1572, 1), (key1665, 1), (key1541, 1), (key1631, -1), (key1545, -1), (key1657, -1), (key1568, -1), (key1665, 1), (key1541, 1), (key1622, 1), (key1572, 1), (key1631, -1), (key1545, -1)]

theorem rawRowCheck5984 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form2 = rawRow5984 := by decide +kernel

def row5984 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1315, 4), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, -2), (key1390, 2), (key1419, 2), (key1423, -4), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, 2), (key1545, -2), (key1568, -2), (key1572, 2), (key1622, 2), (key1631, -2), (key1657, -2), (key1665, 2)]

theorem rowCheck5984 : row5984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5984 := by decide +kernel

theorem rowEval5984 (x : Key → ℝ) : Integer.Sparse.eval row5984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5984, Integer.Sparse.eval_collectBalanced, rawRowCheck5984]

def rawRow5985 : Integer.Sparse Key := [(key1315, -1), (key1336, -1), (key1311, 2), (key1324, -1), (key1343, -1), (key1295, 2), (key1336, 2), (key1291, -1), (key1311, -1), (key1324, 2), (key1295, -1), (key1315, -1), (key1423, 1), (key1454, 1), (key1419, -2), (key1442, 1), (key1464, 1), (key1390, -2), (key1454, -2), (key1386, 1), (key1419, 1), (key1442, -2), (key1390, 1), (key1423, 1), (key1572, -1), (key1654, -1), (key1568, 1), (key1617, 1), (key1545, 1), (key1654, 1), (key1541, -1), (key1617, -1), (key1591, -1), (key1665, -1), (key1554, 1), (key1657, 1), (key1591, 1), (key1631, 1), (key1554, -1), (key1622, -1)]

theorem rawRowCheck5985 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form2 = rawRow5985 := by decide +kernel

def row5985 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck5985 : row5985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5985 := by decide +kernel

theorem rowEval5985 (x : Key → ℝ) : Integer.Sparse.eval row5985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5985, Integer.Sparse.eval_collectBalanced, rawRowCheck5985]

def rawRow5986 : Integer.Sparse Key := [(key1336, -1), (key1315, -1), (key1311, 2), (key1343, -1), (key1324, -1), (key1336, 2), (key1295, 2), (key1311, -1), (key1291, -1), (key1324, 2), (key1315, -1), (key1295, -1), (key1454, 1), (key1423, 1), (key1419, -2), (key1464, 1), (key1442, 1), (key1454, -2), (key1390, -2), (key1419, 1), (key1386, 1), (key1442, -2), (key1423, 1), (key1390, 1), (key1654, -1), (key1572, -1), (key1617, 1), (key1568, 1), (key1654, 1), (key1545, 1), (key1617, -1), (key1541, -1), (key1665, -1), (key1591, -1), (key1657, 1), (key1554, 1), (key1631, 1), (key1591, 1), (key1622, -1), (key1554, -1)]

theorem rawRowCheck5986 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form2 = rawRow5986 := by decide +kernel

def row5986 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck5986 : row5986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5986 := by decide +kernel

theorem rowEval5986 (x : Key → ℝ) : Integer.Sparse.eval row5986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5986, Integer.Sparse.eval_collectBalanced, rawRowCheck5986]

def rawRow5987 : Integer.Sparse Key := [(key1324, -1), (key1324, -1), (key1343, 2), (key1295, -1), (key1295, -1), (key1315, 2), (key1315, 2), (key1336, -1), (key1336, -1), (key1291, 2), (key1311, -1), (key1311, -1), (key1442, 1), (key1442, 1), (key1464, -2), (key1390, 1), (key1390, 1), (key1423, -2), (key1423, -2), (key1454, 1), (key1454, 1), (key1386, -2), (key1419, 1), (key1419, 1), (key1631, -1), (key1631, -1), (key1665, 1), (key1665, 1), (key1622, 1), (key1622, 1), (key1657, -1), (key1657, -1), (key1545, -1), (key1545, -1), (key1572, 1), (key1572, 1), (key1541, 1), (key1541, 1), (key1568, -1), (key1568, -1)]

theorem rawRowCheck5987 : GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form2 = rawRow5987 := by decide +kernel

def row5987 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1315, 4), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, -2), (key1390, 2), (key1419, 2), (key1423, -4), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, 2), (key1545, -2), (key1568, -2), (key1572, 2), (key1622, 2), (key1631, -2), (key1657, -2), (key1665, 2)]

theorem rowCheck5987 : row5987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5987 := by decide +kernel

theorem rowEval5987 (x : Key → ℝ) : Integer.Sparse.eval row5987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5987, Integer.Sparse.eval_collectBalanced, rawRowCheck5987]

def rawRow5988 : Integer.Sparse Key := [(key1324, -1), (key1343, -1), (key1324, 2), (key1315, -1), (key1336, -1), (key1295, 2), (key1336, 2), (key1295, -1), (key1315, -1), (key1311, 2), (key1291, -1), (key1311, -1), (key1442, 1), (key1464, 1), (key1442, -2), (key1423, 1), (key1454, 1), (key1390, -2), (key1454, -2), (key1390, 1), (key1423, 1), (key1419, -2), (key1386, 1), (key1419, 1), (key1591, -1), (key1665, -1), (key1591, 1), (key1631, 1), (key1554, 1), (key1657, 1), (key1554, -1), (key1622, -1), (key1572, -1), (key1654, -1), (key1545, 1), (key1654, 1), (key1568, 1), (key1617, 1), (key1541, -1), (key1617, -1)]

theorem rawRowCheck5988 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form2 = rawRow5988 := by decide +kernel

def row5988 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck5988 : row5988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5988 := by decide +kernel

theorem rowEval5988 (x : Key → ℝ) : Integer.Sparse.eval row5988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5988, Integer.Sparse.eval_collectBalanced, rawRowCheck5988]

def rawRow5989 : Integer.Sparse Key := [(key1343, -1), (key1324, -1), (key1324, 2), (key1336, -1), (key1315, -1), (key1336, 2), (key1295, 2), (key1315, -1), (key1295, -1), (key1311, 2), (key1311, -1), (key1291, -1), (key1464, 1), (key1442, 1), (key1442, -2), (key1454, 1), (key1423, 1), (key1454, -2), (key1390, -2), (key1423, 1), (key1390, 1), (key1419, -2), (key1419, 1), (key1386, 1), (key1665, -1), (key1591, -1), (key1631, 1), (key1591, 1), (key1657, 1), (key1554, 1), (key1622, -1), (key1554, -1), (key1654, -1), (key1572, -1), (key1654, 1), (key1545, 1), (key1617, 1), (key1568, 1), (key1617, -1), (key1541, -1)]

theorem rawRowCheck5989 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form2 = rawRow5989 := by decide +kernel

def row5989 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck5989 : row5989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5989 := by decide +kernel

theorem rowEval5989 (x : Key → ℝ) : Integer.Sparse.eval row5989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5989, Integer.Sparse.eval_collectBalanced, rawRowCheck5989]

def rawRow5990 : Integer.Sparse Key := [(key1386, -1), (key1390, -1), (key1390, 2), (key1541, -1), (key1545, -1), (key1541, 2), (key1554, 2), (key1545, -1), (key1554, -1), (key1771, 2), (key1771, -1), (key1778, -1), (key1291, 1), (key1295, 1), (key1295, -2), (key1568, 1), (key1572, 1), (key1568, -2), (key1591, -2), (key1572, 1), (key1591, 1), (key1787, -2), (key1787, 1), (key1796, 1), (key1311, -1), (key1324, -1), (key1315, 1), (key1324, 1), (key1419, 1), (key1442, 1), (key1423, -1), (key1442, -1), (key1617, -1), (key1622, -1), (key1617, 1), (key1631, 1), (key1812, 1), (key1815, 1), (key1812, -1), (key1823, -1)]

theorem rawRowCheck5990 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form2 = rawRow5990 := by decide +kernel

def row5990 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck5990 : row5990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5990 := by decide +kernel

theorem rowEval5990 (x : Key → ℝ) : Integer.Sparse.eval row5990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5990, Integer.Sparse.eval_collectBalanced, rawRowCheck5990]

def rawRow5991 : Integer.Sparse Key := [(key1390, -1), (key1386, -1), (key1390, 2), (key1545, -1), (key1541, -1), (key1554, 2), (key1541, 2), (key1554, -1), (key1545, -1), (key1771, 2), (key1778, -1), (key1771, -1), (key1295, 1), (key1291, 1), (key1295, -2), (key1572, 1), (key1568, 1), (key1591, -2), (key1568, -2), (key1591, 1), (key1572, 1), (key1787, -2), (key1796, 1), (key1787, 1), (key1324, -1), (key1311, -1), (key1324, 1), (key1315, 1), (key1442, 1), (key1419, 1), (key1442, -1), (key1423, -1), (key1622, -1), (key1617, -1), (key1631, 1), (key1617, 1), (key1815, 1), (key1812, 1), (key1823, -1), (key1812, -1)]

theorem rawRowCheck5991 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form2 = rawRow5991 := by decide +kernel

def row5991 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck5991 : row5991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5991 := by decide +kernel

theorem rowEval5991 (x : Key → ℝ) : Integer.Sparse.eval row5991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5991, Integer.Sparse.eval_collectBalanced, rawRowCheck5991]

def rawRow5992 : Integer.Sparse Key := [(key1390, -1), (key1390, -1), (key1386, 2), (key1554, -1), (key1554, -1), (key1545, 2), (key1545, 2), (key1541, -1), (key1541, -1), (key1778, 2), (key1771, -1), (key1771, -1), (key1295, 1), (key1295, 1), (key1291, -2), (key1591, 1), (key1591, 1), (key1572, -2), (key1572, -2), (key1568, 1), (key1568, 1), (key1796, -2), (key1787, 1), (key1787, 1), (key1315, -1), (key1315, -1), (key1311, 1), (key1311, 1), (key1423, 1), (key1423, 1), (key1419, -1), (key1419, -1), (key1631, -1), (key1631, -1), (key1622, 1), (key1622, 1), (key1823, 1), (key1823, 1), (key1815, -1), (key1815, -1)]

theorem rawRowCheck5992 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form2 = rawRow5992 := by decide +kernel

def row5992 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1315, -2), (key1386, 2), (key1390, -2), (key1419, -2), (key1423, 2), (key1541, -2), (key1545, 4), (key1554, -2), (key1568, 2), (key1572, -4), (key1591, 2), (key1622, 2), (key1631, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

theorem rowCheck5992 : row5992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5992 := by decide +kernel

theorem rowEval5992 (x : Key → ℝ) : Integer.Sparse.eval row5992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5992, Integer.Sparse.eval_collectBalanced, rawRowCheck5992]

def rawRow5993 : Integer.Sparse Key := [(key1541, -1), (key1545, -1), (key1771, 2), (key1386, -1), (key1390, -1), (key1541, 2), (key1554, 2), (key1771, -1), (key1778, -1), (key1390, 2), (key1545, -1), (key1554, -1), (key1568, 1), (key1572, 1), (key1787, -2), (key1291, 1), (key1295, 1), (key1568, -2), (key1591, -2), (key1787, 1), (key1796, 1), (key1295, -2), (key1572, 1), (key1591, 1), (key1617, -1), (key1622, -1), (key1812, 1), (key1815, 1), (key1617, 1), (key1631, 1), (key1812, -1), (key1823, -1), (key1311, -1), (key1324, -1), (key1419, 1), (key1442, 1), (key1315, 1), (key1324, 1), (key1423, -1), (key1442, -1)]

theorem rawRowCheck5993 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form2 = rawRow5993 := by decide +kernel

def row5993 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck5993 : row5993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5993 := by decide +kernel

theorem rowEval5993 (x : Key → ℝ) : Integer.Sparse.eval row5993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5993, Integer.Sparse.eval_collectBalanced, rawRowCheck5993]

def rawRow5994 : Integer.Sparse Key := [(key1545, -1), (key1541, -1), (key1771, 2), (key1390, -1), (key1386, -1), (key1554, 2), (key1541, 2), (key1778, -1), (key1771, -1), (key1390, 2), (key1554, -1), (key1545, -1), (key1572, 1), (key1568, 1), (key1787, -2), (key1295, 1), (key1291, 1), (key1591, -2), (key1568, -2), (key1796, 1), (key1787, 1), (key1295, -2), (key1591, 1), (key1572, 1), (key1622, -1), (key1617, -1), (key1815, 1), (key1812, 1), (key1631, 1), (key1617, 1), (key1823, -1), (key1812, -1), (key1324, -1), (key1311, -1), (key1442, 1), (key1419, 1), (key1324, 1), (key1315, 1), (key1442, -1), (key1423, -1)]

theorem rawRowCheck5994 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form2 = rawRow5994 := by decide +kernel

def row5994 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck5994 : row5994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5994 := by decide +kernel

theorem rowEval5994 (x : Key → ℝ) : Integer.Sparse.eval row5994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5994, Integer.Sparse.eval_collectBalanced, rawRowCheck5994]

def rawRow5995 : Integer.Sparse Key := [(key1541, -1), (key1771, -1), (key1545, 2), (key1541, -1), (key1771, -1), (key1386, 2), (key1778, 2), (key1390, -1), (key1554, -1), (key1545, 2), (key1390, -1), (key1554, -1), (key1568, 1), (key1787, 1), (key1572, -2), (key1568, 1), (key1787, 1), (key1291, -2), (key1796, -2), (key1295, 1), (key1591, 1), (key1572, -2), (key1295, 1), (key1591, 1), (key1419, -1), (key1815, -1), (key1423, 1), (key1622, 1), (key1311, 1), (key1823, 1), (key1315, -1), (key1631, -1), (key1419, -1), (key1815, -1), (key1311, 1), (key1823, 1), (key1423, 1), (key1622, 1), (key1315, -1), (key1631, -1)]

theorem rawRowCheck5995 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form2 = rawRow5995 := by decide +kernel

def row5995 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1315, -2), (key1386, 2), (key1390, -2), (key1419, -2), (key1423, 2), (key1541, -2), (key1545, 4), (key1554, -2), (key1568, 2), (key1572, -4), (key1591, 2), (key1622, 2), (key1631, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

theorem rowCheck5995 : row5995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5995 := by decide +kernel

theorem rowEval5995 (x : Key → ℝ) : Integer.Sparse.eval row5995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5995, Integer.Sparse.eval_collectBalanced, rawRowCheck5995]

def rawRow5996 : Integer.Sparse Key := [(key1771, -1), (key1541, -1), (key1545, 2), (key1771, -1), (key1541, -1), (key1778, 2), (key1386, 2), (key1554, -1), (key1390, -1), (key1545, 2), (key1554, -1), (key1390, -1), (key1787, 1), (key1568, 1), (key1572, -2), (key1787, 1), (key1568, 1), (key1796, -2), (key1291, -2), (key1591, 1), (key1295, 1), (key1572, -2), (key1591, 1), (key1295, 1), (key1815, -1), (key1419, -1), (key1622, 1), (key1423, 1), (key1823, 1), (key1311, 1), (key1631, -1), (key1315, -1), (key1815, -1), (key1419, -1), (key1823, 1), (key1311, 1), (key1622, 1), (key1423, 1), (key1631, -1), (key1315, -1)]

theorem rawRowCheck5996 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form2 = rawRow5996 := by decide +kernel

def row5996 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1315, -2), (key1386, 2), (key1390, -2), (key1419, -2), (key1423, 2), (key1541, -2), (key1545, 4), (key1554, -2), (key1568, 2), (key1572, -4), (key1591, 2), (key1622, 2), (key1631, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

theorem rowCheck5996 : row5996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5996 := by decide +kernel

theorem rowEval5996 (x : Key → ℝ) : Integer.Sparse.eval row5996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5996, Integer.Sparse.eval_collectBalanced, rawRowCheck5996]

def rawRow5997 : Integer.Sparse Key := [(key1545, -1), (key1771, -1), (key1541, 2), (key1554, -1), (key1778, -1), (key1390, 2), (key1771, 2), (key1386, -1), (key1541, -1), (key1554, 2), (key1390, -1), (key1545, -1), (key1572, 1), (key1787, 1), (key1568, -2), (key1591, 1), (key1796, 1), (key1295, -2), (key1787, -2), (key1291, 1), (key1568, 1), (key1591, -2), (key1295, 1), (key1572, 1), (key1423, -1), (key1812, -1), (key1419, 1), (key1617, 1), (key1315, 1), (key1812, 1), (key1311, -1), (key1617, -1), (key1442, -1), (key1823, -1), (key1324, 1), (key1815, 1), (key1442, 1), (key1631, 1), (key1324, -1), (key1622, -1)]

theorem rawRowCheck5997 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form2 = rawRow5997 := by decide +kernel

def row5997 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck5997 : row5997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5997 := by decide +kernel

theorem rowEval5997 (x : Key → ℝ) : Integer.Sparse.eval row5997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5997, Integer.Sparse.eval_collectBalanced, rawRowCheck5997]

def rawRow5998 : Integer.Sparse Key := [(key1771, -1), (key1545, -1), (key1541, 2), (key1778, -1), (key1554, -1), (key1771, 2), (key1390, 2), (key1541, -1), (key1386, -1), (key1554, 2), (key1545, -1), (key1390, -1), (key1787, 1), (key1572, 1), (key1568, -2), (key1796, 1), (key1591, 1), (key1787, -2), (key1295, -2), (key1568, 1), (key1291, 1), (key1591, -2), (key1572, 1), (key1295, 1), (key1812, -1), (key1423, -1), (key1617, 1), (key1419, 1), (key1812, 1), (key1315, 1), (key1617, -1), (key1311, -1), (key1823, -1), (key1442, -1), (key1815, 1), (key1324, 1), (key1631, 1), (key1442, 1), (key1622, -1), (key1324, -1)]

theorem rawRowCheck5998 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form2 = rawRow5998 := by decide +kernel

def row5998 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck5998 : row5998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5998 := by decide +kernel

theorem rowEval5998 (x : Key → ℝ) : Integer.Sparse.eval row5998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5998, Integer.Sparse.eval_collectBalanced, rawRowCheck5998]

def rawRow5999 : Integer.Sparse Key := [(key1554, -1), (key1554, -1), (key1778, 2), (key1390, -1), (key1390, -1), (key1545, 2), (key1545, 2), (key1771, -1), (key1771, -1), (key1386, 2), (key1541, -1), (key1541, -1), (key1591, 1), (key1591, 1), (key1796, -2), (key1295, 1), (key1295, 1), (key1572, -2), (key1572, -2), (key1787, 1), (key1787, 1), (key1291, -2), (key1568, 1), (key1568, 1), (key1631, -1), (key1631, -1), (key1823, 1), (key1823, 1), (key1622, 1), (key1622, 1), (key1815, -1), (key1815, -1), (key1315, -1), (key1315, -1), (key1423, 1), (key1423, 1), (key1311, 1), (key1311, 1), (key1419, -1), (key1419, -1)]

theorem rawRowCheck5999 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form2 = rawRow5999 := by decide +kernel

def row5999 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1315, -2), (key1386, 2), (key1390, -2), (key1419, -2), (key1423, 2), (key1541, -2), (key1545, 4), (key1554, -2), (key1568, 2), (key1572, -4), (key1591, 2), (key1622, 2), (key1631, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

theorem rowCheck5999 : row5999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5999 := by decide +kernel

theorem rowEval5999 (x : Key → ℝ) : Integer.Sparse.eval row5999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5999, Integer.Sparse.eval_collectBalanced, rawRowCheck5999]

def rawRow6000 : Integer.Sparse Key := [(key1554, -1), (key1778, -1), (key1554, 2), (key1545, -1), (key1771, -1), (key1390, 2), (key1771, 2), (key1390, -1), (key1545, -1), (key1541, 2), (key1386, -1), (key1541, -1), (key1591, 1), (key1796, 1), (key1591, -2), (key1572, 1), (key1787, 1), (key1295, -2), (key1787, -2), (key1295, 1), (key1572, 1), (key1568, -2), (key1291, 1), (key1568, 1), (key1442, -1), (key1823, -1), (key1442, 1), (key1631, 1), (key1324, 1), (key1815, 1), (key1324, -1), (key1622, -1), (key1423, -1), (key1812, -1), (key1315, 1), (key1812, 1), (key1419, 1), (key1617, 1), (key1311, -1), (key1617, -1)]

theorem rawRowCheck6000 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form2 = rawRow6000 := by decide +kernel

def row6000 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck6000 : row6000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6000 := by decide +kernel

theorem rowEval6000 (x : Key → ℝ) : Integer.Sparse.eval row6000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6000, Integer.Sparse.eval_collectBalanced, rawRowCheck6000]

def rawRow6001 : Integer.Sparse Key := [(key1778, -1), (key1554, -1), (key1554, 2), (key1771, -1), (key1545, -1), (key1771, 2), (key1390, 2), (key1545, -1), (key1390, -1), (key1541, 2), (key1541, -1), (key1386, -1), (key1796, 1), (key1591, 1), (key1591, -2), (key1787, 1), (key1572, 1), (key1787, -2), (key1295, -2), (key1572, 1), (key1295, 1), (key1568, -2), (key1568, 1), (key1291, 1), (key1823, -1), (key1442, -1), (key1631, 1), (key1442, 1), (key1815, 1), (key1324, 1), (key1622, -1), (key1324, -1), (key1812, -1), (key1423, -1), (key1812, 1), (key1315, 1), (key1617, 1), (key1419, 1), (key1617, -1), (key1311, -1)]

theorem rawRowCheck6001 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form2 = rawRow6001 := by decide +kernel

def row6001 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck6001 : row6001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6001 := by decide +kernel

theorem rowEval6001 (x : Key → ℝ) : Integer.Sparse.eval row6001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6001, Integer.Sparse.eval_collectBalanced, rawRowCheck6001]

def rawRow6002 : Integer.Sparse Key := [(key1419, -1), (key1454, -1), (key1423, 2), (key1617, -1), (key1654, -1), (key1568, 2), (key1657, 2), (key1572, -1), (key1622, -1), (key1812, 2), (key1787, -1), (key1815, -1), (key1311, 1), (key1336, 1), (key1315, -2), (key1617, 1), (key1654, 1), (key1541, -2), (key1665, -2), (key1545, 1), (key1631, 1), (key1812, -2), (key1771, 1), (key1823, 1), (key1291, -1), (key1343, -1), (key1295, 1), (key1324, 1), (key1386, 1), (key1464, 1), (key1390, -1), (key1442, -1), (key1568, -1), (key1657, -1), (key1541, 1), (key1665, 1), (key1787, 1), (key1815, 1), (key1771, -1), (key1823, -1)]

theorem rawRowCheck6002 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form2 = rawRow6002 := by decide +kernel

def row6002 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck6002 : row6002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6002 := by decide +kernel

theorem rowEval6002 (x : Key → ℝ) : Integer.Sparse.eval row6002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6002, Integer.Sparse.eval_collectBalanced, rawRowCheck6002]

def rawRow6003 : Integer.Sparse Key := [(key1454, -1), (key1419, -1), (key1423, 2), (key1654, -1), (key1617, -1), (key1657, 2), (key1568, 2), (key1622, -1), (key1572, -1), (key1812, 2), (key1815, -1), (key1787, -1), (key1336, 1), (key1311, 1), (key1315, -2), (key1654, 1), (key1617, 1), (key1665, -2), (key1541, -2), (key1631, 1), (key1545, 1), (key1812, -2), (key1823, 1), (key1771, 1), (key1343, -1), (key1291, -1), (key1324, 1), (key1295, 1), (key1464, 1), (key1386, 1), (key1442, -1), (key1390, -1), (key1657, -1), (key1568, -1), (key1665, 1), (key1541, 1), (key1815, 1), (key1787, 1), (key1823, -1), (key1771, -1)]

theorem rawRowCheck6003 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form2 = rawRow6003 := by decide +kernel

def row6003 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck6003 : row6003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6003 := by decide +kernel

theorem rowEval6003 (x : Key → ℝ) : Integer.Sparse.eval row6003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6003, Integer.Sparse.eval_collectBalanced, rawRowCheck6003]

def rawRow6004 : Integer.Sparse Key := [(key1423, -1), (key1454, -1), (key1419, 2), (key1622, -1), (key1657, -1), (key1572, 2), (key1654, 2), (key1568, -1), (key1617, -1), (key1815, 2), (key1787, -1), (key1812, -1), (key1315, 1), (key1336, 1), (key1311, -2), (key1631, 1), (key1665, 1), (key1545, -2), (key1654, -2), (key1541, 1), (key1617, 1), (key1823, -2), (key1771, 1), (key1812, 1), (key1295, -1), (key1336, -1), (key1291, 1), (key1311, 1), (key1390, 1), (key1454, 1), (key1386, -1), (key1419, -1), (key1591, -1), (key1665, -1), (key1554, 1), (key1657, 1), (key1796, 1), (key1823, 1), (key1778, -1), (key1815, -1)]

theorem rawRowCheck6004 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form2 = rawRow6004 := by decide +kernel

def row6004 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck6004 : row6004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6004 := by decide +kernel

theorem rowEval6004 (x : Key → ℝ) : Integer.Sparse.eval row6004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6004, Integer.Sparse.eval_collectBalanced, rawRowCheck6004]

def rawRow6005 : Integer.Sparse Key := [(key1454, -1), (key1423, -1), (key1419, 2), (key1657, -1), (key1622, -1), (key1654, 2), (key1572, 2), (key1617, -1), (key1568, -1), (key1815, 2), (key1812, -1), (key1787, -1), (key1336, 1), (key1315, 1), (key1311, -2), (key1665, 1), (key1631, 1), (key1654, -2), (key1545, -2), (key1617, 1), (key1541, 1), (key1823, -2), (key1812, 1), (key1771, 1), (key1336, -1), (key1295, -1), (key1311, 1), (key1291, 1), (key1454, 1), (key1390, 1), (key1419, -1), (key1386, -1), (key1665, -1), (key1591, -1), (key1657, 1), (key1554, 1), (key1823, 1), (key1796, 1), (key1815, -1), (key1778, -1)]

theorem rawRowCheck6005 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form2 = rawRow6005 := by decide +kernel

def row6005 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck6005 : row6005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6005 := by decide +kernel

theorem rowEval6005 (x : Key → ℝ) : Integer.Sparse.eval row6005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6005, Integer.Sparse.eval_collectBalanced, rawRowCheck6005]

def rawRow6006 : Integer.Sparse Key := [(key1568, -1), (key1787, -1), (key1572, 2), (key1617, -1), (key1812, -1), (key1419, 2), (key1815, 2), (key1423, -1), (key1622, -1), (key1654, 2), (key1454, -1), (key1657, -1), (key1541, 1), (key1771, 1), (key1545, -2), (key1617, 1), (key1812, 1), (key1311, -2), (key1823, -2), (key1315, 1), (key1631, 1), (key1654, -2), (key1336, 1), (key1665, 1), (key1386, -1), (key1778, -1), (key1390, 1), (key1554, 1), (key1291, 1), (key1796, 1), (key1295, -1), (key1591, -1), (key1419, -1), (key1815, -1), (key1311, 1), (key1823, 1), (key1454, 1), (key1657, 1), (key1336, -1), (key1665, -1)]

theorem rawRowCheck6006 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form2 = rawRow6006 := by decide +kernel

def row6006 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck6006 : row6006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6006 := by decide +kernel

theorem rowEval6006 (x : Key → ℝ) : Integer.Sparse.eval row6006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6006, Integer.Sparse.eval_collectBalanced, rawRowCheck6006]

def rawRow6007 : Integer.Sparse Key := [(key1787, -1), (key1568, -1), (key1572, 2), (key1812, -1), (key1617, -1), (key1815, 2), (key1419, 2), (key1622, -1), (key1423, -1), (key1654, 2), (key1657, -1), (key1454, -1), (key1771, 1), (key1541, 1), (key1545, -2), (key1812, 1), (key1617, 1), (key1823, -2), (key1311, -2), (key1631, 1), (key1315, 1), (key1654, -2), (key1665, 1), (key1336, 1), (key1778, -1), (key1386, -1), (key1554, 1), (key1390, 1), (key1796, 1), (key1291, 1), (key1591, -1), (key1295, -1), (key1815, -1), (key1419, -1), (key1823, 1), (key1311, 1), (key1657, 1), (key1454, 1), (key1665, -1), (key1336, -1)]

theorem rawRowCheck6007 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form2 = rawRow6007 := by decide +kernel

def row6007 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck6007 : row6007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6007 := by decide +kernel

theorem rowEval6007 (x : Key → ℝ) : Integer.Sparse.eval row6007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6007, Integer.Sparse.eval_collectBalanced, rawRowCheck6007]

def rawRow6008 : Integer.Sparse Key := [(key1572, -1), (key1787, -1), (key1568, 2), (key1622, -1), (key1815, -1), (key1423, 2), (key1812, 2), (key1419, -1), (key1617, -1), (key1657, 2), (key1454, -1), (key1654, -1), (key1545, 1), (key1771, 1), (key1541, -2), (key1631, 1), (key1823, 1), (key1315, -2), (key1812, -2), (key1311, 1), (key1617, 1), (key1665, -2), (key1336, 1), (key1654, 1), (key1390, -1), (key1771, -1), (key1386, 1), (key1541, 1), (key1295, 1), (key1787, 1), (key1291, -1), (key1568, -1), (key1442, -1), (key1823, -1), (key1324, 1), (key1815, 1), (key1464, 1), (key1665, 1), (key1343, -1), (key1657, -1)]

theorem rawRowCheck6008 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form2 = rawRow6008 := by decide +kernel

def row6008 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck6008 : row6008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6008 := by decide +kernel

theorem rowEval6008 (x : Key → ℝ) : Integer.Sparse.eval row6008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6008, Integer.Sparse.eval_collectBalanced, rawRowCheck6008]

def rawRow6009 : Integer.Sparse Key := [(key1787, -1), (key1572, -1), (key1568, 2), (key1815, -1), (key1622, -1), (key1812, 2), (key1423, 2), (key1617, -1), (key1419, -1), (key1657, 2), (key1654, -1), (key1454, -1), (key1771, 1), (key1545, 1), (key1541, -2), (key1823, 1), (key1631, 1), (key1812, -2), (key1315, -2), (key1617, 1), (key1311, 1), (key1665, -2), (key1654, 1), (key1336, 1), (key1771, -1), (key1390, -1), (key1541, 1), (key1386, 1), (key1787, 1), (key1295, 1), (key1568, -1), (key1291, -1), (key1823, -1), (key1442, -1), (key1815, 1), (key1324, 1), (key1665, 1), (key1464, 1), (key1657, -1), (key1343, -1)]

theorem rawRowCheck6009 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form2 = rawRow6009 := by decide +kernel

def row6009 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck6009 : row6009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6009 := by decide +kernel

theorem rowEval6009 (x : Key → ℝ) : Integer.Sparse.eval row6009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6009, Integer.Sparse.eval_collectBalanced, rawRowCheck6009]

def rawRow6010 : Integer.Sparse Key := [(key1617, -1), (key1654, -1), (key1812, 2), (key1419, -1), (key1454, -1), (key1568, 2), (key1657, 2), (key1787, -1), (key1815, -1), (key1423, 2), (key1572, -1), (key1622, -1), (key1617, 1), (key1654, 1), (key1812, -2), (key1311, 1), (key1336, 1), (key1541, -2), (key1665, -2), (key1771, 1), (key1823, 1), (key1315, -2), (key1545, 1), (key1631, 1), (key1568, -1), (key1657, -1), (key1787, 1), (key1815, 1), (key1541, 1), (key1665, 1), (key1771, -1), (key1823, -1), (key1291, -1), (key1343, -1), (key1386, 1), (key1464, 1), (key1295, 1), (key1324, 1), (key1390, -1), (key1442, -1)]

theorem rawRowCheck6010 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form2 = rawRow6010 := by decide +kernel

def row6010 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck6010 : row6010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6010 := by decide +kernel

theorem rowEval6010 (x : Key → ℝ) : Integer.Sparse.eval row6010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6010, Integer.Sparse.eval_collectBalanced, rawRowCheck6010]

def rawRow6011 : Integer.Sparse Key := [(key1654, -1), (key1617, -1), (key1812, 2), (key1454, -1), (key1419, -1), (key1657, 2), (key1568, 2), (key1815, -1), (key1787, -1), (key1423, 2), (key1622, -1), (key1572, -1), (key1654, 1), (key1617, 1), (key1812, -2), (key1336, 1), (key1311, 1), (key1665, -2), (key1541, -2), (key1823, 1), (key1771, 1), (key1315, -2), (key1631, 1), (key1545, 1), (key1657, -1), (key1568, -1), (key1815, 1), (key1787, 1), (key1665, 1), (key1541, 1), (key1823, -1), (key1771, -1), (key1343, -1), (key1291, -1), (key1464, 1), (key1386, 1), (key1324, 1), (key1295, 1), (key1442, -1), (key1390, -1)]

theorem rawRowCheck6011 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form2 = rawRow6011 := by decide +kernel

def row6011 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck6011 : row6011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6011 := by decide +kernel

theorem rowEval6011 (x : Key → ℝ) : Integer.Sparse.eval row6011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6011, Integer.Sparse.eval_collectBalanced, rawRowCheck6011]

def rawRow6012 : Integer.Sparse Key := [(key1617, -1), (key1812, -1), (key1654, 2), (key1568, -1), (key1787, -1), (key1419, 2), (key1815, 2), (key1454, -1), (key1657, -1), (key1572, 2), (key1423, -1), (key1622, -1), (key1617, 1), (key1812, 1), (key1654, -2), (key1541, 1), (key1771, 1), (key1311, -2), (key1823, -2), (key1336, 1), (key1665, 1), (key1545, -2), (key1315, 1), (key1631, 1), (key1419, -1), (key1815, -1), (key1454, 1), (key1657, 1), (key1311, 1), (key1823, 1), (key1336, -1), (key1665, -1), (key1386, -1), (key1778, -1), (key1291, 1), (key1796, 1), (key1390, 1), (key1554, 1), (key1295, -1), (key1591, -1)]

theorem rawRowCheck6012 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form2 = rawRow6012 := by decide +kernel

def row6012 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck6012 : row6012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6012 := by decide +kernel

theorem rowEval6012 (x : Key → ℝ) : Integer.Sparse.eval row6012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6012, Integer.Sparse.eval_collectBalanced, rawRowCheck6012]

def rawRow6013 : Integer.Sparse Key := [(key1812, -1), (key1617, -1), (key1654, 2), (key1787, -1), (key1568, -1), (key1815, 2), (key1419, 2), (key1657, -1), (key1454, -1), (key1572, 2), (key1622, -1), (key1423, -1), (key1812, 1), (key1617, 1), (key1654, -2), (key1771, 1), (key1541, 1), (key1823, -2), (key1311, -2), (key1665, 1), (key1336, 1), (key1545, -2), (key1631, 1), (key1315, 1), (key1815, -1), (key1419, -1), (key1657, 1), (key1454, 1), (key1823, 1), (key1311, 1), (key1665, -1), (key1336, -1), (key1778, -1), (key1386, -1), (key1796, 1), (key1291, 1), (key1554, 1), (key1390, 1), (key1591, -1), (key1295, -1)]

theorem rawRowCheck6013 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form2 = rawRow6013 := by decide +kernel

def row6013 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck6013 : row6013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6013 := by decide +kernel

theorem rowEval6013 (x : Key → ℝ) : Integer.Sparse.eval row6013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6013, Integer.Sparse.eval_collectBalanced, rawRowCheck6013]

def rawRow6014 : Integer.Sparse Key := [(key1622, -1), (key1657, -1), (key1815, 2), (key1423, -1), (key1454, -1), (key1572, 2), (key1654, 2), (key1787, -1), (key1812, -1), (key1419, 2), (key1568, -1), (key1617, -1), (key1631, 1), (key1665, 1), (key1823, -2), (key1315, 1), (key1336, 1), (key1545, -2), (key1654, -2), (key1771, 1), (key1812, 1), (key1311, -2), (key1541, 1), (key1617, 1), (key1591, -1), (key1665, -1), (key1796, 1), (key1823, 1), (key1554, 1), (key1657, 1), (key1778, -1), (key1815, -1), (key1295, -1), (key1336, -1), (key1390, 1), (key1454, 1), (key1291, 1), (key1311, 1), (key1386, -1), (key1419, -1)]

theorem rawRowCheck6014 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form2 = rawRow6014 := by decide +kernel

def row6014 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck6014 : row6014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6014 := by decide +kernel

theorem rowEval6014 (x : Key → ℝ) : Integer.Sparse.eval row6014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6014, Integer.Sparse.eval_collectBalanced, rawRowCheck6014]

def rawRow6015 : Integer.Sparse Key := [(key1657, -1), (key1622, -1), (key1815, 2), (key1454, -1), (key1423, -1), (key1654, 2), (key1572, 2), (key1812, -1), (key1787, -1), (key1419, 2), (key1617, -1), (key1568, -1), (key1665, 1), (key1631, 1), (key1823, -2), (key1336, 1), (key1315, 1), (key1654, -2), (key1545, -2), (key1812, 1), (key1771, 1), (key1311, -2), (key1617, 1), (key1541, 1), (key1665, -1), (key1591, -1), (key1823, 1), (key1796, 1), (key1657, 1), (key1554, 1), (key1815, -1), (key1778, -1), (key1336, -1), (key1295, -1), (key1454, 1), (key1390, 1), (key1311, 1), (key1291, 1), (key1419, -1), (key1386, -1)]

theorem rawRowCheck6015 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form2 = rawRow6015 := by decide +kernel

def row6015 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck6015 : row6015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6015 := by decide +kernel

theorem rowEval6015 (x : Key → ℝ) : Integer.Sparse.eval row6015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6015, Integer.Sparse.eval_collectBalanced, rawRowCheck6015]

end MUB6.Certificate.GramRows

end OAI
