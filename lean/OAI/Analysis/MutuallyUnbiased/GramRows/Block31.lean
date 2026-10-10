import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
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

def rawRow1088 : Integer.Sparse Key := [(key2695, -2), (key2836, -2), (key2695, -2), (key2693, 1), (key2686, 1), (key2822, 1), (key2686, 1), (key2822, 1), (key2693, 1), (key3074, 2), (key3146, 2), (key3074, 2), (key3070, -1), (key3051, -1), (key3107, -1), (key3051, -1), (key3107, -1), (key3070, -1), (key3078, -1), (key3074, -1), (key3146, -1), (key3074, -1), (key3146, -1), (key3078, -1), (key3077, 1), (key3057, 1), (key3116, 1), (key3057, 1), (key3116, 1), (key3077, 1)]

theorem rawRowCheck1088 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form0 = rawRow1088 := by decide +kernel

def row1088 : Integer.Sparse Key := [(key2686, 2), (key2693, 2), (key2695, -4), (key2822, 2), (key2836, -2), (key3051, -2), (key3057, 2), (key3070, -2), (key3074, 2), (key3077, 2), (key3078, -2), (key3107, -2), (key3116, 2)]

theorem rowCheck1088 : row1088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1088 := by decide +kernel

theorem rowEval1088 (x : Key → ℝ) : Integer.Sparse.eval row1088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1088, Integer.Sparse.eval_collectBalanced, rawRowCheck1088]

def rawRow1089 : Integer.Sparse Key := [(key2836, -2), (key2695, -2), (key2695, -2), (key2822, 1), (key2822, 1), (key2693, 1), (key2693, 1), (key2686, 1), (key2686, 1), (key3146, 2), (key3074, 2), (key3074, 2), (key3107, -1), (key3107, -1), (key3070, -1), (key3070, -1), (key3051, -1), (key3051, -1), (key3146, -1), (key3146, -1), (key3078, -1), (key3078, -1), (key3074, -1), (key3074, -1), (key3116, 1), (key3116, 1), (key3077, 1), (key3077, 1), (key3057, 1), (key3057, 1)]

theorem rawRowCheck1089 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form0 = rawRow1089 := by decide +kernel

def row1089 : Integer.Sparse Key := [(key2686, 2), (key2693, 2), (key2695, -4), (key2822, 2), (key2836, -2), (key3051, -2), (key3057, 2), (key3070, -2), (key3074, 2), (key3077, 2), (key3078, -2), (key3107, -2), (key3116, 2)]

theorem rowCheck1089 : row1089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1089 := by decide +kernel

theorem rowEval1089 (x : Key → ℝ) : Integer.Sparse.eval row1089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1089, Integer.Sparse.eval_collectBalanced, rawRowCheck1089]

def rawRow1090 : Integer.Sparse Key := [(key2719, -2), (key2719, -2), (key3027, -2), (key2719, 1), (key2733, 1), (key2719, 1), (key3027, 1), (key2733, 1), (key3027, 1), (key2693, 2), (key3055, 2), (key3117, 2), (key3055, -1), (key3078, -1), (key3055, -1), (key3117, -1), (key3078, -1), (key3117, -1), (key3051, -1), (key3057, -1), (key3051, -1), (key3112, -1), (key3057, -1), (key3112, -1), (key3051, 1), (key3074, 1), (key3051, 1), (key3112, 1), (key3074, 1), (key3112, 1)]

theorem rawRowCheck1090 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form0 = rawRow1090 := by decide +kernel

def row1090 : Integer.Sparse Key := [(key2693, 2), (key2719, -2), (key2733, 2), (key3057, -2), (key3074, 2), (key3078, -2)]

theorem rowCheck1090 : row1090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1090 := by decide +kernel

theorem rowEval1090 (x : Key → ℝ) : Integer.Sparse.eval row1090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1090, Integer.Sparse.eval_collectBalanced, rawRowCheck1090]

def rawRow1091 : Integer.Sparse Key := [(key2719, -2), (key3027, -2), (key2719, -2), (key2733, 1), (key2719, 1), (key3027, 1), (key2719, 1), (key3027, 1), (key2733, 1), (key2693, 2), (key3117, 2), (key3055, 2), (key3078, -1), (key3055, -1), (key3117, -1), (key3055, -1), (key3117, -1), (key3078, -1), (key3057, -1), (key3051, -1), (key3112, -1), (key3051, -1), (key3112, -1), (key3057, -1), (key3074, 1), (key3051, 1), (key3112, 1), (key3051, 1), (key3112, 1), (key3074, 1)]

theorem rawRowCheck1091 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form0 = rawRow1091 := by decide +kernel

def row1091 : Integer.Sparse Key := [(key2693, 2), (key2719, -2), (key2733, 2), (key3057, -2), (key3074, 2), (key3078, -2)]

theorem rowCheck1091 : row1091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1091 := by decide +kernel

theorem rowEval1091 (x : Key → ℝ) : Integer.Sparse.eval row1091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1091, Integer.Sparse.eval_collectBalanced, rawRowCheck1091]

def rawRow1092 : Integer.Sparse Key := [(key3027, -2), (key2719, -2), (key2719, -2), (key3027, 1), (key3027, 1), (key2733, 1), (key2733, 1), (key2719, 1), (key2719, 1), (key3018, 2), (key2693, 2), (key2693, 2), (key3117, -1), (key3117, -1), (key3078, -1), (key3078, -1), (key3055, -1), (key3055, -1), (key3112, -1), (key3112, -1), (key3057, -1), (key3057, -1), (key3051, -1), (key3051, -1), (key3112, 1), (key3112, 1), (key3074, 1), (key3074, 1), (key3051, 1), (key3051, 1)]

theorem rawRowCheck1092 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form0 = rawRow1092 := by decide +kernel

def row1092 : Integer.Sparse Key := [(key2693, 4), (key2719, -2), (key2733, 2), (key3018, 2), (key3055, -2), (key3057, -2), (key3074, 2), (key3078, -2), (key3117, -2)]

theorem rowCheck1092 : row1092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1092 := by decide +kernel

theorem rowEval1092 (x : Key → ℝ) : Integer.Sparse.eval row1092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1092, Integer.Sparse.eval_collectBalanced, rawRowCheck1092]

def rawRow1093 : Integer.Sparse Key := [(key2733, -2), (key2733, -2), (key2733, -2), (key2719, 1), (key2719, 1), (key2719, 1), (key2719, 1), (key2719, 1), (key2719, 1), (key2759, 2), (key2759, 2), (key2759, 2), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key3074, -1), (key3074, -1), (key3074, -1), (key3074, -1), (key3074, -1), (key3074, -1), (key3057, 1), (key3057, 1), (key3057, 1), (key3057, 1), (key3057, 1), (key3057, 1)]

theorem rawRowCheck1093 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form0 = rawRow1093 := by decide +kernel

def row1093 : Integer.Sparse Key := [(key2693, -6), (key2719, 6), (key2733, -6), (key2759, 6), (key3057, 6), (key3074, -6)]

theorem rowCheck1093 : row1093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1093 := by decide +kernel

theorem rowEval1093 (x : Key → ℝ) : Integer.Sparse.eval row1093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1093, Integer.Sparse.eval_collectBalanced, rawRowCheck1093]

def rawRow1094 : Integer.Sparse Key := [(key2756, -2), (key2756, -2), (key2924, -2), (key2756, 1), (key2759, 1), (key2756, 1), (key2924, 1), (key2759, 1), (key2924, 1), (key2695, 2), (key2695, 2), (key2836, 2), (key2695, -1), (key2733, -1), (key2695, -1), (key2836, -1), (key2733, -1), (key2836, -1), (key2686, -1), (key2693, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2822, -1), (key2686, 1), (key2719, 1), (key2686, 1), (key2822, 1), (key2719, 1), (key2822, 1)]

theorem rawRowCheck1094 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form0 = rawRow1094 := by decide +kernel

def row1094 : Integer.Sparse Key := [(key2693, -2), (key2695, 2), (key2719, 2), (key2733, -2), (key2756, -2), (key2759, 2)]

theorem rowCheck1094 : row1094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1094 := by decide +kernel

theorem rowEval1094 (x : Key → ℝ) : Integer.Sparse.eval row1094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1094, Integer.Sparse.eval_collectBalanced, rawRowCheck1094]

def rawRow1095 : Integer.Sparse Key := [(key2756, -2), (key2924, -2), (key2756, -2), (key2759, 1), (key2756, 1), (key2924, 1), (key2756, 1), (key2924, 1), (key2759, 1), (key2695, 2), (key2836, 2), (key2695, 2), (key2733, -1), (key2695, -1), (key2836, -1), (key2695, -1), (key2836, -1), (key2733, -1), (key2693, -1), (key2686, -1), (key2822, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2719, 1), (key2686, 1), (key2822, 1), (key2686, 1), (key2822, 1), (key2719, 1)]

theorem rawRowCheck1095 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form0 = rawRow1095 := by decide +kernel

def row1095 : Integer.Sparse Key := [(key2693, -2), (key2695, 2), (key2719, 2), (key2733, -2), (key2756, -2), (key2759, 2)]

theorem rowCheck1095 : row1095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1095 := by decide +kernel

theorem rowEval1095 (x : Key → ℝ) : Integer.Sparse.eval row1095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1095, Integer.Sparse.eval_collectBalanced, rawRowCheck1095]

def rawRow1096 : Integer.Sparse Key := [(key2924, -2), (key2756, -2), (key2756, -2), (key2924, 1), (key2924, 1), (key2759, 1), (key2759, 1), (key2756, 1), (key2756, 1), (key2836, 2), (key2695, 2), (key2695, 2), (key2836, -1), (key2836, -1), (key2733, -1), (key2733, -1), (key2695, -1), (key2695, -1), (key2822, -1), (key2822, -1), (key2693, -1), (key2693, -1), (key2686, -1), (key2686, -1), (key2822, 1), (key2822, 1), (key2719, 1), (key2719, 1), (key2686, 1), (key2686, 1)]

theorem rawRowCheck1096 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form0 = rawRow1096 := by decide +kernel

def row1096 : Integer.Sparse Key := [(key2693, -2), (key2695, 2), (key2719, 2), (key2733, -2), (key2756, -2), (key2759, 2)]

theorem rowCheck1096 : row1096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1096 := by decide +kernel

theorem rowEval1096 (x : Key → ℝ) : Integer.Sparse.eval row1096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1096, Integer.Sparse.eval_collectBalanced, rawRowCheck1096]

def rawRow1097 : Integer.Sparse Key := [(key2759, -2), (key2759, -2), (key2759, -2), (key2756, 1), (key2756, 1), (key2756, 1), (key2756, 1), (key2756, 1), (key2756, 1), (key2733, 2), (key2733, 2), (key2733, 2), (key2695, -1), (key2695, -1), (key2695, -1), (key2695, -1), (key2695, -1), (key2695, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2693, 1), (key2693, 1), (key2693, 1), (key2693, 1), (key2693, 1), (key2693, 1)]

theorem rawRowCheck1097 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form0 = rawRow1097 := by decide +kernel

def row1097 : Integer.Sparse Key := [(key2693, 6), (key2695, -6), (key2719, -6), (key2733, 6), (key2756, 6), (key2759, -6)]

theorem rowCheck1097 : row1097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1097 := by decide +kernel

theorem rowEval1097 (x : Key → ℝ) : Integer.Sparse.eval row1097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1097, Integer.Sparse.eval_collectBalanced, rawRowCheck1097]

def rawRow1098 : Integer.Sparse Key := [(key1432, -6), (key1404, 2), (key1404, 2), (key1475, 2), (key1581, 6), (key1404, -2), (key1404, -2), (key1906, -2), (key1581, -2), (key1581, -2), (key1686, -2), (key1432, 2), (key1432, 2), (key1923, 2)]

theorem rawRowCheck1098 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form1 = rawRow1098 := by decide +kernel

def row1098 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

theorem rowCheck1098 : row1098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1098 := by decide +kernel

theorem rowEval1098 (x : Key → ℝ) : Integer.Sparse.eval row1098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1098, Integer.Sparse.eval_collectBalanced, rawRowCheck1098]

def rawRow1099 : Integer.Sparse Key := [(key1432, -6), (key1404, 2), (key1475, 2), (key1404, 2), (key1581, 6), (key1404, -2), (key1906, -2), (key1404, -2), (key1581, -2), (key1686, -2), (key1581, -2), (key1432, 2), (key1923, 2), (key1432, 2)]

theorem rawRowCheck1099 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form1 = rawRow1099 := by decide +kernel

def row1099 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

theorem rowCheck1099 : row1099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1099 := by decide +kernel

theorem rowEval1099 (x : Key → ℝ) : Integer.Sparse.eval row1099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1099, Integer.Sparse.eval_collectBalanced, rawRowCheck1099]

def rawRow1100 : Integer.Sparse Key := [(key1432, -6), (key1475, 2), (key1404, 2), (key1404, 2), (key1581, 6), (key1906, -2), (key1404, -2), (key1404, -2), (key1686, -2), (key1581, -2), (key1581, -2), (key1923, 2), (key1432, 2), (key1432, 2)]

theorem rawRowCheck1100 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form1 = rawRow1100 := by decide +kernel

def row1100 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

theorem rowCheck1100 : row1100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1100 := by decide +kernel

theorem rowEval1100 (x : Key → ℝ) : Integer.Sparse.eval row1100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1100, Integer.Sparse.eval_collectBalanced, rawRowCheck1100]

def rawRow1101 : Integer.Sparse Key := [(key1475, -6), (key1404, 2), (key1404, 2), (key1432, 2), (key1906, 6), (key1404, -2), (key1404, -2), (key1581, -2), (key1906, -2), (key1906, -2), (key1923, -2), (key1475, 2), (key1475, 2), (key1686, 2)]

theorem rawRowCheck1101 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form1 = rawRow1101 := by decide +kernel

def row1101 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

theorem rowCheck1101 : row1101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1101 := by decide +kernel

theorem rowEval1101 (x : Key → ℝ) : Integer.Sparse.eval row1101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1101, Integer.Sparse.eval_collectBalanced, rawRowCheck1101]

def rawRow1102 : Integer.Sparse Key := [(key1475, -6), (key1404, 2), (key1432, 2), (key1404, 2), (key1906, 6), (key1404, -2), (key1581, -2), (key1404, -2), (key1906, -2), (key1923, -2), (key1906, -2), (key1475, 2), (key1686, 2), (key1475, 2)]

theorem rawRowCheck1102 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form1 = rawRow1102 := by decide +kernel

def row1102 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

theorem rowCheck1102 : row1102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1102 := by decide +kernel

theorem rowEval1102 (x : Key → ℝ) : Integer.Sparse.eval row1102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1102, Integer.Sparse.eval_collectBalanced, rawRowCheck1102]

def rawRow1103 : Integer.Sparse Key := [(key1475, -6), (key1432, 2), (key1404, 2), (key1404, 2), (key1906, 6), (key1581, -2), (key1404, -2), (key1404, -2), (key1923, -2), (key1906, -2), (key1906, -2), (key1686, 2), (key1475, 2), (key1475, 2)]

theorem rawRowCheck1103 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form1 = rawRow1103 := by decide +kernel

def row1103 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

theorem rowCheck1103 : row1103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1103 := by decide +kernel

theorem rowEval1103 (x : Key → ℝ) : Integer.Sparse.eval row1103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1103, Integer.Sparse.eval_collectBalanced, rawRowCheck1103]

def rawRow1104 : Integer.Sparse Key := [(key1581, -6), (key1581, 2), (key1581, 2), (key1686, 2), (key1432, 6), (key1432, -2), (key1432, -2), (key1923, -2), (key1404, -2), (key1404, -2), (key1475, -2), (key1404, 2), (key1404, 2), (key1906, 2)]

theorem rawRowCheck1104 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form1 = rawRow1104 := by decide +kernel

def row1104 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

theorem rowCheck1104 : row1104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1104 := by decide +kernel

theorem rowEval1104 (x : Key → ℝ) : Integer.Sparse.eval row1104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1104, Integer.Sparse.eval_collectBalanced, rawRowCheck1104]

def rawRow1105 : Integer.Sparse Key := [(key1581, -6), (key1581, 2), (key1686, 2), (key1581, 2), (key1432, 6), (key1432, -2), (key1923, -2), (key1432, -2), (key1404, -2), (key1475, -2), (key1404, -2), (key1404, 2), (key1906, 2), (key1404, 2)]

theorem rawRowCheck1105 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form1 = rawRow1105 := by decide +kernel

def row1105 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

theorem rowCheck1105 : row1105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1105 := by decide +kernel

theorem rowEval1105 (x : Key → ℝ) : Integer.Sparse.eval row1105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1105, Integer.Sparse.eval_collectBalanced, rawRowCheck1105]

def rawRow1106 : Integer.Sparse Key := [(key1581, -6), (key1686, 2), (key1581, 2), (key1581, 2), (key1432, 6), (key1923, -2), (key1432, -2), (key1432, -2), (key1475, -2), (key1404, -2), (key1404, -2), (key1906, 2), (key1404, 2), (key1404, 2)]

theorem rawRowCheck1106 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form1 = rawRow1106 := by decide +kernel

def row1106 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

theorem rowCheck1106 : row1106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1106 := by decide +kernel

theorem rowEval1106 (x : Key → ℝ) : Integer.Sparse.eval row1106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1106, Integer.Sparse.eval_collectBalanced, rawRowCheck1106]

def rawRow1107 : Integer.Sparse Key := [(key1686, -6), (key1581, 2), (key1581, 2), (key1581, 2), (key1923, 6), (key1432, -2), (key1432, -2), (key1432, -2), (key1906, -2), (key1906, -2), (key1906, -2), (key1475, 2), (key1475, 2), (key1475, 2)]

theorem rawRowCheck1107 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form1 = rawRow1107 := by decide +kernel

def row1107 : Integer.Sparse Key := [(key1432, -6), (key1475, 6), (key1581, 6), (key1686, -6), (key1906, -6), (key1923, 6)]

theorem rowCheck1107 : row1107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1107 := by decide +kernel

theorem rowEval1107 (x : Key → ℝ) : Integer.Sparse.eval row1107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1107, Integer.Sparse.eval_collectBalanced, rawRowCheck1107]

def rawRow1108 : Integer.Sparse Key := [(key1906, -6), (key1906, 2), (key1906, 2), (key1923, 2), (key1475, 6), (key1475, -2), (key1475, -2), (key1686, -2), (key1404, -2), (key1404, -2), (key1432, -2), (key1404, 2), (key1404, 2), (key1581, 2)]

theorem rawRowCheck1108 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form1 = rawRow1108 := by decide +kernel

def row1108 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

theorem rowCheck1108 : row1108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1108 := by decide +kernel

theorem rowEval1108 (x : Key → ℝ) : Integer.Sparse.eval row1108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1108, Integer.Sparse.eval_collectBalanced, rawRowCheck1108]

def rawRow1109 : Integer.Sparse Key := [(key1906, -6), (key1906, 2), (key1923, 2), (key1906, 2), (key1475, 6), (key1475, -2), (key1686, -2), (key1475, -2), (key1404, -2), (key1432, -2), (key1404, -2), (key1404, 2), (key1581, 2), (key1404, 2)]

theorem rawRowCheck1109 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form1 = rawRow1109 := by decide +kernel

def row1109 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

theorem rowCheck1109 : row1109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1109 := by decide +kernel

theorem rowEval1109 (x : Key → ℝ) : Integer.Sparse.eval row1109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1109, Integer.Sparse.eval_collectBalanced, rawRowCheck1109]

def rawRow1110 : Integer.Sparse Key := [(key1906, -6), (key1923, 2), (key1906, 2), (key1906, 2), (key1475, 6), (key1686, -2), (key1475, -2), (key1475, -2), (key1432, -2), (key1404, -2), (key1404, -2), (key1581, 2), (key1404, 2), (key1404, 2)]

theorem rawRowCheck1110 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form1 = rawRow1110 := by decide +kernel

def row1110 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

theorem rowCheck1110 : row1110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1110 := by decide +kernel

theorem rowEval1110 (x : Key → ℝ) : Integer.Sparse.eval row1110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1110, Integer.Sparse.eval_collectBalanced, rawRowCheck1110]

def rawRow1111 : Integer.Sparse Key := [(key1923, -6), (key1906, 2), (key1906, 2), (key1906, 2), (key1686, 6), (key1475, -2), (key1475, -2), (key1475, -2), (key1581, -2), (key1581, -2), (key1581, -2), (key1432, 2), (key1432, 2), (key1432, 2)]

theorem rawRowCheck1111 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form1 = rawRow1111 := by decide +kernel

def row1111 : Integer.Sparse Key := [(key1432, 6), (key1475, -6), (key1581, -6), (key1686, 6), (key1906, 6), (key1923, -6)]

theorem rowCheck1111 : row1111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1111 := by decide +kernel

theorem rowEval1111 (x : Key → ℝ) : Integer.Sparse.eval row1111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1111, Integer.Sparse.eval_collectBalanced, rawRowCheck1111]

def rawRow1112 : Integer.Sparse Key := [(key2710, -2), (key2717, -2), (key2717, -2), (key2679, 1), (key2691, 1), (key2679, 1), (key2755, 1), (key2691, 1), (key2755, 1), (key2813, 2), (key2820, 2), (key2820, 2), (key2679, -1), (key2691, -1), (key3047, -1), (key3115, -1), (key3058, -1), (key3115, -1), (key3096, -1), (key3113, -1), (key3096, -1), (key3142, -1), (key3113, -1), (key3142, -1), (key3061, 1), (key3075, 1), (key3061, 1), (key3143, 1), (key3075, 1), (key3143, 1)]

theorem rawRowCheck1112 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form2 = rawRow1112 := by decide +kernel

def row1112 : Integer.Sparse Key := [(key2679, 1), (key2691, 1), (key2710, -2), (key2717, -4), (key2755, 2), (key2813, 2), (key2820, 4), (key3047, -1), (key3058, -1), (key3061, 2), (key3075, 2), (key3096, -2), (key3113, -2), (key3115, -2), (key3142, -2), (key3143, 2)]

theorem rowCheck1112 : row1112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1112 := by decide +kernel

theorem rowEval1112 (x : Key → ℝ) : Integer.Sparse.eval row1112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1112, Integer.Sparse.eval_collectBalanced, rawRowCheck1112]

def rawRow1113 : Integer.Sparse Key := [(key2717, -2), (key2710, -2), (key2717, -2), (key2691, 1), (key2679, 1), (key2755, 1), (key2679, 1), (key2755, 1), (key2691, 1), (key2820, 2), (key2813, 2), (key2820, 2), (key2691, -1), (key2679, -1), (key3115, -1), (key3047, -1), (key3115, -1), (key3058, -1), (key3113, -1), (key3096, -1), (key3142, -1), (key3096, -1), (key3142, -1), (key3113, -1), (key3075, 1), (key3061, 1), (key3143, 1), (key3061, 1), (key3143, 1), (key3075, 1)]

theorem rawRowCheck1113 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form2 = rawRow1113 := by decide +kernel

def row1113 : Integer.Sparse Key := [(key2679, 1), (key2691, 1), (key2710, -2), (key2717, -4), (key2755, 2), (key2813, 2), (key2820, 4), (key3047, -1), (key3058, -1), (key3061, 2), (key3075, 2), (key3096, -2), (key3113, -2), (key3115, -2), (key3142, -2), (key3143, 2)]

theorem rowCheck1113 : row1113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1113 := by decide +kernel

theorem rowEval1113 (x : Key → ℝ) : Integer.Sparse.eval row1113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1113, Integer.Sparse.eval_collectBalanced, rawRowCheck1113]

def rawRow1114 : Integer.Sparse Key := [(key2717, -2), (key2717, -2), (key2710, -2), (key2755, 1), (key2755, 1), (key2691, 1), (key2691, 1), (key2679, 1), (key2679, 1), (key2820, 2), (key2820, 2), (key2813, 2), (key3014, -1), (key3014, -1), (key2691, -1), (key2691, -1), (key2679, -1), (key3047, -1), (key3142, -1), (key3142, -1), (key3113, -1), (key3113, -1), (key3096, -1), (key3096, -1), (key3143, 1), (key3143, 1), (key3075, 1), (key3075, 1), (key3061, 1), (key3061, 1)]

theorem rawRowCheck1114 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form2 = rawRow1114 := by decide +kernel

def row1114 : Integer.Sparse Key := [(key2679, 1), (key2710, -2), (key2717, -4), (key2755, 2), (key2813, 2), (key2820, 4), (key3014, -2), (key3047, -1), (key3061, 2), (key3075, 2), (key3096, -2), (key3113, -2), (key3142, -2), (key3143, 2)]

theorem rowCheck1114 : row1114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1114 := by decide +kernel

theorem rowEval1114 (x : Key → ℝ) : Integer.Sparse.eval row1114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1114, Integer.Sparse.eval_collectBalanced, rawRowCheck1114]

def rawRow1115 : Integer.Sparse Key := [(key2754, -2), (key2755, -2), (key2755, -2), (key2684, 1), (key2691, 1), (key2684, 1), (key2717, 1), (key2691, 1), (key2717, 1), (key3013, 2), (key3014, 2), (key3014, 2), (key2684, -1), (key2691, -1), (key2684, -1), (key2820, -1), (key2691, -1), (key2820, -1), (key3105, -1), (key3115, -1), (key3105, -1), (key3143, -1), (key3115, -1), (key3143, -1), (key3068, 1), (key3076, 1), (key3068, 1), (key3142, 1), (key3076, 1), (key3142, 1)]

theorem rawRowCheck1115 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form2 = rawRow1115 := by decide +kernel

def row1115 : Integer.Sparse Key := [(key2717, 2), (key2754, -2), (key2755, -4), (key2820, -2), (key3013, 2), (key3014, 4), (key3068, 2), (key3076, 2), (key3105, -2), (key3115, -2), (key3142, 2), (key3143, -2)]

theorem rowCheck1115 : row1115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1115 := by decide +kernel

theorem rowEval1115 (x : Key → ℝ) : Integer.Sparse.eval row1115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1115, Integer.Sparse.eval_collectBalanced, rawRowCheck1115]

def rawRow1116 : Integer.Sparse Key := [(key2755, -2), (key2754, -2), (key2755, -2), (key2691, 1), (key2684, 1), (key2717, 1), (key2684, 1), (key2717, 1), (key2691, 1), (key3014, 2), (key3013, 2), (key3014, 2), (key2691, -1), (key2684, -1), (key2820, -1), (key2684, -1), (key2820, -1), (key2691, -1), (key3115, -1), (key3105, -1), (key3143, -1), (key3105, -1), (key3143, -1), (key3115, -1), (key3076, 1), (key3068, 1), (key3142, 1), (key3068, 1), (key3142, 1), (key3076, 1)]

theorem rawRowCheck1116 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form2 = rawRow1116 := by decide +kernel

def row1116 : Integer.Sparse Key := [(key2717, 2), (key2754, -2), (key2755, -4), (key2820, -2), (key3013, 2), (key3014, 4), (key3068, 2), (key3076, 2), (key3105, -2), (key3115, -2), (key3142, 2), (key3143, -2)]

theorem rowCheck1116 : row1116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1116 := by decide +kernel

theorem rowEval1116 (x : Key → ℝ) : Integer.Sparse.eval row1116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1116, Integer.Sparse.eval_collectBalanced, rawRowCheck1116]

def rawRow1117 : Integer.Sparse Key := [(key2755, -2), (key2755, -2), (key2754, -2), (key2717, 1), (key2717, 1), (key2691, 1), (key2691, 1), (key2684, 1), (key2684, 1), (key3014, 2), (key3014, 2), (key3013, 2), (key2820, -1), (key2820, -1), (key2691, -1), (key2691, -1), (key2684, -1), (key2684, -1), (key3143, -1), (key3143, -1), (key3115, -1), (key3115, -1), (key3105, -1), (key3105, -1), (key3142, 1), (key3142, 1), (key3076, 1), (key3076, 1), (key3068, 1), (key3068, 1)]

theorem rawRowCheck1117 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form2 = rawRow1117 := by decide +kernel

def row1117 : Integer.Sparse Key := [(key2717, 2), (key2754, -2), (key2755, -4), (key2820, -2), (key3013, 2), (key3014, 4), (key3068, 2), (key3076, 2), (key3105, -2), (key3115, -2), (key3142, 2), (key3143, -2)]

theorem rowCheck1117 : row1117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1117 := by decide +kernel

theorem rowEval1117 (x : Key → ℝ) : Integer.Sparse.eval row1117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1117, Integer.Sparse.eval_collectBalanced, rawRowCheck1117]

def rawRow1118 : Integer.Sparse Key := [(key2813, -2), (key2820, -2), (key2820, -2), (key2813, 1), (key2820, 1), (key2813, 1), (key2921, 1), (key2820, 1), (key2921, 1), (key2710, 2), (key2717, 2), (key2717, 2), (key2710, -1), (key2717, -1), (key2710, -1), (key3024, -1), (key2717, -1), (key3024, -1), (key2679, -1), (key2691, -1), (key2679, -1), (key2755, -1), (key2691, -1), (key2755, -1), (key2679, 1), (key2691, 1), (key3047, 1), (key3115, 1), (key3058, 1), (key3115, 1)]

theorem rawRowCheck1118 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form2 = rawRow1118 := by decide +kernel

def row1118 : Integer.Sparse Key := [(key2679, -1), (key2691, -1), (key2717, 2), (key2755, -2), (key2820, -2), (key2921, 2), (key3024, -2), (key3047, 1), (key3058, 1), (key3115, 2)]

theorem rowCheck1118 : row1118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1118 := by decide +kernel

theorem rowEval1118 (x : Key → ℝ) : Integer.Sparse.eval row1118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1118, Integer.Sparse.eval_collectBalanced, rawRowCheck1118]

def rawRow1119 : Integer.Sparse Key := [(key2820, -2), (key2813, -2), (key2820, -2), (key2820, 1), (key2813, 1), (key2921, 1), (key2813, 1), (key2921, 1), (key2820, 1), (key2717, 2), (key2710, 2), (key2717, 2), (key2717, -1), (key2710, -1), (key3024, -1), (key2710, -1), (key3024, -1), (key2717, -1), (key2691, -1), (key2679, -1), (key2755, -1), (key2679, -1), (key2755, -1), (key2691, -1), (key2691, 1), (key2679, 1), (key3115, 1), (key3047, 1), (key3115, 1), (key3058, 1)]

theorem rawRowCheck1119 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form2 = rawRow1119 := by decide +kernel

def row1119 : Integer.Sparse Key := [(key2679, -1), (key2691, -1), (key2717, 2), (key2755, -2), (key2820, -2), (key2921, 2), (key3024, -2), (key3047, 1), (key3058, 1), (key3115, 2)]

theorem rowCheck1119 : row1119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1119 := by decide +kernel

theorem rowEval1119 (x : Key → ℝ) : Integer.Sparse.eval row1119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1119, Integer.Sparse.eval_collectBalanced, rawRowCheck1119]

end MUB6.Certificate.GramRows

end OAI
