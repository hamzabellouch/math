import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14592 : Integer.Sparse Key := [(key2645, -1), (key2645, -1), (key2892, -1), (key2892, -1), (key2902, -1), (key2902, -1), (key2651, 2), (key2895, 2), (key2895, 2), (key2611, -1), (key2611, -1), (key2804, -1), (key2804, -1), (key2825, -1), (key2825, -1), (key2627, 2), (key2627, 2), (key2781, 2), (key2781, 2), (key2866, 2), (key2866, 2), (key2636, -1), (key2636, -1), (key2790, -1), (key2790, -1), (key2856, -1), (key2856, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1)]

theorem rawRowCheck14592 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form10 = rawRow14592 := by decide +kernel

def row14592 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2781, 4), (key2790, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2866, 4), (key2892, -2), (key2895, 4), (key2902, -2)]

theorem rowCheck14592 : row14592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14592 := by decide +kernel

theorem rowEval14592 (x : Key → ℝ) : Integer.Sparse.eval row14592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14592, Integer.Sparse.eval_collectBalanced, rawRowCheck14592]

def rawRow14593 : Integer.Sparse Key := [(key2892, -1), (key2902, -1), (key2645, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2895, 2), (key2651, 2), (key2895, 2), (key2804, -1), (key2825, -1), (key2611, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2781, 2), (key2866, 2), (key2627, 2), (key2866, 2), (key2627, 2), (key2781, 2), (key2790, -1), (key2856, -1), (key2636, -1), (key2856, -1), (key2636, -1), (key2790, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1)]

theorem rawRowCheck14593 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form10 = rawRow14593 := by decide +kernel

def row14593 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2781, 4), (key2790, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2866, 4), (key2892, -2), (key2895, 4), (key2902, -2)]

theorem rowCheck14593 : row14593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14593 := by decide +kernel

theorem rowEval14593 (x : Key → ℝ) : Integer.Sparse.eval row14593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14593, Integer.Sparse.eval_collectBalanced, rawRowCheck14593]

def rawRow14594 : Integer.Sparse Key := [(key2902, -1), (key2892, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2645, -1), (key2895, 2), (key2895, 2), (key2651, 2), (key2825, -1), (key2804, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2611, -1), (key2866, 2), (key2781, 2), (key2866, 2), (key2627, 2), (key2781, 2), (key2627, 2), (key2856, -1), (key2790, -1), (key2856, -1), (key2636, -1), (key2790, -1), (key2636, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1)]

theorem rawRowCheck14594 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form10 = rawRow14594 := by decide +kernel

def row14594 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2781, 4), (key2790, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2866, 4), (key2892, -2), (key2895, 4), (key2902, -2)]

theorem rowCheck14594 : row14594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14594 := by decide +kernel

theorem rowEval14594 (x : Key → ℝ) : Integer.Sparse.eval row14594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14594, Integer.Sparse.eval_collectBalanced, rawRowCheck14594]

def rawRow14595 : Integer.Sparse Key := [(key2645, -1), (key2651, -1), (key2734, -1), (key2895, -1), (key2745, -1), (key2902, -1), (key2645, 2), (key2734, 2), (key2892, 2), (key2627, -1), (key2636, -1), (key2701, -1), (key2856, -1), (key2722, -1), (key2866, -1), (key2611, 2), (key2636, 2), (key2666, 2), (key2790, 2), (key2722, 2), (key2825, 2), (key2611, -1), (key2627, -1), (key2666, -1), (key2781, -1), (key2701, -1), (key2804, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1)]

theorem rawRowCheck14595 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form10 = rawRow14595 := by decide +kernel

def row14595 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

theorem rowCheck14595 : row14595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14595 := by decide +kernel

theorem rowEval14595 (x : Key → ℝ) : Integer.Sparse.eval row14595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14595, Integer.Sparse.eval_collectBalanced, rawRowCheck14595]

def rawRow14596 : Integer.Sparse Key := [(key2651, -1), (key2645, -1), (key2895, -1), (key2734, -1), (key2902, -1), (key2745, -1), (key2645, 2), (key2892, 2), (key2734, 2), (key2636, -1), (key2627, -1), (key2856, -1), (key2701, -1), (key2866, -1), (key2722, -1), (key2636, 2), (key2611, 2), (key2790, 2), (key2666, 2), (key2825, 2), (key2722, 2), (key2627, -1), (key2611, -1), (key2781, -1), (key2666, -1), (key2804, -1), (key2701, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1)]

theorem rawRowCheck14596 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form10 = rawRow14596 := by decide +kernel

def row14596 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

theorem rowCheck14596 : row14596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14596 := by decide +kernel

theorem rowEval14596 (x : Key → ℝ) : Integer.Sparse.eval row14596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck14596, Integer.Sparse.eval_collectBalanced, rawRowCheck14596]

def rawRow14597 : Integer.Sparse Key := [(key2734, -1), (key2745, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2734, 2), (key2645, 2), (key2892, 2), (key2701, -1), (key2722, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2666, 2), (key2722, 2), (key2611, 2), (key2825, 2), (key2636, 2), (key2790, 2), (key2666, -1), (key2701, -1), (key2611, -1), (key2804, -1), (key2627, -1), (key2781, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1)]

theorem rawRowCheck14597 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form10 = rawRow14597 := by decide +kernel

def row14597 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

theorem rowCheck14597 : row14597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14597 := by decide +kernel

theorem rowEval14597 (x : Key → ℝ) : Integer.Sparse.eval row14597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14597, Integer.Sparse.eval_collectBalanced, rawRowCheck14597]

def rawRow14598 : Integer.Sparse Key := [(key2745, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2895, -1), (key2651, -1), (key2734, 2), (key2892, 2), (key2645, 2), (key2722, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2856, -1), (key2636, -1), (key2722, 2), (key2666, 2), (key2825, 2), (key2611, 2), (key2790, 2), (key2636, 2), (key2701, -1), (key2666, -1), (key2804, -1), (key2611, -1), (key2781, -1), (key2627, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1)]

theorem rawRowCheck14598 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form10 = rawRow14598 := by decide +kernel

def row14598 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

theorem rowCheck14598 : row14598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14598 := by decide +kernel

theorem rowEval14598 (x : Key → ℝ) : Integer.Sparse.eval row14598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14598, Integer.Sparse.eval_collectBalanced, rawRowCheck14598]

def rawRow14599 : Integer.Sparse Key := [(key2895, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2645, -1), (key2734, -1), (key2892, 2), (key2645, 2), (key2734, 2), (key2856, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2627, -1), (key2701, -1), (key2790, 2), (key2825, 2), (key2636, 2), (key2722, 2), (key2611, 2), (key2666, 2), (key2781, -1), (key2804, -1), (key2627, -1), (key2701, -1), (key2611, -1), (key2666, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1)]

theorem rawRowCheck14599 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form10 = rawRow14599 := by decide +kernel

def row14599 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

theorem rowCheck14599 : row14599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14599 := by decide +kernel

theorem rowEval14599 (x : Key → ℝ) : Integer.Sparse.eval row14599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck14599, Integer.Sparse.eval_collectBalanced, rawRowCheck14599]

def rawRow14600 : Integer.Sparse Key := [(key2902, -1), (key2895, -1), (key2745, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2892, 2), (key2734, 2), (key2645, 2), (key2866, -1), (key2856, -1), (key2722, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2825, 2), (key2790, 2), (key2722, 2), (key2636, 2), (key2666, 2), (key2611, 2), (key2804, -1), (key2781, -1), (key2701, -1), (key2627, -1), (key2666, -1), (key2611, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1)]

theorem rawRowCheck14600 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form10 = rawRow14600 := by decide +kernel

def row14600 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

theorem rowCheck14600 : row14600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14600 := by decide +kernel

theorem rowEval14600 (x : Key → ℝ) : Integer.Sparse.eval row14600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14600, Integer.Sparse.eval_collectBalanced, rawRowCheck14600]

def rawRow14601 : Integer.Sparse Key := [(key1700, 4), (key1700, 4), (key1756, 4), (key1700, -2), (key1706, -2), (key1700, -2), (key1756, -2), (key1706, -2), (key1756, -2), (key1851, -2), (key1855, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1886, -2), (key1855, 4), (key1855, 4), (key1886, 4)]

theorem rawRowCheck14601 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form0 = rawRow14601 := by decide +kernel

def row14601 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck14601 : row14601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14601 := by decide +kernel

theorem rowEval14601 (x : Key → ℝ) : Integer.Sparse.eval row14601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14601, Integer.Sparse.eval_collectBalanced, rawRowCheck14601]

def rawRow14602 : Integer.Sparse Key := [(key1700, 4), (key1756, 4), (key1700, 4), (key1706, -2), (key1700, -2), (key1756, -2), (key1700, -2), (key1756, -2), (key1706, -2), (key1855, -2), (key1851, -2), (key1886, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1855, 4), (key1886, 4), (key1855, 4)]

theorem rawRowCheck14602 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form0 = rawRow14602 := by decide +kernel

def row14602 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck14602 : row14602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14602 := by decide +kernel

theorem rowEval14602 (x : Key → ℝ) : Integer.Sparse.eval row14602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14602, Integer.Sparse.eval_collectBalanced, rawRowCheck14602]

def rawRow14603 : Integer.Sparse Key := [(key1756, 4), (key1700, 4), (key1700, 4), (key1756, -2), (key1756, -2), (key1706, -2), (key1706, -2), (key1700, -2), (key1700, -2), (key1886, -2), (key1886, -2), (key1855, -2), (key1855, -2), (key1851, -2), (key1851, -2), (key1886, 4), (key1855, 4), (key1855, 4)]

theorem rawRowCheck14603 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form0 = rawRow14603 := by decide +kernel

def row14603 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck14603 : row14603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14603 := by decide +kernel

theorem rowEval14603 (x : Key → ℝ) : Integer.Sparse.eval row14603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14603, Integer.Sparse.eval_collectBalanced, rawRowCheck14603]

def rawRow14604 : Integer.Sparse Key := [(key1706, 4), (key1706, 4), (key1706, 4), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1851, 4), (key1851, 4), (key1851, 4)]

theorem rawRowCheck14604 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form0 = rawRow14604 := by decide +kernel

def row14604 : Integer.Sparse Key := [(key1700, -12), (key1706, 12), (key1851, 12), (key1855, -12)]

theorem rowCheck14604 : row14604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14604 := by decide +kernel

theorem rowEval14604 (x : Key → ℝ) : Integer.Sparse.eval row14604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14604, Integer.Sparse.eval_collectBalanced, rawRowCheck14604]

def rawRow14605 : Integer.Sparse Key := [(key1700, 4), (key1700, 4), (key1756, 4), (key1851, -2), (key1855, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1886, -2), (key1700, -2), (key1706, -2), (key1700, -2), (key1756, -2), (key1706, -2), (key1756, -2), (key1855, 4), (key1855, 4), (key1886, 4)]

theorem rawRowCheck14605 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form0 = rawRow14605 := by decide +kernel

def row14605 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck14605 : row14605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14605 := by decide +kernel

theorem rowEval14605 (x : Key → ℝ) : Integer.Sparse.eval row14605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14605, Integer.Sparse.eval_collectBalanced, rawRowCheck14605]

def rawRow14606 : Integer.Sparse Key := [(key1700, 4), (key1756, 4), (key1700, 4), (key1855, -2), (key1851, -2), (key1886, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1706, -2), (key1700, -2), (key1756, -2), (key1700, -2), (key1756, -2), (key1706, -2), (key1855, 4), (key1886, 4), (key1855, 4)]

theorem rawRowCheck14606 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form0 = rawRow14606 := by decide +kernel

def row14606 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck14606 : row14606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14606 := by decide +kernel

theorem rowEval14606 (x : Key → ℝ) : Integer.Sparse.eval row14606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14606, Integer.Sparse.eval_collectBalanced, rawRowCheck14606]

def rawRow14607 : Integer.Sparse Key := [(key1756, 4), (key1700, 4), (key1700, 4), (key1886, -2), (key1886, -2), (key1855, -2), (key1855, -2), (key1851, -2), (key1851, -2), (key1756, -2), (key1756, -2), (key1706, -2), (key1706, -2), (key1700, -2), (key1700, -2), (key1886, 4), (key1855, 4), (key1855, 4)]

theorem rawRowCheck14607 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form0 = rawRow14607 := by decide +kernel

def row14607 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck14607 : row14607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14607 := by decide +kernel

theorem rowEval14607 (x : Key → ℝ) : Integer.Sparse.eval row14607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14607, Integer.Sparse.eval_collectBalanced, rawRowCheck14607]

def rawRow14608 : Integer.Sparse Key := [(key1277, 4), (key1851, 4), (key1886, 4), (key1277, -2), (key1283, -2), (key1700, -2), (key1756, -2), (key1855, -2), (key1886, -2), (key1277, -2), (key1283, -2), (key1700, -2), (key1756, -2), (key1855, -2), (key1886, -2), (key1283, 4), (key1706, 4), (key1756, 4)]

theorem rawRowCheck14608 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form0 = rawRow14608 := by decide +kernel

def row14608 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

theorem rowCheck14608 : row14608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14608 := by decide +kernel

theorem rowEval14608 (x : Key → ℝ) : Integer.Sparse.eval row14608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14608, Integer.Sparse.eval_collectBalanced, rawRowCheck14608]

def rawRow14609 : Integer.Sparse Key := [(key1277, 4), (key1886, 4), (key1851, 4), (key1283, -2), (key1277, -2), (key1756, -2), (key1700, -2), (key1886, -2), (key1855, -2), (key1283, -2), (key1277, -2), (key1756, -2), (key1700, -2), (key1886, -2), (key1855, -2), (key1283, 4), (key1756, 4), (key1706, 4)]

theorem rawRowCheck14609 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form0 = rawRow14609 := by decide +kernel

def row14609 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

theorem rowCheck14609 : row14609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14609 := by decide +kernel

theorem rowEval14609 (x : Key → ℝ) : Integer.Sparse.eval row14609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14609, Integer.Sparse.eval_collectBalanced, rawRowCheck14609]

def rawRow14610 : Integer.Sparse Key := [(key1851, 4), (key1277, 4), (key1886, 4), (key1700, -2), (key1855, -2), (key1277, -2), (key1886, -2), (key1283, -2), (key1756, -2), (key1700, -2), (key1855, -2), (key1277, -2), (key1886, -2), (key1283, -2), (key1756, -2), (key1706, 4), (key1283, 4), (key1756, 4)]

theorem rawRowCheck14610 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form0 = rawRow14610 := by decide +kernel

def row14610 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

theorem rowCheck14610 : row14610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14610 := by decide +kernel

theorem rowEval14610 (x : Key → ℝ) : Integer.Sparse.eval row14610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14610, Integer.Sparse.eval_collectBalanced, rawRowCheck14610]

def rawRow14611 : Integer.Sparse Key := [(key1851, 4), (key1886, 4), (key1277, 4), (key1855, -2), (key1700, -2), (key1886, -2), (key1277, -2), (key1756, -2), (key1283, -2), (key1855, -2), (key1700, -2), (key1886, -2), (key1277, -2), (key1756, -2), (key1283, -2), (key1706, 4), (key1756, 4), (key1283, 4)]

theorem rawRowCheck14611 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form0 = rawRow14611 := by decide +kernel

def row14611 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

theorem rowCheck14611 : row14611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14611 := by decide +kernel

theorem rowEval14611 (x : Key → ℝ) : Integer.Sparse.eval row14611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14611, Integer.Sparse.eval_collectBalanced, rawRowCheck14611]

def rawRow14612 : Integer.Sparse Key := [(key1886, 4), (key1277, 4), (key1851, 4), (key1756, -2), (key1886, -2), (key1283, -2), (key1855, -2), (key1277, -2), (key1700, -2), (key1756, -2), (key1886, -2), (key1283, -2), (key1855, -2), (key1277, -2), (key1700, -2), (key1756, 4), (key1283, 4), (key1706, 4)]

theorem rawRowCheck14612 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form0 = rawRow14612 := by decide +kernel

def row14612 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

theorem rowCheck14612 : row14612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14612 := by decide +kernel

theorem rowEval14612 (x : Key → ℝ) : Integer.Sparse.eval row14612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14612, Integer.Sparse.eval_collectBalanced, rawRowCheck14612]

def rawRow14613 : Integer.Sparse Key := [(key1886, 4), (key1851, 4), (key1277, 4), (key1886, -2), (key1756, -2), (key1855, -2), (key1283, -2), (key1700, -2), (key1277, -2), (key1886, -2), (key1756, -2), (key1855, -2), (key1283, -2), (key1700, -2), (key1277, -2), (key1756, 4), (key1706, 4), (key1283, 4)]

theorem rawRowCheck14613 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form0 = rawRow14613 := by decide +kernel

def row14613 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

theorem rowCheck14613 : row14613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14613 := by decide +kernel

theorem rowEval14613 (x : Key → ℝ) : Integer.Sparse.eval row14613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14613, Integer.Sparse.eval_collectBalanced, rawRowCheck14613]

def rawRow14614 : Integer.Sparse Key := [(key1283, 4), (key1855, 4), (key1855, 4), (key1277, -2), (key1277, -2), (key1700, -2), (key1700, -2), (key1851, -2), (key1851, -2), (key1283, -2), (key1283, -2), (key1706, -2), (key1706, -2), (key1855, -2), (key1855, -2), (key1277, 4), (key1700, 4), (key1700, 4)]

theorem rawRowCheck14614 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form0 = rawRow14614 := by decide +kernel

def row14614 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck14614 : row14614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14614 := by decide +kernel

theorem rowEval14614 (x : Key → ℝ) : Integer.Sparse.eval row14614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14614, Integer.Sparse.eval_collectBalanced, rawRowCheck14614]

def rawRow14615 : Integer.Sparse Key := [(key1855, 4), (key1283, 4), (key1855, 4), (key1700, -2), (key1851, -2), (key1277, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1706, -2), (key1855, -2), (key1283, -2), (key1855, -2), (key1283, -2), (key1706, -2), (key1700, 4), (key1277, 4), (key1700, 4)]

theorem rawRowCheck14615 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form0 = rawRow14615 := by decide +kernel

def row14615 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck14615 : row14615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14615 := by decide +kernel

theorem rowEval14615 (x : Key → ℝ) : Integer.Sparse.eval row14615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14615, Integer.Sparse.eval_collectBalanced, rawRowCheck14615]

def rawRow14616 : Integer.Sparse Key := [(key1855, 4), (key1855, 4), (key1283, 4), (key1851, -2), (key1700, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1277, -2), (key1855, -2), (key1706, -2), (key1855, -2), (key1283, -2), (key1706, -2), (key1283, -2), (key1700, 4), (key1700, 4), (key1277, 4)]

theorem rawRowCheck14616 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form0 = rawRow14616 := by decide +kernel

def row14616 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck14616 : row14616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14616 := by decide +kernel

theorem rowEval14616 (x : Key → ℝ) : Integer.Sparse.eval row14616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14616, Integer.Sparse.eval_collectBalanced, rawRowCheck14616]

def rawRow14617 : Integer.Sparse Key := [(key1706, 4), (key1706, 4), (key1706, 4), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1851, 4), (key1851, 4), (key1851, 4)]

theorem rawRowCheck14617 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form0 = rawRow14617 := by decide +kernel

def row14617 : Integer.Sparse Key := [(key1700, -12), (key1706, 12), (key1851, 12), (key1855, -12)]

theorem rowCheck14617 : row14617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14617 := by decide +kernel

theorem rowEval14617 (x : Key → ℝ) : Integer.Sparse.eval row14617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14617, Integer.Sparse.eval_collectBalanced, rawRowCheck14617]

def rawRow14618 : Integer.Sparse Key := [(key1283, 4), (key1855, 4), (key1855, 4), (key1283, -2), (key1283, -2), (key1706, -2), (key1706, -2), (key1855, -2), (key1855, -2), (key1277, -2), (key1277, -2), (key1700, -2), (key1700, -2), (key1851, -2), (key1851, -2), (key1277, 4), (key1700, 4), (key1700, 4)]

theorem rawRowCheck14618 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form0 = rawRow14618 := by decide +kernel

def row14618 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck14618 : row14618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14618 := by decide +kernel

theorem rowEval14618 (x : Key → ℝ) : Integer.Sparse.eval row14618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14618, Integer.Sparse.eval_collectBalanced, rawRowCheck14618]

def rawRow14619 : Integer.Sparse Key := [(key1855, 4), (key1283, 4), (key1855, 4), (key1706, -2), (key1855, -2), (key1283, -2), (key1855, -2), (key1283, -2), (key1706, -2), (key1700, -2), (key1851, -2), (key1277, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1700, 4), (key1277, 4), (key1700, 4)]

theorem rawRowCheck14619 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form0 = rawRow14619 := by decide +kernel

def row14619 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck14619 : row14619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14619 := by decide +kernel

theorem rowEval14619 (x : Key → ℝ) : Integer.Sparse.eval row14619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14619, Integer.Sparse.eval_collectBalanced, rawRowCheck14619]

def rawRow14620 : Integer.Sparse Key := [(key1855, 4), (key1855, 4), (key1283, 4), (key1855, -2), (key1706, -2), (key1855, -2), (key1283, -2), (key1706, -2), (key1283, -2), (key1851, -2), (key1700, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1277, -2), (key1700, 4), (key1700, 4), (key1277, 4)]

theorem rawRowCheck14620 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form0 = rawRow14620 := by decide +kernel

def row14620 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck14620 : row14620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14620 := by decide +kernel

theorem rowEval14620 (x : Key → ℝ) : Integer.Sparse.eval row14620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14620, Integer.Sparse.eval_collectBalanced, rawRowCheck14620]

def rawRow14621 : Integer.Sparse Key := [(key220, -2), (key225, -2), (key225, -2), (key225, 6), (key492, -2), (key497, -2), (key497, -2), (key492, 2), (key497, 2), (key492, 2), (key551, 2), (key497, 2), (key551, 2), (key497, -2), (key497, -2), (key551, -2), (key664, 6), (key664, -2), (key664, -2), (key681, -2)]

theorem rawRowCheck14621 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form1 = rawRow14621 := by decide +kernel

def row14621 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

theorem rowCheck14621 : row14621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14621 := by decide +kernel

theorem rowEval14621 (x : Key → ℝ) : Integer.Sparse.eval row14621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14621, Integer.Sparse.eval_collectBalanced, rawRowCheck14621]

def rawRow14622 : Integer.Sparse Key := [(key225, -2), (key220, -2), (key225, -2), (key225, 6), (key497, -2), (key492, -2), (key497, -2), (key497, 2), (key492, 2), (key551, 2), (key492, 2), (key551, 2), (key497, 2), (key497, -2), (key551, -2), (key497, -2), (key664, 6), (key664, -2), (key681, -2), (key664, -2)]

theorem rawRowCheck14622 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form1 = rawRow14622 := by decide +kernel

def row14622 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

theorem rowCheck14622 : row14622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14622 := by decide +kernel

theorem rowEval14622 (x : Key → ℝ) : Integer.Sparse.eval row14622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14622, Integer.Sparse.eval_collectBalanced, rawRowCheck14622]

def rawRow14623 : Integer.Sparse Key := [(key225, -2), (key225, -2), (key220, -2), (key225, 6), (key497, -2), (key497, -2), (key492, -2), (key551, 2), (key551, 2), (key497, 2), (key497, 2), (key492, 2), (key492, 2), (key551, -2), (key497, -2), (key497, -2), (key664, 6), (key681, -2), (key664, -2), (key664, -2)]

theorem rawRowCheck14623 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form1 = rawRow14623 := by decide +kernel

def row14623 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

theorem rowCheck14623 : row14623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14623 := by decide +kernel

theorem rowEval14623 (x : Key → ℝ) : Integer.Sparse.eval row14623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14623, Integer.Sparse.eval_collectBalanced, rawRowCheck14623]

def rawRow14624 : Integer.Sparse Key := [(key225, -2), (key225, -2), (key225, -2), (key220, 6), (key551, -2), (key551, -2), (key551, -2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key492, -2), (key492, -2), (key492, -2), (key681, 6), (key664, -2), (key664, -2), (key664, -2)]

theorem rawRowCheck14624 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form1 = rawRow14624 := by decide +kernel

def row14624 : Integer.Sparse Key := [(key220, 6), (key225, -6), (key492, -6), (key497, 12), (key551, -6), (key664, -6), (key681, 6)]

theorem rowCheck14624 : row14624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14624 := by decide +kernel

theorem rowEval14624 (x : Key → ℝ) : Integer.Sparse.eval row14624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14624, Integer.Sparse.eval_collectBalanced, rawRowCheck14624]

def rawRow14625 : Integer.Sparse Key := [(key492, -2), (key497, -2), (key497, -2), (key664, 6), (key220, -2), (key225, -2), (key225, -2), (key492, 2), (key497, 2), (key492, 2), (key551, 2), (key497, 2), (key551, 2), (key664, -2), (key664, -2), (key681, -2), (key225, 6), (key497, -2), (key497, -2), (key551, -2)]

theorem rawRowCheck14625 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form1 = rawRow14625 := by decide +kernel

def row14625 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

theorem rowCheck14625 : row14625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14625 := by decide +kernel

theorem rowEval14625 (x : Key → ℝ) : Integer.Sparse.eval row14625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14625, Integer.Sparse.eval_collectBalanced, rawRowCheck14625]

def rawRow14626 : Integer.Sparse Key := [(key497, -2), (key492, -2), (key497, -2), (key664, 6), (key225, -2), (key220, -2), (key225, -2), (key497, 2), (key492, 2), (key551, 2), (key492, 2), (key551, 2), (key497, 2), (key664, -2), (key681, -2), (key664, -2), (key225, 6), (key497, -2), (key551, -2), (key497, -2)]

theorem rawRowCheck14626 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form1 = rawRow14626 := by decide +kernel

def row14626 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

theorem rowCheck14626 : row14626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14626 := by decide +kernel

theorem rowEval14626 (x : Key → ℝ) : Integer.Sparse.eval row14626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14626, Integer.Sparse.eval_collectBalanced, rawRowCheck14626]

def rawRow14627 : Integer.Sparse Key := [(key497, -2), (key497, -2), (key492, -2), (key664, 6), (key225, -2), (key225, -2), (key220, -2), (key551, 2), (key551, 2), (key497, 2), (key497, 2), (key492, 2), (key492, 2), (key681, -2), (key664, -2), (key664, -2), (key225, 6), (key551, -2), (key497, -2), (key497, -2)]

theorem rawRowCheck14627 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form1 = rawRow14627 := by decide +kernel

def row14627 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

theorem rowCheck14627 : row14627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14627 := by decide +kernel

theorem rowEval14627 (x : Key → ℝ) : Integer.Sparse.eval row14627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14627, Integer.Sparse.eval_collectBalanced, rawRowCheck14627]

def rawRow14628 : Integer.Sparse Key := [(key492, -2), (key497, -2), (key664, -2), (key497, 6), (key492, -2), (key497, -2), (key664, -2), (key220, 2), (key225, 2), (key492, 2), (key551, 2), (key664, 2), (key681, 2), (key225, -2), (key497, -2), (key551, -2), (key497, 6), (key225, -2), (key497, -2), (key551, -2)]

theorem rawRowCheck14628 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form1 = rawRow14628 := by decide +kernel

def row14628 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

theorem rowCheck14628 : row14628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14628 := by decide +kernel

theorem rowEval14628 (x : Key → ℝ) : Integer.Sparse.eval row14628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14628, Integer.Sparse.eval_collectBalanced, rawRowCheck14628]

def rawRow14629 : Integer.Sparse Key := [(key497, -2), (key492, -2), (key664, -2), (key497, 6), (key497, -2), (key492, -2), (key664, -2), (key225, 2), (key220, 2), (key551, 2), (key492, 2), (key681, 2), (key664, 2), (key225, -2), (key551, -2), (key497, -2), (key497, 6), (key225, -2), (key551, -2), (key497, -2)]

theorem rawRowCheck14629 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form1 = rawRow14629 := by decide +kernel

def row14629 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

theorem rowCheck14629 : row14629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14629 := by decide +kernel

theorem rowEval14629 (x : Key → ℝ) : Integer.Sparse.eval row14629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14629, Integer.Sparse.eval_collectBalanced, rawRowCheck14629]

def rawRow14630 : Integer.Sparse Key := [(key492, -2), (key664, -2), (key497, -2), (key497, 6), (key492, -2), (key664, -2), (key497, -2), (key492, 2), (key664, 2), (key220, 2), (key681, 2), (key225, 2), (key551, 2), (key497, -2), (key225, -2), (key551, -2), (key497, 6), (key497, -2), (key225, -2), (key551, -2)]

theorem rawRowCheck14630 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form1 = rawRow14630 := by decide +kernel

def row14630 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

theorem rowCheck14630 : row14630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14630 := by decide +kernel

theorem rowEval14630 (x : Key → ℝ) : Integer.Sparse.eval row14630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14630, Integer.Sparse.eval_collectBalanced, rawRowCheck14630]

def rawRow14631 : Integer.Sparse Key := [(key664, -2), (key492, -2), (key497, -2), (key497, 6), (key664, -2), (key492, -2), (key497, -2), (key664, 2), (key492, 2), (key681, 2), (key220, 2), (key551, 2), (key225, 2), (key497, -2), (key551, -2), (key225, -2), (key497, 6), (key497, -2), (key551, -2), (key225, -2)]

theorem rawRowCheck14631 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form1 = rawRow14631 := by decide +kernel

def row14631 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

theorem rowCheck14631 : row14631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14631 := by decide +kernel

theorem rowEval14631 (x : Key → ℝ) : Integer.Sparse.eval row14631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14631, Integer.Sparse.eval_collectBalanced, rawRowCheck14631]

def rawRow14632 : Integer.Sparse Key := [(key497, -2), (key664, -2), (key492, -2), (key497, 6), (key497, -2), (key664, -2), (key492, -2), (key551, 2), (key681, 2), (key225, 2), (key664, 2), (key220, 2), (key492, 2), (key551, -2), (key225, -2), (key497, -2), (key497, 6), (key551, -2), (key225, -2), (key497, -2)]

theorem rawRowCheck14632 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form1 = rawRow14632 := by decide +kernel

def row14632 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

theorem rowCheck14632 : row14632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14632 := by decide +kernel

theorem rowEval14632 (x : Key → ℝ) : Integer.Sparse.eval row14632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14632, Integer.Sparse.eval_collectBalanced, rawRowCheck14632]

def rawRow14633 : Integer.Sparse Key := [(key664, -2), (key497, -2), (key492, -2), (key497, 6), (key664, -2), (key497, -2), (key492, -2), (key681, 2), (key551, 2), (key664, 2), (key225, 2), (key492, 2), (key220, 2), (key551, -2), (key497, -2), (key225, -2), (key497, 6), (key551, -2), (key497, -2), (key225, -2)]

theorem rawRowCheck14633 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form1 = rawRow14633 := by decide +kernel

def row14633 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

theorem rowCheck14633 : row14633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14633 := by decide +kernel

theorem rowEval14633 (x : Key → ℝ) : Integer.Sparse.eval row14633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14633, Integer.Sparse.eval_collectBalanced, rawRowCheck14633]

def rawRow14634 : Integer.Sparse Key := [(key497, -2), (key497, -2), (key664, -2), (key492, 6), (key551, -2), (key551, -2), (key681, -2), (key225, 2), (key225, 2), (key497, 2), (key497, 2), (key664, 2), (key664, 2), (key220, -2), (key492, -2), (key492, -2), (key551, 6), (key225, -2), (key497, -2), (key497, -2)]

theorem rawRowCheck14634 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form1 = rawRow14634 := by decide +kernel

def row14634 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

theorem rowCheck14634 : row14634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14634 := by decide +kernel

theorem rowEval14634 (x : Key → ℝ) : Integer.Sparse.eval row14634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14634, Integer.Sparse.eval_collectBalanced, rawRowCheck14634]

def rawRow14635 : Integer.Sparse Key := [(key497, -2), (key664, -2), (key497, -2), (key492, 6), (key551, -2), (key681, -2), (key551, -2), (key497, 2), (key664, 2), (key225, 2), (key664, 2), (key225, 2), (key497, 2), (key492, -2), (key220, -2), (key492, -2), (key551, 6), (key497, -2), (key225, -2), (key497, -2)]

theorem rawRowCheck14635 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form1 = rawRow14635 := by decide +kernel

def row14635 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

theorem rowCheck14635 : row14635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14635 := by decide +kernel

theorem rowEval14635 (x : Key → ℝ) : Integer.Sparse.eval row14635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14635, Integer.Sparse.eval_collectBalanced, rawRowCheck14635]

def rawRow14636 : Integer.Sparse Key := [(key664, -2), (key497, -2), (key497, -2), (key492, 6), (key681, -2), (key551, -2), (key551, -2), (key664, 2), (key497, 2), (key664, 2), (key225, 2), (key497, 2), (key225, 2), (key492, -2), (key492, -2), (key220, -2), (key551, 6), (key497, -2), (key497, -2), (key225, -2)]

theorem rawRowCheck14636 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form1 = rawRow14636 := by decide +kernel

def row14636 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

theorem rowCheck14636 : row14636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14636 := by decide +kernel

theorem rowEval14636 (x : Key → ℝ) : Integer.Sparse.eval row14636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14636, Integer.Sparse.eval_collectBalanced, rawRowCheck14636]

def rawRow14637 : Integer.Sparse Key := [(key551, -2), (key551, -2), (key551, -2), (key681, 6), (key225, -2), (key225, -2), (key225, -2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key664, -2), (key664, -2), (key664, -2), (key220, 6), (key492, -2), (key492, -2), (key492, -2)]

theorem rawRowCheck14637 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form1 = rawRow14637 := by decide +kernel

def row14637 : Integer.Sparse Key := [(key220, 6), (key225, -6), (key492, -6), (key497, 12), (key551, -6), (key664, -6), (key681, 6)]

theorem rowCheck14637 : row14637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14637 := by decide +kernel

theorem rowEval14637 (x : Key → ℝ) : Integer.Sparse.eval row14637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14637, Integer.Sparse.eval_collectBalanced, rawRowCheck14637]

def rawRow14638 : Integer.Sparse Key := [(key551, -2), (key551, -2), (key681, -2), (key551, 6), (key497, -2), (key497, -2), (key664, -2), (key225, 2), (key225, 2), (key497, 2), (key497, 2), (key664, 2), (key664, 2), (key225, -2), (key497, -2), (key497, -2), (key492, 6), (key220, -2), (key492, -2), (key492, -2)]

theorem rawRowCheck14638 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form1 = rawRow14638 := by decide +kernel

def row14638 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

theorem rowCheck14638 : row14638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14638 := by decide +kernel

theorem rowEval14638 (x : Key → ℝ) : Integer.Sparse.eval row14638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14638, Integer.Sparse.eval_collectBalanced, rawRowCheck14638]

def rawRow14639 : Integer.Sparse Key := [(key551, -2), (key681, -2), (key551, -2), (key551, 6), (key497, -2), (key664, -2), (key497, -2), (key497, 2), (key664, 2), (key225, 2), (key664, 2), (key225, 2), (key497, 2), (key497, -2), (key225, -2), (key497, -2), (key492, 6), (key492, -2), (key220, -2), (key492, -2)]

theorem rawRowCheck14639 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form1 = rawRow14639 := by decide +kernel

def row14639 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

theorem rowCheck14639 : row14639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14639 := by decide +kernel

theorem rowEval14639 (x : Key → ℝ) : Integer.Sparse.eval row14639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14639, Integer.Sparse.eval_collectBalanced, rawRowCheck14639]

def rawRow14640 : Integer.Sparse Key := [(key681, -2), (key551, -2), (key551, -2), (key551, 6), (key664, -2), (key497, -2), (key497, -2), (key664, 2), (key497, 2), (key664, 2), (key225, 2), (key497, 2), (key225, 2), (key497, -2), (key497, -2), (key225, -2), (key492, 6), (key492, -2), (key492, -2), (key220, -2)]

theorem rawRowCheck14640 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form1 = rawRow14640 := by decide +kernel

def row14640 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

theorem rowCheck14640 : row14640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14640 := by decide +kernel

theorem rowEval14640 (x : Key → ℝ) : Integer.Sparse.eval row14640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14640, Integer.Sparse.eval_collectBalanced, rawRowCheck14640]

def rawRow14641 : Integer.Sparse Key := [(key1273, -2), (key1278, -2), (key1278, -2), (key1278, 6), (key1696, -2), (key1701, -2), (key1701, -2), (key1696, 2), (key1701, 2), (key1696, 2), (key1751, 2), (key1701, 2), (key1751, 2), (key1701, -2), (key1701, -2), (key1751, -2), (key1933, 6), (key1933, -2), (key1933, -2), (key1953, -2)]

theorem rawRowCheck14641 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form2 = rawRow14641 := by decide +kernel

def row14641 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

theorem rowCheck14641 : row14641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14641 := by decide +kernel

theorem rowEval14641 (x : Key → ℝ) : Integer.Sparse.eval row14641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14641, Integer.Sparse.eval_collectBalanced, rawRowCheck14641]

def rawRow14642 : Integer.Sparse Key := [(key1278, -2), (key1273, -2), (key1278, -2), (key1278, 6), (key1701, -2), (key1696, -2), (key1701, -2), (key1701, 2), (key1696, 2), (key1751, 2), (key1696, 2), (key1751, 2), (key1701, 2), (key1701, -2), (key1751, -2), (key1701, -2), (key1933, 6), (key1933, -2), (key1953, -2), (key1933, -2)]

theorem rawRowCheck14642 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form2 = rawRow14642 := by decide +kernel

def row14642 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

theorem rowCheck14642 : row14642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14642 := by decide +kernel

theorem rowEval14642 (x : Key → ℝ) : Integer.Sparse.eval row14642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14642, Integer.Sparse.eval_collectBalanced, rawRowCheck14642]

def rawRow14643 : Integer.Sparse Key := [(key1278, -2), (key1278, -2), (key1273, -2), (key1278, 6), (key1701, -2), (key1701, -2), (key1696, -2), (key1751, 2), (key1751, 2), (key1701, 2), (key1701, 2), (key1696, 2), (key1696, 2), (key1751, -2), (key1701, -2), (key1701, -2), (key1933, 6), (key1953, -2), (key1933, -2), (key1933, -2)]

theorem rawRowCheck14643 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form2 = rawRow14643 := by decide +kernel

def row14643 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

theorem rowCheck14643 : row14643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14643 := by decide +kernel

theorem rowEval14643 (x : Key → ℝ) : Integer.Sparse.eval row14643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14643, Integer.Sparse.eval_collectBalanced, rawRowCheck14643]

def rawRow14644 : Integer.Sparse Key := [(key1278, -2), (key1278, -2), (key1278, -2), (key1273, 6), (key1751, -2), (key1751, -2), (key1751, -2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1696, -2), (key1696, -2), (key1696, -2), (key1953, 6), (key1933, -2), (key1933, -2), (key1933, -2)]

theorem rawRowCheck14644 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form2 = rawRow14644 := by decide +kernel

def row14644 : Integer.Sparse Key := [(key1273, 6), (key1278, -6), (key1696, -6), (key1701, 12), (key1751, -6), (key1933, -6), (key1953, 6)]

theorem rowCheck14644 : row14644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14644 := by decide +kernel

theorem rowEval14644 (x : Key → ℝ) : Integer.Sparse.eval row14644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14644, Integer.Sparse.eval_collectBalanced, rawRowCheck14644]

def rawRow14645 : Integer.Sparse Key := [(key1696, -2), (key1701, -2), (key1701, -2), (key1933, 6), (key1273, -2), (key1278, -2), (key1278, -2), (key1696, 2), (key1701, 2), (key1696, 2), (key1751, 2), (key1701, 2), (key1751, 2), (key1933, -2), (key1933, -2), (key1953, -2), (key1278, 6), (key1701, -2), (key1701, -2), (key1751, -2)]

theorem rawRowCheck14645 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form2 = rawRow14645 := by decide +kernel

def row14645 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

theorem rowCheck14645 : row14645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14645 := by decide +kernel

theorem rowEval14645 (x : Key → ℝ) : Integer.Sparse.eval row14645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14645, Integer.Sparse.eval_collectBalanced, rawRowCheck14645]

def rawRow14646 : Integer.Sparse Key := [(key1701, -2), (key1696, -2), (key1701, -2), (key1933, 6), (key1278, -2), (key1273, -2), (key1278, -2), (key1701, 2), (key1696, 2), (key1751, 2), (key1696, 2), (key1751, 2), (key1701, 2), (key1933, -2), (key1953, -2), (key1933, -2), (key1278, 6), (key1701, -2), (key1751, -2), (key1701, -2)]

theorem rawRowCheck14646 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form2 = rawRow14646 := by decide +kernel

def row14646 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

theorem rowCheck14646 : row14646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14646 := by decide +kernel

theorem rowEval14646 (x : Key → ℝ) : Integer.Sparse.eval row14646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14646, Integer.Sparse.eval_collectBalanced, rawRowCheck14646]

def rawRow14647 : Integer.Sparse Key := [(key1701, -2), (key1701, -2), (key1696, -2), (key1933, 6), (key1278, -2), (key1278, -2), (key1273, -2), (key1751, 2), (key1751, 2), (key1701, 2), (key1701, 2), (key1696, 2), (key1696, 2), (key1953, -2), (key1933, -2), (key1933, -2), (key1278, 6), (key1751, -2), (key1701, -2), (key1701, -2)]

theorem rawRowCheck14647 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form2 = rawRow14647 := by decide +kernel

def row14647 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

theorem rowCheck14647 : row14647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14647 := by decide +kernel

theorem rowEval14647 (x : Key → ℝ) : Integer.Sparse.eval row14647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14647, Integer.Sparse.eval_collectBalanced, rawRowCheck14647]

def rawRow14648 : Integer.Sparse Key := [(key1696, -2), (key1701, -2), (key1933, -2), (key1701, 6), (key1696, -2), (key1701, -2), (key1933, -2), (key1273, 2), (key1278, 2), (key1696, 2), (key1751, 2), (key1933, 2), (key1953, 2), (key1278, -2), (key1701, -2), (key1751, -2), (key1701, 6), (key1278, -2), (key1701, -2), (key1751, -2)]

theorem rawRowCheck14648 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form2 = rawRow14648 := by decide +kernel

def row14648 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

theorem rowCheck14648 : row14648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14648 := by decide +kernel

theorem rowEval14648 (x : Key → ℝ) : Integer.Sparse.eval row14648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14648, Integer.Sparse.eval_collectBalanced, rawRowCheck14648]

def rawRow14649 : Integer.Sparse Key := [(key1701, -2), (key1696, -2), (key1933, -2), (key1701, 6), (key1701, -2), (key1696, -2), (key1933, -2), (key1278, 2), (key1273, 2), (key1751, 2), (key1696, 2), (key1953, 2), (key1933, 2), (key1278, -2), (key1751, -2), (key1701, -2), (key1701, 6), (key1278, -2), (key1751, -2), (key1701, -2)]

theorem rawRowCheck14649 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form2 = rawRow14649 := by decide +kernel

def row14649 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

theorem rowCheck14649 : row14649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14649 := by decide +kernel

theorem rowEval14649 (x : Key → ℝ) : Integer.Sparse.eval row14649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14649, Integer.Sparse.eval_collectBalanced, rawRowCheck14649]

def rawRow14650 : Integer.Sparse Key := [(key1696, -2), (key1933, -2), (key1701, -2), (key1701, 6), (key1696, -2), (key1933, -2), (key1701, -2), (key1696, 2), (key1933, 2), (key1273, 2), (key1953, 2), (key1278, 2), (key1751, 2), (key1701, -2), (key1278, -2), (key1751, -2), (key1701, 6), (key1701, -2), (key1278, -2), (key1751, -2)]

theorem rawRowCheck14650 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form2 = rawRow14650 := by decide +kernel

def row14650 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

theorem rowCheck14650 : row14650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14650 := by decide +kernel

theorem rowEval14650 (x : Key → ℝ) : Integer.Sparse.eval row14650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14650, Integer.Sparse.eval_collectBalanced, rawRowCheck14650]

def rawRow14651 : Integer.Sparse Key := [(key1933, -2), (key1696, -2), (key1701, -2), (key1701, 6), (key1933, -2), (key1696, -2), (key1701, -2), (key1933, 2), (key1696, 2), (key1953, 2), (key1273, 2), (key1751, 2), (key1278, 2), (key1701, -2), (key1751, -2), (key1278, -2), (key1701, 6), (key1701, -2), (key1751, -2), (key1278, -2)]

theorem rawRowCheck14651 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form2 = rawRow14651 := by decide +kernel

def row14651 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

theorem rowCheck14651 : row14651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14651 := by decide +kernel

theorem rowEval14651 (x : Key → ℝ) : Integer.Sparse.eval row14651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14651, Integer.Sparse.eval_collectBalanced, rawRowCheck14651]

def rawRow14652 : Integer.Sparse Key := [(key1701, -2), (key1933, -2), (key1696, -2), (key1701, 6), (key1701, -2), (key1933, -2), (key1696, -2), (key1751, 2), (key1953, 2), (key1278, 2), (key1933, 2), (key1273, 2), (key1696, 2), (key1751, -2), (key1278, -2), (key1701, -2), (key1701, 6), (key1751, -2), (key1278, -2), (key1701, -2)]

theorem rawRowCheck14652 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form2 = rawRow14652 := by decide +kernel

def row14652 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

theorem rowCheck14652 : row14652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14652 := by decide +kernel

theorem rowEval14652 (x : Key → ℝ) : Integer.Sparse.eval row14652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14652, Integer.Sparse.eval_collectBalanced, rawRowCheck14652]

def rawRow14653 : Integer.Sparse Key := [(key1933, -2), (key1701, -2), (key1696, -2), (key1701, 6), (key1933, -2), (key1701, -2), (key1696, -2), (key1953, 2), (key1751, 2), (key1933, 2), (key1278, 2), (key1696, 2), (key1273, 2), (key1751, -2), (key1701, -2), (key1278, -2), (key1701, 6), (key1751, -2), (key1701, -2), (key1278, -2)]

theorem rawRowCheck14653 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form2 = rawRow14653 := by decide +kernel

def row14653 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

theorem rowCheck14653 : row14653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14653 := by decide +kernel

theorem rowEval14653 (x : Key → ℝ) : Integer.Sparse.eval row14653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14653, Integer.Sparse.eval_collectBalanced, rawRowCheck14653]

def rawRow14654 : Integer.Sparse Key := [(key1701, -2), (key1701, -2), (key1933, -2), (key1696, 6), (key1751, -2), (key1751, -2), (key1953, -2), (key1278, 2), (key1278, 2), (key1701, 2), (key1701, 2), (key1933, 2), (key1933, 2), (key1273, -2), (key1696, -2), (key1696, -2), (key1751, 6), (key1278, -2), (key1701, -2), (key1701, -2)]

theorem rawRowCheck14654 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form2 = rawRow14654 := by decide +kernel

def row14654 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

theorem rowCheck14654 : row14654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14654 := by decide +kernel

theorem rowEval14654 (x : Key → ℝ) : Integer.Sparse.eval row14654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14654, Integer.Sparse.eval_collectBalanced, rawRowCheck14654]

def rawRow14655 : Integer.Sparse Key := [(key1701, -2), (key1933, -2), (key1701, -2), (key1696, 6), (key1751, -2), (key1953, -2), (key1751, -2), (key1701, 2), (key1933, 2), (key1278, 2), (key1933, 2), (key1278, 2), (key1701, 2), (key1696, -2), (key1273, -2), (key1696, -2), (key1751, 6), (key1701, -2), (key1278, -2), (key1701, -2)]

theorem rawRowCheck14655 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form2 = rawRow14655 := by decide +kernel

def row14655 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

theorem rowCheck14655 : row14655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14655 := by decide +kernel

theorem rowEval14655 (x : Key → ℝ) : Integer.Sparse.eval row14655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14655, Integer.Sparse.eval_collectBalanced, rawRowCheck14655]

def rawRow14656 : Integer.Sparse Key := [(key1933, -2), (key1701, -2), (key1701, -2), (key1696, 6), (key1953, -2), (key1751, -2), (key1751, -2), (key1933, 2), (key1701, 2), (key1933, 2), (key1278, 2), (key1701, 2), (key1278, 2), (key1696, -2), (key1696, -2), (key1273, -2), (key1751, 6), (key1701, -2), (key1701, -2), (key1278, -2)]

theorem rawRowCheck14656 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form2 = rawRow14656 := by decide +kernel

def row14656 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

theorem rowCheck14656 : row14656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14656 := by decide +kernel

theorem rowEval14656 (x : Key → ℝ) : Integer.Sparse.eval row14656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14656, Integer.Sparse.eval_collectBalanced, rawRowCheck14656]

def rawRow14657 : Integer.Sparse Key := [(key1751, -2), (key1751, -2), (key1751, -2), (key1953, 6), (key1278, -2), (key1278, -2), (key1278, -2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1933, -2), (key1933, -2), (key1933, -2), (key1273, 6), (key1696, -2), (key1696, -2), (key1696, -2)]

theorem rawRowCheck14657 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form2 = rawRow14657 := by decide +kernel

def row14657 : Integer.Sparse Key := [(key1273, 6), (key1278, -6), (key1696, -6), (key1701, 12), (key1751, -6), (key1933, -6), (key1953, 6)]

theorem rowCheck14657 : row14657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14657 := by decide +kernel

theorem rowEval14657 (x : Key → ℝ) : Integer.Sparse.eval row14657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14657, Integer.Sparse.eval_collectBalanced, rawRowCheck14657]

def rawRow14658 : Integer.Sparse Key := [(key1751, -2), (key1751, -2), (key1953, -2), (key1751, 6), (key1701, -2), (key1701, -2), (key1933, -2), (key1278, 2), (key1278, 2), (key1701, 2), (key1701, 2), (key1933, 2), (key1933, 2), (key1278, -2), (key1701, -2), (key1701, -2), (key1696, 6), (key1273, -2), (key1696, -2), (key1696, -2)]

theorem rawRowCheck14658 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form2 = rawRow14658 := by decide +kernel

def row14658 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

theorem rowCheck14658 : row14658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14658 := by decide +kernel

theorem rowEval14658 (x : Key → ℝ) : Integer.Sparse.eval row14658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14658, Integer.Sparse.eval_collectBalanced, rawRowCheck14658]

def rawRow14659 : Integer.Sparse Key := [(key1751, -2), (key1953, -2), (key1751, -2), (key1751, 6), (key1701, -2), (key1933, -2), (key1701, -2), (key1701, 2), (key1933, 2), (key1278, 2), (key1933, 2), (key1278, 2), (key1701, 2), (key1701, -2), (key1278, -2), (key1701, -2), (key1696, 6), (key1696, -2), (key1273, -2), (key1696, -2)]

theorem rawRowCheck14659 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form2 = rawRow14659 := by decide +kernel

def row14659 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

theorem rowCheck14659 : row14659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14659 := by decide +kernel

theorem rowEval14659 (x : Key → ℝ) : Integer.Sparse.eval row14659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14659, Integer.Sparse.eval_collectBalanced, rawRowCheck14659]

def rawRow14660 : Integer.Sparse Key := [(key1953, -2), (key1751, -2), (key1751, -2), (key1751, 6), (key1933, -2), (key1701, -2), (key1701, -2), (key1933, 2), (key1701, 2), (key1933, 2), (key1278, 2), (key1701, 2), (key1278, 2), (key1701, -2), (key1701, -2), (key1278, -2), (key1696, 6), (key1696, -2), (key1696, -2), (key1273, -2)]

theorem rawRowCheck14660 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form2 = rawRow14660 := by decide +kernel

def row14660 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

theorem rowCheck14660 : row14660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14660 := by decide +kernel

theorem rowEval14660 (x : Key → ℝ) : Integer.Sparse.eval row14660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14660, Integer.Sparse.eval_collectBalanced, rawRowCheck14660]

def rawRow14661 : Integer.Sparse Key := [(key1360, 6), (key1360, -2), (key1360, -2), (key1372, -2), (key1486, 6), (key1486, -2), (key1486, -2), (key1511, -2), (key1712, -2), (key1712, -2), (key1721, -2), (key1712, -2), (key1712, -2), (key1739, -2), (key1712, 2), (key1721, 2), (key1712, 2), (key1739, 2), (key1721, 2), (key1739, 2)]

theorem rawRowCheck14661 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form3 = rawRow14661 := by decide +kernel

def row14661 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

theorem rowCheck14661 : row14661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14661 := by decide +kernel

theorem rowEval14661 (x : Key → ℝ) : Integer.Sparse.eval row14661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14661, Integer.Sparse.eval_collectBalanced, rawRowCheck14661]

def rawRow14662 : Integer.Sparse Key := [(key1360, 6), (key1360, -2), (key1372, -2), (key1360, -2), (key1486, 6), (key1486, -2), (key1511, -2), (key1486, -2), (key1712, -2), (key1721, -2), (key1712, -2), (key1712, -2), (key1739, -2), (key1712, -2), (key1721, 2), (key1712, 2), (key1739, 2), (key1712, 2), (key1739, 2), (key1721, 2)]

theorem rawRowCheck14662 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form3 = rawRow14662 := by decide +kernel

def row14662 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

theorem rowCheck14662 : row14662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14662 := by decide +kernel

theorem rowEval14662 (x : Key → ℝ) : Integer.Sparse.eval row14662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14662, Integer.Sparse.eval_collectBalanced, rawRowCheck14662]

def rawRow14663 : Integer.Sparse Key := [(key1360, 6), (key1372, -2), (key1360, -2), (key1360, -2), (key1486, 6), (key1511, -2), (key1486, -2), (key1486, -2), (key1721, -2), (key1712, -2), (key1712, -2), (key1739, -2), (key1712, -2), (key1712, -2), (key1739, 2), (key1739, 2), (key1721, 2), (key1721, 2), (key1712, 2), (key1712, 2)]

theorem rawRowCheck14663 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form3 = rawRow14663 := by decide +kernel

def row14663 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

theorem rowCheck14663 : row14663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14663 := by decide +kernel

theorem rowEval14663 (x : Key → ℝ) : Integer.Sparse.eval row14663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14663, Integer.Sparse.eval_collectBalanced, rawRowCheck14663]

def rawRow14664 : Integer.Sparse Key := [(key1372, 6), (key1360, -2), (key1360, -2), (key1360, -2), (key1511, 6), (key1486, -2), (key1486, -2), (key1486, -2), (key1739, -2), (key1739, -2), (key1739, -2), (key1721, -2), (key1721, -2), (key1721, -2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2)]

theorem rawRowCheck14664 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form3 = rawRow14664 := by decide +kernel

def row14664 : Integer.Sparse Key := [(key1360, -6), (key1372, 6), (key1486, -6), (key1511, 6), (key1712, 12), (key1721, -6), (key1739, -6)]

theorem rowCheck14664 : row14664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14664 := by decide +kernel

theorem rowEval14664 (x : Key → ℝ) : Integer.Sparse.eval row14664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14664, Integer.Sparse.eval_collectBalanced, rawRowCheck14664]

def rawRow14665 : Integer.Sparse Key := [(key1486, 6), (key1712, -2), (key1712, -2), (key1721, -2), (key1360, 6), (key1712, -2), (key1712, -2), (key1739, -2), (key1360, -2), (key1360, -2), (key1372, -2), (key1486, -2), (key1486, -2), (key1511, -2), (key1712, 2), (key1721, 2), (key1712, 2), (key1739, 2), (key1721, 2), (key1739, 2)]

theorem rawRowCheck14665 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form3 = rawRow14665 := by decide +kernel

def row14665 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

theorem rowCheck14665 : row14665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14665 := by decide +kernel

theorem rowEval14665 (x : Key → ℝ) : Integer.Sparse.eval row14665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14665, Integer.Sparse.eval_collectBalanced, rawRowCheck14665]

def rawRow14666 : Integer.Sparse Key := [(key1486, 6), (key1712, -2), (key1721, -2), (key1712, -2), (key1360, 6), (key1712, -2), (key1739, -2), (key1712, -2), (key1360, -2), (key1372, -2), (key1360, -2), (key1486, -2), (key1511, -2), (key1486, -2), (key1721, 2), (key1712, 2), (key1739, 2), (key1712, 2), (key1739, 2), (key1721, 2)]

theorem rawRowCheck14666 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form3 = rawRow14666 := by decide +kernel

def row14666 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

theorem rowCheck14666 : row14666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14666 := by decide +kernel

theorem rowEval14666 (x : Key → ℝ) : Integer.Sparse.eval row14666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14666, Integer.Sparse.eval_collectBalanced, rawRowCheck14666]

def rawRow14667 : Integer.Sparse Key := [(key1486, 6), (key1721, -2), (key1712, -2), (key1712, -2), (key1360, 6), (key1739, -2), (key1712, -2), (key1712, -2), (key1372, -2), (key1360, -2), (key1360, -2), (key1511, -2), (key1486, -2), (key1486, -2), (key1739, 2), (key1739, 2), (key1721, 2), (key1721, 2), (key1712, 2), (key1712, 2)]

theorem rawRowCheck14667 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form3 = rawRow14667 := by decide +kernel

def row14667 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

theorem rowCheck14667 : row14667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14667 := by decide +kernel

theorem rowEval14667 (x : Key → ℝ) : Integer.Sparse.eval row14667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14667, Integer.Sparse.eval_collectBalanced, rawRowCheck14667]

def rawRow14668 : Integer.Sparse Key := [(key1712, 6), (key1486, -2), (key1712, -2), (key1721, -2), (key1712, 6), (key1360, -2), (key1712, -2), (key1739, -2), (key1486, -2), (key1712, -2), (key1721, -2), (key1360, -2), (key1712, -2), (key1739, -2), (key1360, 2), (key1372, 2), (key1486, 2), (key1511, 2), (key1721, 2), (key1739, 2)]

theorem rawRowCheck14668 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form3 = rawRow14668 := by decide +kernel

def row14668 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

theorem rowCheck14668 : row14668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14668 := by decide +kernel

theorem rowEval14668 (x : Key → ℝ) : Integer.Sparse.eval row14668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14668, Integer.Sparse.eval_collectBalanced, rawRowCheck14668]

def rawRow14669 : Integer.Sparse Key := [(key1712, 6), (key1486, -2), (key1721, -2), (key1712, -2), (key1712, 6), (key1360, -2), (key1739, -2), (key1712, -2), (key1486, -2), (key1721, -2), (key1712, -2), (key1360, -2), (key1739, -2), (key1712, -2), (key1372, 2), (key1360, 2), (key1511, 2), (key1486, 2), (key1739, 2), (key1721, 2)]

theorem rawRowCheck14669 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form3 = rawRow14669 := by decide +kernel

def row14669 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

theorem rowCheck14669 : row14669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14669 := by decide +kernel

theorem rowEval14669 (x : Key → ℝ) : Integer.Sparse.eval row14669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14669, Integer.Sparse.eval_collectBalanced, rawRowCheck14669]

def rawRow14670 : Integer.Sparse Key := [(key1712, 6), (key1712, -2), (key1486, -2), (key1721, -2), (key1712, 6), (key1712, -2), (key1360, -2), (key1739, -2), (key1712, -2), (key1486, -2), (key1721, -2), (key1712, -2), (key1360, -2), (key1739, -2), (key1486, 2), (key1721, 2), (key1360, 2), (key1739, 2), (key1372, 2), (key1511, 2)]

theorem rawRowCheck14670 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form3 = rawRow14670 := by decide +kernel

def row14670 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

theorem rowCheck14670 : row14670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14670 := by decide +kernel

theorem rowEval14670 (x : Key → ℝ) : Integer.Sparse.eval row14670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14670, Integer.Sparse.eval_collectBalanced, rawRowCheck14670]

def rawRow14671 : Integer.Sparse Key := [(key1712, 6), (key1712, -2), (key1721, -2), (key1486, -2), (key1712, 6), (key1712, -2), (key1739, -2), (key1360, -2), (key1712, -2), (key1721, -2), (key1486, -2), (key1712, -2), (key1739, -2), (key1360, -2), (key1721, 2), (key1486, 2), (key1739, 2), (key1360, 2), (key1511, 2), (key1372, 2)]

theorem rawRowCheck14671 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form3 = rawRow14671 := by decide +kernel

def row14671 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

theorem rowCheck14671 : row14671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14671 := by decide +kernel

theorem rowEval14671 (x : Key → ℝ) : Integer.Sparse.eval row14671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14671, Integer.Sparse.eval_collectBalanced, rawRowCheck14671]

def rawRow14672 : Integer.Sparse Key := [(key1712, 6), (key1721, -2), (key1486, -2), (key1712, -2), (key1712, 6), (key1739, -2), (key1360, -2), (key1712, -2), (key1721, -2), (key1486, -2), (key1712, -2), (key1739, -2), (key1360, -2), (key1712, -2), (key1511, 2), (key1739, 2), (key1372, 2), (key1721, 2), (key1360, 2), (key1486, 2)]

theorem rawRowCheck14672 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form3 = rawRow14672 := by decide +kernel

def row14672 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

theorem rowCheck14672 : row14672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14672 := by decide +kernel

theorem rowEval14672 (x : Key → ℝ) : Integer.Sparse.eval row14672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14672, Integer.Sparse.eval_collectBalanced, rawRowCheck14672]

def rawRow14673 : Integer.Sparse Key := [(key1712, 6), (key1721, -2), (key1712, -2), (key1486, -2), (key1712, 6), (key1739, -2), (key1712, -2), (key1360, -2), (key1721, -2), (key1712, -2), (key1486, -2), (key1739, -2), (key1712, -2), (key1360, -2), (key1739, 2), (key1511, 2), (key1721, 2), (key1372, 2), (key1486, 2), (key1360, 2)]

theorem rawRowCheck14673 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form3 = rawRow14673 := by decide +kernel

def row14673 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

theorem rowCheck14673 : row14673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14673 := by decide +kernel

theorem rowEval14673 (x : Key → ℝ) : Integer.Sparse.eval row14673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14673, Integer.Sparse.eval_collectBalanced, rawRowCheck14673]

def rawRow14674 : Integer.Sparse Key := [(key1721, 6), (key1486, -2), (key1712, -2), (key1712, -2), (key1739, 6), (key1360, -2), (key1712, -2), (key1712, -2), (key1511, -2), (key1739, -2), (key1739, -2), (key1372, -2), (key1721, -2), (key1721, -2), (key1360, 2), (key1360, 2), (key1486, 2), (key1486, 2), (key1712, 2), (key1712, 2)]

theorem rawRowCheck14674 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form3 = rawRow14674 := by decide +kernel

def row14674 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

theorem rowCheck14674 : row14674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14674 := by decide +kernel

theorem rowEval14674 (x : Key → ℝ) : Integer.Sparse.eval row14674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14674, Integer.Sparse.eval_collectBalanced, rawRowCheck14674]

def rawRow14675 : Integer.Sparse Key := [(key1721, 6), (key1712, -2), (key1486, -2), (key1712, -2), (key1739, 6), (key1712, -2), (key1360, -2), (key1712, -2), (key1739, -2), (key1511, -2), (key1739, -2), (key1721, -2), (key1372, -2), (key1721, -2), (key1486, 2), (key1712, 2), (key1360, 2), (key1712, 2), (key1360, 2), (key1486, 2)]

theorem rawRowCheck14675 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form3 = rawRow14675 := by decide +kernel

def row14675 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

theorem rowCheck14675 : row14675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14675 := by decide +kernel

theorem rowEval14675 (x : Key → ℝ) : Integer.Sparse.eval row14675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14675, Integer.Sparse.eval_collectBalanced, rawRowCheck14675]

def rawRow14676 : Integer.Sparse Key := [(key1721, 6), (key1712, -2), (key1712, -2), (key1486, -2), (key1739, 6), (key1712, -2), (key1712, -2), (key1360, -2), (key1739, -2), (key1739, -2), (key1511, -2), (key1721, -2), (key1721, -2), (key1372, -2), (key1712, 2), (key1486, 2), (key1712, 2), (key1360, 2), (key1486, 2), (key1360, 2)]

theorem rawRowCheck14676 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form3 = rawRow14676 := by decide +kernel

def row14676 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

theorem rowCheck14676 : row14676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14676 := by decide +kernel

theorem rowEval14676 (x : Key → ℝ) : Integer.Sparse.eval row14676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14676, Integer.Sparse.eval_collectBalanced, rawRowCheck14676]

def rawRow14677 : Integer.Sparse Key := [(key1511, 6), (key1739, -2), (key1739, -2), (key1739, -2), (key1372, 6), (key1721, -2), (key1721, -2), (key1721, -2), (key1360, -2), (key1360, -2), (key1360, -2), (key1486, -2), (key1486, -2), (key1486, -2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2)]

theorem rawRowCheck14677 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form3 = rawRow14677 := by decide +kernel

def row14677 : Integer.Sparse Key := [(key1360, -6), (key1372, 6), (key1486, -6), (key1511, 6), (key1712, 12), (key1721, -6), (key1739, -6)]

theorem rowCheck14677 : row14677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14677 := by decide +kernel

theorem rowEval14677 (x : Key → ℝ) : Integer.Sparse.eval row14677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14677, Integer.Sparse.eval_collectBalanced, rawRowCheck14677]

def rawRow14678 : Integer.Sparse Key := [(key1739, 6), (key1511, -2), (key1739, -2), (key1739, -2), (key1721, 6), (key1372, -2), (key1721, -2), (key1721, -2), (key1486, -2), (key1712, -2), (key1712, -2), (key1360, -2), (key1712, -2), (key1712, -2), (key1360, 2), (key1360, 2), (key1486, 2), (key1486, 2), (key1712, 2), (key1712, 2)]

theorem rawRowCheck14678 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form3 = rawRow14678 := by decide +kernel

def row14678 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

theorem rowCheck14678 : row14678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14678 := by decide +kernel

theorem rowEval14678 (x : Key → ℝ) : Integer.Sparse.eval row14678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14678, Integer.Sparse.eval_collectBalanced, rawRowCheck14678]

def rawRow14679 : Integer.Sparse Key := [(key1739, 6), (key1739, -2), (key1511, -2), (key1739, -2), (key1721, 6), (key1721, -2), (key1372, -2), (key1721, -2), (key1712, -2), (key1486, -2), (key1712, -2), (key1712, -2), (key1360, -2), (key1712, -2), (key1486, 2), (key1712, 2), (key1360, 2), (key1712, 2), (key1360, 2), (key1486, 2)]

theorem rawRowCheck14679 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form3 = rawRow14679 := by decide +kernel

def row14679 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

theorem rowCheck14679 : row14679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14679 := by decide +kernel

theorem rowEval14679 (x : Key → ℝ) : Integer.Sparse.eval row14679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14679, Integer.Sparse.eval_collectBalanced, rawRowCheck14679]

def rawRow14680 : Integer.Sparse Key := [(key1739, 6), (key1739, -2), (key1739, -2), (key1511, -2), (key1721, 6), (key1721, -2), (key1721, -2), (key1372, -2), (key1712, -2), (key1712, -2), (key1486, -2), (key1712, -2), (key1712, -2), (key1360, -2), (key1712, 2), (key1486, 2), (key1712, 2), (key1360, 2), (key1486, 2), (key1360, 2)]

theorem rawRowCheck14680 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form3 = rawRow14680 := by decide +kernel

def row14680 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

theorem rowCheck14680 : row14680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14680 := by decide +kernel

theorem rowEval14680 (x : Key → ℝ) : Integer.Sparse.eval row14680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14680, Integer.Sparse.eval_collectBalanced, rawRowCheck14680]

def rawRow14681 : Integer.Sparse Key := [(key221, -2), (key225, -2), (key225, -2), (key225, 6), (key493, -2), (key497, -2), (key497, -2), (key493, 2), (key497, 2), (key493, 2), (key551, 2), (key497, 2), (key551, 2), (key497, -2), (key497, -2), (key551, -2), (key619, 6), (key619, -2), (key619, -2), (key645, -2)]

theorem rawRowCheck14681 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form4 = rawRow14681 := by decide +kernel

def row14681 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

theorem rowCheck14681 : row14681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14681 := by decide +kernel

theorem rowEval14681 (x : Key → ℝ) : Integer.Sparse.eval row14681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14681, Integer.Sparse.eval_collectBalanced, rawRowCheck14681]

def rawRow14682 : Integer.Sparse Key := [(key225, -2), (key221, -2), (key225, -2), (key225, 6), (key497, -2), (key493, -2), (key497, -2), (key497, 2), (key493, 2), (key551, 2), (key493, 2), (key551, 2), (key497, 2), (key497, -2), (key551, -2), (key497, -2), (key619, 6), (key619, -2), (key645, -2), (key619, -2)]

theorem rawRowCheck14682 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form4 = rawRow14682 := by decide +kernel

def row14682 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

theorem rowCheck14682 : row14682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14682 := by decide +kernel

theorem rowEval14682 (x : Key → ℝ) : Integer.Sparse.eval row14682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14682, Integer.Sparse.eval_collectBalanced, rawRowCheck14682]

def rawRow14683 : Integer.Sparse Key := [(key225, -2), (key225, -2), (key221, -2), (key225, 6), (key497, -2), (key497, -2), (key493, -2), (key551, 2), (key551, 2), (key497, 2), (key497, 2), (key493, 2), (key493, 2), (key551, -2), (key497, -2), (key497, -2), (key619, 6), (key645, -2), (key619, -2), (key619, -2)]

theorem rawRowCheck14683 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form4 = rawRow14683 := by decide +kernel

def row14683 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

theorem rowCheck14683 : row14683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14683 := by decide +kernel

theorem rowEval14683 (x : Key → ℝ) : Integer.Sparse.eval row14683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14683, Integer.Sparse.eval_collectBalanced, rawRowCheck14683]

def rawRow14684 : Integer.Sparse Key := [(key225, -2), (key225, -2), (key225, -2), (key221, 6), (key551, -2), (key551, -2), (key551, -2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key493, -2), (key493, -2), (key493, -2), (key645, 6), (key619, -2), (key619, -2), (key619, -2)]

theorem rawRowCheck14684 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form4 = rawRow14684 := by decide +kernel

def row14684 : Integer.Sparse Key := [(key221, 6), (key225, -6), (key493, -6), (key497, 12), (key551, -6), (key619, -6), (key645, 6)]

theorem rowCheck14684 : row14684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14684 := by decide +kernel

theorem rowEval14684 (x : Key → ℝ) : Integer.Sparse.eval row14684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14684, Integer.Sparse.eval_collectBalanced, rawRowCheck14684]

def rawRow14685 : Integer.Sparse Key := [(key493, -2), (key497, -2), (key497, -2), (key619, 6), (key221, -2), (key225, -2), (key225, -2), (key493, 2), (key497, 2), (key493, 2), (key551, 2), (key497, 2), (key551, 2), (key619, -2), (key619, -2), (key645, -2), (key225, 6), (key497, -2), (key497, -2), (key551, -2)]

theorem rawRowCheck14685 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form4 = rawRow14685 := by decide +kernel

def row14685 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

theorem rowCheck14685 : row14685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14685 := by decide +kernel

theorem rowEval14685 (x : Key → ℝ) : Integer.Sparse.eval row14685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14685, Integer.Sparse.eval_collectBalanced, rawRowCheck14685]

def rawRow14686 : Integer.Sparse Key := [(key497, -2), (key493, -2), (key497, -2), (key619, 6), (key225, -2), (key221, -2), (key225, -2), (key497, 2), (key493, 2), (key551, 2), (key493, 2), (key551, 2), (key497, 2), (key619, -2), (key645, -2), (key619, -2), (key225, 6), (key497, -2), (key551, -2), (key497, -2)]

theorem rawRowCheck14686 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form4 = rawRow14686 := by decide +kernel

def row14686 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

theorem rowCheck14686 : row14686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14686 := by decide +kernel

theorem rowEval14686 (x : Key → ℝ) : Integer.Sparse.eval row14686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14686, Integer.Sparse.eval_collectBalanced, rawRowCheck14686]

def rawRow14687 : Integer.Sparse Key := [(key497, -2), (key497, -2), (key493, -2), (key619, 6), (key225, -2), (key225, -2), (key221, -2), (key551, 2), (key551, 2), (key497, 2), (key497, 2), (key493, 2), (key493, 2), (key645, -2), (key619, -2), (key619, -2), (key225, 6), (key551, -2), (key497, -2), (key497, -2)]

theorem rawRowCheck14687 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form4 = rawRow14687 := by decide +kernel

def row14687 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

theorem rowCheck14687 : row14687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14687 := by decide +kernel

theorem rowEval14687 (x : Key → ℝ) : Integer.Sparse.eval row14687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14687, Integer.Sparse.eval_collectBalanced, rawRowCheck14687]

def rawRow14688 : Integer.Sparse Key := [(key493, -2), (key497, -2), (key619, -2), (key497, 6), (key493, -2), (key497, -2), (key619, -2), (key221, 2), (key225, 2), (key493, 2), (key551, 2), (key619, 2), (key645, 2), (key225, -2), (key497, -2), (key551, -2), (key497, 6), (key225, -2), (key497, -2), (key551, -2)]

theorem rawRowCheck14688 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form4 = rawRow14688 := by decide +kernel

def row14688 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

theorem rowCheck14688 : row14688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14688 := by decide +kernel

theorem rowEval14688 (x : Key → ℝ) : Integer.Sparse.eval row14688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14688, Integer.Sparse.eval_collectBalanced, rawRowCheck14688]

def rawRow14689 : Integer.Sparse Key := [(key497, -2), (key493, -2), (key619, -2), (key497, 6), (key497, -2), (key493, -2), (key619, -2), (key225, 2), (key221, 2), (key551, 2), (key493, 2), (key645, 2), (key619, 2), (key225, -2), (key551, -2), (key497, -2), (key497, 6), (key225, -2), (key551, -2), (key497, -2)]

theorem rawRowCheck14689 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form4 = rawRow14689 := by decide +kernel

def row14689 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

theorem rowCheck14689 : row14689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14689 := by decide +kernel

theorem rowEval14689 (x : Key → ℝ) : Integer.Sparse.eval row14689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14689, Integer.Sparse.eval_collectBalanced, rawRowCheck14689]

def rawRow14690 : Integer.Sparse Key := [(key493, -2), (key619, -2), (key497, -2), (key497, 6), (key493, -2), (key619, -2), (key497, -2), (key493, 2), (key619, 2), (key221, 2), (key645, 2), (key225, 2), (key551, 2), (key497, -2), (key225, -2), (key551, -2), (key497, 6), (key497, -2), (key225, -2), (key551, -2)]

theorem rawRowCheck14690 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form4 = rawRow14690 := by decide +kernel

def row14690 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

theorem rowCheck14690 : row14690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14690 := by decide +kernel

theorem rowEval14690 (x : Key → ℝ) : Integer.Sparse.eval row14690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14690, Integer.Sparse.eval_collectBalanced, rawRowCheck14690]

def rawRow14691 : Integer.Sparse Key := [(key619, -2), (key493, -2), (key497, -2), (key497, 6), (key619, -2), (key493, -2), (key497, -2), (key619, 2), (key493, 2), (key645, 2), (key221, 2), (key551, 2), (key225, 2), (key497, -2), (key551, -2), (key225, -2), (key497, 6), (key497, -2), (key551, -2), (key225, -2)]

theorem rawRowCheck14691 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form4 = rawRow14691 := by decide +kernel

def row14691 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

theorem rowCheck14691 : row14691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14691 := by decide +kernel

theorem rowEval14691 (x : Key → ℝ) : Integer.Sparse.eval row14691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14691, Integer.Sparse.eval_collectBalanced, rawRowCheck14691]

def rawRow14692 : Integer.Sparse Key := [(key497, -2), (key619, -2), (key493, -2), (key497, 6), (key497, -2), (key619, -2), (key493, -2), (key551, 2), (key645, 2), (key225, 2), (key619, 2), (key221, 2), (key493, 2), (key551, -2), (key225, -2), (key497, -2), (key497, 6), (key551, -2), (key225, -2), (key497, -2)]

theorem rawRowCheck14692 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form4 = rawRow14692 := by decide +kernel

def row14692 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

theorem rowCheck14692 : row14692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14692 := by decide +kernel

theorem rowEval14692 (x : Key → ℝ) : Integer.Sparse.eval row14692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14692, Integer.Sparse.eval_collectBalanced, rawRowCheck14692]

def rawRow14693 : Integer.Sparse Key := [(key619, -2), (key497, -2), (key493, -2), (key497, 6), (key619, -2), (key497, -2), (key493, -2), (key645, 2), (key551, 2), (key619, 2), (key225, 2), (key493, 2), (key221, 2), (key551, -2), (key497, -2), (key225, -2), (key497, 6), (key551, -2), (key497, -2), (key225, -2)]

theorem rawRowCheck14693 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form4 = rawRow14693 := by decide +kernel

def row14693 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

theorem rowCheck14693 : row14693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14693 := by decide +kernel

theorem rowEval14693 (x : Key → ℝ) : Integer.Sparse.eval row14693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14693, Integer.Sparse.eval_collectBalanced, rawRowCheck14693]

def rawRow14694 : Integer.Sparse Key := [(key497, -2), (key497, -2), (key619, -2), (key493, 6), (key551, -2), (key551, -2), (key645, -2), (key225, 2), (key225, 2), (key497, 2), (key497, 2), (key619, 2), (key619, 2), (key221, -2), (key493, -2), (key493, -2), (key551, 6), (key225, -2), (key497, -2), (key497, -2)]

theorem rawRowCheck14694 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form4 = rawRow14694 := by decide +kernel

def row14694 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

theorem rowCheck14694 : row14694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14694 := by decide +kernel

theorem rowEval14694 (x : Key → ℝ) : Integer.Sparse.eval row14694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14694, Integer.Sparse.eval_collectBalanced, rawRowCheck14694]

def rawRow14695 : Integer.Sparse Key := [(key497, -2), (key619, -2), (key497, -2), (key493, 6), (key551, -2), (key645, -2), (key551, -2), (key497, 2), (key619, 2), (key225, 2), (key619, 2), (key225, 2), (key497, 2), (key493, -2), (key221, -2), (key493, -2), (key551, 6), (key497, -2), (key225, -2), (key497, -2)]

theorem rawRowCheck14695 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form4 = rawRow14695 := by decide +kernel

def row14695 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

theorem rowCheck14695 : row14695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14695 := by decide +kernel

theorem rowEval14695 (x : Key → ℝ) : Integer.Sparse.eval row14695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14695, Integer.Sparse.eval_collectBalanced, rawRowCheck14695]

def rawRow14696 : Integer.Sparse Key := [(key619, -2), (key497, -2), (key497, -2), (key493, 6), (key645, -2), (key551, -2), (key551, -2), (key619, 2), (key497, 2), (key619, 2), (key225, 2), (key497, 2), (key225, 2), (key493, -2), (key493, -2), (key221, -2), (key551, 6), (key497, -2), (key497, -2), (key225, -2)]

theorem rawRowCheck14696 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form4 = rawRow14696 := by decide +kernel

def row14696 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

theorem rowCheck14696 : row14696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14696 := by decide +kernel

theorem rowEval14696 (x : Key → ℝ) : Integer.Sparse.eval row14696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14696, Integer.Sparse.eval_collectBalanced, rawRowCheck14696]

def rawRow14697 : Integer.Sparse Key := [(key551, -2), (key551, -2), (key551, -2), (key645, 6), (key225, -2), (key225, -2), (key225, -2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key619, -2), (key619, -2), (key619, -2), (key221, 6), (key493, -2), (key493, -2), (key493, -2)]

theorem rawRowCheck14697 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form4 = rawRow14697 := by decide +kernel

def row14697 : Integer.Sparse Key := [(key221, 6), (key225, -6), (key493, -6), (key497, 12), (key551, -6), (key619, -6), (key645, 6)]

theorem rowCheck14697 : row14697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14697 := by decide +kernel

theorem rowEval14697 (x : Key → ℝ) : Integer.Sparse.eval row14697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14697, Integer.Sparse.eval_collectBalanced, rawRowCheck14697]

def rawRow14698 : Integer.Sparse Key := [(key551, -2), (key551, -2), (key645, -2), (key551, 6), (key497, -2), (key497, -2), (key619, -2), (key225, 2), (key225, 2), (key497, 2), (key497, 2), (key619, 2), (key619, 2), (key225, -2), (key497, -2), (key497, -2), (key493, 6), (key221, -2), (key493, -2), (key493, -2)]

theorem rawRowCheck14698 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form4 = rawRow14698 := by decide +kernel

def row14698 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

theorem rowCheck14698 : row14698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14698 := by decide +kernel

theorem rowEval14698 (x : Key → ℝ) : Integer.Sparse.eval row14698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14698, Integer.Sparse.eval_collectBalanced, rawRowCheck14698]

def rawRow14699 : Integer.Sparse Key := [(key551, -2), (key645, -2), (key551, -2), (key551, 6), (key497, -2), (key619, -2), (key497, -2), (key497, 2), (key619, 2), (key225, 2), (key619, 2), (key225, 2), (key497, 2), (key497, -2), (key225, -2), (key497, -2), (key493, 6), (key493, -2), (key221, -2), (key493, -2)]

theorem rawRowCheck14699 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form4 = rawRow14699 := by decide +kernel

def row14699 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

theorem rowCheck14699 : row14699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14699 := by decide +kernel

theorem rowEval14699 (x : Key → ℝ) : Integer.Sparse.eval row14699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14699, Integer.Sparse.eval_collectBalanced, rawRowCheck14699]

def rawRow14700 : Integer.Sparse Key := [(key645, -2), (key551, -2), (key551, -2), (key551, 6), (key619, -2), (key497, -2), (key497, -2), (key619, 2), (key497, 2), (key619, 2), (key225, 2), (key497, 2), (key225, 2), (key497, -2), (key497, -2), (key225, -2), (key493, 6), (key493, -2), (key493, -2), (key221, -2)]

theorem rawRowCheck14700 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form4 = rawRow14700 := by decide +kernel

def row14700 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

theorem rowCheck14700 : row14700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14700 := by decide +kernel

theorem rowEval14700 (x : Key → ℝ) : Integer.Sparse.eval row14700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14700, Integer.Sparse.eval_collectBalanced, rawRowCheck14700]

def rawRow14701 : Integer.Sparse Key := [(key496, 4), (key496, 4), (key559, 4), (key496, -2), (key502, -2), (key496, -2), (key559, -2), (key502, -2), (key559, -2), (key618, -2), (key622, -2), (key618, -2), (key648, -2), (key622, -2), (key648, -2), (key622, 4), (key622, 4), (key648, 4)]

theorem rawRowCheck14701 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form5 = rawRow14701 := by decide +kernel

def row14701 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

theorem rowCheck14701 : row14701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14701 := by decide +kernel

theorem rowEval14701 (x : Key → ℝ) : Integer.Sparse.eval row14701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14701, Integer.Sparse.eval_collectBalanced, rawRowCheck14701]

def rawRow14702 : Integer.Sparse Key := [(key496, 4), (key559, 4), (key496, 4), (key502, -2), (key496, -2), (key559, -2), (key496, -2), (key559, -2), (key502, -2), (key622, -2), (key618, -2), (key648, -2), (key618, -2), (key648, -2), (key622, -2), (key622, 4), (key648, 4), (key622, 4)]

theorem rawRowCheck14702 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form5 = rawRow14702 := by decide +kernel

def row14702 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

theorem rowCheck14702 : row14702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14702 := by decide +kernel

theorem rowEval14702 (x : Key → ℝ) : Integer.Sparse.eval row14702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14702, Integer.Sparse.eval_collectBalanced, rawRowCheck14702]

def rawRow14703 : Integer.Sparse Key := [(key559, 4), (key496, 4), (key496, 4), (key559, -2), (key559, -2), (key502, -2), (key502, -2), (key496, -2), (key496, -2), (key648, -2), (key648, -2), (key622, -2), (key622, -2), (key618, -2), (key618, -2), (key648, 4), (key622, 4), (key622, 4)]

theorem rawRowCheck14703 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form5 = rawRow14703 := by decide +kernel

def row14703 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

theorem rowCheck14703 : row14703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14703 := by decide +kernel

theorem rowEval14703 (x : Key → ℝ) : Integer.Sparse.eval row14703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14703, Integer.Sparse.eval_collectBalanced, rawRowCheck14703]

def rawRow14704 : Integer.Sparse Key := [(key502, 4), (key502, 4), (key502, 4), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key618, 4), (key618, 4), (key618, 4)]

theorem rawRowCheck14704 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form5 = rawRow14704 := by decide +kernel

def row14704 : Integer.Sparse Key := [(key496, -12), (key502, 12), (key618, 12), (key622, -12)]

theorem rowCheck14704 : row14704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14704 := by decide +kernel

theorem rowEval14704 (x : Key → ℝ) : Integer.Sparse.eval row14704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14704, Integer.Sparse.eval_collectBalanced, rawRowCheck14704]

def rawRow14705 : Integer.Sparse Key := [(key496, 4), (key496, 4), (key559, 4), (key618, -2), (key622, -2), (key618, -2), (key648, -2), (key622, -2), (key648, -2), (key496, -2), (key502, -2), (key496, -2), (key559, -2), (key502, -2), (key559, -2), (key622, 4), (key622, 4), (key648, 4)]

theorem rawRowCheck14705 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form5 = rawRow14705 := by decide +kernel

def row14705 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

theorem rowCheck14705 : row14705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14705 := by decide +kernel

theorem rowEval14705 (x : Key → ℝ) : Integer.Sparse.eval row14705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14705, Integer.Sparse.eval_collectBalanced, rawRowCheck14705]

def rawRow14706 : Integer.Sparse Key := [(key496, 4), (key559, 4), (key496, 4), (key622, -2), (key618, -2), (key648, -2), (key618, -2), (key648, -2), (key622, -2), (key502, -2), (key496, -2), (key559, -2), (key496, -2), (key559, -2), (key502, -2), (key622, 4), (key648, 4), (key622, 4)]

theorem rawRowCheck14706 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form5 = rawRow14706 := by decide +kernel

def row14706 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

theorem rowCheck14706 : row14706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14706 := by decide +kernel

theorem rowEval14706 (x : Key → ℝ) : Integer.Sparse.eval row14706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14706, Integer.Sparse.eval_collectBalanced, rawRowCheck14706]

def rawRow14707 : Integer.Sparse Key := [(key559, 4), (key496, 4), (key496, 4), (key648, -2), (key648, -2), (key622, -2), (key622, -2), (key618, -2), (key618, -2), (key559, -2), (key559, -2), (key502, -2), (key502, -2), (key496, -2), (key496, -2), (key648, 4), (key622, 4), (key622, 4)]

theorem rawRowCheck14707 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form5 = rawRow14707 := by decide +kernel

def row14707 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

theorem rowCheck14707 : row14707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14707 := by decide +kernel

theorem rowEval14707 (x : Key → ℝ) : Integer.Sparse.eval row14707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14707, Integer.Sparse.eval_collectBalanced, rawRowCheck14707]

def rawRow14708 : Integer.Sparse Key := [(key224, 4), (key618, 4), (key648, 4), (key224, -2), (key230, -2), (key496, -2), (key559, -2), (key622, -2), (key648, -2), (key224, -2), (key230, -2), (key496, -2), (key559, -2), (key622, -2), (key648, -2), (key230, 4), (key502, 4), (key559, 4)]

theorem rawRowCheck14708 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form5 = rawRow14708 := by decide +kernel

def row14708 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

theorem rowCheck14708 : row14708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14708 := by decide +kernel

theorem rowEval14708 (x : Key → ℝ) : Integer.Sparse.eval row14708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14708, Integer.Sparse.eval_collectBalanced, rawRowCheck14708]

def rawRow14709 : Integer.Sparse Key := [(key224, 4), (key648, 4), (key618, 4), (key230, -2), (key224, -2), (key559, -2), (key496, -2), (key648, -2), (key622, -2), (key230, -2), (key224, -2), (key559, -2), (key496, -2), (key648, -2), (key622, -2), (key230, 4), (key559, 4), (key502, 4)]

theorem rawRowCheck14709 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form5 = rawRow14709 := by decide +kernel

def row14709 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

theorem rowCheck14709 : row14709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14709 := by decide +kernel

theorem rowEval14709 (x : Key → ℝ) : Integer.Sparse.eval row14709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14709, Integer.Sparse.eval_collectBalanced, rawRowCheck14709]

def rawRow14710 : Integer.Sparse Key := [(key618, 4), (key224, 4), (key648, 4), (key496, -2), (key622, -2), (key224, -2), (key648, -2), (key230, -2), (key559, -2), (key496, -2), (key622, -2), (key224, -2), (key648, -2), (key230, -2), (key559, -2), (key502, 4), (key230, 4), (key559, 4)]

theorem rawRowCheck14710 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form5 = rawRow14710 := by decide +kernel

def row14710 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

theorem rowCheck14710 : row14710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14710 := by decide +kernel

theorem rowEval14710 (x : Key → ℝ) : Integer.Sparse.eval row14710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14710, Integer.Sparse.eval_collectBalanced, rawRowCheck14710]

def rawRow14711 : Integer.Sparse Key := [(key618, 4), (key648, 4), (key224, 4), (key622, -2), (key496, -2), (key648, -2), (key224, -2), (key559, -2), (key230, -2), (key622, -2), (key496, -2), (key648, -2), (key224, -2), (key559, -2), (key230, -2), (key502, 4), (key559, 4), (key230, 4)]

theorem rawRowCheck14711 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form5 = rawRow14711 := by decide +kernel

def row14711 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

theorem rowCheck14711 : row14711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14711 := by decide +kernel

theorem rowEval14711 (x : Key → ℝ) : Integer.Sparse.eval row14711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14711, Integer.Sparse.eval_collectBalanced, rawRowCheck14711]

def rawRow14712 : Integer.Sparse Key := [(key648, 4), (key224, 4), (key618, 4), (key559, -2), (key648, -2), (key230, -2), (key622, -2), (key224, -2), (key496, -2), (key559, -2), (key648, -2), (key230, -2), (key622, -2), (key224, -2), (key496, -2), (key559, 4), (key230, 4), (key502, 4)]

theorem rawRowCheck14712 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form5 = rawRow14712 := by decide +kernel

def row14712 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

theorem rowCheck14712 : row14712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14712 := by decide +kernel

theorem rowEval14712 (x : Key → ℝ) : Integer.Sparse.eval row14712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14712, Integer.Sparse.eval_collectBalanced, rawRowCheck14712]

def rawRow14713 : Integer.Sparse Key := [(key648, 4), (key618, 4), (key224, 4), (key648, -2), (key559, -2), (key622, -2), (key230, -2), (key496, -2), (key224, -2), (key648, -2), (key559, -2), (key622, -2), (key230, -2), (key496, -2), (key224, -2), (key559, 4), (key502, 4), (key230, 4)]

theorem rawRowCheck14713 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form5 = rawRow14713 := by decide +kernel

def row14713 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

theorem rowCheck14713 : row14713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14713 := by decide +kernel

theorem rowEval14713 (x : Key → ℝ) : Integer.Sparse.eval row14713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14713, Integer.Sparse.eval_collectBalanced, rawRowCheck14713]

def rawRow14714 : Integer.Sparse Key := [(key230, 4), (key622, 4), (key622, 4), (key224, -2), (key224, -2), (key496, -2), (key496, -2), (key618, -2), (key618, -2), (key230, -2), (key230, -2), (key502, -2), (key502, -2), (key622, -2), (key622, -2), (key224, 4), (key496, 4), (key496, 4)]

theorem rawRowCheck14714 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form5 = rawRow14714 := by decide +kernel

def row14714 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

theorem rowCheck14714 : row14714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14714 := by decide +kernel

theorem rowEval14714 (x : Key → ℝ) : Integer.Sparse.eval row14714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14714, Integer.Sparse.eval_collectBalanced, rawRowCheck14714]

def rawRow14715 : Integer.Sparse Key := [(key622, 4), (key230, 4), (key622, 4), (key496, -2), (key618, -2), (key224, -2), (key618, -2), (key224, -2), (key496, -2), (key502, -2), (key622, -2), (key230, -2), (key622, -2), (key230, -2), (key502, -2), (key496, 4), (key224, 4), (key496, 4)]

theorem rawRowCheck14715 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form5 = rawRow14715 := by decide +kernel

def row14715 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

theorem rowCheck14715 : row14715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14715 := by decide +kernel

theorem rowEval14715 (x : Key → ℝ) : Integer.Sparse.eval row14715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14715, Integer.Sparse.eval_collectBalanced, rawRowCheck14715]

def rawRow14716 : Integer.Sparse Key := [(key622, 4), (key622, 4), (key230, 4), (key618, -2), (key496, -2), (key618, -2), (key224, -2), (key496, -2), (key224, -2), (key622, -2), (key502, -2), (key622, -2), (key230, -2), (key502, -2), (key230, -2), (key496, 4), (key496, 4), (key224, 4)]

theorem rawRowCheck14716 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form5 = rawRow14716 := by decide +kernel

def row14716 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

theorem rowCheck14716 : row14716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14716 := by decide +kernel

theorem rowEval14716 (x : Key → ℝ) : Integer.Sparse.eval row14716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14716, Integer.Sparse.eval_collectBalanced, rawRowCheck14716]

def rawRow14717 : Integer.Sparse Key := [(key502, 4), (key502, 4), (key502, 4), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key618, 4), (key618, 4), (key618, 4)]

theorem rawRowCheck14717 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form5 = rawRow14717 := by decide +kernel

def row14717 : Integer.Sparse Key := [(key496, -12), (key502, 12), (key618, 12), (key622, -12)]

theorem rowCheck14717 : row14717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14717 := by decide +kernel

theorem rowEval14717 (x : Key → ℝ) : Integer.Sparse.eval row14717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14717, Integer.Sparse.eval_collectBalanced, rawRowCheck14717]

def rawRow14718 : Integer.Sparse Key := [(key230, 4), (key622, 4), (key622, 4), (key230, -2), (key230, -2), (key502, -2), (key502, -2), (key622, -2), (key622, -2), (key224, -2), (key224, -2), (key496, -2), (key496, -2), (key618, -2), (key618, -2), (key224, 4), (key496, 4), (key496, 4)]

theorem rawRowCheck14718 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form5 = rawRow14718 := by decide +kernel

def row14718 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

theorem rowCheck14718 : row14718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14718 := by decide +kernel

theorem rowEval14718 (x : Key → ℝ) : Integer.Sparse.eval row14718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14718, Integer.Sparse.eval_collectBalanced, rawRowCheck14718]

def rawRow14719 : Integer.Sparse Key := [(key622, 4), (key230, 4), (key622, 4), (key502, -2), (key622, -2), (key230, -2), (key622, -2), (key230, -2), (key502, -2), (key496, -2), (key618, -2), (key224, -2), (key618, -2), (key224, -2), (key496, -2), (key496, 4), (key224, 4), (key496, 4)]

theorem rawRowCheck14719 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form5 = rawRow14719 := by decide +kernel

def row14719 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

theorem rowCheck14719 : row14719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14719 := by decide +kernel

theorem rowEval14719 (x : Key → ℝ) : Integer.Sparse.eval row14719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14719, Integer.Sparse.eval_collectBalanced, rawRowCheck14719]

end MUB6.Certificate.GramRows

end OAI
