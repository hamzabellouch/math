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

def rawRow11776 : Integer.Sparse Key := [(key2851, -2), (key2866, -2), (key2856, -2), (key2698, -2), (key2722, -2), (key2624, -2), (key2981, -2), (key2636, -2), (key2974, -2), (key2701, -2), (key2627, -2), (key2971, -2), (key2801, 1), (key2825, 1), (key2778, 1), (key2902, 1), (key2790, 1), (key2895, 1), (key2698, 1), (key2722, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2663, 1), (key2745, 1), (key2608, 1), (key2958, 1), (key2651, 1), (key2745, 1), (key2666, 1), (key2790, 1), (key2611, 1), (key2825, 1), (key2636, 1), (key2722, 1)]

theorem rawRowCheck11776 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form22 = rawRow11776 := by decide +kernel

def row11776 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 2), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11776 : row11776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11776 := by decide +kernel

theorem rowEval11776 (x : Key → ℝ) : Integer.Sparse.eval row11776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck11776, Integer.Sparse.eval_collectBalanced, rawRowCheck11776]

def rawRow11777 : Integer.Sparse Key := [(key2866, -2), (key2851, -2), (key2856, -2), (key2722, -2), (key2698, -2), (key2981, -2), (key2624, -2), (key2974, -2), (key2636, -2), (key2701, -2), (key2971, -2), (key2627, -2), (key2825, 1), (key2801, 1), (key2902, 1), (key2778, 1), (key2895, 1), (key2790, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2974, 1), (key2636, 1), (key2745, 1), (key2663, 1), (key2958, 1), (key2608, 1), (key2745, 1), (key2651, 1), (key2790, 1), (key2666, 1), (key2825, 1), (key2611, 1), (key2722, 1), (key2636, 1)]

theorem rawRowCheck11777 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form22 = rawRow11777 := by decide +kernel

def row11777 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 2), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11777 : row11777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11777 := by decide +kernel

theorem rowEval11777 (x : Key → ℝ) : Integer.Sparse.eval row11777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck11777, Integer.Sparse.eval_collectBalanced, rawRowCheck11777]

def rawRow11778 : Integer.Sparse Key := [(key2856, -2), (key2866, -2), (key2851, -2), (key2974, -2), (key2981, -2), (key2636, -2), (key2722, -2), (key2624, -2), (key2698, -2), (key2971, -2), (key2627, -2), (key2701, -2), (key2895, 1), (key2902, 1), (key2790, 1), (key2825, 1), (key2778, 1), (key2801, 1), (key2974, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2624, 1), (key2698, 1), (key2941, 1), (key2958, 1), (key2651, 1), (key2745, 1), (key2608, 1), (key2663, 1), (key2722, 1), (key2825, 1), (key2636, 1), (key2790, 1), (key2611, 1), (key2666, 1)]

theorem rawRowCheck11778 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form22 = rawRow11778 := by decide +kernel

def row11778 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 1), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11778 : row11778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11778 := by decide +kernel

theorem rowEval11778 (x : Key → ℝ) : Integer.Sparse.eval row11778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck11778, Integer.Sparse.eval_collectBalanced, rawRowCheck11778]

def rawRow11779 : Integer.Sparse Key := [(key2866, -2), (key2856, -2), (key2851, -2), (key2981, -2), (key2974, -2), (key2722, -2), (key2636, -2), (key2698, -2), (key2624, -2), (key2971, -2), (key2701, -2), (key2627, -2), (key2902, 1), (key2895, 1), (key2825, 1), (key2790, 1), (key2801, 1), (key2778, 1), (key2981, 1), (key2974, 1), (key2722, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2958, 1), (key2941, 1), (key2745, 1), (key2651, 1), (key2663, 1), (key2608, 1), (key2825, 1), (key2722, 1), (key2790, 1), (key2636, 1), (key2666, 1), (key2611, 1)]

theorem rawRowCheck11779 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form22 = rawRow11779 := by decide +kernel

def row11779 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 1), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11779 : row11779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11779 := by decide +kernel

theorem rowEval11779 (x : Key → ℝ) : Integer.Sparse.eval row11779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck11779, Integer.Sparse.eval_collectBalanced, rawRowCheck11779]

def rawRow11780 : Integer.Sparse Key := [(key2971, -2), (key2974, -2), (key2981, -2), (key2627, -2), (key2636, -2), (key2701, -2), (key2856, -2), (key2722, -2), (key2866, -2), (key2624, -2), (key2698, -2), (key2851, -2), (key2935, 1), (key2941, 1), (key2947, 1), (key2974, 1), (key2958, 1), (key2981, 1), (key2645, 1), (key2651, 1), (key2734, 1), (key2895, 1), (key2745, 1), (key2902, 1), (key2611, 1), (key2636, 1), (key2666, 1), (key2790, 1), (key2722, 1), (key2825, 1), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1)]

theorem rawRowCheck11780 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form22 = rawRow11780 := by decide +kernel

def row11780 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11780 : row11780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11780 := by decide +kernel

theorem rowEval11780 (x : Key → ℝ) : Integer.Sparse.eval row11780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck11780, Integer.Sparse.eval_collectBalanced, rawRowCheck11780]

def rawRow11781 : Integer.Sparse Key := [(key2974, -2), (key2971, -2), (key2981, -2), (key2636, -2), (key2627, -2), (key2856, -2), (key2701, -2), (key2866, -2), (key2722, -2), (key2624, -2), (key2851, -2), (key2698, -2), (key2941, 1), (key2935, 1), (key2974, 1), (key2947, 1), (key2981, 1), (key2958, 1), (key2651, 1), (key2645, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2745, 1), (key2636, 1), (key2611, 1), (key2790, 1), (key2666, 1), (key2825, 1), (key2722, 1), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1)]

theorem rawRowCheck11781 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form22 = rawRow11781 := by decide +kernel

def row11781 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11781 : row11781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11781 := by decide +kernel

theorem rowEval11781 (x : Key → ℝ) : Integer.Sparse.eval row11781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck11781, Integer.Sparse.eval_collectBalanced, rawRowCheck11781]

def rawRow11782 : Integer.Sparse Key := [(key2971, -2), (key2981, -2), (key2974, -2), (key2701, -2), (key2722, -2), (key2627, -2), (key2866, -2), (key2636, -2), (key2856, -2), (key2698, -2), (key2624, -2), (key2851, -2), (key2947, 1), (key2958, 1), (key2935, 1), (key2981, 1), (key2941, 1), (key2974, 1), (key2734, 1), (key2745, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2666, 1), (key2722, 1), (key2611, 1), (key2825, 1), (key2636, 1), (key2790, 1), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1)]

theorem rawRowCheck11782 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form22 = rawRow11782 := by decide +kernel

def row11782 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11782 : row11782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11782 := by decide +kernel

theorem rowEval11782 (x : Key → ℝ) : Integer.Sparse.eval row11782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck11782, Integer.Sparse.eval_collectBalanced, rawRowCheck11782]

def rawRow11783 : Integer.Sparse Key := [(key2981, -2), (key2971, -2), (key2974, -2), (key2722, -2), (key2701, -2), (key2866, -2), (key2627, -2), (key2856, -2), (key2636, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2958, 1), (key2947, 1), (key2981, 1), (key2935, 1), (key2974, 1), (key2941, 1), (key2745, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2895, 1), (key2651, 1), (key2722, 1), (key2666, 1), (key2825, 1), (key2611, 1), (key2790, 1), (key2636, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1)]

theorem rawRowCheck11783 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form22 = rawRow11783 := by decide +kernel

def row11783 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11783 : row11783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11783 := by decide +kernel

theorem rowEval11783 (x : Key → ℝ) : Integer.Sparse.eval row11783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck11783, Integer.Sparse.eval_collectBalanced, rawRowCheck11783]

def rawRow11784 : Integer.Sparse Key := [(key2974, -2), (key2981, -2), (key2971, -2), (key2856, -2), (key2866, -2), (key2636, -2), (key2722, -2), (key2627, -2), (key2701, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2974, 1), (key2981, 1), (key2941, 1), (key2958, 1), (key2935, 1), (key2947, 1), (key2895, 1), (key2902, 1), (key2651, 1), (key2745, 1), (key2645, 1), (key2734, 1), (key2790, 1), (key2825, 1), (key2636, 1), (key2722, 1), (key2611, 1), (key2666, 1), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1)]

theorem rawRowCheck11784 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form22 = rawRow11784 := by decide +kernel

def row11784 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11784 : row11784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11784 := by decide +kernel

theorem rowEval11784 (x : Key → ℝ) : Integer.Sparse.eval row11784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck11784, Integer.Sparse.eval_collectBalanced, rawRowCheck11784]

def rawRow11785 : Integer.Sparse Key := [(key2981, -2), (key2974, -2), (key2971, -2), (key2866, -2), (key2856, -2), (key2722, -2), (key2636, -2), (key2701, -2), (key2627, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2981, 1), (key2974, 1), (key2958, 1), (key2941, 1), (key2947, 1), (key2935, 1), (key2902, 1), (key2895, 1), (key2745, 1), (key2651, 1), (key2734, 1), (key2645, 1), (key2825, 1), (key2790, 1), (key2722, 1), (key2636, 1), (key2666, 1), (key2611, 1), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1)]

theorem rawRowCheck11785 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form22 = rawRow11785 := by decide +kernel

def row11785 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11785 : row11785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11785 := by decide +kernel

theorem rowEval11785 (x : Key → ℝ) : Integer.Sparse.eval row11785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck11785, Integer.Sparse.eval_collectBalanced, rawRowCheck11785]

def rawRow11786 : Integer.Sparse Key := [(key2457, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2460, 2), (key2460, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2525, 2), (key2532, -2), (key2532, -2), (key2533, -2), (key2532, -2), (key2532, -2), (key2562, -2), (key2562, -2), (key2564, -2), (key2564, -2), (key2533, -2), (key2564, -2), (key2564, -2)]

theorem rawRowCheck11786 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form0 = rawRow11786 := by decide +kernel

def row11786 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

theorem rowCheck11786 : row11786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11786 := by decide +kernel

theorem rowEval11786 (x : Key → ℝ) : Integer.Sparse.eval row11786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck11786, Integer.Sparse.eval_collectBalanced, rawRowCheck11786]

def rawRow11787 : Integer.Sparse Key := [(key2460, 2), (key2457, 2), (key2460, 2), (key2521, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2532, -2), (key2533, -2), (key2532, -2), (key2562, -2), (key2564, -2), (key2532, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2564, -2), (key2533, -2), (key2564, -2)]

theorem rawRowCheck11787 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form0 = rawRow11787 := by decide +kernel

def row11787 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

theorem rowCheck11787 : row11787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11787 := by decide +kernel

theorem rowEval11787 (x : Key → ℝ) : Integer.Sparse.eval row11787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck11787, Integer.Sparse.eval_collectBalanced, rawRowCheck11787]

def rawRow11788 : Integer.Sparse Key := [(key2460, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2457, 2), (key2525, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2460, 2), (key2533, -2), (key2532, -2), (key2532, -2), (key2564, -2), (key2562, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2532, -2), (key2564, -2), (key2564, -2), (key2533, -2)]

theorem rawRowCheck11788 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form0 = rawRow11788 := by decide +kernel

def row11788 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

theorem rowCheck11788 : row11788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11788 := by decide +kernel

theorem rowEval11788 (x : Key → ℝ) : Integer.Sparse.eval row11788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck11788, Integer.Sparse.eval_collectBalanced, rawRowCheck11788]

def rawRow11789 : Integer.Sparse Key := [(key2521, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2460, 2), (key2525, 2), (key2457, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2460, 2), (key2521, 2), (key2562, -2), (key2564, -2), (key2564, -2), (key2532, -2), (key2533, -2), (key2532, -2), (key2564, -2), (key2533, -2), (key2564, -2), (key2532, -2), (key2532, -2), (key2562, -2)]

theorem rawRowCheck11789 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form0 = rawRow11789 := by decide +kernel

def row11789 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

theorem rowCheck11789 : row11789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11789 := by decide +kernel

theorem rowEval11789 (x : Key → ℝ) : Integer.Sparse.eval row11789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck11789, Integer.Sparse.eval_collectBalanced, rawRowCheck11789]

def rawRow11790 : Integer.Sparse Key := [(key2521, 2), (key2525, 2), (key2521, 2), (key2460, 2), (key2525, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2457, 2), (key2521, 2), (key2460, 2), (key2564, -2), (key2562, -2), (key2564, -2), (key2533, -2), (key2532, -2), (key2564, -2), (key2532, -2), (key2564, -2), (key2533, -2), (key2532, -2), (key2562, -2), (key2532, -2)]

theorem rawRowCheck11790 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form0 = rawRow11790 := by decide +kernel

def row11790 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

theorem rowCheck11790 : row11790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11790 := by decide +kernel

theorem rowEval11790 (x : Key → ℝ) : Integer.Sparse.eval row11790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck11790, Integer.Sparse.eval_collectBalanced, rawRowCheck11790]

def rawRow11791 : Integer.Sparse Key := [(key2525, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2460, 2), (key2521, 2), (key2521, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2457, 2), (key2564, -2), (key2564, -2), (key2562, -2), (key2564, -2), (key2564, -2), (key2533, -2), (key2533, -2), (key2532, -2), (key2532, -2), (key2562, -2), (key2532, -2), (key2532, -2)]

theorem rawRowCheck11791 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form0 = rawRow11791 := by decide +kernel

def row11791 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

theorem rowCheck11791 : row11791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11791 := by decide +kernel

theorem rowEval11791 (x : Key → ℝ) : Integer.Sparse.eval row11791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck11791, Integer.Sparse.eval_collectBalanced, rawRowCheck11791]

def rawRow11792 : Integer.Sparse Key := [(key974, -24), (key1088, 6), (key1088, 6), (key1178, 6), (key1178, 6)]

theorem rawRowCheck11792 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form1 = rawRow11792 := by decide +kernel

def row11792 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

theorem rowCheck11792 : row11792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11792 := by decide +kernel

theorem rowEval11792 (x : Key → ℝ) : Integer.Sparse.eval row11792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11792, Integer.Sparse.eval_collectBalanced, rawRowCheck11792]

def rawRow11793 : Integer.Sparse Key := [(key974, -24), (key1088, 6), (key1178, 6), (key1088, 6), (key1178, 6)]

theorem rawRowCheck11793 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form1 = rawRow11793 := by decide +kernel

def row11793 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

theorem rowCheck11793 : row11793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11793 := by decide +kernel

theorem rowEval11793 (x : Key → ℝ) : Integer.Sparse.eval row11793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11793, Integer.Sparse.eval_collectBalanced, rawRowCheck11793]

def rawRow11794 : Integer.Sparse Key := [(key974, -24), (key1088, 6), (key1178, 6), (key1178, 6), (key1088, 6)]

theorem rawRowCheck11794 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form1 = rawRow11794 := by decide +kernel

def row11794 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

theorem rowCheck11794 : row11794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11794 := by decide +kernel

theorem rowEval11794 (x : Key → ℝ) : Integer.Sparse.eval row11794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11794, Integer.Sparse.eval_collectBalanced, rawRowCheck11794]

def rawRow11795 : Integer.Sparse Key := [(key974, -24), (key1178, 6), (key1088, 6), (key1088, 6), (key1178, 6)]

theorem rawRowCheck11795 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form1 = rawRow11795 := by decide +kernel

def row11795 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

theorem rowCheck11795 : row11795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11795 := by decide +kernel

theorem rowEval11795 (x : Key → ℝ) : Integer.Sparse.eval row11795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11795, Integer.Sparse.eval_collectBalanced, rawRowCheck11795]

def rawRow11796 : Integer.Sparse Key := [(key974, -24), (key1178, 6), (key1088, 6), (key1178, 6), (key1088, 6)]

theorem rawRowCheck11796 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form1 = rawRow11796 := by decide +kernel

def row11796 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

theorem rowCheck11796 : row11796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11796 := by decide +kernel

theorem rowEval11796 (x : Key → ℝ) : Integer.Sparse.eval row11796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11796, Integer.Sparse.eval_collectBalanced, rawRowCheck11796]

def rawRow11797 : Integer.Sparse Key := [(key974, -24), (key1178, 6), (key1178, 6), (key1088, 6), (key1088, 6)]

theorem rawRowCheck11797 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form1 = rawRow11797 := by decide +kernel

def row11797 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

theorem rowCheck11797 : row11797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11797 := by decide +kernel

theorem rowEval11797 (x : Key → ℝ) : Integer.Sparse.eval row11797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11797, Integer.Sparse.eval_collectBalanced, rawRowCheck11797]

def rawRow11798 : Integer.Sparse Key := [(key1088, -24), (key974, 6), (key1088, 6), (key1178, 6), (key1178, 6)]

theorem rawRowCheck11798 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form1 = rawRow11798 := by decide +kernel

def row11798 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

theorem rowCheck11798 : row11798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11798 := by decide +kernel

theorem rowEval11798 (x : Key → ℝ) : Integer.Sparse.eval row11798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11798, Integer.Sparse.eval_collectBalanced, rawRowCheck11798]

def rawRow11799 : Integer.Sparse Key := [(key1088, -24), (key974, 6), (key1178, 6), (key1088, 6), (key1178, 6)]

theorem rawRowCheck11799 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form1 = rawRow11799 := by decide +kernel

def row11799 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

theorem rowCheck11799 : row11799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11799 := by decide +kernel

theorem rowEval11799 (x : Key → ℝ) : Integer.Sparse.eval row11799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11799, Integer.Sparse.eval_collectBalanced, rawRowCheck11799]

def rawRow11800 : Integer.Sparse Key := [(key1088, -24), (key974, 6), (key1178, 6), (key1178, 6), (key1088, 6)]

theorem rawRowCheck11800 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form1 = rawRow11800 := by decide +kernel

def row11800 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

theorem rowCheck11800 : row11800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11800 := by decide +kernel

theorem rowEval11800 (x : Key → ℝ) : Integer.Sparse.eval row11800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11800, Integer.Sparse.eval_collectBalanced, rawRowCheck11800]

def rawRow11801 : Integer.Sparse Key := [(key1088, -24), (key1088, 6), (key974, 6), (key1178, 6), (key1178, 6)]

theorem rawRowCheck11801 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form1 = rawRow11801 := by decide +kernel

def row11801 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

theorem rowCheck11801 : row11801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11801 := by decide +kernel

theorem rowEval11801 (x : Key → ℝ) : Integer.Sparse.eval row11801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11801, Integer.Sparse.eval_collectBalanced, rawRowCheck11801]

def rawRow11802 : Integer.Sparse Key := [(key1088, -24), (key1088, 6), (key1178, 6), (key974, 6), (key1178, 6)]

theorem rawRowCheck11802 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form1 = rawRow11802 := by decide +kernel

def row11802 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

theorem rowCheck11802 : row11802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11802 := by decide +kernel

theorem rowEval11802 (x : Key → ℝ) : Integer.Sparse.eval row11802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11802, Integer.Sparse.eval_collectBalanced, rawRowCheck11802]

def rawRow11803 : Integer.Sparse Key := [(key1088, -24), (key1088, 6), (key1178, 6), (key1178, 6), (key974, 6)]

theorem rawRowCheck11803 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form1 = rawRow11803 := by decide +kernel

def row11803 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

theorem rowCheck11803 : row11803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11803 := by decide +kernel

theorem rowEval11803 (x : Key → ℝ) : Integer.Sparse.eval row11803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck11803, Integer.Sparse.eval_collectBalanced, rawRowCheck11803]

def rawRow11804 : Integer.Sparse Key := [(key1088, -24), (key1178, 6), (key974, 6), (key1088, 6), (key1178, 6)]

theorem rawRowCheck11804 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form1 = rawRow11804 := by decide +kernel

def row11804 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

theorem rowCheck11804 : row11804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11804 := by decide +kernel

theorem rowEval11804 (x : Key → ℝ) : Integer.Sparse.eval row11804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11804, Integer.Sparse.eval_collectBalanced, rawRowCheck11804]

def rawRow11805 : Integer.Sparse Key := [(key1088, -24), (key1178, 6), (key974, 6), (key1178, 6), (key1088, 6)]

theorem rawRowCheck11805 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form1 = rawRow11805 := by decide +kernel

def row11805 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

theorem rowCheck11805 : row11805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11805 := by decide +kernel

theorem rowEval11805 (x : Key → ℝ) : Integer.Sparse.eval row11805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11805, Integer.Sparse.eval_collectBalanced, rawRowCheck11805]

def rawRow11806 : Integer.Sparse Key := [(key1088, -24), (key1178, 6), (key1088, 6), (key974, 6), (key1178, 6)]

theorem rawRowCheck11806 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form1 = rawRow11806 := by decide +kernel

def row11806 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

theorem rowCheck11806 : row11806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11806 := by decide +kernel

theorem rowEval11806 (x : Key → ℝ) : Integer.Sparse.eval row11806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11806, Integer.Sparse.eval_collectBalanced, rawRowCheck11806]

def rawRow11807 : Integer.Sparse Key := [(key1088, -24), (key1178, 6), (key1088, 6), (key1178, 6), (key974, 6)]

theorem rawRowCheck11807 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form1 = rawRow11807 := by decide +kernel

def row11807 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

theorem rowCheck11807 : row11807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11807 := by decide +kernel

theorem rowEval11807 (x : Key → ℝ) : Integer.Sparse.eval row11807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck11807, Integer.Sparse.eval_collectBalanced, rawRowCheck11807]

def rawRow11808 : Integer.Sparse Key := [(key1088, -24), (key1178, 6), (key1178, 6), (key974, 6), (key1088, 6)]

theorem rawRowCheck11808 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form1 = rawRow11808 := by decide +kernel

def row11808 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

theorem rowCheck11808 : row11808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11808 := by decide +kernel

theorem rowEval11808 (x : Key → ℝ) : Integer.Sparse.eval row11808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11808, Integer.Sparse.eval_collectBalanced, rawRowCheck11808]

def rawRow11809 : Integer.Sparse Key := [(key1088, -24), (key1178, 6), (key1178, 6), (key1088, 6), (key974, 6)]

theorem rawRowCheck11809 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form1 = rawRow11809 := by decide +kernel

def row11809 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

theorem rowCheck11809 : row11809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11809 := by decide +kernel

theorem rowEval11809 (x : Key → ℝ) : Integer.Sparse.eval row11809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck11809, Integer.Sparse.eval_collectBalanced, rawRowCheck11809]

def rawRow11810 : Integer.Sparse Key := [(key976, -6), (key976, -6), (key984, -6), (key984, -6), (key1090, 2), (key1090, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1183, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key1183, 2)]

theorem rawRowCheck11810 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form2 = rawRow11810 := by decide +kernel

def row11810 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

theorem rowCheck11810 : row11810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11810 := by decide +kernel

theorem rowEval11810 (x : Key → ℝ) : Integer.Sparse.eval row11810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11810, Integer.Sparse.eval_collectBalanced, rawRowCheck11810]

def rawRow11811 : Integer.Sparse Key := [(key976, -6), (key984, -6), (key976, -6), (key984, -6), (key1090, 2), (key1098, 2), (key1090, 2), (key1180, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1183, 2), (key1098, 2), (key1183, 2)]

theorem rawRowCheck11811 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form2 = rawRow11811 := by decide +kernel

def row11811 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

theorem rowCheck11811 : row11811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11811 := by decide +kernel

theorem rowEval11811 (x : Key → ℝ) : Integer.Sparse.eval row11811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11811, Integer.Sparse.eval_collectBalanced, rawRowCheck11811]

def rawRow11812 : Integer.Sparse Key := [(key984, -6), (key976, -6), (key976, -6), (key984, -6), (key1098, 2), (key1090, 2), (key1090, 2), (key1183, 2), (key1180, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1183, 2), (key1183, 2), (key1098, 2)]

theorem rawRowCheck11812 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form2 = rawRow11812 := by decide +kernel

def row11812 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

theorem rowCheck11812 : row11812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11812 := by decide +kernel

theorem rowEval11812 (x : Key → ℝ) : Integer.Sparse.eval row11812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11812, Integer.Sparse.eval_collectBalanced, rawRowCheck11812]

def rawRow11813 : Integer.Sparse Key := [(key976, -6), (key984, -6), (key984, -6), (key976, -6), (key1180, 2), (key1183, 2), (key1183, 2), (key1090, 2), (key1098, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key1090, 2), (key1090, 2), (key1180, 2)]

theorem rawRowCheck11813 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form2 = rawRow11813 := by decide +kernel

def row11813 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

theorem rowCheck11813 : row11813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11813 := by decide +kernel

theorem rowEval11813 (x : Key → ℝ) : Integer.Sparse.eval row11813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11813, Integer.Sparse.eval_collectBalanced, rawRowCheck11813]

def rawRow11814 : Integer.Sparse Key := [(key984, -6), (key976, -6), (key984, -6), (key976, -6), (key1183, 2), (key1180, 2), (key1183, 2), (key1098, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1090, 2), (key1180, 2), (key1090, 2)]

theorem rawRowCheck11814 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form2 = rawRow11814 := by decide +kernel

def row11814 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

theorem rowCheck11814 : row11814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11814 := by decide +kernel

theorem rowEval11814 (x : Key → ℝ) : Integer.Sparse.eval row11814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11814, Integer.Sparse.eval_collectBalanced, rawRowCheck11814]

def rawRow11815 : Integer.Sparse Key := [(key984, -6), (key984, -6), (key976, -6), (key976, -6), (key1183, 2), (key1183, 2), (key1180, 2), (key1183, 2), (key1183, 2), (key1098, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1090, 2)]

theorem rawRowCheck11815 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form2 = rawRow11815 := by decide +kernel

def row11815 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

theorem rowCheck11815 : row11815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11815 := by decide +kernel

theorem rowEval11815 (x : Key → ℝ) : Integer.Sparse.eval row11815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11815, Integer.Sparse.eval_collectBalanced, rawRowCheck11815]

def rawRow11816 : Integer.Sparse Key := [(key1090, -6), (key1090, -6), (key1098, -6), (key1169, -6), (key976, 2), (key976, 2), (key984, 2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1183, 2), (key1183, 2), (key1169, 2), (key1220, 2), (key1220, 2)]

theorem rawRowCheck11816 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form2 = rawRow11816 := by decide +kernel

def row11816 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

theorem rowCheck11816 : row11816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11816 := by decide +kernel

theorem rowEval11816 (x : Key → ℝ) : Integer.Sparse.eval row11816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11816, Integer.Sparse.eval_collectBalanced, rawRowCheck11816]

def rawRow11817 : Integer.Sparse Key := [(key1090, -6), (key1098, -6), (key1090, -6), (key1169, -6), (key976, 2), (key984, 2), (key976, 2), (key1180, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1220, 2), (key1169, 2), (key1220, 2)]

theorem rawRowCheck11817 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form2 = rawRow11817 := by decide +kernel

def row11817 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

theorem rowCheck11817 : row11817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11817 := by decide +kernel

theorem rowEval11817 (x : Key → ℝ) : Integer.Sparse.eval row11817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11817, Integer.Sparse.eval_collectBalanced, rawRowCheck11817]

def rawRow11818 : Integer.Sparse Key := [(key1098, -6), (key1090, -6), (key1090, -6), (key1169, -6), (key984, 2), (key976, 2), (key976, 2), (key1183, 2), (key1180, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1220, 2), (key1220, 2), (key1169, 2)]

theorem rawRowCheck11818 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form2 = rawRow11818 := by decide +kernel

def row11818 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

theorem rowCheck11818 : row11818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11818 := by decide +kernel

theorem rowEval11818 (x : Key → ℝ) : Integer.Sparse.eval row11818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11818, Integer.Sparse.eval_collectBalanced, rawRowCheck11818]

def rawRow11819 : Integer.Sparse Key := [(key1090, -6), (key1090, -6), (key1169, -6), (key1098, -6), (key1090, 2), (key1090, 2), (key1169, 2), (key976, 2), (key976, 2), (key1180, 2), (key1180, 2), (key1220, 2), (key1220, 2), (key984, 2), (key1183, 2), (key1183, 2)]

theorem rawRowCheck11819 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form2 = rawRow11819 := by decide +kernel

def row11819 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

theorem rowCheck11819 : row11819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11819 := by decide +kernel

theorem rowEval11819 (x : Key → ℝ) : Integer.Sparse.eval row11819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11819, Integer.Sparse.eval_collectBalanced, rawRowCheck11819]

def rawRow11820 : Integer.Sparse Key := [(key1090, -6), (key1169, -6), (key1090, -6), (key1098, -6), (key1090, 2), (key1169, 2), (key1090, 2), (key1180, 2), (key1220, 2), (key976, 2), (key1220, 2), (key976, 2), (key1180, 2), (key1183, 2), (key984, 2), (key1183, 2)]

theorem rawRowCheck11820 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form2 = rawRow11820 := by decide +kernel

def row11820 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

theorem rowCheck11820 : row11820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11820 := by decide +kernel

theorem rowEval11820 (x : Key → ℝ) : Integer.Sparse.eval row11820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11820, Integer.Sparse.eval_collectBalanced, rawRowCheck11820]

def rawRow11821 : Integer.Sparse Key := [(key1169, -6), (key1090, -6), (key1090, -6), (key1098, -6), (key1169, 2), (key1090, 2), (key1090, 2), (key1220, 2), (key1180, 2), (key1220, 2), (key976, 2), (key1180, 2), (key976, 2), (key1183, 2), (key1183, 2), (key984, 2)]

theorem rawRowCheck11821 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form2 = rawRow11821 := by decide +kernel

def row11821 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

theorem rowCheck11821 : row11821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11821 := by decide +kernel

theorem rowEval11821 (x : Key → ℝ) : Integer.Sparse.eval row11821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck11821, Integer.Sparse.eval_collectBalanced, rawRowCheck11821]

def rawRow11822 : Integer.Sparse Key := [(key1090, -6), (key1098, -6), (key1169, -6), (key1090, -6), (key1180, 2), (key1183, 2), (key1220, 2), (key976, 2), (key984, 2), (key1090, 2), (key1183, 2), (key1169, 2), (key1220, 2), (key976, 2), (key1090, 2), (key1180, 2)]

theorem rawRowCheck11822 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form2 = rawRow11822 := by decide +kernel

def row11822 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

theorem rowCheck11822 : row11822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11822 := by decide +kernel

theorem rowEval11822 (x : Key → ℝ) : Integer.Sparse.eval row11822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11822, Integer.Sparse.eval_collectBalanced, rawRowCheck11822]

def rawRow11823 : Integer.Sparse Key := [(key1098, -6), (key1090, -6), (key1169, -6), (key1090, -6), (key1183, 2), (key1180, 2), (key1220, 2), (key984, 2), (key976, 2), (key1183, 2), (key1090, 2), (key1220, 2), (key1169, 2), (key976, 2), (key1180, 2), (key1090, 2)]

theorem rawRowCheck11823 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form2 = rawRow11823 := by decide +kernel

def row11823 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

theorem rowCheck11823 : row11823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11823 := by decide +kernel

theorem rowEval11823 (x : Key → ℝ) : Integer.Sparse.eval row11823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11823, Integer.Sparse.eval_collectBalanced, rawRowCheck11823]

def rawRow11824 : Integer.Sparse Key := [(key1090, -6), (key1169, -6), (key1098, -6), (key1090, -6), (key1180, 2), (key1220, 2), (key1183, 2), (key1090, 2), (key1169, 2), (key976, 2), (key1220, 2), (key984, 2), (key1183, 2), (key1090, 2), (key976, 2), (key1180, 2)]

theorem rawRowCheck11824 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form2 = rawRow11824 := by decide +kernel

def row11824 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

theorem rowCheck11824 : row11824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11824 := by decide +kernel

theorem rowEval11824 (x : Key → ℝ) : Integer.Sparse.eval row11824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11824, Integer.Sparse.eval_collectBalanced, rawRowCheck11824]

def rawRow11825 : Integer.Sparse Key := [(key1169, -6), (key1090, -6), (key1098, -6), (key1090, -6), (key1220, 2), (key1180, 2), (key1183, 2), (key1169, 2), (key1090, 2), (key1220, 2), (key976, 2), (key1183, 2), (key984, 2), (key1090, 2), (key1180, 2), (key976, 2)]

theorem rawRowCheck11825 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form2 = rawRow11825 := by decide +kernel

def row11825 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

theorem rowCheck11825 : row11825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11825 := by decide +kernel

theorem rowEval11825 (x : Key → ℝ) : Integer.Sparse.eval row11825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck11825, Integer.Sparse.eval_collectBalanced, rawRowCheck11825]

def rawRow11826 : Integer.Sparse Key := [(key1098, -6), (key1169, -6), (key1090, -6), (key1090, -6), (key1183, 2), (key1220, 2), (key1180, 2), (key1183, 2), (key1220, 2), (key984, 2), (key1169, 2), (key976, 2), (key1090, 2), (key1180, 2), (key976, 2), (key1090, 2)]

theorem rawRowCheck11826 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form2 = rawRow11826 := by decide +kernel

def row11826 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

theorem rowCheck11826 : row11826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11826 := by decide +kernel

theorem rowEval11826 (x : Key → ℝ) : Integer.Sparse.eval row11826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11826, Integer.Sparse.eval_collectBalanced, rawRowCheck11826]

def rawRow11827 : Integer.Sparse Key := [(key1169, -6), (key1098, -6), (key1090, -6), (key1090, -6), (key1220, 2), (key1183, 2), (key1180, 2), (key1220, 2), (key1183, 2), (key1169, 2), (key984, 2), (key1090, 2), (key976, 2), (key1180, 2), (key1090, 2), (key976, 2)]

theorem rawRowCheck11827 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form2 = rawRow11827 := by decide +kernel

def row11827 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

theorem rowCheck11827 : row11827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11827 := by decide +kernel

theorem rowEval11827 (x : Key → ℝ) : Integer.Sparse.eval row11827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck11827, Integer.Sparse.eval_collectBalanced, rawRowCheck11827]

def rawRow11828 : Integer.Sparse Key := [(key2405, -6), (key2405, -6), (key2436, -6), (key2436, -6), (key2471, 2), (key2479, 2), (key2479, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2479, 2), (key2479, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2518, 2)]

theorem rawRowCheck11828 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form3 = rawRow11828 := by decide +kernel

def row11828 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

theorem rowCheck11828 : row11828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11828 := by decide +kernel

theorem rowEval11828 (x : Key → ℝ) : Integer.Sparse.eval row11828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11828, Integer.Sparse.eval_collectBalanced, rawRowCheck11828]

def rawRow11829 : Integer.Sparse Key := [(key2405, -6), (key2436, -6), (key2405, -6), (key2436, -6), (key2479, 2), (key2471, 2), (key2479, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2518, 2), (key2479, 2), (key2502, 2)]

theorem rawRowCheck11829 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form3 = rawRow11829 := by decide +kernel

def row11829 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

theorem rowCheck11829 : row11829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11829 := by decide +kernel

theorem rowEval11829 (x : Key → ℝ) : Integer.Sparse.eval row11829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11829, Integer.Sparse.eval_collectBalanced, rawRowCheck11829]

def rawRow11830 : Integer.Sparse Key := [(key2405, -6), (key2436, -6), (key2436, -6), (key2405, -6), (key2479, 2), (key2479, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2471, 2), (key2518, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2502, 2), (key2479, 2)]

theorem rawRowCheck11830 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form3 = rawRow11830 := by decide +kernel

def row11830 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

theorem rowCheck11830 : row11830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11830 := by decide +kernel

theorem rowEval11830 (x : Key → ℝ) : Integer.Sparse.eval row11830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11830, Integer.Sparse.eval_collectBalanced, rawRowCheck11830]

def rawRow11831 : Integer.Sparse Key := [(key2436, -6), (key2405, -6), (key2405, -6), (key2436, -6), (key2502, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2479, 2), (key2518, 2), (key2471, 2), (key2479, 2), (key2471, 2), (key2502, 2), (key2479, 2), (key2502, 2)]

theorem rawRowCheck11831 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form3 = rawRow11831 := by decide +kernel

def row11831 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

theorem rowCheck11831 : row11831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11831 := by decide +kernel

theorem rowEval11831 (x : Key → ℝ) : Integer.Sparse.eval row11831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11831, Integer.Sparse.eval_collectBalanced, rawRowCheck11831]

def rawRow11832 : Integer.Sparse Key := [(key2436, -6), (key2405, -6), (key2436, -6), (key2405, -6), (key2502, 2), (key2518, 2), (key2502, 2), (key2479, 2), (key2518, 2), (key2479, 2), (key2479, 2), (key2471, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2479, 2)]

theorem rawRowCheck11832 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form3 = rawRow11832 := by decide +kernel

def row11832 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

theorem rowCheck11832 : row11832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11832 := by decide +kernel

theorem rowEval11832 (x : Key → ℝ) : Integer.Sparse.eval row11832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11832, Integer.Sparse.eval_collectBalanced, rawRowCheck11832]

def rawRow11833 : Integer.Sparse Key := [(key2436, -6), (key2436, -6), (key2405, -6), (key2405, -6), (key2518, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2479, 2), (key2502, 2), (key2502, 2), (key2479, 2), (key2479, 2), (key2471, 2), (key2471, 2)]

theorem rawRowCheck11833 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form3 = rawRow11833 := by decide +kernel

def row11833 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

theorem rowCheck11833 : row11833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11833 := by decide +kernel

theorem rowEval11833 (x : Key → ℝ) : Integer.Sparse.eval row11833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11833, Integer.Sparse.eval_collectBalanced, rawRowCheck11833]

def rawRow11834 : Integer.Sparse Key := [(key2377, -6), (key2471, -6), (key2502, -6), (key2502, -6), (key2377, 2), (key2389, 2), (key2389, 2), (key2405, 2), (key2436, 2), (key2436, 2), (key2479, 2), (key2479, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2518, 2)]

theorem rawRowCheck11834 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form3 = rawRow11834 := by decide +kernel

def row11834 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

theorem rowCheck11834 : row11834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11834 := by decide +kernel

theorem rowEval11834 (x : Key → ℝ) : Integer.Sparse.eval row11834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11834, Integer.Sparse.eval_collectBalanced, rawRowCheck11834]

def rawRow11835 : Integer.Sparse Key := [(key2377, -6), (key2502, -6), (key2471, -6), (key2502, -6), (key2389, 2), (key2377, 2), (key2389, 2), (key2436, 2), (key2405, 2), (key2436, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2518, 2), (key2479, 2), (key2502, 2)]

theorem rawRowCheck11835 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form3 = rawRow11835 := by decide +kernel

def row11835 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

theorem rowCheck11835 : row11835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11835 := by decide +kernel

theorem rowEval11835 (x : Key → ℝ) : Integer.Sparse.eval row11835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11835, Integer.Sparse.eval_collectBalanced, rawRowCheck11835]

def rawRow11836 : Integer.Sparse Key := [(key2377, -6), (key2502, -6), (key2502, -6), (key2471, -6), (key2389, 2), (key2389, 2), (key2377, 2), (key2436, 2), (key2436, 2), (key2405, 2), (key2518, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2502, 2), (key2479, 2)]

theorem rawRowCheck11836 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form3 = rawRow11836 := by decide +kernel

def row11836 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

theorem rowCheck11836 : row11836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11836 := by decide +kernel

theorem rowEval11836 (x : Key → ℝ) : Integer.Sparse.eval row11836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11836, Integer.Sparse.eval_collectBalanced, rawRowCheck11836]

def rawRow11837 : Integer.Sparse Key := [(key2471, -6), (key2377, -6), (key2502, -6), (key2502, -6), (key2405, 2), (key2479, 2), (key2479, 2), (key2377, 2), (key2502, 2), (key2502, 2), (key2389, 2), (key2389, 2), (key2436, 2), (key2436, 2), (key2518, 2), (key2518, 2)]

theorem rawRowCheck11837 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form3 = rawRow11837 := by decide +kernel

def row11837 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

theorem rowCheck11837 : row11837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11837 := by decide +kernel

theorem rowEval11837 (x : Key → ℝ) : Integer.Sparse.eval row11837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11837, Integer.Sparse.eval_collectBalanced, rawRowCheck11837]

def rawRow11838 : Integer.Sparse Key := [(key2471, -6), (key2502, -6), (key2377, -6), (key2502, -6), (key2479, 2), (key2405, 2), (key2479, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2436, 2), (key2518, 2), (key2389, 2), (key2518, 2), (key2389, 2), (key2436, 2)]

theorem rawRowCheck11838 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form3 = rawRow11838 := by decide +kernel

def row11838 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

theorem rowCheck11838 : row11838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11838 := by decide +kernel

theorem rowEval11838 (x : Key → ℝ) : Integer.Sparse.eval row11838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11838, Integer.Sparse.eval_collectBalanced, rawRowCheck11838]

def rawRow11839 : Integer.Sparse Key := [(key2471, -6), (key2502, -6), (key2502, -6), (key2377, -6), (key2479, 2), (key2479, 2), (key2405, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2518, 2), (key2436, 2), (key2518, 2), (key2389, 2), (key2436, 2), (key2389, 2)]

theorem rawRowCheck11839 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form3 = rawRow11839 := by decide +kernel

def row11839 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

theorem rowCheck11839 : row11839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11839 := by decide +kernel

theorem rowEval11839 (x : Key → ℝ) : Integer.Sparse.eval row11839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck11839, Integer.Sparse.eval_collectBalanced, rawRowCheck11839]

def rawRow11840 : Integer.Sparse Key := [(key2502, -6), (key2377, -6), (key2471, -6), (key2502, -6), (key2436, 2), (key2502, 2), (key2518, 2), (key2389, 2), (key2479, 2), (key2518, 2), (key2377, 2), (key2389, 2), (key2405, 2), (key2436, 2), (key2479, 2), (key2502, 2)]

theorem rawRowCheck11840 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form3 = rawRow11840 := by decide +kernel

def row11840 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

theorem rowCheck11840 : row11840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11840 := by decide +kernel

theorem rowEval11840 (x : Key → ℝ) : Integer.Sparse.eval row11840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11840, Integer.Sparse.eval_collectBalanced, rawRowCheck11840]

def rawRow11841 : Integer.Sparse Key := [(key2502, -6), (key2377, -6), (key2502, -6), (key2471, -6), (key2436, 2), (key2518, 2), (key2502, 2), (key2389, 2), (key2518, 2), (key2479, 2), (key2389, 2), (key2377, 2), (key2436, 2), (key2405, 2), (key2502, 2), (key2479, 2)]

theorem rawRowCheck11841 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form3 = rawRow11841 := by decide +kernel

def row11841 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

theorem rowCheck11841 : row11841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11841 := by decide +kernel

theorem rowEval11841 (x : Key → ℝ) : Integer.Sparse.eval row11841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11841, Integer.Sparse.eval_collectBalanced, rawRowCheck11841]

def rawRow11842 : Integer.Sparse Key := [(key2502, -6), (key2471, -6), (key2377, -6), (key2502, -6), (key2502, 2), (key2436, 2), (key2518, 2), (key2479, 2), (key2389, 2), (key2518, 2), (key2405, 2), (key2479, 2), (key2377, 2), (key2502, 2), (key2389, 2), (key2436, 2)]

theorem rawRowCheck11842 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form3 = rawRow11842 := by decide +kernel

def row11842 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

theorem rowCheck11842 : row11842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11842 := by decide +kernel

theorem rowEval11842 (x : Key → ℝ) : Integer.Sparse.eval row11842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11842, Integer.Sparse.eval_collectBalanced, rawRowCheck11842]

def rawRow11843 : Integer.Sparse Key := [(key2502, -6), (key2471, -6), (key2502, -6), (key2377, -6), (key2502, 2), (key2518, 2), (key2436, 2), (key2479, 2), (key2518, 2), (key2389, 2), (key2479, 2), (key2405, 2), (key2502, 2), (key2377, 2), (key2436, 2), (key2389, 2)]

theorem rawRowCheck11843 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form3 = rawRow11843 := by decide +kernel

def row11843 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

theorem rowCheck11843 : row11843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11843 := by decide +kernel

theorem rowEval11843 (x : Key → ℝ) : Integer.Sparse.eval row11843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck11843, Integer.Sparse.eval_collectBalanced, rawRowCheck11843]

def rawRow11844 : Integer.Sparse Key := [(key2502, -6), (key2502, -6), (key2377, -6), (key2471, -6), (key2518, 2), (key2436, 2), (key2502, 2), (key2518, 2), (key2389, 2), (key2479, 2), (key2436, 2), (key2502, 2), (key2389, 2), (key2479, 2), (key2377, 2), (key2405, 2)]

theorem rawRowCheck11844 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form3 = rawRow11844 := by decide +kernel

def row11844 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

theorem rowCheck11844 : row11844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11844 := by decide +kernel

theorem rowEval11844 (x : Key → ℝ) : Integer.Sparse.eval row11844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11844, Integer.Sparse.eval_collectBalanced, rawRowCheck11844]

def rawRow11845 : Integer.Sparse Key := [(key2502, -6), (key2502, -6), (key2471, -6), (key2377, -6), (key2518, 2), (key2502, 2), (key2436, 2), (key2518, 2), (key2479, 2), (key2389, 2), (key2502, 2), (key2436, 2), (key2479, 2), (key2389, 2), (key2405, 2), (key2377, 2)]

theorem rawRowCheck11845 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form3 = rawRow11845 := by decide +kernel

def row11845 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

theorem rowCheck11845 : row11845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11845 := by decide +kernel

theorem rowEval11845 (x : Key → ℝ) : Integer.Sparse.eval row11845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck11845, Integer.Sparse.eval_collectBalanced, rawRowCheck11845]

def rawRow11846 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2366, -6), (key2366, -6), (key2456, 2), (key2456, 2), (key2461, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2523, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2523, 2)]

theorem rawRowCheck11846 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form4 = rawRow11846 := by decide +kernel

def row11846 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2366, -12), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

theorem rowCheck11846 : row11846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11846 := by decide +kernel

theorem rowEval11846 (x : Key → ℝ) : Integer.Sparse.eval row11846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11846, Integer.Sparse.eval_collectBalanced, rawRowCheck11846]

def rawRow11847 : Integer.Sparse Key := [(key2357, -6), (key2363, -6), (key2361, -6), (key2366, -6), (key2456, 2), (key2461, 2), (key2456, 2), (key2517, 2), (key2523, 2), (key2456, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2523, 2), (key2461, 2), (key2523, 2)]

theorem rawRowCheck11847 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form4 = rawRow11847 := by decide +kernel

def row11847 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2363, -6), (key2366, -6), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

theorem rowCheck11847 : row11847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11847 := by decide +kernel

theorem rowEval11847 (x : Key → ℝ) : Integer.Sparse.eval row11847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11847, Integer.Sparse.eval_collectBalanced, rawRowCheck11847]

def rawRow11848 : Integer.Sparse Key := [(key2363, -6), (key2357, -6), (key2361, -6), (key2366, -6), (key2461, 2), (key2456, 2), (key2456, 2), (key2523, 2), (key2517, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2523, 2), (key2523, 2), (key2461, 2)]

theorem rawRowCheck11848 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form4 = rawRow11848 := by decide +kernel

def row11848 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2363, -6), (key2366, -6), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

theorem rowCheck11848 : row11848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11848 := by decide +kernel

theorem rowEval11848 (x : Key → ℝ) : Integer.Sparse.eval row11848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11848, Integer.Sparse.eval_collectBalanced, rawRowCheck11848]

def rawRow11849 : Integer.Sparse Key := [(key2357, -6), (key2363, -6), (key2363, -6), (key2361, -6), (key2517, 2), (key2523, 2), (key2523, 2), (key2456, 2), (key2461, 2), (key2456, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2456, 2), (key2456, 2), (key2517, 2)]

theorem rawRowCheck11849 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form4 = rawRow11849 := by decide +kernel

def row11849 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2363, -12), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

theorem rowCheck11849 : row11849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11849 := by decide +kernel

theorem rowEval11849 (x : Key → ℝ) : Integer.Sparse.eval row11849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11849, Integer.Sparse.eval_collectBalanced, rawRowCheck11849]

def rawRow11850 : Integer.Sparse Key := [(key2363, -6), (key2357, -6), (key2363, -6), (key2361, -6), (key2523, 2), (key2517, 2), (key2523, 2), (key2461, 2), (key2456, 2), (key2523, 2), (key2456, 2), (key2523, 2), (key2461, 2), (key2456, 2), (key2517, 2), (key2456, 2)]

theorem rawRowCheck11850 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form4 = rawRow11850 := by decide +kernel

def row11850 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2363, -12), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

theorem rowCheck11850 : row11850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11850 := by decide +kernel

theorem rowEval11850 (x : Key → ℝ) : Integer.Sparse.eval row11850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11850, Integer.Sparse.eval_collectBalanced, rawRowCheck11850]

def rawRow11851 : Integer.Sparse Key := [(key2363, -6), (key2363, -6), (key2357, -6), (key2361, -6), (key2523, 2), (key2523, 2), (key2517, 2), (key2523, 2), (key2523, 2), (key2461, 2), (key2461, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2456, 2)]

theorem rawRowCheck11851 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form4 = rawRow11851 := by decide +kernel

def row11851 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2363, -12), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

theorem rowCheck11851 : row11851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11851 := by decide +kernel

theorem rowEval11851 (x : Key → ℝ) : Integer.Sparse.eval row11851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11851, Integer.Sparse.eval_collectBalanced, rawRowCheck11851]

def rawRow11852 : Integer.Sparse Key := [(key2452, -6), (key2452, -6), (key2458, -6), (key2519, -6), (key2357, 2), (key2361, 2), (key2366, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2523, 2), (key2523, 2), (key2567, 2), (key2579, 2), (key2579, 2)]

theorem rawRowCheck11852 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form4 = rawRow11852 := by decide +kernel

def row11852 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2366, 2), (key2452, -12), (key2456, 4), (key2458, -6), (key2517, 4), (key2519, -6), (key2523, 4), (key2567, 2), (key2579, 4)]

theorem rowCheck11852 : row11852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11852 := by decide +kernel

theorem rowEval11852 (x : Key → ℝ) : Integer.Sparse.eval row11852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11852, Integer.Sparse.eval_collectBalanced, rawRowCheck11852]

def rawRow11853 : Integer.Sparse Key := [(key2452, -6), (key2458, -6), (key2452, -6), (key2519, -6), (key2357, 2), (key2363, 2), (key2361, 2), (key2517, 2), (key2523, 2), (key2456, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2579, 2), (key2567, 2), (key2579, 2)]

theorem rawRowCheck11853 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form4 = rawRow11853 := by decide +kernel

def row11853 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -12), (key2456, 4), (key2458, -6), (key2517, 4), (key2519, -6), (key2523, 4), (key2567, 2), (key2579, 4)]

theorem rowCheck11853 : row11853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11853 := by decide +kernel

theorem rowEval11853 (x : Key → ℝ) : Integer.Sparse.eval row11853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11853, Integer.Sparse.eval_collectBalanced, rawRowCheck11853]

def rawRow11854 : Integer.Sparse Key := [(key2458, -6), (key2452, -6), (key2452, -6), (key2519, -6), (key2363, 2), (key2357, 2), (key2361, 2), (key2523, 2), (key2517, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2579, 2), (key2579, 2), (key2567, 2)]

theorem rawRowCheck11854 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form4 = rawRow11854 := by decide +kernel

def row11854 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -12), (key2456, 4), (key2458, -6), (key2517, 4), (key2519, -6), (key2523, 4), (key2567, 2), (key2579, 4)]

theorem rowCheck11854 : row11854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11854 := by decide +kernel

theorem rowEval11854 (x : Key → ℝ) : Integer.Sparse.eval row11854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11854, Integer.Sparse.eval_collectBalanced, rawRowCheck11854]

def rawRow11855 : Integer.Sparse Key := [(key2452, -6), (key2452, -6), (key2519, -6), (key2458, -6), (key2452, 2), (key2452, 2), (key2519, 2), (key2357, 2), (key2361, 2), (key2517, 2), (key2517, 2), (key2579, 2), (key2579, 2), (key2366, 2), (key2523, 2), (key2523, 2)]

theorem rawRowCheck11855 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form4 = rawRow11855 := by decide +kernel

def row11855 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2366, 2), (key2452, -8), (key2458, -6), (key2517, 4), (key2519, -4), (key2523, 4), (key2579, 4)]

theorem rowCheck11855 : row11855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11855 := by decide +kernel

theorem rowEval11855 (x : Key → ℝ) : Integer.Sparse.eval row11855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11855, Integer.Sparse.eval_collectBalanced, rawRowCheck11855]

def rawRow11856 : Integer.Sparse Key := [(key2452, -6), (key2519, -6), (key2452, -6), (key2458, -6), (key2452, 2), (key2519, 2), (key2452, 2), (key2528, 2), (key2560, 2), (key2357, 2), (key2560, 2), (key2361, 2), (key2517, 2), (key2523, 2), (key2366, 2), (key2523, 2)]

theorem rawRowCheck11856 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form4 = rawRow11856 := by decide +kernel

def row11856 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2366, 2), (key2452, -8), (key2458, -6), (key2517, 2), (key2519, -4), (key2523, 4), (key2528, 2), (key2560, 4)]

theorem rowCheck11856 : row11856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11856 := by decide +kernel

theorem rowEval11856 (x : Key → ℝ) : Integer.Sparse.eval row11856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11856, Integer.Sparse.eval_collectBalanced, rawRowCheck11856]

def rawRow11857 : Integer.Sparse Key := [(key2519, -6), (key2452, -6), (key2452, -6), (key2458, -6), (key2519, 2), (key2452, 2), (key2452, 2), (key2560, 2), (key2528, 2), (key2560, 2), (key2357, 2), (key2517, 2), (key2361, 2), (key2523, 2), (key2523, 2), (key2366, 2)]

theorem rawRowCheck11857 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form4 = rawRow11857 := by decide +kernel

def row11857 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2366, 2), (key2452, -8), (key2458, -6), (key2517, 2), (key2519, -4), (key2523, 4), (key2528, 2), (key2560, 4)]

theorem rowCheck11857 : row11857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11857 := by decide +kernel

theorem rowEval11857 (x : Key → ℝ) : Integer.Sparse.eval row11857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck11857, Integer.Sparse.eval_collectBalanced, rawRowCheck11857]

def rawRow11858 : Integer.Sparse Key := [(key2452, -6), (key2458, -6), (key2519, -6), (key2452, -6), (key2528, 2), (key2530, 2), (key2560, 2), (key2357, 2), (key2363, 2), (key2452, 2), (key2530, 2), (key2519, 2), (key2560, 2), (key2361, 2), (key2456, 2), (key2517, 2)]

theorem rawRowCheck11858 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form4 = rawRow11858 := by decide +kernel

def row11858 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

theorem rowCheck11858 : row11858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11858 := by decide +kernel

theorem rowEval11858 (x : Key → ℝ) : Integer.Sparse.eval row11858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11858, Integer.Sparse.eval_collectBalanced, rawRowCheck11858]

def rawRow11859 : Integer.Sparse Key := [(key2458, -6), (key2452, -6), (key2519, -6), (key2452, -6), (key2530, 2), (key2528, 2), (key2560, 2), (key2363, 2), (key2357, 2), (key2530, 2), (key2452, 2), (key2560, 2), (key2519, 2), (key2361, 2), (key2517, 2), (key2456, 2)]

theorem rawRowCheck11859 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form4 = rawRow11859 := by decide +kernel

def row11859 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

theorem rowCheck11859 : row11859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11859 := by decide +kernel

theorem rowEval11859 (x : Key → ℝ) : Integer.Sparse.eval row11859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11859, Integer.Sparse.eval_collectBalanced, rawRowCheck11859]

def rawRow11860 : Integer.Sparse Key := [(key2452, -6), (key2519, -6), (key2458, -6), (key2452, -6), (key2528, 2), (key2560, 2), (key2530, 2), (key2452, 2), (key2519, 2), (key2357, 2), (key2560, 2), (key2363, 2), (key2530, 2), (key2456, 2), (key2361, 2), (key2517, 2)]

theorem rawRowCheck11860 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form4 = rawRow11860 := by decide +kernel

def row11860 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

theorem rowCheck11860 : row11860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11860 := by decide +kernel

theorem rowEval11860 (x : Key → ℝ) : Integer.Sparse.eval row11860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11860, Integer.Sparse.eval_collectBalanced, rawRowCheck11860]

def rawRow11861 : Integer.Sparse Key := [(key2519, -6), (key2452, -6), (key2458, -6), (key2452, -6), (key2560, 2), (key2528, 2), (key2530, 2), (key2519, 2), (key2452, 2), (key2560, 2), (key2357, 2), (key2530, 2), (key2363, 2), (key2456, 2), (key2517, 2), (key2361, 2)]

theorem rawRowCheck11861 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form4 = rawRow11861 := by decide +kernel

def row11861 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

theorem rowCheck11861 : row11861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11861 := by decide +kernel

theorem rowEval11861 (x : Key → ℝ) : Integer.Sparse.eval row11861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck11861, Integer.Sparse.eval_collectBalanced, rawRowCheck11861]

def rawRow11862 : Integer.Sparse Key := [(key2458, -6), (key2519, -6), (key2452, -6), (key2452, -6), (key2530, 2), (key2560, 2), (key2528, 2), (key2530, 2), (key2560, 2), (key2363, 2), (key2519, 2), (key2357, 2), (key2452, 2), (key2517, 2), (key2361, 2), (key2456, 2)]

theorem rawRowCheck11862 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form4 = rawRow11862 := by decide +kernel

def row11862 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

theorem rowCheck11862 : row11862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11862 := by decide +kernel

theorem rowEval11862 (x : Key → ℝ) : Integer.Sparse.eval row11862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11862, Integer.Sparse.eval_collectBalanced, rawRowCheck11862]

def rawRow11863 : Integer.Sparse Key := [(key2519, -6), (key2458, -6), (key2452, -6), (key2452, -6), (key2560, 2), (key2530, 2), (key2528, 2), (key2560, 2), (key2530, 2), (key2519, 2), (key2363, 2), (key2452, 2), (key2357, 2), (key2517, 2), (key2456, 2), (key2361, 2)]

theorem rawRowCheck11863 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form4 = rawRow11863 := by decide +kernel

def row11863 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

theorem rowCheck11863 : row11863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11863 := by decide +kernel

theorem rowEval11863 (x : Key → ℝ) : Integer.Sparse.eval row11863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck11863, Integer.Sparse.eval_collectBalanced, rawRowCheck11863]

def rawRow11864 : Integer.Sparse Key := [(key2406, -2), (key2406, -2), (key2411, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2437, -2), (key2443, -2), (key2443, -2), (key2411, -2), (key2443, -2), (key2443, -2), (key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2509, 1), (key2509, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2509, 1), (key2509, 1), (key2524, 1), (key2524, 1)]

theorem rawRowCheck11864 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form5 = rawRow11864 := by decide +kernel

def row11864 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

theorem rowCheck11864 : row11864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11864 := by decide +kernel

theorem rowEval11864 (x : Key → ℝ) : Integer.Sparse.eval row11864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck11864, Integer.Sparse.eval_collectBalanced, rawRowCheck11864]

def rawRow11865 : Integer.Sparse Key := [(key2406, -2), (key2411, -2), (key2406, -2), (key2437, -2), (key2443, -2), (key2406, -2), (key2443, -2), (key2406, -2), (key2437, -2), (key2443, -2), (key2411, -2), (key2443, -2), (key2480, 1), (key2484, 1), (key2472, 1), (key2484, 1), (key2472, 1), (key2480, 1), (key2503, 1), (key2509, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2509, 1), (key2524, 1), (key2484, 1), (key2524, 1), (key2484, 1), (key2509, 1)]

theorem rawRowCheck11865 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form5 = rawRow11865 := by decide +kernel

def row11865 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

theorem rowCheck11865 : row11865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11865 := by decide +kernel

theorem rowEval11865 (x : Key → ℝ) : Integer.Sparse.eval row11865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck11865, Integer.Sparse.eval_collectBalanced, rawRowCheck11865]

def rawRow11866 : Integer.Sparse Key := [(key2411, -2), (key2406, -2), (key2406, -2), (key2443, -2), (key2437, -2), (key2443, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2443, -2), (key2443, -2), (key2411, -2), (key2484, 1), (key2480, 1), (key2484, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2509, 1), (key2503, 1), (key2509, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2524, 1), (key2509, 1), (key2524, 1), (key2484, 1), (key2509, 1), (key2484, 1)]

theorem rawRowCheck11866 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form5 = rawRow11866 := by decide +kernel

def row11866 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

theorem rowCheck11866 : row11866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11866 := by decide +kernel

theorem rowEval11866 (x : Key → ℝ) : Integer.Sparse.eval row11866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck11866, Integer.Sparse.eval_collectBalanced, rawRowCheck11866]

def rawRow11867 : Integer.Sparse Key := [(key2437, -2), (key2443, -2), (key2443, -2), (key2406, -2), (key2411, -2), (key2406, -2), (key2443, -2), (key2411, -2), (key2443, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2503, 1), (key2509, 1), (key2503, 1), (key2524, 1), (key2509, 1), (key2524, 1), (key2480, 1), (key2484, 1), (key2480, 1), (key2524, 1), (key2484, 1), (key2524, 1), (key2472, 1), (key2484, 1), (key2472, 1), (key2509, 1), (key2484, 1), (key2509, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2503, 1)]

theorem rawRowCheck11867 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form5 = rawRow11867 := by decide +kernel

def row11867 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

theorem rowCheck11867 : row11867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11867 := by decide +kernel

theorem rowEval11867 (x : Key → ℝ) : Integer.Sparse.eval row11867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck11867, Integer.Sparse.eval_collectBalanced, rawRowCheck11867]

def rawRow11868 : Integer.Sparse Key := [(key2443, -2), (key2437, -2), (key2443, -2), (key2411, -2), (key2406, -2), (key2443, -2), (key2406, -2), (key2443, -2), (key2411, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2509, 1), (key2503, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2509, 1), (key2484, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2509, 1), (key2484, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2503, 1), (key2480, 1)]

theorem rawRowCheck11868 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form5 = rawRow11868 := by decide +kernel

def row11868 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

theorem rowCheck11868 : row11868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11868 := by decide +kernel

theorem rowEval11868 (x : Key → ℝ) : Integer.Sparse.eval row11868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck11868, Integer.Sparse.eval_collectBalanced, rawRowCheck11868]

def rawRow11869 : Integer.Sparse Key := [(key2443, -2), (key2443, -2), (key2437, -2), (key2443, -2), (key2443, -2), (key2411, -2), (key2411, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2406, -2), (key2524, 1), (key2524, 1), (key2509, 1), (key2509, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2480, 1), (key2480, 1), (key2509, 1), (key2509, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2480, 1), (key2480, 1), (key2472, 1), (key2472, 1)]

theorem rawRowCheck11869 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form5 = rawRow11869 := by decide +kernel

def row11869 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

theorem rowCheck11869 : row11869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11869 := by decide +kernel

theorem rowEval11869 (x : Key → ℝ) : Integer.Sparse.eval row11869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck11869, Integer.Sparse.eval_collectBalanced, rawRowCheck11869]

def rawRow11870 : Integer.Sparse Key := [(key2587, -2), (key2587, -2), (key2593, -2), (key2843, -2), (key2843, -2), (key2966, -2), (key2966, -2), (key2968, -2), (key2968, -2), (key2880, -2), (key2989, -2), (key2989, -2), (key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2394, 1), (key2394, 1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2443, 1), (key2443, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2571, 1), (key2571, 1), (key2576, 1), (key2576, 1), (key2580, 1), (key2580, 1)]

theorem rawRowCheck11870 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form5 = rawRow11870 := by decide +kernel

def row11870 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -4), (key2593, -2), (key2843, -4), (key2880, -2), (key2966, -4), (key2968, -4), (key2989, -4)]

theorem rowCheck11870 : row11870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11870 := by decide +kernel

theorem rowEval11870 (x : Key → ℝ) : Integer.Sparse.eval row11870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck11870, Integer.Sparse.eval_collectBalanced, rawRowCheck11870]

def rawRow11871 : Integer.Sparse Key := [(key2587, -2), (key2593, -2), (key2587, -2), (key2966, -2), (key2968, -2), (key2843, -2), (key2968, -2), (key2843, -2), (key2966, -2), (key2989, -2), (key2880, -2), (key2989, -2), (key2390, 1), (key2394, 1), (key2378, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2437, 1), (key2443, 1), (key2406, 1), (key2443, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2576, 1), (key2580, 1), (key2571, 1), (key2580, 1), (key2571, 1), (key2576, 1)]

theorem rawRowCheck11871 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form5 = rawRow11871 := by decide +kernel

def row11871 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -4), (key2593, -2), (key2843, -4), (key2880, -2), (key2966, -4), (key2968, -4), (key2989, -4)]

theorem rowCheck11871 : row11871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11871 := by decide +kernel

theorem rowEval11871 (x : Key → ℝ) : Integer.Sparse.eval row11871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck11871, Integer.Sparse.eval_collectBalanced, rawRowCheck11871]

def rawRow11872 : Integer.Sparse Key := [(key2593, -2), (key2587, -2), (key2587, -2), (key2968, -2), (key2966, -2), (key2968, -2), (key2843, -2), (key2966, -2), (key2843, -2), (key2989, -2), (key2989, -2), (key2880, -2), (key2394, 1), (key2390, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2443, 1), (key2437, 1), (key2443, 1), (key2406, 1), (key2437, 1), (key2406, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2580, 1), (key2576, 1), (key2580, 1), (key2571, 1), (key2576, 1), (key2571, 1)]

theorem rawRowCheck11872 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form5 = rawRow11872 := by decide +kernel

def row11872 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -4), (key2593, -2), (key2843, -4), (key2880, -2), (key2966, -4), (key2968, -4), (key2989, -4)]

theorem rowCheck11872 : row11872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11872 := by decide +kernel

theorem rowEval11872 (x : Key → ℝ) : Integer.Sparse.eval row11872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck11872, Integer.Sparse.eval_collectBalanced, rawRowCheck11872]

def rawRow11873 : Integer.Sparse Key := [(key2843, -2), (key2843, -2), (key2880, -2), (key2587, -2), (key2587, -2), (key2966, -2), (key2966, -2), (key2989, -2), (key2989, -2), (key2593, -2), (key2968, -2), (key2968, -2), (key2766, 1), (key2766, 1), (key2887, 1), (key2887, 1), (key2910, 1), (key2910, 1), (key2587, 1), (key2587, 1), (key2966, 1), (key2966, 1), (key2989, 1), (key2989, 1), (key2390, 1), (key2390, 1), (key2437, 1), (key2437, 1), (key2580, 1), (key2580, 1), (key2394, 1), (key2394, 1), (key2443, 1), (key2443, 1), (key2524, 1), (key2524, 1)]

theorem rawRowCheck11873 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form5 = rawRow11873 := by decide +kernel

def row11873 : Integer.Sparse Key := [(key2390, 2), (key2394, 2), (key2437, 2), (key2443, 2), (key2524, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2766, 2), (key2843, -4), (key2880, -2), (key2887, 2), (key2910, 2), (key2966, -2), (key2968, -4), (key2989, -2)]

theorem rowCheck11873 : row11873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11873 := by decide +kernel

theorem rowEval11873 (x : Key → ℝ) : Integer.Sparse.eval row11873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck11873, Integer.Sparse.eval_collectBalanced, rawRowCheck11873]

def rawRow11874 : Integer.Sparse Key := [(key2843, -2), (key2880, -2), (key2843, -2), (key2966, -2), (key2989, -2), (key2587, -2), (key2989, -2), (key2587, -2), (key2966, -2), (key2968, -2), (key2593, -2), (key2968, -2), (key2887, 1), (key2910, 1), (key2766, 1), (key2910, 1), (key2766, 1), (key2887, 1), (key2966, 1), (key2989, 1), (key2587, 1), (key2989, 1), (key2587, 1), (key2966, 1), (key2929, 1), (key3002, 1), (key2598, 1), (key3002, 1), (key2390, 1), (key2437, 1), (key2443, 1), (key2524, 1), (key2394, 1), (key2524, 1), (key2394, 1), (key2443, 1)]

theorem rawRowCheck11874 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form5 = rawRow11874 := by decide +kernel

def row11874 : Integer.Sparse Key := [(key2390, 1), (key2394, 2), (key2437, 1), (key2443, 2), (key2524, 2), (key2587, -2), (key2593, -2), (key2598, 1), (key2766, 2), (key2843, -4), (key2880, -2), (key2887, 2), (key2910, 2), (key2929, 1), (key2966, -2), (key2968, -4), (key2989, -2), (key3002, 2)]

theorem rowCheck11874 : row11874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11874 := by decide +kernel

theorem rowEval11874 (x : Key → ℝ) : Integer.Sparse.eval row11874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck11874, Integer.Sparse.eval_collectBalanced, rawRowCheck11874]

def rawRow11875 : Integer.Sparse Key := [(key2880, -2), (key2843, -2), (key2843, -2), (key2989, -2), (key2966, -2), (key2989, -2), (key2587, -2), (key2966, -2), (key2587, -2), (key2968, -2), (key2968, -2), (key2593, -2), (key2910, 1), (key2887, 1), (key2910, 1), (key2766, 1), (key2887, 1), (key2766, 1), (key2989, 1), (key2966, 1), (key2989, 1), (key2587, 1), (key2966, 1), (key2587, 1), (key3002, 1), (key2929, 1), (key3002, 1), (key2598, 1), (key2437, 1), (key2390, 1), (key2524, 1), (key2443, 1), (key2524, 1), (key2394, 1), (key2443, 1), (key2394, 1)]

theorem rawRowCheck11875 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form5 = rawRow11875 := by decide +kernel

def row11875 : Integer.Sparse Key := [(key2390, 1), (key2394, 2), (key2437, 1), (key2443, 2), (key2524, 2), (key2587, -2), (key2593, -2), (key2598, 1), (key2766, 2), (key2843, -4), (key2880, -2), (key2887, 2), (key2910, 2), (key2929, 1), (key2966, -2), (key2968, -4), (key2989, -2), (key3002, 2)]

theorem rowCheck11875 : row11875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11875 := by decide +kernel

theorem rowEval11875 (x : Key → ℝ) : Integer.Sparse.eval row11875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck11875, Integer.Sparse.eval_collectBalanced, rawRowCheck11875]

def rawRow11876 : Integer.Sparse Key := [(key2966, -2), (key2968, -2), (key2989, -2), (key2587, -2), (key2593, -2), (key2843, -2), (key2968, -2), (key2880, -2), (key2989, -2), (key2587, -2), (key2843, -2), (key2966, -2), (key2929, 1), (key2931, 1), (key2966, 1), (key2995, 1), (key2989, 1), (key3002, 1), (key2598, 1), (key2600, 1), (key2887, 1), (key2995, 1), (key2910, 1), (key3002, 1), (key2587, 1), (key2600, 1), (key2766, 1), (key2931, 1), (key2910, 1), (key2989, 1), (key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1)]

theorem rawRowCheck11876 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form5 = rawRow11876 := by decide +kernel

def row11876 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck11876 : row11876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11876 := by decide +kernel

theorem rowEval11876 (x : Key → ℝ) : Integer.Sparse.eval row11876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck11876, Integer.Sparse.eval_collectBalanced, rawRowCheck11876]

def rawRow11877 : Integer.Sparse Key := [(key2968, -2), (key2966, -2), (key2989, -2), (key2593, -2), (key2587, -2), (key2968, -2), (key2843, -2), (key2989, -2), (key2880, -2), (key2587, -2), (key2966, -2), (key2843, -2), (key2931, 1), (key2929, 1), (key2995, 1), (key2966, 1), (key3002, 1), (key2989, 1), (key2600, 1), (key2598, 1), (key2995, 1), (key2887, 1), (key3002, 1), (key2910, 1), (key2600, 1), (key2587, 1), (key2931, 1), (key2766, 1), (key2989, 1), (key2910, 1), (key2390, 1), (key2378, 1), (key2437, 1), (key2406, 1), (key2503, 1), (key2480, 1)]

theorem rawRowCheck11877 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form5 = rawRow11877 := by decide +kernel

def row11877 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck11877 : row11877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11877 := by decide +kernel

theorem rowEval11877 (x : Key → ℝ) : Integer.Sparse.eval row11877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck11877, Integer.Sparse.eval_collectBalanced, rawRowCheck11877]

def rawRow11878 : Integer.Sparse Key := [(key2966, -2), (key2989, -2), (key2968, -2), (key2843, -2), (key2880, -2), (key2587, -2), (key2989, -2), (key2593, -2), (key2968, -2), (key2843, -2), (key2587, -2), (key2966, -2), (key2966, 1), (key2989, 1), (key2929, 1), (key3002, 1), (key2931, 1), (key2995, 1), (key2887, 1), (key2910, 1), (key2598, 1), (key3002, 1), (key2600, 1), (key2995, 1), (key2766, 1), (key2910, 1), (key2587, 1), (key2989, 1), (key2600, 1), (key2931, 1), (key2406, 1), (key2480, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2437, 1)]

theorem rawRowCheck11878 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form5 = rawRow11878 := by decide +kernel

def row11878 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck11878 : row11878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11878 := by decide +kernel

theorem rowEval11878 (x : Key → ℝ) : Integer.Sparse.eval row11878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck11878, Integer.Sparse.eval_collectBalanced, rawRowCheck11878]

def rawRow11879 : Integer.Sparse Key := [(key2989, -2), (key2966, -2), (key2968, -2), (key2880, -2), (key2843, -2), (key2989, -2), (key2587, -2), (key2968, -2), (key2593, -2), (key2843, -2), (key2966, -2), (key2587, -2), (key2989, 1), (key2966, 1), (key3002, 1), (key2929, 1), (key2995, 1), (key2931, 1), (key2910, 1), (key2887, 1), (key3002, 1), (key2598, 1), (key2995, 1), (key2600, 1), (key2910, 1), (key2766, 1), (key2989, 1), (key2587, 1), (key2931, 1), (key2600, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2437, 1), (key2390, 1)]

theorem rawRowCheck11879 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form5 = rawRow11879 := by decide +kernel

def row11879 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck11879 : row11879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11879 := by decide +kernel

theorem rowEval11879 (x : Key → ℝ) : Integer.Sparse.eval row11879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck11879, Integer.Sparse.eval_collectBalanced, rawRowCheck11879]

def rawRow11880 : Integer.Sparse Key := [(key2968, -2), (key2989, -2), (key2966, -2), (key2968, -2), (key2989, -2), (key2593, -2), (key2880, -2), (key2587, -2), (key2843, -2), (key2966, -2), (key2587, -2), (key2843, -2), (key2995, 1), (key3002, 1), (key2931, 1), (key2989, 1), (key2929, 1), (key2966, 1), (key2995, 1), (key3002, 1), (key2600, 1), (key2910, 1), (key2598, 1), (key2887, 1), (key2931, 1), (key2989, 1), (key2600, 1), (key2910, 1), (key2587, 1), (key2766, 1), (key2437, 1), (key2503, 1), (key2390, 1), (key2480, 1), (key2378, 1), (key2406, 1)]

theorem rawRowCheck11880 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form5 = rawRow11880 := by decide +kernel

def row11880 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck11880 : row11880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11880 := by decide +kernel

theorem rowEval11880 (x : Key → ℝ) : Integer.Sparse.eval row11880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck11880, Integer.Sparse.eval_collectBalanced, rawRowCheck11880]

def rawRow11881 : Integer.Sparse Key := [(key2989, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2880, -2), (key2593, -2), (key2843, -2), (key2587, -2), (key2966, -2), (key2843, -2), (key2587, -2), (key3002, 1), (key2995, 1), (key2989, 1), (key2931, 1), (key2966, 1), (key2929, 1), (key3002, 1), (key2995, 1), (key2910, 1), (key2600, 1), (key2887, 1), (key2598, 1), (key2989, 1), (key2931, 1), (key2910, 1), (key2600, 1), (key2766, 1), (key2587, 1), (key2503, 1), (key2437, 1), (key2480, 1), (key2390, 1), (key2406, 1), (key2378, 1)]

theorem rawRowCheck11881 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form5 = rawRow11881 := by decide +kernel

def row11881 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck11881 : row11881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11881 := by decide +kernel

theorem rowEval11881 (x : Key → ℝ) : Integer.Sparse.eval row11881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck11881, Integer.Sparse.eval_collectBalanced, rawRowCheck11881]

def rawRow11882 : Integer.Sparse Key := [(key2360, -24), (key2455, 6), (key2455, 6), (key2516, 6), (key2516, 6)]

theorem rawRowCheck11882 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form6 = rawRow11882 := by decide +kernel

def row11882 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

theorem rowCheck11882 : row11882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11882 := by decide +kernel

theorem rowEval11882 (x : Key → ℝ) : Integer.Sparse.eval row11882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11882, Integer.Sparse.eval_collectBalanced, rawRowCheck11882]

def rawRow11883 : Integer.Sparse Key := [(key2360, -24), (key2455, 6), (key2516, 6), (key2455, 6), (key2516, 6)]

theorem rawRowCheck11883 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form6 = rawRow11883 := by decide +kernel

def row11883 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

theorem rowCheck11883 : row11883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11883 := by decide +kernel

theorem rowEval11883 (x : Key → ℝ) : Integer.Sparse.eval row11883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11883, Integer.Sparse.eval_collectBalanced, rawRowCheck11883]

def rawRow11884 : Integer.Sparse Key := [(key2360, -24), (key2455, 6), (key2516, 6), (key2516, 6), (key2455, 6)]

theorem rawRowCheck11884 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form6 = rawRow11884 := by decide +kernel

def row11884 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

theorem rowCheck11884 : row11884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11884 := by decide +kernel

theorem rowEval11884 (x : Key → ℝ) : Integer.Sparse.eval row11884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11884, Integer.Sparse.eval_collectBalanced, rawRowCheck11884]

def rawRow11885 : Integer.Sparse Key := [(key2360, -24), (key2516, 6), (key2455, 6), (key2455, 6), (key2516, 6)]

theorem rawRowCheck11885 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form6 = rawRow11885 := by decide +kernel

def row11885 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

theorem rowCheck11885 : row11885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11885 := by decide +kernel

theorem rowEval11885 (x : Key → ℝ) : Integer.Sparse.eval row11885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11885, Integer.Sparse.eval_collectBalanced, rawRowCheck11885]

def rawRow11886 : Integer.Sparse Key := [(key2360, -24), (key2516, 6), (key2455, 6), (key2516, 6), (key2455, 6)]

theorem rawRowCheck11886 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form6 = rawRow11886 := by decide +kernel

def row11886 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

theorem rowCheck11886 : row11886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11886 := by decide +kernel

theorem rowEval11886 (x : Key → ℝ) : Integer.Sparse.eval row11886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11886, Integer.Sparse.eval_collectBalanced, rawRowCheck11886]

def rawRow11887 : Integer.Sparse Key := [(key2360, -24), (key2516, 6), (key2516, 6), (key2455, 6), (key2455, 6)]

theorem rawRowCheck11887 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form6 = rawRow11887 := by decide +kernel

def row11887 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

theorem rowCheck11887 : row11887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11887 := by decide +kernel

theorem rowEval11887 (x : Key → ℝ) : Integer.Sparse.eval row11887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11887, Integer.Sparse.eval_collectBalanced, rawRowCheck11887]

def rawRow11888 : Integer.Sparse Key := [(key2455, -24), (key2360, 6), (key2455, 6), (key2516, 6), (key2516, 6)]

theorem rawRowCheck11888 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form6 = rawRow11888 := by decide +kernel

def row11888 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

theorem rowCheck11888 : row11888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11888 := by decide +kernel

theorem rowEval11888 (x : Key → ℝ) : Integer.Sparse.eval row11888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11888, Integer.Sparse.eval_collectBalanced, rawRowCheck11888]

def rawRow11889 : Integer.Sparse Key := [(key2455, -24), (key2360, 6), (key2516, 6), (key2455, 6), (key2516, 6)]

theorem rawRowCheck11889 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form6 = rawRow11889 := by decide +kernel

def row11889 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

theorem rowCheck11889 : row11889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11889 := by decide +kernel

theorem rowEval11889 (x : Key → ℝ) : Integer.Sparse.eval row11889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11889, Integer.Sparse.eval_collectBalanced, rawRowCheck11889]

def rawRow11890 : Integer.Sparse Key := [(key2455, -24), (key2360, 6), (key2516, 6), (key2516, 6), (key2455, 6)]

theorem rawRowCheck11890 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form6 = rawRow11890 := by decide +kernel

def row11890 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

theorem rowCheck11890 : row11890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11890 := by decide +kernel

theorem rowEval11890 (x : Key → ℝ) : Integer.Sparse.eval row11890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11890, Integer.Sparse.eval_collectBalanced, rawRowCheck11890]

def rawRow11891 : Integer.Sparse Key := [(key2455, -24), (key2455, 6), (key2360, 6), (key2516, 6), (key2516, 6)]

theorem rawRowCheck11891 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form6 = rawRow11891 := by decide +kernel

def row11891 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

theorem rowCheck11891 : row11891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11891 := by decide +kernel

theorem rowEval11891 (x : Key → ℝ) : Integer.Sparse.eval row11891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11891, Integer.Sparse.eval_collectBalanced, rawRowCheck11891]

def rawRow11892 : Integer.Sparse Key := [(key2455, -24), (key2455, 6), (key2516, 6), (key2360, 6), (key2516, 6)]

theorem rawRowCheck11892 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form6 = rawRow11892 := by decide +kernel

def row11892 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

theorem rowCheck11892 : row11892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11892 := by decide +kernel

theorem rowEval11892 (x : Key → ℝ) : Integer.Sparse.eval row11892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11892, Integer.Sparse.eval_collectBalanced, rawRowCheck11892]

def rawRow11893 : Integer.Sparse Key := [(key2455, -24), (key2455, 6), (key2516, 6), (key2516, 6), (key2360, 6)]

theorem rawRowCheck11893 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form6 = rawRow11893 := by decide +kernel

def row11893 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

theorem rowCheck11893 : row11893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11893 := by decide +kernel

theorem rowEval11893 (x : Key → ℝ) : Integer.Sparse.eval row11893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck11893, Integer.Sparse.eval_collectBalanced, rawRowCheck11893]

def rawRow11894 : Integer.Sparse Key := [(key2455, -24), (key2516, 6), (key2360, 6), (key2455, 6), (key2516, 6)]

theorem rawRowCheck11894 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form6 = rawRow11894 := by decide +kernel

def row11894 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

theorem rowCheck11894 : row11894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11894 := by decide +kernel

theorem rowEval11894 (x : Key → ℝ) : Integer.Sparse.eval row11894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11894, Integer.Sparse.eval_collectBalanced, rawRowCheck11894]

def rawRow11895 : Integer.Sparse Key := [(key2455, -24), (key2516, 6), (key2360, 6), (key2516, 6), (key2455, 6)]

theorem rawRowCheck11895 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form6 = rawRow11895 := by decide +kernel

def row11895 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

theorem rowCheck11895 : row11895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11895 := by decide +kernel

theorem rowEval11895 (x : Key → ℝ) : Integer.Sparse.eval row11895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11895, Integer.Sparse.eval_collectBalanced, rawRowCheck11895]

def rawRow11896 : Integer.Sparse Key := [(key2455, -24), (key2516, 6), (key2455, 6), (key2360, 6), (key2516, 6)]

theorem rawRowCheck11896 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form6 = rawRow11896 := by decide +kernel

def row11896 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

theorem rowCheck11896 : row11896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11896 := by decide +kernel

theorem rowEval11896 (x : Key → ℝ) : Integer.Sparse.eval row11896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11896, Integer.Sparse.eval_collectBalanced, rawRowCheck11896]

def rawRow11897 : Integer.Sparse Key := [(key2455, -24), (key2516, 6), (key2455, 6), (key2516, 6), (key2360, 6)]

theorem rawRowCheck11897 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form6 = rawRow11897 := by decide +kernel

def row11897 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

theorem rowCheck11897 : row11897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11897 := by decide +kernel

theorem rowEval11897 (x : Key → ℝ) : Integer.Sparse.eval row11897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck11897, Integer.Sparse.eval_collectBalanced, rawRowCheck11897]

def rawRow11898 : Integer.Sparse Key := [(key2455, -24), (key2516, 6), (key2516, 6), (key2360, 6), (key2455, 6)]

theorem rawRowCheck11898 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form6 = rawRow11898 := by decide +kernel

def row11898 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

theorem rowCheck11898 : row11898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11898 := by decide +kernel

theorem rowEval11898 (x : Key → ℝ) : Integer.Sparse.eval row11898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11898, Integer.Sparse.eval_collectBalanced, rawRowCheck11898]

def rawRow11899 : Integer.Sparse Key := [(key2455, -24), (key2516, 6), (key2516, 6), (key2455, 6), (key2360, 6)]

theorem rawRowCheck11899 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form6 = rawRow11899 := by decide +kernel

def row11899 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

theorem rowCheck11899 : row11899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11899 := by decide +kernel

theorem rowEval11899 (x : Key → ℝ) : Integer.Sparse.eval row11899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck11899, Integer.Sparse.eval_collectBalanced, rawRowCheck11899]

def rawRow11900 : Integer.Sparse Key := [(key2378, -2), (key2378, -2), (key2383, -2), (key2378, -2), (key2378, -2), (key2390, -2), (key2390, -2), (key2394, -2), (key2394, -2), (key2383, -2), (key2394, -2), (key2394, -2), (key2406, 2), (key2406, 2), (key2411, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2437, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2443, 2)]

theorem rawRowCheck11900 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form7 = rawRow11900 := by decide +kernel

def row11900 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

theorem rowCheck11900 : row11900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11900 := by decide +kernel

theorem rowEval11900 (x : Key → ℝ) : Integer.Sparse.eval row11900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck11900, Integer.Sparse.eval_collectBalanced, rawRowCheck11900]

def rawRow11901 : Integer.Sparse Key := [(key2378, -2), (key2383, -2), (key2378, -2), (key2390, -2), (key2394, -2), (key2378, -2), (key2394, -2), (key2378, -2), (key2390, -2), (key2394, -2), (key2383, -2), (key2394, -2), (key2406, 2), (key2411, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2411, 2), (key2443, 2)]

theorem rawRowCheck11901 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form7 = rawRow11901 := by decide +kernel

def row11901 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

theorem rowCheck11901 : row11901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11901 := by decide +kernel

theorem rowEval11901 (x : Key → ℝ) : Integer.Sparse.eval row11901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck11901, Integer.Sparse.eval_collectBalanced, rawRowCheck11901]

def rawRow11902 : Integer.Sparse Key := [(key2383, -2), (key2378, -2), (key2378, -2), (key2394, -2), (key2390, -2), (key2394, -2), (key2378, -2), (key2390, -2), (key2378, -2), (key2394, -2), (key2394, -2), (key2383, -2), (key2411, 2), (key2406, 2), (key2406, 2), (key2443, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2443, 2), (key2443, 2), (key2411, 2)]

theorem rawRowCheck11902 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form7 = rawRow11902 := by decide +kernel

def row11902 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

theorem rowCheck11902 : row11902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11902 := by decide +kernel

theorem rowEval11902 (x : Key → ℝ) : Integer.Sparse.eval row11902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck11902, Integer.Sparse.eval_collectBalanced, rawRowCheck11902]

def rawRow11903 : Integer.Sparse Key := [(key2390, -2), (key2394, -2), (key2394, -2), (key2378, -2), (key2383, -2), (key2378, -2), (key2394, -2), (key2383, -2), (key2394, -2), (key2378, -2), (key2378, -2), (key2390, -2), (key2437, 2), (key2443, 2), (key2443, 2), (key2406, 2), (key2411, 2), (key2406, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2406, 2), (key2406, 2), (key2437, 2)]

theorem rawRowCheck11903 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form7 = rawRow11903 := by decide +kernel

def row11903 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

theorem rowCheck11903 : row11903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11903 := by decide +kernel

theorem rowEval11903 (x : Key → ℝ) : Integer.Sparse.eval row11903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck11903, Integer.Sparse.eval_collectBalanced, rawRowCheck11903]

end MUB6.Certificate.GramRows

end OAI
