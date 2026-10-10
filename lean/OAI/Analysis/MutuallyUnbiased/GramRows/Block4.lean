import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow224 : Integer.Sparse Key := [(key2704, -1), (key2698, -1), (key2724, 2), (key2669, 1), (key2663, 1), (key2757, -1), (key2724, -1), (key2669, -2), (key2752, 1), (key2704, 1), (key2807, 1), (key2801, 1), (key2827, -2), (key2614, -1), (key2608, -1), (key3016, 1), (key3011, 1), (key2614, 2), (key2827, -1), (key2807, -1), (key2704, -1), (key2698, -1), (key3022, 1), (key3021, 1), (key2630, 1), (key2624, 1), (key3025, -1), (key3021, -1), (key2638, -1), (key2630, -1), (key2724, 1), (key2704, 1), (key2752, 2), (key2919, -1), (key2918, -1), (key2657, -2), (key2922, 1), (key2918, 1), (key2659, 1), (key2657, 1), (key2757, -1), (key2752, -1)]

theorem rawRowCheck224 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block0.form2 = rawRow224 := by decide +kernel

def row224 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2801, 1), (key2827, -3), (key2919, -1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck224 : row224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow224 := by decide +kernel

theorem rowEval224 (x : Key → ℝ) : Integer.Sparse.eval row224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck224, Integer.Sparse.eval_collectBalanced, rawRowCheck224]

def rawRow225 : Integer.Sparse Key := [(key2704, -1), (key2724, -1), (key2698, 2), (key2752, 1), (key2757, 1), (key2663, -1), (key2698, -1), (key2752, -2), (key2669, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2801, -2), (key3011, -1), (key3016, -1), (key2608, 1), (key2801, 1), (key2827, 2), (key2614, -1), (key2807, -1), (key2858, -1), (key3022, -1), (key2698, 1), (key2851, 1), (key2868, 1), (key3025, 1), (key2624, -1), (key2851, -1), (key2724, -1), (key2868, -1), (key2638, 1), (key2858, 1), (key2919, 2), (key2752, -1), (key2918, -1), (key2922, -2), (key2657, 1), (key2918, 1), (key2757, 1), (key2922, 1), (key2659, -1), (key2919, -1)]

theorem rawRowCheck225 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block0.form2 = rawRow225 := by decide +kernel

def row225 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, -1), (key2827, 3), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck225 : row225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow225 := by decide +kernel

theorem rowEval225 (x : Key → ℝ) : Integer.Sparse.eval row225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck225, Integer.Sparse.eval_collectBalanced, rawRowCheck225]

def rawRow226 : Integer.Sparse Key := [(key2724, -1), (key2704, -1), (key2698, 2), (key2757, 1), (key2752, 1), (key2698, -1), (key2663, -1), (key2752, -2), (key2704, 1), (key2669, 1), (key2827, 1), (key2807, 1), (key2801, -2), (key3016, -1), (key3011, -1), (key2801, 1), (key2608, 1), (key2827, 2), (key2807, -1), (key2614, -1), (key3022, -1), (key2858, -1), (key2851, 1), (key2698, 1), (key3025, 1), (key2868, 1), (key2851, -1), (key2624, -1), (key2868, -1), (key2724, -1), (key2858, 1), (key2638, 1), (key2919, 2), (key2918, -1), (key2752, -1), (key2922, -2), (key2918, 1), (key2657, 1), (key2922, 1), (key2757, 1), (key2919, -1), (key2659, -1)]

theorem rawRowCheck226 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block0.form2 = rawRow226 := by decide +kernel

def row226 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, -1), (key2827, 3), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck226 : row226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow226 := by decide +kernel

theorem rowEval226 (x : Key → ℝ) : Integer.Sparse.eval row226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck226, Integer.Sparse.eval_collectBalanced, rawRowCheck226]

def rawRow227 : Integer.Sparse Key := [(key2752, -1), (key2752, -1), (key2757, 2), (key2669, 1), (key2669, 1), (key2724, -1), (key2724, -1), (key2663, -2), (key2698, 1), (key2698, 1), (key3011, 1), (key3011, 1), (key3016, -2), (key2614, -1), (key2614, -1), (key2827, 1), (key2827, 1), (key2608, 2), (key2801, -1), (key2801, -1), (key2724, -1), (key2724, -1), (key3025, 1), (key3025, 1), (key2638, 1), (key2638, 1), (key3022, -1), (key3022, -1), (key2624, -1), (key2624, -1), (key2698, 1), (key2698, 1), (key2757, 2), (key2922, -1), (key2922, -1), (key2659, -2), (key2919, 1), (key2919, 1), (key2657, 1), (key2657, 1), (key2752, -1), (key2752, -1)]

theorem rawRowCheck227 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block0.form2 = rawRow227 := by decide +kernel

def row227 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, -2), (key2669, 2), (key2698, 4), (key2724, -4), (key2752, -4), (key2757, 4), (key2801, -2), (key2827, 2), (key2919, 2), (key2922, -2), (key3011, 2), (key3016, -2), (key3022, -2), (key3025, 2)]

theorem rowCheck227 : row227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow227 := by decide +kernel

theorem rowEval227 (x : Key → ℝ) : Integer.Sparse.eval row227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck227, Integer.Sparse.eval_collectBalanced, rawRowCheck227]

def rawRow228 : Integer.Sparse Key := [(key2752, -1), (key2757, -1), (key2752, 2), (key2704, 1), (key2724, 1), (key2669, -1), (key2704, -1), (key2698, -2), (key2663, 1), (key2698, 1), (key3011, 1), (key3016, 1), (key3011, -2), (key2807, -1), (key2827, -1), (key2614, 1), (key2807, 1), (key2801, 2), (key2608, -1), (key2801, -1), (key2868, -1), (key3025, -1), (key2724, 1), (key2868, 1), (key2858, 1), (key3022, 1), (key2638, -1), (key2858, -1), (key2698, -1), (key2851, -1), (key2624, 1), (key2851, 1), (key2922, 2), (key2757, -1), (key2922, -1), (key2919, -2), (key2659, 1), (key2919, 1), (key2752, 1), (key2918, 1), (key2657, -1), (key2918, -1)]

theorem rawRowCheck228 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block0.form2 = rawRow228 := by decide +kernel

def row228 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck228 : row228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow228 := by decide +kernel

theorem rowEval228 (x : Key → ℝ) : Integer.Sparse.eval row228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck228, Integer.Sparse.eval_collectBalanced, rawRowCheck228]

def rawRow229 : Integer.Sparse Key := [(key2757, -1), (key2752, -1), (key2752, 2), (key2724, 1), (key2704, 1), (key2704, -1), (key2669, -1), (key2698, -2), (key2698, 1), (key2663, 1), (key3016, 1), (key3011, 1), (key3011, -2), (key2827, -1), (key2807, -1), (key2807, 1), (key2614, 1), (key2801, 2), (key2801, -1), (key2608, -1), (key3025, -1), (key2868, -1), (key2868, 1), (key2724, 1), (key3022, 1), (key2858, 1), (key2858, -1), (key2638, -1), (key2851, -1), (key2698, -1), (key2851, 1), (key2624, 1), (key2922, 2), (key2922, -1), (key2757, -1), (key2919, -2), (key2919, 1), (key2659, 1), (key2918, 1), (key2752, 1), (key2918, -1), (key2657, -1)]

theorem rawRowCheck229 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block0.form2 = rawRow229 := by decide +kernel

def row229 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck229 : row229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow229 := by decide +kernel

theorem rowEval229 (x : Key → ℝ) : Integer.Sparse.eval row229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck229, Integer.Sparse.eval_collectBalanced, rawRowCheck229]

def rawRow230 : Integer.Sparse Key := [(key2778, -1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, 1), (key2858, -1), (key2919, -1), (key2827, -2), (key2868, 1), (key2922, 1), (key2624, 1), (key2630, 1), (key2638, -2), (key2698, -1), (key2704, -1), (key2858, 1), (key3022, 1), (key2724, 2), (key2868, -1), (key3025, -1), (key2608, -1), (key2614, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2752, -1), (key2757, -1), (key3007, -1), (key3009, -1), (key3011, 1), (key3016, 1), (key2614, 2), (key2630, -1), (key2638, -1), (key2669, -2), (key2704, 1), (key2724, 1), (key2784, 1), (key2792, 1), (key2807, -1), (key2827, -1)]

theorem rawRowCheck230 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block0.form2 = rawRow230 := by decide +kernel

def row230 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2792, 3), (key2801, 1), (key2827, -3), (key2919, -1), (key2922, 1), (key3007, -1), (key3009, -1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck230 : row230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow230 := by decide +kernel

theorem rowEval230 (x : Key → ℝ) : Integer.Sparse.eval row230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block0.form2) x := by
  rw [rowCheck230, Integer.Sparse.eval_collectBalanced, rawRowCheck230]

def rawRow231 : Integer.Sparse Key := [(key2784, -1), (key2778, -1), (key2792, 2), (key2807, 1), (key2801, 1), (key2919, -1), (key2858, -1), (key2827, -2), (key2922, 1), (key2868, 1), (key2630, 1), (key2624, 1), (key2638, -2), (key2704, -1), (key2698, -1), (key3022, 1), (key2858, 1), (key2724, 2), (key3025, -1), (key2868, -1), (key2614, -1), (key2608, -1), (key2659, 1), (key2657, 1), (key2669, 1), (key2663, 1), (key2757, -1), (key2752, -1), (key3009, -1), (key3007, -1), (key3016, 1), (key3011, 1), (key2614, 2), (key2638, -1), (key2630, -1), (key2669, -2), (key2724, 1), (key2704, 1), (key2792, 1), (key2784, 1), (key2827, -1), (key2807, -1)]

theorem rawRowCheck231 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block0.form2 = rawRow231 := by decide +kernel

def row231 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2792, 3), (key2801, 1), (key2827, -3), (key2919, -1), (key2922, 1), (key3007, -1), (key3009, -1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck231 : row231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow231 := by decide +kernel

theorem rowEval231 (x : Key → ℝ) : Integer.Sparse.eval row231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck231, Integer.Sparse.eval_collectBalanced, rawRowCheck231]

def rawRow232 : Integer.Sparse Key := [(key2784, -1), (key2792, -1), (key2778, 2), (key2918, 1), (key2919, 1), (key2801, -1), (key2851, -1), (key2922, -2), (key2827, 1), (key2868, 1), (key2630, 1), (key2638, 1), (key2624, -2), (key3021, -1), (key3022, -1), (key2698, 1), (key2851, 1), (key3025, 2), (key2724, -1), (key2868, -1), (key2657, -1), (key2659, -1), (key2608, 1), (key2624, 1), (key2724, 1), (key2757, 1), (key2663, -1), (key2698, -1), (key3016, -1), (key3025, -1), (key3009, 1), (key3022, 1), (key2638, 2), (key2614, -1), (key2630, -1), (key2724, -2), (key2669, 1), (key2704, 1), (key2827, 1), (key2868, 1), (key2792, -1), (key2858, -1)]

theorem rawRowCheck232 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block0.form2 = rawRow232 := by decide +kernel

def row232 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, 1), (key2724, -2), (key2757, 1), (key2778, 2), (key2784, -1), (key2792, -2), (key2801, -1), (key2827, 2), (key2858, -1), (key2868, 1), (key2918, 1), (key2919, 1), (key2922, -2), (key3009, 1), (key3016, -1), (key3021, -1), (key3025, 1)]

theorem rowCheck232 : row232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow232 := by decide +kernel

theorem rowEval232 (x : Key → ℝ) : Integer.Sparse.eval row232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck232, Integer.Sparse.eval_collectBalanced, rawRowCheck232]

def rawRow233 : Integer.Sparse Key := [(key2792, -1), (key2784, -1), (key2778, 2), (key2919, 1), (key2918, 1), (key2851, -1), (key2801, -1), (key2922, -2), (key2868, 1), (key2827, 1), (key2638, 1), (key2630, 1), (key2624, -2), (key3022, -1), (key3021, -1), (key2851, 1), (key2698, 1), (key3025, 2), (key2868, -1), (key2724, -1), (key2659, -1), (key2657, -1), (key2624, 1), (key2608, 1), (key2757, 1), (key2724, 1), (key2698, -1), (key2663, -1), (key3025, -1), (key3016, -1), (key3022, 1), (key3009, 1), (key2638, 2), (key2630, -1), (key2614, -1), (key2724, -2), (key2704, 1), (key2669, 1), (key2868, 1), (key2827, 1), (key2858, -1), (key2792, -1)]

theorem rawRowCheck233 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block0.form2 = rawRow233 := by decide +kernel

def row233 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, 1), (key2724, -2), (key2757, 1), (key2778, 2), (key2784, -1), (key2792, -2), (key2801, -1), (key2827, 2), (key2858, -1), (key2868, 1), (key2918, 1), (key2919, 1), (key2922, -2), (key3009, 1), (key3016, -1), (key3021, -1), (key3025, 1)]

theorem rowCheck233 : row233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow233 := by decide +kernel

theorem rowEval233 (x : Key → ℝ) : Integer.Sparse.eval row233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck233, Integer.Sparse.eval_collectBalanced, rawRowCheck233]

def rawRow234 : Integer.Sparse Key := [(key2801, -1), (key2807, -1), (key2827, 2), (key2778, 1), (key2784, 1), (key2868, -1), (key2922, -1), (key2792, -2), (key2858, 1), (key2919, 1), (key2698, 1), (key2704, 1), (key2724, -2), (key2624, -1), (key2630, -1), (key2868, 1), (key3025, 1), (key2638, 2), (key2858, -1), (key3022, -1), (key2663, -1), (key2669, -1), (key2724, 1), (key2757, 1), (key2608, 1), (key2614, 1), (key3011, -1), (key3016, -1), (key2657, -1), (key2659, -1), (key2752, 1), (key2757, 1), (key2669, 2), (key2784, -1), (key2792, -1), (key2614, -2), (key2807, 1), (key2827, 1), (key2630, 1), (key2638, 1), (key2704, -1), (key2724, -1)]

theorem rawRowCheck234 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block0.form2 = rawRow234 := by decide +kernel

def row234 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -2), (key2752, 1), (key2757, 2), (key2778, 1), (key2792, -3), (key2801, -1), (key2827, 3), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck234 : row234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow234 := by decide +kernel

theorem rowEval234 (x : Key → ℝ) : Integer.Sparse.eval row234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block0.form2) x := by
  rw [rowCheck234, Integer.Sparse.eval_collectBalanced, rawRowCheck234]

def rawRow235 : Integer.Sparse Key := [(key2807, -1), (key2801, -1), (key2827, 2), (key2784, 1), (key2778, 1), (key2922, -1), (key2868, -1), (key2792, -2), (key2919, 1), (key2858, 1), (key2704, 1), (key2698, 1), (key2724, -2), (key2630, -1), (key2624, -1), (key3025, 1), (key2868, 1), (key2638, 2), (key3022, -1), (key2858, -1), (key2669, -1), (key2663, -1), (key2757, 1), (key2724, 1), (key2614, 1), (key2608, 1), (key3016, -1), (key3011, -1), (key2659, -1), (key2657, -1), (key2757, 1), (key2752, 1), (key2669, 2), (key2792, -1), (key2784, -1), (key2614, -2), (key2827, 1), (key2807, 1), (key2638, 1), (key2630, 1), (key2724, -1), (key2704, -1)]

theorem rawRowCheck235 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block0.form2 = rawRow235 := by decide +kernel

def row235 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -2), (key2752, 1), (key2757, 2), (key2778, 1), (key2792, -3), (key2801, -1), (key2827, 3), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck235 : row235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow235 := by decide +kernel

theorem rowEval235 (x : Key → ℝ) : Integer.Sparse.eval row235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck235, Integer.Sparse.eval_collectBalanced, rawRowCheck235]

def rawRow236 : Integer.Sparse Key := [(key2807, -1), (key2827, -1), (key2801, 2), (key2918, 1), (key2922, 1), (key2778, -1), (key2851, -1), (key2919, -2), (key2792, 1), (key2858, 1), (key2704, 1), (key2724, 1), (key2698, -2), (key3021, -1), (key3025, -1), (key2624, 1), (key2851, 1), (key3022, 2), (key2638, -1), (key2858, -1), (key2752, -1), (key2757, -1), (key2663, 1), (key2698, 1), (key3011, 1), (key3016, 1), (key2608, -1), (key2801, -1), (key2757, -1), (key2922, -1), (key2659, 1), (key2919, 1), (key2792, 2), (key2669, -1), (key2784, -1), (key2827, -2), (key2614, 1), (key2807, 1), (key2724, 1), (key2868, 1), (key2638, -1), (key2858, -1)]

theorem rawRowCheck236 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block0.form2 = rawRow236 := by decide +kernel

def row236 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, 2), (key2752, -1), (key2757, -2), (key2778, -1), (key2784, -1), (key2792, 3), (key2801, 1), (key2827, -3), (key2858, -1), (key2868, 1), (key2918, 1), (key2919, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

theorem rowCheck236 : row236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow236 := by decide +kernel

theorem rowEval236 (x : Key → ℝ) : Integer.Sparse.eval row236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck236, Integer.Sparse.eval_collectBalanced, rawRowCheck236]

def rawRow237 : Integer.Sparse Key := [(key2827, -1), (key2807, -1), (key2801, 2), (key2922, 1), (key2918, 1), (key2851, -1), (key2778, -1), (key2919, -2), (key2858, 1), (key2792, 1), (key2724, 1), (key2704, 1), (key2698, -2), (key3025, -1), (key3021, -1), (key2851, 1), (key2624, 1), (key3022, 2), (key2858, -1), (key2638, -1), (key2757, -1), (key2752, -1), (key2698, 1), (key2663, 1), (key3016, 1), (key3011, 1), (key2801, -1), (key2608, -1), (key2922, -1), (key2757, -1), (key2919, 1), (key2659, 1), (key2792, 2), (key2784, -1), (key2669, -1), (key2827, -2), (key2807, 1), (key2614, 1), (key2868, 1), (key2724, 1), (key2858, -1), (key2638, -1)]

theorem rawRowCheck237 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block0.form2 = rawRow237 := by decide +kernel

def row237 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, 2), (key2752, -1), (key2757, -2), (key2778, -1), (key2784, -1), (key2792, 3), (key2801, 1), (key2827, -3), (key2858, -1), (key2868, 1), (key2918, 1), (key2919, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

theorem rowCheck237 : row237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow237 := by decide +kernel

theorem rowEval237 (x : Key → ℝ) : Integer.Sparse.eval row237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck237, Integer.Sparse.eval_collectBalanced, rawRowCheck237]

def rawRow238 : Integer.Sparse Key := [(key2918, -1), (key2919, -1), (key2922, 2), (key2784, 1), (key2792, 1), (key2827, -1), (key2868, -1), (key2778, -2), (key2801, 1), (key2851, 1), (key3021, 1), (key3022, 1), (key3025, -2), (key2630, -1), (key2638, -1), (key2724, 1), (key2868, 1), (key2624, 2), (key2698, -1), (key2851, -1), (key3007, -1), (key3009, -1), (key3016, 1), (key3025, 1), (key2657, 1), (key2659, 1), (key2757, -1), (key2922, -1), (key2608, -1), (key2624, -1), (key2663, 1), (key2698, 1), (key2724, 2), (key2827, -1), (key2868, -1), (key2638, -2), (key2792, 1), (key2858, 1), (key2614, 1), (key2630, 1), (key2669, -1), (key2704, -1)]

theorem rawRowCheck238 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block0.form2 = rawRow238 := by decide +kernel

def row238 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2704, -1), (key2724, 3), (key2757, -1), (key2778, -2), (key2784, 1), (key2792, 2), (key2801, 1), (key2827, -2), (key2858, 1), (key2868, -1), (key2918, -1), (key2919, -1), (key2922, 1), (key3007, -1), (key3009, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck238 : row238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow238 := by decide +kernel

theorem rowEval238 (x : Key → ℝ) : Integer.Sparse.eval row238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck238, Integer.Sparse.eval_collectBalanced, rawRowCheck238]

def rawRow239 : Integer.Sparse Key := [(key2919, -1), (key2918, -1), (key2922, 2), (key2792, 1), (key2784, 1), (key2868, -1), (key2827, -1), (key2778, -2), (key2851, 1), (key2801, 1), (key3022, 1), (key3021, 1), (key3025, -2), (key2638, -1), (key2630, -1), (key2868, 1), (key2724, 1), (key2624, 2), (key2851, -1), (key2698, -1), (key3009, -1), (key3007, -1), (key3025, 1), (key3016, 1), (key2659, 1), (key2657, 1), (key2922, -1), (key2757, -1), (key2624, -1), (key2608, -1), (key2698, 1), (key2663, 1), (key2724, 2), (key2868, -1), (key2827, -1), (key2638, -2), (key2858, 1), (key2792, 1), (key2630, 1), (key2614, 1), (key2704, -1), (key2669, -1)]

theorem rawRowCheck239 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block0.form2 = rawRow239 := by decide +kernel

def row239 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2704, -1), (key2724, 3), (key2757, -1), (key2778, -2), (key2784, 1), (key2792, 2), (key2801, 1), (key2827, -2), (key2858, 1), (key2868, -1), (key2918, -1), (key2919, -1), (key2922, 1), (key3007, -1), (key3009, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck239 : row239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow239 := by decide +kernel

theorem rowEval239 (x : Key → ℝ) : Integer.Sparse.eval row239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck239, Integer.Sparse.eval_collectBalanced, rawRowCheck239]

def rawRow240 : Integer.Sparse Key := [(key2918, -1), (key2922, -1), (key2919, 2), (key2807, 1), (key2827, 1), (key2792, -1), (key2858, -1), (key2801, -2), (key2778, 1), (key2851, 1), (key3021, 1), (key3025, 1), (key3022, -2), (key2704, -1), (key2724, -1), (key2638, 1), (key2858, 1), (key2698, 2), (key2624, -1), (key2851, -1), (key3011, -1), (key3016, -1), (key3009, 1), (key3022, 1), (key2752, 1), (key2757, 1), (key2659, -1), (key2919, -1), (key2663, -1), (key2698, -1), (key2608, 1), (key2801, 1), (key2827, 2), (key2724, -1), (key2868, -1), (key2792, -2), (key2638, 1), (key2858, 1), (key2669, 1), (key2784, 1), (key2614, -1), (key2807, -1)]

theorem rawRowCheck240 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block0.form2 = rawRow240 := by decide +kernel

def row240 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -1), (key2724, -2), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2792, -3), (key2801, -1), (key2827, 3), (key2858, 1), (key2868, -1), (key2918, -1), (key2919, 1), (key2922, -1), (key3009, 1), (key3011, -1), (key3016, -1), (key3021, 1), (key3022, -1), (key3025, 1)]

theorem rowCheck240 : row240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow240 := by decide +kernel

theorem rowEval240 (x : Key → ℝ) : Integer.Sparse.eval row240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck240, Integer.Sparse.eval_collectBalanced, rawRowCheck240]

def rawRow241 : Integer.Sparse Key := [(key2922, -1), (key2918, -1), (key2919, 2), (key2827, 1), (key2807, 1), (key2858, -1), (key2792, -1), (key2801, -2), (key2851, 1), (key2778, 1), (key3025, 1), (key3021, 1), (key3022, -2), (key2724, -1), (key2704, -1), (key2858, 1), (key2638, 1), (key2698, 2), (key2851, -1), (key2624, -1), (key3016, -1), (key3011, -1), (key3022, 1), (key3009, 1), (key2757, 1), (key2752, 1), (key2919, -1), (key2659, -1), (key2698, -1), (key2663, -1), (key2801, 1), (key2608, 1), (key2827, 2), (key2868, -1), (key2724, -1), (key2792, -2), (key2858, 1), (key2638, 1), (key2784, 1), (key2669, 1), (key2807, -1), (key2614, -1)]

theorem rawRowCheck241 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block0.form2 = rawRow241 := by decide +kernel

def row241 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -1), (key2724, -2), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2792, -3), (key2801, -1), (key2827, 3), (key2858, 1), (key2868, -1), (key2918, -1), (key2919, 1), (key2922, -1), (key3009, 1), (key3011, -1), (key3016, -1), (key3021, 1), (key3022, -1), (key3025, 1)]

theorem rowCheck241 : row241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow241 := by decide +kernel

theorem rowEval241 (x : Key → ℝ) : Integer.Sparse.eval row241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck241, Integer.Sparse.eval_collectBalanced, rawRowCheck241]

def rawRow242 : Integer.Sparse Key := [(key3007, -1), (key3007, -1), (key3009, 2), (key3011, 1), (key3011, 1), (key3022, -1), (key3022, -1), (key3016, -2), (key3025, 1), (key3025, 1), (key2657, 1), (key2657, 1), (key2659, -2), (key2752, -1), (key2752, -1), (key2919, 1), (key2919, 1), (key2757, 2), (key2922, -1), (key2922, -1), (key2614, -1), (key2614, -1), (key2638, 1), (key2638, 1), (key2669, 1), (key2669, 1), (key2792, -1), (key2792, -1), (key2724, -1), (key2724, -1), (key2827, 1), (key2827, 1), (key2608, 2), (key2624, -1), (key2624, -1), (key2663, -2), (key2698, 1), (key2698, 1), (key2778, 1), (key2778, 1), (key2801, -1), (key2801, -1)]

theorem rawRowCheck242 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block0.form2 = rawRow242 := by decide +kernel

def row242 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, -2), (key2669, 2), (key2698, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2778, 2), (key2792, -2), (key2801, -2), (key2827, 2), (key2919, 2), (key2922, -2), (key3007, -2), (key3009, 2), (key3011, 2), (key3016, -2), (key3022, -2), (key3025, 2)]

theorem rowCheck242 : row242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow242 := by decide +kernel

theorem rowEval242 (x : Key → ℝ) : Integer.Sparse.eval row242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck242, Integer.Sparse.eval_collectBalanced, rawRowCheck242]

def rawRow243 : Integer.Sparse Key := [(key3007, -1), (key3009, -1), (key3007, 2), (key3021, 1), (key3022, 1), (key3011, -1), (key3021, -1), (key3025, -2), (key3016, 1), (key3025, 1), (key2657, 1), (key2659, 1), (key2657, -2), (key2918, -1), (key2919, -1), (key2752, 1), (key2918, 1), (key2922, 2), (key2757, -1), (key2922, -1), (key2630, -1), (key2638, -1), (key2614, 1), (key2630, 1), (key2784, 1), (key2792, 1), (key2669, -1), (key2784, -1), (key2827, -1), (key2868, -1), (key2724, 1), (key2868, 1), (key2624, 2), (key2608, -1), (key2624, -1), (key2698, -2), (key2663, 1), (key2698, 1), (key2801, 1), (key2851, 1), (key2778, -1), (key2851, -1)]

theorem rawRowCheck243 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block0.form2 = rawRow243 := by decide +kernel

def row243 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck243 : row243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow243 := by decide +kernel

theorem rowEval243 (x : Key → ℝ) : Integer.Sparse.eval row243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck243, Integer.Sparse.eval_collectBalanced, rawRowCheck243]

def rawRow244 : Integer.Sparse Key := [(key3009, -1), (key3007, -1), (key3007, 2), (key3022, 1), (key3021, 1), (key3021, -1), (key3011, -1), (key3025, -2), (key3025, 1), (key3016, 1), (key2659, 1), (key2657, 1), (key2657, -2), (key2919, -1), (key2918, -1), (key2918, 1), (key2752, 1), (key2922, 2), (key2922, -1), (key2757, -1), (key2638, -1), (key2630, -1), (key2630, 1), (key2614, 1), (key2792, 1), (key2784, 1), (key2784, -1), (key2669, -1), (key2868, -1), (key2827, -1), (key2868, 1), (key2724, 1), (key2624, 2), (key2624, -1), (key2608, -1), (key2698, -2), (key2698, 1), (key2663, 1), (key2851, 1), (key2801, 1), (key2851, -1), (key2778, -1)]

theorem rawRowCheck244 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block0.form2 = rawRow244 := by decide +kernel

def row244 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck244 : row244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow244 := by decide +kernel

theorem rowEval244 (x : Key → ℝ) : Integer.Sparse.eval row244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck244, Integer.Sparse.eval_collectBalanced, rawRowCheck244]

def rawRow245 : Integer.Sparse Key := [(key3011, -1), (key3011, -1), (key3016, 2), (key3007, 1), (key3007, 1), (key3025, -1), (key3025, -1), (key3009, -2), (key3022, 1), (key3022, 1), (key2752, 1), (key2752, 1), (key2757, -2), (key2657, -1), (key2657, -1), (key2922, 1), (key2922, 1), (key2659, 2), (key2919, -1), (key2919, -1), (key2669, -1), (key2669, -1), (key2724, 1), (key2724, 1), (key2614, 1), (key2614, 1), (key2827, -1), (key2827, -1), (key2638, -1), (key2638, -1), (key2792, 1), (key2792, 1), (key2663, 2), (key2698, -1), (key2698, -1), (key2608, -2), (key2801, 1), (key2801, 1), (key2624, 1), (key2624, 1), (key2698, -1), (key2698, -1)]

theorem rawRowCheck245 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block0.form2 = rawRow245 := by decide +kernel

def row245 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2792, 2), (key2801, 2), (key2827, -2), (key2919, -2), (key2922, 2), (key3007, 2), (key3009, -2), (key3011, -2), (key3016, 2), (key3022, 2), (key3025, -2)]

theorem rowCheck245 : row245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow245 := by decide +kernel

theorem rowEval245 (x : Key → ℝ) : Integer.Sparse.eval row245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck245, Integer.Sparse.eval_collectBalanced, rawRowCheck245]

def rawRow246 : Integer.Sparse Key := [(key3011, -1), (key3016, -1), (key3011, 2), (key3021, 1), (key3025, 1), (key3007, -1), (key3021, -1), (key3022, -2), (key3009, 1), (key3022, 1), (key2752, 1), (key2757, 1), (key2752, -2), (key2918, -1), (key2922, -1), (key2657, 1), (key2918, 1), (key2919, 2), (key2659, -1), (key2919, -1), (key2704, -1), (key2724, -1), (key2669, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2614, -1), (key2807, -1), (key2792, -1), (key2858, -1), (key2638, 1), (key2858, 1), (key2698, 2), (key2663, -1), (key2698, -1), (key2801, -2), (key2608, 1), (key2801, 1), (key2698, 1), (key2851, 1), (key2624, -1), (key2851, -1)]

theorem rawRowCheck246 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block0.form2 = rawRow246 := by decide +kernel

def row246 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck246 : row246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow246 := by decide +kernel

theorem rowEval246 (x : Key → ℝ) : Integer.Sparse.eval row246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck246, Integer.Sparse.eval_collectBalanced, rawRowCheck246]

def rawRow247 : Integer.Sparse Key := [(key3016, -1), (key3011, -1), (key3011, 2), (key3025, 1), (key3021, 1), (key3021, -1), (key3007, -1), (key3022, -2), (key3022, 1), (key3009, 1), (key2757, 1), (key2752, 1), (key2752, -2), (key2922, -1), (key2918, -1), (key2918, 1), (key2657, 1), (key2919, 2), (key2919, -1), (key2659, -1), (key2724, -1), (key2704, -1), (key2704, 1), (key2669, 1), (key2827, 1), (key2807, 1), (key2807, -1), (key2614, -1), (key2858, -1), (key2792, -1), (key2858, 1), (key2638, 1), (key2698, 2), (key2698, -1), (key2663, -1), (key2801, -2), (key2801, 1), (key2608, 1), (key2851, 1), (key2698, 1), (key2851, -1), (key2624, -1)]

theorem rawRowCheck247 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block0.form2 = rawRow247 := by decide +kernel

def row247 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck247 : row247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow247 := by decide +kernel

theorem rowEval247 (x : Key → ℝ) : Integer.Sparse.eval row247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck247, Integer.Sparse.eval_collectBalanced, rawRowCheck247]

def rawRow248 : Integer.Sparse Key := [(key3021, -1), (key3022, -1), (key3025, 2), (key3007, 1), (key3009, 1), (key3016, -1), (key3025, -1), (key3007, -2), (key3011, 1), (key3021, 1), (key2918, 1), (key2919, 1), (key2922, -2), (key2657, -1), (key2659, -1), (key2757, 1), (key2922, 1), (key2657, 2), (key2752, -1), (key2918, -1), (key2784, -1), (key2792, -1), (key2827, 1), (key2868, 1), (key2630, 1), (key2638, 1), (key2724, -1), (key2868, -1), (key2614, -1), (key2630, -1), (key2669, 1), (key2784, 1), (key2778, 2), (key2801, -1), (key2851, -1), (key2624, -2), (key2698, 1), (key2851, 1), (key2608, 1), (key2624, 1), (key2663, -1), (key2698, -1)]

theorem rawRowCheck248 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block0.form2 = rawRow248 := by decide +kernel

def row248 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 2), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck248 : row248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow248 := by decide +kernel

theorem rowEval248 (x : Key → ℝ) : Integer.Sparse.eval row248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck248, Integer.Sparse.eval_collectBalanced, rawRowCheck248]

def rawRow249 : Integer.Sparse Key := [(key3022, -1), (key3021, -1), (key3025, 2), (key3009, 1), (key3007, 1), (key3025, -1), (key3016, -1), (key3007, -2), (key3021, 1), (key3011, 1), (key2919, 1), (key2918, 1), (key2922, -2), (key2659, -1), (key2657, -1), (key2922, 1), (key2757, 1), (key2657, 2), (key2918, -1), (key2752, -1), (key2792, -1), (key2784, -1), (key2868, 1), (key2827, 1), (key2638, 1), (key2630, 1), (key2868, -1), (key2724, -1), (key2630, -1), (key2614, -1), (key2784, 1), (key2669, 1), (key2778, 2), (key2851, -1), (key2801, -1), (key2624, -2), (key2851, 1), (key2698, 1), (key2624, 1), (key2608, 1), (key2698, -1), (key2663, -1)]

theorem rawRowCheck249 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block0.form2 = rawRow249 := by decide +kernel

def row249 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 2), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck249 : row249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow249 := by decide +kernel

theorem rowEval249 (x : Key → ℝ) : Integer.Sparse.eval row249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck249, Integer.Sparse.eval_collectBalanced, rawRowCheck249]

def rawRow250 : Integer.Sparse Key := [(key3021, -1), (key3025, -1), (key3022, 2), (key3011, 1), (key3016, 1), (key3009, -1), (key3022, -1), (key3011, -2), (key3007, 1), (key3021, 1), (key2918, 1), (key2922, 1), (key2919, -2), (key2752, -1), (key2757, -1), (key2659, 1), (key2919, 1), (key2752, 2), (key2657, -1), (key2918, -1), (key2807, -1), (key2827, -1), (key2792, 1), (key2858, 1), (key2704, 1), (key2724, 1), (key2638, -1), (key2858, -1), (key2669, -1), (key2704, -1), (key2614, 1), (key2807, 1), (key2801, 2), (key2778, -1), (key2851, -1), (key2698, -2), (key2624, 1), (key2851, 1), (key2663, 1), (key2698, 1), (key2608, -1), (key2801, -1)]

theorem rawRowCheck250 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block0.form2 = rawRow250 := by decide +kernel

def row250 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck250 : row250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow250 := by decide +kernel

theorem rowEval250 (x : Key → ℝ) : Integer.Sparse.eval row250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck250, Integer.Sparse.eval_collectBalanced, rawRowCheck250]

def rawRow251 : Integer.Sparse Key := [(key3025, -1), (key3021, -1), (key3022, 2), (key3016, 1), (key3011, 1), (key3022, -1), (key3009, -1), (key3011, -2), (key3021, 1), (key3007, 1), (key2922, 1), (key2918, 1), (key2919, -2), (key2757, -1), (key2752, -1), (key2919, 1), (key2659, 1), (key2752, 2), (key2918, -1), (key2657, -1), (key2827, -1), (key2807, -1), (key2858, 1), (key2792, 1), (key2724, 1), (key2704, 1), (key2858, -1), (key2638, -1), (key2704, -1), (key2669, -1), (key2807, 1), (key2614, 1), (key2801, 2), (key2851, -1), (key2778, -1), (key2698, -2), (key2851, 1), (key2624, 1), (key2698, 1), (key2663, 1), (key2801, -1), (key2608, -1)]

theorem rawRowCheck251 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block0.form2 = rawRow251 := by decide +kernel

def row251 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck251 : row251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow251 := by decide +kernel

theorem rowEval251 (x : Key → ℝ) : Integer.Sparse.eval row251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck251, Integer.Sparse.eval_collectBalanced, rawRowCheck251]

def rawRow252 : Integer.Sparse Key := [(key242, -1), (key242, -1), (key244, 2), (key254, 1), (key254, 1), (key265, -1), (key265, -1), (key269, -2), (key274, 1), (key274, 1), (key308, 1), (key308, 1), (key310, -2), (key322, -1), (key322, -1), (key333, 1), (key333, 1), (key337, 2), (key343, -1), (key343, -1), (key391, -1), (key391, -1), (key402, 1), (key402, 1), (key412, 1), (key412, 1), (key423, -1), (key423, -1), (key472, -1), (key472, -1), (key478, 1), (key478, 1), (key570, 2), (key575, -1), (key575, -1), (key580, -2), (key586, 1), (key586, 1), (key598, 1), (key598, 1), (key604, -1), (key604, -1)]

theorem rawRowCheck252 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form0 = rawRow252 := by decide +kernel

def row252 : Integer.Sparse Key := [(key242, -2), (key244, 2), (key254, 2), (key265, -2), (key269, -2), (key274, 2), (key308, 2), (key310, -2), (key322, -2), (key333, 2), (key337, 2), (key343, -2), (key391, -2), (key402, 2), (key412, 2), (key423, -2), (key472, -2), (key478, 2), (key570, 2), (key575, -2), (key580, -2), (key586, 2), (key598, 2), (key604, -2)]

theorem rowCheck252 : row252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow252 := by decide +kernel

theorem rowEval252 (x : Key → ℝ) : Integer.Sparse.eval row252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck252, Integer.Sparse.eval_collectBalanced, rawRowCheck252]

def rawRow253 : Integer.Sparse Key := [(key242, -1), (key244, -1), (key242, 2), (key264, 1), (key265, 1), (key254, -1), (key264, -1), (key274, -2), (key269, 1), (key274, 1), (key308, 1), (key310, 1), (key308, -2), (key332, -1), (key333, -1), (key322, 1), (key332, 1), (key343, 2), (key337, -1), (key343, -1), (key401, -1), (key402, -1), (key391, 1), (key401, 1), (key422, 1), (key423, 1), (key412, -1), (key422, -1), (key478, -1), (key484, -1), (key472, 1), (key484, 1), (key575, 2), (key570, -1), (key575, -1), (key586, -2), (key580, 1), (key586, 1), (key604, 1), (key610, 1), (key598, -1), (key610, -1)]

theorem rawRowCheck253 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form0 = rawRow253 := by decide +kernel

def row253 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck253 : row253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow253 := by decide +kernel

theorem rowEval253 (x : Key → ℝ) : Integer.Sparse.eval row253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck253, Integer.Sparse.eval_collectBalanced, rawRowCheck253]

def rawRow254 : Integer.Sparse Key := [(key244, -1), (key242, -1), (key242, 2), (key265, 1), (key264, 1), (key264, -1), (key254, -1), (key274, -2), (key274, 1), (key269, 1), (key310, 1), (key308, 1), (key308, -2), (key333, -1), (key332, -1), (key332, 1), (key322, 1), (key343, 2), (key343, -1), (key337, -1), (key402, -1), (key401, -1), (key401, 1), (key391, 1), (key423, 1), (key422, 1), (key422, -1), (key412, -1), (key484, -1), (key478, -1), (key484, 1), (key472, 1), (key575, 2), (key575, -1), (key570, -1), (key586, -2), (key586, 1), (key580, 1), (key610, 1), (key604, 1), (key610, -1), (key598, -1)]

theorem rawRowCheck254 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form0 = rawRow254 := by decide +kernel

def row254 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck254 : row254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow254 := by decide +kernel

theorem rowEval254 (x : Key → ℝ) : Integer.Sparse.eval row254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck254, Integer.Sparse.eval_collectBalanced, rawRowCheck254]

def rawRow255 : Integer.Sparse Key := [(key254, -1), (key254, -1), (key269, 2), (key242, 1), (key242, 1), (key274, -1), (key274, -1), (key244, -2), (key265, 1), (key265, 1), (key322, 1), (key322, 1), (key337, -2), (key308, -1), (key308, -1), (key343, 1), (key343, 1), (key310, 2), (key333, -1), (key333, -1), (key412, -1), (key412, -1), (key472, 1), (key472, 1), (key391, 1), (key391, 1), (key478, -1), (key478, -1), (key402, -1), (key402, -1), (key423, 1), (key423, 1), (key580, 2), (key598, -1), (key598, -1), (key570, -2), (key604, 1), (key604, 1), (key575, 1), (key575, 1), (key586, -1), (key586, -1)]

theorem rawRowCheck255 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form0 = rawRow255 := by decide +kernel

def row255 : Integer.Sparse Key := [(key242, 2), (key244, -2), (key254, -2), (key265, 2), (key269, 2), (key274, -2), (key308, -2), (key310, 2), (key322, 2), (key333, -2), (key337, -2), (key343, 2), (key391, 2), (key402, -2), (key412, -2), (key423, 2), (key472, 2), (key478, -2), (key570, -2), (key575, 2), (key580, 2), (key586, -2), (key598, -2), (key604, 2)]

theorem rowCheck255 : row255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow255 := by decide +kernel

theorem rowEval255 (x : Key → ℝ) : Integer.Sparse.eval row255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck255, Integer.Sparse.eval_collectBalanced, rawRowCheck255]

end MUB6.Certificate.GramRows

end OAI
