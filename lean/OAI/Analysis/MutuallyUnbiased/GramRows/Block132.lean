import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow13824 : Integer.Sparse Key := [(key2624, -1), (key2638, -1), (key2698, -1), (key3022, -1), (key2724, -1), (key3025, -1), (key2630, 2), (key2704, 2), (key3021, 2), (key2624, -1), (key2638, -1), (key2698, -1), (key3022, -1), (key2724, -1), (key3025, -1), (key2608, 2), (key2659, 2), (key2663, 2), (key2757, 2), (key3009, 2), (key3016, 2), (key2614, -1), (key2638, -1), (key2669, -1), (key2724, -1), (key2792, -1), (key2827, -1), (key2630, 2), (key2784, 2), (key2868, 2), (key2614, -1), (key2638, -1), (key2669, -1), (key2724, -1), (key2792, -1), (key2827, -1)]

theorem rawRowCheck13824 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form6 = rawRow13824 := by decide +kernel

def row13824 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 2), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

theorem rowCheck13824 : row13824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13824 := by decide +kernel

theorem rowEval13824 (x : Key → ℝ) : Integer.Sparse.eval row13824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13824, Integer.Sparse.eval_collectBalanced, rawRowCheck13824]

def rawRow13825 : Integer.Sparse Key := [(key2638, -1), (key2624, -1), (key3022, -1), (key2698, -1), (key3025, -1), (key2724, -1), (key2630, 2), (key3021, 2), (key2704, 2), (key2638, -1), (key2624, -1), (key3022, -1), (key2698, -1), (key3025, -1), (key2724, -1), (key2659, 2), (key2608, 2), (key2757, 2), (key2663, 2), (key3016, 2), (key3009, 2), (key2638, -1), (key2614, -1), (key2724, -1), (key2669, -1), (key2827, -1), (key2792, -1), (key2630, 2), (key2868, 2), (key2784, 2), (key2638, -1), (key2614, -1), (key2724, -1), (key2669, -1), (key2827, -1), (key2792, -1)]

theorem rawRowCheck13825 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form6 = rawRow13825 := by decide +kernel

def row13825 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 2), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

theorem rowCheck13825 : row13825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13825 := by decide +kernel

theorem rowEval13825 (x : Key → ℝ) : Integer.Sparse.eval row13825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13825, Integer.Sparse.eval_collectBalanced, rawRowCheck13825]

def rawRow13826 : Integer.Sparse Key := [(key2698, -1), (key2724, -1), (key2624, -1), (key3025, -1), (key2638, -1), (key3022, -1), (key2704, 2), (key2630, 2), (key3021, 2), (key2698, -1), (key2724, -1), (key2624, -1), (key3025, -1), (key2638, -1), (key3022, -1), (key2663, 2), (key2757, 2), (key2608, 2), (key3016, 2), (key2659, 2), (key2757, 2), (key2669, -1), (key2792, -1), (key2614, -1), (key2827, -1), (key2638, -1), (key2724, -1), (key2784, 2), (key2630, 2), (key2868, 2), (key2669, -1), (key2792, -1), (key2614, -1), (key2827, -1), (key2638, -1), (key2724, -1)]

theorem rawRowCheck13826 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form6 = rawRow13826 := by decide +kernel

def row13826 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 4), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

theorem rowCheck13826 : row13826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13826 := by decide +kernel

theorem rowEval13826 (x : Key → ℝ) : Integer.Sparse.eval row13826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13826, Integer.Sparse.eval_collectBalanced, rawRowCheck13826]

def rawRow13827 : Integer.Sparse Key := [(key2724, -1), (key2698, -1), (key3025, -1), (key2624, -1), (key3022, -1), (key2638, -1), (key2704, 2), (key3021, 2), (key2630, 2), (key2724, -1), (key2698, -1), (key3025, -1), (key2624, -1), (key3022, -1), (key2638, -1), (key2757, 2), (key2663, 2), (key3016, 2), (key2608, 2), (key2757, 2), (key2659, 2), (key2792, -1), (key2669, -1), (key2827, -1), (key2614, -1), (key2724, -1), (key2638, -1), (key2784, 2), (key2868, 2), (key2630, 2), (key2792, -1), (key2669, -1), (key2827, -1), (key2614, -1), (key2724, -1), (key2638, -1)]

theorem rawRowCheck13827 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form6 = rawRow13827 := by decide +kernel

def row13827 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 4), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

theorem rowCheck13827 : row13827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13827 := by decide +kernel

theorem rowEval13827 (x : Key → ℝ) : Integer.Sparse.eval row13827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13827, Integer.Sparse.eval_collectBalanced, rawRowCheck13827]

def rawRow13828 : Integer.Sparse Key := [(key3022, -1), (key3025, -1), (key2638, -1), (key2724, -1), (key2624, -1), (key2698, -1), (key3021, 2), (key2630, 2), (key2704, 2), (key3022, -1), (key3025, -1), (key2638, -1), (key2724, -1), (key2624, -1), (key2698, -1), (key3009, 2), (key3016, 2), (key2659, 2), (key2757, 2), (key2608, 2), (key2663, 2), (key2724, -1), (key2827, -1), (key2638, -1), (key2792, -1), (key2614, -1), (key2669, -1), (key2868, 2), (key2630, 2), (key2784, 2), (key2724, -1), (key2827, -1), (key2638, -1), (key2792, -1), (key2614, -1), (key2669, -1)]

theorem rawRowCheck13828 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form6 = rawRow13828 := by decide +kernel

def row13828 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 2), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

theorem rowCheck13828 : row13828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13828 := by decide +kernel

theorem rowEval13828 (x : Key → ℝ) : Integer.Sparse.eval row13828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13828, Integer.Sparse.eval_collectBalanced, rawRowCheck13828]

def rawRow13829 : Integer.Sparse Key := [(key3025, -1), (key3022, -1), (key2724, -1), (key2638, -1), (key2698, -1), (key2624, -1), (key3021, 2), (key2704, 2), (key2630, 2), (key3025, -1), (key3022, -1), (key2724, -1), (key2638, -1), (key2698, -1), (key2624, -1), (key3016, 2), (key3009, 2), (key2757, 2), (key2659, 2), (key2663, 2), (key2608, 2), (key2827, -1), (key2724, -1), (key2792, -1), (key2638, -1), (key2669, -1), (key2614, -1), (key2868, 2), (key2784, 2), (key2630, 2), (key2827, -1), (key2724, -1), (key2792, -1), (key2638, -1), (key2669, -1), (key2614, -1)]

theorem rawRowCheck13829 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form6 = rawRow13829 := by decide +kernel

def row13829 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 2), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

theorem rowCheck13829 : row13829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13829 := by decide +kernel

theorem rowEval13829 (x : Key → ℝ) : Integer.Sparse.eval row13829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13829, Integer.Sparse.eval_collectBalanced, rawRowCheck13829]

def rawRow13830 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2704, -1), (key2858, -1), (key2724, -1), (key2868, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2657, -1), (key2659, -1), (key2752, -1), (key2919, -1), (key2757, -1), (key2922, -1), (key2614, 2), (key2638, 2), (key2669, 2), (key2792, 2), (key2724, 2), (key2827, 2), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1), (key2638, 2), (key2792, 2), (key2858, 2), (key2614, -1), (key2630, -1), (key2669, -1), (key2704, -1), (key2784, -1), (key2807, -1)]

theorem rawRowCheck13830 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block4.form6 = rawRow13830 := by decide +kernel

def row13830 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

theorem rowCheck13830 : row13830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13830 := by decide +kernel

theorem rowEval13830 (x : Key → ℝ) : Integer.Sparse.eval row13830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13830, Integer.Sparse.eval_collectBalanced, rawRowCheck13830]

def rawRow13831 : Integer.Sparse Key := [(key2638, -1), (key2630, -1), (key2858, -1), (key2704, -1), (key2868, -1), (key2724, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2659, -1), (key2657, -1), (key2919, -1), (key2752, -1), (key2922, -1), (key2757, -1), (key2638, 2), (key2614, 2), (key2792, 2), (key2669, 2), (key2827, 2), (key2724, 2), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1), (key2638, 2), (key2858, 2), (key2792, 2), (key2630, -1), (key2614, -1), (key2704, -1), (key2669, -1), (key2807, -1), (key2784, -1)]

theorem rawRowCheck13831 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block4.form6 = rawRow13831 := by decide +kernel

def row13831 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

theorem rowCheck13831 : row13831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13831 := by decide +kernel

theorem rowEval13831 (x : Key → ℝ) : Integer.Sparse.eval row13831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13831, Integer.Sparse.eval_collectBalanced, rawRowCheck13831]

def rawRow13832 : Integer.Sparse Key := [(key2704, -1), (key2724, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2752, -1), (key2757, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2669, 2), (key2724, 2), (key2614, 2), (key2827, 2), (key2638, 2), (key2792, 2), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2792, 2), (key2638, 2), (key2858, 2), (key2669, -1), (key2784, -1), (key2614, -1), (key2807, -1), (key2630, -1), (key2704, -1)]

theorem rawRowCheck13832 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block4.form6 = rawRow13832 := by decide +kernel

def row13832 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

theorem rowCheck13832 : row13832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13832 := by decide +kernel

theorem rowEval13832 (x : Key → ℝ) : Integer.Sparse.eval row13832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13832, Integer.Sparse.eval_collectBalanced, rawRowCheck13832]

def rawRow13833 : Integer.Sparse Key := [(key2724, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2858, -1), (key2638, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2757, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2919, -1), (key2659, -1), (key2724, 2), (key2669, 2), (key2827, 2), (key2614, 2), (key2792, 2), (key2638, 2), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1), (key2792, 2), (key2858, 2), (key2638, 2), (key2784, -1), (key2669, -1), (key2807, -1), (key2614, -1), (key2704, -1), (key2630, -1)]

theorem rawRowCheck13833 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block4.form6 = rawRow13833 := by decide +kernel

def row13833 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

theorem rowCheck13833 : row13833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13833 := by decide +kernel

theorem rowEval13833 (x : Key → ℝ) : Integer.Sparse.eval row13833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13833, Integer.Sparse.eval_collectBalanced, rawRowCheck13833]

def rawRow13834 : Integer.Sparse Key := [(key2858, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2630, -1), (key2704, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2919, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2657, -1), (key2752, -1), (key2792, 2), (key2827, 2), (key2638, 2), (key2724, 2), (key2614, 2), (key2669, 2), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1), (key2858, 2), (key2638, 2), (key2792, 2), (key2704, -1), (key2807, -1), (key2630, -1), (key2784, -1), (key2614, -1), (key2669, -1)]

theorem rawRowCheck13834 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block4.form6 = rawRow13834 := by decide +kernel

def row13834 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

theorem rowCheck13834 : row13834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13834 := by decide +kernel

theorem rowEval13834 (x : Key → ℝ) : Integer.Sparse.eval row13834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13834, Integer.Sparse.eval_collectBalanced, rawRowCheck13834]

def rawRow13835 : Integer.Sparse Key := [(key2868, -1), (key2858, -1), (key2724, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2922, -1), (key2919, -1), (key2757, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2827, 2), (key2792, 2), (key2724, 2), (key2638, 2), (key2669, 2), (key2614, 2), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1), (key2858, 2), (key2792, 2), (key2638, 2), (key2807, -1), (key2704, -1), (key2784, -1), (key2630, -1), (key2669, -1), (key2614, -1)]

theorem rawRowCheck13835 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block4.form6 = rawRow13835 := by decide +kernel

def row13835 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

theorem rowCheck13835 : row13835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13835 := by decide +kernel

theorem rowEval13835 (x : Key → ℝ) : Integer.Sparse.eval row13835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13835, Integer.Sparse.eval_collectBalanced, rawRowCheck13835]

def rawRow13836 : Integer.Sparse Key := [(key2657, -1), (key2657, -1), (key2918, -1), (key2918, -1), (key2922, -1), (key2922, -1), (key2659, 2), (key2919, 2), (key2919, 2), (key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2630, 2), (key2630, 2), (key2784, 2), (key2784, 2), (key2868, 2), (key2868, 2), (key2638, -1), (key2638, -1), (key2792, -1), (key2792, -1), (key2858, -1), (key2858, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1)]

theorem rawRowCheck13836 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form6 = rawRow13836 := by decide +kernel

def row13836 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2784, 4), (key2792, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2868, 4), (key2918, -2), (key2919, 4), (key2922, -2)]

theorem rowCheck13836 : row13836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13836 := by decide +kernel

theorem rowEval13836 (x : Key → ℝ) : Integer.Sparse.eval row13836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13836, Integer.Sparse.eval_collectBalanced, rawRowCheck13836]

def rawRow13837 : Integer.Sparse Key := [(key2918, -1), (key2922, -1), (key2657, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2919, 2), (key2659, 2), (key2919, 2), (key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2784, 2), (key2868, 2), (key2630, 2), (key2868, 2), (key2630, 2), (key2784, 2), (key2792, -1), (key2858, -1), (key2638, -1), (key2858, -1), (key2638, -1), (key2792, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1)]

theorem rawRowCheck13837 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form6 = rawRow13837 := by decide +kernel

def row13837 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2784, 4), (key2792, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2868, 4), (key2918, -2), (key2919, 4), (key2922, -2)]

theorem rowCheck13837 : row13837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13837 := by decide +kernel

theorem rowEval13837 (x : Key → ℝ) : Integer.Sparse.eval row13837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13837, Integer.Sparse.eval_collectBalanced, rawRowCheck13837]

def rawRow13838 : Integer.Sparse Key := [(key2922, -1), (key2918, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2657, -1), (key2919, 2), (key2919, 2), (key2659, 2), (key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key2868, 2), (key2784, 2), (key2868, 2), (key2630, 2), (key2784, 2), (key2630, 2), (key2858, -1), (key2792, -1), (key2858, -1), (key2638, -1), (key2792, -1), (key2638, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1)]

theorem rawRowCheck13838 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form6 = rawRow13838 := by decide +kernel

def row13838 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2784, 4), (key2792, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2868, 4), (key2918, -2), (key2919, 4), (key2922, -2)]

theorem rowCheck13838 : row13838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13838 := by decide +kernel

theorem rowEval13838 (x : Key → ℝ) : Integer.Sparse.eval row13838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13838, Integer.Sparse.eval_collectBalanced, rawRowCheck13838]

def rawRow13839 : Integer.Sparse Key := [(key2657, -1), (key2659, -1), (key2752, -1), (key2919, -1), (key2757, -1), (key2922, -1), (key2657, 2), (key2752, 2), (key2918, 2), (key2630, -1), (key2638, -1), (key2704, -1), (key2858, -1), (key2724, -1), (key2868, -1), (key2614, 2), (key2638, 2), (key2669, 2), (key2792, 2), (key2724, 2), (key2827, 2), (key2614, -1), (key2630, -1), (key2669, -1), (key2784, -1), (key2704, -1), (key2807, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1)]

theorem rawRowCheck13839 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block4.form6 = rawRow13839 := by decide +kernel

def row13839 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck13839 : row13839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13839 := by decide +kernel

theorem rowEval13839 (x : Key → ℝ) : Integer.Sparse.eval row13839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13839, Integer.Sparse.eval_collectBalanced, rawRowCheck13839]

def rawRow13840 : Integer.Sparse Key := [(key2659, -1), (key2657, -1), (key2919, -1), (key2752, -1), (key2922, -1), (key2757, -1), (key2657, 2), (key2918, 2), (key2752, 2), (key2638, -1), (key2630, -1), (key2858, -1), (key2704, -1), (key2868, -1), (key2724, -1), (key2638, 2), (key2614, 2), (key2792, 2), (key2669, 2), (key2827, 2), (key2724, 2), (key2630, -1), (key2614, -1), (key2784, -1), (key2669, -1), (key2807, -1), (key2704, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1)]

theorem rawRowCheck13840 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block4.form6 = rawRow13840 := by decide +kernel

def row13840 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck13840 : row13840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13840 := by decide +kernel

theorem rowEval13840 (x : Key → ℝ) : Integer.Sparse.eval row13840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13840, Integer.Sparse.eval_collectBalanced, rawRowCheck13840]

def rawRow13841 : Integer.Sparse Key := [(key2752, -1), (key2757, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2752, 2), (key2657, 2), (key2918, 2), (key2704, -1), (key2724, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2669, 2), (key2724, 2), (key2614, 2), (key2827, 2), (key2638, 2), (key2792, 2), (key2669, -1), (key2704, -1), (key2614, -1), (key2807, -1), (key2630, -1), (key2784, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1)]

theorem rawRowCheck13841 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block4.form6 = rawRow13841 := by decide +kernel

def row13841 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck13841 : row13841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13841 := by decide +kernel

theorem rowEval13841 (x : Key → ℝ) : Integer.Sparse.eval row13841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13841, Integer.Sparse.eval_collectBalanced, rawRowCheck13841]

def rawRow13842 : Integer.Sparse Key := [(key2757, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2919, -1), (key2659, -1), (key2752, 2), (key2918, 2), (key2657, 2), (key2724, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2858, -1), (key2638, -1), (key2724, 2), (key2669, 2), (key2827, 2), (key2614, 2), (key2792, 2), (key2638, 2), (key2704, -1), (key2669, -1), (key2807, -1), (key2614, -1), (key2784, -1), (key2630, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1)]

theorem rawRowCheck13842 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block4.form6 = rawRow13842 := by decide +kernel

def row13842 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck13842 : row13842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13842 := by decide +kernel

theorem rowEval13842 (x : Key → ℝ) : Integer.Sparse.eval row13842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13842, Integer.Sparse.eval_collectBalanced, rawRowCheck13842]

def rawRow13843 : Integer.Sparse Key := [(key2919, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2657, -1), (key2752, -1), (key2918, 2), (key2657, 2), (key2752, 2), (key2858, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2630, -1), (key2704, -1), (key2792, 2), (key2827, 2), (key2638, 2), (key2724, 2), (key2614, 2), (key2669, 2), (key2784, -1), (key2807, -1), (key2630, -1), (key2704, -1), (key2614, -1), (key2669, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1)]

theorem rawRowCheck13843 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block4.form6 = rawRow13843 := by decide +kernel

def row13843 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck13843 : row13843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13843 := by decide +kernel

theorem rowEval13843 (x : Key → ℝ) : Integer.Sparse.eval row13843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13843, Integer.Sparse.eval_collectBalanced, rawRowCheck13843]

def rawRow13844 : Integer.Sparse Key := [(key2922, -1), (key2919, -1), (key2757, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2918, 2), (key2752, 2), (key2657, 2), (key2868, -1), (key2858, -1), (key2724, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key2827, 2), (key2792, 2), (key2724, 2), (key2638, 2), (key2669, 2), (key2614, 2), (key2807, -1), (key2784, -1), (key2704, -1), (key2630, -1), (key2669, -1), (key2614, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1)]

theorem rawRowCheck13844 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block4.form6 = rawRow13844 := by decide +kernel

def row13844 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck13844 : row13844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13844 := by decide +kernel

theorem rowEval13844 (x : Key → ℝ) : Integer.Sparse.eval row13844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13844, Integer.Sparse.eval_collectBalanced, rawRowCheck13844]

def rawRow13845 : Integer.Sparse Key := [(key2420, 4), (key2495, 4), (key2495, 4), (key2427, -2), (key2427, -2), (key2495, -2), (key2495, -2), (key2504, -2), (key2504, -2), (key2427, -2), (key2427, -2), (key2495, -2), (key2495, -2), (key2504, -2), (key2504, -2), (key2438, 4), (key2504, 4), (key2504, 4)]

theorem rawRowCheck13845 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form0 = rawRow13845 := by decide +kernel

def row13845 : Integer.Sparse Key := [(key2420, 4), (key2427, -8), (key2438, 4)]

theorem rowCheck13845 : row13845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13845 := by decide +kernel

theorem rowEval13845 (x : Key → ℝ) : Integer.Sparse.eval row13845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13845, Integer.Sparse.eval_collectBalanced, rawRowCheck13845]

def rawRow13846 : Integer.Sparse Key := [(key2495, 4), (key2420, 4), (key2495, 4), (key2495, -2), (key2504, -2), (key2427, -2), (key2504, -2), (key2427, -2), (key2495, -2), (key2495, -2), (key2504, -2), (key2427, -2), (key2504, -2), (key2427, -2), (key2495, -2), (key2504, 4), (key2438, 4), (key2504, 4)]

theorem rawRowCheck13846 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form0 = rawRow13846 := by decide +kernel

def row13846 : Integer.Sparse Key := [(key2420, 4), (key2427, -8), (key2438, 4)]

theorem rowCheck13846 : row13846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13846 := by decide +kernel

theorem rowEval13846 (x : Key → ℝ) : Integer.Sparse.eval row13846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13846, Integer.Sparse.eval_collectBalanced, rawRowCheck13846]

def rawRow13847 : Integer.Sparse Key := [(key2495, 4), (key2495, 4), (key2420, 4), (key2504, -2), (key2495, -2), (key2504, -2), (key2427, -2), (key2495, -2), (key2427, -2), (key2504, -2), (key2495, -2), (key2504, -2), (key2427, -2), (key2495, -2), (key2427, -2), (key2504, 4), (key2504, 4), (key2438, 4)]

theorem rawRowCheck13847 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form0 = rawRow13847 := by decide +kernel

def row13847 : Integer.Sparse Key := [(key2420, 4), (key2427, -8), (key2438, 4)]

theorem rowCheck13847 : row13847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13847 := by decide +kernel

theorem rowEval13847 (x : Key → ℝ) : Integer.Sparse.eval row13847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13847, Integer.Sparse.eval_collectBalanced, rawRowCheck13847]

def rawRow13848 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2504, 4), (key2420, -2), (key2427, -2), (key2420, -2), (key2495, -2), (key2427, -2), (key2495, -2), (key2427, -2), (key2438, -2), (key2427, -2), (key2504, -2), (key2438, -2), (key2504, -2), (key2427, 4), (key2427, 4), (key2495, 4)]

theorem rawRowCheck13848 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form0 = rawRow13848 := by decide +kernel

def row13848 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck13848 : row13848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13848 := by decide +kernel

theorem rowEval13848 (x : Key → ℝ) : Integer.Sparse.eval row13848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13848, Integer.Sparse.eval_collectBalanced, rawRowCheck13848]

def rawRow13849 : Integer.Sparse Key := [(key2427, 4), (key2504, 4), (key2427, 4), (key2427, -2), (key2420, -2), (key2495, -2), (key2420, -2), (key2495, -2), (key2427, -2), (key2438, -2), (key2427, -2), (key2504, -2), (key2427, -2), (key2504, -2), (key2438, -2), (key2427, 4), (key2495, 4), (key2427, 4)]

theorem rawRowCheck13849 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form0 = rawRow13849 := by decide +kernel

def row13849 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck13849 : row13849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13849 := by decide +kernel

theorem rowEval13849 (x : Key → ℝ) : Integer.Sparse.eval row13849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13849, Integer.Sparse.eval_collectBalanced, rawRowCheck13849]

def rawRow13850 : Integer.Sparse Key := [(key2504, 4), (key2427, 4), (key2427, 4), (key2495, -2), (key2495, -2), (key2427, -2), (key2427, -2), (key2420, -2), (key2420, -2), (key2504, -2), (key2504, -2), (key2438, -2), (key2438, -2), (key2427, -2), (key2427, -2), (key2495, 4), (key2427, 4), (key2427, 4)]

theorem rawRowCheck13850 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form0 = rawRow13850 := by decide +kernel

def row13850 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck13850 : row13850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13850 := by decide +kernel

theorem rowEval13850 (x : Key → ℝ) : Integer.Sparse.eval row13850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13850, Integer.Sparse.eval_collectBalanced, rawRowCheck13850]

def rawRow13851 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2504, 4), (key2427, -2), (key2438, -2), (key2427, -2), (key2504, -2), (key2438, -2), (key2504, -2), (key2420, -2), (key2427, -2), (key2420, -2), (key2495, -2), (key2427, -2), (key2495, -2), (key2427, 4), (key2427, 4), (key2495, 4)]

theorem rawRowCheck13851 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form0 = rawRow13851 := by decide +kernel

def row13851 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck13851 : row13851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13851 := by decide +kernel

theorem rowEval13851 (x : Key → ℝ) : Integer.Sparse.eval row13851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13851, Integer.Sparse.eval_collectBalanced, rawRowCheck13851]

def rawRow13852 : Integer.Sparse Key := [(key2427, 4), (key2504, 4), (key2427, 4), (key2438, -2), (key2427, -2), (key2504, -2), (key2427, -2), (key2504, -2), (key2438, -2), (key2427, -2), (key2420, -2), (key2495, -2), (key2420, -2), (key2495, -2), (key2427, -2), (key2427, 4), (key2495, 4), (key2427, 4)]

theorem rawRowCheck13852 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form0 = rawRow13852 := by decide +kernel

def row13852 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck13852 : row13852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13852 := by decide +kernel

theorem rowEval13852 (x : Key → ℝ) : Integer.Sparse.eval row13852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13852, Integer.Sparse.eval_collectBalanced, rawRowCheck13852]

def rawRow13853 : Integer.Sparse Key := [(key2504, 4), (key2427, 4), (key2427, 4), (key2504, -2), (key2504, -2), (key2438, -2), (key2438, -2), (key2427, -2), (key2427, -2), (key2495, -2), (key2495, -2), (key2427, -2), (key2427, -2), (key2420, -2), (key2420, -2), (key2495, 4), (key2427, 4), (key2427, 4)]

theorem rawRowCheck13853 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form0 = rawRow13853 := by decide +kernel

def row13853 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck13853 : row13853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13853 := by decide +kernel

theorem rowEval13853 (x : Key → ℝ) : Integer.Sparse.eval row13853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13853, Integer.Sparse.eval_collectBalanced, rawRowCheck13853]

def rawRow13854 : Integer.Sparse Key := [(key2438, 4), (key2438, 4), (key2438, 4), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2420, 4), (key2420, 4), (key2420, 4)]

theorem rawRowCheck13854 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form0 = rawRow13854 := by decide +kernel

def row13854 : Integer.Sparse Key := [(key2420, 12), (key2427, -24), (key2438, 12)]

theorem rowCheck13854 : row13854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13854 := by decide +kernel

theorem rowEval13854 (x : Key → ℝ) : Integer.Sparse.eval row13854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13854, Integer.Sparse.eval_collectBalanced, rawRowCheck13854]

def rawRow13855 : Integer.Sparse Key := [(key1050, -2), (key1050, -2), (key1058, -2), (key1058, 6), (key1050, -2), (key1050, -2), (key1058, -2), (key1050, 2), (key1050, 2), (key1136, 2), (key1136, 2), (key1138, 2), (key1138, 2), (key1058, -2), (key1138, -2), (key1138, -2), (key1058, 6), (key1058, -2), (key1138, -2), (key1138, -2)]

theorem rawRowCheck13855 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form1 = rawRow13855 := by decide +kernel

def row13855 : Integer.Sparse Key := [(key1050, -4), (key1058, 4), (key1136, 4), (key1138, -4)]

theorem rowCheck13855 : row13855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13855 := by decide +kernel

theorem rowEval13855 (x : Key → ℝ) : Integer.Sparse.eval row13855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13855, Integer.Sparse.eval_collectBalanced, rawRowCheck13855]

def rawRow13856 : Integer.Sparse Key := [(key1050, -2), (key1058, -2), (key1050, -2), (key1058, 6), (key1050, -2), (key1058, -2), (key1050, -2), (key1136, 2), (key1138, 2), (key1050, 2), (key1138, 2), (key1050, 2), (key1136, 2), (key1138, -2), (key1058, -2), (key1138, -2), (key1058, 6), (key1138, -2), (key1058, -2), (key1138, -2)]

theorem rawRowCheck13856 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form1 = rawRow13856 := by decide +kernel

def row13856 : Integer.Sparse Key := [(key1050, -4), (key1058, 4), (key1136, 4), (key1138, -4)]

theorem rowCheck13856 : row13856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13856 := by decide +kernel

theorem rowEval13856 (x : Key → ℝ) : Integer.Sparse.eval row13856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13856, Integer.Sparse.eval_collectBalanced, rawRowCheck13856]

def rawRow13857 : Integer.Sparse Key := [(key1058, -2), (key1050, -2), (key1050, -2), (key1058, 6), (key1058, -2), (key1050, -2), (key1050, -2), (key1138, 2), (key1136, 2), (key1138, 2), (key1050, 2), (key1136, 2), (key1050, 2), (key1138, -2), (key1138, -2), (key1058, -2), (key1058, 6), (key1138, -2), (key1138, -2), (key1058, -2)]

theorem rawRowCheck13857 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form1 = rawRow13857 := by decide +kernel

def row13857 : Integer.Sparse Key := [(key1050, -4), (key1058, 4), (key1136, 4), (key1138, -4)]

theorem rowCheck13857 : row13857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13857 := by decide +kernel

theorem rowEval13857 (x : Key → ℝ) : Integer.Sparse.eval row13857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13857, Integer.Sparse.eval_collectBalanced, rawRowCheck13857]

def rawRow13858 : Integer.Sparse Key := [(key1050, -2), (key1058, -2), (key1058, -2), (key1050, 6), (key1136, -2), (key1138, -2), (key1138, -2), (key1050, 2), (key1058, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1138, 2), (key1050, -2), (key1050, -2), (key1136, -2), (key1138, 6), (key1058, -2), (key1058, -2), (key1138, -2)]

theorem rawRowCheck13858 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form1 = rawRow13858 := by decide +kernel

def row13858 : Integer.Sparse Key := [(key1050, 4), (key1058, -4), (key1136, -4), (key1138, 4)]

theorem rowCheck13858 : row13858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13858 := by decide +kernel

theorem rowEval13858 (x : Key → ℝ) : Integer.Sparse.eval row13858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13858, Integer.Sparse.eval_collectBalanced, rawRowCheck13858]

def rawRow13859 : Integer.Sparse Key := [(key1058, -2), (key1050, -2), (key1058, -2), (key1050, 6), (key1138, -2), (key1136, -2), (key1138, -2), (key1058, 2), (key1050, 2), (key1138, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1050, -2), (key1136, -2), (key1050, -2), (key1138, 6), (key1058, -2), (key1138, -2), (key1058, -2)]

theorem rawRowCheck13859 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form1 = rawRow13859 := by decide +kernel

def row13859 : Integer.Sparse Key := [(key1050, 4), (key1058, -4), (key1136, -4), (key1138, 4)]

theorem rowCheck13859 : row13859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13859 := by decide +kernel

theorem rowEval13859 (x : Key → ℝ) : Integer.Sparse.eval row13859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13859, Integer.Sparse.eval_collectBalanced, rawRowCheck13859]

def rawRow13860 : Integer.Sparse Key := [(key1058, -2), (key1058, -2), (key1050, -2), (key1050, 6), (key1138, -2), (key1138, -2), (key1136, -2), (key1138, 2), (key1138, 2), (key1058, 2), (key1058, 2), (key1050, 2), (key1050, 2), (key1136, -2), (key1050, -2), (key1050, -2), (key1138, 6), (key1138, -2), (key1058, -2), (key1058, -2)]

theorem rawRowCheck13860 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form1 = rawRow13860 := by decide +kernel

def row13860 : Integer.Sparse Key := [(key1050, 4), (key1058, -4), (key1136, -4), (key1138, 4)]

theorem rowCheck13860 : row13860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13860 := by decide +kernel

theorem rowEval13860 (x : Key → ℝ) : Integer.Sparse.eval row13860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13860, Integer.Sparse.eval_collectBalanced, rawRowCheck13860]

def rawRow13861 : Integer.Sparse Key := [(key1136, -2), (key1138, -2), (key1138, -2), (key1138, 6), (key1050, -2), (key1058, -2), (key1058, -2), (key1050, 2), (key1058, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1138, 2), (key1058, -2), (key1058, -2), (key1138, -2), (key1050, 6), (key1050, -2), (key1050, -2), (key1136, -2)]

theorem rawRowCheck13861 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form1 = rawRow13861 := by decide +kernel

def row13861 : Integer.Sparse Key := [(key1050, 4), (key1058, -4), (key1136, -4), (key1138, 4)]

theorem rowCheck13861 : row13861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13861 := by decide +kernel

theorem rowEval13861 (x : Key → ℝ) : Integer.Sparse.eval row13861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13861, Integer.Sparse.eval_collectBalanced, rawRowCheck13861]

def rawRow13862 : Integer.Sparse Key := [(key1138, -2), (key1136, -2), (key1138, -2), (key1138, 6), (key1058, -2), (key1050, -2), (key1058, -2), (key1058, 2), (key1050, 2), (key1138, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1058, -2), (key1138, -2), (key1058, -2), (key1050, 6), (key1050, -2), (key1136, -2), (key1050, -2)]

theorem rawRowCheck13862 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form1 = rawRow13862 := by decide +kernel

def row13862 : Integer.Sparse Key := [(key1050, 4), (key1058, -4), (key1136, -4), (key1138, 4)]

theorem rowCheck13862 : row13862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13862 := by decide +kernel

theorem rowEval13862 (x : Key → ℝ) : Integer.Sparse.eval row13862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13862, Integer.Sparse.eval_collectBalanced, rawRowCheck13862]

def rawRow13863 : Integer.Sparse Key := [(key1138, -2), (key1138, -2), (key1136, -2), (key1138, 6), (key1058, -2), (key1058, -2), (key1050, -2), (key1138, 2), (key1138, 2), (key1058, 2), (key1058, 2), (key1050, 2), (key1050, 2), (key1138, -2), (key1058, -2), (key1058, -2), (key1050, 6), (key1136, -2), (key1050, -2), (key1050, -2)]

theorem rawRowCheck13863 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form1 = rawRow13863 := by decide +kernel

def row13863 : Integer.Sparse Key := [(key1050, 4), (key1058, -4), (key1136, -4), (key1138, 4)]

theorem rowCheck13863 : row13863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13863 := by decide +kernel

theorem rowEval13863 (x : Key → ℝ) : Integer.Sparse.eval row13863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13863, Integer.Sparse.eval_collectBalanced, rawRowCheck13863]

def rawRow13864 : Integer.Sparse Key := [(key1138, -2), (key1138, -2), (key1138, -2), (key1136, 6), (key1138, -2), (key1138, -2), (key1138, -2), (key1058, 2), (key1058, 2), (key1058, 2), (key1058, 2), (key1058, 2), (key1058, 2), (key1050, -2), (key1050, -2), (key1050, -2), (key1136, 6), (key1050, -2), (key1050, -2), (key1050, -2)]

theorem rawRowCheck13864 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form1 = rawRow13864 := by decide +kernel

def row13864 : Integer.Sparse Key := [(key1050, -12), (key1058, 12), (key1136, 12), (key1138, -12)]

theorem rowCheck13864 : row13864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13864 := by decide +kernel

theorem rowEval13864 (x : Key → ℝ) : Integer.Sparse.eval row13864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13864, Integer.Sparse.eval_collectBalanced, rawRowCheck13864]

def rawRow13865 : Integer.Sparse Key := [(key2416, -2), (key2416, -2), (key2423, -2), (key2423, 6), (key2416, -2), (key2416, -2), (key2423, -2), (key2416, 2), (key2416, 2), (key2489, 2), (key2489, 2), (key2491, 2), (key2491, 2), (key2423, -2), (key2491, -2), (key2491, -2), (key2423, 6), (key2423, -2), (key2491, -2), (key2491, -2)]

theorem rawRowCheck13865 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form2 = rawRow13865 := by decide +kernel

def row13865 : Integer.Sparse Key := [(key2416, -4), (key2423, 4), (key2489, 4), (key2491, -4)]

theorem rowCheck13865 : row13865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13865 := by decide +kernel

theorem rowEval13865 (x : Key → ℝ) : Integer.Sparse.eval row13865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13865, Integer.Sparse.eval_collectBalanced, rawRowCheck13865]

def rawRow13866 : Integer.Sparse Key := [(key2416, -2), (key2423, -2), (key2416, -2), (key2423, 6), (key2416, -2), (key2423, -2), (key2416, -2), (key2489, 2), (key2491, 2), (key2416, 2), (key2491, 2), (key2416, 2), (key2489, 2), (key2491, -2), (key2423, -2), (key2491, -2), (key2423, 6), (key2491, -2), (key2423, -2), (key2491, -2)]

theorem rawRowCheck13866 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form2 = rawRow13866 := by decide +kernel

def row13866 : Integer.Sparse Key := [(key2416, -4), (key2423, 4), (key2489, 4), (key2491, -4)]

theorem rowCheck13866 : row13866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13866 := by decide +kernel

theorem rowEval13866 (x : Key → ℝ) : Integer.Sparse.eval row13866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13866, Integer.Sparse.eval_collectBalanced, rawRowCheck13866]

def rawRow13867 : Integer.Sparse Key := [(key2423, -2), (key2416, -2), (key2416, -2), (key2423, 6), (key2423, -2), (key2416, -2), (key2416, -2), (key2491, 2), (key2489, 2), (key2491, 2), (key2416, 2), (key2489, 2), (key2416, 2), (key2491, -2), (key2491, -2), (key2423, -2), (key2423, 6), (key2491, -2), (key2491, -2), (key2423, -2)]

theorem rawRowCheck13867 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form2 = rawRow13867 := by decide +kernel

def row13867 : Integer.Sparse Key := [(key2416, -4), (key2423, 4), (key2489, 4), (key2491, -4)]

theorem rowCheck13867 : row13867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13867 := by decide +kernel

theorem rowEval13867 (x : Key → ℝ) : Integer.Sparse.eval row13867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13867, Integer.Sparse.eval_collectBalanced, rawRowCheck13867]

def rawRow13868 : Integer.Sparse Key := [(key2416, -2), (key2423, -2), (key2423, -2), (key2416, 6), (key2489, -2), (key2491, -2), (key2491, -2), (key2416, 2), (key2423, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2491, 2), (key2416, -2), (key2416, -2), (key2489, -2), (key2491, 6), (key2423, -2), (key2423, -2), (key2491, -2)]

theorem rawRowCheck13868 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form2 = rawRow13868 := by decide +kernel

def row13868 : Integer.Sparse Key := [(key2416, 4), (key2423, -4), (key2489, -4), (key2491, 4)]

theorem rowCheck13868 : row13868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13868 := by decide +kernel

theorem rowEval13868 (x : Key → ℝ) : Integer.Sparse.eval row13868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13868, Integer.Sparse.eval_collectBalanced, rawRowCheck13868]

def rawRow13869 : Integer.Sparse Key := [(key2423, -2), (key2416, -2), (key2423, -2), (key2416, 6), (key2491, -2), (key2489, -2), (key2491, -2), (key2423, 2), (key2416, 2), (key2491, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2416, -2), (key2489, -2), (key2416, -2), (key2491, 6), (key2423, -2), (key2491, -2), (key2423, -2)]

theorem rawRowCheck13869 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form2 = rawRow13869 := by decide +kernel

def row13869 : Integer.Sparse Key := [(key2416, 4), (key2423, -4), (key2489, -4), (key2491, 4)]

theorem rowCheck13869 : row13869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13869 := by decide +kernel

theorem rowEval13869 (x : Key → ℝ) : Integer.Sparse.eval row13869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13869, Integer.Sparse.eval_collectBalanced, rawRowCheck13869]

def rawRow13870 : Integer.Sparse Key := [(key2423, -2), (key2423, -2), (key2416, -2), (key2416, 6), (key2491, -2), (key2491, -2), (key2489, -2), (key2491, 2), (key2491, 2), (key2423, 2), (key2423, 2), (key2416, 2), (key2416, 2), (key2489, -2), (key2416, -2), (key2416, -2), (key2491, 6), (key2491, -2), (key2423, -2), (key2423, -2)]

theorem rawRowCheck13870 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form2 = rawRow13870 := by decide +kernel

def row13870 : Integer.Sparse Key := [(key2416, 4), (key2423, -4), (key2489, -4), (key2491, 4)]

theorem rowCheck13870 : row13870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13870 := by decide +kernel

theorem rowEval13870 (x : Key → ℝ) : Integer.Sparse.eval row13870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13870, Integer.Sparse.eval_collectBalanced, rawRowCheck13870]

def rawRow13871 : Integer.Sparse Key := [(key2489, -2), (key2491, -2), (key2491, -2), (key2491, 6), (key2416, -2), (key2423, -2), (key2423, -2), (key2416, 2), (key2423, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2491, 2), (key2423, -2), (key2423, -2), (key2491, -2), (key2416, 6), (key2416, -2), (key2416, -2), (key2489, -2)]

theorem rawRowCheck13871 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form2 = rawRow13871 := by decide +kernel

def row13871 : Integer.Sparse Key := [(key2416, 4), (key2423, -4), (key2489, -4), (key2491, 4)]

theorem rowCheck13871 : row13871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13871 := by decide +kernel

theorem rowEval13871 (x : Key → ℝ) : Integer.Sparse.eval row13871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13871, Integer.Sparse.eval_collectBalanced, rawRowCheck13871]

def rawRow13872 : Integer.Sparse Key := [(key2491, -2), (key2489, -2), (key2491, -2), (key2491, 6), (key2423, -2), (key2416, -2), (key2423, -2), (key2423, 2), (key2416, 2), (key2491, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2423, -2), (key2491, -2), (key2423, -2), (key2416, 6), (key2416, -2), (key2489, -2), (key2416, -2)]

theorem rawRowCheck13872 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form2 = rawRow13872 := by decide +kernel

def row13872 : Integer.Sparse Key := [(key2416, 4), (key2423, -4), (key2489, -4), (key2491, 4)]

theorem rowCheck13872 : row13872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13872 := by decide +kernel

theorem rowEval13872 (x : Key → ℝ) : Integer.Sparse.eval row13872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13872, Integer.Sparse.eval_collectBalanced, rawRowCheck13872]

def rawRow13873 : Integer.Sparse Key := [(key2491, -2), (key2491, -2), (key2489, -2), (key2491, 6), (key2423, -2), (key2423, -2), (key2416, -2), (key2491, 2), (key2491, 2), (key2423, 2), (key2423, 2), (key2416, 2), (key2416, 2), (key2491, -2), (key2423, -2), (key2423, -2), (key2416, 6), (key2489, -2), (key2416, -2), (key2416, -2)]

theorem rawRowCheck13873 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form2 = rawRow13873 := by decide +kernel

def row13873 : Integer.Sparse Key := [(key2416, 4), (key2423, -4), (key2489, -4), (key2491, 4)]

theorem rowCheck13873 : row13873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13873 := by decide +kernel

theorem rowEval13873 (x : Key → ℝ) : Integer.Sparse.eval row13873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13873, Integer.Sparse.eval_collectBalanced, rawRowCheck13873]

def rawRow13874 : Integer.Sparse Key := [(key2491, -2), (key2491, -2), (key2491, -2), (key2489, 6), (key2491, -2), (key2491, -2), (key2491, -2), (key2423, 2), (key2423, 2), (key2423, 2), (key2423, 2), (key2423, 2), (key2423, 2), (key2416, -2), (key2416, -2), (key2416, -2), (key2489, 6), (key2416, -2), (key2416, -2), (key2416, -2)]

theorem rawRowCheck13874 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form2 = rawRow13874 := by decide +kernel

def row13874 : Integer.Sparse Key := [(key2416, -12), (key2423, 12), (key2489, 12), (key2491, -12)]

theorem rowCheck13874 : row13874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13874 := by decide +kernel

theorem rowEval13874 (x : Key → ℝ) : Integer.Sparse.eval row13874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13874, Integer.Sparse.eval_collectBalanced, rawRowCheck13874]

def rawRow13875 : Integer.Sparse Key := [(key2677, 6), (key2677, -2), (key2708, -2), (key2708, -2), (key2677, 6), (key3045, -2), (key3094, -2), (key3094, -2), (key3045, -2), (key3059, -2), (key3059, -2), (key3045, -2), (key3094, -2), (key3094, -2), (key3059, 2), (key3059, 2), (key3094, 2), (key3094, 2), (key3122, 2), (key3122, 2)]

theorem rawRowCheck13875 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form3 = rawRow13875 := by decide +kernel

def row13875 : Integer.Sparse Key := [(key2677, 10), (key2708, -4), (key3045, -6), (key3094, -4), (key3122, 4)]

theorem rowCheck13875 : row13875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13875 := by decide +kernel

theorem rowEval13875 (x : Key → ℝ) : Integer.Sparse.eval row13875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13875, Integer.Sparse.eval_collectBalanced, rawRowCheck13875]

def rawRow13876 : Integer.Sparse Key := [(key2677, 6), (key2708, -2), (key2677, -2), (key2708, -2), (key2677, 6), (key3094, -2), (key3045, -2), (key3094, -2), (key3059, -2), (key3045, -2), (key3059, -2), (key3094, -2), (key3045, -2), (key3094, -2), (key3094, 2), (key3122, 2), (key3059, 2), (key3122, 2), (key3059, 2), (key3094, 2)]

theorem rawRowCheck13876 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form3 = rawRow13876 := by decide +kernel

def row13876 : Integer.Sparse Key := [(key2677, 10), (key2708, -4), (key3045, -6), (key3094, -4), (key3122, 4)]

theorem rowCheck13876 : row13876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13876 := by decide +kernel

theorem rowEval13876 (x : Key → ℝ) : Integer.Sparse.eval row13876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13876, Integer.Sparse.eval_collectBalanced, rawRowCheck13876]

def rawRow13877 : Integer.Sparse Key := [(key2677, 6), (key2708, -2), (key2708, -2), (key2677, -2), (key2677, 6), (key3094, -2), (key3094, -2), (key3045, -2), (key3059, -2), (key3059, -2), (key3045, -2), (key3094, -2), (key3094, -2), (key3045, -2), (key3122, 2), (key3094, 2), (key3122, 2), (key3059, 2), (key3094, 2), (key3059, 2)]

theorem rawRowCheck13877 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form3 = rawRow13877 := by decide +kernel

def row13877 : Integer.Sparse Key := [(key2677, 10), (key2708, -4), (key3045, -6), (key3094, -4), (key3122, 4)]

theorem rowCheck13877 : row13877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13877 := by decide +kernel

theorem rowEval13877 (x : Key → ℝ) : Integer.Sparse.eval row13877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13877, Integer.Sparse.eval_collectBalanced, rawRowCheck13877]

def rawRow13878 : Integer.Sparse Key := [(key2708, 6), (key2677, -2), (key2677, -2), (key2708, -2), (key2811, 6), (key2677, -2), (key3045, -2), (key3094, -2), (key3094, -2), (key3094, -2), (key3122, -2), (key3059, -2), (key3059, -2), (key3122, -2), (key3045, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3059, 2), (key3094, 2)]

theorem rawRowCheck13878 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form3 = rawRow13878 := by decide +kernel

def row13878 : Integer.Sparse Key := [(key2677, -6), (key2708, 4), (key2811, 6), (key3045, 2), (key3094, -2), (key3122, -4)]

theorem rowCheck13878 : row13878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13878 := by decide +kernel

theorem rowEval13878 (x : Key → ℝ) : Integer.Sparse.eval row13878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13878, Integer.Sparse.eval_collectBalanced, rawRowCheck13878]

def rawRow13879 : Integer.Sparse Key := [(key2708, 6), (key2677, -2), (key2708, -2), (key2677, -2), (key2811, 6), (key2677, -2), (key3094, -2), (key3045, -2), (key3094, -2), (key3122, -2), (key3094, -2), (key3059, -2), (key3122, -2), (key3059, -2), (key3059, 2), (key3045, 2), (key3094, 2), (key3045, 2), (key3094, 2), (key3059, 2)]

theorem rawRowCheck13879 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form3 = rawRow13879 := by decide +kernel

def row13879 : Integer.Sparse Key := [(key2677, -6), (key2708, 4), (key2811, 6), (key3045, 2), (key3094, -2), (key3122, -4)]

theorem rowCheck13879 : row13879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13879 := by decide +kernel

theorem rowEval13879 (x : Key → ℝ) : Integer.Sparse.eval row13879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13879, Integer.Sparse.eval_collectBalanced, rawRowCheck13879]

def rawRow13880 : Integer.Sparse Key := [(key2708, 6), (key2708, -2), (key2677, -2), (key2677, -2), (key2811, 6), (key2811, -2), (key2677, -2), (key3045, -2), (key3122, -2), (key3094, -2), (key3094, -2), (key3122, -2), (key3059, -2), (key3059, -2), (key3094, 2), (key3094, 2), (key3059, 2), (key3059, 2), (key3045, 2), (key3045, 2)]

theorem rawRowCheck13880 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form3 = rawRow13880 := by decide +kernel

def row13880 : Integer.Sparse Key := [(key2677, -6), (key2708, 4), (key2811, 4), (key3045, 2), (key3122, -4)]

theorem rowCheck13880 : row13880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13880 := by decide +kernel

theorem rowEval13880 (x : Key → ℝ) : Integer.Sparse.eval row13880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13880, Integer.Sparse.eval_collectBalanced, rawRowCheck13880]

def rawRow13881 : Integer.Sparse Key := [(key2811, 6), (key2811, -2), (key2811, -2), (key2861, -2), (key2708, 6), (key2708, -2), (key2708, -2), (key2861, -2), (key2677, -2), (key2677, -2), (key2708, -2), (key2677, -2), (key3045, -2), (key3094, -2), (key3045, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3059, 2), (key3094, 2)]

theorem rawRowCheck13881 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form3 = rawRow13881 := by decide +kernel

def row13881 : Integer.Sparse Key := [(key2677, -6), (key2811, 2), (key2861, -4), (key3045, 2), (key3059, 4), (key3094, 2)]

theorem rowCheck13881 : row13881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13881 := by decide +kernel

theorem rowEval13881 (x : Key → ℝ) : Integer.Sparse.eval row13881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13881, Integer.Sparse.eval_collectBalanced, rawRowCheck13881]

def rawRow13882 : Integer.Sparse Key := [(key2811, 6), (key2811, -2), (key2861, -2), (key2811, -2), (key2708, 6), (key2708, -2), (key2861, -2), (key2708, -2), (key2677, -2), (key2708, -2), (key2677, -2), (key2677, -2), (key3094, -2), (key3045, -2), (key3059, 2), (key3045, 2), (key3094, 2), (key3045, 2), (key3094, 2), (key3059, 2)]

theorem rawRowCheck13882 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form3 = rawRow13882 := by decide +kernel

def row13882 : Integer.Sparse Key := [(key2677, -6), (key2811, 2), (key2861, -4), (key3045, 2), (key3059, 4), (key3094, 2)]

theorem rowCheck13882 : row13882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13882 := by decide +kernel

theorem rowEval13882 (x : Key → ℝ) : Integer.Sparse.eval row13882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13882, Integer.Sparse.eval_collectBalanced, rawRowCheck13882]

def rawRow13883 : Integer.Sparse Key := [(key2811, 6), (key2861, -2), (key2811, -2), (key2811, -2), (key2708, 6), (key2861, -2), (key2708, -2), (key2708, -2), (key2708, -2), (key2677, -2), (key2677, -2), (key2811, -2), (key2677, -2), (key3045, -2), (key3094, 2), (key3094, 2), (key3059, 2), (key3059, 2), (key3045, 2), (key3045, 2)]

theorem rawRowCheck13883 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form3 = rawRow13883 := by decide +kernel

def row13883 : Integer.Sparse Key := [(key2677, -6), (key2861, -4), (key3045, 2), (key3059, 4), (key3094, 4)]

theorem rowCheck13883 : row13883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13883 := by decide +kernel

theorem rowEval13883 (x : Key → ℝ) : Integer.Sparse.eval row13883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13883, Integer.Sparse.eval_collectBalanced, rawRowCheck13883]

def rawRow13884 : Integer.Sparse Key := [(key2861, 6), (key2811, -2), (key2811, -2), (key2811, -2), (key2861, 6), (key2708, -2), (key2708, -2), (key2708, -2), (key2811, -2), (key2811, -2), (key2811, -2), (key2708, -2), (key2708, -2), (key2708, -2), (key2677, 2), (key2677, 2), (key2677, 2), (key3045, 2), (key3045, 2), (key3045, 2)]

theorem rawRowCheck13884 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form3 = rawRow13884 := by decide +kernel

def row13884 : Integer.Sparse Key := [(key2677, 6), (key2708, -12), (key2811, -12), (key2861, 12), (key3045, 6)]

theorem rowCheck13884 : row13884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13884 := by decide +kernel

theorem rowEval13884 (x : Key → ℝ) : Integer.Sparse.eval row13884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13884, Integer.Sparse.eval_collectBalanced, rawRowCheck13884]

def rawRow13885 : Integer.Sparse Key := [(key1047, -2), (key1047, -2), (key1057, -2), (key1057, 6), (key1047, -2), (key1047, -2), (key1057, -2), (key1047, 2), (key1047, 2), (key1133, 2), (key1133, 2), (key1137, 2), (key1137, 2), (key1057, -2), (key1137, -2), (key1137, -2), (key1057, 6), (key1057, -2), (key1137, -2), (key1137, -2)]

theorem rawRowCheck13885 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form4 = rawRow13885 := by decide +kernel

def row13885 : Integer.Sparse Key := [(key1047, -4), (key1057, 4), (key1133, 4), (key1137, -4)]

theorem rowCheck13885 : row13885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13885 := by decide +kernel

theorem rowEval13885 (x : Key → ℝ) : Integer.Sparse.eval row13885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13885, Integer.Sparse.eval_collectBalanced, rawRowCheck13885]

def rawRow13886 : Integer.Sparse Key := [(key1047, -2), (key1057, -2), (key1047, -2), (key1057, 6), (key1047, -2), (key1057, -2), (key1047, -2), (key1133, 2), (key1137, 2), (key1047, 2), (key1137, 2), (key1047, 2), (key1133, 2), (key1137, -2), (key1057, -2), (key1137, -2), (key1057, 6), (key1137, -2), (key1057, -2), (key1137, -2)]

theorem rawRowCheck13886 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form4 = rawRow13886 := by decide +kernel

def row13886 : Integer.Sparse Key := [(key1047, -4), (key1057, 4), (key1133, 4), (key1137, -4)]

theorem rowCheck13886 : row13886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13886 := by decide +kernel

theorem rowEval13886 (x : Key → ℝ) : Integer.Sparse.eval row13886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13886, Integer.Sparse.eval_collectBalanced, rawRowCheck13886]

def rawRow13887 : Integer.Sparse Key := [(key1057, -2), (key1047, -2), (key1047, -2), (key1057, 6), (key1057, -2), (key1047, -2), (key1047, -2), (key1137, 2), (key1133, 2), (key1137, 2), (key1047, 2), (key1133, 2), (key1047, 2), (key1137, -2), (key1137, -2), (key1057, -2), (key1057, 6), (key1137, -2), (key1137, -2), (key1057, -2)]

theorem rawRowCheck13887 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form4 = rawRow13887 := by decide +kernel

def row13887 : Integer.Sparse Key := [(key1047, -4), (key1057, 4), (key1133, 4), (key1137, -4)]

theorem rowCheck13887 : row13887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13887 := by decide +kernel

theorem rowEval13887 (x : Key → ℝ) : Integer.Sparse.eval row13887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13887, Integer.Sparse.eval_collectBalanced, rawRowCheck13887]

def rawRow13888 : Integer.Sparse Key := [(key1047, -2), (key1057, -2), (key1057, -2), (key1047, 6), (key1133, -2), (key1137, -2), (key1137, -2), (key1047, 2), (key1057, 2), (key1047, 2), (key1137, 2), (key1057, 2), (key1137, 2), (key1047, -2), (key1047, -2), (key1133, -2), (key1137, 6), (key1057, -2), (key1057, -2), (key1137, -2)]

theorem rawRowCheck13888 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form4 = rawRow13888 := by decide +kernel

def row13888 : Integer.Sparse Key := [(key1047, 4), (key1057, -4), (key1133, -4), (key1137, 4)]

theorem rowCheck13888 : row13888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13888 := by decide +kernel

theorem rowEval13888 (x : Key → ℝ) : Integer.Sparse.eval row13888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13888, Integer.Sparse.eval_collectBalanced, rawRowCheck13888]

def rawRow13889 : Integer.Sparse Key := [(key1057, -2), (key1047, -2), (key1057, -2), (key1047, 6), (key1137, -2), (key1133, -2), (key1137, -2), (key1057, 2), (key1047, 2), (key1137, 2), (key1047, 2), (key1137, 2), (key1057, 2), (key1047, -2), (key1133, -2), (key1047, -2), (key1137, 6), (key1057, -2), (key1137, -2), (key1057, -2)]

theorem rawRowCheck13889 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form4 = rawRow13889 := by decide +kernel

def row13889 : Integer.Sparse Key := [(key1047, 4), (key1057, -4), (key1133, -4), (key1137, 4)]

theorem rowCheck13889 : row13889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13889 := by decide +kernel

theorem rowEval13889 (x : Key → ℝ) : Integer.Sparse.eval row13889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13889, Integer.Sparse.eval_collectBalanced, rawRowCheck13889]

def rawRow13890 : Integer.Sparse Key := [(key1057, -2), (key1057, -2), (key1047, -2), (key1047, 6), (key1137, -2), (key1137, -2), (key1133, -2), (key1137, 2), (key1137, 2), (key1057, 2), (key1057, 2), (key1047, 2), (key1047, 2), (key1133, -2), (key1047, -2), (key1047, -2), (key1137, 6), (key1137, -2), (key1057, -2), (key1057, -2)]

theorem rawRowCheck13890 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form4 = rawRow13890 := by decide +kernel

def row13890 : Integer.Sparse Key := [(key1047, 4), (key1057, -4), (key1133, -4), (key1137, 4)]

theorem rowCheck13890 : row13890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13890 := by decide +kernel

theorem rowEval13890 (x : Key → ℝ) : Integer.Sparse.eval row13890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13890, Integer.Sparse.eval_collectBalanced, rawRowCheck13890]

def rawRow13891 : Integer.Sparse Key := [(key1133, -2), (key1137, -2), (key1137, -2), (key1137, 6), (key1047, -2), (key1057, -2), (key1057, -2), (key1047, 2), (key1057, 2), (key1047, 2), (key1137, 2), (key1057, 2), (key1137, 2), (key1057, -2), (key1057, -2), (key1137, -2), (key1047, 6), (key1047, -2), (key1047, -2), (key1133, -2)]

theorem rawRowCheck13891 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form4 = rawRow13891 := by decide +kernel

def row13891 : Integer.Sparse Key := [(key1047, 4), (key1057, -4), (key1133, -4), (key1137, 4)]

theorem rowCheck13891 : row13891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13891 := by decide +kernel

theorem rowEval13891 (x : Key → ℝ) : Integer.Sparse.eval row13891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13891, Integer.Sparse.eval_collectBalanced, rawRowCheck13891]

def rawRow13892 : Integer.Sparse Key := [(key1137, -2), (key1133, -2), (key1137, -2), (key1137, 6), (key1057, -2), (key1047, -2), (key1057, -2), (key1057, 2), (key1047, 2), (key1137, 2), (key1047, 2), (key1137, 2), (key1057, 2), (key1057, -2), (key1137, -2), (key1057, -2), (key1047, 6), (key1047, -2), (key1133, -2), (key1047, -2)]

theorem rawRowCheck13892 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form4 = rawRow13892 := by decide +kernel

def row13892 : Integer.Sparse Key := [(key1047, 4), (key1057, -4), (key1133, -4), (key1137, 4)]

theorem rowCheck13892 : row13892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13892 := by decide +kernel

theorem rowEval13892 (x : Key → ℝ) : Integer.Sparse.eval row13892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13892, Integer.Sparse.eval_collectBalanced, rawRowCheck13892]

def rawRow13893 : Integer.Sparse Key := [(key1137, -2), (key1137, -2), (key1133, -2), (key1137, 6), (key1057, -2), (key1057, -2), (key1047, -2), (key1137, 2), (key1137, 2), (key1057, 2), (key1057, 2), (key1047, 2), (key1047, 2), (key1137, -2), (key1057, -2), (key1057, -2), (key1047, 6), (key1133, -2), (key1047, -2), (key1047, -2)]

theorem rawRowCheck13893 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form4 = rawRow13893 := by decide +kernel

def row13893 : Integer.Sparse Key := [(key1047, 4), (key1057, -4), (key1133, -4), (key1137, 4)]

theorem rowCheck13893 : row13893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13893 := by decide +kernel

theorem rowEval13893 (x : Key → ℝ) : Integer.Sparse.eval row13893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13893, Integer.Sparse.eval_collectBalanced, rawRowCheck13893]

def rawRow13894 : Integer.Sparse Key := [(key1137, -2), (key1137, -2), (key1137, -2), (key1133, 6), (key1137, -2), (key1137, -2), (key1137, -2), (key1057, 2), (key1057, 2), (key1057, 2), (key1057, 2), (key1057, 2), (key1057, 2), (key1047, -2), (key1047, -2), (key1047, -2), (key1133, 6), (key1047, -2), (key1047, -2), (key1047, -2)]

theorem rawRowCheck13894 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form4 = rawRow13894 := by decide +kernel

def row13894 : Integer.Sparse Key := [(key1047, -12), (key1057, 12), (key1133, 12), (key1137, -12)]

theorem rowCheck13894 : row13894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13894 := by decide +kernel

theorem rowEval13894 (x : Key → ℝ) : Integer.Sparse.eval row13894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13894, Integer.Sparse.eval_collectBalanced, rawRowCheck13894]

def rawRow13895 : Integer.Sparse Key := [(key1055, 4), (key1143, 4), (key1143, 4), (key1063, -2), (key1063, -2), (key1143, -2), (key1143, -2), (key1153, -2), (key1153, -2), (key1063, -2), (key1063, -2), (key1143, -2), (key1143, -2), (key1153, -2), (key1153, -2), (key1074, 4), (key1153, 4), (key1153, 4)]

theorem rawRowCheck13895 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form5 = rawRow13895 := by decide +kernel

def row13895 : Integer.Sparse Key := [(key1055, 4), (key1063, -8), (key1074, 4)]

theorem rowCheck13895 : row13895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13895 := by decide +kernel

theorem rowEval13895 (x : Key → ℝ) : Integer.Sparse.eval row13895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13895, Integer.Sparse.eval_collectBalanced, rawRowCheck13895]

def rawRow13896 : Integer.Sparse Key := [(key1143, 4), (key1055, 4), (key1143, 4), (key1143, -2), (key1153, -2), (key1063, -2), (key1153, -2), (key1063, -2), (key1143, -2), (key1143, -2), (key1153, -2), (key1063, -2), (key1153, -2), (key1063, -2), (key1143, -2), (key1153, 4), (key1074, 4), (key1153, 4)]

theorem rawRowCheck13896 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form5 = rawRow13896 := by decide +kernel

def row13896 : Integer.Sparse Key := [(key1055, 4), (key1063, -8), (key1074, 4)]

theorem rowCheck13896 : row13896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13896 := by decide +kernel

theorem rowEval13896 (x : Key → ℝ) : Integer.Sparse.eval row13896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13896, Integer.Sparse.eval_collectBalanced, rawRowCheck13896]

def rawRow13897 : Integer.Sparse Key := [(key1143, 4), (key1143, 4), (key1055, 4), (key1153, -2), (key1143, -2), (key1153, -2), (key1063, -2), (key1143, -2), (key1063, -2), (key1153, -2), (key1143, -2), (key1153, -2), (key1063, -2), (key1143, -2), (key1063, -2), (key1153, 4), (key1153, 4), (key1074, 4)]

theorem rawRowCheck13897 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form5 = rawRow13897 := by decide +kernel

def row13897 : Integer.Sparse Key := [(key1055, 4), (key1063, -8), (key1074, 4)]

theorem rowCheck13897 : row13897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13897 := by decide +kernel

theorem rowEval13897 (x : Key → ℝ) : Integer.Sparse.eval row13897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13897, Integer.Sparse.eval_collectBalanced, rawRowCheck13897]

def rawRow13898 : Integer.Sparse Key := [(key1063, 4), (key1063, 4), (key1153, 4), (key1055, -2), (key1063, -2), (key1055, -2), (key1143, -2), (key1063, -2), (key1143, -2), (key1063, -2), (key1074, -2), (key1063, -2), (key1153, -2), (key1074, -2), (key1153, -2), (key1063, 4), (key1063, 4), (key1143, 4)]

theorem rawRowCheck13898 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form5 = rawRow13898 := by decide +kernel

def row13898 : Integer.Sparse Key := [(key1055, -4), (key1063, 8), (key1074, -4)]

theorem rowCheck13898 : row13898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13898 := by decide +kernel

theorem rowEval13898 (x : Key → ℝ) : Integer.Sparse.eval row13898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13898, Integer.Sparse.eval_collectBalanced, rawRowCheck13898]

def rawRow13899 : Integer.Sparse Key := [(key1063, 4), (key1153, 4), (key1063, 4), (key1063, -2), (key1055, -2), (key1143, -2), (key1055, -2), (key1143, -2), (key1063, -2), (key1074, -2), (key1063, -2), (key1153, -2), (key1063, -2), (key1153, -2), (key1074, -2), (key1063, 4), (key1143, 4), (key1063, 4)]

theorem rawRowCheck13899 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form5 = rawRow13899 := by decide +kernel

def row13899 : Integer.Sparse Key := [(key1055, -4), (key1063, 8), (key1074, -4)]

theorem rowCheck13899 : row13899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13899 := by decide +kernel

theorem rowEval13899 (x : Key → ℝ) : Integer.Sparse.eval row13899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13899, Integer.Sparse.eval_collectBalanced, rawRowCheck13899]

def rawRow13900 : Integer.Sparse Key := [(key1153, 4), (key1063, 4), (key1063, 4), (key1143, -2), (key1143, -2), (key1063, -2), (key1063, -2), (key1055, -2), (key1055, -2), (key1153, -2), (key1153, -2), (key1074, -2), (key1074, -2), (key1063, -2), (key1063, -2), (key1143, 4), (key1063, 4), (key1063, 4)]

theorem rawRowCheck13900 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form5 = rawRow13900 := by decide +kernel

def row13900 : Integer.Sparse Key := [(key1055, -4), (key1063, 8), (key1074, -4)]

theorem rowCheck13900 : row13900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13900 := by decide +kernel

theorem rowEval13900 (x : Key → ℝ) : Integer.Sparse.eval row13900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13900, Integer.Sparse.eval_collectBalanced, rawRowCheck13900]

def rawRow13901 : Integer.Sparse Key := [(key1063, 4), (key1063, 4), (key1153, 4), (key1063, -2), (key1074, -2), (key1063, -2), (key1153, -2), (key1074, -2), (key1153, -2), (key1055, -2), (key1063, -2), (key1055, -2), (key1143, -2), (key1063, -2), (key1143, -2), (key1063, 4), (key1063, 4), (key1143, 4)]

theorem rawRowCheck13901 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form5 = rawRow13901 := by decide +kernel

def row13901 : Integer.Sparse Key := [(key1055, -4), (key1063, 8), (key1074, -4)]

theorem rowCheck13901 : row13901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13901 := by decide +kernel

theorem rowEval13901 (x : Key → ℝ) : Integer.Sparse.eval row13901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13901, Integer.Sparse.eval_collectBalanced, rawRowCheck13901]

def rawRow13902 : Integer.Sparse Key := [(key1063, 4), (key1153, 4), (key1063, 4), (key1074, -2), (key1063, -2), (key1153, -2), (key1063, -2), (key1153, -2), (key1074, -2), (key1063, -2), (key1055, -2), (key1143, -2), (key1055, -2), (key1143, -2), (key1063, -2), (key1063, 4), (key1143, 4), (key1063, 4)]

theorem rawRowCheck13902 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form5 = rawRow13902 := by decide +kernel

def row13902 : Integer.Sparse Key := [(key1055, -4), (key1063, 8), (key1074, -4)]

theorem rowCheck13902 : row13902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13902 := by decide +kernel

theorem rowEval13902 (x : Key → ℝ) : Integer.Sparse.eval row13902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13902, Integer.Sparse.eval_collectBalanced, rawRowCheck13902]

def rawRow13903 : Integer.Sparse Key := [(key1153, 4), (key1063, 4), (key1063, 4), (key1153, -2), (key1153, -2), (key1074, -2), (key1074, -2), (key1063, -2), (key1063, -2), (key1143, -2), (key1143, -2), (key1063, -2), (key1063, -2), (key1055, -2), (key1055, -2), (key1143, 4), (key1063, 4), (key1063, 4)]

theorem rawRowCheck13903 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form5 = rawRow13903 := by decide +kernel

def row13903 : Integer.Sparse Key := [(key1055, -4), (key1063, 8), (key1074, -4)]

theorem rowCheck13903 : row13903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13903 := by decide +kernel

theorem rowEval13903 (x : Key → ℝ) : Integer.Sparse.eval row13903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13903, Integer.Sparse.eval_collectBalanced, rawRowCheck13903]

def rawRow13904 : Integer.Sparse Key := [(key1074, 4), (key1074, 4), (key1074, 4), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1055, 4), (key1055, 4), (key1055, 4)]

theorem rawRowCheck13904 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form5 = rawRow13904 := by decide +kernel

def row13904 : Integer.Sparse Key := [(key1055, 12), (key1063, -24), (key1074, 12)]

theorem rowCheck13904 : row13904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13904 := by decide +kernel

theorem rowEval13904 (x : Key → ℝ) : Integer.Sparse.eval row13904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13904, Integer.Sparse.eval_collectBalanced, rawRowCheck13904]

def rawRow13905 : Integer.Sparse Key := [(key2681, -1), (key2681, -1), (key2815, -1), (key2815, -1), (key2817, -1), (key2817, -1), (key2688, 2), (key2817, 2), (key2817, 2), (key2681, -1), (key2681, -1), (key2815, -1), (key2815, -1), (key2817, -1), (key2817, -1), (key2712, 2), (key2712, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2863, 2), (key2714, -1), (key2714, -1), (key2817, -1), (key2817, -1), (key2863, -1), (key2863, -1), (key2688, 2), (key2817, 2), (key2817, 2), (key2714, -1), (key2714, -1), (key2817, -1), (key2817, -1), (key2863, -1), (key2863, -1)]

theorem rawRowCheck13905 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form6 = rawRow13905 := by decide +kernel

def row13905 : Integer.Sparse Key := [(key2681, -4), (key2688, 4), (key2712, 4), (key2714, -4)]

theorem rowCheck13905 : row13905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13905 := by decide +kernel

theorem rowEval13905 (x : Key → ℝ) : Integer.Sparse.eval row13905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13905, Integer.Sparse.eval_collectBalanced, rawRowCheck13905]

def rawRow13906 : Integer.Sparse Key := [(key2815, -1), (key2817, -1), (key2681, -1), (key2817, -1), (key2681, -1), (key2815, -1), (key2817, 2), (key2688, 2), (key2817, 2), (key2815, -1), (key2817, -1), (key2681, -1), (key2817, -1), (key2681, -1), (key2815, -1), (key2815, 2), (key2863, 2), (key2712, 2), (key2863, 2), (key2712, 2), (key2815, 2), (key2817, -1), (key2863, -1), (key2714, -1), (key2863, -1), (key2714, -1), (key2817, -1), (key2817, 2), (key2688, 2), (key2817, 2), (key2817, -1), (key2863, -1), (key2714, -1), (key2863, -1), (key2714, -1), (key2817, -1)]

theorem rawRowCheck13906 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form6 = rawRow13906 := by decide +kernel

def row13906 : Integer.Sparse Key := [(key2681, -4), (key2688, 4), (key2712, 4), (key2714, -4)]

theorem rowCheck13906 : row13906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13906 := by decide +kernel

theorem rowEval13906 (x : Key → ℝ) : Integer.Sparse.eval row13906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13906, Integer.Sparse.eval_collectBalanced, rawRowCheck13906]

def rawRow13907 : Integer.Sparse Key := [(key2817, -1), (key2815, -1), (key2817, -1), (key2681, -1), (key2815, -1), (key2681, -1), (key2817, 2), (key2817, 2), (key2688, 2), (key2817, -1), (key2815, -1), (key2817, -1), (key2681, -1), (key2815, -1), (key2681, -1), (key2863, 2), (key2815, 2), (key2863, 2), (key2712, 2), (key2815, 2), (key2712, 2), (key2863, -1), (key2817, -1), (key2863, -1), (key2714, -1), (key2817, -1), (key2714, -1), (key2817, 2), (key2817, 2), (key2688, 2), (key2863, -1), (key2817, -1), (key2863, -1), (key2714, -1), (key2817, -1), (key2714, -1)]

theorem rawRowCheck13907 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form6 = rawRow13907 := by decide +kernel

def row13907 : Integer.Sparse Key := [(key2681, -4), (key2688, 4), (key2712, 4), (key2714, -4)]

theorem rowCheck13907 : row13907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13907 := by decide +kernel

theorem rowEval13907 (x : Key → ℝ) : Integer.Sparse.eval row13907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13907, Integer.Sparse.eval_collectBalanced, rawRowCheck13907]

def rawRow13908 : Integer.Sparse Key := [(key2681, -1), (key2688, -1), (key2681, -1), (key2817, -1), (key2688, -1), (key2817, -1), (key2681, 2), (key2681, 2), (key2815, 2), (key2712, -1), (key2714, -1), (key2712, -1), (key2863, -1), (key2714, -1), (key2863, -1), (key2681, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2817, 2), (key2681, -1), (key2712, -1), (key2681, -1), (key2815, -1), (key2712, -1), (key2815, -1), (key2714, 2), (key2714, 2), (key2863, 2), (key2688, -1), (key2714, -1), (key2688, -1), (key2817, -1), (key2714, -1), (key2817, -1)]

theorem rawRowCheck13908 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form6 = rawRow13908 := by decide +kernel

def row13908 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, -4), (key2714, 4)]

theorem rowCheck13908 : row13908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13908 := by decide +kernel

theorem rowEval13908 (x : Key → ℝ) : Integer.Sparse.eval row13908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13908, Integer.Sparse.eval_collectBalanced, rawRowCheck13908]

def rawRow13909 : Integer.Sparse Key := [(key2688, -1), (key2681, -1), (key2817, -1), (key2681, -1), (key2817, -1), (key2688, -1), (key2681, 2), (key2815, 2), (key2681, 2), (key2714, -1), (key2712, -1), (key2863, -1), (key2712, -1), (key2863, -1), (key2714, -1), (key2714, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2712, -1), (key2681, -1), (key2815, -1), (key2681, -1), (key2815, -1), (key2712, -1), (key2714, 2), (key2863, 2), (key2714, 2), (key2714, -1), (key2688, -1), (key2817, -1), (key2688, -1), (key2817, -1), (key2714, -1)]

theorem rawRowCheck13909 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form6 = rawRow13909 := by decide +kernel

def row13909 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, -4), (key2714, 4)]

theorem rowCheck13909 : row13909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13909 := by decide +kernel

theorem rowEval13909 (x : Key → ℝ) : Integer.Sparse.eval row13909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13909, Integer.Sparse.eval_collectBalanced, rawRowCheck13909]

def rawRow13910 : Integer.Sparse Key := [(key2817, -1), (key2817, -1), (key2688, -1), (key2688, -1), (key2681, -1), (key2681, -1), (key2815, 2), (key2681, 2), (key2681, 2), (key2863, -1), (key2863, -1), (key2714, -1), (key2714, -1), (key2712, -1), (key2712, -1), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2815, -1), (key2815, -1), (key2712, -1), (key2712, -1), (key2681, -1), (key2681, -1), (key2863, 2), (key2714, 2), (key2714, 2), (key2817, -1), (key2817, -1), (key2714, -1), (key2714, -1), (key2688, -1), (key2688, -1)]

theorem rawRowCheck13910 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form6 = rawRow13910 := by decide +kernel

def row13910 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, -4), (key2714, 4)]

theorem rowCheck13910 : row13910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13910 := by decide +kernel

theorem rowEval13910 (x : Key → ℝ) : Integer.Sparse.eval row13910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13910, Integer.Sparse.eval_collectBalanced, rawRowCheck13910]

def rawRow13911 : Integer.Sparse Key := [(key2712, -1), (key2714, -1), (key2712, -1), (key2863, -1), (key2714, -1), (key2863, -1), (key2714, 2), (key2714, 2), (key2863, 2), (key2681, -1), (key2688, -1), (key2681, -1), (key2817, -1), (key2688, -1), (key2817, -1), (key2681, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2817, 2), (key2688, -1), (key2714, -1), (key2688, -1), (key2817, -1), (key2714, -1), (key2817, -1), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, -1), (key2712, -1), (key2681, -1), (key2815, -1), (key2712, -1), (key2815, -1)]

theorem rawRowCheck13911 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form6 = rawRow13911 := by decide +kernel

def row13911 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, -4), (key2714, 4)]

theorem rowCheck13911 : row13911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13911 := by decide +kernel

theorem rowEval13911 (x : Key → ℝ) : Integer.Sparse.eval row13911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13911, Integer.Sparse.eval_collectBalanced, rawRowCheck13911]

def rawRow13912 : Integer.Sparse Key := [(key2714, -1), (key2712, -1), (key2863, -1), (key2712, -1), (key2863, -1), (key2714, -1), (key2714, 2), (key2863, 2), (key2714, 2), (key2688, -1), (key2681, -1), (key2817, -1), (key2681, -1), (key2817, -1), (key2688, -1), (key2714, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2714, -1), (key2688, -1), (key2817, -1), (key2688, -1), (key2817, -1), (key2714, -1), (key2681, 2), (key2815, 2), (key2681, 2), (key2712, -1), (key2681, -1), (key2815, -1), (key2681, -1), (key2815, -1), (key2712, -1)]

theorem rawRowCheck13912 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form6 = rawRow13912 := by decide +kernel

def row13912 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, -4), (key2714, 4)]

theorem rowCheck13912 : row13912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13912 := by decide +kernel

theorem rowEval13912 (x : Key → ℝ) : Integer.Sparse.eval row13912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13912, Integer.Sparse.eval_collectBalanced, rawRowCheck13912]

def rawRow13913 : Integer.Sparse Key := [(key2863, -1), (key2863, -1), (key2714, -1), (key2714, -1), (key2712, -1), (key2712, -1), (key2863, 2), (key2714, 2), (key2714, 2), (key2817, -1), (key2817, -1), (key2688, -1), (key2688, -1), (key2681, -1), (key2681, -1), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2817, -1), (key2817, -1), (key2714, -1), (key2714, -1), (key2688, -1), (key2688, -1), (key2815, 2), (key2681, 2), (key2681, 2), (key2815, -1), (key2815, -1), (key2712, -1), (key2712, -1), (key2681, -1), (key2681, -1)]

theorem rawRowCheck13913 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form6 = rawRow13913 := by decide +kernel

def row13913 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, -4), (key2714, 4)]

theorem rowCheck13913 : row13913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13913 := by decide +kernel

theorem rowEval13913 (x : Key → ℝ) : Integer.Sparse.eval row13913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13913, Integer.Sparse.eval_collectBalanced, rawRowCheck13913]

def rawRow13914 : Integer.Sparse Key := [(key2714, -1), (key2714, -1), (key2714, -1), (key2714, -1), (key2714, -1), (key2714, -1), (key2712, 2), (key2712, 2), (key2712, 2), (key2714, -1), (key2714, -1), (key2714, -1), (key2714, -1), (key2714, -1), (key2714, -1), (key2688, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2681, -1), (key2681, -1), (key2681, -1), (key2681, -1), (key2681, -1), (key2681, -1), (key2712, 2), (key2712, 2), (key2712, 2), (key2681, -1), (key2681, -1), (key2681, -1), (key2681, -1), (key2681, -1), (key2681, -1)]

theorem rawRowCheck13914 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form6 = rawRow13914 := by decide +kernel

def row13914 : Integer.Sparse Key := [(key2681, -12), (key2688, 12), (key2712, 12), (key2714, -12)]

theorem rowCheck13914 : row13914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13914 := by decide +kernel

theorem rowEval13914 (x : Key → ℝ) : Integer.Sparse.eval row13914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13914, Integer.Sparse.eval_collectBalanced, rawRowCheck13914]

def rawRow13915 : Integer.Sparse Key := [(key3079, 4), (key3084, 4), (key3084, 4), (key3084, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3084, -4), (key3099, -4), (key3099, 12)]

theorem rawRowCheck13915 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form7 = rawRow13915 := by decide +kernel

def row13915 : Integer.Sparse Key := [(key3079, 4), (key3084, -8), (key3099, 4)]

theorem rowCheck13915 : row13915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13915 := by decide +kernel

theorem rowEval13915 (x : Key → ℝ) : Integer.Sparse.eval row13915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck13915, Integer.Sparse.eval_collectBalanced, rawRowCheck13915]

def rawRow13916 : Integer.Sparse Key := [(key3084, 4), (key3079, 4), (key3084, 4), (key3084, -4), (key3099, -4), (key3084, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3099, 12)]

theorem rawRowCheck13916 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form7 = rawRow13916 := by decide +kernel

def row13916 : Integer.Sparse Key := [(key3079, 4), (key3084, -8), (key3099, 4)]

theorem rowCheck13916 : row13916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13916 := by decide +kernel

theorem rowEval13916 (x : Key → ℝ) : Integer.Sparse.eval row13916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck13916, Integer.Sparse.eval_collectBalanced, rawRowCheck13916]

def rawRow13917 : Integer.Sparse Key := [(key3084, 4), (key3084, 4), (key3079, 4), (key3099, -4), (key3084, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3084, -4), (key3099, 12)]

theorem rawRowCheck13917 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form7 = rawRow13917 := by decide +kernel

def row13917 : Integer.Sparse Key := [(key3079, 4), (key3084, -8), (key3099, 4)]

theorem rowCheck13917 : row13917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13917 := by decide +kernel

theorem rowEval13917 (x : Key → ℝ) : Integer.Sparse.eval row13917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck13917, Integer.Sparse.eval_collectBalanced, rawRowCheck13917]

def rawRow13918 : Integer.Sparse Key := [(key3084, 4), (key3084, 4), (key3099, 4), (key3079, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3099, -4), (key3099, -4), (key3084, 12)]

theorem rawRowCheck13918 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form7 = rawRow13918 := by decide +kernel

def row13918 : Integer.Sparse Key := [(key3079, -4), (key3084, 8), (key3099, -4)]

theorem rowCheck13918 : row13918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13918 := by decide +kernel

theorem rowEval13918 (x : Key → ℝ) : Integer.Sparse.eval row13918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck13918, Integer.Sparse.eval_collectBalanced, rawRowCheck13918]

def rawRow13919 : Integer.Sparse Key := [(key3084, 4), (key3099, 4), (key3084, 4), (key3084, -4), (key3079, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3099, -4), (key3084, 12)]

theorem rawRowCheck13919 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form7 = rawRow13919 := by decide +kernel

def row13919 : Integer.Sparse Key := [(key3079, -4), (key3084, 8), (key3099, -4)]

theorem rowCheck13919 : row13919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13919 := by decide +kernel

theorem rowEval13919 (x : Key → ℝ) : Integer.Sparse.eval row13919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck13919, Integer.Sparse.eval_collectBalanced, rawRowCheck13919]

def rawRow13920 : Integer.Sparse Key := [(key3099, 4), (key3084, 4), (key3084, 4), (key3084, -4), (key3084, -4), (key3079, -4), (key3099, -4), (key3099, -4), (key3084, -4), (key3084, 12)]

theorem rawRowCheck13920 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form7 = rawRow13920 := by decide +kernel

def row13920 : Integer.Sparse Key := [(key3079, -4), (key3084, 8), (key3099, -4)]

theorem rowCheck13920 : row13920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13920 := by decide +kernel

theorem rowEval13920 (x : Key → ℝ) : Integer.Sparse.eval row13920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck13920, Integer.Sparse.eval_collectBalanced, rawRowCheck13920]

def rawRow13921 : Integer.Sparse Key := [(key3084, 4), (key3084, 4), (key3099, 4), (key3084, -4), (key3099, -4), (key3099, -4), (key3079, -4), (key3084, -4), (key3084, -4), (key3084, 12)]

theorem rawRowCheck13921 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form7 = rawRow13921 := by decide +kernel

def row13921 : Integer.Sparse Key := [(key3079, -4), (key3084, 8), (key3099, -4)]

theorem rowCheck13921 : row13921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13921 := by decide +kernel

theorem rowEval13921 (x : Key → ℝ) : Integer.Sparse.eval row13921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck13921, Integer.Sparse.eval_collectBalanced, rawRowCheck13921]

def rawRow13922 : Integer.Sparse Key := [(key3084, 4), (key3099, 4), (key3084, 4), (key3099, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3079, -4), (key3084, -4), (key3084, 12)]

theorem rawRowCheck13922 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form7 = rawRow13922 := by decide +kernel

def row13922 : Integer.Sparse Key := [(key3079, -4), (key3084, 8), (key3099, -4)]

theorem rowCheck13922 : row13922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13922 := by decide +kernel

theorem rowEval13922 (x : Key → ℝ) : Integer.Sparse.eval row13922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck13922, Integer.Sparse.eval_collectBalanced, rawRowCheck13922]

def rawRow13923 : Integer.Sparse Key := [(key3099, 4), (key3084, 4), (key3084, 4), (key3099, -4), (key3099, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3079, -4), (key3084, 12)]

theorem rawRowCheck13923 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form7 = rawRow13923 := by decide +kernel

def row13923 : Integer.Sparse Key := [(key3079, -4), (key3084, 8), (key3099, -4)]

theorem rowCheck13923 : row13923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13923 := by decide +kernel

theorem rowEval13923 (x : Key → ℝ) : Integer.Sparse.eval row13923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck13923, Integer.Sparse.eval_collectBalanced, rawRowCheck13923]

def rawRow13924 : Integer.Sparse Key := [(key3099, 4), (key3099, 4), (key3099, 4), (key3084, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3079, 12)]

theorem rawRowCheck13924 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form7 = rawRow13924 := by decide +kernel

def row13924 : Integer.Sparse Key := [(key3079, 12), (key3084, -24), (key3099, 12)]

theorem rowCheck13924 : row13924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13924 := by decide +kernel

theorem rowEval13924 (x : Key → ℝ) : Integer.Sparse.eval row13924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck13924, Integer.Sparse.eval_collectBalanced, rawRowCheck13924]

def rawRow13925 : Integer.Sparse Key := [(key2456, 4), (key2456, 4), (key2531, 4), (key2456, -2), (key2459, -2), (key2456, -2), (key2531, -2), (key2459, -2), (key2531, -2), (key2517, -2), (key2520, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2561, -2), (key2520, 4), (key2520, 4), (key2561, 4)]

theorem rawRowCheck13925 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form0 = rawRow13925 := by decide +kernel

def row13925 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck13925 : row13925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13925 := by decide +kernel

theorem rowEval13925 (x : Key → ℝ) : Integer.Sparse.eval row13925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13925, Integer.Sparse.eval_collectBalanced, rawRowCheck13925]

def rawRow13926 : Integer.Sparse Key := [(key2456, 4), (key2531, 4), (key2456, 4), (key2459, -2), (key2456, -2), (key2531, -2), (key2456, -2), (key2531, -2), (key2459, -2), (key2520, -2), (key2517, -2), (key2561, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2520, 4), (key2561, 4), (key2520, 4)]

theorem rawRowCheck13926 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form0 = rawRow13926 := by decide +kernel

def row13926 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck13926 : row13926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13926 := by decide +kernel

theorem rowEval13926 (x : Key → ℝ) : Integer.Sparse.eval row13926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13926, Integer.Sparse.eval_collectBalanced, rawRowCheck13926]

def rawRow13927 : Integer.Sparse Key := [(key2531, 4), (key2456, 4), (key2456, 4), (key2531, -2), (key2531, -2), (key2459, -2), (key2459, -2), (key2456, -2), (key2456, -2), (key2561, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2517, -2), (key2561, 4), (key2520, 4), (key2520, 4)]

theorem rawRowCheck13927 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form0 = rawRow13927 := by decide +kernel

def row13927 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck13927 : row13927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13927 := by decide +kernel

theorem rowEval13927 (x : Key → ℝ) : Integer.Sparse.eval row13927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13927, Integer.Sparse.eval_collectBalanced, rawRowCheck13927]

def rawRow13928 : Integer.Sparse Key := [(key2459, 4), (key2459, 4), (key2459, 4), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2517, 4), (key2517, 4), (key2517, 4)]

theorem rawRowCheck13928 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13928 := by decide +kernel

def row13928 : Integer.Sparse Key := [(key2456, -12), (key2459, 12), (key2517, 12), (key2520, -12)]

theorem rowCheck13928 : row13928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13928 := by decide +kernel

theorem rowEval13928 (x : Key → ℝ) : Integer.Sparse.eval row13928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13928, Integer.Sparse.eval_collectBalanced, rawRowCheck13928]

def rawRow13929 : Integer.Sparse Key := [(key2456, 4), (key2456, 4), (key2531, 4), (key2517, -2), (key2520, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2561, -2), (key2456, -2), (key2459, -2), (key2456, -2), (key2531, -2), (key2459, -2), (key2531, -2), (key2520, 4), (key2520, 4), (key2561, 4)]

theorem rawRowCheck13929 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form0 = rawRow13929 := by decide +kernel

def row13929 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck13929 : row13929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13929 := by decide +kernel

theorem rowEval13929 (x : Key → ℝ) : Integer.Sparse.eval row13929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13929, Integer.Sparse.eval_collectBalanced, rawRowCheck13929]

def rawRow13930 : Integer.Sparse Key := [(key2456, 4), (key2531, 4), (key2456, 4), (key2520, -2), (key2517, -2), (key2561, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2459, -2), (key2456, -2), (key2531, -2), (key2456, -2), (key2531, -2), (key2459, -2), (key2520, 4), (key2561, 4), (key2520, 4)]

theorem rawRowCheck13930 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form0 = rawRow13930 := by decide +kernel

def row13930 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck13930 : row13930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13930 := by decide +kernel

theorem rowEval13930 (x : Key → ℝ) : Integer.Sparse.eval row13930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13930, Integer.Sparse.eval_collectBalanced, rawRowCheck13930]

def rawRow13931 : Integer.Sparse Key := [(key2531, 4), (key2456, 4), (key2456, 4), (key2561, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2517, -2), (key2531, -2), (key2531, -2), (key2459, -2), (key2459, -2), (key2456, -2), (key2456, -2), (key2561, 4), (key2520, 4), (key2520, 4)]

theorem rawRowCheck13931 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form0 = rawRow13931 := by decide +kernel

def row13931 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck13931 : row13931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13931 := by decide +kernel

theorem rowEval13931 (x : Key → ℝ) : Integer.Sparse.eval row13931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13931, Integer.Sparse.eval_collectBalanced, rawRowCheck13931]

def rawRow13932 : Integer.Sparse Key := [(key2361, 4), (key2517, 4), (key2561, 4), (key2361, -2), (key2364, -2), (key2456, -2), (key2531, -2), (key2520, -2), (key2561, -2), (key2361, -2), (key2364, -2), (key2456, -2), (key2531, -2), (key2520, -2), (key2561, -2), (key2364, 4), (key2459, 4), (key2531, 4)]

theorem rawRowCheck13932 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13932 := by decide +kernel

def row13932 : Integer.Sparse Key := [(key2456, -4), (key2459, 4), (key2517, 4), (key2520, -4)]

theorem rowCheck13932 : row13932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13932 := by decide +kernel

theorem rowEval13932 (x : Key → ℝ) : Integer.Sparse.eval row13932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13932, Integer.Sparse.eval_collectBalanced, rawRowCheck13932]

def rawRow13933 : Integer.Sparse Key := [(key2361, 4), (key2561, 4), (key2517, 4), (key2364, -2), (key2361, -2), (key2531, -2), (key2456, -2), (key2561, -2), (key2520, -2), (key2364, -2), (key2361, -2), (key2531, -2), (key2456, -2), (key2561, -2), (key2520, -2), (key2364, 4), (key2531, 4), (key2459, 4)]

theorem rawRowCheck13933 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13933 := by decide +kernel

def row13933 : Integer.Sparse Key := [(key2456, -4), (key2459, 4), (key2517, 4), (key2520, -4)]

theorem rowCheck13933 : row13933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13933 := by decide +kernel

theorem rowEval13933 (x : Key → ℝ) : Integer.Sparse.eval row13933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13933, Integer.Sparse.eval_collectBalanced, rawRowCheck13933]

def rawRow13934 : Integer.Sparse Key := [(key2517, 4), (key2361, 4), (key2561, 4), (key2456, -2), (key2520, -2), (key2361, -2), (key2561, -2), (key2364, -2), (key2531, -2), (key2456, -2), (key2520, -2), (key2361, -2), (key2561, -2), (key2364, -2), (key2531, -2), (key2459, 4), (key2364, 4), (key2531, 4)]

theorem rawRowCheck13934 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13934 := by decide +kernel

def row13934 : Integer.Sparse Key := [(key2456, -4), (key2459, 4), (key2517, 4), (key2520, -4)]

theorem rowCheck13934 : row13934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13934 := by decide +kernel

theorem rowEval13934 (x : Key → ℝ) : Integer.Sparse.eval row13934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13934, Integer.Sparse.eval_collectBalanced, rawRowCheck13934]

def rawRow13935 : Integer.Sparse Key := [(key2517, 4), (key2561, 4), (key2361, 4), (key2520, -2), (key2456, -2), (key2561, -2), (key2361, -2), (key2531, -2), (key2364, -2), (key2520, -2), (key2456, -2), (key2561, -2), (key2361, -2), (key2531, -2), (key2364, -2), (key2459, 4), (key2531, 4), (key2364, 4)]

theorem rawRowCheck13935 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13935 := by decide +kernel

def row13935 : Integer.Sparse Key := [(key2456, -4), (key2459, 4), (key2517, 4), (key2520, -4)]

theorem rowCheck13935 : row13935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13935 := by decide +kernel

theorem rowEval13935 (x : Key → ℝ) : Integer.Sparse.eval row13935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13935, Integer.Sparse.eval_collectBalanced, rawRowCheck13935]

def rawRow13936 : Integer.Sparse Key := [(key2561, 4), (key2361, 4), (key2517, 4), (key2531, -2), (key2561, -2), (key2364, -2), (key2520, -2), (key2361, -2), (key2456, -2), (key2531, -2), (key2561, -2), (key2364, -2), (key2520, -2), (key2361, -2), (key2456, -2), (key2531, 4), (key2364, 4), (key2459, 4)]

theorem rawRowCheck13936 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13936 := by decide +kernel

def row13936 : Integer.Sparse Key := [(key2456, -4), (key2459, 4), (key2517, 4), (key2520, -4)]

theorem rowCheck13936 : row13936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13936 := by decide +kernel

theorem rowEval13936 (x : Key → ℝ) : Integer.Sparse.eval row13936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13936, Integer.Sparse.eval_collectBalanced, rawRowCheck13936]

def rawRow13937 : Integer.Sparse Key := [(key2561, 4), (key2517, 4), (key2361, 4), (key2561, -2), (key2531, -2), (key2520, -2), (key2364, -2), (key2456, -2), (key2361, -2), (key2561, -2), (key2531, -2), (key2520, -2), (key2364, -2), (key2456, -2), (key2361, -2), (key2531, 4), (key2459, 4), (key2364, 4)]

theorem rawRowCheck13937 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13937 := by decide +kernel

def row13937 : Integer.Sparse Key := [(key2456, -4), (key2459, 4), (key2517, 4), (key2520, -4)]

theorem rowCheck13937 : row13937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13937 := by decide +kernel

theorem rowEval13937 (x : Key → ℝ) : Integer.Sparse.eval row13937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13937, Integer.Sparse.eval_collectBalanced, rawRowCheck13937]

def rawRow13938 : Integer.Sparse Key := [(key2364, 4), (key2520, 4), (key2520, 4), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2364, -2), (key2364, -2), (key2459, -2), (key2459, -2), (key2520, -2), (key2520, -2), (key2361, 4), (key2456, 4), (key2456, 4)]

theorem rawRowCheck13938 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13938 := by decide +kernel

def row13938 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck13938 : row13938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13938 := by decide +kernel

theorem rowEval13938 (x : Key → ℝ) : Integer.Sparse.eval row13938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13938, Integer.Sparse.eval_collectBalanced, rawRowCheck13938]

def rawRow13939 : Integer.Sparse Key := [(key2520, 4), (key2364, 4), (key2520, 4), (key2456, -2), (key2517, -2), (key2361, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2459, -2), (key2520, -2), (key2364, -2), (key2520, -2), (key2364, -2), (key2459, -2), (key2456, 4), (key2361, 4), (key2456, 4)]

theorem rawRowCheck13939 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13939 := by decide +kernel

def row13939 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck13939 : row13939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13939 := by decide +kernel

theorem rowEval13939 (x : Key → ℝ) : Integer.Sparse.eval row13939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13939, Integer.Sparse.eval_collectBalanced, rawRowCheck13939]

def rawRow13940 : Integer.Sparse Key := [(key2520, 4), (key2520, 4), (key2364, 4), (key2517, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2361, -2), (key2520, -2), (key2459, -2), (key2520, -2), (key2364, -2), (key2459, -2), (key2364, -2), (key2456, 4), (key2456, 4), (key2361, 4)]

theorem rawRowCheck13940 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13940 := by decide +kernel

def row13940 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck13940 : row13940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13940 := by decide +kernel

theorem rowEval13940 (x : Key → ℝ) : Integer.Sparse.eval row13940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13940, Integer.Sparse.eval_collectBalanced, rawRowCheck13940]

def rawRow13941 : Integer.Sparse Key := [(key2459, 4), (key2459, 4), (key2459, 4), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2517, 4), (key2517, 4), (key2517, 4)]

theorem rawRowCheck13941 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13941 := by decide +kernel

def row13941 : Integer.Sparse Key := [(key2456, -12), (key2459, 12), (key2517, 12), (key2520, -12)]

theorem rowCheck13941 : row13941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13941 := by decide +kernel

theorem rowEval13941 (x : Key → ℝ) : Integer.Sparse.eval row13941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13941, Integer.Sparse.eval_collectBalanced, rawRowCheck13941]

def rawRow13942 : Integer.Sparse Key := [(key2364, 4), (key2520, 4), (key2520, 4), (key2364, -2), (key2364, -2), (key2459, -2), (key2459, -2), (key2520, -2), (key2520, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2361, 4), (key2456, 4), (key2456, 4)]

theorem rawRowCheck13942 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13942 := by decide +kernel

def row13942 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck13942 : row13942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13942 := by decide +kernel

theorem rowEval13942 (x : Key → ℝ) : Integer.Sparse.eval row13942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13942, Integer.Sparse.eval_collectBalanced, rawRowCheck13942]

def rawRow13943 : Integer.Sparse Key := [(key2520, 4), (key2364, 4), (key2520, 4), (key2459, -2), (key2520, -2), (key2364, -2), (key2520, -2), (key2364, -2), (key2459, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, 4), (key2361, 4), (key2456, 4)]

theorem rawRowCheck13943 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13943 := by decide +kernel

def row13943 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck13943 : row13943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13943 := by decide +kernel

theorem rowEval13943 (x : Key → ℝ) : Integer.Sparse.eval row13943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13943, Integer.Sparse.eval_collectBalanced, rawRowCheck13943]

def rawRow13944 : Integer.Sparse Key := [(key2520, 4), (key2520, 4), (key2364, 4), (key2520, -2), (key2459, -2), (key2520, -2), (key2364, -2), (key2459, -2), (key2364, -2), (key2517, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2361, -2), (key2456, 4), (key2456, 4), (key2361, 4)]

theorem rawRowCheck13944 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13944 := by decide +kernel

def row13944 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck13944 : row13944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13944 := by decide +kernel

theorem rowEval13944 (x : Key → ℝ) : Integer.Sparse.eval row13944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13944, Integer.Sparse.eval_collectBalanced, rawRowCheck13944]

def rawRow13945 : Integer.Sparse Key := [(key972, -2), (key977, -2), (key977, -2), (key977, 6), (key1086, -2), (key1091, -2), (key1091, -2), (key1086, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1181, 2), (key1091, -2), (key1091, -2), (key1181, -2), (key1162, 6), (key1162, -2), (key1162, -2), (key1218, -2)]

theorem rawRowCheck13945 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form1 = rawRow13945 := by decide +kernel

def row13945 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck13945 : row13945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13945 := by decide +kernel

theorem rowEval13945 (x : Key → ℝ) : Integer.Sparse.eval row13945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13945, Integer.Sparse.eval_collectBalanced, rawRowCheck13945]

def rawRow13946 : Integer.Sparse Key := [(key977, -2), (key972, -2), (key977, -2), (key977, 6), (key1091, -2), (key1086, -2), (key1091, -2), (key1091, 2), (key1086, 2), (key1181, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1091, -2), (key1181, -2), (key1091, -2), (key1162, 6), (key1162, -2), (key1218, -2), (key1162, -2)]

theorem rawRowCheck13946 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form1 = rawRow13946 := by decide +kernel

def row13946 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck13946 : row13946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13946 := by decide +kernel

theorem rowEval13946 (x : Key → ℝ) : Integer.Sparse.eval row13946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13946, Integer.Sparse.eval_collectBalanced, rawRowCheck13946]

def rawRow13947 : Integer.Sparse Key := [(key977, -2), (key977, -2), (key972, -2), (key977, 6), (key1091, -2), (key1091, -2), (key1086, -2), (key1181, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1086, 2), (key1181, -2), (key1091, -2), (key1091, -2), (key1162, 6), (key1218, -2), (key1162, -2), (key1162, -2)]

theorem rawRowCheck13947 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form1 = rawRow13947 := by decide +kernel

def row13947 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck13947 : row13947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13947 := by decide +kernel

theorem rowEval13947 (x : Key → ℝ) : Integer.Sparse.eval row13947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13947, Integer.Sparse.eval_collectBalanced, rawRowCheck13947]

def rawRow13948 : Integer.Sparse Key := [(key977, -2), (key977, -2), (key977, -2), (key972, 6), (key1181, -2), (key1181, -2), (key1181, -2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1086, -2), (key1086, -2), (key1086, -2), (key1218, 6), (key1162, -2), (key1162, -2), (key1162, -2)]

theorem rawRowCheck13948 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13948 := by decide +kernel

def row13948 : Integer.Sparse Key := [(key972, 6), (key977, -6), (key1086, -6), (key1091, 12), (key1162, -6), (key1181, -6), (key1218, 6)]

theorem rowCheck13948 : row13948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13948 := by decide +kernel

theorem rowEval13948 (x : Key → ℝ) : Integer.Sparse.eval row13948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13948, Integer.Sparse.eval_collectBalanced, rawRowCheck13948]

def rawRow13949 : Integer.Sparse Key := [(key1086, -2), (key1091, -2), (key1091, -2), (key1162, 6), (key972, -2), (key977, -2), (key977, -2), (key1086, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1181, 2), (key1162, -2), (key1162, -2), (key1218, -2), (key977, 6), (key1091, -2), (key1091, -2), (key1181, -2)]

theorem rawRowCheck13949 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form1 = rawRow13949 := by decide +kernel

def row13949 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck13949 : row13949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13949 := by decide +kernel

theorem rowEval13949 (x : Key → ℝ) : Integer.Sparse.eval row13949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13949, Integer.Sparse.eval_collectBalanced, rawRowCheck13949]

def rawRow13950 : Integer.Sparse Key := [(key1091, -2), (key1086, -2), (key1091, -2), (key1162, 6), (key977, -2), (key972, -2), (key977, -2), (key1091, 2), (key1086, 2), (key1181, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1162, -2), (key1218, -2), (key1162, -2), (key977, 6), (key1091, -2), (key1181, -2), (key1091, -2)]

theorem rawRowCheck13950 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form1 = rawRow13950 := by decide +kernel

def row13950 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck13950 : row13950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13950 := by decide +kernel

theorem rowEval13950 (x : Key → ℝ) : Integer.Sparse.eval row13950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13950, Integer.Sparse.eval_collectBalanced, rawRowCheck13950]

def rawRow13951 : Integer.Sparse Key := [(key1091, -2), (key1091, -2), (key1086, -2), (key1162, 6), (key977, -2), (key977, -2), (key972, -2), (key1181, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1086, 2), (key1218, -2), (key1162, -2), (key1162, -2), (key977, 6), (key1181, -2), (key1091, -2), (key1091, -2)]

theorem rawRowCheck13951 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form1 = rawRow13951 := by decide +kernel

def row13951 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck13951 : row13951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13951 := by decide +kernel

theorem rowEval13951 (x : Key → ℝ) : Integer.Sparse.eval row13951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13951, Integer.Sparse.eval_collectBalanced, rawRowCheck13951]

end MUB6.Certificate.GramRows

end OAI
