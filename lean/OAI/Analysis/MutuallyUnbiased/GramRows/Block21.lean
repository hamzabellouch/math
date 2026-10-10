import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow768 : Integer.Sparse Key := [(key2778, -2), (key2792, -2), (key2784, -2), (key2851, 1), (key2858, 1), (key2801, 1), (key2919, 1), (key2807, 1), (key2918, 1), (key2624, 2), (key2638, 2), (key2630, 2), (key2851, -1), (key2858, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2624, -1), (key2638, -1), (key2608, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2698, 1), (key2752, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2724, 1)]

theorem rawRowCheck768 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form2 = rawRow768 := by decide +kernel

def row768 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

theorem rowCheck768 : row768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow768 := by decide +kernel

theorem rowEval768 (x : Key → ℝ) : Integer.Sparse.eval row768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck768, Integer.Sparse.eval_collectBalanced, rawRowCheck768]

def rawRow769 : Integer.Sparse Key := [(key2792, -2), (key2778, -2), (key2784, -2), (key2858, 1), (key2851, 1), (key2919, 1), (key2801, 1), (key2918, 1), (key2807, 1), (key2638, 2), (key2624, 2), (key2630, 2), (key2858, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key3021, -1), (key2704, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2608, -1), (key2638, -1), (key2614, -1), (key2752, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2724, 1), (key2669, 1)]

theorem rawRowCheck769 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form2 = rawRow769 := by decide +kernel

def row769 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

theorem rowCheck769 : row769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow769 := by decide +kernel

theorem rowEval769 (x : Key → ℝ) : Integer.Sparse.eval row769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck769, Integer.Sparse.eval_collectBalanced, rawRowCheck769]

def rawRow770 : Integer.Sparse Key := [(key2784, -2), (key2792, -2), (key2778, -2), (key2918, 1), (key2919, 1), (key2807, 1), (key2858, 1), (key2801, 1), (key2851, 1), (key2630, 2), (key2638, 2), (key2624, 2), (key3021, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2698, -1), (key2851, -1), (key2657, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2608, -1), (key2624, -1), (key2724, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2663, 1), (key2698, 1)]

theorem rawRowCheck770 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form2 = rawRow770 := by decide +kernel

def row770 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

theorem rowCheck770 : row770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow770 := by decide +kernel

theorem rowEval770 (x : Key → ℝ) : Integer.Sparse.eval row770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck770, Integer.Sparse.eval_collectBalanced, rawRowCheck770]

def rawRow771 : Integer.Sparse Key := [(key2792, -2), (key2784, -2), (key2778, -2), (key2919, 1), (key2918, 1), (key2858, 1), (key2807, 1), (key2851, 1), (key2801, 1), (key2638, 2), (key2630, 2), (key2624, 2), (key3022, -1), (key3021, -1), (key2858, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key2659, -1), (key2657, -1), (key2638, -1), (key2614, -1), (key2624, -1), (key2608, -1), (key2757, 1), (key2724, 1), (key2752, 1), (key2669, 1), (key2698, 1), (key2663, 1)]

theorem rawRowCheck771 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form2 = rawRow771 := by decide +kernel

def row771 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

theorem rowCheck771 : row771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow771 := by decide +kernel

theorem rowEval771 (x : Key → ℝ) : Integer.Sparse.eval row771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck771, Integer.Sparse.eval_collectBalanced, rawRowCheck771]

def rawRow772 : Integer.Sparse Key := [(key2801, -2), (key2807, -2), (key2827, -2), (key2778, 1), (key2784, 1), (key2851, 1), (key2918, 1), (key2868, 1), (key2922, 1), (key2698, 2), (key2704, 2), (key2724, 2), (key2624, -1), (key2630, -1), (key2851, -1), (key3021, -1), (key2868, -1), (key3025, -1), (key2663, -1), (key2669, -1), (key2698, -1), (key2752, -1), (key2724, -1), (key2757, -1), (key2608, 1), (key2614, 1), (key2801, 1), (key2827, 1), (key3011, 1), (key3016, 1)]

theorem rawRowCheck772 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form2 = rawRow772 := by decide +kernel

def row772 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2827, -1), (key2918, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

theorem rowCheck772 : row772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow772 := by decide +kernel

theorem rowEval772 (x : Key → ℝ) : Integer.Sparse.eval row772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck772, Integer.Sparse.eval_collectBalanced, rawRowCheck772]

def rawRow773 : Integer.Sparse Key := [(key2807, -2), (key2801, -2), (key2827, -2), (key2784, 1), (key2778, 1), (key2918, 1), (key2851, 1), (key2922, 1), (key2868, 1), (key2704, 2), (key2698, 2), (key2724, 2), (key2630, -1), (key2624, -1), (key3021, -1), (key2851, -1), (key3025, -1), (key2868, -1), (key2669, -1), (key2663, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2724, -1), (key2614, 1), (key2608, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key3011, 1)]

theorem rawRowCheck773 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form2 = rawRow773 := by decide +kernel

def row773 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2827, -1), (key2918, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

theorem rowCheck773 : row773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow773 := by decide +kernel

theorem rowEval773 (x : Key → ℝ) : Integer.Sparse.eval row773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck773, Integer.Sparse.eval_collectBalanced, rawRowCheck773]

def rawRow774 : Integer.Sparse Key := [(key2801, -2), (key2827, -2), (key2807, -2), (key2851, 1), (key2868, 1), (key2778, 1), (key2922, 1), (key2784, 1), (key2918, 1), (key2698, 2), (key2724, 2), (key2704, 2), (key2851, -1), (key2868, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2698, -1), (key2724, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2801, 1), (key2827, 1), (key2608, 1), (key3016, 1), (key2614, 1), (key2827, 1)]

theorem rawRowCheck774 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form2 = rawRow774 := by decide +kernel

def row774 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2918, 1), (key2922, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

theorem rowCheck774 : row774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow774 := by decide +kernel

theorem rowEval774 (x : Key → ℝ) : Integer.Sparse.eval row774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck774, Integer.Sparse.eval_collectBalanced, rawRowCheck774]

def rawRow775 : Integer.Sparse Key := [(key2827, -2), (key2801, -2), (key2807, -2), (key2868, 1), (key2851, 1), (key2922, 1), (key2778, 1), (key2918, 1), (key2784, 1), (key2724, 2), (key2698, 2), (key2704, 2), (key2868, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key3021, -1), (key2630, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2752, -1), (key2669, -1), (key2827, 1), (key2801, 1), (key3016, 1), (key2608, 1), (key2827, 1), (key2614, 1)]

theorem rawRowCheck775 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form2 = rawRow775 := by decide +kernel

def row775 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2918, 1), (key2922, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

theorem rowCheck775 : row775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow775 := by decide +kernel

theorem rowEval775 (x : Key → ℝ) : Integer.Sparse.eval row775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck775, Integer.Sparse.eval_collectBalanced, rawRowCheck775]

def rawRow776 : Integer.Sparse Key := [(key2807, -2), (key2827, -2), (key2801, -2), (key2918, 1), (key2922, 1), (key2784, 1), (key2868, 1), (key2778, 1), (key2851, 1), (key2704, 2), (key2724, 2), (key2698, 2), (key3021, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2624, -1), (key2851, -1), (key2752, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2663, -1), (key2698, -1), (key3011, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2608, 1), (key2801, 1)]

theorem rawRowCheck776 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form2 = rawRow776 := by decide +kernel

def row776 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2827, -1), (key2918, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

theorem rowCheck776 : row776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow776 := by decide +kernel

theorem rowEval776 (x : Key → ℝ) : Integer.Sparse.eval row776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck776, Integer.Sparse.eval_collectBalanced, rawRowCheck776]

def rawRow777 : Integer.Sparse Key := [(key2827, -2), (key2807, -2), (key2801, -2), (key2922, 1), (key2918, 1), (key2868, 1), (key2784, 1), (key2851, 1), (key2778, 1), (key2724, 2), (key2704, 2), (key2698, 2), (key3025, -1), (key3021, -1), (key2868, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key2757, -1), (key2752, -1), (key2724, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key3016, 1), (key3011, 1), (key2827, 1), (key2614, 1), (key2801, 1), (key2608, 1)]

theorem rawRowCheck777 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form2 = rawRow777 := by decide +kernel

def row777 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2827, -1), (key2918, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

theorem rowCheck777 : row777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow777 := by decide +kernel

theorem rowEval777 (x : Key → ℝ) : Integer.Sparse.eval row777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck777, Integer.Sparse.eval_collectBalanced, rawRowCheck777]

def rawRow778 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1076, -2), (key1033, 1), (key1041, 1), (key1033, 1), (key1076, 1), (key1041, 1), (key1076, 1), (key1111, 2), (key1111, 2), (key1155, 2), (key1111, -1), (key1127, -1), (key1111, -1), (key1155, -1), (key1127, -1), (key1155, -1), (key1190, -1), (key1193, -1), (key1190, -1), (key1212, -1), (key1193, -1), (key1212, -1), (key1190, 1), (key1199, 1), (key1190, 1), (key1212, 1), (key1199, 1), (key1212, 1)]

theorem rawRowCheck778 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form0 = rawRow778 := by decide +kernel

def row778 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

theorem rowCheck778 : row778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow778 := by decide +kernel

theorem rowEval778 (x : Key → ℝ) : Integer.Sparse.eval row778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck778, Integer.Sparse.eval_collectBalanced, rawRowCheck778]

def rawRow779 : Integer.Sparse Key := [(key1033, -2), (key1076, -2), (key1033, -2), (key1041, 1), (key1033, 1), (key1076, 1), (key1033, 1), (key1076, 1), (key1041, 1), (key1111, 2), (key1155, 2), (key1111, 2), (key1127, -1), (key1111, -1), (key1155, -1), (key1111, -1), (key1155, -1), (key1127, -1), (key1193, -1), (key1190, -1), (key1212, -1), (key1190, -1), (key1212, -1), (key1193, -1), (key1199, 1), (key1190, 1), (key1212, 1), (key1190, 1), (key1212, 1), (key1199, 1)]

theorem rawRowCheck779 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form0 = rawRow779 := by decide +kernel

def row779 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

theorem rowCheck779 : row779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow779 := by decide +kernel

theorem rowEval779 (x : Key → ℝ) : Integer.Sparse.eval row779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck779, Integer.Sparse.eval_collectBalanced, rawRowCheck779]

def rawRow780 : Integer.Sparse Key := [(key1076, -2), (key1033, -2), (key1033, -2), (key1076, 1), (key1076, 1), (key1041, 1), (key1041, 1), (key1033, 1), (key1033, 1), (key1155, 2), (key1111, 2), (key1111, 2), (key1155, -1), (key1155, -1), (key1127, -1), (key1127, -1), (key1111, -1), (key1111, -1), (key1212, -1), (key1212, -1), (key1193, -1), (key1193, -1), (key1190, -1), (key1190, -1), (key1212, 1), (key1212, 1), (key1199, 1), (key1199, 1), (key1190, 1), (key1190, 1)]

theorem rawRowCheck780 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form0 = rawRow780 := by decide +kernel

def row780 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

theorem rowCheck780 : row780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow780 := by decide +kernel

theorem rowEval780 (x : Key → ℝ) : Integer.Sparse.eval row780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck780, Integer.Sparse.eval_collectBalanced, rawRowCheck780]

def rawRow781 : Integer.Sparse Key := [(key1041, -2), (key1041, -2), (key1041, -2), (key1033, 1), (key1033, 1), (key1033, 1), (key1033, 1), (key1033, 1), (key1033, 1), (key1127, 2), (key1127, 2), (key1127, 2), (key1111, -1), (key1111, -1), (key1111, -1), (key1111, -1), (key1111, -1), (key1111, -1), (key1199, -1), (key1199, -1), (key1199, -1), (key1199, -1), (key1199, -1), (key1199, -1), (key1193, 1), (key1193, 1), (key1193, 1), (key1193, 1), (key1193, 1), (key1193, 1)]

theorem rawRowCheck781 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form0 = rawRow781 := by decide +kernel

def row781 : Integer.Sparse Key := [(key1033, 6), (key1041, -6), (key1111, -6), (key1127, 6), (key1193, 6), (key1199, -6)]

theorem rowCheck781 : row781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow781 := by decide +kernel

theorem rowEval781 (x : Key → ℝ) : Integer.Sparse.eval row781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck781, Integer.Sparse.eval_collectBalanced, rawRowCheck781]

def rawRow782 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1155, -2), (key1190, 1), (key1193, 1), (key1190, 1), (key1212, 1), (key1193, 1), (key1212, 1), (key1033, 2), (key1033, 2), (key1076, 2), (key1190, -1), (key1199, -1), (key1190, -1), (key1212, -1), (key1199, -1), (key1212, -1), (key1033, -1), (key1041, -1), (key1033, -1), (key1076, -1), (key1041, -1), (key1076, -1), (key1111, 1), (key1127, 1), (key1111, 1), (key1155, 1), (key1127, 1), (key1155, 1)]

theorem rawRowCheck782 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form0 = rawRow782 := by decide +kernel

def row782 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

theorem rowCheck782 : row782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow782 := by decide +kernel

theorem rowEval782 (x : Key → ℝ) : Integer.Sparse.eval row782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck782, Integer.Sparse.eval_collectBalanced, rawRowCheck782]

def rawRow783 : Integer.Sparse Key := [(key1111, -2), (key1155, -2), (key1111, -2), (key1193, 1), (key1190, 1), (key1212, 1), (key1190, 1), (key1212, 1), (key1193, 1), (key1033, 2), (key1076, 2), (key1033, 2), (key1199, -1), (key1190, -1), (key1212, -1), (key1190, -1), (key1212, -1), (key1199, -1), (key1041, -1), (key1033, -1), (key1076, -1), (key1033, -1), (key1076, -1), (key1041, -1), (key1127, 1), (key1111, 1), (key1155, 1), (key1111, 1), (key1155, 1), (key1127, 1)]

theorem rawRowCheck783 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form0 = rawRow783 := by decide +kernel

def row783 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

theorem rowCheck783 : row783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow783 := by decide +kernel

theorem rowEval783 (x : Key → ℝ) : Integer.Sparse.eval row783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck783, Integer.Sparse.eval_collectBalanced, rawRowCheck783]

def rawRow784 : Integer.Sparse Key := [(key1155, -2), (key1111, -2), (key1111, -2), (key1212, 1), (key1212, 1), (key1193, 1), (key1193, 1), (key1190, 1), (key1190, 1), (key1076, 2), (key1033, 2), (key1033, 2), (key1212, -1), (key1212, -1), (key1199, -1), (key1199, -1), (key1190, -1), (key1190, -1), (key1076, -1), (key1076, -1), (key1041, -1), (key1041, -1), (key1033, -1), (key1033, -1), (key1155, 1), (key1155, 1), (key1127, 1), (key1127, 1), (key1111, 1), (key1111, 1)]

theorem rawRowCheck784 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form0 = rawRow784 := by decide +kernel

def row784 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

theorem rowCheck784 : row784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow784 := by decide +kernel

theorem rowEval784 (x : Key → ℝ) : Integer.Sparse.eval row784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck784, Integer.Sparse.eval_collectBalanced, rawRowCheck784]

def rawRow785 : Integer.Sparse Key := [(key1006, -2), (key1193, -2), (key1193, -2), (key998, 1), (key998, 1), (key1111, 1), (key1111, 1), (key1190, 1), (key1190, 1), (key1019, 2), (key1199, 2), (key1199, 2), (key998, -1), (key998, -1), (key1033, -1), (key1033, -1), (key1190, -1), (key1190, -1), (key1019, -1), (key1019, -1), (key1127, -1), (key1127, -1), (key1199, -1), (key1199, -1), (key1006, 1), (key1006, 1), (key1041, 1), (key1041, 1), (key1193, 1), (key1193, 1)]

theorem rawRowCheck785 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form0 = rawRow785 := by decide +kernel

def row785 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

theorem rowCheck785 : row785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow785 := by decide +kernel

theorem rowEval785 (x : Key → ℝ) : Integer.Sparse.eval row785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck785, Integer.Sparse.eval_collectBalanced, rawRowCheck785]

def rawRow786 : Integer.Sparse Key := [(key1193, -2), (key1006, -2), (key1193, -2), (key1111, 1), (key1190, 1), (key998, 1), (key1190, 1), (key998, 1), (key1111, 1), (key1199, 2), (key1019, 2), (key1199, 2), (key1033, -1), (key1190, -1), (key998, -1), (key1190, -1), (key998, -1), (key1033, -1), (key1127, -1), (key1199, -1), (key1019, -1), (key1199, -1), (key1019, -1), (key1127, -1), (key1041, 1), (key1193, 1), (key1006, 1), (key1193, 1), (key1006, 1), (key1041, 1)]

theorem rawRowCheck786 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form0 = rawRow786 := by decide +kernel

def row786 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

theorem rowCheck786 : row786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow786 := by decide +kernel

theorem rowEval786 (x : Key → ℝ) : Integer.Sparse.eval row786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck786, Integer.Sparse.eval_collectBalanced, rawRowCheck786]

def rawRow787 : Integer.Sparse Key := [(key1193, -2), (key1193, -2), (key1006, -2), (key1190, 1), (key1111, 1), (key1190, 1), (key998, 1), (key1111, 1), (key998, 1), (key1199, 2), (key1199, 2), (key1019, 2), (key1190, -1), (key1033, -1), (key1190, -1), (key998, -1), (key1033, -1), (key998, -1), (key1199, -1), (key1127, -1), (key1199, -1), (key1019, -1), (key1127, -1), (key1019, -1), (key1193, 1), (key1041, 1), (key1193, 1), (key1006, 1), (key1041, 1), (key1006, 1)]

theorem rawRowCheck787 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form0 = rawRow787 := by decide +kernel

def row787 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

theorem rowCheck787 : row787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow787 := by decide +kernel

theorem rowEval787 (x : Key → ℝ) : Integer.Sparse.eval row787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck787, Integer.Sparse.eval_collectBalanced, rawRowCheck787]

def rawRow788 : Integer.Sparse Key := [(key1127, -2), (key1127, -2), (key1127, -2), (key1199, 1), (key1199, 1), (key1199, 1), (key1199, 1), (key1199, 1), (key1199, 1), (key1041, 2), (key1041, 2), (key1041, 2), (key1193, -1), (key1193, -1), (key1193, -1), (key1193, -1), (key1193, -1), (key1193, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1111, 1), (key1111, 1), (key1111, 1), (key1111, 1), (key1111, 1), (key1111, 1)]

theorem rawRowCheck788 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form0 = rawRow788 := by decide +kernel

def row788 : Integer.Sparse Key := [(key1033, -6), (key1041, 6), (key1111, 6), (key1127, -6), (key1193, -6), (key1199, 6)]

theorem rowCheck788 : row788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow788 := by decide +kernel

theorem rowEval788 (x : Key → ℝ) : Integer.Sparse.eval row788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck788, Integer.Sparse.eval_collectBalanced, rawRowCheck788]

def rawRow789 : Integer.Sparse Key := [(key1019, -2), (key1199, -2), (key1199, -2), (key1019, 1), (key1019, 1), (key1127, 1), (key1127, 1), (key1199, 1), (key1199, 1), (key1006, 2), (key1193, 2), (key1193, 2), (key1006, -1), (key1006, -1), (key1041, -1), (key1041, -1), (key1193, -1), (key1193, -1), (key998, -1), (key998, -1), (key1111, -1), (key1111, -1), (key1190, -1), (key1190, -1), (key998, 1), (key998, 1), (key1033, 1), (key1033, 1), (key1190, 1), (key1190, 1)]

theorem rawRowCheck789 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form0 = rawRow789 := by decide +kernel

def row789 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

theorem rowCheck789 : row789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow789 := by decide +kernel

theorem rowEval789 (x : Key → ℝ) : Integer.Sparse.eval row789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck789, Integer.Sparse.eval_collectBalanced, rawRowCheck789]

def rawRow790 : Integer.Sparse Key := [(key1199, -2), (key1019, -2), (key1199, -2), (key1127, 1), (key1199, 1), (key1019, 1), (key1199, 1), (key1019, 1), (key1127, 1), (key1193, 2), (key1006, 2), (key1193, 2), (key1041, -1), (key1193, -1), (key1006, -1), (key1193, -1), (key1006, -1), (key1041, -1), (key1111, -1), (key1190, -1), (key998, -1), (key1190, -1), (key998, -1), (key1111, -1), (key1033, 1), (key1190, 1), (key998, 1), (key1190, 1), (key998, 1), (key1033, 1)]

theorem rawRowCheck790 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form0 = rawRow790 := by decide +kernel

def row790 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

theorem rowCheck790 : row790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow790 := by decide +kernel

theorem rowEval790 (x : Key → ℝ) : Integer.Sparse.eval row790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck790, Integer.Sparse.eval_collectBalanced, rawRowCheck790]

def rawRow791 : Integer.Sparse Key := [(key1199, -2), (key1199, -2), (key1019, -2), (key1199, 1), (key1127, 1), (key1199, 1), (key1019, 1), (key1127, 1), (key1019, 1), (key1193, 2), (key1193, 2), (key1006, 2), (key1193, -1), (key1041, -1), (key1193, -1), (key1006, -1), (key1041, -1), (key1006, -1), (key1190, -1), (key1111, -1), (key1190, -1), (key998, -1), (key1111, -1), (key998, -1), (key1190, 1), (key1033, 1), (key1190, 1), (key998, 1), (key1033, 1), (key998, 1)]

theorem rawRowCheck791 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form0 = rawRow791 := by decide +kernel

def row791 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

theorem rowCheck791 : row791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow791 := by decide +kernel

theorem rowEval791 (x : Key → ℝ) : Integer.Sparse.eval row791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck791, Integer.Sparse.eval_collectBalanced, rawRowCheck791]

def rawRow792 : Integer.Sparse Key := [(key20, -6), (key20, 2), (key20, 2), (key31, 2), (key45, 6), (key45, -2), (key45, -2), (key70, -2), (key102, -2), (key102, -2), (key111, -2), (key102, 2), (key102, 2), (key133, 2)]

theorem rawRowCheck792 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form1 = rawRow792 := by decide +kernel

def row792 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

theorem rowCheck792 : row792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow792 := by decide +kernel

theorem rowEval792 (x : Key → ℝ) : Integer.Sparse.eval row792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck792, Integer.Sparse.eval_collectBalanced, rawRowCheck792]

def rawRow793 : Integer.Sparse Key := [(key20, -6), (key20, 2), (key31, 2), (key20, 2), (key45, 6), (key45, -2), (key70, -2), (key45, -2), (key102, -2), (key111, -2), (key102, -2), (key102, 2), (key133, 2), (key102, 2)]

theorem rawRowCheck793 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form1 = rawRow793 := by decide +kernel

def row793 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

theorem rowCheck793 : row793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow793 := by decide +kernel

theorem rowEval793 (x : Key → ℝ) : Integer.Sparse.eval row793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck793, Integer.Sparse.eval_collectBalanced, rawRowCheck793]

def rawRow794 : Integer.Sparse Key := [(key20, -6), (key31, 2), (key20, 2), (key20, 2), (key45, 6), (key70, -2), (key45, -2), (key45, -2), (key111, -2), (key102, -2), (key102, -2), (key133, 2), (key102, 2), (key102, 2)]

theorem rawRowCheck794 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form1 = rawRow794 := by decide +kernel

def row794 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

theorem rowCheck794 : row794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow794 := by decide +kernel

theorem rowEval794 (x : Key → ℝ) : Integer.Sparse.eval row794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck794, Integer.Sparse.eval_collectBalanced, rawRowCheck794]

def rawRow795 : Integer.Sparse Key := [(key31, -6), (key20, 2), (key20, 2), (key20, 2), (key70, 6), (key45, -2), (key45, -2), (key45, -2), (key133, -2), (key133, -2), (key133, -2), (key111, 2), (key111, 2), (key111, 2)]

theorem rawRowCheck795 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form1 = rawRow795 := by decide +kernel

def row795 : Integer.Sparse Key := [(key20, 6), (key31, -6), (key45, -6), (key70, 6), (key111, 6), (key133, -6)]

theorem rowCheck795 : row795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow795 := by decide +kernel

theorem rowEval795 (x : Key → ℝ) : Integer.Sparse.eval row795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck795, Integer.Sparse.eval_collectBalanced, rawRowCheck795]

def rawRow796 : Integer.Sparse Key := [(key45, -6), (key102, 2), (key102, 2), (key111, 2), (key20, 6), (key102, -2), (key102, -2), (key133, -2), (key20, -2), (key20, -2), (key31, -2), (key45, 2), (key45, 2), (key70, 2)]

theorem rawRowCheck796 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form1 = rawRow796 := by decide +kernel

def row796 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

theorem rowCheck796 : row796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow796 := by decide +kernel

theorem rowEval796 (x : Key → ℝ) : Integer.Sparse.eval row796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck796, Integer.Sparse.eval_collectBalanced, rawRowCheck796]

def rawRow797 : Integer.Sparse Key := [(key45, -6), (key102, 2), (key111, 2), (key102, 2), (key20, 6), (key102, -2), (key133, -2), (key102, -2), (key20, -2), (key31, -2), (key20, -2), (key45, 2), (key70, 2), (key45, 2)]

theorem rawRowCheck797 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form1 = rawRow797 := by decide +kernel

def row797 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

theorem rowCheck797 : row797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow797 := by decide +kernel

theorem rowEval797 (x : Key → ℝ) : Integer.Sparse.eval row797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck797, Integer.Sparse.eval_collectBalanced, rawRowCheck797]

def rawRow798 : Integer.Sparse Key := [(key45, -6), (key111, 2), (key102, 2), (key102, 2), (key20, 6), (key133, -2), (key102, -2), (key102, -2), (key31, -2), (key20, -2), (key20, -2), (key70, 2), (key45, 2), (key45, 2)]

theorem rawRowCheck798 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form1 = rawRow798 := by decide +kernel

def row798 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

theorem rowCheck798 : row798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow798 := by decide +kernel

theorem rowEval798 (x : Key → ℝ) : Integer.Sparse.eval row798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck798, Integer.Sparse.eval_collectBalanced, rawRowCheck798]

def rawRow799 : Integer.Sparse Key := [(key111, -6), (key45, 2), (key102, 2), (key102, 2), (key133, 6), (key20, -2), (key102, -2), (key102, -2), (key70, -2), (key133, -2), (key133, -2), (key31, 2), (key111, 2), (key111, 2)]

theorem rawRowCheck799 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form1 = rawRow799 := by decide +kernel

def row799 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

theorem rowCheck799 : row799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow799 := by decide +kernel

theorem rowEval799 (x : Key → ℝ) : Integer.Sparse.eval row799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck799, Integer.Sparse.eval_collectBalanced, rawRowCheck799]

end MUB6.Certificate.GramRows

end OAI
