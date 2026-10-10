import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
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

def rawRow18560 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key1230, 24), (key1026, 24), (key991, 24)]

theorem rawRowCheck18560 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form1 = rawRow18560 := by decide +kernel

def row18560 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18560 : row18560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18560 := by decide +kernel

theorem rowEval18560 (x : Key → ℝ) : Integer.Sparse.eval row18560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18560, Integer.Sparse.eval_collectBalanced, rawRowCheck18560]

def rawRow18561 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key991, 24), (key1026, 24), (key1104, 24)]

theorem rawRowCheck18561 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form1 = rawRow18561 := by decide +kernel

def row18561 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18561 : row18561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18561 := by decide +kernel

theorem rowEval18561 (x : Key → ℝ) : Integer.Sparse.eval row18561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18561, Integer.Sparse.eval_collectBalanced, rawRowCheck18561]

def rawRow18562 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key991, 24), (key1104, 24), (key1026, 24)]

theorem rawRowCheck18562 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form1 = rawRow18562 := by decide +kernel

def row18562 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18562 : row18562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18562 := by decide +kernel

theorem rowEval18562 (x : Key → ℝ) : Integer.Sparse.eval row18562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18562, Integer.Sparse.eval_collectBalanced, rawRowCheck18562]

def rawRow18563 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key1026, 24), (key991, 24), (key1104, 24)]

theorem rawRowCheck18563 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form1 = rawRow18563 := by decide +kernel

def row18563 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18563 : row18563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18563 := by decide +kernel

theorem rowEval18563 (x : Key → ℝ) : Integer.Sparse.eval row18563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18563, Integer.Sparse.eval_collectBalanced, rawRowCheck18563]

def rawRow18564 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key1026, 24), (key1104, 24), (key991, 24)]

theorem rawRowCheck18564 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form1 = rawRow18564 := by decide +kernel

def row18564 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18564 : row18564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18564 := by decide +kernel

theorem rowEval18564 (x : Key → ℝ) : Integer.Sparse.eval row18564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18564, Integer.Sparse.eval_collectBalanced, rawRowCheck18564]

def rawRow18565 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key1104, 24), (key991, 24), (key1026, 24)]

theorem rawRowCheck18565 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form1 = rawRow18565 := by decide +kernel

def row18565 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18565 : row18565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18565 := by decide +kernel

theorem rowEval18565 (x : Key → ℝ) : Integer.Sparse.eval row18565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18565, Integer.Sparse.eval_collectBalanced, rawRowCheck18565]

def rawRow18566 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key1104, 24), (key1026, 24), (key991, 24)]

theorem rawRowCheck18566 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form1 = rawRow18566 := by decide +kernel

def row18566 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18566 : row18566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18566 := by decide +kernel

theorem rowEval18566 (x : Key → ℝ) : Integer.Sparse.eval row18566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18566, Integer.Sparse.eval_collectBalanced, rawRowCheck18566]

def rawRow18567 : Integer.Sparse Key := [(key1230, 24), (key991, 24), (key1026, 24), (key1104, 24), (key1104, 24)]

theorem rawRowCheck18567 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form1 = rawRow18567 := by decide +kernel

def row18567 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18567 : row18567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18567 := by decide +kernel

theorem rowEval18567 (x : Key → ℝ) : Integer.Sparse.eval row18567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18567, Integer.Sparse.eval_collectBalanced, rawRowCheck18567]

def rawRow18568 : Integer.Sparse Key := [(key1230, 24), (key991, 24), (key1104, 24), (key1026, 24), (key1104, 24)]

theorem rawRowCheck18568 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form1 = rawRow18568 := by decide +kernel

def row18568 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18568 : row18568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18568 := by decide +kernel

theorem rowEval18568 (x : Key → ℝ) : Integer.Sparse.eval row18568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18568, Integer.Sparse.eval_collectBalanced, rawRowCheck18568]

def rawRow18569 : Integer.Sparse Key := [(key1230, 24), (key991, 24), (key1104, 24), (key1104, 24), (key1026, 24)]

theorem rawRowCheck18569 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form1 = rawRow18569 := by decide +kernel

def row18569 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18569 : row18569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18569 := by decide +kernel

theorem rowEval18569 (x : Key → ℝ) : Integer.Sparse.eval row18569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18569, Integer.Sparse.eval_collectBalanced, rawRowCheck18569]

def rawRow18570 : Integer.Sparse Key := [(key1230, 24), (key1026, 24), (key991, 24), (key1104, 24), (key1104, 24)]

theorem rawRowCheck18570 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form1 = rawRow18570 := by decide +kernel

def row18570 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18570 : row18570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18570 := by decide +kernel

theorem rowEval18570 (x : Key → ℝ) : Integer.Sparse.eval row18570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18570, Integer.Sparse.eval_collectBalanced, rawRowCheck18570]

def rawRow18571 : Integer.Sparse Key := [(key1230, 24), (key1026, 24), (key1104, 24), (key991, 24), (key1104, 24)]

theorem rawRowCheck18571 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form1 = rawRow18571 := by decide +kernel

def row18571 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18571 : row18571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18571 := by decide +kernel

theorem rowEval18571 (x : Key → ℝ) : Integer.Sparse.eval row18571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18571, Integer.Sparse.eval_collectBalanced, rawRowCheck18571]

def rawRow18572 : Integer.Sparse Key := [(key1230, 24), (key1026, 24), (key1104, 24), (key1104, 24), (key991, 24)]

theorem rawRowCheck18572 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form1 = rawRow18572 := by decide +kernel

def row18572 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18572 : row18572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18572 := by decide +kernel

theorem rowEval18572 (x : Key → ℝ) : Integer.Sparse.eval row18572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18572, Integer.Sparse.eval_collectBalanced, rawRowCheck18572]

def rawRow18573 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key991, 24), (key1026, 24), (key1104, 24)]

theorem rawRowCheck18573 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form1 = rawRow18573 := by decide +kernel

def row18573 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18573 : row18573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18573 := by decide +kernel

theorem rowEval18573 (x : Key → ℝ) : Integer.Sparse.eval row18573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18573, Integer.Sparse.eval_collectBalanced, rawRowCheck18573]

def rawRow18574 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key991, 24), (key1104, 24), (key1026, 24)]

theorem rawRowCheck18574 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form1 = rawRow18574 := by decide +kernel

def row18574 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18574 : row18574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18574 := by decide +kernel

theorem rowEval18574 (x : Key → ℝ) : Integer.Sparse.eval row18574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18574, Integer.Sparse.eval_collectBalanced, rawRowCheck18574]

def rawRow18575 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key1026, 24), (key991, 24), (key1104, 24)]

theorem rawRowCheck18575 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form1 = rawRow18575 := by decide +kernel

def row18575 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18575 : row18575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18575 := by decide +kernel

theorem rowEval18575 (x : Key → ℝ) : Integer.Sparse.eval row18575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18575, Integer.Sparse.eval_collectBalanced, rawRowCheck18575]

def rawRow18576 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key1026, 24), (key1104, 24), (key991, 24)]

theorem rawRowCheck18576 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form1 = rawRow18576 := by decide +kernel

def row18576 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18576 : row18576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18576 := by decide +kernel

theorem rowEval18576 (x : Key → ℝ) : Integer.Sparse.eval row18576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18576, Integer.Sparse.eval_collectBalanced, rawRowCheck18576]

def rawRow18577 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key1104, 24), (key991, 24), (key1026, 24)]

theorem rawRowCheck18577 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form1 = rawRow18577 := by decide +kernel

def row18577 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18577 : row18577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18577 := by decide +kernel

theorem rowEval18577 (x : Key → ℝ) : Integer.Sparse.eval row18577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18577, Integer.Sparse.eval_collectBalanced, rawRowCheck18577]

def rawRow18578 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key1104, 24), (key1026, 24), (key991, 24)]

theorem rawRowCheck18578 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form1 = rawRow18578 := by decide +kernel

def row18578 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

theorem rowCheck18578 : row18578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18578 := by decide +kernel

theorem rowEval18578 (x : Key → ℝ) : Integer.Sparse.eval row18578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18578, Integer.Sparse.eval_collectBalanced, rawRowCheck18578]

def rawRow18579 : Integer.Sparse Key := [(key2608, 2), (key2614, 2), (key2614, 2), (key2624, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2630, 2), (key2638, 2), (key2657, 2), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 2), (key2669, 2), (key2698, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2724, 2), (key2752, 2), (key2752, 2), (key2757, 2), (key2778, 2), (key2784, 2), (key2778, 2), (key2792, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2919, 2), (key2922, 2), (key3007, 2), (key3007, 2), (key3009, 2), (key3011, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key3022, 2), (key3025, 2)]

theorem rawRowCheck18579 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form2 = rawRow18579 := by decide +kernel

def row18579 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18579 : row18579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18579 := by decide +kernel

theorem rowEval18579 (x : Key → ℝ) : Integer.Sparse.eval row18579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18579, Integer.Sparse.eval_collectBalanced, rawRowCheck18579]

def rawRow18580 : Integer.Sparse Key := [(key2614, 2), (key2608, 2), (key2614, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2624, 2), (key2638, 2), (key2630, 2), (key2657, 2), (key2659, 2), (key2657, 2), (key2669, 2), (key2663, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2752, 2), (key2757, 2), (key2752, 2), (key2784, 2), (key2778, 2), (key2792, 2), (key2778, 2), (key2792, 2), (key2784, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2918, 2), (key2922, 2), (key2919, 2), (key3007, 2), (key3009, 2), (key3007, 2), (key3011, 2), (key3016, 2), (key3011, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key3021, 2), (key3025, 2), (key3022, 2)]

theorem rawRowCheck18580 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form2 = rawRow18580 := by decide +kernel

def row18580 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18580 : row18580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18580 := by decide +kernel

theorem rowEval18580 (x : Key → ℝ) : Integer.Sparse.eval row18580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18580, Integer.Sparse.eval_collectBalanced, rawRowCheck18580]

def rawRow18581 : Integer.Sparse Key := [(key2614, 2), (key2614, 2), (key2608, 2), (key2638, 2), (key2638, 2), (key2630, 2), (key2630, 2), (key2624, 2), (key2624, 2), (key2659, 2), (key2657, 2), (key2657, 2), (key2669, 2), (key2669, 2), (key2663, 2), (key2724, 2), (key2724, 2), (key2704, 2), (key2704, 2), (key2698, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2752, 2), (key2792, 2), (key2792, 2), (key2784, 2), (key2784, 2), (key2778, 2), (key2778, 2), (key2827, 2), (key2827, 2), (key2807, 2), (key2807, 2), (key2801, 2), (key2801, 2), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2), (key2922, 2), (key2922, 2), (key2919, 2), (key2919, 2), (key2918, 2), (key2918, 2), (key3009, 2), (key3007, 2), (key3007, 2), (key3016, 2), (key3011, 2), (key3011, 2), (key3025, 2), (key3025, 2), (key3022, 2), (key3022, 2), (key3021, 2), (key3021, 2)]

theorem rawRowCheck18581 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form2 = rawRow18581 := by decide +kernel

def row18581 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18581 : row18581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18581 := by decide +kernel

theorem rowEval18581 (x : Key → ℝ) : Integer.Sparse.eval row18581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18581, Integer.Sparse.eval_collectBalanced, rawRowCheck18581]

def rawRow18582 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2608, 2), (key2614, 2), (key2624, 2), (key2638, 2), (key2657, 2), (key2659, 2), (key2614, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2752, 2), (key2663, 2), (key2669, 2), (key2698, 2), (key2724, 2), (key2752, 2), (key2757, 2), (key2669, 2), (key2704, 2), (key2724, 2), (key2801, 2), (key2807, 2), (key2851, 2), (key2858, 2), (key2918, 2), (key2919, 2), (key2778, 2), (key2784, 2), (key2851, 2), (key2868, 2), (key2918, 2), (key2922, 2), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key3011, 2), (key3021, 2), (key3022, 2), (key3007, 2), (key3021, 2), (key3025, 2), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3022, 2), (key3025, 2)]

theorem rawRowCheck18582 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form2 = rawRow18582 := by decide +kernel

def row18582 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18582 : row18582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18582 := by decide +kernel

theorem rowEval18582 (x : Key → ℝ) : Integer.Sparse.eval row18582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18582, Integer.Sparse.eval_collectBalanced, rawRowCheck18582]

def rawRow18583 : Integer.Sparse Key := [(key2630, 2), (key2624, 2), (key2638, 2), (key2614, 2), (key2608, 2), (key2638, 2), (key2624, 2), (key2659, 2), (key2657, 2), (key2614, 2), (key2638, 2), (key2630, 2), (key2704, 2), (key2698, 2), (key2752, 2), (key2669, 2), (key2663, 2), (key2724, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2669, 2), (key2724, 2), (key2704, 2), (key2807, 2), (key2801, 2), (key2858, 2), (key2851, 2), (key2919, 2), (key2918, 2), (key2784, 2), (key2778, 2), (key2868, 2), (key2851, 2), (key2922, 2), (key2918, 2), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2), (key2792, 2), (key2784, 2), (key2827, 2), (key2807, 2), (key2868, 2), (key2858, 2), (key3011, 2), (key3022, 2), (key3021, 2), (key3007, 2), (key3025, 2), (key3021, 2), (key3009, 2), (key3007, 2), (key3016, 2), (key3011, 2), (key3025, 2), (key3022, 2)]

theorem rawRowCheck18583 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form2 = rawRow18583 := by decide +kernel

def row18583 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18583 : row18583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18583 := by decide +kernel

theorem rowEval18583 (x : Key → ℝ) : Integer.Sparse.eval row18583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18583, Integer.Sparse.eval_collectBalanced, rawRowCheck18583]

def rawRow18584 : Integer.Sparse Key := [(key2624, 2), (key2638, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2608, 2), (key2659, 2), (key2614, 2), (key2638, 2), (key2630, 2), (key2614, 2), (key2638, 2), (key2698, 2), (key2752, 2), (key2704, 2), (key2698, 2), (key2752, 2), (key2663, 2), (key2757, 2), (key2669, 2), (key2724, 2), (key2704, 2), (key2669, 2), (key2724, 2), (key2851, 2), (key2918, 2), (key2801, 2), (key2919, 2), (key2807, 2), (key2858, 2), (key2851, 2), (key2918, 2), (key2778, 2), (key2922, 2), (key2784, 2), (key2868, 2), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2), (key2807, 2), (key2858, 2), (key2784, 2), (key2868, 2), (key2792, 2), (key2827, 2), (key3021, 2), (key3011, 2), (key3022, 2), (key3021, 2), (key3007, 2), (key3025, 2), (key3011, 2), (key3022, 2), (key3007, 2), (key3025, 2), (key3009, 2), (key3016, 2)]

theorem rawRowCheck18584 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form2 = rawRow18584 := by decide +kernel

def row18584 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18584 : row18584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18584 := by decide +kernel

theorem rowEval18584 (x : Key → ℝ) : Integer.Sparse.eval row18584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18584, Integer.Sparse.eval_collectBalanced, rawRowCheck18584]

def rawRow18585 : Integer.Sparse Key := [(key2638, 2), (key2624, 2), (key2630, 2), (key2638, 2), (key2624, 2), (key2659, 2), (key2608, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2638, 2), (key2614, 2), (key2752, 2), (key2698, 2), (key2704, 2), (key2752, 2), (key2698, 2), (key2757, 2), (key2663, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2724, 2), (key2669, 2), (key2918, 2), (key2851, 2), (key2919, 2), (key2801, 2), (key2858, 2), (key2807, 2), (key2918, 2), (key2851, 2), (key2922, 2), (key2778, 2), (key2868, 2), (key2784, 2), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2), (key2858, 2), (key2807, 2), (key2868, 2), (key2784, 2), (key2827, 2), (key2792, 2), (key3021, 2), (key3022, 2), (key3011, 2), (key3021, 2), (key3025, 2), (key3007, 2), (key3022, 2), (key3011, 2), (key3025, 2), (key3007, 2), (key3016, 2), (key3009, 2)]

theorem rawRowCheck18585 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form2 = rawRow18585 := by decide +kernel

def row18585 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18585 : row18585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18585 := by decide +kernel

theorem rowEval18585 (x : Key → ℝ) : Integer.Sparse.eval row18585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18585, Integer.Sparse.eval_collectBalanced, rawRowCheck18585]

def rawRow18586 : Integer.Sparse Key := [(key2630, 2), (key2638, 2), (key2624, 2), (key2657, 2), (key2659, 2), (key2614, 2), (key2638, 2), (key2608, 2), (key2624, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2704, 2), (key2752, 2), (key2698, 2), (key2724, 2), (key2757, 2), (key2669, 2), (key2752, 2), (key2663, 2), (key2698, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2858, 2), (key2919, 2), (key2807, 2), (key2918, 2), (key2801, 2), (key2851, 2), (key2868, 2), (key2922, 2), (key2784, 2), (key2918, 2), (key2778, 2), (key2851, 2), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2), (key2827, 2), (key2868, 2), (key2792, 2), (key2858, 2), (key2784, 2), (key2807, 2), (key3022, 2), (key3011, 2), (key3021, 2), (key3025, 2), (key3007, 2), (key3021, 2), (key3016, 2), (key3025, 2), (key3009, 2), (key3022, 2), (key3007, 2), (key3011, 2)]

theorem rawRowCheck18586 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form2 = rawRow18586 := by decide +kernel

def row18586 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18586 : row18586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18586 := by decide +kernel

theorem rowEval18586 (x : Key → ℝ) : Integer.Sparse.eval row18586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18586, Integer.Sparse.eval_collectBalanced, rawRowCheck18586]

def rawRow18587 : Integer.Sparse Key := [(key2638, 2), (key2630, 2), (key2624, 2), (key2659, 2), (key2657, 2), (key2638, 2), (key2614, 2), (key2624, 2), (key2608, 2), (key2638, 2), (key2630, 2), (key2614, 2), (key2752, 2), (key2704, 2), (key2698, 2), (key2757, 2), (key2724, 2), (key2752, 2), (key2669, 2), (key2698, 2), (key2663, 2), (key2724, 2), (key2704, 2), (key2669, 2), (key2919, 2), (key2858, 2), (key2918, 2), (key2807, 2), (key2851, 2), (key2801, 2), (key2922, 2), (key2868, 2), (key2918, 2), (key2784, 2), (key2851, 2), (key2778, 2), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2), (key2868, 2), (key2827, 2), (key2858, 2), (key2792, 2), (key2807, 2), (key2784, 2), (key3022, 2), (key3021, 2), (key3011, 2), (key3025, 2), (key3021, 2), (key3007, 2), (key3025, 2), (key3016, 2), (key3022, 2), (key3009, 2), (key3011, 2), (key3007, 2)]

theorem rawRowCheck18587 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form2 = rawRow18587 := by decide +kernel

def row18587 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18587 : row18587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18587 := by decide +kernel

theorem rowEval18587 (x : Key → ℝ) : Integer.Sparse.eval row18587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18587, Integer.Sparse.eval_collectBalanced, rawRowCheck18587]

def rawRow18588 : Integer.Sparse Key := [(key2657, 2), (key2657, 2), (key2659, 2), (key2614, 2), (key2614, 2), (key2630, 2), (key2630, 2), (key2638, 2), (key2638, 2), (key2608, 2), (key2624, 2), (key2624, 2), (key2724, 2), (key2724, 2), (key2757, 2), (key2669, 2), (key2669, 2), (key2704, 2), (key2704, 2), (key2752, 2), (key2752, 2), (key2663, 2), (key2698, 2), (key2698, 2), (key2827, 2), (key2827, 2), (key2868, 2), (key2868, 2), (key2922, 2), (key2922, 2), (key2792, 2), (key2792, 2), (key2858, 2), (key2858, 2), (key2919, 2), (key2919, 2), (key2784, 2), (key2784, 2), (key2807, 2), (key2807, 2), (key2918, 2), (key2918, 2), (key2778, 2), (key2778, 2), (key2801, 2), (key2801, 2), (key2851, 2), (key2851, 2), (key3016, 2), (key3025, 2), (key3025, 2), (key3009, 2), (key3022, 2), (key3022, 2), (key3007, 2), (key3007, 2), (key3011, 2), (key3011, 2), (key3021, 2), (key3021, 2)]

theorem rawRowCheck18588 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form2 = rawRow18588 := by decide +kernel

def row18588 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18588 : row18588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18588 := by decide +kernel

theorem rowEval18588 (x : Key → ℝ) : Integer.Sparse.eval row18588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18588, Integer.Sparse.eval_collectBalanced, rawRowCheck18588]

def rawRow18589 : Integer.Sparse Key := [(key2657, 2), (key2659, 2), (key2657, 2), (key2630, 2), (key2638, 2), (key2614, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2624, 2), (key2608, 2), (key2624, 2), (key2724, 2), (key2757, 2), (key2724, 2), (key2704, 2), (key2752, 2), (key2669, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2663, 2), (key2698, 2), (key2868, 2), (key2922, 2), (key2827, 2), (key2922, 2), (key2827, 2), (key2868, 2), (key2858, 2), (key2919, 2), (key2792, 2), (key2919, 2), (key2792, 2), (key2858, 2), (key2807, 2), (key2918, 2), (key2784, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2801, 2), (key2851, 2), (key2778, 2), (key2851, 2), (key2778, 2), (key2801, 2), (key3025, 2), (key3016, 2), (key3025, 2), (key3022, 2), (key3009, 2), (key3022, 2), (key3011, 2), (key3021, 2), (key3007, 2), (key3021, 2), (key3007, 2), (key3011, 2)]

theorem rawRowCheck18589 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form2 = rawRow18589 := by decide +kernel

def row18589 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18589 : row18589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18589 := by decide +kernel

theorem rowEval18589 (x : Key → ℝ) : Integer.Sparse.eval row18589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18589, Integer.Sparse.eval_collectBalanced, rawRowCheck18589]

def rawRow18590 : Integer.Sparse Key := [(key2659, 2), (key2657, 2), (key2657, 2), (key2638, 2), (key2630, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2614, 2), (key2624, 2), (key2624, 2), (key2608, 2), (key2757, 2), (key2724, 2), (key2724, 2), (key2752, 2), (key2704, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2669, 2), (key2698, 2), (key2698, 2), (key2663, 2), (key2922, 2), (key2868, 2), (key2922, 2), (key2827, 2), (key2868, 2), (key2827, 2), (key2919, 2), (key2858, 2), (key2919, 2), (key2792, 2), (key2858, 2), (key2792, 2), (key2918, 2), (key2807, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2784, 2), (key2851, 2), (key2801, 2), (key2851, 2), (key2778, 2), (key2801, 2), (key2778, 2), (key3025, 2), (key3025, 2), (key3016, 2), (key3022, 2), (key3022, 2), (key3009, 2), (key3021, 2), (key3011, 2), (key3021, 2), (key3007, 2), (key3011, 2), (key3007, 2)]

theorem rawRowCheck18590 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form2 = rawRow18590 := by decide +kernel

def row18590 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18590 : row18590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18590 := by decide +kernel

theorem rowEval18590 (x : Key → ℝ) : Integer.Sparse.eval row18590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18590, Integer.Sparse.eval_collectBalanced, rawRowCheck18590]

def rawRow18591 : Integer.Sparse Key := [(key2663, 2), (key2669, 2), (key2669, 2), (key2698, 2), (key2704, 2), (key2698, 2), (key2752, 2), (key2704, 2), (key2752, 2), (key2724, 2), (key2724, 2), (key2757, 2), (key2608, 2), (key2614, 2), (key2614, 2), (key2801, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key2827, 2), (key3011, 2), (key3011, 2), (key3016, 2), (key2624, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2724, 2), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2), (key3021, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key3022, 2), (key3025, 2), (key2657, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2752, 2), (key2757, 2), (key2918, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2919, 2), (key2922, 2)]

theorem rawRowCheck18591 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form2 = rawRow18591 := by decide +kernel

def row18591 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18591 : row18591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18591 := by decide +kernel

theorem rowEval18591 (x : Key → ℝ) : Integer.Sparse.eval row18591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18591, Integer.Sparse.eval_collectBalanced, rawRowCheck18591]

def rawRow18592 : Integer.Sparse Key := [(key2669, 2), (key2663, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2752, 2), (key2698, 2), (key2752, 2), (key2704, 2), (key2724, 2), (key2757, 2), (key2724, 2), (key2614, 2), (key2608, 2), (key2614, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key3011, 2), (key3016, 2), (key3011, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2624, 2), (key2638, 2), (key2630, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key3021, 2), (key3025, 2), (key3022, 2), (key2657, 2), (key2659, 2), (key2657, 2), (key2752, 2), (key2757, 2), (key2752, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2918, 2), (key2922, 2), (key2919, 2)]

theorem rawRowCheck18592 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form2 = rawRow18592 := by decide +kernel

def row18592 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18592 : row18592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18592 := by decide +kernel

theorem rowEval18592 (x : Key → ℝ) : Integer.Sparse.eval row18592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18592, Integer.Sparse.eval_collectBalanced, rawRowCheck18592]

def rawRow18593 : Integer.Sparse Key := [(key2669, 2), (key2669, 2), (key2663, 2), (key2752, 2), (key2752, 2), (key2704, 2), (key2704, 2), (key2698, 2), (key2698, 2), (key2757, 2), (key2724, 2), (key2724, 2), (key2614, 2), (key2614, 2), (key2608, 2), (key2827, 2), (key2827, 2), (key2807, 2), (key2807, 2), (key2801, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key3011, 2), (key2638, 2), (key2638, 2), (key2630, 2), (key2630, 2), (key2624, 2), (key2624, 2), (key2724, 2), (key2724, 2), (key2704, 2), (key2704, 2), (key2698, 2), (key2698, 2), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2), (key3025, 2), (key3025, 2), (key3022, 2), (key3022, 2), (key3021, 2), (key3021, 2), (key2659, 2), (key2657, 2), (key2657, 2), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, 2), (key2922, 2), (key2919, 2), (key2919, 2), (key2918, 2), (key2918, 2)]

theorem rawRowCheck18593 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form2 = rawRow18593 := by decide +kernel

def row18593 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18593 : row18593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18593 := by decide +kernel

theorem rowEval18593 (x : Key → ℝ) : Integer.Sparse.eval row18593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18593, Integer.Sparse.eval_collectBalanced, rawRowCheck18593]

def rawRow18594 : Integer.Sparse Key := [(key2698, 2), (key2704, 2), (key2724, 2), (key2663, 2), (key2669, 2), (key2698, 2), (key2752, 2), (key2724, 2), (key2757, 2), (key2669, 2), (key2704, 2), (key2752, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2608, 2), (key2614, 2), (key2801, 2), (key2827, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2807, 2), (key2827, 2), (key2698, 2), (key2704, 2), (key2851, 2), (key2858, 2), (key3021, 2), (key3022, 2), (key2624, 2), (key2630, 2), (key2851, 2), (key2868, 2), (key3021, 2), (key3025, 2), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2), (key2630, 2), (key2638, 2), (key2704, 2), (key2724, 2), (key2858, 2), (key2868, 2), (key2752, 2), (key2918, 2), (key2919, 2), (key2657, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2757, 2), (key2919, 2), (key2922, 2)]

theorem rawRowCheck18594 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form2 = rawRow18594 := by decide +kernel

def row18594 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18594 : row18594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18594 := by decide +kernel

theorem rowEval18594 (x : Key → ℝ) : Integer.Sparse.eval row18594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18594, Integer.Sparse.eval_collectBalanced, rawRowCheck18594]

def rawRow18595 : Integer.Sparse Key := [(key2704, 2), (key2698, 2), (key2724, 2), (key2669, 2), (key2663, 2), (key2752, 2), (key2698, 2), (key2757, 2), (key2724, 2), (key2669, 2), (key2752, 2), (key2704, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2614, 2), (key2608, 2), (key2827, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key2614, 2), (key2827, 2), (key2807, 2), (key2704, 2), (key2698, 2), (key2858, 2), (key2851, 2), (key3022, 2), (key3021, 2), (key2630, 2), (key2624, 2), (key2868, 2), (key2851, 2), (key3025, 2), (key3021, 2), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2), (key2638, 2), (key2630, 2), (key2724, 2), (key2704, 2), (key2868, 2), (key2858, 2), (key2752, 2), (key2919, 2), (key2918, 2), (key2657, 2), (key2922, 2), (key2918, 2), (key2659, 2), (key2657, 2), (key2757, 2), (key2752, 2), (key2922, 2), (key2919, 2)]

theorem rawRowCheck18595 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form2 = rawRow18595 := by decide +kernel

def row18595 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18595 : row18595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18595 := by decide +kernel

theorem rowEval18595 (x : Key → ℝ) : Integer.Sparse.eval row18595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18595, Integer.Sparse.eval_collectBalanced, rawRowCheck18595]

def rawRow18596 : Integer.Sparse Key := [(key2698, 2), (key2724, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2663, 2), (key2757, 2), (key2669, 2), (key2752, 2), (key2704, 2), (key2669, 2), (key2752, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2608, 2), (key3016, 2), (key2614, 2), (key2827, 2), (key2807, 2), (key2614, 2), (key2827, 2), (key2851, 2), (key3021, 2), (key2698, 2), (key3022, 2), (key2704, 2), (key2858, 2), (key2851, 2), (key3021, 2), (key2624, 2), (key3025, 2), (key2630, 2), (key2868, 2), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2704, 2), (key2858, 2), (key2630, 2), (key2868, 2), (key2638, 2), (key2724, 2), (key2918, 2), (key2752, 2), (key2919, 2), (key2918, 2), (key2657, 2), (key2922, 2), (key2752, 2), (key2919, 2), (key2657, 2), (key2922, 2), (key2659, 2), (key2757, 2)]

theorem rawRowCheck18596 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form2 = rawRow18596 := by decide +kernel

def row18596 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18596 : row18596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18596 := by decide +kernel

theorem rowEval18596 (x : Key → ℝ) : Integer.Sparse.eval row18596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18596, Integer.Sparse.eval_collectBalanced, rawRowCheck18596]

def rawRow18597 : Integer.Sparse Key := [(key2724, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2698, 2), (key2757, 2), (key2663, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2752, 2), (key2669, 2), (key2827, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2801, 2), (key3016, 2), (key2608, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key3021, 2), (key2851, 2), (key3022, 2), (key2698, 2), (key2858, 2), (key2704, 2), (key3021, 2), (key2851, 2), (key3025, 2), (key2624, 2), (key2868, 2), (key2630, 2), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2), (key2858, 2), (key2704, 2), (key2868, 2), (key2630, 2), (key2724, 2), (key2638, 2), (key2918, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2919, 2), (key2752, 2), (key2922, 2), (key2657, 2), (key2757, 2), (key2659, 2)]

theorem rawRowCheck18597 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form2 = rawRow18597 := by decide +kernel

def row18597 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18597 : row18597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18597 := by decide +kernel

theorem rowEval18597 (x : Key → ℝ) : Integer.Sparse.eval row18597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18597, Integer.Sparse.eval_collectBalanced, rawRowCheck18597]

def rawRow18598 : Integer.Sparse Key := [(key2704, 2), (key2724, 2), (key2698, 2), (key2752, 2), (key2757, 2), (key2669, 2), (key2724, 2), (key2663, 2), (key2698, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2807, 2), (key2827, 2), (key2801, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2827, 2), (key2608, 2), (key2801, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2858, 2), (key3022, 2), (key2704, 2), (key3021, 2), (key2698, 2), (key2851, 2), (key2868, 2), (key3025, 2), (key2630, 2), (key3021, 2), (key2624, 2), (key2851, 2), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2), (key2724, 2), (key2868, 2), (key2638, 2), (key2858, 2), (key2630, 2), (key2704, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2918, 2), (key2757, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2657, 2), (key2752, 2)]

theorem rawRowCheck18598 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form2 = rawRow18598 := by decide +kernel

def row18598 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18598 : row18598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18598 := by decide +kernel

theorem rowEval18598 (x : Key → ℝ) : Integer.Sparse.eval row18598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18598, Integer.Sparse.eval_collectBalanced, rawRowCheck18598]

def rawRow18599 : Integer.Sparse Key := [(key2724, 2), (key2704, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2724, 2), (key2669, 2), (key2698, 2), (key2663, 2), (key2752, 2), (key2704, 2), (key2669, 2), (key2827, 2), (key2807, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key2827, 2), (key2614, 2), (key2801, 2), (key2608, 2), (key2827, 2), (key2807, 2), (key2614, 2), (key3022, 2), (key2858, 2), (key3021, 2), (key2704, 2), (key2851, 2), (key2698, 2), (key3025, 2), (key2868, 2), (key3021, 2), (key2630, 2), (key2851, 2), (key2624, 2), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key2868, 2), (key2724, 2), (key2858, 2), (key2638, 2), (key2704, 2), (key2630, 2), (key2919, 2), (key2918, 2), (key2752, 2), (key2922, 2), (key2918, 2), (key2657, 2), (key2922, 2), (key2757, 2), (key2919, 2), (key2659, 2), (key2752, 2), (key2657, 2)]

theorem rawRowCheck18599 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form2 = rawRow18599 := by decide +kernel

def row18599 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18599 : row18599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18599 := by decide +kernel

theorem rowEval18599 (x : Key → ℝ) : Integer.Sparse.eval row18599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18599, Integer.Sparse.eval_collectBalanced, rawRowCheck18599]

def rawRow18600 : Integer.Sparse Key := [(key2752, 2), (key2752, 2), (key2757, 2), (key2669, 2), (key2669, 2), (key2704, 2), (key2704, 2), (key2724, 2), (key2724, 2), (key2663, 2), (key2698, 2), (key2698, 2), (key3011, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2614, 2), (key2807, 2), (key2807, 2), (key2827, 2), (key2827, 2), (key2608, 2), (key2801, 2), (key2801, 2), (key2724, 2), (key2724, 2), (key2868, 2), (key2868, 2), (key3025, 2), (key3025, 2), (key2638, 2), (key2638, 2), (key2858, 2), (key2858, 2), (key3022, 2), (key3022, 2), (key2630, 2), (key2630, 2), (key2704, 2), (key2704, 2), (key3021, 2), (key3021, 2), (key2624, 2), (key2624, 2), (key2698, 2), (key2698, 2), (key2851, 2), (key2851, 2), (key2757, 2), (key2922, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2919, 2), (key2657, 2), (key2657, 2), (key2752, 2), (key2752, 2), (key2918, 2), (key2918, 2)]

theorem rawRowCheck18600 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form2 = rawRow18600 := by decide +kernel

def row18600 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18600 : row18600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18600 := by decide +kernel

theorem rowEval18600 (x : Key → ℝ) : Integer.Sparse.eval row18600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18600, Integer.Sparse.eval_collectBalanced, rawRowCheck18600]

def rawRow18601 : Integer.Sparse Key := [(key2752, 2), (key2757, 2), (key2752, 2), (key2704, 2), (key2724, 2), (key2669, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2663, 2), (key2698, 2), (key3011, 2), (key3016, 2), (key3011, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2801, 2), (key2608, 2), (key2801, 2), (key2868, 2), (key3025, 2), (key2724, 2), (key3025, 2), (key2724, 2), (key2868, 2), (key2858, 2), (key3022, 2), (key2638, 2), (key3022, 2), (key2638, 2), (key2858, 2), (key2704, 2), (key3021, 2), (key2630, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2698, 2), (key2851, 2), (key2624, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key2922, 2), (key2757, 2), (key2922, 2), (key2919, 2), (key2659, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2657, 2), (key2918, 2), (key2657, 2), (key2752, 2)]

theorem rawRowCheck18601 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form2 = rawRow18601 := by decide +kernel

def row18601 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18601 : row18601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18601 := by decide +kernel

theorem rowEval18601 (x : Key → ℝ) : Integer.Sparse.eval row18601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18601, Integer.Sparse.eval_collectBalanced, rawRowCheck18601]

def rawRow18602 : Integer.Sparse Key := [(key2757, 2), (key2752, 2), (key2752, 2), (key2724, 2), (key2704, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2669, 2), (key2698, 2), (key2698, 2), (key2663, 2), (key3016, 2), (key3011, 2), (key3011, 2), (key2827, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2614, 2), (key2801, 2), (key2801, 2), (key2608, 2), (key3025, 2), (key2868, 2), (key3025, 2), (key2724, 2), (key2868, 2), (key2724, 2), (key3022, 2), (key2858, 2), (key3022, 2), (key2638, 2), (key2858, 2), (key2638, 2), (key3021, 2), (key2704, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2630, 2), (key2851, 2), (key2698, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key2624, 2), (key2922, 2), (key2922, 2), (key2757, 2), (key2919, 2), (key2919, 2), (key2659, 2), (key2918, 2), (key2752, 2), (key2918, 2), (key2657, 2), (key2752, 2), (key2657, 2)]

theorem rawRowCheck18602 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form2 = rawRow18602 := by decide +kernel

def row18602 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18602 : row18602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18602 := by decide +kernel

theorem rowEval18602 (x : Key → ℝ) : Integer.Sparse.eval row18602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18602, Integer.Sparse.eval_collectBalanced, rawRowCheck18602]

def rawRow18603 : Integer.Sparse Key := [(key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2851, 2), (key2918, 2), (key2858, 2), (key2919, 2), (key2827, 2), (key2868, 2), (key2922, 2), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2851, 2), (key3021, 2), (key2858, 2), (key3022, 2), (key2724, 2), (key2868, 2), (key3025, 2), (key2608, 2), (key2614, 2), (key2624, 2), (key2638, 2), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 2), (key2698, 2), (key2724, 2), (key2752, 2), (key2757, 2), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3022, 2), (key3025, 2), (key2614, 2), (key2630, 2), (key2638, 2), (key2669, 2), (key2704, 2), (key2724, 2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2)]

theorem rawRowCheck18603 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form2 = rawRow18603 := by decide +kernel

def row18603 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18603 : row18603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18603 := by decide +kernel

theorem rowEval18603 (x : Key → ℝ) : Integer.Sparse.eval row18603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18603, Integer.Sparse.eval_collectBalanced, rawRowCheck18603]

def rawRow18604 : Integer.Sparse Key := [(key2784, 2), (key2778, 2), (key2792, 2), (key2807, 2), (key2801, 2), (key2918, 2), (key2851, 2), (key2919, 2), (key2858, 2), (key2827, 2), (key2922, 2), (key2868, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2704, 2), (key2698, 2), (key3021, 2), (key2851, 2), (key3022, 2), (key2858, 2), (key2724, 2), (key3025, 2), (key2868, 2), (key2614, 2), (key2608, 2), (key2638, 2), (key2624, 2), (key2659, 2), (key2657, 2), (key2669, 2), (key2663, 2), (key2724, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2), (key3009, 2), (key3007, 2), (key3016, 2), (key3011, 2), (key3025, 2), (key3022, 2), (key2614, 2), (key2638, 2), (key2630, 2), (key2669, 2), (key2724, 2), (key2704, 2), (key2792, 2), (key2784, 2), (key2827, 2), (key2807, 2), (key2868, 2), (key2858, 2)]

theorem rawRowCheck18604 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form2 = rawRow18604 := by decide +kernel

def row18604 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18604 : row18604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18604 := by decide +kernel

theorem rowEval18604 (x : Key → ℝ) : Integer.Sparse.eval row18604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18604, Integer.Sparse.eval_collectBalanced, rawRowCheck18604]

def rawRow18605 : Integer.Sparse Key := [(key2778, 2), (key2792, 2), (key2784, 2), (key2851, 2), (key2858, 2), (key2801, 2), (key2919, 2), (key2807, 2), (key2918, 2), (key2868, 2), (key2827, 2), (key2922, 2), (key2624, 2), (key2638, 2), (key2630, 2), (key2851, 2), (key2858, 2), (key2698, 2), (key3022, 2), (key2704, 2), (key3021, 2), (key2868, 2), (key2724, 2), (key3025, 2), (key2624, 2), (key2638, 2), (key2608, 2), (key2659, 2), (key2614, 2), (key2638, 2), (key2698, 2), (key2752, 2), (key2663, 2), (key2757, 2), (key2669, 2), (key2724, 2), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2), (key3011, 2), (key3022, 2), (key3007, 2), (key3025, 2), (key3009, 2), (key3016, 2), (key2630, 2), (key2614, 2), (key2638, 2), (key2704, 2), (key2669, 2), (key2724, 2), (key2807, 2), (key2858, 2), (key2784, 2), (key2868, 2), (key2792, 2), (key2827, 2)]

theorem rawRowCheck18605 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form2 = rawRow18605 := by decide +kernel

def row18605 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18605 : row18605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18605 := by decide +kernel

theorem rowEval18605 (x : Key → ℝ) : Integer.Sparse.eval row18605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18605, Integer.Sparse.eval_collectBalanced, rawRowCheck18605]

def rawRow18606 : Integer.Sparse Key := [(key2792, 2), (key2778, 2), (key2784, 2), (key2858, 2), (key2851, 2), (key2919, 2), (key2801, 2), (key2918, 2), (key2807, 2), (key2868, 2), (key2922, 2), (key2827, 2), (key2638, 2), (key2624, 2), (key2630, 2), (key2858, 2), (key2851, 2), (key3022, 2), (key2698, 2), (key3021, 2), (key2704, 2), (key2868, 2), (key3025, 2), (key2724, 2), (key2638, 2), (key2624, 2), (key2659, 2), (key2608, 2), (key2638, 2), (key2614, 2), (key2752, 2), (key2698, 2), (key2757, 2), (key2663, 2), (key2724, 2), (key2669, 2), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2), (key3022, 2), (key3011, 2), (key3025, 2), (key3007, 2), (key3016, 2), (key3009, 2), (key2630, 2), (key2638, 2), (key2614, 2), (key2704, 2), (key2724, 2), (key2669, 2), (key2858, 2), (key2807, 2), (key2868, 2), (key2784, 2), (key2827, 2), (key2792, 2)]

theorem rawRowCheck18606 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form2 = rawRow18606 := by decide +kernel

def row18606 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18606 : row18606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18606 := by decide +kernel

theorem rowEval18606 (x : Key → ℝ) : Integer.Sparse.eval row18606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18606, Integer.Sparse.eval_collectBalanced, rawRowCheck18606]

def rawRow18607 : Integer.Sparse Key := [(key2784, 2), (key2792, 2), (key2778, 2), (key2918, 2), (key2919, 2), (key2807, 2), (key2858, 2), (key2801, 2), (key2851, 2), (key2922, 2), (key2827, 2), (key2868, 2), (key2630, 2), (key2638, 2), (key2624, 2), (key3021, 2), (key3022, 2), (key2704, 2), (key2858, 2), (key2698, 2), (key2851, 2), (key3025, 2), (key2724, 2), (key2868, 2), (key2657, 2), (key2659, 2), (key2614, 2), (key2638, 2), (key2608, 2), (key2624, 2), (key2724, 2), (key2757, 2), (key2669, 2), (key2752, 2), (key2663, 2), (key2698, 2), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2), (key3016, 2), (key3025, 2), (key3009, 2), (key3022, 2), (key3007, 2), (key3011, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2827, 2), (key2868, 2), (key2792, 2), (key2858, 2), (key2784, 2), (key2807, 2)]

theorem rawRowCheck18607 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form2 = rawRow18607 := by decide +kernel

def row18607 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18607 : row18607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18607 := by decide +kernel

theorem rowEval18607 (x : Key → ℝ) : Integer.Sparse.eval row18607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18607, Integer.Sparse.eval_collectBalanced, rawRowCheck18607]

def rawRow18608 : Integer.Sparse Key := [(key2792, 2), (key2784, 2), (key2778, 2), (key2919, 2), (key2918, 2), (key2858, 2), (key2807, 2), (key2851, 2), (key2801, 2), (key2922, 2), (key2868, 2), (key2827, 2), (key2638, 2), (key2630, 2), (key2624, 2), (key3022, 2), (key3021, 2), (key2858, 2), (key2704, 2), (key2851, 2), (key2698, 2), (key3025, 2), (key2868, 2), (key2724, 2), (key2659, 2), (key2657, 2), (key2638, 2), (key2614, 2), (key2624, 2), (key2608, 2), (key2757, 2), (key2724, 2), (key2752, 2), (key2669, 2), (key2698, 2), (key2663, 2), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2), (key3025, 2), (key3016, 2), (key3022, 2), (key3009, 2), (key3011, 2), (key3007, 2), (key2638, 2), (key2630, 2), (key2614, 2), (key2724, 2), (key2704, 2), (key2669, 2), (key2868, 2), (key2827, 2), (key2858, 2), (key2792, 2), (key2807, 2), (key2784, 2)]

theorem rawRowCheck18608 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form2 = rawRow18608 := by decide +kernel

def row18608 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18608 : row18608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18608 := by decide +kernel

theorem rowEval18608 (x : Key → ℝ) : Integer.Sparse.eval row18608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18608, Integer.Sparse.eval_collectBalanced, rawRowCheck18608]

def rawRow18609 : Integer.Sparse Key := [(key2801, 2), (key2807, 2), (key2827, 2), (key2778, 2), (key2784, 2), (key2851, 2), (key2918, 2), (key2868, 2), (key2922, 2), (key2792, 2), (key2858, 2), (key2919, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2624, 2), (key2630, 2), (key2851, 2), (key3021, 2), (key2868, 2), (key3025, 2), (key2638, 2), (key2858, 2), (key3022, 2), (key2663, 2), (key2669, 2), (key2698, 2), (key2752, 2), (key2724, 2), (key2757, 2), (key2608, 2), (key2614, 2), (key2801, 2), (key2827, 2), (key3011, 2), (key3016, 2), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2757, 2), (key2919, 2), (key2922, 2), (key2669, 2), (key2784, 2), (key2792, 2), (key2614, 2), (key2807, 2), (key2827, 2), (key2630, 2), (key2638, 2), (key2704, 2), (key2724, 2), (key2858, 2), (key2868, 2)]

theorem rawRowCheck18609 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form2 = rawRow18609 := by decide +kernel

def row18609 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18609 : row18609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18609 := by decide +kernel

theorem rowEval18609 (x : Key → ℝ) : Integer.Sparse.eval row18609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18609, Integer.Sparse.eval_collectBalanced, rawRowCheck18609]

def rawRow18610 : Integer.Sparse Key := [(key2807, 2), (key2801, 2), (key2827, 2), (key2784, 2), (key2778, 2), (key2918, 2), (key2851, 2), (key2922, 2), (key2868, 2), (key2792, 2), (key2919, 2), (key2858, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2630, 2), (key2624, 2), (key3021, 2), (key2851, 2), (key3025, 2), (key2868, 2), (key2638, 2), (key3022, 2), (key2858, 2), (key2669, 2), (key2663, 2), (key2752, 2), (key2698, 2), (key2757, 2), (key2724, 2), (key2614, 2), (key2608, 2), (key2827, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2), (key2659, 2), (key2657, 2), (key2757, 2), (key2752, 2), (key2922, 2), (key2919, 2), (key2669, 2), (key2792, 2), (key2784, 2), (key2614, 2), (key2827, 2), (key2807, 2), (key2638, 2), (key2630, 2), (key2724, 2), (key2704, 2), (key2868, 2), (key2858, 2)]

theorem rawRowCheck18610 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form2 = rawRow18610 := by decide +kernel

def row18610 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18610 : row18610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18610 := by decide +kernel

theorem rowEval18610 (x : Key → ℝ) : Integer.Sparse.eval row18610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18610, Integer.Sparse.eval_collectBalanced, rawRowCheck18610]

def rawRow18611 : Integer.Sparse Key := [(key2801, 2), (key2827, 2), (key2807, 2), (key2851, 2), (key2868, 2), (key2778, 2), (key2922, 2), (key2784, 2), (key2918, 2), (key2858, 2), (key2792, 2), (key2919, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2851, 2), (key2868, 2), (key2624, 2), (key3025, 2), (key2630, 2), (key3021, 2), (key2858, 2), (key2638, 2), (key3022, 2), (key2698, 2), (key2724, 2), (key2663, 2), (key2757, 2), (key2669, 2), (key2752, 2), (key2801, 2), (key2827, 2), (key2608, 2), (key3016, 2), (key2614, 2), (key2827, 2), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2752, 2), (key2919, 2), (key2657, 2), (key2922, 2), (key2659, 2), (key2757, 2), (key2784, 2), (key2669, 2), (key2792, 2), (key2807, 2), (key2614, 2), (key2827, 2), (key2704, 2), (key2858, 2), (key2630, 2), (key2868, 2), (key2638, 2), (key2724, 2)]

theorem rawRowCheck18611 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form2 = rawRow18611 := by decide +kernel

def row18611 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18611 : row18611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18611 := by decide +kernel

theorem rowEval18611 (x : Key → ℝ) : Integer.Sparse.eval row18611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18611, Integer.Sparse.eval_collectBalanced, rawRowCheck18611]

def rawRow18612 : Integer.Sparse Key := [(key2827, 2), (key2801, 2), (key2807, 2), (key2868, 2), (key2851, 2), (key2922, 2), (key2778, 2), (key2918, 2), (key2784, 2), (key2858, 2), (key2919, 2), (key2792, 2), (key2724, 2), (key2698, 2), (key2704, 2), (key2868, 2), (key2851, 2), (key3025, 2), (key2624, 2), (key3021, 2), (key2630, 2), (key2858, 2), (key3022, 2), (key2638, 2), (key2724, 2), (key2698, 2), (key2757, 2), (key2663, 2), (key2752, 2), (key2669, 2), (key2827, 2), (key2801, 2), (key3016, 2), (key2608, 2), (key2827, 2), (key2614, 2), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2), (key2919, 2), (key2752, 2), (key2922, 2), (key2657, 2), (key2757, 2), (key2659, 2), (key2784, 2), (key2792, 2), (key2669, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2858, 2), (key2704, 2), (key2868, 2), (key2630, 2), (key2724, 2), (key2638, 2)]

theorem rawRowCheck18612 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form2 = rawRow18612 := by decide +kernel

def row18612 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18612 : row18612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18612 := by decide +kernel

theorem rowEval18612 (x : Key → ℝ) : Integer.Sparse.eval row18612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18612, Integer.Sparse.eval_collectBalanced, rawRowCheck18612]

def rawRow18613 : Integer.Sparse Key := [(key2807, 2), (key2827, 2), (key2801, 2), (key2918, 2), (key2922, 2), (key2784, 2), (key2868, 2), (key2778, 2), (key2851, 2), (key2919, 2), (key2792, 2), (key2858, 2), (key2704, 2), (key2724, 2), (key2698, 2), (key3021, 2), (key3025, 2), (key2630, 2), (key2868, 2), (key2624, 2), (key2851, 2), (key3022, 2), (key2638, 2), (key2858, 2), (key2752, 2), (key2757, 2), (key2669, 2), (key2724, 2), (key2663, 2), (key2698, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2827, 2), (key2608, 2), (key2801, 2), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2), (key2757, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2657, 2), (key2752, 2), (key2792, 2), (key2669, 2), (key2784, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2724, 2), (key2868, 2), (key2638, 2), (key2858, 2), (key2630, 2), (key2704, 2)]

theorem rawRowCheck18613 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form2 = rawRow18613 := by decide +kernel

def row18613 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18613 : row18613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18613 := by decide +kernel

theorem rowEval18613 (x : Key → ℝ) : Integer.Sparse.eval row18613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18613, Integer.Sparse.eval_collectBalanced, rawRowCheck18613]

def rawRow18614 : Integer.Sparse Key := [(key2827, 2), (key2807, 2), (key2801, 2), (key2922, 2), (key2918, 2), (key2868, 2), (key2784, 2), (key2851, 2), (key2778, 2), (key2919, 2), (key2858, 2), (key2792, 2), (key2724, 2), (key2704, 2), (key2698, 2), (key3025, 2), (key3021, 2), (key2868, 2), (key2630, 2), (key2851, 2), (key2624, 2), (key3022, 2), (key2858, 2), (key2638, 2), (key2757, 2), (key2752, 2), (key2724, 2), (key2669, 2), (key2698, 2), (key2663, 2), (key3016, 2), (key3011, 2), (key2827, 2), (key2614, 2), (key2801, 2), (key2608, 2), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key2922, 2), (key2757, 2), (key2919, 2), (key2659, 2), (key2752, 2), (key2657, 2), (key2792, 2), (key2784, 2), (key2669, 2), (key2827, 2), (key2807, 2), (key2614, 2), (key2868, 2), (key2724, 2), (key2858, 2), (key2638, 2), (key2704, 2), (key2630, 2)]

theorem rawRowCheck18614 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form2 = rawRow18614 := by decide +kernel

def row18614 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18614 : row18614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18614 := by decide +kernel

theorem rowEval18614 (x : Key → ℝ) : Integer.Sparse.eval row18614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18614, Integer.Sparse.eval_collectBalanced, rawRowCheck18614]

def rawRow18615 : Integer.Sparse Key := [(key2851, 2), (key2858, 2), (key2868, 2), (key2778, 2), (key2792, 2), (key2801, 2), (key2919, 2), (key2827, 2), (key2922, 2), (key2784, 2), (key2807, 2), (key2918, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2624, 2), (key2638, 2), (key2698, 2), (key3022, 2), (key2724, 2), (key3025, 2), (key2630, 2), (key2704, 2), (key3021, 2), (key2778, 2), (key2792, 2), (key2801, 2), (key2919, 2), (key2827, 2), (key2922, 2), (key2624, 2), (key2638, 2), (key2698, 2), (key3022, 2), (key2724, 2), (key3025, 2), (key2608, 2), (key2659, 2), (key2663, 2), (key2757, 2), (key3009, 2), (key3016, 2), (key2614, 2), (key2638, 2), (key2669, 2), (key2724, 2), (key2792, 2), (key2827, 2), (key2704, 2), (key2807, 2), (key2858, 2), (key2630, 2), (key2784, 2), (key2868, 2), (key2614, 2), (key2638, 2), (key2669, 2), (key2724, 2), (key2792, 2), (key2827, 2)]

theorem rawRowCheck18615 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form2 = rawRow18615 := by decide +kernel

def row18615 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18615 : row18615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18615 := by decide +kernel

theorem rowEval18615 (x : Key → ℝ) : Integer.Sparse.eval row18615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18615, Integer.Sparse.eval_collectBalanced, rawRowCheck18615]

def rawRow18616 : Integer.Sparse Key := [(key2858, 2), (key2851, 2), (key2868, 2), (key2792, 2), (key2778, 2), (key2919, 2), (key2801, 2), (key2922, 2), (key2827, 2), (key2784, 2), (key2918, 2), (key2807, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2638, 2), (key2624, 2), (key3022, 2), (key2698, 2), (key3025, 2), (key2724, 2), (key2630, 2), (key3021, 2), (key2704, 2), (key2792, 2), (key2778, 2), (key2919, 2), (key2801, 2), (key2922, 2), (key2827, 2), (key2638, 2), (key2624, 2), (key3022, 2), (key2698, 2), (key3025, 2), (key2724, 2), (key2659, 2), (key2608, 2), (key2757, 2), (key2663, 2), (key3016, 2), (key3009, 2), (key2638, 2), (key2614, 2), (key2724, 2), (key2669, 2), (key2827, 2), (key2792, 2), (key2704, 2), (key2858, 2), (key2807, 2), (key2630, 2), (key2868, 2), (key2784, 2), (key2638, 2), (key2614, 2), (key2724, 2), (key2669, 2), (key2827, 2), (key2792, 2)]

theorem rawRowCheck18616 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form2 = rawRow18616 := by decide +kernel

def row18616 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18616 : row18616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18616 := by decide +kernel

theorem rowEval18616 (x : Key → ℝ) : Integer.Sparse.eval row18616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18616, Integer.Sparse.eval_collectBalanced, rawRowCheck18616]

def rawRow18617 : Integer.Sparse Key := [(key2851, 2), (key2868, 2), (key2858, 2), (key2801, 2), (key2827, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2807, 2), (key2784, 2), (key2918, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2698, 2), (key2724, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2704, 2), (key2630, 2), (key3021, 2), (key2801, 2), (key2827, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2698, 2), (key2724, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2663, 2), (key2757, 2), (key2608, 2), (key3016, 2), (key2659, 2), (key2757, 2), (key2669, 2), (key2792, 2), (key2614, 2), (key2827, 2), (key2638, 2), (key2724, 2), (key2807, 2), (key2704, 2), (key2858, 2), (key2784, 2), (key2630, 2), (key2868, 2), (key2669, 2), (key2792, 2), (key2614, 2), (key2827, 2), (key2638, 2), (key2724, 2)]

theorem rawRowCheck18617 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form2 = rawRow18617 := by decide +kernel

def row18617 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 4), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18617 : row18617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18617 := by decide +kernel

theorem rowEval18617 (x : Key → ℝ) : Integer.Sparse.eval row18617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18617, Integer.Sparse.eval_collectBalanced, rawRowCheck18617]

def rawRow18618 : Integer.Sparse Key := [(key2868, 2), (key2851, 2), (key2858, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2919, 2), (key2792, 2), (key2807, 2), (key2918, 2), (key2784, 2), (key2868, 2), (key2851, 2), (key2858, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key3022, 2), (key2638, 2), (key2704, 2), (key3021, 2), (key2630, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2919, 2), (key2792, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key3022, 2), (key2638, 2), (key2757, 2), (key2663, 2), (key3016, 2), (key2608, 2), (key2757, 2), (key2659, 2), (key2792, 2), (key2669, 2), (key2827, 2), (key2614, 2), (key2724, 2), (key2638, 2), (key2807, 2), (key2858, 2), (key2704, 2), (key2784, 2), (key2868, 2), (key2630, 2), (key2792, 2), (key2669, 2), (key2827, 2), (key2614, 2), (key2724, 2), (key2638, 2)]

theorem rawRowCheck18618 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form2 = rawRow18618 := by decide +kernel

def row18618 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 4), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18618 : row18618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18618 := by decide +kernel

theorem rowEval18618 (x : Key → ℝ) : Integer.Sparse.eval row18618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18618, Integer.Sparse.eval_collectBalanced, rawRowCheck18618]

def rawRow18619 : Integer.Sparse Key := [(key2858, 2), (key2868, 2), (key2851, 2), (key2919, 2), (key2922, 2), (key2792, 2), (key2827, 2), (key2778, 2), (key2801, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2858, 2), (key2868, 2), (key2851, 2), (key3022, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2624, 2), (key2698, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2919, 2), (key2922, 2), (key2792, 2), (key2827, 2), (key2778, 2), (key2801, 2), (key3022, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2624, 2), (key2698, 2), (key3009, 2), (key3016, 2), (key2659, 2), (key2757, 2), (key2608, 2), (key2663, 2), (key2724, 2), (key2827, 2), (key2638, 2), (key2792, 2), (key2614, 2), (key2669, 2), (key2858, 2), (key2704, 2), (key2807, 2), (key2868, 2), (key2630, 2), (key2784, 2), (key2724, 2), (key2827, 2), (key2638, 2), (key2792, 2), (key2614, 2), (key2669, 2)]

theorem rawRowCheck18619 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form2 = rawRow18619 := by decide +kernel

def row18619 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18619 : row18619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18619 := by decide +kernel

theorem rowEval18619 (x : Key → ℝ) : Integer.Sparse.eval row18619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18619, Integer.Sparse.eval_collectBalanced, rawRowCheck18619]

def rawRow18620 : Integer.Sparse Key := [(key2868, 2), (key2858, 2), (key2851, 2), (key2922, 2), (key2919, 2), (key2827, 2), (key2792, 2), (key2801, 2), (key2778, 2), (key2918, 2), (key2807, 2), (key2784, 2), (key2868, 2), (key2858, 2), (key2851, 2), (key3025, 2), (key3022, 2), (key2724, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key3021, 2), (key2704, 2), (key2630, 2), (key2922, 2), (key2919, 2), (key2827, 2), (key2792, 2), (key2801, 2), (key2778, 2), (key3025, 2), (key3022, 2), (key2724, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key3016, 2), (key3009, 2), (key2757, 2), (key2659, 2), (key2663, 2), (key2608, 2), (key2827, 2), (key2724, 2), (key2792, 2), (key2638, 2), (key2669, 2), (key2614, 2), (key2858, 2), (key2807, 2), (key2704, 2), (key2868, 2), (key2784, 2), (key2630, 2), (key2827, 2), (key2724, 2), (key2792, 2), (key2638, 2), (key2669, 2), (key2614, 2)]

theorem rawRowCheck18620 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form2 = rawRow18620 := by decide +kernel

def row18620 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18620 : row18620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18620 := by decide +kernel

theorem rowEval18620 (x : Key → ℝ) : Integer.Sparse.eval row18620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18620, Integer.Sparse.eval_collectBalanced, rawRowCheck18620]

def rawRow18621 : Integer.Sparse Key := [(key2918, 2), (key2919, 2), (key2922, 2), (key2784, 2), (key2792, 2), (key2807, 2), (key2858, 2), (key2827, 2), (key2868, 2), (key2778, 2), (key2801, 2), (key2851, 2), (key3021, 2), (key3022, 2), (key3025, 2), (key2630, 2), (key2638, 2), (key2704, 2), (key2858, 2), (key2724, 2), (key2868, 2), (key2624, 2), (key2698, 2), (key2851, 2), (key3007, 2), (key3009, 2), (key3011, 2), (key3022, 2), (key3016, 2), (key3025, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2919, 2), (key2757, 2), (key2922, 2), (key2614, 2), (key2638, 2), (key2669, 2), (key2792, 2), (key2724, 2), (key2827, 2), (key2608, 2), (key2624, 2), (key2663, 2), (key2698, 2), (key2778, 2), (key2801, 2), (key2724, 2), (key2827, 2), (key2868, 2), (key2638, 2), (key2792, 2), (key2858, 2), (key2614, 2), (key2630, 2), (key2669, 2), (key2704, 2), (key2784, 2), (key2807, 2)]

theorem rawRowCheck18621 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form2 = rawRow18621 := by decide +kernel

def row18621 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18621 : row18621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18621 := by decide +kernel

theorem rowEval18621 (x : Key → ℝ) : Integer.Sparse.eval row18621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18621, Integer.Sparse.eval_collectBalanced, rawRowCheck18621]

def rawRow18622 : Integer.Sparse Key := [(key2919, 2), (key2918, 2), (key2922, 2), (key2792, 2), (key2784, 2), (key2858, 2), (key2807, 2), (key2868, 2), (key2827, 2), (key2778, 2), (key2851, 2), (key2801, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key2638, 2), (key2630, 2), (key2858, 2), (key2704, 2), (key2868, 2), (key2724, 2), (key2624, 2), (key2851, 2), (key2698, 2), (key3009, 2), (key3007, 2), (key3022, 2), (key3011, 2), (key3025, 2), (key3016, 2), (key2659, 2), (key2657, 2), (key2919, 2), (key2752, 2), (key2922, 2), (key2757, 2), (key2638, 2), (key2614, 2), (key2792, 2), (key2669, 2), (key2827, 2), (key2724, 2), (key2624, 2), (key2608, 2), (key2698, 2), (key2663, 2), (key2801, 2), (key2778, 2), (key2724, 2), (key2868, 2), (key2827, 2), (key2638, 2), (key2858, 2), (key2792, 2), (key2630, 2), (key2614, 2), (key2704, 2), (key2669, 2), (key2807, 2), (key2784, 2)]

theorem rawRowCheck18622 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form2 = rawRow18622 := by decide +kernel

def row18622 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18622 : row18622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18622 := by decide +kernel

theorem rowEval18622 (x : Key → ℝ) : Integer.Sparse.eval row18622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18622, Integer.Sparse.eval_collectBalanced, rawRowCheck18622]

def rawRow18623 : Integer.Sparse Key := [(key2918, 2), (key2922, 2), (key2919, 2), (key2807, 2), (key2827, 2), (key2784, 2), (key2868, 2), (key2792, 2), (key2858, 2), (key2801, 2), (key2778, 2), (key2851, 2), (key3021, 2), (key3025, 2), (key3022, 2), (key2704, 2), (key2724, 2), (key2630, 2), (key2868, 2), (key2638, 2), (key2858, 2), (key2698, 2), (key2624, 2), (key2851, 2), (key3011, 2), (key3016, 2), (key3007, 2), (key3025, 2), (key3009, 2), (key3022, 2), (key2752, 2), (key2757, 2), (key2657, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2669, 2), (key2724, 2), (key2614, 2), (key2827, 2), (key2638, 2), (key2792, 2), (key2663, 2), (key2698, 2), (key2608, 2), (key2801, 2), (key2624, 2), (key2698, 2), (key2827, 2), (key2724, 2), (key2868, 2), (key2792, 2), (key2638, 2), (key2858, 2), (key2669, 2), (key2784, 2), (key2614, 2), (key2807, 2), (key2630, 2), (key2704, 2)]

theorem rawRowCheck18623 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form2 = rawRow18623 := by decide +kernel

def row18623 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 2), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18623 : row18623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18623 := by decide +kernel

theorem rowEval18623 (x : Key → ℝ) : Integer.Sparse.eval row18623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18623, Integer.Sparse.eval_collectBalanced, rawRowCheck18623]

def rawRow18624 : Integer.Sparse Key := [(key2922, 2), (key2918, 2), (key2919, 2), (key2827, 2), (key2807, 2), (key2868, 2), (key2784, 2), (key2858, 2), (key2792, 2), (key2801, 2), (key2851, 2), (key2778, 2), (key3025, 2), (key3021, 2), (key3022, 2), (key2724, 2), (key2704, 2), (key2868, 2), (key2630, 2), (key2858, 2), (key2638, 2), (key2698, 2), (key2851, 2), (key2624, 2), (key3016, 2), (key3011, 2), (key3025, 2), (key3007, 2), (key3022, 2), (key3009, 2), (key2757, 2), (key2752, 2), (key2922, 2), (key2657, 2), (key2919, 2), (key2659, 2), (key2724, 2), (key2669, 2), (key2827, 2), (key2614, 2), (key2792, 2), (key2638, 2), (key2698, 2), (key2663, 2), (key2801, 2), (key2608, 2), (key2698, 2), (key2624, 2), (key2827, 2), (key2868, 2), (key2724, 2), (key2792, 2), (key2858, 2), (key2638, 2), (key2784, 2), (key2669, 2), (key2807, 2), (key2614, 2), (key2704, 2), (key2630, 2)]

theorem rawRowCheck18624 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form2 = rawRow18624 := by decide +kernel

def row18624 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 2), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18624 : row18624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18624 := by decide +kernel

theorem rowEval18624 (x : Key → ℝ) : Integer.Sparse.eval row18624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18624, Integer.Sparse.eval_collectBalanced, rawRowCheck18624]

def rawRow18625 : Integer.Sparse Key := [(key2919, 2), (key2922, 2), (key2918, 2), (key2858, 2), (key2868, 2), (key2792, 2), (key2827, 2), (key2784, 2), (key2807, 2), (key2851, 2), (key2778, 2), (key2801, 2), (key3022, 2), (key3025, 2), (key3021, 2), (key2858, 2), (key2868, 2), (key2638, 2), (key2724, 2), (key2630, 2), (key2704, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key3022, 2), (key3025, 2), (key3009, 2), (key3016, 2), (key3007, 2), (key3011, 2), (key2919, 2), (key2922, 2), (key2659, 2), (key2757, 2), (key2657, 2), (key2752, 2), (key2792, 2), (key2827, 2), (key2638, 2), (key2724, 2), (key2614, 2), (key2669, 2), (key2778, 2), (key2801, 2), (key2624, 2), (key2698, 2), (key2608, 2), (key2663, 2), (key2868, 2), (key2724, 2), (key2827, 2), (key2858, 2), (key2638, 2), (key2792, 2), (key2704, 2), (key2807, 2), (key2630, 2), (key2784, 2), (key2614, 2), (key2669, 2)]

theorem rawRowCheck18625 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form2 = rawRow18625 := by decide +kernel

def row18625 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18625 : row18625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18625 := by decide +kernel

theorem rowEval18625 (x : Key → ℝ) : Integer.Sparse.eval row18625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18625, Integer.Sparse.eval_collectBalanced, rawRowCheck18625]

def rawRow18626 : Integer.Sparse Key := [(key2922, 2), (key2919, 2), (key2918, 2), (key2868, 2), (key2858, 2), (key2827, 2), (key2792, 2), (key2807, 2), (key2784, 2), (key2851, 2), (key2801, 2), (key2778, 2), (key3025, 2), (key3022, 2), (key3021, 2), (key2868, 2), (key2858, 2), (key2724, 2), (key2638, 2), (key2704, 2), (key2630, 2), (key2851, 2), (key2698, 2), (key2624, 2), (key3025, 2), (key3022, 2), (key3016, 2), (key3009, 2), (key3011, 2), (key3007, 2), (key2922, 2), (key2919, 2), (key2757, 2), (key2659, 2), (key2752, 2), (key2657, 2), (key2827, 2), (key2792, 2), (key2724, 2), (key2638, 2), (key2669, 2), (key2614, 2), (key2801, 2), (key2778, 2), (key2698, 2), (key2624, 2), (key2663, 2), (key2608, 2), (key2868, 2), (key2827, 2), (key2724, 2), (key2858, 2), (key2792, 2), (key2638, 2), (key2807, 2), (key2704, 2), (key2784, 2), (key2630, 2), (key2669, 2), (key2614, 2)]

theorem rawRowCheck18626 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form2 = rawRow18626 := by decide +kernel

def row18626 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

theorem rowCheck18626 : row18626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18626 := by decide +kernel

theorem rowEval18626 (x : Key → ℝ) : Integer.Sparse.eval row18626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18626, Integer.Sparse.eval_collectBalanced, rawRowCheck18626]

def rawRow18627 : Integer.Sparse Key := [(key3007, 2), (key3007, 2), (key3009, 2), (key3011, 2), (key3011, 2), (key3021, 2), (key3021, 2), (key3022, 2), (key3022, 2), (key3016, 2), (key3025, 2), (key3025, 2), (key2657, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2752, 2), (key2918, 2), (key2918, 2), (key2919, 2), (key2919, 2), (key2757, 2), (key2922, 2), (key2922, 2), (key2614, 2), (key2614, 2), (key2630, 2), (key2630, 2), (key2638, 2), (key2638, 2), (key2669, 2), (key2669, 2), (key2784, 2), (key2784, 2), (key2792, 2), (key2792, 2), (key2704, 2), (key2704, 2), (key2807, 2), (key2807, 2), (key2858, 2), (key2858, 2), (key2724, 2), (key2724, 2), (key2827, 2), (key2827, 2), (key2868, 2), (key2868, 2), (key2608, 2), (key2624, 2), (key2624, 2), (key2663, 2), (key2698, 2), (key2698, 2), (key2778, 2), (key2778, 2), (key2801, 2), (key2801, 2), (key2851, 2), (key2851, 2)]

theorem rawRowCheck18627 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form2 = rawRow18627 := by decide +kernel

def row18627 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18627 : row18627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18627 := by decide +kernel

theorem rowEval18627 (x : Key → ℝ) : Integer.Sparse.eval row18627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18627, Integer.Sparse.eval_collectBalanced, rawRowCheck18627]

def rawRow18628 : Integer.Sparse Key := [(key3007, 2), (key3009, 2), (key3007, 2), (key3021, 2), (key3022, 2), (key3011, 2), (key3022, 2), (key3011, 2), (key3021, 2), (key3025, 2), (key3016, 2), (key3025, 2), (key2657, 2), (key2659, 2), (key2657, 2), (key2918, 2), (key2919, 2), (key2752, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2922, 2), (key2757, 2), (key2922, 2), (key2630, 2), (key2638, 2), (key2614, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2784, 2), (key2792, 2), (key2669, 2), (key2792, 2), (key2669, 2), (key2784, 2), (key2807, 2), (key2858, 2), (key2704, 2), (key2858, 2), (key2704, 2), (key2807, 2), (key2827, 2), (key2868, 2), (key2724, 2), (key2868, 2), (key2724, 2), (key2827, 2), (key2624, 2), (key2608, 2), (key2624, 2), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, 2), (key2851, 2), (key2778, 2), (key2851, 2), (key2778, 2), (key2801, 2)]

theorem rawRowCheck18628 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form2 = rawRow18628 := by decide +kernel

def row18628 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18628 : row18628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18628 := by decide +kernel

theorem rowEval18628 (x : Key → ℝ) : Integer.Sparse.eval row18628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18628, Integer.Sparse.eval_collectBalanced, rawRowCheck18628]

def rawRow18629 : Integer.Sparse Key := [(key3009, 2), (key3007, 2), (key3007, 2), (key3022, 2), (key3021, 2), (key3022, 2), (key3011, 2), (key3021, 2), (key3011, 2), (key3025, 2), (key3025, 2), (key3016, 2), (key2659, 2), (key2657, 2), (key2657, 2), (key2919, 2), (key2918, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2752, 2), (key2922, 2), (key2922, 2), (key2757, 2), (key2638, 2), (key2630, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2614, 2), (key2792, 2), (key2784, 2), (key2792, 2), (key2669, 2), (key2784, 2), (key2669, 2), (key2858, 2), (key2807, 2), (key2858, 2), (key2704, 2), (key2807, 2), (key2704, 2), (key2868, 2), (key2827, 2), (key2868, 2), (key2724, 2), (key2827, 2), (key2724, 2), (key2624, 2), (key2624, 2), (key2608, 2), (key2698, 2), (key2698, 2), (key2663, 2), (key2851, 2), (key2801, 2), (key2851, 2), (key2778, 2), (key2801, 2), (key2778, 2)]

theorem rawRowCheck18629 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form2 = rawRow18629 := by decide +kernel

def row18629 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18629 : row18629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18629 := by decide +kernel

theorem rowEval18629 (x : Key → ℝ) : Integer.Sparse.eval row18629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18629, Integer.Sparse.eval_collectBalanced, rawRowCheck18629]

def rawRow18630 : Integer.Sparse Key := [(key3011, 2), (key3011, 2), (key3016, 2), (key3007, 2), (key3007, 2), (key3021, 2), (key3021, 2), (key3025, 2), (key3025, 2), (key3009, 2), (key3022, 2), (key3022, 2), (key2752, 2), (key2752, 2), (key2757, 2), (key2657, 2), (key2657, 2), (key2918, 2), (key2918, 2), (key2922, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2919, 2), (key2669, 2), (key2669, 2), (key2704, 2), (key2704, 2), (key2724, 2), (key2724, 2), (key2614, 2), (key2614, 2), (key2807, 2), (key2807, 2), (key2827, 2), (key2827, 2), (key2630, 2), (key2630, 2), (key2784, 2), (key2784, 2), (key2868, 2), (key2868, 2), (key2638, 2), (key2638, 2), (key2792, 2), (key2792, 2), (key2858, 2), (key2858, 2), (key2663, 2), (key2698, 2), (key2698, 2), (key2608, 2), (key2801, 2), (key2801, 2), (key2624, 2), (key2624, 2), (key2698, 2), (key2698, 2), (key2851, 2), (key2851, 2)]

theorem rawRowCheck18630 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form2 = rawRow18630 := by decide +kernel

def row18630 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18630 : row18630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18630 := by decide +kernel

theorem rowEval18630 (x : Key → ℝ) : Integer.Sparse.eval row18630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18630, Integer.Sparse.eval_collectBalanced, rawRowCheck18630]

def rawRow18631 : Integer.Sparse Key := [(key3011, 2), (key3016, 2), (key3011, 2), (key3021, 2), (key3025, 2), (key3007, 2), (key3025, 2), (key3007, 2), (key3021, 2), (key3022, 2), (key3009, 2), (key3022, 2), (key2752, 2), (key2757, 2), (key2752, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2922, 2), (key2657, 2), (key2918, 2), (key2919, 2), (key2659, 2), (key2919, 2), (key2704, 2), (key2724, 2), (key2669, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2784, 2), (key2868, 2), (key2630, 2), (key2868, 2), (key2630, 2), (key2784, 2), (key2792, 2), (key2858, 2), (key2638, 2), (key2858, 2), (key2638, 2), (key2792, 2), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, 2), (key2608, 2), (key2801, 2), (key2698, 2), (key2851, 2), (key2624, 2), (key2851, 2), (key2624, 2), (key2698, 2)]

theorem rawRowCheck18631 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form2 = rawRow18631 := by decide +kernel

def row18631 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18631 : row18631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18631 := by decide +kernel

theorem rowEval18631 (x : Key → ℝ) : Integer.Sparse.eval row18631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18631, Integer.Sparse.eval_collectBalanced, rawRowCheck18631]

def rawRow18632 : Integer.Sparse Key := [(key3016, 2), (key3011, 2), (key3011, 2), (key3025, 2), (key3021, 2), (key3025, 2), (key3007, 2), (key3021, 2), (key3007, 2), (key3022, 2), (key3022, 2), (key3009, 2), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2918, 2), (key2657, 2), (key2919, 2), (key2919, 2), (key2659, 2), (key2724, 2), (key2704, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2669, 2), (key2827, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2614, 2), (key2868, 2), (key2784, 2), (key2868, 2), (key2630, 2), (key2784, 2), (key2630, 2), (key2858, 2), (key2792, 2), (key2858, 2), (key2638, 2), (key2792, 2), (key2638, 2), (key2698, 2), (key2698, 2), (key2663, 2), (key2801, 2), (key2801, 2), (key2608, 2), (key2851, 2), (key2698, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key2624, 2)]

theorem rawRowCheck18632 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form2 = rawRow18632 := by decide +kernel

def row18632 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18632 : row18632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18632 := by decide +kernel

theorem rowEval18632 (x : Key → ℝ) : Integer.Sparse.eval row18632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18632, Integer.Sparse.eval_collectBalanced, rawRowCheck18632]

def rawRow18633 : Integer.Sparse Key := [(key3021, 2), (key3022, 2), (key3025, 2), (key3007, 2), (key3009, 2), (key3011, 2), (key3022, 2), (key3016, 2), (key3025, 2), (key3007, 2), (key3011, 2), (key3021, 2), (key2918, 2), (key2919, 2), (key2922, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2919, 2), (key2757, 2), (key2922, 2), (key2657, 2), (key2752, 2), (key2918, 2), (key2784, 2), (key2792, 2), (key2807, 2), (key2858, 2), (key2827, 2), (key2868, 2), (key2630, 2), (key2638, 2), (key2704, 2), (key2858, 2), (key2724, 2), (key2868, 2), (key2614, 2), (key2638, 2), (key2669, 2), (key2792, 2), (key2724, 2), (key2827, 2), (key2614, 2), (key2630, 2), (key2669, 2), (key2784, 2), (key2704, 2), (key2807, 2), (key2778, 2), (key2801, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key2851, 2), (key2608, 2), (key2624, 2), (key2663, 2), (key2698, 2), (key2778, 2), (key2801, 2)]

theorem rawRowCheck18633 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form2 = rawRow18633 := by decide +kernel

def row18633 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18633 : row18633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18633 := by decide +kernel

theorem rowEval18633 (x : Key → ℝ) : Integer.Sparse.eval row18633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18633, Integer.Sparse.eval_collectBalanced, rawRowCheck18633]

def rawRow18634 : Integer.Sparse Key := [(key3022, 2), (key3021, 2), (key3025, 2), (key3009, 2), (key3007, 2), (key3022, 2), (key3011, 2), (key3025, 2), (key3016, 2), (key3007, 2), (key3021, 2), (key3011, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2659, 2), (key2657, 2), (key2919, 2), (key2752, 2), (key2922, 2), (key2757, 2), (key2657, 2), (key2918, 2), (key2752, 2), (key2792, 2), (key2784, 2), (key2858, 2), (key2807, 2), (key2868, 2), (key2827, 2), (key2638, 2), (key2630, 2), (key2858, 2), (key2704, 2), (key2868, 2), (key2724, 2), (key2638, 2), (key2614, 2), (key2792, 2), (key2669, 2), (key2827, 2), (key2724, 2), (key2630, 2), (key2614, 2), (key2784, 2), (key2669, 2), (key2807, 2), (key2704, 2), (key2778, 2), (key2851, 2), (key2801, 2), (key2624, 2), (key2851, 2), (key2698, 2), (key2624, 2), (key2608, 2), (key2698, 2), (key2663, 2), (key2801, 2), (key2778, 2)]

theorem rawRowCheck18634 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form2 = rawRow18634 := by decide +kernel

def row18634 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18634 : row18634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18634 := by decide +kernel

theorem rowEval18634 (x : Key → ℝ) : Integer.Sparse.eval row18634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18634, Integer.Sparse.eval_collectBalanced, rawRowCheck18634]

def rawRow18635 : Integer.Sparse Key := [(key3021, 2), (key3025, 2), (key3022, 2), (key3011, 2), (key3016, 2), (key3007, 2), (key3025, 2), (key3009, 2), (key3022, 2), (key3011, 2), (key3007, 2), (key3021, 2), (key2918, 2), (key2922, 2), (key2919, 2), (key2752, 2), (key2757, 2), (key2657, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2752, 2), (key2657, 2), (key2918, 2), (key2807, 2), (key2827, 2), (key2784, 2), (key2868, 2), (key2792, 2), (key2858, 2), (key2704, 2), (key2724, 2), (key2630, 2), (key2868, 2), (key2638, 2), (key2858, 2), (key2669, 2), (key2724, 2), (key2614, 2), (key2827, 2), (key2638, 2), (key2792, 2), (key2669, 2), (key2704, 2), (key2614, 2), (key2807, 2), (key2630, 2), (key2784, 2), (key2801, 2), (key2778, 2), (key2851, 2), (key2698, 2), (key2624, 2), (key2851, 2), (key2663, 2), (key2698, 2), (key2608, 2), (key2801, 2), (key2624, 2), (key2698, 2)]

theorem rawRowCheck18635 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form2 = rawRow18635 := by decide +kernel

def row18635 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18635 : row18635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18635 := by decide +kernel

theorem rowEval18635 (x : Key → ℝ) : Integer.Sparse.eval row18635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18635, Integer.Sparse.eval_collectBalanced, rawRowCheck18635]

def rawRow18636 : Integer.Sparse Key := [(key3025, 2), (key3021, 2), (key3022, 2), (key3016, 2), (key3011, 2), (key3025, 2), (key3007, 2), (key3022, 2), (key3009, 2), (key3011, 2), (key3021, 2), (key3007, 2), (key2922, 2), (key2918, 2), (key2919, 2), (key2757, 2), (key2752, 2), (key2922, 2), (key2657, 2), (key2919, 2), (key2659, 2), (key2752, 2), (key2918, 2), (key2657, 2), (key2827, 2), (key2807, 2), (key2868, 2), (key2784, 2), (key2858, 2), (key2792, 2), (key2724, 2), (key2704, 2), (key2868, 2), (key2630, 2), (key2858, 2), (key2638, 2), (key2724, 2), (key2669, 2), (key2827, 2), (key2614, 2), (key2792, 2), (key2638, 2), (key2704, 2), (key2669, 2), (key2807, 2), (key2614, 2), (key2784, 2), (key2630, 2), (key2801, 2), (key2851, 2), (key2778, 2), (key2698, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key2663, 2), (key2801, 2), (key2608, 2), (key2698, 2), (key2624, 2)]

theorem rawRowCheck18636 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form2 = rawRow18636 := by decide +kernel

def row18636 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18636 : row18636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18636 := by decide +kernel

theorem rowEval18636 (x : Key → ℝ) : Integer.Sparse.eval row18636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18636, Integer.Sparse.eval_collectBalanced, rawRowCheck18636]

def rawRow18637 : Integer.Sparse Key := [(key3022, 2), (key3025, 2), (key3021, 2), (key3022, 2), (key3025, 2), (key3009, 2), (key3016, 2), (key3007, 2), (key3011, 2), (key3021, 2), (key3007, 2), (key3011, 2), (key2919, 2), (key2922, 2), (key2918, 2), (key2919, 2), (key2922, 2), (key2659, 2), (key2757, 2), (key2657, 2), (key2752, 2), (key2918, 2), (key2657, 2), (key2752, 2), (key2858, 2), (key2868, 2), (key2792, 2), (key2827, 2), (key2784, 2), (key2807, 2), (key2858, 2), (key2868, 2), (key2638, 2), (key2724, 2), (key2630, 2), (key2704, 2), (key2792, 2), (key2827, 2), (key2638, 2), (key2724, 2), (key2614, 2), (key2669, 2), (key2784, 2), (key2807, 2), (key2630, 2), (key2704, 2), (key2614, 2), (key2669, 2), (key2851, 2), (key2778, 2), (key2801, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key2778, 2), (key2801, 2), (key2624, 2), (key2698, 2), (key2608, 2), (key2663, 2)]

theorem rawRowCheck18637 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form2 = rawRow18637 := by decide +kernel

def row18637 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18637 : row18637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18637 := by decide +kernel

theorem rowEval18637 (x : Key → ℝ) : Integer.Sparse.eval row18637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18637, Integer.Sparse.eval_collectBalanced, rawRowCheck18637]

def rawRow18638 : Integer.Sparse Key := [(key3025, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key3022, 2), (key3016, 2), (key3009, 2), (key3011, 2), (key3007, 2), (key3021, 2), (key3011, 2), (key3007, 2), (key2922, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2919, 2), (key2757, 2), (key2659, 2), (key2752, 2), (key2657, 2), (key2918, 2), (key2752, 2), (key2657, 2), (key2868, 2), (key2858, 2), (key2827, 2), (key2792, 2), (key2807, 2), (key2784, 2), (key2868, 2), (key2858, 2), (key2724, 2), (key2638, 2), (key2704, 2), (key2630, 2), (key2827, 2), (key2792, 2), (key2724, 2), (key2638, 2), (key2669, 2), (key2614, 2), (key2807, 2), (key2784, 2), (key2704, 2), (key2630, 2), (key2669, 2), (key2614, 2), (key2851, 2), (key2801, 2), (key2778, 2), (key2851, 2), (key2698, 2), (key2624, 2), (key2801, 2), (key2778, 2), (key2698, 2), (key2624, 2), (key2663, 2), (key2608, 2)]

theorem rawRowCheck18638 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form2 = rawRow18638 := by decide +kernel

def row18638 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

theorem rowCheck18638 : row18638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18638 := by decide +kernel

theorem rowEval18638 (x : Key → ℝ) : Integer.Sparse.eval row18638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18638, Integer.Sparse.eval_collectBalanced, rawRowCheck18638]

def rawRow18639 : Integer.Sparse Key := [(key2355, 6), (key2355, 6), (key2355, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2512, 6), (key2512, 6), (key2512, 6)]

theorem rawRowCheck18639 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18639 := by decide +kernel

def row18639 : Integer.Sparse Key := [(key2355, 24), (key2450, 72), (key2512, 24)]

theorem rowCheck18639 : row18639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18639 := by decide +kernel

theorem rowEval18639 (x : Key → ℝ) : Integer.Sparse.eval row18639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18639, Integer.Sparse.eval_collectBalanced, rawRowCheck18639]

def rawRow18640 : Integer.Sparse Key := [(key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2355, 6), (key2355, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2512, 6), (key2512, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6)]

theorem rawRowCheck18640 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18640 := by decide +kernel

def row18640 : Integer.Sparse Key := [(key2355, 24), (key2450, 72), (key2512, 24)]

theorem rowCheck18640 : row18640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18640 := by decide +kernel

theorem rowEval18640 (x : Key → ℝ) : Integer.Sparse.eval row18640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18640, Integer.Sparse.eval_collectBalanced, rawRowCheck18640]

def rawRow18641 : Integer.Sparse Key := [(key2450, 6), (key2450, 6), (key2512, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2355, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2512, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2355, 6), (key2450, 6), (key2450, 6)]

theorem rawRowCheck18641 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18641 := by decide +kernel

def row18641 : Integer.Sparse Key := [(key2355, 24), (key2450, 72), (key2512, 24)]

theorem rowCheck18641 : row18641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18641 := by decide +kernel

theorem rowEval18641 (x : Key → ℝ) : Integer.Sparse.eval row18641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18641, Integer.Sparse.eval_collectBalanced, rawRowCheck18641]

def rawRow18642 : Integer.Sparse Key := [(key2450, 6), (key2512, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2355, 6), (key2512, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2355, 6), (key2450, 6)]

theorem rawRowCheck18642 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18642 := by decide +kernel

def row18642 : Integer.Sparse Key := [(key2355, 24), (key2450, 72), (key2512, 24)]

theorem rowCheck18642 : row18642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18642 := by decide +kernel

theorem rowEval18642 (x : Key → ℝ) : Integer.Sparse.eval row18642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18642, Integer.Sparse.eval_collectBalanced, rawRowCheck18642]

def rawRow18643 : Integer.Sparse Key := [(key2512, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2450, 6), (key2512, 6), (key2355, 6), (key2450, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2355, 6)]

theorem rawRowCheck18643 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18643 := by decide +kernel

def row18643 : Integer.Sparse Key := [(key2355, 24), (key2450, 72), (key2512, 24)]

theorem rowCheck18643 : row18643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18643 := by decide +kernel

theorem rowEval18643 (x : Key → ℝ) : Integer.Sparse.eval row18643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18643, Integer.Sparse.eval_collectBalanced, rawRowCheck18643]

def rawRow18644 : Integer.Sparse Key := [(key968, 24), (key1082, 24), (key1082, 24), (key1082, 24), (key1082, 24)]

theorem rawRowCheck18644 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18644 := by decide +kernel

def row18644 : Integer.Sparse Key := [(key968, 24), (key1082, 96)]

theorem rowCheck18644 : row18644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18644 := by decide +kernel

theorem rowEval18644 (x : Key → ℝ) : Integer.Sparse.eval row18644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18644, Integer.Sparse.eval_collectBalanced, rawRowCheck18644]

def rawRow18645 : Integer.Sparse Key := [(key1082, 24), (key968, 24), (key1082, 24), (key1082, 24), (key1082, 24)]

theorem rawRowCheck18645 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18645 := by decide +kernel

def row18645 : Integer.Sparse Key := [(key968, 24), (key1082, 96)]

theorem rowCheck18645 : row18645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18645 := by decide +kernel

theorem rowEval18645 (x : Key → ℝ) : Integer.Sparse.eval row18645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18645, Integer.Sparse.eval_collectBalanced, rawRowCheck18645]

def rawRow18646 : Integer.Sparse Key := [(key1082, 24), (key1082, 24), (key968, 24), (key1082, 24), (key1082, 24)]

theorem rawRowCheck18646 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18646 := by decide +kernel

def row18646 : Integer.Sparse Key := [(key968, 24), (key1082, 96)]

theorem rowCheck18646 : row18646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18646 := by decide +kernel

theorem rowEval18646 (x : Key → ℝ) : Integer.Sparse.eval row18646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18646, Integer.Sparse.eval_collectBalanced, rawRowCheck18646]

def rawRow18647 : Integer.Sparse Key := [(key1082, 24), (key1082, 24), (key1082, 24), (key968, 24), (key1082, 24)]

theorem rawRowCheck18647 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18647 := by decide +kernel

def row18647 : Integer.Sparse Key := [(key968, 24), (key1082, 96)]

theorem rowCheck18647 : row18647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18647 := by decide +kernel

theorem rowEval18647 (x : Key → ℝ) : Integer.Sparse.eval row18647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18647, Integer.Sparse.eval_collectBalanced, rawRowCheck18647]

def rawRow18648 : Integer.Sparse Key := [(key1082, 24), (key1082, 24), (key1082, 24), (key1082, 24), (key968, 24)]

theorem rawRowCheck18648 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18648 := by decide +kernel

def row18648 : Integer.Sparse Key := [(key968, 24), (key1082, 96)]

theorem rowCheck18648 : row18648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18648 := by decide +kernel

theorem rowEval18648 (x : Key → ℝ) : Integer.Sparse.eval row18648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18648, Integer.Sparse.eval_collectBalanced, rawRowCheck18648]

def rawRow18649 : Integer.Sparse Key := [(key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2)]

theorem rawRowCheck18649 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form2 = rawRow18649 := by decide +kernel

def row18649 : Integer.Sparse Key := [(key2585, 24), (key2764, 24), (key2841, 48), (key2873, 24)]

theorem rowCheck18649 : row18649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18649 := by decide +kernel

theorem rowEval18649 (x : Key → ℝ) : Integer.Sparse.eval row18649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18649, Integer.Sparse.eval_collectBalanced, rawRowCheck18649]

def rawRow18650 : Integer.Sparse Key := [(key2764, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2)]

theorem rawRowCheck18650 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form2 = rawRow18650 := by decide +kernel

def row18650 : Integer.Sparse Key := [(key2585, 24), (key2764, 24), (key2841, 48), (key2873, 24)]

theorem rowCheck18650 : row18650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18650 := by decide +kernel

theorem rowEval18650 (x : Key → ℝ) : Integer.Sparse.eval row18650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18650, Integer.Sparse.eval_collectBalanced, rawRowCheck18650]

def rawRow18651 : Integer.Sparse Key := [(key2841, 2), (key2841, 2), (key2873, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2)]

theorem rawRowCheck18651 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form2 = rawRow18651 := by decide +kernel

def row18651 : Integer.Sparse Key := [(key2585, 24), (key2764, 24), (key2841, 48), (key2873, 24)]

theorem rowCheck18651 : row18651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18651 := by decide +kernel

theorem rowEval18651 (x : Key → ℝ) : Integer.Sparse.eval row18651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18651, Integer.Sparse.eval_collectBalanced, rawRowCheck18651]

def rawRow18652 : Integer.Sparse Key := [(key2841, 2), (key2873, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2764, 2), (key2873, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2585, 2), (key2873, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2764, 2), (key2873, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2585, 2), (key2873, 2), (key2585, 2), (key2841, 2), (key2764, 2), (key2873, 2), (key2585, 2), (key2873, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2585, 2), (key2764, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2585, 2), (key2764, 2)]

theorem rawRowCheck18652 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form2 = rawRow18652 := by decide +kernel

def row18652 : Integer.Sparse Key := [(key2585, 24), (key2764, 24), (key2841, 48), (key2873, 24)]

theorem rowCheck18652 : row18652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18652 := by decide +kernel

theorem rowEval18652 (x : Key → ℝ) : Integer.Sparse.eval row18652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18652, Integer.Sparse.eval_collectBalanced, rawRowCheck18652]

def rawRow18653 : Integer.Sparse Key := [(key2873, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2841, 2), (key2873, 2), (key2764, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2764, 2), (key2873, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2841, 2), (key2873, 2), (key2585, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2873, 2), (key2841, 2), (key2873, 2), (key2764, 2), (key2841, 2), (key2764, 2), (key2873, 2), (key2841, 2), (key2873, 2), (key2585, 2), (key2841, 2), (key2585, 2), (key2873, 2), (key2764, 2), (key2873, 2), (key2585, 2), (key2764, 2), (key2585, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2585, 2), (key2764, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2585, 2), (key2764, 2), (key2585, 2)]

theorem rawRowCheck18653 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form2 = rawRow18653 := by decide +kernel

def row18653 : Integer.Sparse Key := [(key2585, 24), (key2764, 24), (key2841, 48), (key2873, 24)]

theorem rowCheck18653 : row18653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18653 := by decide +kernel

theorem rowEval18653 (x : Key → ℝ) : Integer.Sparse.eval row18653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18653, Integer.Sparse.eval_collectBalanced, rawRowCheck18653]

def rawRow18654 : Integer.Sparse Key := [(key2351, 24), (key2446, 24), (key2446, 24), (key2446, 24), (key2446, 24)]

theorem rawRowCheck18654 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form3 = rawRow18654 := by decide +kernel

def row18654 : Integer.Sparse Key := [(key2351, 24), (key2446, 96)]

theorem rowCheck18654 : row18654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18654 := by decide +kernel

theorem rowEval18654 (x : Key → ℝ) : Integer.Sparse.eval row18654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18654, Integer.Sparse.eval_collectBalanced, rawRowCheck18654]

def rawRow18655 : Integer.Sparse Key := [(key2446, 24), (key2351, 24), (key2446, 24), (key2446, 24), (key2446, 24)]

theorem rawRowCheck18655 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form3 = rawRow18655 := by decide +kernel

def row18655 : Integer.Sparse Key := [(key2351, 24), (key2446, 96)]

theorem rowCheck18655 : row18655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18655 := by decide +kernel

theorem rowEval18655 (x : Key → ℝ) : Integer.Sparse.eval row18655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18655, Integer.Sparse.eval_collectBalanced, rawRowCheck18655]

def rawRow18656 : Integer.Sparse Key := [(key2446, 24), (key2446, 24), (key2351, 24), (key2446, 24), (key2446, 24)]

theorem rawRowCheck18656 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form3 = rawRow18656 := by decide +kernel

def row18656 : Integer.Sparse Key := [(key2351, 24), (key2446, 96)]

theorem rowCheck18656 : row18656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18656 := by decide +kernel

theorem rowEval18656 (x : Key → ℝ) : Integer.Sparse.eval row18656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18656, Integer.Sparse.eval_collectBalanced, rawRowCheck18656]

def rawRow18657 : Integer.Sparse Key := [(key2446, 24), (key2446, 24), (key2446, 24), (key2351, 24), (key2446, 24)]

theorem rawRowCheck18657 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form3 = rawRow18657 := by decide +kernel

def row18657 : Integer.Sparse Key := [(key2351, 24), (key2446, 96)]

theorem rowCheck18657 : row18657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18657 := by decide +kernel

theorem rowEval18657 (x : Key → ℝ) : Integer.Sparse.eval row18657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18657, Integer.Sparse.eval_collectBalanced, rawRowCheck18657]

def rawRow18658 : Integer.Sparse Key := [(key2446, 24), (key2446, 24), (key2446, 24), (key2446, 24), (key2351, 24)]

theorem rawRowCheck18658 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form3 = rawRow18658 := by decide +kernel

def row18658 : Integer.Sparse Key := [(key2351, 24), (key2446, 96)]

theorem rowCheck18658 : row18658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18658 := by decide +kernel

theorem rowEval18658 (x : Key → ℝ) : Integer.Sparse.eval row18658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18658, Integer.Sparse.eval_collectBalanced, rawRowCheck18658]

def rawRow18659 : Integer.Sparse Key := [(key971, 6), (key979, 6), (key979, 6), (key979, 6), (key1085, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1164, 6), (key1228, 6), (key1228, 6), (key1228, 6), (key1245, 6)]

theorem rawRowCheck18659 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form0 = rawRow18659 := by decide +kernel

def row18659 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18659 : row18659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18659 := by decide +kernel

theorem rowEval18659 (x : Key → ℝ) : Integer.Sparse.eval row18659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18659, Integer.Sparse.eval_collectBalanced, rawRowCheck18659]

def rawRow18660 : Integer.Sparse Key := [(key979, 6), (key971, 6), (key979, 6), (key979, 6), (key1093, 6), (key1085, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1164, 6), (key1093, 6), (key1228, 6), (key1228, 6), (key1245, 6), (key1228, 6)]

theorem rawRowCheck18660 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form0 = rawRow18660 := by decide +kernel

def row18660 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18660 : row18660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18660 := by decide +kernel

theorem rowEval18660 (x : Key → ℝ) : Integer.Sparse.eval row18660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18660, Integer.Sparse.eval_collectBalanced, rawRowCheck18660]

def rawRow18661 : Integer.Sparse Key := [(key979, 6), (key979, 6), (key971, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1245, 6), (key1228, 6), (key1228, 6)]

theorem rawRowCheck18661 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form0 = rawRow18661 := by decide +kernel

def row18661 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18661 : row18661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18661 := by decide +kernel

theorem rowEval18661 (x : Key → ℝ) : Integer.Sparse.eval row18661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18661, Integer.Sparse.eval_collectBalanced, rawRowCheck18661]

def rawRow18662 : Integer.Sparse Key := [(key979, 6), (key979, 6), (key979, 6), (key971, 6), (key1164, 6), (key1164, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1085, 6), (key1085, 6), (key1245, 6), (key1228, 6), (key1228, 6), (key1228, 6)]

theorem rawRowCheck18662 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18662 := by decide +kernel

def row18662 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18662 : row18662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18662 := by decide +kernel

theorem rowEval18662 (x : Key → ℝ) : Integer.Sparse.eval row18662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18662, Integer.Sparse.eval_collectBalanced, rawRowCheck18662]

def rawRow18663 : Integer.Sparse Key := [(key1085, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key971, 6), (key979, 6), (key979, 6), (key1085, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key1164, 6), (key1228, 6), (key1228, 6), (key1245, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1164, 6)]

theorem rawRowCheck18663 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form0 = rawRow18663 := by decide +kernel

def row18663 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18663 : row18663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18663 := by decide +kernel

theorem rowEval18663 (x : Key → ℝ) : Integer.Sparse.eval row18663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18663, Integer.Sparse.eval_collectBalanced, rawRowCheck18663]

def rawRow18664 : Integer.Sparse Key := [(key1093, 6), (key1085, 6), (key1093, 6), (key1228, 6), (key979, 6), (key971, 6), (key979, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key1228, 6), (key1245, 6), (key1228, 6), (key979, 6), (key1093, 6), (key1164, 6), (key1093, 6)]

theorem rawRowCheck18664 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form0 = rawRow18664 := by decide +kernel

def row18664 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18664 : row18664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18664 := by decide +kernel

theorem rowEval18664 (x : Key → ℝ) : Integer.Sparse.eval row18664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18664, Integer.Sparse.eval_collectBalanced, rawRowCheck18664]

def rawRow18665 : Integer.Sparse Key := [(key1093, 6), (key1093, 6), (key1085, 6), (key1228, 6), (key979, 6), (key979, 6), (key971, 6), (key1164, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1085, 6), (key1245, 6), (key1228, 6), (key1228, 6), (key979, 6), (key1164, 6), (key1093, 6), (key1093, 6)]

theorem rawRowCheck18665 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form0 = rawRow18665 := by decide +kernel

def row18665 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18665 : row18665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18665 := by decide +kernel

theorem rowEval18665 (x : Key → ℝ) : Integer.Sparse.eval row18665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18665, Integer.Sparse.eval_collectBalanced, rawRowCheck18665]

def rawRow18666 : Integer.Sparse Key := [(key1085, 6), (key1093, 6), (key1228, 6), (key1093, 6), (key1085, 6), (key1093, 6), (key1228, 6), (key971, 6), (key979, 6), (key1085, 6), (key1164, 6), (key1228, 6), (key1245, 6), (key979, 6), (key1093, 6), (key1164, 6), (key1093, 6), (key979, 6), (key1093, 6), (key1164, 6)]

theorem rawRowCheck18666 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form0 = rawRow18666 := by decide +kernel

def row18666 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18666 : row18666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18666 := by decide +kernel

theorem rowEval18666 (x : Key → ℝ) : Integer.Sparse.eval row18666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18666, Integer.Sparse.eval_collectBalanced, rawRowCheck18666]

def rawRow18667 : Integer.Sparse Key := [(key1093, 6), (key1085, 6), (key1228, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1228, 6), (key979, 6), (key971, 6), (key1164, 6), (key1085, 6), (key1245, 6), (key1228, 6), (key979, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key979, 6), (key1164, 6), (key1093, 6)]

theorem rawRowCheck18667 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form0 = rawRow18667 := by decide +kernel

def row18667 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18667 : row18667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18667 := by decide +kernel

theorem rowEval18667 (x : Key → ℝ) : Integer.Sparse.eval row18667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18667, Integer.Sparse.eval_collectBalanced, rawRowCheck18667]

def rawRow18668 : Integer.Sparse Key := [(key1085, 6), (key1228, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1228, 6), (key1093, 6), (key1085, 6), (key1228, 6), (key971, 6), (key1245, 6), (key979, 6), (key1164, 6), (key1093, 6), (key979, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key979, 6), (key1164, 6)]

theorem rawRowCheck18668 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form0 = rawRow18668 := by decide +kernel

def row18668 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18668 : row18668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18668 := by decide +kernel

theorem rowEval18668 (x : Key → ℝ) : Integer.Sparse.eval row18668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18668, Integer.Sparse.eval_collectBalanced, rawRowCheck18668]

def rawRow18669 : Integer.Sparse Key := [(key1228, 6), (key1085, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1085, 6), (key1093, 6), (key1228, 6), (key1085, 6), (key1245, 6), (key971, 6), (key1164, 6), (key979, 6), (key1093, 6), (key1164, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1164, 6), (key979, 6)]

theorem rawRowCheck18669 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form0 = rawRow18669 := by decide +kernel

def row18669 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18669 : row18669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18669 := by decide +kernel

theorem rowEval18669 (x : Key → ℝ) : Integer.Sparse.eval row18669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18669, Integer.Sparse.eval_collectBalanced, rawRowCheck18669]

def rawRow18670 : Integer.Sparse Key := [(key1093, 6), (key1228, 6), (key1085, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1085, 6), (key1164, 6), (key1245, 6), (key979, 6), (key1228, 6), (key971, 6), (key1085, 6), (key1164, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1164, 6), (key979, 6), (key1093, 6)]

theorem rawRowCheck18670 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form0 = rawRow18670 := by decide +kernel

def row18670 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18670 : row18670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18670 := by decide +kernel

theorem rowEval18670 (x : Key → ℝ) : Integer.Sparse.eval row18670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18670, Integer.Sparse.eval_collectBalanced, rawRowCheck18670]

def rawRow18671 : Integer.Sparse Key := [(key1228, 6), (key1093, 6), (key1085, 6), (key1093, 6), (key1228, 6), (key1093, 6), (key1085, 6), (key1245, 6), (key1164, 6), (key1228, 6), (key979, 6), (key1085, 6), (key971, 6), (key1164, 6), (key1093, 6), (key979, 6), (key1093, 6), (key1164, 6), (key1093, 6), (key979, 6)]

theorem rawRowCheck18671 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form0 = rawRow18671 := by decide +kernel

def row18671 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18671 : row18671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18671 := by decide +kernel

theorem rowEval18671 (x : Key → ℝ) : Integer.Sparse.eval row18671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18671, Integer.Sparse.eval_collectBalanced, rawRowCheck18671]

def rawRow18672 : Integer.Sparse Key := [(key1093, 6), (key1093, 6), (key1228, 6), (key1085, 6), (key1164, 6), (key1164, 6), (key1245, 6), (key979, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1228, 6), (key971, 6), (key1085, 6), (key1085, 6), (key1164, 6), (key979, 6), (key1093, 6), (key1093, 6)]

theorem rawRowCheck18672 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18672 := by decide +kernel

def row18672 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18672 : row18672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18672 := by decide +kernel

theorem rowEval18672 (x : Key → ℝ) : Integer.Sparse.eval row18672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18672, Integer.Sparse.eval_collectBalanced, rawRowCheck18672]

def rawRow18673 : Integer.Sparse Key := [(key1093, 6), (key1228, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1245, 6), (key1164, 6), (key1093, 6), (key1228, 6), (key979, 6), (key1228, 6), (key979, 6), (key1093, 6), (key1085, 6), (key971, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key979, 6), (key1093, 6)]

theorem rawRowCheck18673 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18673 := by decide +kernel

def row18673 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18673 : row18673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18673 := by decide +kernel

theorem rowEval18673 (x : Key → ℝ) : Integer.Sparse.eval row18673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18673, Integer.Sparse.eval_collectBalanced, rawRowCheck18673]

def rawRow18674 : Integer.Sparse Key := [(key1228, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1245, 6), (key1164, 6), (key1164, 6), (key1228, 6), (key1093, 6), (key1228, 6), (key979, 6), (key1093, 6), (key979, 6), (key1085, 6), (key1085, 6), (key971, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key979, 6)]

theorem rawRowCheck18674 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18674 := by decide +kernel

def row18674 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18674 : row18674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18674 := by decide +kernel

theorem rowEval18674 (x : Key → ℝ) : Integer.Sparse.eval row18674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18674, Integer.Sparse.eval_collectBalanced, rawRowCheck18674]

def rawRow18675 : Integer.Sparse Key := [(key1164, 6), (key1164, 6), (key1164, 6), (key1245, 6), (key979, 6), (key979, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1228, 6), (key1228, 6), (key971, 6), (key1085, 6), (key1085, 6), (key1085, 6)]

theorem rawRowCheck18675 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18675 := by decide +kernel

def row18675 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18675 : row18675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18675 := by decide +kernel

theorem rowEval18675 (x : Key → ℝ) : Integer.Sparse.eval row18675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18675, Integer.Sparse.eval_collectBalanced, rawRowCheck18675]

def rawRow18676 : Integer.Sparse Key := [(key1164, 6), (key1164, 6), (key1245, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key979, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1228, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key971, 6), (key1085, 6), (key1085, 6)]

theorem rawRowCheck18676 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18676 := by decide +kernel

def row18676 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18676 : row18676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18676 := by decide +kernel

theorem rowEval18676 (x : Key → ℝ) : Integer.Sparse.eval row18676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18676, Integer.Sparse.eval_collectBalanced, rawRowCheck18676]

def rawRow18677 : Integer.Sparse Key := [(key1164, 6), (key1245, 6), (key1164, 6), (key1164, 6), (key1093, 6), (key1228, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key979, 6), (key1228, 6), (key979, 6), (key1093, 6), (key1093, 6), (key979, 6), (key1093, 6), (key1085, 6), (key1085, 6), (key971, 6), (key1085, 6)]

theorem rawRowCheck18677 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18677 := by decide +kernel

def row18677 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18677 : row18677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18677 := by decide +kernel

theorem rowEval18677 (x : Key → ℝ) : Integer.Sparse.eval row18677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18677, Integer.Sparse.eval_collectBalanced, rawRowCheck18677]

def rawRow18678 : Integer.Sparse Key := [(key1245, 6), (key1164, 6), (key1164, 6), (key1164, 6), (key1228, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1093, 6), (key1228, 6), (key979, 6), (key1093, 6), (key979, 6), (key1093, 6), (key1093, 6), (key979, 6), (key1085, 6), (key1085, 6), (key1085, 6), (key971, 6)]

theorem rawRowCheck18678 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18678 := by decide +kernel

def row18678 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

theorem rowCheck18678 : row18678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18678 := by decide +kernel

theorem rowEval18678 (x : Key → ℝ) : Integer.Sparse.eval row18678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18678, Integer.Sparse.eval_collectBalanced, rawRowCheck18678]

def rawRow18679 : Integer.Sparse Key := [(key3, 24), (key86, 24), (key86, 24), (key86, 24), (key147, 24)]

theorem rawRowCheck18679 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form1 = rawRow18679 := by decide +kernel

def row18679 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18679 : row18679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18679 := by decide +kernel

theorem rowEval18679 (x : Key → ℝ) : Integer.Sparse.eval row18679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18679, Integer.Sparse.eval_collectBalanced, rawRowCheck18679]

def rawRow18680 : Integer.Sparse Key := [(key3, 24), (key86, 24), (key86, 24), (key147, 24), (key86, 24)]

theorem rawRowCheck18680 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form1 = rawRow18680 := by decide +kernel

def row18680 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18680 : row18680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18680 := by decide +kernel

theorem rowEval18680 (x : Key → ℝ) : Integer.Sparse.eval row18680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18680, Integer.Sparse.eval_collectBalanced, rawRowCheck18680]

def rawRow18681 : Integer.Sparse Key := [(key3, 24), (key86, 24), (key147, 24), (key86, 24), (key86, 24)]

theorem rawRowCheck18681 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form1 = rawRow18681 := by decide +kernel

def row18681 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18681 : row18681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18681 := by decide +kernel

theorem rowEval18681 (x : Key → ℝ) : Integer.Sparse.eval row18681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18681, Integer.Sparse.eval_collectBalanced, rawRowCheck18681]

def rawRow18682 : Integer.Sparse Key := [(key3, 24), (key147, 24), (key86, 24), (key86, 24), (key86, 24)]

theorem rawRowCheck18682 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18682 := by decide +kernel

def row18682 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18682 : row18682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18682 := by decide +kernel

theorem rowEval18682 (x : Key → ℝ) : Integer.Sparse.eval row18682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18682, Integer.Sparse.eval_collectBalanced, rawRowCheck18682]

def rawRow18683 : Integer.Sparse Key := [(key86, 24), (key3, 24), (key86, 24), (key86, 24), (key147, 24)]

theorem rawRowCheck18683 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form1 = rawRow18683 := by decide +kernel

def row18683 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18683 : row18683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18683 := by decide +kernel

theorem rowEval18683 (x : Key → ℝ) : Integer.Sparse.eval row18683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18683, Integer.Sparse.eval_collectBalanced, rawRowCheck18683]

def rawRow18684 : Integer.Sparse Key := [(key86, 24), (key3, 24), (key86, 24), (key147, 24), (key86, 24)]

theorem rawRowCheck18684 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form1 = rawRow18684 := by decide +kernel

def row18684 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18684 : row18684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18684 := by decide +kernel

theorem rowEval18684 (x : Key → ℝ) : Integer.Sparse.eval row18684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18684, Integer.Sparse.eval_collectBalanced, rawRowCheck18684]

def rawRow18685 : Integer.Sparse Key := [(key86, 24), (key3, 24), (key147, 24), (key86, 24), (key86, 24)]

theorem rawRowCheck18685 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form1 = rawRow18685 := by decide +kernel

def row18685 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18685 : row18685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18685 := by decide +kernel

theorem rowEval18685 (x : Key → ℝ) : Integer.Sparse.eval row18685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18685, Integer.Sparse.eval_collectBalanced, rawRowCheck18685]

def rawRow18686 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key3, 24), (key86, 24), (key147, 24)]

theorem rawRowCheck18686 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form1 = rawRow18686 := by decide +kernel

def row18686 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18686 : row18686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18686 := by decide +kernel

theorem rowEval18686 (x : Key → ℝ) : Integer.Sparse.eval row18686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18686, Integer.Sparse.eval_collectBalanced, rawRowCheck18686]

def rawRow18687 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key3, 24), (key147, 24), (key86, 24)]

theorem rawRowCheck18687 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form1 = rawRow18687 := by decide +kernel

def row18687 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18687 : row18687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18687 := by decide +kernel

theorem rowEval18687 (x : Key → ℝ) : Integer.Sparse.eval row18687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18687, Integer.Sparse.eval_collectBalanced, rawRowCheck18687]

end MUB6.Certificate.GramRows

end OAI
