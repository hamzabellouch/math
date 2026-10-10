import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
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

def rawRow736 : Integer.Sparse Key := [(key1539, -6), (key1566, 2), (key1615, 2), (key1680, 2), (key1309, 6), (key1417, -2), (key1615, -2), (key1917, -2), (key1289, -2), (key1309, -2), (key1350, -2), (key1384, 2), (key1539, 2), (key1895, 2)]

theorem rawRowCheck736 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form1 = rawRow736 := by decide +kernel

def row736 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

theorem rowCheck736 : row736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow736 := by decide +kernel

theorem rowEval736 (x : Key → ℝ) : Integer.Sparse.eval row736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck736, Integer.Sparse.eval_collectBalanced, rawRowCheck736]

def rawRow737 : Integer.Sparse Key := [(key1539, -6), (key1566, 2), (key1680, 2), (key1615, 2), (key1309, 6), (key1417, -2), (key1917, -2), (key1615, -2), (key1289, -2), (key1350, -2), (key1309, -2), (key1384, 2), (key1895, 2), (key1539, 2)]

theorem rawRowCheck737 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form1 = rawRow737 := by decide +kernel

def row737 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

theorem rowCheck737 : row737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow737 := by decide +kernel

theorem rowEval737 (x : Key → ℝ) : Integer.Sparse.eval row737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck737, Integer.Sparse.eval_collectBalanced, rawRowCheck737]

def rawRow738 : Integer.Sparse Key := [(key1539, -6), (key1615, 2), (key1566, 2), (key1680, 2), (key1309, 6), (key1615, -2), (key1417, -2), (key1917, -2), (key1309, -2), (key1289, -2), (key1350, -2), (key1539, 2), (key1384, 2), (key1895, 2)]

theorem rawRowCheck738 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form1 = rawRow738 := by decide +kernel

def row738 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

theorem rowCheck738 : row738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow738 := by decide +kernel

theorem rowEval738 (x : Key → ℝ) : Integer.Sparse.eval row738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck738, Integer.Sparse.eval_collectBalanced, rawRowCheck738]

def rawRow739 : Integer.Sparse Key := [(key1539, -6), (key1615, 2), (key1680, 2), (key1566, 2), (key1309, 6), (key1615, -2), (key1917, -2), (key1417, -2), (key1309, -2), (key1350, -2), (key1289, -2), (key1539, 2), (key1895, 2), (key1384, 2)]

theorem rawRowCheck739 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form1 = rawRow739 := by decide +kernel

def row739 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

theorem rowCheck739 : row739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow739 := by decide +kernel

theorem rowEval739 (x : Key → ℝ) : Integer.Sparse.eval row739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck739, Integer.Sparse.eval_collectBalanced, rawRowCheck739]

def rawRow740 : Integer.Sparse Key := [(key1539, -6), (key1680, 2), (key1566, 2), (key1615, 2), (key1309, 6), (key1917, -2), (key1417, -2), (key1615, -2), (key1350, -2), (key1289, -2), (key1309, -2), (key1895, 2), (key1384, 2), (key1539, 2)]

theorem rawRowCheck740 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form1 = rawRow740 := by decide +kernel

def row740 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

theorem rowCheck740 : row740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow740 := by decide +kernel

theorem rowEval740 (x : Key → ℝ) : Integer.Sparse.eval row740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck740, Integer.Sparse.eval_collectBalanced, rawRowCheck740]

def rawRow741 : Integer.Sparse Key := [(key1539, -6), (key1680, 2), (key1615, 2), (key1566, 2), (key1309, 6), (key1917, -2), (key1615, -2), (key1417, -2), (key1350, -2), (key1309, -2), (key1289, -2), (key1895, 2), (key1539, 2), (key1384, 2)]

theorem rawRowCheck741 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form1 = rawRow741 := by decide +kernel

def row741 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

theorem rowCheck741 : row741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow741 := by decide +kernel

theorem rowEval741 (x : Key → ℝ) : Integer.Sparse.eval row741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck741, Integer.Sparse.eval_collectBalanced, rawRowCheck741]

def rawRow742 : Integer.Sparse Key := [(key1566, -6), (key1539, 2), (key1615, 2), (key1680, 2), (key1417, 6), (key1309, -2), (key1615, -2), (key1917, -2), (key1384, -2), (key1417, -2), (key1471, -2), (key1289, 2), (key1566, 2), (key1902, 2)]

theorem rawRowCheck742 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form1 = rawRow742 := by decide +kernel

def row742 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

theorem rowCheck742 : row742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow742 := by decide +kernel

theorem rowEval742 (x : Key → ℝ) : Integer.Sparse.eval row742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck742, Integer.Sparse.eval_collectBalanced, rawRowCheck742]

def rawRow743 : Integer.Sparse Key := [(key1566, -6), (key1539, 2), (key1680, 2), (key1615, 2), (key1417, 6), (key1309, -2), (key1917, -2), (key1615, -2), (key1384, -2), (key1471, -2), (key1417, -2), (key1289, 2), (key1902, 2), (key1566, 2)]

theorem rawRowCheck743 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form1 = rawRow743 := by decide +kernel

def row743 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

theorem rowCheck743 : row743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow743 := by decide +kernel

theorem rowEval743 (x : Key → ℝ) : Integer.Sparse.eval row743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck743, Integer.Sparse.eval_collectBalanced, rawRowCheck743]

def rawRow744 : Integer.Sparse Key := [(key1566, -6), (key1615, 2), (key1539, 2), (key1680, 2), (key1417, 6), (key1615, -2), (key1309, -2), (key1917, -2), (key1417, -2), (key1384, -2), (key1471, -2), (key1566, 2), (key1289, 2), (key1902, 2)]

theorem rawRowCheck744 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form1 = rawRow744 := by decide +kernel

def row744 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

theorem rowCheck744 : row744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow744 := by decide +kernel

theorem rowEval744 (x : Key → ℝ) : Integer.Sparse.eval row744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck744, Integer.Sparse.eval_collectBalanced, rawRowCheck744]

def rawRow745 : Integer.Sparse Key := [(key1566, -6), (key1615, 2), (key1680, 2), (key1539, 2), (key1417, 6), (key1615, -2), (key1917, -2), (key1309, -2), (key1417, -2), (key1471, -2), (key1384, -2), (key1566, 2), (key1902, 2), (key1289, 2)]

theorem rawRowCheck745 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form1 = rawRow745 := by decide +kernel

def row745 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

theorem rowCheck745 : row745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow745 := by decide +kernel

theorem rowEval745 (x : Key → ℝ) : Integer.Sparse.eval row745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck745, Integer.Sparse.eval_collectBalanced, rawRowCheck745]

def rawRow746 : Integer.Sparse Key := [(key1566, -6), (key1680, 2), (key1539, 2), (key1615, 2), (key1417, 6), (key1917, -2), (key1309, -2), (key1615, -2), (key1471, -2), (key1384, -2), (key1417, -2), (key1902, 2), (key1289, 2), (key1566, 2)]

theorem rawRowCheck746 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form1 = rawRow746 := by decide +kernel

def row746 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

theorem rowCheck746 : row746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow746 := by decide +kernel

theorem rowEval746 (x : Key → ℝ) : Integer.Sparse.eval row746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck746, Integer.Sparse.eval_collectBalanced, rawRowCheck746]

def rawRow747 : Integer.Sparse Key := [(key1566, -6), (key1680, 2), (key1615, 2), (key1539, 2), (key1417, 6), (key1917, -2), (key1615, -2), (key1309, -2), (key1471, -2), (key1417, -2), (key1384, -2), (key1902, 2), (key1566, 2), (key1289, 2)]

theorem rawRowCheck747 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form1 = rawRow747 := by decide +kernel

def row747 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

theorem rowCheck747 : row747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow747 := by decide +kernel

theorem rowEval747 (x : Key → ℝ) : Integer.Sparse.eval row747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck747, Integer.Sparse.eval_collectBalanced, rawRowCheck747]

def rawRow748 : Integer.Sparse Key := [(key2608, -2), (key2614, -2), (key2614, -2), (key2624, 1), (key2630, 1), (key2624, 1), (key2638, 1), (key2630, 1), (key2638, 1), (key2663, 2), (key2669, 2), (key2669, 2), (key2698, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2778, -1), (key2784, -1), (key2778, -1), (key2792, -1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, 1), (key2801, 1), (key2827, 1), (key2807, 1), (key2827, 1)]

theorem rawRowCheck748 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form2 = rawRow748 := by decide +kernel

def row748 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 2), (key2807, 2), (key2827, 2)]

theorem rowCheck748 : row748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow748 := by decide +kernel

theorem rowEval748 (x : Key → ℝ) : Integer.Sparse.eval row748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck748, Integer.Sparse.eval_collectBalanced, rawRowCheck748]

def rawRow749 : Integer.Sparse Key := [(key2614, -2), (key2608, -2), (key2614, -2), (key2630, 1), (key2624, 1), (key2638, 1), (key2624, 1), (key2638, 1), (key2630, 1), (key2669, 2), (key2663, 2), (key2669, 2), (key2704, -1), (key2698, -1), (key2724, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2784, -1), (key2778, -1), (key2792, -1), (key2778, -1), (key2792, -1), (key2784, -1), (key2807, 1), (key2801, 1), (key2827, 1), (key2801, 1), (key2827, 1), (key2807, 1)]

theorem rawRowCheck749 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form2 = rawRow749 := by decide +kernel

def row749 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 2), (key2807, 2), (key2827, 2)]

theorem rowCheck749 : row749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow749 := by decide +kernel

theorem rowEval749 (x : Key → ℝ) : Integer.Sparse.eval row749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck749, Integer.Sparse.eval_collectBalanced, rawRowCheck749]

def rawRow750 : Integer.Sparse Key := [(key2614, -2), (key2614, -2), (key2608, -2), (key2638, 1), (key2638, 1), (key2630, 1), (key2630, 1), (key2624, 1), (key2624, 1), (key2669, 2), (key2669, 2), (key2663, 2), (key2724, -1), (key2724, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2792, -1), (key2792, -1), (key2784, -1), (key2784, -1), (key2778, -1), (key2778, -1), (key2827, 1), (key2827, 1), (key2807, 1), (key2807, 1), (key2801, 1), (key2801, 1)]

theorem rawRowCheck750 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form2 = rawRow750 := by decide +kernel

def row750 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 2), (key2807, 2), (key2827, 2)]

theorem rowCheck750 : row750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow750 := by decide +kernel

theorem rowEval750 (x : Key → ℝ) : Integer.Sparse.eval row750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck750, Integer.Sparse.eval_collectBalanced, rawRowCheck750]

def rawRow751 : Integer.Sparse Key := [(key2624, -2), (key2630, -2), (key2638, -2), (key2608, 1), (key2614, 1), (key2624, 1), (key2638, 1), (key2657, 1), (key2659, 1), (key2698, 2), (key2704, 2), (key2752, 2), (key2663, -1), (key2669, -1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, -1), (key2851, -1), (key2858, -1), (key2918, -1), (key2919, -1), (key2778, 1), (key2784, 1), (key2851, 1), (key2868, 1), (key2918, 1), (key2922, 1)]

theorem rawRowCheck751 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form2 = rawRow751 := by decide +kernel

def row751 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

theorem rowCheck751 : row751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow751 := by decide +kernel

theorem rowEval751 (x : Key → ℝ) : Integer.Sparse.eval row751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck751, Integer.Sparse.eval_collectBalanced, rawRowCheck751]

def rawRow752 : Integer.Sparse Key := [(key2630, -2), (key2624, -2), (key2638, -2), (key2614, 1), (key2608, 1), (key2638, 1), (key2624, 1), (key2659, 1), (key2657, 1), (key2704, 2), (key2698, 2), (key2752, 2), (key2669, -1), (key2663, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2752, -1), (key2807, -1), (key2801, -1), (key2858, -1), (key2851, -1), (key2919, -1), (key2918, -1), (key2784, 1), (key2778, 1), (key2868, 1), (key2851, 1), (key2922, 1), (key2918, 1)]

theorem rawRowCheck752 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form2 = rawRow752 := by decide +kernel

def row752 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

theorem rowCheck752 : row752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow752 := by decide +kernel

theorem rowEval752 (x : Key → ℝ) : Integer.Sparse.eval row752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck752, Integer.Sparse.eval_collectBalanced, rawRowCheck752]

def rawRow753 : Integer.Sparse Key := [(key2624, -2), (key2638, -2), (key2630, -2), (key2624, 1), (key2638, 1), (key2608, 1), (key2659, 1), (key2614, 1), (key2638, 1), (key2698, 2), (key2752, 2), (key2704, 2), (key2698, -1), (key2752, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2851, -1), (key2918, -1), (key2801, -1), (key2919, -1), (key2807, -1), (key2858, -1), (key2851, 1), (key2918, 1), (key2778, 1), (key2922, 1), (key2784, 1), (key2868, 1)]

theorem rawRowCheck753 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form2 = rawRow753 := by decide +kernel

def row753 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

theorem rowCheck753 : row753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow753 := by decide +kernel

theorem rowEval753 (x : Key → ℝ) : Integer.Sparse.eval row753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck753, Integer.Sparse.eval_collectBalanced, rawRowCheck753]

def rawRow754 : Integer.Sparse Key := [(key2638, -2), (key2624, -2), (key2630, -2), (key2638, 1), (key2624, 1), (key2659, 1), (key2608, 1), (key2638, 1), (key2614, 1), (key2752, 2), (key2698, 2), (key2704, 2), (key2752, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2724, -1), (key2669, -1), (key2918, -1), (key2851, -1), (key2919, -1), (key2801, -1), (key2858, -1), (key2807, -1), (key2918, 1), (key2851, 1), (key2922, 1), (key2778, 1), (key2868, 1), (key2784, 1)]

theorem rawRowCheck754 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form2 = rawRow754 := by decide +kernel

def row754 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

theorem rowCheck754 : row754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow754 := by decide +kernel

theorem rowEval754 (x : Key → ℝ) : Integer.Sparse.eval row754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck754, Integer.Sparse.eval_collectBalanced, rawRowCheck754]

def rawRow755 : Integer.Sparse Key := [(key2630, -2), (key2638, -2), (key2624, -2), (key2657, 1), (key2659, 1), (key2614, 1), (key2638, 1), (key2608, 1), (key2624, 1), (key2704, 2), (key2752, 2), (key2698, 2), (key2724, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2663, -1), (key2698, -1), (key2858, -1), (key2919, -1), (key2807, -1), (key2918, -1), (key2801, -1), (key2851, -1), (key2868, 1), (key2922, 1), (key2784, 1), (key2918, 1), (key2778, 1), (key2851, 1)]

theorem rawRowCheck755 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form2 = rawRow755 := by decide +kernel

def row755 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

theorem rowCheck755 : row755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow755 := by decide +kernel

theorem rowEval755 (x : Key → ℝ) : Integer.Sparse.eval row755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck755, Integer.Sparse.eval_collectBalanced, rawRowCheck755]

def rawRow756 : Integer.Sparse Key := [(key2638, -2), (key2630, -2), (key2624, -2), (key2659, 1), (key2657, 1), (key2638, 1), (key2614, 1), (key2624, 1), (key2608, 1), (key2752, 2), (key2704, 2), (key2698, 2), (key2757, -1), (key2724, -1), (key2752, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2919, -1), (key2858, -1), (key2918, -1), (key2807, -1), (key2851, -1), (key2801, -1), (key2922, 1), (key2868, 1), (key2918, 1), (key2784, 1), (key2851, 1), (key2778, 1)]

theorem rawRowCheck756 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form2 = rawRow756 := by decide +kernel

def row756 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

theorem rowCheck756 : row756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow756 := by decide +kernel

theorem rowEval756 (x : Key → ℝ) : Integer.Sparse.eval row756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck756, Integer.Sparse.eval_collectBalanced, rawRowCheck756]

def rawRow757 : Integer.Sparse Key := [(key2663, -2), (key2669, -2), (key2669, -2), (key2698, 1), (key2704, 1), (key2698, 1), (key2752, 1), (key2704, 1), (key2752, 1), (key2608, 2), (key2614, 2), (key2614, 2), (key2801, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key2624, -1), (key2630, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2638, -1), (key2698, 1), (key2704, 1), (key2698, 1), (key2724, 1), (key2704, 1), (key2724, 1)]

theorem rawRowCheck757 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form2 = rawRow757 := by decide +kernel

def row757 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, -4), (key2698, 4), (key2704, 4), (key2724, 2), (key2752, 2), (key2801, -2), (key2807, -2), (key2827, -2)]

theorem rowCheck757 : row757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow757 := by decide +kernel

theorem rowEval757 (x : Key → ℝ) : Integer.Sparse.eval row757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck757, Integer.Sparse.eval_collectBalanced, rawRowCheck757]

def rawRow758 : Integer.Sparse Key := [(key2669, -2), (key2663, -2), (key2669, -2), (key2704, 1), (key2698, 1), (key2752, 1), (key2698, 1), (key2752, 1), (key2704, 1), (key2614, 2), (key2608, 2), (key2614, 2), (key2807, -1), (key2801, -1), (key2827, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2630, -1), (key2624, -1), (key2638, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2704, 1), (key2698, 1), (key2724, 1), (key2698, 1), (key2724, 1), (key2704, 1)]

theorem rawRowCheck758 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form2 = rawRow758 := by decide +kernel

def row758 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, -4), (key2698, 4), (key2704, 4), (key2724, 2), (key2752, 2), (key2801, -2), (key2807, -2), (key2827, -2)]

theorem rowCheck758 : row758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow758 := by decide +kernel

theorem rowEval758 (x : Key → ℝ) : Integer.Sparse.eval row758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck758, Integer.Sparse.eval_collectBalanced, rawRowCheck758]

def rawRow759 : Integer.Sparse Key := [(key2669, -2), (key2669, -2), (key2663, -2), (key2752, 1), (key2752, 1), (key2704, 1), (key2704, 1), (key2698, 1), (key2698, 1), (key2614, 2), (key2614, 2), (key2608, 2), (key2827, -1), (key2827, -1), (key2807, -1), (key2807, -1), (key2801, -1), (key2801, -1), (key2638, -1), (key2638, -1), (key2630, -1), (key2630, -1), (key2624, -1), (key2624, -1), (key2724, 1), (key2724, 1), (key2704, 1), (key2704, 1), (key2698, 1), (key2698, 1)]

theorem rawRowCheck759 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form2 = rawRow759 := by decide +kernel

def row759 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, -4), (key2698, 4), (key2704, 4), (key2724, 2), (key2752, 2), (key2801, -2), (key2807, -2), (key2827, -2)]

theorem rowCheck759 : row759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow759 := by decide +kernel

theorem rowEval759 (x : Key → ℝ) : Integer.Sparse.eval row759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck759, Integer.Sparse.eval_collectBalanced, rawRowCheck759]

def rawRow760 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2663, 1), (key2669, 1), (key2698, 1), (key2752, 1), (key2724, 1), (key2757, 1), (key2801, 2), (key2807, 2), (key2827, 2), (key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2698, -1), (key2704, -1), (key2851, -1), (key2858, -1), (key3021, -1), (key3022, -1), (key2624, 1), (key2630, 1), (key2851, 1), (key2868, 1), (key3021, 1), (key3025, 1)]

theorem rawRowCheck760 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form2 = rawRow760 := by decide +kernel

def row760 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2827, 1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck760 : row760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow760 := by decide +kernel

theorem rowEval760 (x : Key → ℝ) : Integer.Sparse.eval row760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck760, Integer.Sparse.eval_collectBalanced, rawRowCheck760]

def rawRow761 : Integer.Sparse Key := [(key2704, -2), (key2698, -2), (key2724, -2), (key2669, 1), (key2663, 1), (key2752, 1), (key2698, 1), (key2757, 1), (key2724, 1), (key2807, 2), (key2801, 2), (key2827, 2), (key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2704, -1), (key2698, -1), (key2858, -1), (key2851, -1), (key3022, -1), (key3021, -1), (key2630, 1), (key2624, 1), (key2868, 1), (key2851, 1), (key3025, 1), (key3021, 1)]

theorem rawRowCheck761 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form2 = rawRow761 := by decide +kernel

def row761 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2827, 1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck761 : row761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow761 := by decide +kernel

theorem rowEval761 (x : Key → ℝ) : Integer.Sparse.eval row761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck761, Integer.Sparse.eval_collectBalanced, rawRowCheck761]

def rawRow762 : Integer.Sparse Key := [(key2698, -2), (key2724, -2), (key2704, -2), (key2698, 1), (key2724, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2801, 2), (key2827, 2), (key2807, 2), (key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2851, -1), (key3021, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2851, 1), (key3021, 1), (key2624, 1), (key3025, 1), (key2630, 1), (key2868, 1)]

theorem rawRowCheck762 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form2 = rawRow762 := by decide +kernel

def row762 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2858, -1), (key2868, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck762 : row762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow762 := by decide +kernel

theorem rowEval762 (x : Key → ℝ) : Integer.Sparse.eval row762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck762, Integer.Sparse.eval_collectBalanced, rawRowCheck762]

def rawRow763 : Integer.Sparse Key := [(key2724, -2), (key2698, -2), (key2704, -2), (key2724, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2752, 1), (key2669, 1), (key2827, 2), (key2801, 2), (key2807, 2), (key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key3021, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key2858, -1), (key2704, -1), (key3021, 1), (key2851, 1), (key3025, 1), (key2624, 1), (key2868, 1), (key2630, 1)]

theorem rawRowCheck763 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form2 = rawRow763 := by decide +kernel

def row763 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2858, -1), (key2868, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck763 : row763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow763 := by decide +kernel

theorem rowEval763 (x : Key → ℝ) : Integer.Sparse.eval row763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck763, Integer.Sparse.eval_collectBalanced, rawRowCheck763]

def rawRow764 : Integer.Sparse Key := [(key2704, -2), (key2724, -2), (key2698, -2), (key2752, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2663, 1), (key2698, 1), (key2807, 2), (key2827, 2), (key2801, 2), (key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2858, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2698, -1), (key2851, -1), (key2868, 1), (key3025, 1), (key2630, 1), (key3021, 1), (key2624, 1), (key2851, 1)]

theorem rawRowCheck764 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form2 = rawRow764 := by decide +kernel

def row764 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2827, 1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck764 : row764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow764 := by decide +kernel

theorem rowEval764 (x : Key → ℝ) : Integer.Sparse.eval row764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck764, Integer.Sparse.eval_collectBalanced, rawRowCheck764]

def rawRow765 : Integer.Sparse Key := [(key2724, -2), (key2704, -2), (key2698, -2), (key2757, 1), (key2752, 1), (key2724, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key2827, 2), (key2807, 2), (key2801, 2), (key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key3022, -1), (key2858, -1), (key3021, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key3025, 1), (key2868, 1), (key3021, 1), (key2630, 1), (key2851, 1), (key2624, 1)]

theorem rawRowCheck765 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form2 = rawRow765 := by decide +kernel

def row765 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2827, 1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

theorem rowCheck765 : row765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow765 := by decide +kernel

theorem rowEval765 (x : Key → ℝ) : Integer.Sparse.eval row765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck765, Integer.Sparse.eval_collectBalanced, rawRowCheck765]

def rawRow766 : Integer.Sparse Key := [(key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2851, 1), (key2918, 1), (key2858, 1), (key2919, 1), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, -1), (key2704, -1), (key2851, -1), (key3021, -1), (key2858, -1), (key3022, -1), (key2608, -1), (key2614, -1), (key2624, -1), (key2638, -1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2698, 1), (key2724, 1), (key2752, 1), (key2757, 1)]

theorem rawRowCheck766 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form2 = rawRow766 := by decide +kernel

def row766 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

theorem rowCheck766 : row766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow766 := by decide +kernel

theorem rowEval766 (x : Key → ℝ) : Integer.Sparse.eval row766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck766, Integer.Sparse.eval_collectBalanced, rawRowCheck766]

def rawRow767 : Integer.Sparse Key := [(key2784, -2), (key2778, -2), (key2792, -2), (key2807, 1), (key2801, 1), (key2918, 1), (key2851, 1), (key2919, 1), (key2858, 1), (key2630, 2), (key2624, 2), (key2638, 2), (key2704, -1), (key2698, -1), (key3021, -1), (key2851, -1), (key3022, -1), (key2858, -1), (key2614, -1), (key2608, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2657, -1), (key2669, 1), (key2663, 1), (key2724, 1), (key2698, 1), (key2757, 1), (key2752, 1)]

theorem rawRowCheck767 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form2 = rawRow767 := by decide +kernel

def row767 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

theorem rowCheck767 : row767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow767 := by decide +kernel

theorem rowEval767 (x : Key → ℝ) : Integer.Sparse.eval row767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck767, Integer.Sparse.eval_collectBalanced, rawRowCheck767]

end MUB6.Certificate.GramRows

end OAI
