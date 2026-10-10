import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14848 : Integer.Sparse Key := [(key2521, 4), (key2457, 4), (key2521, 4), (key2562, -2), (key2564, -2), (key2532, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2521, -2), (key2525, -2), (key2460, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2564, 4), (key2533, 4), (key2564, 4)]

theorem rawRowCheck14848 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form0 = rawRow14848 := by decide +kernel

def row14848 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

theorem rowCheck14848 : row14848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14848 := by decide +kernel

theorem rowEval14848 (x : Key → ℝ) : Integer.Sparse.eval row14848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14848, Integer.Sparse.eval_collectBalanced, rawRowCheck14848]

def rawRow14849 : Integer.Sparse Key := [(key2521, 4), (key2521, 4), (key2457, 4), (key2564, -2), (key2562, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2532, -2), (key2525, -2), (key2521, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2460, -2), (key2564, 4), (key2564, 4), (key2533, 4)]

theorem rawRowCheck14849 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form0 = rawRow14849 := by decide +kernel

def row14849 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

theorem rowCheck14849 : row14849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14849 := by decide +kernel

theorem rowEval14849 (x : Key → ℝ) : Integer.Sparse.eval row14849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14849, Integer.Sparse.eval_collectBalanced, rawRowCheck14849]

def rawRow14850 : Integer.Sparse Key := [(key2460, 4), (key2460, 4), (key2533, 4), (key2521, -2), (key2525, -2), (key2521, -2), (key2564, -2), (key2525, -2), (key2564, -2), (key2457, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2521, -2), (key2532, 4), (key2532, 4), (key2562, 4)]

theorem rawRowCheck14850 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form0 = rawRow14850 := by decide +kernel

def row14850 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -8), (key2525, -4), (key2532, 8), (key2533, 4), (key2562, 4), (key2564, -4)]

theorem rowCheck14850 : row14850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14850 := by decide +kernel

theorem rowEval14850 (x : Key → ℝ) : Integer.Sparse.eval row14850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14850, Integer.Sparse.eval_collectBalanced, rawRowCheck14850]

def rawRow14851 : Integer.Sparse Key := [(key2460, 4), (key2533, 4), (key2460, 4), (key2525, -2), (key2521, -2), (key2564, -2), (key2521, -2), (key2564, -2), (key2525, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2532, 4), (key2562, 4), (key2532, 4)]

theorem rawRowCheck14851 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form0 = rawRow14851 := by decide +kernel

def row14851 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -8), (key2525, -4), (key2532, 8), (key2533, 4), (key2562, 4), (key2564, -4)]

theorem rowCheck14851 : row14851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14851 := by decide +kernel

theorem rowEval14851 (x : Key → ℝ) : Integer.Sparse.eval row14851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14851, Integer.Sparse.eval_collectBalanced, rawRowCheck14851]

def rawRow14852 : Integer.Sparse Key := [(key2533, 4), (key2460, 4), (key2460, 4), (key2564, -2), (key2564, -2), (key2525, -2), (key2525, -2), (key2521, -2), (key2521, -2), (key2521, -2), (key2521, -2), (key2460, -2), (key2460, -2), (key2457, -2), (key2457, -2), (key2562, 4), (key2532, 4), (key2532, 4)]

theorem rawRowCheck14852 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form0 = rawRow14852 := by decide +kernel

def row14852 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -8), (key2525, -4), (key2532, 8), (key2533, 4), (key2562, 4), (key2564, -4)]

theorem rowCheck14852 : row14852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14852 := by decide +kernel

theorem rowEval14852 (x : Key → ℝ) : Integer.Sparse.eval row14852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14852, Integer.Sparse.eval_collectBalanced, rawRowCheck14852]

def rawRow14853 : Integer.Sparse Key := [(key976, -2), (key976, -2), (key984, -2), (key984, 6), (key1090, -2), (key1090, -2), (key1098, -2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1183, 2), (key1183, 2), (key1098, -2), (key1183, -2), (key1183, -2), (key1169, 6), (key1169, -2), (key1220, -2), (key1220, -2)]

theorem rawRowCheck14853 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form1 = rawRow14853 := by decide +kernel

def row14853 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

theorem rowCheck14853 : row14853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14853 := by decide +kernel

theorem rowEval14853 (x : Key → ℝ) : Integer.Sparse.eval row14853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14853, Integer.Sparse.eval_collectBalanced, rawRowCheck14853]

def rawRow14854 : Integer.Sparse Key := [(key976, -2), (key984, -2), (key976, -2), (key984, 6), (key1090, -2), (key1098, -2), (key1090, -2), (key1180, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1183, -2), (key1098, -2), (key1183, -2), (key1169, 6), (key1220, -2), (key1169, -2), (key1220, -2)]

theorem rawRowCheck14854 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form1 = rawRow14854 := by decide +kernel

def row14854 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

theorem rowCheck14854 : row14854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14854 := by decide +kernel

theorem rowEval14854 (x : Key → ℝ) : Integer.Sparse.eval row14854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14854, Integer.Sparse.eval_collectBalanced, rawRowCheck14854]

def rawRow14855 : Integer.Sparse Key := [(key984, -2), (key976, -2), (key976, -2), (key984, 6), (key1098, -2), (key1090, -2), (key1090, -2), (key1183, 2), (key1180, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1183, -2), (key1183, -2), (key1098, -2), (key1169, 6), (key1220, -2), (key1220, -2), (key1169, -2)]

theorem rawRowCheck14855 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form1 = rawRow14855 := by decide +kernel

def row14855 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

theorem rowCheck14855 : row14855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14855 := by decide +kernel

theorem rowEval14855 (x : Key → ℝ) : Integer.Sparse.eval row14855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14855, Integer.Sparse.eval_collectBalanced, rawRowCheck14855]

def rawRow14856 : Integer.Sparse Key := [(key976, -2), (key984, -2), (key984, -2), (key976, 6), (key1180, -2), (key1183, -2), (key1183, -2), (key1090, 2), (key1098, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key1090, -2), (key1090, -2), (key1180, -2), (key1220, 6), (key1169, -2), (key1169, -2), (key1220, -2)]

theorem rawRowCheck14856 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form1 = rawRow14856 := by decide +kernel

def row14856 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

theorem rowCheck14856 : row14856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14856 := by decide +kernel

theorem rowEval14856 (x : Key → ℝ) : Integer.Sparse.eval row14856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14856, Integer.Sparse.eval_collectBalanced, rawRowCheck14856]

def rawRow14857 : Integer.Sparse Key := [(key984, -2), (key976, -2), (key984, -2), (key976, 6), (key1183, -2), (key1180, -2), (key1183, -2), (key1098, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1090, -2), (key1180, -2), (key1090, -2), (key1220, 6), (key1169, -2), (key1220, -2), (key1169, -2)]

theorem rawRowCheck14857 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form1 = rawRow14857 := by decide +kernel

def row14857 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

theorem rowCheck14857 : row14857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14857 := by decide +kernel

theorem rowEval14857 (x : Key → ℝ) : Integer.Sparse.eval row14857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14857, Integer.Sparse.eval_collectBalanced, rawRowCheck14857]

def rawRow14858 : Integer.Sparse Key := [(key984, -2), (key984, -2), (key976, -2), (key976, 6), (key1183, -2), (key1183, -2), (key1180, -2), (key1183, 2), (key1183, 2), (key1098, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1180, -2), (key1090, -2), (key1090, -2), (key1220, 6), (key1220, -2), (key1169, -2), (key1169, -2)]

theorem rawRowCheck14858 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form1 = rawRow14858 := by decide +kernel

def row14858 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

theorem rowCheck14858 : row14858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14858 := by decide +kernel

theorem rowEval14858 (x : Key → ℝ) : Integer.Sparse.eval row14858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14858, Integer.Sparse.eval_collectBalanced, rawRowCheck14858]

def rawRow14859 : Integer.Sparse Key := [(key1090, -2), (key1090, -2), (key1098, -2), (key1169, 6), (key976, -2), (key976, -2), (key984, -2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1183, 2), (key1183, 2), (key1169, -2), (key1220, -2), (key1220, -2), (key984, 6), (key1098, -2), (key1183, -2), (key1183, -2)]

theorem rawRowCheck14859 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form1 = rawRow14859 := by decide +kernel

def row14859 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

theorem rowCheck14859 : row14859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14859 := by decide +kernel

theorem rowEval14859 (x : Key → ℝ) : Integer.Sparse.eval row14859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14859, Integer.Sparse.eval_collectBalanced, rawRowCheck14859]

def rawRow14860 : Integer.Sparse Key := [(key1090, -2), (key1098, -2), (key1090, -2), (key1169, 6), (key976, -2), (key984, -2), (key976, -2), (key1180, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1220, -2), (key1169, -2), (key1220, -2), (key984, 6), (key1183, -2), (key1098, -2), (key1183, -2)]

theorem rawRowCheck14860 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form1 = rawRow14860 := by decide +kernel

def row14860 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

theorem rowCheck14860 : row14860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14860 := by decide +kernel

theorem rowEval14860 (x : Key → ℝ) : Integer.Sparse.eval row14860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14860, Integer.Sparse.eval_collectBalanced, rawRowCheck14860]

def rawRow14861 : Integer.Sparse Key := [(key1098, -2), (key1090, -2), (key1090, -2), (key1169, 6), (key984, -2), (key976, -2), (key976, -2), (key1183, 2), (key1180, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1220, -2), (key1220, -2), (key1169, -2), (key984, 6), (key1183, -2), (key1183, -2), (key1098, -2)]

theorem rawRowCheck14861 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form1 = rawRow14861 := by decide +kernel

def row14861 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

theorem rowCheck14861 : row14861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14861 := by decide +kernel

theorem rowEval14861 (x : Key → ℝ) : Integer.Sparse.eval row14861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14861, Integer.Sparse.eval_collectBalanced, rawRowCheck14861]

def rawRow14862 : Integer.Sparse Key := [(key1090, -2), (key1098, -2), (key1169, -2), (key1090, 6), (key1180, -2), (key1183, -2), (key1220, -2), (key976, 2), (key984, 2), (key1090, 2), (key1183, 2), (key1169, 2), (key1220, 2), (key976, -2), (key1090, -2), (key1180, -2), (key1183, 6), (key984, -2), (key1098, -2), (key1183, -2)]

theorem rawRowCheck14862 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form1 = rawRow14862 := by decide +kernel

def row14862 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck14862 : row14862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14862 := by decide +kernel

theorem rowEval14862 (x : Key → ℝ) : Integer.Sparse.eval row14862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14862, Integer.Sparse.eval_collectBalanced, rawRowCheck14862]

def rawRow14863 : Integer.Sparse Key := [(key1098, -2), (key1090, -2), (key1169, -2), (key1090, 6), (key1183, -2), (key1180, -2), (key1220, -2), (key984, 2), (key976, 2), (key1183, 2), (key1090, 2), (key1220, 2), (key1169, 2), (key976, -2), (key1180, -2), (key1090, -2), (key1183, 6), (key984, -2), (key1183, -2), (key1098, -2)]

theorem rawRowCheck14863 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form1 = rawRow14863 := by decide +kernel

def row14863 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck14863 : row14863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14863 := by decide +kernel

theorem rowEval14863 (x : Key → ℝ) : Integer.Sparse.eval row14863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14863, Integer.Sparse.eval_collectBalanced, rawRowCheck14863]

def rawRow14864 : Integer.Sparse Key := [(key1090, -2), (key1169, -2), (key1098, -2), (key1090, 6), (key1180, -2), (key1220, -2), (key1183, -2), (key1090, 2), (key1169, 2), (key976, 2), (key1220, 2), (key984, 2), (key1183, 2), (key1090, -2), (key976, -2), (key1180, -2), (key1183, 6), (key1098, -2), (key984, -2), (key1183, -2)]

theorem rawRowCheck14864 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form1 = rawRow14864 := by decide +kernel

def row14864 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck14864 : row14864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14864 := by decide +kernel

theorem rowEval14864 (x : Key → ℝ) : Integer.Sparse.eval row14864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14864, Integer.Sparse.eval_collectBalanced, rawRowCheck14864]

def rawRow14865 : Integer.Sparse Key := [(key1169, -2), (key1090, -2), (key1098, -2), (key1090, 6), (key1220, -2), (key1180, -2), (key1183, -2), (key1169, 2), (key1090, 2), (key1220, 2), (key976, 2), (key1183, 2), (key984, 2), (key1090, -2), (key1180, -2), (key976, -2), (key1183, 6), (key1098, -2), (key1183, -2), (key984, -2)]

theorem rawRowCheck14865 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form1 = rawRow14865 := by decide +kernel

def row14865 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck14865 : row14865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14865 := by decide +kernel

theorem rowEval14865 (x : Key → ℝ) : Integer.Sparse.eval row14865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck14865, Integer.Sparse.eval_collectBalanced, rawRowCheck14865]

def rawRow14866 : Integer.Sparse Key := [(key1098, -2), (key1169, -2), (key1090, -2), (key1090, 6), (key1183, -2), (key1220, -2), (key1180, -2), (key1183, 2), (key1220, 2), (key984, 2), (key1169, 2), (key976, 2), (key1090, 2), (key1180, -2), (key976, -2), (key1090, -2), (key1183, 6), (key1183, -2), (key984, -2), (key1098, -2)]

theorem rawRowCheck14866 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form1 = rawRow14866 := by decide +kernel

def row14866 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck14866 : row14866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14866 := by decide +kernel

theorem rowEval14866 (x : Key → ℝ) : Integer.Sparse.eval row14866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14866, Integer.Sparse.eval_collectBalanced, rawRowCheck14866]

def rawRow14867 : Integer.Sparse Key := [(key1169, -2), (key1098, -2), (key1090, -2), (key1090, 6), (key1220, -2), (key1183, -2), (key1180, -2), (key1220, 2), (key1183, 2), (key1169, 2), (key984, 2), (key1090, 2), (key976, 2), (key1180, -2), (key1090, -2), (key976, -2), (key1183, 6), (key1183, -2), (key1098, -2), (key984, -2)]

theorem rawRowCheck14867 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form1 = rawRow14867 := by decide +kernel

def row14867 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck14867 : row14867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14867 := by decide +kernel

theorem rowEval14867 (x : Key → ℝ) : Integer.Sparse.eval row14867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck14867, Integer.Sparse.eval_collectBalanced, rawRowCheck14867]

def rawRow14868 : Integer.Sparse Key := [(key1180, -2), (key1183, -2), (key1183, -2), (key1220, 6), (key976, -2), (key984, -2), (key984, -2), (key1090, 2), (key1098, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key1169, -2), (key1169, -2), (key1220, -2), (key976, 6), (key1090, -2), (key1090, -2), (key1180, -2)]

theorem rawRowCheck14868 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form1 = rawRow14868 := by decide +kernel

def row14868 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

theorem rowCheck14868 : row14868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14868 := by decide +kernel

theorem rowEval14868 (x : Key → ℝ) : Integer.Sparse.eval row14868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14868, Integer.Sparse.eval_collectBalanced, rawRowCheck14868]

def rawRow14869 : Integer.Sparse Key := [(key1183, -2), (key1180, -2), (key1183, -2), (key1220, 6), (key984, -2), (key976, -2), (key984, -2), (key1098, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1169, -2), (key1220, -2), (key1169, -2), (key976, 6), (key1090, -2), (key1180, -2), (key1090, -2)]

theorem rawRowCheck14869 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form1 = rawRow14869 := by decide +kernel

def row14869 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

theorem rowCheck14869 : row14869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14869 := by decide +kernel

theorem rowEval14869 (x : Key → ℝ) : Integer.Sparse.eval row14869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14869, Integer.Sparse.eval_collectBalanced, rawRowCheck14869]

def rawRow14870 : Integer.Sparse Key := [(key1183, -2), (key1183, -2), (key1180, -2), (key1220, 6), (key984, -2), (key984, -2), (key976, -2), (key1183, 2), (key1183, 2), (key1098, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1220, -2), (key1169, -2), (key1169, -2), (key976, 6), (key1180, -2), (key1090, -2), (key1090, -2)]

theorem rawRowCheck14870 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form1 = rawRow14870 := by decide +kernel

def row14870 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

theorem rowCheck14870 : row14870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14870 := by decide +kernel

theorem rowEval14870 (x : Key → ℝ) : Integer.Sparse.eval row14870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14870, Integer.Sparse.eval_collectBalanced, rawRowCheck14870]

def rawRow14871 : Integer.Sparse Key := [(key1180, -2), (key1183, -2), (key1220, -2), (key1183, 6), (key1090, -2), (key1098, -2), (key1169, -2), (key976, 2), (key984, 2), (key1090, 2), (key1183, 2), (key1169, 2), (key1220, 2), (key984, -2), (key1098, -2), (key1183, -2), (key1090, 6), (key976, -2), (key1090, -2), (key1180, -2)]

theorem rawRowCheck14871 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form1 = rawRow14871 := by decide +kernel

def row14871 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck14871 : row14871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14871 := by decide +kernel

theorem rowEval14871 (x : Key → ℝ) : Integer.Sparse.eval row14871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14871, Integer.Sparse.eval_collectBalanced, rawRowCheck14871]

def rawRow14872 : Integer.Sparse Key := [(key1183, -2), (key1180, -2), (key1220, -2), (key1183, 6), (key1098, -2), (key1090, -2), (key1169, -2), (key984, 2), (key976, 2), (key1183, 2), (key1090, 2), (key1220, 2), (key1169, 2), (key984, -2), (key1183, -2), (key1098, -2), (key1090, 6), (key976, -2), (key1180, -2), (key1090, -2)]

theorem rawRowCheck14872 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form1 = rawRow14872 := by decide +kernel

def row14872 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck14872 : row14872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14872 := by decide +kernel

theorem rowEval14872 (x : Key → ℝ) : Integer.Sparse.eval row14872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14872, Integer.Sparse.eval_collectBalanced, rawRowCheck14872]

def rawRow14873 : Integer.Sparse Key := [(key1180, -2), (key1220, -2), (key1183, -2), (key1183, 6), (key1090, -2), (key1169, -2), (key1098, -2), (key1090, 2), (key1169, 2), (key976, 2), (key1220, 2), (key984, 2), (key1183, 2), (key1098, -2), (key984, -2), (key1183, -2), (key1090, 6), (key1090, -2), (key976, -2), (key1180, -2)]

theorem rawRowCheck14873 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form1 = rawRow14873 := by decide +kernel

def row14873 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck14873 : row14873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14873 := by decide +kernel

theorem rowEval14873 (x : Key → ℝ) : Integer.Sparse.eval row14873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14873, Integer.Sparse.eval_collectBalanced, rawRowCheck14873]

def rawRow14874 : Integer.Sparse Key := [(key1220, -2), (key1180, -2), (key1183, -2), (key1183, 6), (key1169, -2), (key1090, -2), (key1098, -2), (key1169, 2), (key1090, 2), (key1220, 2), (key976, 2), (key1183, 2), (key984, 2), (key1098, -2), (key1183, -2), (key984, -2), (key1090, 6), (key1090, -2), (key1180, -2), (key976, -2)]

theorem rawRowCheck14874 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form1 = rawRow14874 := by decide +kernel

def row14874 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck14874 : row14874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14874 := by decide +kernel

theorem rowEval14874 (x : Key → ℝ) : Integer.Sparse.eval row14874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck14874, Integer.Sparse.eval_collectBalanced, rawRowCheck14874]

def rawRow14875 : Integer.Sparse Key := [(key1183, -2), (key1220, -2), (key1180, -2), (key1183, 6), (key1098, -2), (key1169, -2), (key1090, -2), (key1183, 2), (key1220, 2), (key984, 2), (key1169, 2), (key976, 2), (key1090, 2), (key1183, -2), (key984, -2), (key1098, -2), (key1090, 6), (key1180, -2), (key976, -2), (key1090, -2)]

theorem rawRowCheck14875 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form1 = rawRow14875 := by decide +kernel

def row14875 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck14875 : row14875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14875 := by decide +kernel

theorem rowEval14875 (x : Key → ℝ) : Integer.Sparse.eval row14875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14875, Integer.Sparse.eval_collectBalanced, rawRowCheck14875]

def rawRow14876 : Integer.Sparse Key := [(key1220, -2), (key1183, -2), (key1180, -2), (key1183, 6), (key1169, -2), (key1098, -2), (key1090, -2), (key1220, 2), (key1183, 2), (key1169, 2), (key984, 2), (key1090, 2), (key976, 2), (key1183, -2), (key1098, -2), (key984, -2), (key1090, 6), (key1180, -2), (key1090, -2), (key976, -2)]

theorem rawRowCheck14876 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form1 = rawRow14876 := by decide +kernel

def row14876 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck14876 : row14876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14876 := by decide +kernel

theorem rowEval14876 (x : Key → ℝ) : Integer.Sparse.eval row14876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck14876, Integer.Sparse.eval_collectBalanced, rawRowCheck14876]

def rawRow14877 : Integer.Sparse Key := [(key1183, -2), (key1183, -2), (key1220, -2), (key1180, 6), (key1183, -2), (key1183, -2), (key1220, -2), (key984, 2), (key984, 2), (key1098, 2), (key1098, 2), (key1169, 2), (key1169, 2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, 6), (key976, -2), (key1090, -2), (key1090, -2)]

theorem rawRowCheck14877 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form1 = rawRow14877 := by decide +kernel

def row14877 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, -8), (key1098, 4), (key1169, 4), (key1180, 12), (key1183, -8), (key1220, -4)]

theorem rowCheck14877 : row14877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14877 := by decide +kernel

theorem rowEval14877 (x : Key → ℝ) : Integer.Sparse.eval row14877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14877, Integer.Sparse.eval_collectBalanced, rawRowCheck14877]

def rawRow14878 : Integer.Sparse Key := [(key1183, -2), (key1220, -2), (key1183, -2), (key1180, 6), (key1183, -2), (key1220, -2), (key1183, -2), (key1098, 2), (key1169, 2), (key984, 2), (key1169, 2), (key984, 2), (key1098, 2), (key1090, -2), (key976, -2), (key1090, -2), (key1180, 6), (key1090, -2), (key976, -2), (key1090, -2)]

theorem rawRowCheck14878 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form1 = rawRow14878 := by decide +kernel

def row14878 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, -8), (key1098, 4), (key1169, 4), (key1180, 12), (key1183, -8), (key1220, -4)]

theorem rowCheck14878 : row14878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14878 := by decide +kernel

theorem rowEval14878 (x : Key → ℝ) : Integer.Sparse.eval row14878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14878, Integer.Sparse.eval_collectBalanced, rawRowCheck14878]

def rawRow14879 : Integer.Sparse Key := [(key1220, -2), (key1183, -2), (key1183, -2), (key1180, 6), (key1220, -2), (key1183, -2), (key1183, -2), (key1169, 2), (key1098, 2), (key1169, 2), (key984, 2), (key1098, 2), (key984, 2), (key1090, -2), (key1090, -2), (key976, -2), (key1180, 6), (key1090, -2), (key1090, -2), (key976, -2)]

theorem rawRowCheck14879 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form1 = rawRow14879 := by decide +kernel

def row14879 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, -8), (key1098, 4), (key1169, 4), (key1180, 12), (key1183, -8), (key1220, -4)]

theorem rowCheck14879 : row14879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14879 := by decide +kernel

theorem rowEval14879 (x : Key → ℝ) : Integer.Sparse.eval row14879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck14879, Integer.Sparse.eval_collectBalanced, rawRowCheck14879]

def rawRow14880 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2366, -2), (key2366, 6), (key2456, -2), (key2456, -2), (key2461, -2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2523, 2), (key2523, 2), (key2461, -2), (key2523, -2), (key2523, -2), (key2567, 6), (key2567, -2), (key2579, -2), (key2579, -2)]

theorem rawRowCheck14880 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form2 = rawRow14880 := by decide +kernel

def row14880 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2366, 4), (key2461, -4), (key2517, 4), (key2567, 4), (key2579, -4)]

theorem rowCheck14880 : row14880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14880 := by decide +kernel

theorem rowEval14880 (x : Key → ℝ) : Integer.Sparse.eval row14880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14880, Integer.Sparse.eval_collectBalanced, rawRowCheck14880]

def rawRow14881 : Integer.Sparse Key := [(key2357, -2), (key2363, -2), (key2361, -2), (key2366, 6), (key2456, -2), (key2461, -2), (key2456, -2), (key2517, 2), (key2523, 2), (key2456, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2523, -2), (key2461, -2), (key2523, -2), (key2567, 6), (key2579, -2), (key2567, -2), (key2579, -2)]

theorem rawRowCheck14881 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form2 = rawRow14881 := by decide +kernel

def row14881 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2461, -4), (key2517, 4), (key2567, 4), (key2579, -4)]

theorem rowCheck14881 : row14881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14881 := by decide +kernel

theorem rowEval14881 (x : Key → ℝ) : Integer.Sparse.eval row14881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14881, Integer.Sparse.eval_collectBalanced, rawRowCheck14881]

def rawRow14882 : Integer.Sparse Key := [(key2363, -2), (key2357, -2), (key2361, -2), (key2366, 6), (key2461, -2), (key2456, -2), (key2456, -2), (key2523, 2), (key2517, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2523, -2), (key2523, -2), (key2461, -2), (key2567, 6), (key2579, -2), (key2579, -2), (key2567, -2)]

theorem rawRowCheck14882 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form2 = rawRow14882 := by decide +kernel

def row14882 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2461, -4), (key2517, 4), (key2567, 4), (key2579, -4)]

theorem rowCheck14882 : row14882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14882 := by decide +kernel

theorem rowEval14882 (x : Key → ℝ) : Integer.Sparse.eval row14882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14882, Integer.Sparse.eval_collectBalanced, rawRowCheck14882]

def rawRow14883 : Integer.Sparse Key := [(key2357, -2), (key2363, -2), (key2363, -2), (key2361, 6), (key2517, -2), (key2523, -2), (key2523, -2), (key2456, 2), (key2461, 2), (key2456, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2579, 6), (key2567, -2), (key2567, -2), (key2579, -2)]

theorem rawRowCheck14883 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form2 = rawRow14883 := by decide +kernel

def row14883 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2461, 4), (key2517, -4), (key2567, -4), (key2579, 4)]

theorem rowCheck14883 : row14883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14883 := by decide +kernel

theorem rowEval14883 (x : Key → ℝ) : Integer.Sparse.eval row14883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14883, Integer.Sparse.eval_collectBalanced, rawRowCheck14883]

def rawRow14884 : Integer.Sparse Key := [(key2363, -2), (key2357, -2), (key2363, -2), (key2361, 6), (key2523, -2), (key2517, -2), (key2523, -2), (key2461, 2), (key2456, 2), (key2523, 2), (key2456, 2), (key2523, 2), (key2461, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2579, 6), (key2567, -2), (key2579, -2), (key2567, -2)]

theorem rawRowCheck14884 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form2 = rawRow14884 := by decide +kernel

def row14884 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2461, 4), (key2517, -4), (key2567, -4), (key2579, 4)]

theorem rowCheck14884 : row14884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14884 := by decide +kernel

theorem rowEval14884 (x : Key → ℝ) : Integer.Sparse.eval row14884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14884, Integer.Sparse.eval_collectBalanced, rawRowCheck14884]

def rawRow14885 : Integer.Sparse Key := [(key2363, -2), (key2363, -2), (key2357, -2), (key2361, 6), (key2523, -2), (key2523, -2), (key2517, -2), (key2523, 2), (key2523, 2), (key2461, 2), (key2461, 2), (key2456, 2), (key2456, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2579, 6), (key2579, -2), (key2567, -2), (key2567, -2)]

theorem rawRowCheck14885 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form2 = rawRow14885 := by decide +kernel

def row14885 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2461, 4), (key2517, -4), (key2567, -4), (key2579, 4)]

theorem rowCheck14885 : row14885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14885 := by decide +kernel

theorem rowEval14885 (x : Key → ℝ) : Integer.Sparse.eval row14885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14885, Integer.Sparse.eval_collectBalanced, rawRowCheck14885]

def rawRow14886 : Integer.Sparse Key := [(key2452, -2), (key2452, -2), (key2458, -2), (key2519, 6), (key2357, -2), (key2361, -2), (key2366, -2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2523, 2), (key2523, 2), (key2567, -2), (key2579, -2), (key2579, -2), (key2366, 6), (key2461, -2), (key2523, -2), (key2523, -2)]

theorem rawRowCheck14886 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form2 = rawRow14886 := by decide +kernel

def row14886 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2366, 4), (key2452, -4), (key2456, 4), (key2458, -2), (key2461, -2), (key2517, 4), (key2519, 6), (key2567, -2), (key2579, -4)]

theorem rowCheck14886 : row14886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14886 := by decide +kernel

theorem rowEval14886 (x : Key → ℝ) : Integer.Sparse.eval row14886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14886, Integer.Sparse.eval_collectBalanced, rawRowCheck14886]

def rawRow14887 : Integer.Sparse Key := [(key2452, -2), (key2458, -2), (key2452, -2), (key2519, 6), (key2357, -2), (key2363, -2), (key2361, -2), (key2517, 2), (key2523, 2), (key2456, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2579, -2), (key2567, -2), (key2579, -2), (key2366, 6), (key2523, -2), (key2461, -2), (key2523, -2)]

theorem rawRowCheck14887 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form2 = rawRow14887 := by decide +kernel

def row14887 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2452, -4), (key2456, 4), (key2458, -2), (key2461, -2), (key2517, 4), (key2519, 6), (key2567, -2), (key2579, -4)]

theorem rowCheck14887 : row14887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14887 := by decide +kernel

theorem rowEval14887 (x : Key → ℝ) : Integer.Sparse.eval row14887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14887, Integer.Sparse.eval_collectBalanced, rawRowCheck14887]

def rawRow14888 : Integer.Sparse Key := [(key2458, -2), (key2452, -2), (key2452, -2), (key2519, 6), (key2363, -2), (key2357, -2), (key2361, -2), (key2523, 2), (key2517, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2579, -2), (key2579, -2), (key2567, -2), (key2366, 6), (key2523, -2), (key2523, -2), (key2461, -2)]

theorem rawRowCheck14888 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form2 = rawRow14888 := by decide +kernel

def row14888 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2452, -4), (key2456, 4), (key2458, -2), (key2461, -2), (key2517, 4), (key2519, 6), (key2567, -2), (key2579, -4)]

theorem rowCheck14888 : row14888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14888 := by decide +kernel

theorem rowEval14888 (x : Key → ℝ) : Integer.Sparse.eval row14888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14888, Integer.Sparse.eval_collectBalanced, rawRowCheck14888]

def rawRow14889 : Integer.Sparse Key := [(key2452, -2), (key2458, -2), (key2519, -2), (key2452, 6), (key2528, -2), (key2530, -2), (key2560, -2), (key2357, 2), (key2363, 2), (key2452, 2), (key2530, 2), (key2519, 2), (key2560, 2), (key2361, -2), (key2456, -2), (key2517, -2), (key2523, 6), (key2366, -2), (key2461, -2), (key2523, -2)]

theorem rawRowCheck14889 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form2 = rawRow14889 := by decide +kernel

def row14889 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

theorem rowCheck14889 : row14889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14889 := by decide +kernel

theorem rowEval14889 (x : Key → ℝ) : Integer.Sparse.eval row14889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14889, Integer.Sparse.eval_collectBalanced, rawRowCheck14889]

def rawRow14890 : Integer.Sparse Key := [(key2458, -2), (key2452, -2), (key2519, -2), (key2452, 6), (key2530, -2), (key2528, -2), (key2560, -2), (key2363, 2), (key2357, 2), (key2530, 2), (key2452, 2), (key2560, 2), (key2519, 2), (key2361, -2), (key2517, -2), (key2456, -2), (key2523, 6), (key2366, -2), (key2523, -2), (key2461, -2)]

theorem rawRowCheck14890 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form2 = rawRow14890 := by decide +kernel

def row14890 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

theorem rowCheck14890 : row14890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14890 := by decide +kernel

theorem rowEval14890 (x : Key → ℝ) : Integer.Sparse.eval row14890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14890, Integer.Sparse.eval_collectBalanced, rawRowCheck14890]

def rawRow14891 : Integer.Sparse Key := [(key2452, -2), (key2519, -2), (key2458, -2), (key2452, 6), (key2528, -2), (key2560, -2), (key2530, -2), (key2452, 2), (key2519, 2), (key2357, 2), (key2560, 2), (key2363, 2), (key2530, 2), (key2456, -2), (key2361, -2), (key2517, -2), (key2523, 6), (key2461, -2), (key2366, -2), (key2523, -2)]

theorem rawRowCheck14891 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form2 = rawRow14891 := by decide +kernel

def row14891 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

theorem rowCheck14891 : row14891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14891 := by decide +kernel

theorem rowEval14891 (x : Key → ℝ) : Integer.Sparse.eval row14891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14891, Integer.Sparse.eval_collectBalanced, rawRowCheck14891]

def rawRow14892 : Integer.Sparse Key := [(key2519, -2), (key2452, -2), (key2458, -2), (key2452, 6), (key2560, -2), (key2528, -2), (key2530, -2), (key2519, 2), (key2452, 2), (key2560, 2), (key2357, 2), (key2530, 2), (key2363, 2), (key2456, -2), (key2517, -2), (key2361, -2), (key2523, 6), (key2461, -2), (key2523, -2), (key2366, -2)]

theorem rawRowCheck14892 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form2 = rawRow14892 := by decide +kernel

def row14892 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

theorem rowCheck14892 : row14892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14892 := by decide +kernel

theorem rowEval14892 (x : Key → ℝ) : Integer.Sparse.eval row14892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck14892, Integer.Sparse.eval_collectBalanced, rawRowCheck14892]

def rawRow14893 : Integer.Sparse Key := [(key2458, -2), (key2519, -2), (key2452, -2), (key2452, 6), (key2530, -2), (key2560, -2), (key2528, -2), (key2530, 2), (key2560, 2), (key2363, 2), (key2519, 2), (key2357, 2), (key2452, 2), (key2517, -2), (key2361, -2), (key2456, -2), (key2523, 6), (key2523, -2), (key2366, -2), (key2461, -2)]

theorem rawRowCheck14893 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form2 = rawRow14893 := by decide +kernel

def row14893 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

theorem rowCheck14893 : row14893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14893 := by decide +kernel

theorem rowEval14893 (x : Key → ℝ) : Integer.Sparse.eval row14893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14893, Integer.Sparse.eval_collectBalanced, rawRowCheck14893]

def rawRow14894 : Integer.Sparse Key := [(key2519, -2), (key2458, -2), (key2452, -2), (key2452, 6), (key2560, -2), (key2530, -2), (key2528, -2), (key2560, 2), (key2530, 2), (key2519, 2), (key2363, 2), (key2452, 2), (key2357, 2), (key2517, -2), (key2456, -2), (key2361, -2), (key2523, 6), (key2523, -2), (key2461, -2), (key2366, -2)]

theorem rawRowCheck14894 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form2 = rawRow14894 := by decide +kernel

def row14894 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

theorem rowCheck14894 : row14894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14894 := by decide +kernel

theorem rowEval14894 (x : Key → ℝ) : Integer.Sparse.eval row14894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck14894, Integer.Sparse.eval_collectBalanced, rawRowCheck14894]

def rawRow14895 : Integer.Sparse Key := [(key2528, -2), (key2530, -2), (key2530, -2), (key2560, 6), (key2357, -2), (key2363, -2), (key2363, -2), (key2452, 2), (key2458, 2), (key2452, 2), (key2530, 2), (key2458, 2), (key2530, 2), (key2519, -2), (key2519, -2), (key2560, -2), (key2361, 6), (key2456, -2), (key2456, -2), (key2517, -2)]

theorem rawRowCheck14895 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form2 = rawRow14895 := by decide +kernel

def row14895 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2452, 4), (key2456, -4), (key2458, 4), (key2517, -2), (key2519, -4), (key2528, -2), (key2560, 4)]

theorem rowCheck14895 : row14895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14895 := by decide +kernel

theorem rowEval14895 (x : Key → ℝ) : Integer.Sparse.eval row14895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14895, Integer.Sparse.eval_collectBalanced, rawRowCheck14895]

def rawRow14896 : Integer.Sparse Key := [(key2530, -2), (key2528, -2), (key2530, -2), (key2560, 6), (key2363, -2), (key2357, -2), (key2363, -2), (key2458, 2), (key2452, 2), (key2530, 2), (key2452, 2), (key2530, 2), (key2458, 2), (key2519, -2), (key2560, -2), (key2519, -2), (key2361, 6), (key2456, -2), (key2517, -2), (key2456, -2)]

theorem rawRowCheck14896 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form2 = rawRow14896 := by decide +kernel

def row14896 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2452, 4), (key2456, -4), (key2458, 4), (key2517, -2), (key2519, -4), (key2528, -2), (key2560, 4)]

theorem rowCheck14896 : row14896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14896 := by decide +kernel

theorem rowEval14896 (x : Key → ℝ) : Integer.Sparse.eval row14896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14896, Integer.Sparse.eval_collectBalanced, rawRowCheck14896]

def rawRow14897 : Integer.Sparse Key := [(key2530, -2), (key2530, -2), (key2528, -2), (key2560, 6), (key2363, -2), (key2363, -2), (key2357, -2), (key2530, 2), (key2530, 2), (key2458, 2), (key2458, 2), (key2452, 2), (key2452, 2), (key2560, -2), (key2519, -2), (key2519, -2), (key2361, 6), (key2517, -2), (key2456, -2), (key2456, -2)]

theorem rawRowCheck14897 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form2 = rawRow14897 := by decide +kernel

def row14897 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2452, 4), (key2456, -4), (key2458, 4), (key2517, -2), (key2519, -4), (key2528, -2), (key2560, 4)]

theorem rowCheck14897 : row14897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14897 := by decide +kernel

theorem rowEval14897 (x : Key → ℝ) : Integer.Sparse.eval row14897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14897, Integer.Sparse.eval_collectBalanced, rawRowCheck14897]

def rawRow14898 : Integer.Sparse Key := [(key2528, -2), (key2530, -2), (key2560, -2), (key2530, 6), (key2452, -2), (key2458, -2), (key2519, -2), (key2357, 2), (key2363, 2), (key2452, 2), (key2530, 2), (key2519, 2), (key2560, 2), (key2363, -2), (key2458, -2), (key2530, -2), (key2456, 6), (key2361, -2), (key2456, -2), (key2517, -2)]

theorem rawRowCheck14898 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form2 = rawRow14898 := by decide +kernel

def row14898 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

theorem rowCheck14898 : row14898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14898 := by decide +kernel

theorem rowEval14898 (x : Key → ℝ) : Integer.Sparse.eval row14898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14898, Integer.Sparse.eval_collectBalanced, rawRowCheck14898]

def rawRow14899 : Integer.Sparse Key := [(key2530, -2), (key2528, -2), (key2560, -2), (key2530, 6), (key2458, -2), (key2452, -2), (key2519, -2), (key2363, 2), (key2357, 2), (key2530, 2), (key2452, 2), (key2560, 2), (key2519, 2), (key2363, -2), (key2530, -2), (key2458, -2), (key2456, 6), (key2361, -2), (key2517, -2), (key2456, -2)]

theorem rawRowCheck14899 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form2 = rawRow14899 := by decide +kernel

def row14899 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

theorem rowCheck14899 : row14899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14899 := by decide +kernel

theorem rowEval14899 (x : Key → ℝ) : Integer.Sparse.eval row14899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14899, Integer.Sparse.eval_collectBalanced, rawRowCheck14899]

def rawRow14900 : Integer.Sparse Key := [(key2528, -2), (key2560, -2), (key2530, -2), (key2530, 6), (key2452, -2), (key2519, -2), (key2458, -2), (key2452, 2), (key2519, 2), (key2357, 2), (key2560, 2), (key2363, 2), (key2530, 2), (key2458, -2), (key2363, -2), (key2530, -2), (key2456, 6), (key2456, -2), (key2361, -2), (key2517, -2)]

theorem rawRowCheck14900 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form2 = rawRow14900 := by decide +kernel

def row14900 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

theorem rowCheck14900 : row14900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14900 := by decide +kernel

theorem rowEval14900 (x : Key → ℝ) : Integer.Sparse.eval row14900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14900, Integer.Sparse.eval_collectBalanced, rawRowCheck14900]

def rawRow14901 : Integer.Sparse Key := [(key2560, -2), (key2528, -2), (key2530, -2), (key2530, 6), (key2519, -2), (key2452, -2), (key2458, -2), (key2519, 2), (key2452, 2), (key2560, 2), (key2357, 2), (key2530, 2), (key2363, 2), (key2458, -2), (key2530, -2), (key2363, -2), (key2456, 6), (key2456, -2), (key2517, -2), (key2361, -2)]

theorem rawRowCheck14901 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form2 = rawRow14901 := by decide +kernel

def row14901 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

theorem rowCheck14901 : row14901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14901 := by decide +kernel

theorem rowEval14901 (x : Key → ℝ) : Integer.Sparse.eval row14901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck14901, Integer.Sparse.eval_collectBalanced, rawRowCheck14901]

def rawRow14902 : Integer.Sparse Key := [(key2530, -2), (key2560, -2), (key2528, -2), (key2530, 6), (key2458, -2), (key2519, -2), (key2452, -2), (key2530, 2), (key2560, 2), (key2363, 2), (key2519, 2), (key2357, 2), (key2452, 2), (key2530, -2), (key2363, -2), (key2458, -2), (key2456, 6), (key2517, -2), (key2361, -2), (key2456, -2)]

theorem rawRowCheck14902 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form2 = rawRow14902 := by decide +kernel

def row14902 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

theorem rowCheck14902 : row14902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14902 := by decide +kernel

theorem rowEval14902 (x : Key → ℝ) : Integer.Sparse.eval row14902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14902, Integer.Sparse.eval_collectBalanced, rawRowCheck14902]

def rawRow14903 : Integer.Sparse Key := [(key2560, -2), (key2530, -2), (key2528, -2), (key2530, 6), (key2519, -2), (key2458, -2), (key2452, -2), (key2560, 2), (key2530, 2), (key2519, 2), (key2363, 2), (key2452, 2), (key2357, 2), (key2530, -2), (key2458, -2), (key2363, -2), (key2456, 6), (key2517, -2), (key2456, -2), (key2361, -2)]

theorem rawRowCheck14903 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form2 = rawRow14903 := by decide +kernel

def row14903 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

theorem rowCheck14903 : row14903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14903 := by decide +kernel

theorem rowEval14903 (x : Key → ℝ) : Integer.Sparse.eval row14903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck14903, Integer.Sparse.eval_collectBalanced, rawRowCheck14903]

def rawRow14904 : Integer.Sparse Key := [(key2530, -2), (key2530, -2), (key2560, -2), (key2528, 6), (key2530, -2), (key2530, -2), (key2560, -2), (key2363, 2), (key2363, 2), (key2458, 2), (key2458, 2), (key2519, 2), (key2519, 2), (key2357, -2), (key2452, -2), (key2452, -2), (key2517, 6), (key2361, -2), (key2456, -2), (key2456, -2)]

theorem rawRowCheck14904 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form2 = rawRow14904 := by decide +kernel

def row14904 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, 4), (key2452, -4), (key2456, -4), (key2458, 4), (key2517, 6), (key2519, 4), (key2528, 6), (key2530, -8), (key2560, -4)]

theorem rowCheck14904 : row14904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14904 := by decide +kernel

theorem rowEval14904 (x : Key → ℝ) : Integer.Sparse.eval row14904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14904, Integer.Sparse.eval_collectBalanced, rawRowCheck14904]

def rawRow14905 : Integer.Sparse Key := [(key2530, -2), (key2560, -2), (key2530, -2), (key2528, 6), (key2530, -2), (key2560, -2), (key2530, -2), (key2458, 2), (key2519, 2), (key2363, 2), (key2519, 2), (key2363, 2), (key2458, 2), (key2452, -2), (key2357, -2), (key2452, -2), (key2517, 6), (key2456, -2), (key2361, -2), (key2456, -2)]

theorem rawRowCheck14905 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form2 = rawRow14905 := by decide +kernel

def row14905 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, 4), (key2452, -4), (key2456, -4), (key2458, 4), (key2517, 6), (key2519, 4), (key2528, 6), (key2530, -8), (key2560, -4)]

theorem rowCheck14905 : row14905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14905 := by decide +kernel

theorem rowEval14905 (x : Key → ℝ) : Integer.Sparse.eval row14905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14905, Integer.Sparse.eval_collectBalanced, rawRowCheck14905]

def rawRow14906 : Integer.Sparse Key := [(key2560, -2), (key2530, -2), (key2530, -2), (key2528, 6), (key2560, -2), (key2530, -2), (key2530, -2), (key2519, 2), (key2458, 2), (key2519, 2), (key2363, 2), (key2458, 2), (key2363, 2), (key2452, -2), (key2452, -2), (key2357, -2), (key2517, 6), (key2456, -2), (key2456, -2), (key2361, -2)]

theorem rawRowCheck14906 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form2 = rawRow14906 := by decide +kernel

def row14906 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, 4), (key2452, -4), (key2456, -4), (key2458, 4), (key2517, 6), (key2519, 4), (key2528, 6), (key2530, -8), (key2560, -4)]

theorem rowCheck14906 : row14906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14906 := by decide +kernel

theorem rowEval14906 (x : Key → ℝ) : Integer.Sparse.eval row14906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck14906, Integer.Sparse.eval_collectBalanced, rawRowCheck14906]

def rawRow14907 : Integer.Sparse Key := [(key2377, 6), (key2377, -2), (key2389, -2), (key2389, -2), (key2405, 6), (key2405, -2), (key2436, -2), (key2436, -2), (key2471, -2), (key2479, -2), (key2479, -2), (key2471, -2), (key2502, -2), (key2502, -2), (key2479, 2), (key2479, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2518, 2)]

theorem rawRowCheck14907 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form3 = rawRow14907 := by decide +kernel

def row14907 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

theorem rowCheck14907 : row14907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14907 := by decide +kernel

theorem rowEval14907 (x : Key → ℝ) : Integer.Sparse.eval row14907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14907, Integer.Sparse.eval_collectBalanced, rawRowCheck14907]

def rawRow14908 : Integer.Sparse Key := [(key2377, 6), (key2389, -2), (key2377, -2), (key2389, -2), (key2405, 6), (key2436, -2), (key2405, -2), (key2436, -2), (key2479, -2), (key2471, -2), (key2479, -2), (key2502, -2), (key2471, -2), (key2502, -2), (key2502, 2), (key2518, 2), (key2479, 2), (key2518, 2), (key2479, 2), (key2502, 2)]

theorem rawRowCheck14908 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form3 = rawRow14908 := by decide +kernel

def row14908 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

theorem rowCheck14908 : row14908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14908 := by decide +kernel

theorem rowEval14908 (x : Key → ℝ) : Integer.Sparse.eval row14908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14908, Integer.Sparse.eval_collectBalanced, rawRowCheck14908]

def rawRow14909 : Integer.Sparse Key := [(key2377, 6), (key2389, -2), (key2389, -2), (key2377, -2), (key2405, 6), (key2436, -2), (key2436, -2), (key2405, -2), (key2479, -2), (key2479, -2), (key2471, -2), (key2502, -2), (key2502, -2), (key2471, -2), (key2518, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2502, 2), (key2479, 2)]

theorem rawRowCheck14909 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form3 = rawRow14909 := by decide +kernel

def row14909 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

theorem rowCheck14909 : row14909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14909 := by decide +kernel

theorem rowEval14909 (x : Key → ℝ) : Integer.Sparse.eval row14909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14909, Integer.Sparse.eval_collectBalanced, rawRowCheck14909]

def rawRow14910 : Integer.Sparse Key := [(key2389, 6), (key2377, -2), (key2377, -2), (key2389, -2), (key2436, 6), (key2405, -2), (key2405, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2471, 2), (key2479, 2), (key2471, 2), (key2502, 2), (key2479, 2), (key2502, 2)]

theorem rawRowCheck14910 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form3 = rawRow14910 := by decide +kernel

def row14910 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

theorem rowCheck14910 : row14910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14910 := by decide +kernel

theorem rowEval14910 (x : Key → ℝ) : Integer.Sparse.eval row14910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14910, Integer.Sparse.eval_collectBalanced, rawRowCheck14910]

def rawRow14911 : Integer.Sparse Key := [(key2389, 6), (key2377, -2), (key2389, -2), (key2377, -2), (key2436, 6), (key2405, -2), (key2436, -2), (key2405, -2), (key2502, -2), (key2518, -2), (key2502, -2), (key2479, -2), (key2518, -2), (key2479, -2), (key2479, 2), (key2471, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2479, 2)]

theorem rawRowCheck14911 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form3 = rawRow14911 := by decide +kernel

def row14911 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

theorem rowCheck14911 : row14911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14911 := by decide +kernel

theorem rowEval14911 (x : Key → ℝ) : Integer.Sparse.eval row14911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14911, Integer.Sparse.eval_collectBalanced, rawRowCheck14911]

def rawRow14912 : Integer.Sparse Key := [(key2389, 6), (key2389, -2), (key2377, -2), (key2377, -2), (key2436, 6), (key2436, -2), (key2405, -2), (key2405, -2), (key2518, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2479, -2), (key2479, -2), (key2502, 2), (key2502, 2), (key2479, 2), (key2479, 2), (key2471, 2), (key2471, 2)]

theorem rawRowCheck14912 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form3 = rawRow14912 := by decide +kernel

def row14912 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

theorem rowCheck14912 : row14912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14912 := by decide +kernel

theorem rowEval14912 (x : Key → ℝ) : Integer.Sparse.eval row14912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14912, Integer.Sparse.eval_collectBalanced, rawRowCheck14912]

def rawRow14913 : Integer.Sparse Key := [(key2405, 6), (key2471, -2), (key2479, -2), (key2479, -2), (key2377, 6), (key2471, -2), (key2502, -2), (key2502, -2), (key2377, -2), (key2389, -2), (key2389, -2), (key2405, -2), (key2436, -2), (key2436, -2), (key2479, 2), (key2479, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2518, 2)]

theorem rawRowCheck14913 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form3 = rawRow14913 := by decide +kernel

def row14913 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

theorem rowCheck14913 : row14913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14913 := by decide +kernel

theorem rowEval14913 (x : Key → ℝ) : Integer.Sparse.eval row14913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14913, Integer.Sparse.eval_collectBalanced, rawRowCheck14913]

def rawRow14914 : Integer.Sparse Key := [(key2405, 6), (key2479, -2), (key2471, -2), (key2479, -2), (key2377, 6), (key2502, -2), (key2471, -2), (key2502, -2), (key2389, -2), (key2377, -2), (key2389, -2), (key2436, -2), (key2405, -2), (key2436, -2), (key2502, 2), (key2518, 2), (key2479, 2), (key2518, 2), (key2479, 2), (key2502, 2)]

theorem rawRowCheck14914 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form3 = rawRow14914 := by decide +kernel

def row14914 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

theorem rowCheck14914 : row14914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14914 := by decide +kernel

theorem rowEval14914 (x : Key → ℝ) : Integer.Sparse.eval row14914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14914, Integer.Sparse.eval_collectBalanced, rawRowCheck14914]

def rawRow14915 : Integer.Sparse Key := [(key2405, 6), (key2479, -2), (key2479, -2), (key2471, -2), (key2377, 6), (key2502, -2), (key2502, -2), (key2471, -2), (key2389, -2), (key2389, -2), (key2377, -2), (key2436, -2), (key2436, -2), (key2405, -2), (key2518, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2502, 2), (key2479, 2)]

theorem rawRowCheck14915 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form3 = rawRow14915 := by decide +kernel

def row14915 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

theorem rowCheck14915 : row14915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14915 := by decide +kernel

theorem rowEval14915 (x : Key → ℝ) : Integer.Sparse.eval row14915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14915, Integer.Sparse.eval_collectBalanced, rawRowCheck14915]

def rawRow14916 : Integer.Sparse Key := [(key2479, 6), (key2405, -2), (key2471, -2), (key2479, -2), (key2502, 6), (key2377, -2), (key2471, -2), (key2502, -2), (key2436, -2), (key2502, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2518, -2), (key2377, 2), (key2389, 2), (key2405, 2), (key2436, 2), (key2479, 2), (key2502, 2)]

theorem rawRowCheck14916 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form3 = rawRow14916 := by decide +kernel

def row14916 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck14916 : row14916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14916 := by decide +kernel

theorem rowEval14916 (x : Key → ℝ) : Integer.Sparse.eval row14916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14916, Integer.Sparse.eval_collectBalanced, rawRowCheck14916]

def rawRow14917 : Integer.Sparse Key := [(key2479, 6), (key2405, -2), (key2479, -2), (key2471, -2), (key2502, 6), (key2377, -2), (key2502, -2), (key2471, -2), (key2436, -2), (key2518, -2), (key2502, -2), (key2389, -2), (key2518, -2), (key2479, -2), (key2389, 2), (key2377, 2), (key2436, 2), (key2405, 2), (key2502, 2), (key2479, 2)]

theorem rawRowCheck14917 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form3 = rawRow14917 := by decide +kernel

def row14917 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck14917 : row14917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14917 := by decide +kernel

theorem rowEval14917 (x : Key → ℝ) : Integer.Sparse.eval row14917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14917, Integer.Sparse.eval_collectBalanced, rawRowCheck14917]

def rawRow14918 : Integer.Sparse Key := [(key2479, 6), (key2471, -2), (key2405, -2), (key2479, -2), (key2502, 6), (key2471, -2), (key2377, -2), (key2502, -2), (key2502, -2), (key2436, -2), (key2518, -2), (key2479, -2), (key2389, -2), (key2518, -2), (key2405, 2), (key2479, 2), (key2377, 2), (key2502, 2), (key2389, 2), (key2436, 2)]

theorem rawRowCheck14918 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form3 = rawRow14918 := by decide +kernel

def row14918 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck14918 : row14918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14918 := by decide +kernel

theorem rowEval14918 (x : Key → ℝ) : Integer.Sparse.eval row14918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14918, Integer.Sparse.eval_collectBalanced, rawRowCheck14918]

def rawRow14919 : Integer.Sparse Key := [(key2479, 6), (key2471, -2), (key2479, -2), (key2405, -2), (key2502, 6), (key2471, -2), (key2502, -2), (key2377, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2479, 2), (key2405, 2), (key2502, 2), (key2377, 2), (key2436, 2), (key2389, 2)]

theorem rawRowCheck14919 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form3 = rawRow14919 := by decide +kernel

def row14919 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck14919 : row14919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14919 := by decide +kernel

theorem rowEval14919 (x : Key → ℝ) : Integer.Sparse.eval row14919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck14919, Integer.Sparse.eval_collectBalanced, rawRowCheck14919]

def rawRow14920 : Integer.Sparse Key := [(key2479, 6), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, 6), (key2502, -2), (key2377, -2), (key2471, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2436, 2), (key2502, 2), (key2389, 2), (key2479, 2), (key2377, 2), (key2405, 2)]

theorem rawRowCheck14920 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form3 = rawRow14920 := by decide +kernel

def row14920 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck14920 : row14920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14920 := by decide +kernel

theorem rowEval14920 (x : Key → ℝ) : Integer.Sparse.eval row14920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14920, Integer.Sparse.eval_collectBalanced, rawRowCheck14920]

def rawRow14921 : Integer.Sparse Key := [(key2479, 6), (key2479, -2), (key2471, -2), (key2405, -2), (key2502, 6), (key2502, -2), (key2471, -2), (key2377, -2), (key2518, -2), (key2502, -2), (key2436, -2), (key2518, -2), (key2479, -2), (key2389, -2), (key2502, 2), (key2436, 2), (key2479, 2), (key2389, 2), (key2405, 2), (key2377, 2)]

theorem rawRowCheck14921 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form3 = rawRow14921 := by decide +kernel

def row14921 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck14921 : row14921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14921 := by decide +kernel

theorem rowEval14921 (x : Key → ℝ) : Integer.Sparse.eval row14921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck14921, Integer.Sparse.eval_collectBalanced, rawRowCheck14921]

def rawRow14922 : Integer.Sparse Key := [(key2436, 6), (key2502, -2), (key2502, -2), (key2518, -2), (key2389, 6), (key2479, -2), (key2479, -2), (key2518, -2), (key2377, -2), (key2377, -2), (key2389, -2), (key2405, -2), (key2405, -2), (key2436, -2), (key2471, 2), (key2479, 2), (key2471, 2), (key2502, 2), (key2479, 2), (key2502, 2)]

theorem rawRowCheck14922 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form3 = rawRow14922 := by decide +kernel

def row14922 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

theorem rowCheck14922 : row14922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14922 := by decide +kernel

theorem rowEval14922 (x : Key → ℝ) : Integer.Sparse.eval row14922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14922, Integer.Sparse.eval_collectBalanced, rawRowCheck14922]

def rawRow14923 : Integer.Sparse Key := [(key2436, 6), (key2502, -2), (key2518, -2), (key2502, -2), (key2389, 6), (key2479, -2), (key2518, -2), (key2479, -2), (key2377, -2), (key2389, -2), (key2377, -2), (key2405, -2), (key2436, -2), (key2405, -2), (key2479, 2), (key2471, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2479, 2)]

theorem rawRowCheck14923 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form3 = rawRow14923 := by decide +kernel

def row14923 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

theorem rowCheck14923 : row14923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14923 := by decide +kernel

theorem rowEval14923 (x : Key → ℝ) : Integer.Sparse.eval row14923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14923, Integer.Sparse.eval_collectBalanced, rawRowCheck14923]

def rawRow14924 : Integer.Sparse Key := [(key2436, 6), (key2518, -2), (key2502, -2), (key2502, -2), (key2389, 6), (key2518, -2), (key2479, -2), (key2479, -2), (key2389, -2), (key2377, -2), (key2377, -2), (key2436, -2), (key2405, -2), (key2405, -2), (key2502, 2), (key2502, 2), (key2479, 2), (key2479, 2), (key2471, 2), (key2471, 2)]

theorem rawRowCheck14924 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form3 = rawRow14924 := by decide +kernel

def row14924 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

theorem rowCheck14924 : row14924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14924 := by decide +kernel

theorem rowEval14924 (x : Key → ℝ) : Integer.Sparse.eval row14924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14924, Integer.Sparse.eval_collectBalanced, rawRowCheck14924]

def rawRow14925 : Integer.Sparse Key := [(key2502, 6), (key2436, -2), (key2502, -2), (key2518, -2), (key2479, 6), (key2389, -2), (key2479, -2), (key2518, -2), (key2405, -2), (key2471, -2), (key2479, -2), (key2377, -2), (key2471, -2), (key2502, -2), (key2377, 2), (key2389, 2), (key2405, 2), (key2436, 2), (key2479, 2), (key2502, 2)]

theorem rawRowCheck14925 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form3 = rawRow14925 := by decide +kernel

def row14925 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck14925 : row14925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14925 := by decide +kernel

theorem rowEval14925 (x : Key → ℝ) : Integer.Sparse.eval row14925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14925, Integer.Sparse.eval_collectBalanced, rawRowCheck14925]

def rawRow14926 : Integer.Sparse Key := [(key2502, 6), (key2436, -2), (key2518, -2), (key2502, -2), (key2479, 6), (key2389, -2), (key2518, -2), (key2479, -2), (key2405, -2), (key2479, -2), (key2471, -2), (key2377, -2), (key2502, -2), (key2471, -2), (key2389, 2), (key2377, 2), (key2436, 2), (key2405, 2), (key2502, 2), (key2479, 2)]

theorem rawRowCheck14926 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form3 = rawRow14926 := by decide +kernel

def row14926 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck14926 : row14926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14926 := by decide +kernel

theorem rowEval14926 (x : Key → ℝ) : Integer.Sparse.eval row14926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14926, Integer.Sparse.eval_collectBalanced, rawRowCheck14926]

def rawRow14927 : Integer.Sparse Key := [(key2502, 6), (key2502, -2), (key2436, -2), (key2518, -2), (key2479, 6), (key2479, -2), (key2389, -2), (key2518, -2), (key2471, -2), (key2405, -2), (key2479, -2), (key2471, -2), (key2377, -2), (key2502, -2), (key2405, 2), (key2479, 2), (key2377, 2), (key2502, 2), (key2389, 2), (key2436, 2)]

theorem rawRowCheck14927 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form3 = rawRow14927 := by decide +kernel

def row14927 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck14927 : row14927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14927 := by decide +kernel

theorem rowEval14927 (x : Key → ℝ) : Integer.Sparse.eval row14927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14927, Integer.Sparse.eval_collectBalanced, rawRowCheck14927]

def rawRow14928 : Integer.Sparse Key := [(key2502, 6), (key2502, -2), (key2518, -2), (key2436, -2), (key2479, 6), (key2479, -2), (key2518, -2), (key2389, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2479, 2), (key2405, 2), (key2502, 2), (key2377, 2), (key2436, 2), (key2389, 2)]

theorem rawRowCheck14928 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form3 = rawRow14928 := by decide +kernel

def row14928 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck14928 : row14928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14928 := by decide +kernel

theorem rowEval14928 (x : Key → ℝ) : Integer.Sparse.eval row14928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck14928, Integer.Sparse.eval_collectBalanced, rawRowCheck14928]

def rawRow14929 : Integer.Sparse Key := [(key2502, 6), (key2518, -2), (key2436, -2), (key2502, -2), (key2479, 6), (key2518, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2436, 2), (key2502, 2), (key2389, 2), (key2479, 2), (key2377, 2), (key2405, 2)]

theorem rawRowCheck14929 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form3 = rawRow14929 := by decide +kernel

def row14929 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck14929 : row14929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14929 := by decide +kernel

theorem rowEval14929 (x : Key → ℝ) : Integer.Sparse.eval row14929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14929, Integer.Sparse.eval_collectBalanced, rawRowCheck14929]

def rawRow14930 : Integer.Sparse Key := [(key2502, 6), (key2518, -2), (key2502, -2), (key2436, -2), (key2479, 6), (key2518, -2), (key2479, -2), (key2389, -2), (key2479, -2), (key2471, -2), (key2405, -2), (key2502, -2), (key2471, -2), (key2377, -2), (key2502, 2), (key2436, 2), (key2479, 2), (key2389, 2), (key2405, 2), (key2377, 2)]

theorem rawRowCheck14930 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form3 = rawRow14930 := by decide +kernel

def row14930 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck14930 : row14930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14930 := by decide +kernel

theorem rowEval14930 (x : Key → ℝ) : Integer.Sparse.eval row14930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck14930, Integer.Sparse.eval_collectBalanced, rawRowCheck14930]

def rawRow14931 : Integer.Sparse Key := [(key2518, 6), (key2436, -2), (key2502, -2), (key2502, -2), (key2518, 6), (key2389, -2), (key2479, -2), (key2479, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2377, 2), (key2377, 2), (key2405, 2), (key2405, 2), (key2471, 2), (key2471, 2)]

theorem rawRowCheck14931 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form3 = rawRow14931 := by decide +kernel

def row14931 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, 4), (key2479, -8), (key2502, -8), (key2518, 12)]

theorem rowCheck14931 : row14931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14931 := by decide +kernel

theorem rowEval14931 (x : Key → ℝ) : Integer.Sparse.eval row14931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14931, Integer.Sparse.eval_collectBalanced, rawRowCheck14931]

def rawRow14932 : Integer.Sparse Key := [(key2518, 6), (key2502, -2), (key2436, -2), (key2502, -2), (key2518, 6), (key2479, -2), (key2389, -2), (key2479, -2), (key2502, -2), (key2436, -2), (key2502, -2), (key2479, -2), (key2389, -2), (key2479, -2), (key2405, 2), (key2471, 2), (key2377, 2), (key2471, 2), (key2377, 2), (key2405, 2)]

theorem rawRowCheck14932 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form3 = rawRow14932 := by decide +kernel

def row14932 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, 4), (key2479, -8), (key2502, -8), (key2518, 12)]

theorem rowCheck14932 : row14932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14932 := by decide +kernel

theorem rowEval14932 (x : Key → ℝ) : Integer.Sparse.eval row14932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14932, Integer.Sparse.eval_collectBalanced, rawRowCheck14932]

def rawRow14933 : Integer.Sparse Key := [(key2518, 6), (key2502, -2), (key2502, -2), (key2436, -2), (key2518, 6), (key2479, -2), (key2479, -2), (key2389, -2), (key2502, -2), (key2502, -2), (key2436, -2), (key2479, -2), (key2479, -2), (key2389, -2), (key2471, 2), (key2405, 2), (key2471, 2), (key2377, 2), (key2405, 2), (key2377, 2)]

theorem rawRowCheck14933 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form3 = rawRow14933 := by decide +kernel

def row14933 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, 4), (key2479, -8), (key2502, -8), (key2518, 12)]

theorem rowCheck14933 : row14933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14933 := by decide +kernel

theorem rowEval14933 (x : Key → ℝ) : Integer.Sparse.eval row14933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck14933, Integer.Sparse.eval_collectBalanced, rawRowCheck14933]

def rawRow14934 : Integer.Sparse Key := [(key976, -2), (key976, -2), (key983, -2), (key983, 6), (key1090, -2), (key1090, -2), (key1097, -2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1182, 2), (key1182, 2), (key1097, -2), (key1182, -2), (key1182, -2), (key1168, 6), (key1168, -2), (key1219, -2), (key1219, -2)]

theorem rawRowCheck14934 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form4 = rawRow14934 := by decide +kernel

def row14934 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

theorem rowCheck14934 : row14934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14934 := by decide +kernel

theorem rowEval14934 (x : Key → ℝ) : Integer.Sparse.eval row14934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14934, Integer.Sparse.eval_collectBalanced, rawRowCheck14934]

def rawRow14935 : Integer.Sparse Key := [(key976, -2), (key983, -2), (key976, -2), (key983, 6), (key1090, -2), (key1097, -2), (key1090, -2), (key1180, 2), (key1182, 2), (key1090, 2), (key1182, 2), (key1090, 2), (key1180, 2), (key1182, -2), (key1097, -2), (key1182, -2), (key1168, 6), (key1219, -2), (key1168, -2), (key1219, -2)]

theorem rawRowCheck14935 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form4 = rawRow14935 := by decide +kernel

def row14935 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

theorem rowCheck14935 : row14935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14935 := by decide +kernel

theorem rowEval14935 (x : Key → ℝ) : Integer.Sparse.eval row14935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14935, Integer.Sparse.eval_collectBalanced, rawRowCheck14935]

def rawRow14936 : Integer.Sparse Key := [(key983, -2), (key976, -2), (key976, -2), (key983, 6), (key1097, -2), (key1090, -2), (key1090, -2), (key1182, 2), (key1180, 2), (key1182, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1182, -2), (key1182, -2), (key1097, -2), (key1168, 6), (key1219, -2), (key1219, -2), (key1168, -2)]

theorem rawRowCheck14936 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form4 = rawRow14936 := by decide +kernel

def row14936 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

theorem rowCheck14936 : row14936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14936 := by decide +kernel

theorem rowEval14936 (x : Key → ℝ) : Integer.Sparse.eval row14936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14936, Integer.Sparse.eval_collectBalanced, rawRowCheck14936]

def rawRow14937 : Integer.Sparse Key := [(key976, -2), (key983, -2), (key983, -2), (key976, 6), (key1180, -2), (key1182, -2), (key1182, -2), (key1090, 2), (key1097, 2), (key1090, 2), (key1182, 2), (key1097, 2), (key1182, 2), (key1090, -2), (key1090, -2), (key1180, -2), (key1219, 6), (key1168, -2), (key1168, -2), (key1219, -2)]

theorem rawRowCheck14937 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form4 = rawRow14937 := by decide +kernel

def row14937 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

theorem rowCheck14937 : row14937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14937 := by decide +kernel

theorem rowEval14937 (x : Key → ℝ) : Integer.Sparse.eval row14937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14937, Integer.Sparse.eval_collectBalanced, rawRowCheck14937]

def rawRow14938 : Integer.Sparse Key := [(key983, -2), (key976, -2), (key983, -2), (key976, 6), (key1182, -2), (key1180, -2), (key1182, -2), (key1097, 2), (key1090, 2), (key1182, 2), (key1090, 2), (key1182, 2), (key1097, 2), (key1090, -2), (key1180, -2), (key1090, -2), (key1219, 6), (key1168, -2), (key1219, -2), (key1168, -2)]

theorem rawRowCheck14938 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form4 = rawRow14938 := by decide +kernel

def row14938 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

theorem rowCheck14938 : row14938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14938 := by decide +kernel

theorem rowEval14938 (x : Key → ℝ) : Integer.Sparse.eval row14938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14938, Integer.Sparse.eval_collectBalanced, rawRowCheck14938]

def rawRow14939 : Integer.Sparse Key := [(key983, -2), (key983, -2), (key976, -2), (key976, 6), (key1182, -2), (key1182, -2), (key1180, -2), (key1182, 2), (key1182, 2), (key1097, 2), (key1097, 2), (key1090, 2), (key1090, 2), (key1180, -2), (key1090, -2), (key1090, -2), (key1219, 6), (key1219, -2), (key1168, -2), (key1168, -2)]

theorem rawRowCheck14939 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form4 = rawRow14939 := by decide +kernel

def row14939 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

theorem rowCheck14939 : row14939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14939 := by decide +kernel

theorem rowEval14939 (x : Key → ℝ) : Integer.Sparse.eval row14939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14939, Integer.Sparse.eval_collectBalanced, rawRowCheck14939]

def rawRow14940 : Integer.Sparse Key := [(key1090, -2), (key1090, -2), (key1097, -2), (key1168, 6), (key976, -2), (key976, -2), (key983, -2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1182, 2), (key1182, 2), (key1168, -2), (key1219, -2), (key1219, -2), (key983, 6), (key1097, -2), (key1182, -2), (key1182, -2)]

theorem rawRowCheck14940 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form4 = rawRow14940 := by decide +kernel

def row14940 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

theorem rowCheck14940 : row14940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14940 := by decide +kernel

theorem rowEval14940 (x : Key → ℝ) : Integer.Sparse.eval row14940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14940, Integer.Sparse.eval_collectBalanced, rawRowCheck14940]

def rawRow14941 : Integer.Sparse Key := [(key1090, -2), (key1097, -2), (key1090, -2), (key1168, 6), (key976, -2), (key983, -2), (key976, -2), (key1180, 2), (key1182, 2), (key1090, 2), (key1182, 2), (key1090, 2), (key1180, 2), (key1219, -2), (key1168, -2), (key1219, -2), (key983, 6), (key1182, -2), (key1097, -2), (key1182, -2)]

theorem rawRowCheck14941 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form4 = rawRow14941 := by decide +kernel

def row14941 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

theorem rowCheck14941 : row14941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14941 := by decide +kernel

theorem rowEval14941 (x : Key → ℝ) : Integer.Sparse.eval row14941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14941, Integer.Sparse.eval_collectBalanced, rawRowCheck14941]

def rawRow14942 : Integer.Sparse Key := [(key1097, -2), (key1090, -2), (key1090, -2), (key1168, 6), (key983, -2), (key976, -2), (key976, -2), (key1182, 2), (key1180, 2), (key1182, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1219, -2), (key1219, -2), (key1168, -2), (key983, 6), (key1182, -2), (key1182, -2), (key1097, -2)]

theorem rawRowCheck14942 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form4 = rawRow14942 := by decide +kernel

def row14942 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

theorem rowCheck14942 : row14942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14942 := by decide +kernel

theorem rowEval14942 (x : Key → ℝ) : Integer.Sparse.eval row14942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14942, Integer.Sparse.eval_collectBalanced, rawRowCheck14942]

def rawRow14943 : Integer.Sparse Key := [(key1090, -2), (key1097, -2), (key1168, -2), (key1090, 6), (key1180, -2), (key1182, -2), (key1219, -2), (key976, 2), (key983, 2), (key1090, 2), (key1182, 2), (key1168, 2), (key1219, 2), (key976, -2), (key1090, -2), (key1180, -2), (key1182, 6), (key983, -2), (key1097, -2), (key1182, -2)]

theorem rawRowCheck14943 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form4 = rawRow14943 := by decide +kernel

def row14943 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck14943 : row14943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14943 := by decide +kernel

theorem rowEval14943 (x : Key → ℝ) : Integer.Sparse.eval row14943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14943, Integer.Sparse.eval_collectBalanced, rawRowCheck14943]

def rawRow14944 : Integer.Sparse Key := [(key1097, -2), (key1090, -2), (key1168, -2), (key1090, 6), (key1182, -2), (key1180, -2), (key1219, -2), (key983, 2), (key976, 2), (key1182, 2), (key1090, 2), (key1219, 2), (key1168, 2), (key976, -2), (key1180, -2), (key1090, -2), (key1182, 6), (key983, -2), (key1182, -2), (key1097, -2)]

theorem rawRowCheck14944 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form4 = rawRow14944 := by decide +kernel

def row14944 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck14944 : row14944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14944 := by decide +kernel

theorem rowEval14944 (x : Key → ℝ) : Integer.Sparse.eval row14944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14944, Integer.Sparse.eval_collectBalanced, rawRowCheck14944]

def rawRow14945 : Integer.Sparse Key := [(key1090, -2), (key1168, -2), (key1097, -2), (key1090, 6), (key1180, -2), (key1219, -2), (key1182, -2), (key1090, 2), (key1168, 2), (key976, 2), (key1219, 2), (key983, 2), (key1182, 2), (key1090, -2), (key976, -2), (key1180, -2), (key1182, 6), (key1097, -2), (key983, -2), (key1182, -2)]

theorem rawRowCheck14945 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form4 = rawRow14945 := by decide +kernel

def row14945 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck14945 : row14945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14945 := by decide +kernel

theorem rowEval14945 (x : Key → ℝ) : Integer.Sparse.eval row14945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14945, Integer.Sparse.eval_collectBalanced, rawRowCheck14945]

def rawRow14946 : Integer.Sparse Key := [(key1168, -2), (key1090, -2), (key1097, -2), (key1090, 6), (key1219, -2), (key1180, -2), (key1182, -2), (key1168, 2), (key1090, 2), (key1219, 2), (key976, 2), (key1182, 2), (key983, 2), (key1090, -2), (key1180, -2), (key976, -2), (key1182, 6), (key1097, -2), (key1182, -2), (key983, -2)]

theorem rawRowCheck14946 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form4 = rawRow14946 := by decide +kernel

def row14946 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck14946 : row14946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14946 := by decide +kernel

theorem rowEval14946 (x : Key → ℝ) : Integer.Sparse.eval row14946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14946, Integer.Sparse.eval_collectBalanced, rawRowCheck14946]

def rawRow14947 : Integer.Sparse Key := [(key1097, -2), (key1168, -2), (key1090, -2), (key1090, 6), (key1182, -2), (key1219, -2), (key1180, -2), (key1182, 2), (key1219, 2), (key983, 2), (key1168, 2), (key976, 2), (key1090, 2), (key1180, -2), (key976, -2), (key1090, -2), (key1182, 6), (key1182, -2), (key983, -2), (key1097, -2)]

theorem rawRowCheck14947 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form4 = rawRow14947 := by decide +kernel

def row14947 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck14947 : row14947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14947 := by decide +kernel

theorem rowEval14947 (x : Key → ℝ) : Integer.Sparse.eval row14947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14947, Integer.Sparse.eval_collectBalanced, rawRowCheck14947]

def rawRow14948 : Integer.Sparse Key := [(key1168, -2), (key1097, -2), (key1090, -2), (key1090, 6), (key1219, -2), (key1182, -2), (key1180, -2), (key1219, 2), (key1182, 2), (key1168, 2), (key983, 2), (key1090, 2), (key976, 2), (key1180, -2), (key1090, -2), (key976, -2), (key1182, 6), (key1182, -2), (key1097, -2), (key983, -2)]

theorem rawRowCheck14948 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form4 = rawRow14948 := by decide +kernel

def row14948 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck14948 : row14948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14948 := by decide +kernel

theorem rowEval14948 (x : Key → ℝ) : Integer.Sparse.eval row14948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14948, Integer.Sparse.eval_collectBalanced, rawRowCheck14948]

def rawRow14949 : Integer.Sparse Key := [(key1180, -2), (key1182, -2), (key1182, -2), (key1219, 6), (key976, -2), (key983, -2), (key983, -2), (key1090, 2), (key1097, 2), (key1090, 2), (key1182, 2), (key1097, 2), (key1182, 2), (key1168, -2), (key1168, -2), (key1219, -2), (key976, 6), (key1090, -2), (key1090, -2), (key1180, -2)]

theorem rawRowCheck14949 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form4 = rawRow14949 := by decide +kernel

def row14949 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

theorem rowCheck14949 : row14949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14949 := by decide +kernel

theorem rowEval14949 (x : Key → ℝ) : Integer.Sparse.eval row14949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14949, Integer.Sparse.eval_collectBalanced, rawRowCheck14949]

def rawRow14950 : Integer.Sparse Key := [(key1182, -2), (key1180, -2), (key1182, -2), (key1219, 6), (key983, -2), (key976, -2), (key983, -2), (key1097, 2), (key1090, 2), (key1182, 2), (key1090, 2), (key1182, 2), (key1097, 2), (key1168, -2), (key1219, -2), (key1168, -2), (key976, 6), (key1090, -2), (key1180, -2), (key1090, -2)]

theorem rawRowCheck14950 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form4 = rawRow14950 := by decide +kernel

def row14950 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

theorem rowCheck14950 : row14950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14950 := by decide +kernel

theorem rowEval14950 (x : Key → ℝ) : Integer.Sparse.eval row14950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14950, Integer.Sparse.eval_collectBalanced, rawRowCheck14950]

def rawRow14951 : Integer.Sparse Key := [(key1182, -2), (key1182, -2), (key1180, -2), (key1219, 6), (key983, -2), (key983, -2), (key976, -2), (key1182, 2), (key1182, 2), (key1097, 2), (key1097, 2), (key1090, 2), (key1090, 2), (key1219, -2), (key1168, -2), (key1168, -2), (key976, 6), (key1180, -2), (key1090, -2), (key1090, -2)]

theorem rawRowCheck14951 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form4 = rawRow14951 := by decide +kernel

def row14951 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

theorem rowCheck14951 : row14951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14951 := by decide +kernel

theorem rowEval14951 (x : Key → ℝ) : Integer.Sparse.eval row14951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14951, Integer.Sparse.eval_collectBalanced, rawRowCheck14951]

def rawRow14952 : Integer.Sparse Key := [(key1180, -2), (key1182, -2), (key1219, -2), (key1182, 6), (key1090, -2), (key1097, -2), (key1168, -2), (key976, 2), (key983, 2), (key1090, 2), (key1182, 2), (key1168, 2), (key1219, 2), (key983, -2), (key1097, -2), (key1182, -2), (key1090, 6), (key976, -2), (key1090, -2), (key1180, -2)]

theorem rawRowCheck14952 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form4 = rawRow14952 := by decide +kernel

def row14952 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck14952 : row14952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14952 := by decide +kernel

theorem rowEval14952 (x : Key → ℝ) : Integer.Sparse.eval row14952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14952, Integer.Sparse.eval_collectBalanced, rawRowCheck14952]

def rawRow14953 : Integer.Sparse Key := [(key1182, -2), (key1180, -2), (key1219, -2), (key1182, 6), (key1097, -2), (key1090, -2), (key1168, -2), (key983, 2), (key976, 2), (key1182, 2), (key1090, 2), (key1219, 2), (key1168, 2), (key983, -2), (key1182, -2), (key1097, -2), (key1090, 6), (key976, -2), (key1180, -2), (key1090, -2)]

theorem rawRowCheck14953 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form4 = rawRow14953 := by decide +kernel

def row14953 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck14953 : row14953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14953 := by decide +kernel

theorem rowEval14953 (x : Key → ℝ) : Integer.Sparse.eval row14953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14953, Integer.Sparse.eval_collectBalanced, rawRowCheck14953]

def rawRow14954 : Integer.Sparse Key := [(key1180, -2), (key1219, -2), (key1182, -2), (key1182, 6), (key1090, -2), (key1168, -2), (key1097, -2), (key1090, 2), (key1168, 2), (key976, 2), (key1219, 2), (key983, 2), (key1182, 2), (key1097, -2), (key983, -2), (key1182, -2), (key1090, 6), (key1090, -2), (key976, -2), (key1180, -2)]

theorem rawRowCheck14954 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form4 = rawRow14954 := by decide +kernel

def row14954 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck14954 : row14954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14954 := by decide +kernel

theorem rowEval14954 (x : Key → ℝ) : Integer.Sparse.eval row14954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14954, Integer.Sparse.eval_collectBalanced, rawRowCheck14954]

def rawRow14955 : Integer.Sparse Key := [(key1219, -2), (key1180, -2), (key1182, -2), (key1182, 6), (key1168, -2), (key1090, -2), (key1097, -2), (key1168, 2), (key1090, 2), (key1219, 2), (key976, 2), (key1182, 2), (key983, 2), (key1097, -2), (key1182, -2), (key983, -2), (key1090, 6), (key1090, -2), (key1180, -2), (key976, -2)]

theorem rawRowCheck14955 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form4 = rawRow14955 := by decide +kernel

def row14955 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck14955 : row14955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14955 := by decide +kernel

theorem rowEval14955 (x : Key → ℝ) : Integer.Sparse.eval row14955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14955, Integer.Sparse.eval_collectBalanced, rawRowCheck14955]

def rawRow14956 : Integer.Sparse Key := [(key1182, -2), (key1219, -2), (key1180, -2), (key1182, 6), (key1097, -2), (key1168, -2), (key1090, -2), (key1182, 2), (key1219, 2), (key983, 2), (key1168, 2), (key976, 2), (key1090, 2), (key1182, -2), (key983, -2), (key1097, -2), (key1090, 6), (key1180, -2), (key976, -2), (key1090, -2)]

theorem rawRowCheck14956 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form4 = rawRow14956 := by decide +kernel

def row14956 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck14956 : row14956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14956 := by decide +kernel

theorem rowEval14956 (x : Key → ℝ) : Integer.Sparse.eval row14956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14956, Integer.Sparse.eval_collectBalanced, rawRowCheck14956]

def rawRow14957 : Integer.Sparse Key := [(key1219, -2), (key1182, -2), (key1180, -2), (key1182, 6), (key1168, -2), (key1097, -2), (key1090, -2), (key1219, 2), (key1182, 2), (key1168, 2), (key983, 2), (key1090, 2), (key976, 2), (key1182, -2), (key1097, -2), (key983, -2), (key1090, 6), (key1180, -2), (key1090, -2), (key976, -2)]

theorem rawRowCheck14957 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form4 = rawRow14957 := by decide +kernel

def row14957 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck14957 : row14957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14957 := by decide +kernel

theorem rowEval14957 (x : Key → ℝ) : Integer.Sparse.eval row14957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14957, Integer.Sparse.eval_collectBalanced, rawRowCheck14957]

def rawRow14958 : Integer.Sparse Key := [(key1182, -2), (key1182, -2), (key1219, -2), (key1180, 6), (key1182, -2), (key1182, -2), (key1219, -2), (key983, 2), (key983, 2), (key1097, 2), (key1097, 2), (key1168, 2), (key1168, 2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, 6), (key976, -2), (key1090, -2), (key1090, -2)]

theorem rawRowCheck14958 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form4 = rawRow14958 := by decide +kernel

def row14958 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, -8), (key1097, 4), (key1168, 4), (key1180, 12), (key1182, -8), (key1219, -4)]

theorem rowCheck14958 : row14958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14958 := by decide +kernel

theorem rowEval14958 (x : Key → ℝ) : Integer.Sparse.eval row14958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14958, Integer.Sparse.eval_collectBalanced, rawRowCheck14958]

def rawRow14959 : Integer.Sparse Key := [(key1182, -2), (key1219, -2), (key1182, -2), (key1180, 6), (key1182, -2), (key1219, -2), (key1182, -2), (key1097, 2), (key1168, 2), (key983, 2), (key1168, 2), (key983, 2), (key1097, 2), (key1090, -2), (key976, -2), (key1090, -2), (key1180, 6), (key1090, -2), (key976, -2), (key1090, -2)]

theorem rawRowCheck14959 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form4 = rawRow14959 := by decide +kernel

def row14959 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, -8), (key1097, 4), (key1168, 4), (key1180, 12), (key1182, -8), (key1219, -4)]

theorem rowCheck14959 : row14959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14959 := by decide +kernel

theorem rowEval14959 (x : Key → ℝ) : Integer.Sparse.eval row14959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14959, Integer.Sparse.eval_collectBalanced, rawRowCheck14959]

def rawRow14960 : Integer.Sparse Key := [(key1219, -2), (key1182, -2), (key1182, -2), (key1180, 6), (key1219, -2), (key1182, -2), (key1182, -2), (key1168, 2), (key1097, 2), (key1168, 2), (key983, 2), (key1097, 2), (key983, 2), (key1090, -2), (key1090, -2), (key976, -2), (key1180, 6), (key1090, -2), (key1090, -2), (key976, -2)]

theorem rawRowCheck14960 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form4 = rawRow14960 := by decide +kernel

def row14960 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, -8), (key1097, 4), (key1168, 4), (key1180, 12), (key1182, -8), (key1219, -4)]

theorem rowCheck14960 : row14960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14960 := by decide +kernel

theorem rowEval14960 (x : Key → ℝ) : Integer.Sparse.eval row14960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14960, Integer.Sparse.eval_collectBalanced, rawRowCheck14960]

def rawRow14961 : Integer.Sparse Key := [(key1096, 4), (key1185, 4), (key1185, 4), (key1100, -2), (key1100, -2), (key1185, -2), (key1185, -2), (key1186, -2), (key1186, -2), (key1171, -2), (key1171, -2), (key1222, -2), (key1222, -2), (key1224, -2), (key1224, -2), (key1175, 4), (key1224, 4), (key1224, 4)]

theorem rawRowCheck14961 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form5 = rawRow14961 := by decide +kernel

def row14961 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

theorem rowCheck14961 : row14961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14961 := by decide +kernel

theorem rowEval14961 (x : Key → ℝ) : Integer.Sparse.eval row14961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14961, Integer.Sparse.eval_collectBalanced, rawRowCheck14961]

def rawRow14962 : Integer.Sparse Key := [(key1185, 4), (key1096, 4), (key1185, 4), (key1185, -2), (key1186, -2), (key1100, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1222, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1224, 4), (key1175, 4), (key1224, 4)]

theorem rawRowCheck14962 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form5 = rawRow14962 := by decide +kernel

def row14962 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

theorem rowCheck14962 : row14962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14962 := by decide +kernel

theorem rowEval14962 (x : Key → ℝ) : Integer.Sparse.eval row14962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14962, Integer.Sparse.eval_collectBalanced, rawRowCheck14962]

def rawRow14963 : Integer.Sparse Key := [(key1185, 4), (key1185, 4), (key1096, 4), (key1186, -2), (key1185, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1100, -2), (key1224, -2), (key1222, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1171, -2), (key1224, 4), (key1224, 4), (key1175, 4)]

theorem rawRowCheck14963 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form5 = rawRow14963 := by decide +kernel

def row14963 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

theorem rowCheck14963 : row14963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14963 := by decide +kernel

theorem rowEval14963 (x : Key → ℝ) : Integer.Sparse.eval row14963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14963, Integer.Sparse.eval_collectBalanced, rawRowCheck14963]

def rawRow14964 : Integer.Sparse Key := [(key1100, 4), (key1100, 4), (key1186, 4), (key1096, -2), (key1100, -2), (key1096, -2), (key1185, -2), (key1100, -2), (key1185, -2), (key1171, -2), (key1175, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1224, -2), (key1171, 4), (key1171, 4), (key1222, 4)]

theorem rawRowCheck14964 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form5 = rawRow14964 := by decide +kernel

def row14964 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

theorem rowCheck14964 : row14964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14964 := by decide +kernel

theorem rowEval14964 (x : Key → ℝ) : Integer.Sparse.eval row14964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14964, Integer.Sparse.eval_collectBalanced, rawRowCheck14964]

def rawRow14965 : Integer.Sparse Key := [(key1100, 4), (key1186, 4), (key1100, 4), (key1100, -2), (key1096, -2), (key1185, -2), (key1096, -2), (key1185, -2), (key1100, -2), (key1175, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1171, 4), (key1222, 4), (key1171, 4)]

theorem rawRowCheck14965 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form5 = rawRow14965 := by decide +kernel

def row14965 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

theorem rowCheck14965 : row14965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14965 := by decide +kernel

theorem rowEval14965 (x : Key → ℝ) : Integer.Sparse.eval row14965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14965, Integer.Sparse.eval_collectBalanced, rawRowCheck14965]

def rawRow14966 : Integer.Sparse Key := [(key1186, 4), (key1100, 4), (key1100, 4), (key1185, -2), (key1185, -2), (key1100, -2), (key1100, -2), (key1096, -2), (key1096, -2), (key1224, -2), (key1224, -2), (key1175, -2), (key1175, -2), (key1171, -2), (key1171, -2), (key1222, 4), (key1171, 4), (key1171, 4)]

theorem rawRowCheck14966 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form5 = rawRow14966 := by decide +kernel

def row14966 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

theorem rowCheck14966 : row14966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14966 := by decide +kernel

theorem rowEval14966 (x : Key → ℝ) : Integer.Sparse.eval row14966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14966, Integer.Sparse.eval_collectBalanced, rawRowCheck14966]

def rawRow14967 : Integer.Sparse Key := [(key1096, 4), (key1185, 4), (key1185, 4), (key1171, -2), (key1171, -2), (key1222, -2), (key1222, -2), (key1224, -2), (key1224, -2), (key1100, -2), (key1100, -2), (key1185, -2), (key1185, -2), (key1186, -2), (key1186, -2), (key1175, 4), (key1224, 4), (key1224, 4)]

theorem rawRowCheck14967 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form5 = rawRow14967 := by decide +kernel

def row14967 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

theorem rowCheck14967 : row14967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14967 := by decide +kernel

theorem rowEval14967 (x : Key → ℝ) : Integer.Sparse.eval row14967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14967, Integer.Sparse.eval_collectBalanced, rawRowCheck14967]

def rawRow14968 : Integer.Sparse Key := [(key1185, 4), (key1096, 4), (key1185, 4), (key1222, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1185, -2), (key1186, -2), (key1100, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1224, 4), (key1175, 4), (key1224, 4)]

theorem rawRowCheck14968 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form5 = rawRow14968 := by decide +kernel

def row14968 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

theorem rowCheck14968 : row14968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14968 := by decide +kernel

theorem rowEval14968 (x : Key → ℝ) : Integer.Sparse.eval row14968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14968, Integer.Sparse.eval_collectBalanced, rawRowCheck14968]

def rawRow14969 : Integer.Sparse Key := [(key1185, 4), (key1185, 4), (key1096, 4), (key1224, -2), (key1222, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1171, -2), (key1186, -2), (key1185, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1100, -2), (key1224, 4), (key1224, 4), (key1175, 4)]

theorem rawRowCheck14969 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form5 = rawRow14969 := by decide +kernel

def row14969 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

theorem rowCheck14969 : row14969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14969 := by decide +kernel

theorem rowEval14969 (x : Key → ℝ) : Integer.Sparse.eval row14969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14969, Integer.Sparse.eval_collectBalanced, rawRowCheck14969]

def rawRow14970 : Integer.Sparse Key := [(key986, 4), (key1171, 4), (key1224, 4), (key982, -2), (key986, -2), (key1096, -2), (key1185, -2), (key1171, -2), (key1222, -2), (key986, -2), (key988, -2), (key1100, -2), (key1186, -2), (key1175, -2), (key1224, -2), (key986, 4), (key1100, 4), (key1185, 4)]

theorem rawRowCheck14970 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form5 = rawRow14970 := by decide +kernel

def row14970 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck14970 : row14970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14970 := by decide +kernel

theorem rowEval14970 (x : Key → ℝ) : Integer.Sparse.eval row14970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14970, Integer.Sparse.eval_collectBalanced, rawRowCheck14970]

def rawRow14971 : Integer.Sparse Key := [(key986, 4), (key1224, 4), (key1171, 4), (key986, -2), (key982, -2), (key1185, -2), (key1096, -2), (key1222, -2), (key1171, -2), (key988, -2), (key986, -2), (key1186, -2), (key1100, -2), (key1224, -2), (key1175, -2), (key986, 4), (key1185, 4), (key1100, 4)]

theorem rawRowCheck14971 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form5 = rawRow14971 := by decide +kernel

def row14971 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck14971 : row14971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14971 := by decide +kernel

theorem rowEval14971 (x : Key → ℝ) : Integer.Sparse.eval row14971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14971, Integer.Sparse.eval_collectBalanced, rawRowCheck14971]

def rawRow14972 : Integer.Sparse Key := [(key1171, 4), (key986, 4), (key1224, 4), (key1096, -2), (key1171, -2), (key982, -2), (key1222, -2), (key986, -2), (key1185, -2), (key1100, -2), (key1175, -2), (key986, -2), (key1224, -2), (key988, -2), (key1186, -2), (key1100, 4), (key986, 4), (key1185, 4)]

theorem rawRowCheck14972 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form5 = rawRow14972 := by decide +kernel

def row14972 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck14972 : row14972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14972 := by decide +kernel

theorem rowEval14972 (x : Key → ℝ) : Integer.Sparse.eval row14972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14972, Integer.Sparse.eval_collectBalanced, rawRowCheck14972]

def rawRow14973 : Integer.Sparse Key := [(key1171, 4), (key1224, 4), (key986, 4), (key1171, -2), (key1096, -2), (key1222, -2), (key982, -2), (key1185, -2), (key986, -2), (key1175, -2), (key1100, -2), (key1224, -2), (key986, -2), (key1186, -2), (key988, -2), (key1100, 4), (key1185, 4), (key986, 4)]

theorem rawRowCheck14973 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form5 = rawRow14973 := by decide +kernel

def row14973 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck14973 : row14973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14973 := by decide +kernel

theorem rowEval14973 (x : Key → ℝ) : Integer.Sparse.eval row14973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14973, Integer.Sparse.eval_collectBalanced, rawRowCheck14973]

def rawRow14974 : Integer.Sparse Key := [(key1224, 4), (key986, 4), (key1171, 4), (key1185, -2), (key1222, -2), (key986, -2), (key1171, -2), (key982, -2), (key1096, -2), (key1186, -2), (key1224, -2), (key988, -2), (key1175, -2), (key986, -2), (key1100, -2), (key1185, 4), (key986, 4), (key1100, 4)]

theorem rawRowCheck14974 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form5 = rawRow14974 := by decide +kernel

def row14974 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck14974 : row14974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14974 := by decide +kernel

theorem rowEval14974 (x : Key → ℝ) : Integer.Sparse.eval row14974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14974, Integer.Sparse.eval_collectBalanced, rawRowCheck14974]

def rawRow14975 : Integer.Sparse Key := [(key1224, 4), (key1171, 4), (key986, 4), (key1222, -2), (key1185, -2), (key1171, -2), (key986, -2), (key1096, -2), (key982, -2), (key1224, -2), (key1186, -2), (key1175, -2), (key988, -2), (key1100, -2), (key986, -2), (key1185, 4), (key1100, 4), (key986, 4)]

theorem rawRowCheck14975 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form5 = rawRow14975 := by decide +kernel

def row14975 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck14975 : row14975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14975 := by decide +kernel

theorem rowEval14975 (x : Key → ℝ) : Integer.Sparse.eval row14975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14975, Integer.Sparse.eval_collectBalanced, rawRowCheck14975]

end MUB6.Certificate.GramRows

end OAI
