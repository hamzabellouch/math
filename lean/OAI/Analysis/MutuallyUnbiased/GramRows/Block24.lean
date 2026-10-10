import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow864 : Integer.Sparse Key := [(key2626, -2), (key2635, -2), (key2626, -2), (key2626, 1), (key2635, 1), (key2610, 1), (key2635, 1), (key2610, 1), (key2626, 1), (key2780, 2), (key2789, 2), (key2780, 2), (key2780, -1), (key2789, -1), (key2665, -1), (key2789, -1), (key2665, -1), (key2780, -1), (key2853, -1), (key2855, -1), (key2803, -1), (key2855, -1), (key2803, -1), (key2853, -1), (key2853, 1), (key2855, 1), (key2700, 1), (key2855, 1), (key2700, 1), (key2853, 1)]

theorem rawRowCheck864 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form2 = rawRow864 := by decide +kernel

def row864 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

theorem rowCheck864 : row864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow864 := by decide +kernel

theorem rowEval864 (x : Key → ℝ) : Integer.Sparse.eval row864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck864, Integer.Sparse.eval_collectBalanced, rawRowCheck864]

def rawRow865 : Integer.Sparse Key := [(key2635, -2), (key2626, -2), (key2626, -2), (key2635, 1), (key2626, 1), (key2635, 1), (key2610, 1), (key2626, 1), (key2610, 1), (key2789, 2), (key2780, 2), (key2780, 2), (key2789, -1), (key2780, -1), (key2789, -1), (key2665, -1), (key2780, -1), (key2665, -1), (key2855, -1), (key2853, -1), (key2855, -1), (key2803, -1), (key2853, -1), (key2803, -1), (key2855, 1), (key2853, 1), (key2855, 1), (key2700, 1), (key2853, 1), (key2700, 1)]

theorem rawRowCheck865 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form2 = rawRow865 := by decide +kernel

def row865 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

theorem rowCheck865 : row865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow865 := by decide +kernel

theorem rowEval865 (x : Key → ℝ) : Integer.Sparse.eval row865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck865, Integer.Sparse.eval_collectBalanced, rawRowCheck865]

def rawRow866 : Integer.Sparse Key := [(key2665, -2), (key2665, -2), (key2665, -2), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2610, 2), (key2610, 2), (key2610, 2), (key2803, -1), (key2803, -1), (key2803, -1), (key2803, -1), (key2803, -1), (key2803, -1), (key2626, -1), (key2626, -1), (key2626, -1), (key2626, -1), (key2626, -1), (key2626, -1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1)]

theorem rawRowCheck866 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form2 = rawRow866 := by decide +kernel

def row866 : Integer.Sparse Key := [(key2610, 6), (key2626, -6), (key2665, -6), (key2700, 6), (key2780, 6), (key2803, -6)]

theorem rowCheck866 : row866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow866 := by decide +kernel

theorem rowEval866 (x : Key → ℝ) : Integer.Sparse.eval row866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck866, Integer.Sparse.eval_collectBalanced, rawRowCheck866]

def rawRow867 : Integer.Sparse Key := [(key2700, -2), (key2700, -2), (key2721, -2), (key2665, 1), (key2665, 1), (key2700, 1), (key2700, 1), (key2721, 1), (key2721, 1), (key2803, 2), (key2803, 2), (key2824, 2), (key2610, -1), (key2610, -1), (key2803, -1), (key2803, -1), (key2824, -1), (key2824, -1), (key2780, -1), (key2780, -1), (key2853, -1), (key2853, -1), (key2865, -1), (key2865, -1), (key2626, 1), (key2626, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1)]

theorem rawRowCheck867 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form2 = rawRow867 := by decide +kernel

def row867 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

theorem rowCheck867 : row867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow867 := by decide +kernel

theorem rowEval867 (x : Key → ℝ) : Integer.Sparse.eval row867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck867, Integer.Sparse.eval_collectBalanced, rawRowCheck867]

def rawRow868 : Integer.Sparse Key := [(key2700, -2), (key2721, -2), (key2700, -2), (key2700, 1), (key2721, 1), (key2665, 1), (key2721, 1), (key2665, 1), (key2700, 1), (key2803, 2), (key2824, 2), (key2803, 2), (key2803, -1), (key2824, -1), (key2610, -1), (key2824, -1), (key2610, -1), (key2803, -1), (key2853, -1), (key2865, -1), (key2780, -1), (key2865, -1), (key2780, -1), (key2853, -1), (key2853, 1), (key2865, 1), (key2626, 1), (key2865, 1), (key2626, 1), (key2853, 1)]

theorem rawRowCheck868 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form2 = rawRow868 := by decide +kernel

def row868 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

theorem rowCheck868 : row868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow868 := by decide +kernel

theorem rowEval868 (x : Key → ℝ) : Integer.Sparse.eval row868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck868, Integer.Sparse.eval_collectBalanced, rawRowCheck868]

def rawRow869 : Integer.Sparse Key := [(key2721, -2), (key2700, -2), (key2700, -2), (key2721, 1), (key2700, 1), (key2721, 1), (key2665, 1), (key2700, 1), (key2665, 1), (key2824, 2), (key2803, 2), (key2803, 2), (key2824, -1), (key2803, -1), (key2824, -1), (key2610, -1), (key2803, -1), (key2610, -1), (key2865, -1), (key2853, -1), (key2865, -1), (key2780, -1), (key2853, -1), (key2780, -1), (key2865, 1), (key2853, 1), (key2865, 1), (key2626, 1), (key2853, 1), (key2626, 1)]

theorem rawRowCheck869 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form2 = rawRow869 := by decide +kernel

def row869 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

theorem rowCheck869 : row869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow869 := by decide +kernel

theorem rowEval869 (x : Key → ℝ) : Integer.Sparse.eval row869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck869, Integer.Sparse.eval_collectBalanced, rawRowCheck869]

def rawRow870 : Integer.Sparse Key := [(key2780, -2), (key2780, -2), (key2789, -2), (key2803, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1), (key2626, 2), (key2626, 2), (key2635, 2), (key2700, -1), (key2700, -1), (key2853, -1), (key2853, -1), (key2855, -1), (key2855, -1), (key2610, -1), (key2610, -1), (key2626, -1), (key2626, -1), (key2635, -1), (key2635, -1), (key2665, 1), (key2665, 1), (key2780, 1), (key2780, 1), (key2789, 1), (key2789, 1)]

theorem rawRowCheck870 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form2 = rawRow870 := by decide +kernel

def row870 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

theorem rowCheck870 : row870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow870 := by decide +kernel

theorem rowEval870 (x : Key → ℝ) : Integer.Sparse.eval row870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck870, Integer.Sparse.eval_collectBalanced, rawRowCheck870]

def rawRow871 : Integer.Sparse Key := [(key2780, -2), (key2789, -2), (key2780, -2), (key2853, 1), (key2855, 1), (key2803, 1), (key2855, 1), (key2803, 1), (key2853, 1), (key2626, 2), (key2635, 2), (key2626, 2), (key2853, -1), (key2855, -1), (key2700, -1), (key2855, -1), (key2700, -1), (key2853, -1), (key2626, -1), (key2635, -1), (key2610, -1), (key2635, -1), (key2610, -1), (key2626, -1), (key2780, 1), (key2789, 1), (key2665, 1), (key2789, 1), (key2665, 1), (key2780, 1)]

theorem rawRowCheck871 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form2 = rawRow871 := by decide +kernel

def row871 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

theorem rowCheck871 : row871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow871 := by decide +kernel

theorem rowEval871 (x : Key → ℝ) : Integer.Sparse.eval row871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck871, Integer.Sparse.eval_collectBalanced, rawRowCheck871]

def rawRow872 : Integer.Sparse Key := [(key2789, -2), (key2780, -2), (key2780, -2), (key2855, 1), (key2853, 1), (key2855, 1), (key2803, 1), (key2853, 1), (key2803, 1), (key2635, 2), (key2626, 2), (key2626, 2), (key2855, -1), (key2853, -1), (key2855, -1), (key2700, -1), (key2853, -1), (key2700, -1), (key2635, -1), (key2626, -1), (key2635, -1), (key2610, -1), (key2626, -1), (key2610, -1), (key2789, 1), (key2780, 1), (key2789, 1), (key2665, 1), (key2780, 1), (key2665, 1)]

theorem rawRowCheck872 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form2 = rawRow872 := by decide +kernel

def row872 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

theorem rowCheck872 : row872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow872 := by decide +kernel

theorem rowEval872 (x : Key → ℝ) : Integer.Sparse.eval row872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck872, Integer.Sparse.eval_collectBalanced, rawRowCheck872]

def rawRow873 : Integer.Sparse Key := [(key2803, -2), (key2803, -2), (key2824, -2), (key2780, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1), (key2700, 2), (key2700, 2), (key2721, 2), (key2626, -1), (key2626, -1), (key2853, -1), (key2853, -1), (key2865, -1), (key2865, -1), (key2665, -1), (key2665, -1), (key2700, -1), (key2700, -1), (key2721, -1), (key2721, -1), (key2610, 1), (key2610, 1), (key2803, 1), (key2803, 1), (key2824, 1), (key2824, 1)]

theorem rawRowCheck873 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form2 = rawRow873 := by decide +kernel

def row873 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

theorem rowCheck873 : row873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow873 := by decide +kernel

theorem rowEval873 (x : Key → ℝ) : Integer.Sparse.eval row873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck873, Integer.Sparse.eval_collectBalanced, rawRowCheck873]

def rawRow874 : Integer.Sparse Key := [(key2803, -2), (key2824, -2), (key2803, -2), (key2853, 1), (key2865, 1), (key2780, 1), (key2865, 1), (key2780, 1), (key2853, 1), (key2700, 2), (key2721, 2), (key2700, 2), (key2853, -1), (key2865, -1), (key2626, -1), (key2865, -1), (key2626, -1), (key2853, -1), (key2700, -1), (key2721, -1), (key2665, -1), (key2721, -1), (key2665, -1), (key2700, -1), (key2803, 1), (key2824, 1), (key2610, 1), (key2824, 1), (key2610, 1), (key2803, 1)]

theorem rawRowCheck874 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form2 = rawRow874 := by decide +kernel

def row874 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

theorem rowCheck874 : row874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow874 := by decide +kernel

theorem rowEval874 (x : Key → ℝ) : Integer.Sparse.eval row874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck874, Integer.Sparse.eval_collectBalanced, rawRowCheck874]

def rawRow875 : Integer.Sparse Key := [(key2824, -2), (key2803, -2), (key2803, -2), (key2865, 1), (key2853, 1), (key2865, 1), (key2780, 1), (key2853, 1), (key2780, 1), (key2721, 2), (key2700, 2), (key2700, 2), (key2865, -1), (key2853, -1), (key2865, -1), (key2626, -1), (key2853, -1), (key2626, -1), (key2721, -1), (key2700, -1), (key2721, -1), (key2665, -1), (key2700, -1), (key2665, -1), (key2824, 1), (key2803, 1), (key2824, 1), (key2610, 1), (key2803, 1), (key2610, 1)]

theorem rawRowCheck875 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form2 = rawRow875 := by decide +kernel

def row875 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

theorem rowCheck875 : row875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow875 := by decide +kernel

theorem rowEval875 (x : Key → ℝ) : Integer.Sparse.eval row875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck875, Integer.Sparse.eval_collectBalanced, rawRowCheck875]

def rawRow876 : Integer.Sparse Key := [(key995, -2), (key995, -2), (key995, -2), (key1011, 6), (key1030, 2), (key1030, 2), (key1030, 2), (key1119, -2), (key1119, -2), (key1119, -2), (key1067, -6), (key1146, 2), (key1146, 2), (key1146, 2)]

theorem rawRowCheck876 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form3 = rawRow876 := by decide +kernel

def row876 : Integer.Sparse Key := [(key995, -6), (key1011, 6), (key1030, 6), (key1067, -6), (key1119, -6), (key1146, 6)]

theorem rowCheck876 : row876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow876 := by decide +kernel

theorem rowEval876 (x : Key → ℝ) : Integer.Sparse.eval row876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck876, Integer.Sparse.eval_collectBalanced, rawRowCheck876]

def rawRow877 : Integer.Sparse Key := [(key995, -2), (key995, -2), (key1011, -2), (key995, 6), (key1108, 2), (key1108, 2), (key1119, 2), (key1030, -2), (key1108, -2), (key1108, -2), (key1146, -6), (key1067, 2), (key1146, 2), (key1146, 2)]

theorem rawRowCheck877 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form3 = rawRow877 := by decide +kernel

def row877 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

theorem rowCheck877 : row877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow877 := by decide +kernel

theorem rowEval877 (x : Key → ℝ) : Integer.Sparse.eval row877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck877, Integer.Sparse.eval_collectBalanced, rawRowCheck877]

def rawRow878 : Integer.Sparse Key := [(key995, -2), (key1011, -2), (key995, -2), (key995, 6), (key1108, 2), (key1119, 2), (key1108, 2), (key1108, -2), (key1030, -2), (key1108, -2), (key1146, -6), (key1146, 2), (key1067, 2), (key1146, 2)]

theorem rawRowCheck878 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form3 = rawRow878 := by decide +kernel

def row878 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

theorem rowCheck878 : row878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow878 := by decide +kernel

theorem rowEval878 (x : Key → ℝ) : Integer.Sparse.eval row878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck878, Integer.Sparse.eval_collectBalanced, rawRowCheck878]

def rawRow879 : Integer.Sparse Key := [(key1011, -2), (key995, -2), (key995, -2), (key995, 6), (key1119, 2), (key1108, 2), (key1108, 2), (key1108, -2), (key1108, -2), (key1030, -2), (key1146, -6), (key1146, 2), (key1146, 2), (key1067, 2)]

theorem rawRowCheck879 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form3 = rawRow879 := by decide +kernel

def row879 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

theorem rowCheck879 : row879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow879 := by decide +kernel

theorem rowEval879 (x : Key → ℝ) : Integer.Sparse.eval row879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck879, Integer.Sparse.eval_collectBalanced, rawRowCheck879]

def rawRow880 : Integer.Sparse Key := [(key1030, -2), (key1030, -2), (key1030, -2), (key1067, 6), (key995, 2), (key995, 2), (key995, 2), (key1146, -2), (key1146, -2), (key1146, -2), (key1011, -6), (key1119, 2), (key1119, 2), (key1119, 2)]

theorem rawRowCheck880 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form3 = rawRow880 := by decide +kernel

def row880 : Integer.Sparse Key := [(key995, 6), (key1011, -6), (key1030, -6), (key1067, 6), (key1119, 6), (key1146, -6)]

theorem rowCheck880 : row880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow880 := by decide +kernel

theorem rowEval880 (x : Key → ℝ) : Integer.Sparse.eval row880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck880, Integer.Sparse.eval_collectBalanced, rawRowCheck880]

def rawRow881 : Integer.Sparse Key := [(key1030, -2), (key1030, -2), (key1067, -2), (key1030, 6), (key1108, 2), (key1108, 2), (key1146, 2), (key995, -2), (key1108, -2), (key1108, -2), (key1119, -6), (key1011, 2), (key1119, 2), (key1119, 2)]

theorem rawRowCheck881 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form3 = rawRow881 := by decide +kernel

def row881 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

theorem rowCheck881 : row881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow881 := by decide +kernel

theorem rowEval881 (x : Key → ℝ) : Integer.Sparse.eval row881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck881, Integer.Sparse.eval_collectBalanced, rawRowCheck881]

def rawRow882 : Integer.Sparse Key := [(key1030, -2), (key1067, -2), (key1030, -2), (key1030, 6), (key1108, 2), (key1146, 2), (key1108, 2), (key1108, -2), (key995, -2), (key1108, -2), (key1119, -6), (key1119, 2), (key1011, 2), (key1119, 2)]

theorem rawRowCheck882 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form3 = rawRow882 := by decide +kernel

def row882 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

theorem rowCheck882 : row882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow882 := by decide +kernel

theorem rowEval882 (x : Key → ℝ) : Integer.Sparse.eval row882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck882, Integer.Sparse.eval_collectBalanced, rawRowCheck882]

def rawRow883 : Integer.Sparse Key := [(key1067, -2), (key1030, -2), (key1030, -2), (key1030, 6), (key1146, 2), (key1108, 2), (key1108, 2), (key1108, -2), (key1108, -2), (key995, -2), (key1119, -6), (key1119, 2), (key1119, 2), (key1011, 2)]

theorem rawRowCheck883 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form3 = rawRow883 := by decide +kernel

def row883 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

theorem rowCheck883 : row883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow883 := by decide +kernel

theorem rowEval883 (x : Key → ℝ) : Integer.Sparse.eval row883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck883, Integer.Sparse.eval_collectBalanced, rawRowCheck883]

def rawRow884 : Integer.Sparse Key := [(key1108, -2), (key1108, -2), (key1119, -2), (key1146, 6), (key995, 2), (key995, 2), (key1011, 2), (key1067, -2), (key1146, -2), (key1146, -2), (key995, -6), (key1030, 2), (key1108, 2), (key1108, 2)]

theorem rawRowCheck884 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form3 = rawRow884 := by decide +kernel

def row884 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

theorem rowCheck884 : row884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow884 := by decide +kernel

theorem rowEval884 (x : Key → ℝ) : Integer.Sparse.eval row884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck884, Integer.Sparse.eval_collectBalanced, rawRowCheck884]

def rawRow885 : Integer.Sparse Key := [(key1108, -2), (key1119, -2), (key1108, -2), (key1146, 6), (key995, 2), (key1011, 2), (key995, 2), (key1146, -2), (key1067, -2), (key1146, -2), (key995, -6), (key1108, 2), (key1030, 2), (key1108, 2)]

theorem rawRowCheck885 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form3 = rawRow885 := by decide +kernel

def row885 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

theorem rowCheck885 : row885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow885 := by decide +kernel

theorem rowEval885 (x : Key → ℝ) : Integer.Sparse.eval row885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck885, Integer.Sparse.eval_collectBalanced, rawRowCheck885]

def rawRow886 : Integer.Sparse Key := [(key1119, -2), (key1108, -2), (key1108, -2), (key1146, 6), (key1011, 2), (key995, 2), (key995, 2), (key1146, -2), (key1146, -2), (key1067, -2), (key995, -6), (key1108, 2), (key1108, 2), (key1030, 2)]

theorem rawRowCheck886 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form3 = rawRow886 := by decide +kernel

def row886 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

theorem rowCheck886 : row886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow886 := by decide +kernel

theorem rowEval886 (x : Key → ℝ) : Integer.Sparse.eval row886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck886, Integer.Sparse.eval_collectBalanced, rawRowCheck886]

def rawRow887 : Integer.Sparse Key := [(key1108, -2), (key1108, -2), (key1146, -2), (key1119, 6), (key1030, 2), (key1030, 2), (key1067, 2), (key1011, -2), (key1119, -2), (key1119, -2), (key1030, -6), (key995, 2), (key1108, 2), (key1108, 2)]

theorem rawRowCheck887 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow887 := by decide +kernel

def row887 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

theorem rowCheck887 : row887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow887 := by decide +kernel

theorem rowEval887 (x : Key → ℝ) : Integer.Sparse.eval row887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck887, Integer.Sparse.eval_collectBalanced, rawRowCheck887]

def rawRow888 : Integer.Sparse Key := [(key1108, -2), (key1146, -2), (key1108, -2), (key1119, 6), (key1030, 2), (key1067, 2), (key1030, 2), (key1119, -2), (key1011, -2), (key1119, -2), (key1030, -6), (key1108, 2), (key995, 2), (key1108, 2)]

theorem rawRowCheck888 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow888 := by decide +kernel

def row888 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

theorem rowCheck888 : row888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow888 := by decide +kernel

theorem rowEval888 (x : Key → ℝ) : Integer.Sparse.eval row888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck888, Integer.Sparse.eval_collectBalanced, rawRowCheck888]

def rawRow889 : Integer.Sparse Key := [(key1146, -2), (key1108, -2), (key1108, -2), (key1119, 6), (key1067, 2), (key1030, 2), (key1030, 2), (key1119, -2), (key1119, -2), (key1011, -2), (key1030, -6), (key1108, 2), (key1108, 2), (key995, 2)]

theorem rawRowCheck889 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow889 := by decide +kernel

def row889 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

theorem rowCheck889 : row889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow889 := by decide +kernel

theorem rowEval889 (x : Key → ℝ) : Integer.Sparse.eval row889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck889, Integer.Sparse.eval_collectBalanced, rawRowCheck889]

def rawRow890 : Integer.Sparse Key := [(key2606, -6), (key2622, 2), (key2622, 2), (key2622, 2), (key2661, 6), (key2696, -2), (key2696, -2), (key2696, -2), (key2776, -2), (key2776, -2), (key2776, -2), (key2799, 2), (key2799, 2), (key2799, 2)]

theorem rawRowCheck890 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form4 = rawRow890 := by decide +kernel

def row890 : Integer.Sparse Key := [(key2606, -6), (key2622, 6), (key2661, 6), (key2696, -6), (key2776, -6), (key2799, 6)]

theorem rowCheck890 : row890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow890 := by decide +kernel

theorem rowEval890 (x : Key → ℝ) : Integer.Sparse.eval row890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck890, Integer.Sparse.eval_collectBalanced, rawRowCheck890]

def rawRow891 : Integer.Sparse Key := [(key2622, -6), (key2606, 2), (key2622, 2), (key2622, 2), (key2696, 6), (key2661, -2), (key2696, -2), (key2696, -2), (key2799, -2), (key2849, -2), (key2849, -2), (key2776, 2), (key2849, 2), (key2849, 2)]

theorem rawRowCheck891 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form4 = rawRow891 := by decide +kernel

def row891 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

theorem rowCheck891 : row891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow891 := by decide +kernel

theorem rowEval891 (x : Key → ℝ) : Integer.Sparse.eval row891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck891, Integer.Sparse.eval_collectBalanced, rawRowCheck891]

def rawRow892 : Integer.Sparse Key := [(key2622, -6), (key2622, 2), (key2606, 2), (key2622, 2), (key2696, 6), (key2696, -2), (key2661, -2), (key2696, -2), (key2849, -2), (key2799, -2), (key2849, -2), (key2849, 2), (key2776, 2), (key2849, 2)]

theorem rawRowCheck892 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form4 = rawRow892 := by decide +kernel

def row892 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

theorem rowCheck892 : row892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow892 := by decide +kernel

theorem rowEval892 (x : Key → ℝ) : Integer.Sparse.eval row892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck892, Integer.Sparse.eval_collectBalanced, rawRowCheck892]

def rawRow893 : Integer.Sparse Key := [(key2622, -6), (key2622, 2), (key2622, 2), (key2606, 2), (key2696, 6), (key2696, -2), (key2696, -2), (key2661, -2), (key2849, -2), (key2849, -2), (key2799, -2), (key2849, 2), (key2849, 2), (key2776, 2)]

theorem rawRowCheck893 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form4 = rawRow893 := by decide +kernel

def row893 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

theorem rowCheck893 : row893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow893 := by decide +kernel

theorem rowEval893 (x : Key → ℝ) : Integer.Sparse.eval row893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck893, Integer.Sparse.eval_collectBalanced, rawRowCheck893]

def rawRow894 : Integer.Sparse Key := [(key2661, -6), (key2696, 2), (key2696, 2), (key2696, 2), (key2606, 6), (key2799, -2), (key2799, -2), (key2799, -2), (key2622, -2), (key2622, -2), (key2622, -2), (key2696, 2), (key2696, 2), (key2696, 2)]

theorem rawRowCheck894 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form4 = rawRow894 := by decide +kernel

def row894 : Integer.Sparse Key := [(key2606, 6), (key2622, -6), (key2661, -6), (key2696, 12), (key2799, -6)]

theorem rowCheck894 : row894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow894 := by decide +kernel

theorem rowEval894 (x : Key → ℝ) : Integer.Sparse.eval row894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck894, Integer.Sparse.eval_collectBalanced, rawRowCheck894]

def rawRow895 : Integer.Sparse Key := [(key2696, -6), (key2661, 2), (key2696, 2), (key2696, 2), (key2799, 6), (key2606, -2), (key2799, -2), (key2799, -2), (key2696, -2), (key2849, -2), (key2849, -2), (key2622, 2), (key2849, 2), (key2849, 2)]

theorem rawRowCheck895 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form4 = rawRow895 := by decide +kernel

def row895 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, -4), (key2799, 2)]

theorem rowCheck895 : row895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow895 := by decide +kernel

theorem rowEval895 (x : Key → ℝ) : Integer.Sparse.eval row895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck895, Integer.Sparse.eval_collectBalanced, rawRowCheck895]

end MUB6.Certificate.GramRows

end OAI
