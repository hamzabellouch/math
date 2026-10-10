import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
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

def rawRow4864 : Integer.Sparse Key := [(key2805, -2), (key2831, -2), (key2805, -2), (key2893, 1), (key2904, 1), (key2782, 1), (key2904, 1), (key2782, 1), (key2893, 1), (key2702, 2), (key2728, 2), (key2702, 2), (key2972, -1), (key2983, -1), (key2628, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1)]

theorem rawRowCheck4864 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form2 = rawRow4864 := by decide +kernel

def row4864 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -2), (key2667, -2), (key2702, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, 2), (key2805, -4), (key2829, 1), (key2831, -2), (key2893, 2), (key2904, 2), (key2948, 1), (key2960, 2), (key2972, -2), (key2983, -2)]

theorem rowCheck4864 : row4864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4864 := by decide +kernel

theorem rowEval4864 (x : Key → ℝ) : Integer.Sparse.eval row4864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck4864, Integer.Sparse.eval_collectBalanced, rawRowCheck4864]

def rawRow4865 : Integer.Sparse Key := [(key2831, -2), (key2805, -2), (key2805, -2), (key2904, 1), (key2893, 1), (key2904, 1), (key2782, 1), (key2893, 1), (key2782, 1), (key2728, 2), (key2702, 2), (key2702, 2), (key2983, -1), (key2972, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2747, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2667, -1), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1)]

theorem rawRowCheck4865 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form2 = rawRow4865 := by decide +kernel

def row4865 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -2), (key2667, -2), (key2702, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, 2), (key2805, -4), (key2829, 1), (key2831, -2), (key2893, 2), (key2904, 2), (key2948, 1), (key2960, 2), (key2972, -2), (key2983, -2)]

theorem rowCheck4865 : row4865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4865 := by decide +kernel

theorem rowEval4865 (x : Key → ℝ) : Integer.Sparse.eval row4865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck4865, Integer.Sparse.eval_collectBalanced, rawRowCheck4865]

def rawRow4866 : Integer.Sparse Key := [(key998, -2), (key998, -2), (key1006, -2), (key1019, 6), (key1033, 2), (key1033, 2), (key1041, 2), (key1127, -2), (key1199, -2), (key1199, -2), (key1076, -6), (key1155, 2), (key1212, 2), (key1212, 2)]

theorem rawRowCheck4866 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form3 = rawRow4866 := by decide +kernel

def row4866 : Integer.Sparse Key := [(key998, -4), (key1006, -2), (key1019, 6), (key1033, 4), (key1041, 2), (key1076, -6), (key1127, -2), (key1155, 2), (key1199, -4), (key1212, 4)]

theorem rowCheck4866 : row4866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4866 := by decide +kernel

theorem rowEval4866 (x : Key → ℝ) : Integer.Sparse.eval row4866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4866, Integer.Sparse.eval_collectBalanced, rawRowCheck4866]

def rawRow4867 : Integer.Sparse Key := [(key998, -2), (key1006, -2), (key998, -2), (key1019, 6), (key1033, 2), (key1041, 2), (key1033, 2), (key1199, -2), (key1127, -2), (key1199, -2), (key1076, -6), (key1212, 2), (key1155, 2), (key1212, 2)]

theorem rawRowCheck4867 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form3 = rawRow4867 := by decide +kernel

def row4867 : Integer.Sparse Key := [(key998, -4), (key1006, -2), (key1019, 6), (key1033, 4), (key1041, 2), (key1076, -6), (key1127, -2), (key1155, 2), (key1199, -4), (key1212, 4)]

theorem rowCheck4867 : row4867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4867 := by decide +kernel

theorem rowEval4867 (x : Key → ℝ) : Integer.Sparse.eval row4867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4867, Integer.Sparse.eval_collectBalanced, rawRowCheck4867]

def rawRow4868 : Integer.Sparse Key := [(key1006, -2), (key998, -2), (key998, -2), (key1019, 6), (key1041, 2), (key1033, 2), (key1033, 2), (key1199, -2), (key1199, -2), (key1127, -2), (key1076, -6), (key1212, 2), (key1212, 2), (key1155, 2)]

theorem rawRowCheck4868 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form3 = rawRow4868 := by decide +kernel

def row4868 : Integer.Sparse Key := [(key998, -4), (key1006, -2), (key1019, 6), (key1033, 4), (key1041, 2), (key1076, -6), (key1127, -2), (key1155, 2), (key1199, -4), (key1212, 4)]

theorem rowCheck4868 : row4868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4868 := by decide +kernel

theorem rowEval4868 (x : Key → ℝ) : Integer.Sparse.eval row4868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4868, Integer.Sparse.eval_collectBalanced, rawRowCheck4868]

def rawRow4869 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1041, -2), (key1076, 6), (key998, 2), (key998, 2), (key1006, 2), (key1155, -2), (key1212, -2), (key1212, -2), (key1019, -6), (key1127, 2), (key1199, 2), (key1199, 2)]

theorem rawRowCheck4869 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form3 = rawRow4869 := by decide +kernel

def row4869 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1019, -6), (key1033, -4), (key1041, -2), (key1076, 6), (key1127, 2), (key1155, -2), (key1199, 4), (key1212, -4)]

theorem rowCheck4869 : row4869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4869 := by decide +kernel

theorem rowEval4869 (x : Key → ℝ) : Integer.Sparse.eval row4869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4869, Integer.Sparse.eval_collectBalanced, rawRowCheck4869]

def rawRow4870 : Integer.Sparse Key := [(key1033, -2), (key1041, -2), (key1033, -2), (key1076, 6), (key998, 2), (key1006, 2), (key998, 2), (key1212, -2), (key1155, -2), (key1212, -2), (key1019, -6), (key1199, 2), (key1127, 2), (key1199, 2)]

theorem rawRowCheck4870 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form3 = rawRow4870 := by decide +kernel

def row4870 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1019, -6), (key1033, -4), (key1041, -2), (key1076, 6), (key1127, 2), (key1155, -2), (key1199, 4), (key1212, -4)]

theorem rowCheck4870 : row4870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4870 := by decide +kernel

theorem rowEval4870 (x : Key → ℝ) : Integer.Sparse.eval row4870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4870, Integer.Sparse.eval_collectBalanced, rawRowCheck4870]

def rawRow4871 : Integer.Sparse Key := [(key1041, -2), (key1033, -2), (key1033, -2), (key1076, 6), (key1006, 2), (key998, 2), (key998, 2), (key1212, -2), (key1212, -2), (key1155, -2), (key1019, -6), (key1199, 2), (key1199, 2), (key1127, 2)]

theorem rawRowCheck4871 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form3 = rawRow4871 := by decide +kernel

def row4871 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1019, -6), (key1033, -4), (key1041, -2), (key1076, 6), (key1127, 2), (key1155, -2), (key1199, 4), (key1212, -4)]

theorem rowCheck4871 : row4871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4871 := by decide +kernel

theorem rowEval4871 (x : Key → ℝ) : Integer.Sparse.eval row4871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4871, Integer.Sparse.eval_collectBalanced, rawRowCheck4871]

def rawRow4872 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1076, -2), (key1041, 6), (key1111, 2), (key1111, 2), (key1155, 2), (key1006, -2), (key1193, -2), (key1193, -2), (key1127, -6), (key1019, 2), (key1199, 2), (key1199, 2)]

theorem rawRowCheck4872 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form3 = rawRow4872 := by decide +kernel

def row4872 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, 4), (key1127, -6), (key1155, 2), (key1193, -4), (key1199, 4)]

theorem rowCheck4872 : row4872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4872 := by decide +kernel

theorem rowEval4872 (x : Key → ℝ) : Integer.Sparse.eval row4872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4872, Integer.Sparse.eval_collectBalanced, rawRowCheck4872]

def rawRow4873 : Integer.Sparse Key := [(key1033, -2), (key1076, -2), (key1033, -2), (key1041, 6), (key1111, 2), (key1155, 2), (key1111, 2), (key1193, -2), (key1006, -2), (key1193, -2), (key1127, -6), (key1199, 2), (key1019, 2), (key1199, 2)]

theorem rawRowCheck4873 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form3 = rawRow4873 := by decide +kernel

def row4873 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, 4), (key1127, -6), (key1155, 2), (key1193, -4), (key1199, 4)]

theorem rowCheck4873 : row4873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4873 := by decide +kernel

theorem rowEval4873 (x : Key → ℝ) : Integer.Sparse.eval row4873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4873, Integer.Sparse.eval_collectBalanced, rawRowCheck4873]

def rawRow4874 : Integer.Sparse Key := [(key1076, -2), (key1033, -2), (key1033, -2), (key1041, 6), (key1155, 2), (key1111, 2), (key1111, 2), (key1193, -2), (key1193, -2), (key1006, -2), (key1127, -6), (key1199, 2), (key1199, 2), (key1019, 2)]

theorem rawRowCheck4874 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form3 = rawRow4874 := by decide +kernel

def row4874 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, 4), (key1127, -6), (key1155, 2), (key1193, -4), (key1199, 4)]

theorem rowCheck4874 : row4874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4874 := by decide +kernel

theorem rowEval4874 (x : Key → ℝ) : Integer.Sparse.eval row4874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4874, Integer.Sparse.eval_collectBalanced, rawRowCheck4874]

def rawRow4875 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1155, -2), (key1127, 6), (key1033, 2), (key1033, 2), (key1076, 2), (key1019, -2), (key1199, -2), (key1199, -2), (key1041, -6), (key1006, 2), (key1193, 2), (key1193, 2)]

theorem rawRowCheck4875 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form3 = rawRow4875 := by decide +kernel

def row4875 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -6), (key1076, 2), (key1111, -4), (key1127, 6), (key1155, -2), (key1193, 4), (key1199, -4)]

theorem rowCheck4875 : row4875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4875 := by decide +kernel

theorem rowEval4875 (x : Key → ℝ) : Integer.Sparse.eval row4875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4875, Integer.Sparse.eval_collectBalanced, rawRowCheck4875]

def rawRow4876 : Integer.Sparse Key := [(key1111, -2), (key1155, -2), (key1111, -2), (key1127, 6), (key1033, 2), (key1076, 2), (key1033, 2), (key1199, -2), (key1019, -2), (key1199, -2), (key1041, -6), (key1193, 2), (key1006, 2), (key1193, 2)]

theorem rawRowCheck4876 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form3 = rawRow4876 := by decide +kernel

def row4876 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -6), (key1076, 2), (key1111, -4), (key1127, 6), (key1155, -2), (key1193, 4), (key1199, -4)]

theorem rowCheck4876 : row4876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4876 := by decide +kernel

theorem rowEval4876 (x : Key → ℝ) : Integer.Sparse.eval row4876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4876, Integer.Sparse.eval_collectBalanced, rawRowCheck4876]

def rawRow4877 : Integer.Sparse Key := [(key1155, -2), (key1111, -2), (key1111, -2), (key1127, 6), (key1076, 2), (key1033, 2), (key1033, 2), (key1199, -2), (key1199, -2), (key1019, -2), (key1041, -6), (key1193, 2), (key1193, 2), (key1006, 2)]

theorem rawRowCheck4877 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form3 = rawRow4877 := by decide +kernel

def row4877 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -6), (key1076, 2), (key1111, -4), (key1127, 6), (key1155, -2), (key1193, 4), (key1199, -4)]

theorem rowCheck4877 : row4877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4877 := by decide +kernel

theorem rowEval4877 (x : Key → ℝ) : Integer.Sparse.eval row4877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4877, Integer.Sparse.eval_collectBalanced, rawRowCheck4877]

def rawRow4878 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 2), (key2639, 2), (key2670, 6), (key2705, -2), (key2725, -2), (key2725, -2), (key2785, -2), (key2793, -2), (key2793, -2), (key2808, 2), (key2828, 2), (key2828, 2)]

theorem rawRowCheck4878 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form4 = rawRow4878 := by decide +kernel

def row4878 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2670, 6), (key2705, -2), (key2725, -4), (key2785, -2), (key2793, -4), (key2808, 2), (key2828, 4)]

theorem rowCheck4878 : row4878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4878 := by decide +kernel

theorem rowEval4878 (x : Key → ℝ) : Integer.Sparse.eval row4878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4878, Integer.Sparse.eval_collectBalanced, rawRowCheck4878]

def rawRow4879 : Integer.Sparse Key := [(key2615, -6), (key2639, 2), (key2631, 2), (key2639, 2), (key2670, 6), (key2725, -2), (key2705, -2), (key2725, -2), (key2793, -2), (key2785, -2), (key2793, -2), (key2828, 2), (key2808, 2), (key2828, 2)]

theorem rawRowCheck4879 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form4 = rawRow4879 := by decide +kernel

def row4879 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2670, 6), (key2705, -2), (key2725, -4), (key2785, -2), (key2793, -4), (key2808, 2), (key2828, 4)]

theorem rowCheck4879 : row4879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4879 := by decide +kernel

theorem rowEval4879 (x : Key → ℝ) : Integer.Sparse.eval row4879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4879, Integer.Sparse.eval_collectBalanced, rawRowCheck4879]

def rawRow4880 : Integer.Sparse Key := [(key2615, -6), (key2639, 2), (key2639, 2), (key2631, 2), (key2670, 6), (key2725, -2), (key2725, -2), (key2705, -2), (key2793, -2), (key2793, -2), (key2785, -2), (key2828, 2), (key2828, 2), (key2808, 2)]

theorem rawRowCheck4880 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form4 = rawRow4880 := by decide +kernel

def row4880 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2670, 6), (key2705, -2), (key2725, -4), (key2785, -2), (key2793, -4), (key2808, 2), (key2828, 4)]

theorem rowCheck4880 : row4880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4880 := by decide +kernel

theorem rowEval4880 (x : Key → ℝ) : Integer.Sparse.eval row4880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4880, Integer.Sparse.eval_collectBalanced, rawRowCheck4880]

def rawRow4881 : Integer.Sparse Key := [(key2670, -6), (key2785, 2), (key2793, 2), (key2793, 2), (key2615, 6), (key2808, -2), (key2828, -2), (key2828, -2), (key2631, -2), (key2639, -2), (key2639, -2), (key2705, 2), (key2725, 2), (key2725, 2)]

theorem rawRowCheck4881 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form4 = rawRow4881 := by decide +kernel

def row4881 : Integer.Sparse Key := [(key2615, 6), (key2631, -2), (key2639, -4), (key2670, -6), (key2705, 2), (key2725, 4), (key2785, 2), (key2793, 4), (key2808, -2), (key2828, -4)]

theorem rowCheck4881 : row4881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4881 := by decide +kernel

theorem rowEval4881 (x : Key → ℝ) : Integer.Sparse.eval row4881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4881, Integer.Sparse.eval_collectBalanced, rawRowCheck4881]

def rawRow4882 : Integer.Sparse Key := [(key2670, -6), (key2793, 2), (key2785, 2), (key2793, 2), (key2615, 6), (key2828, -2), (key2808, -2), (key2828, -2), (key2639, -2), (key2631, -2), (key2639, -2), (key2725, 2), (key2705, 2), (key2725, 2)]

theorem rawRowCheck4882 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form4 = rawRow4882 := by decide +kernel

def row4882 : Integer.Sparse Key := [(key2615, 6), (key2631, -2), (key2639, -4), (key2670, -6), (key2705, 2), (key2725, 4), (key2785, 2), (key2793, 4), (key2808, -2), (key2828, -4)]

theorem rowCheck4882 : row4882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4882 := by decide +kernel

theorem rowEval4882 (x : Key → ℝ) : Integer.Sparse.eval row4882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4882, Integer.Sparse.eval_collectBalanced, rawRowCheck4882]

def rawRow4883 : Integer.Sparse Key := [(key2670, -6), (key2793, 2), (key2793, 2), (key2785, 2), (key2615, 6), (key2828, -2), (key2828, -2), (key2808, -2), (key2639, -2), (key2639, -2), (key2631, -2), (key2725, 2), (key2725, 2), (key2705, 2)]

theorem rawRowCheck4883 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form4 = rawRow4883 := by decide +kernel

def row4883 : Integer.Sparse Key := [(key2615, 6), (key2631, -2), (key2639, -4), (key2670, -6), (key2705, 2), (key2725, 4), (key2785, 2), (key2793, 4), (key2808, -2), (key2828, -4)]

theorem rowCheck4883 : row4883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4883 := by decide +kernel

theorem rowEval4883 (x : Key → ℝ) : Integer.Sparse.eval row4883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4883, Integer.Sparse.eval_collectBalanced, rawRowCheck4883]

def rawRow4884 : Integer.Sparse Key := [(key2785, -6), (key2670, 2), (key2793, 2), (key2793, 2), (key2808, 6), (key2615, -2), (key2828, -2), (key2828, -2), (key2705, -2), (key2859, -2), (key2859, -2), (key2631, 2), (key2869, 2), (key2869, 2)]

theorem rawRowCheck4884 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form4 = rawRow4884 := by decide +kernel

def row4884 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, 2), (key2705, -2), (key2785, -6), (key2793, 4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, 4)]

theorem rowCheck4884 : row4884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4884 := by decide +kernel

theorem rowEval4884 (x : Key → ℝ) : Integer.Sparse.eval row4884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4884, Integer.Sparse.eval_collectBalanced, rawRowCheck4884]

def rawRow4885 : Integer.Sparse Key := [(key2785, -6), (key2793, 2), (key2670, 2), (key2793, 2), (key2808, 6), (key2828, -2), (key2615, -2), (key2828, -2), (key2859, -2), (key2705, -2), (key2859, -2), (key2869, 2), (key2631, 2), (key2869, 2)]

theorem rawRowCheck4885 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form4 = rawRow4885 := by decide +kernel

def row4885 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, 2), (key2705, -2), (key2785, -6), (key2793, 4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, 4)]

theorem rowCheck4885 : row4885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4885 := by decide +kernel

theorem rowEval4885 (x : Key → ℝ) : Integer.Sparse.eval row4885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4885, Integer.Sparse.eval_collectBalanced, rawRowCheck4885]

def rawRow4886 : Integer.Sparse Key := [(key2785, -6), (key2793, 2), (key2793, 2), (key2670, 2), (key2808, 6), (key2828, -2), (key2828, -2), (key2615, -2), (key2859, -2), (key2859, -2), (key2705, -2), (key2869, 2), (key2869, 2), (key2631, 2)]

theorem rawRowCheck4886 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form4 = rawRow4886 := by decide +kernel

def row4886 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, 2), (key2705, -2), (key2785, -6), (key2793, 4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, 4)]

theorem rowCheck4886 : row4886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4886 := by decide +kernel

theorem rowEval4886 (x : Key → ℝ) : Integer.Sparse.eval row4886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4886, Integer.Sparse.eval_collectBalanced, rawRowCheck4886]

def rawRow4887 : Integer.Sparse Key := [(key2808, -6), (key2705, 2), (key2859, 2), (key2859, 2), (key2785, 6), (key2631, -2), (key2869, -2), (key2869, -2), (key2670, -2), (key2793, -2), (key2793, -2), (key2615, 2), (key2828, 2), (key2828, 2)]

theorem rawRowCheck4887 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form4 = rawRow4887 := by decide +kernel

def row4887 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, -2), (key2705, 2), (key2785, 6), (key2793, -4), (key2808, -6), (key2828, 4), (key2859, 4), (key2869, -4)]

theorem rowCheck4887 : row4887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4887 := by decide +kernel

theorem rowEval4887 (x : Key → ℝ) : Integer.Sparse.eval row4887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4887, Integer.Sparse.eval_collectBalanced, rawRowCheck4887]

def rawRow4888 : Integer.Sparse Key := [(key2808, -6), (key2859, 2), (key2705, 2), (key2859, 2), (key2785, 6), (key2869, -2), (key2631, -2), (key2869, -2), (key2793, -2), (key2670, -2), (key2793, -2), (key2828, 2), (key2615, 2), (key2828, 2)]

theorem rawRowCheck4888 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form4 = rawRow4888 := by decide +kernel

def row4888 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, -2), (key2705, 2), (key2785, 6), (key2793, -4), (key2808, -6), (key2828, 4), (key2859, 4), (key2869, -4)]

theorem rowCheck4888 : row4888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4888 := by decide +kernel

theorem rowEval4888 (x : Key → ℝ) : Integer.Sparse.eval row4888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4888, Integer.Sparse.eval_collectBalanced, rawRowCheck4888]

def rawRow4889 : Integer.Sparse Key := [(key2808, -6), (key2859, 2), (key2859, 2), (key2705, 2), (key2785, 6), (key2869, -2), (key2869, -2), (key2631, -2), (key2793, -2), (key2793, -2), (key2670, -2), (key2828, 2), (key2828, 2), (key2615, 2)]

theorem rawRowCheck4889 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form4 = rawRow4889 := by decide +kernel

def row4889 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, -2), (key2705, 2), (key2785, 6), (key2793, -4), (key2808, -6), (key2828, 4), (key2859, 4), (key2869, -4)]

theorem rowCheck4889 : row4889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4889 := by decide +kernel

theorem rowEval4889 (x : Key → ℝ) : Integer.Sparse.eval row4889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4889, Integer.Sparse.eval_collectBalanced, rawRowCheck4889]

def rawRow4890 : Integer.Sparse Key := [(key1546, -1), (key1546, -1), (key1772, -1), (key1772, -1), (key1775, -1), (key1775, -1), (key1560, 2), (key1781, 2), (key1781, 2), (key1573, 1), (key1573, 1), (key1788, 1), (key1788, 1), (key1791, 1), (key1791, 1), (key1660, -1), (key1660, -1), (key1818, -1), (key1818, -1), (key1842, -1), (key1842, -1), (key1597, -2), (key1799, -2), (key1799, -2), (key1668, 1), (key1668, 1), (key1826, 1), (key1826, 1), (key1845, 1), (key1845, 1)]

theorem rawRowCheck4890 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form5 = rawRow4890 := by decide +kernel

def row4890 : Integer.Sparse Key := [(key1546, -2), (key1560, 2), (key1573, 2), (key1597, -2), (key1660, -2), (key1668, 2), (key1772, -2), (key1775, -2), (key1781, 4), (key1788, 2), (key1791, 2), (key1799, -4), (key1818, -2), (key1826, 2), (key1842, -2), (key1845, 2)]

theorem rowCheck4890 : row4890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4890 := by decide +kernel

theorem rowEval4890 (x : Key → ℝ) : Integer.Sparse.eval row4890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4890, Integer.Sparse.eval_collectBalanced, rawRowCheck4890]

def rawRow4891 : Integer.Sparse Key := [(key1772, -1), (key1775, -1), (key1546, -1), (key1775, -1), (key1546, -1), (key1772, -1), (key1781, 2), (key1560, 2), (key1781, 2), (key1788, 1), (key1791, 1), (key1573, 1), (key1791, 1), (key1573, 1), (key1788, 1), (key1818, -1), (key1842, -1), (key1660, -1), (key1842, -1), (key1660, -1), (key1818, -1), (key1799, -2), (key1597, -2), (key1799, -2), (key1826, 1), (key1845, 1), (key1668, 1), (key1845, 1), (key1668, 1), (key1826, 1)]

theorem rawRowCheck4891 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form5 = rawRow4891 := by decide +kernel

def row4891 : Integer.Sparse Key := [(key1546, -2), (key1560, 2), (key1573, 2), (key1597, -2), (key1660, -2), (key1668, 2), (key1772, -2), (key1775, -2), (key1781, 4), (key1788, 2), (key1791, 2), (key1799, -4), (key1818, -2), (key1826, 2), (key1842, -2), (key1845, 2)]

theorem rowCheck4891 : row4891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4891 := by decide +kernel

theorem rowEval4891 (x : Key → ℝ) : Integer.Sparse.eval row4891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4891, Integer.Sparse.eval_collectBalanced, rawRowCheck4891]

def rawRow4892 : Integer.Sparse Key := [(key1775, -1), (key1772, -1), (key1775, -1), (key1546, -1), (key1772, -1), (key1546, -1), (key1781, 2), (key1781, 2), (key1560, 2), (key1791, 1), (key1788, 1), (key1791, 1), (key1573, 1), (key1788, 1), (key1573, 1), (key1842, -1), (key1818, -1), (key1842, -1), (key1660, -1), (key1818, -1), (key1660, -1), (key1799, -2), (key1799, -2), (key1597, -2), (key1845, 1), (key1826, 1), (key1845, 1), (key1668, 1), (key1826, 1), (key1668, 1)]

theorem rawRowCheck4892 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form5 = rawRow4892 := by decide +kernel

def row4892 : Integer.Sparse Key := [(key1546, -2), (key1560, 2), (key1573, 2), (key1597, -2), (key1660, -2), (key1668, 2), (key1772, -2), (key1775, -2), (key1781, 4), (key1788, 2), (key1791, 2), (key1799, -4), (key1818, -2), (key1826, 2), (key1842, -2), (key1845, 2)]

theorem rowCheck4892 : row4892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4892 := by decide +kernel

theorem rowEval4892 (x : Key → ℝ) : Integer.Sparse.eval row4892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4892, Integer.Sparse.eval_collectBalanced, rawRowCheck4892]

def rawRow4893 : Integer.Sparse Key := [(key1573, -1), (key1573, -1), (key1788, -1), (key1788, -1), (key1791, -1), (key1791, -1), (key1597, 2), (key1799, 2), (key1799, 2), (key1546, 1), (key1546, 1), (key1772, 1), (key1772, 1), (key1775, 1), (key1775, 1), (key1668, -1), (key1668, -1), (key1826, -1), (key1826, -1), (key1845, -1), (key1845, -1), (key1560, -2), (key1781, -2), (key1781, -2), (key1660, 1), (key1660, 1), (key1818, 1), (key1818, 1), (key1842, 1), (key1842, 1)]

theorem rawRowCheck4893 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form5 = rawRow4893 := by decide +kernel

def row4893 : Integer.Sparse Key := [(key1546, 2), (key1560, -2), (key1573, -2), (key1597, 2), (key1660, 2), (key1668, -2), (key1772, 2), (key1775, 2), (key1781, -4), (key1788, -2), (key1791, -2), (key1799, 4), (key1818, 2), (key1826, -2), (key1842, 2), (key1845, -2)]

theorem rowCheck4893 : row4893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4893 := by decide +kernel

theorem rowEval4893 (x : Key → ℝ) : Integer.Sparse.eval row4893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4893, Integer.Sparse.eval_collectBalanced, rawRowCheck4893]

def rawRow4894 : Integer.Sparse Key := [(key1788, -1), (key1791, -1), (key1573, -1), (key1791, -1), (key1573, -1), (key1788, -1), (key1799, 2), (key1597, 2), (key1799, 2), (key1772, 1), (key1775, 1), (key1546, 1), (key1775, 1), (key1546, 1), (key1772, 1), (key1826, -1), (key1845, -1), (key1668, -1), (key1845, -1), (key1668, -1), (key1826, -1), (key1781, -2), (key1560, -2), (key1781, -2), (key1818, 1), (key1842, 1), (key1660, 1), (key1842, 1), (key1660, 1), (key1818, 1)]

theorem rawRowCheck4894 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form5 = rawRow4894 := by decide +kernel

def row4894 : Integer.Sparse Key := [(key1546, 2), (key1560, -2), (key1573, -2), (key1597, 2), (key1660, 2), (key1668, -2), (key1772, 2), (key1775, 2), (key1781, -4), (key1788, -2), (key1791, -2), (key1799, 4), (key1818, 2), (key1826, -2), (key1842, 2), (key1845, -2)]

theorem rowCheck4894 : row4894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4894 := by decide +kernel

theorem rowEval4894 (x : Key → ℝ) : Integer.Sparse.eval row4894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4894, Integer.Sparse.eval_collectBalanced, rawRowCheck4894]

def rawRow4895 : Integer.Sparse Key := [(key1791, -1), (key1788, -1), (key1791, -1), (key1573, -1), (key1788, -1), (key1573, -1), (key1799, 2), (key1799, 2), (key1597, 2), (key1775, 1), (key1772, 1), (key1775, 1), (key1546, 1), (key1772, 1), (key1546, 1), (key1845, -1), (key1826, -1), (key1845, -1), (key1668, -1), (key1826, -1), (key1668, -1), (key1781, -2), (key1781, -2), (key1560, -2), (key1842, 1), (key1818, 1), (key1842, 1), (key1660, 1), (key1818, 1), (key1660, 1)]

theorem rawRowCheck4895 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form5 = rawRow4895 := by decide +kernel

def row4895 : Integer.Sparse Key := [(key1546, 2), (key1560, -2), (key1573, -2), (key1597, 2), (key1660, 2), (key1668, -2), (key1772, 2), (key1775, 2), (key1781, -4), (key1788, -2), (key1791, -2), (key1799, 4), (key1818, 2), (key1826, -2), (key1842, 2), (key1845, -2)]

theorem rowCheck4895 : row4895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4895 := by decide +kernel

theorem rowEval4895 (x : Key → ℝ) : Integer.Sparse.eval row4895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4895, Integer.Sparse.eval_collectBalanced, rawRowCheck4895]

def rawRow4896 : Integer.Sparse Key := [(key1296, -1), (key1296, -1), (key1788, -1), (key1788, -1), (key1799, -1), (key1799, -1), (key1303, 2), (key1791, 2), (key1791, 2), (key1316, 1), (key1316, 1), (key1813, 1), (key1813, 1), (key1826, 1), (key1826, 1), (key1340, -1), (key1340, -1), (key1775, -1), (key1775, -1), (key1840, -1), (key1840, -1), (key1330, -2), (key1818, -2), (key1818, -2), (key1346, 1), (key1346, 1), (key1781, 1), (key1781, 1), (key1842, 1), (key1842, 1)]

theorem rawRowCheck4896 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form5 = rawRow4896 := by decide +kernel

def row4896 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1775, -2), (key1781, 2), (key1788, -2), (key1791, 4), (key1799, -2), (key1813, 2), (key1818, -4), (key1826, 2), (key1840, -2), (key1842, 2)]

theorem rowCheck4896 : row4896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4896 := by decide +kernel

theorem rowEval4896 (x : Key → ℝ) : Integer.Sparse.eval row4896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4896, Integer.Sparse.eval_collectBalanced, rawRowCheck4896]

def rawRow4897 : Integer.Sparse Key := [(key1788, -1), (key1799, -1), (key1296, -1), (key1799, -1), (key1296, -1), (key1788, -1), (key1791, 2), (key1303, 2), (key1791, 2), (key1813, 1), (key1826, 1), (key1316, 1), (key1826, 1), (key1316, 1), (key1813, 1), (key1775, -1), (key1840, -1), (key1340, -1), (key1840, -1), (key1340, -1), (key1775, -1), (key1818, -2), (key1330, -2), (key1818, -2), (key1781, 1), (key1842, 1), (key1346, 1), (key1842, 1), (key1346, 1), (key1781, 1)]

theorem rawRowCheck4897 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form5 = rawRow4897 := by decide +kernel

def row4897 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1775, -2), (key1781, 2), (key1788, -2), (key1791, 4), (key1799, -2), (key1813, 2), (key1818, -4), (key1826, 2), (key1840, -2), (key1842, 2)]

theorem rowCheck4897 : row4897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4897 := by decide +kernel

theorem rowEval4897 (x : Key → ℝ) : Integer.Sparse.eval row4897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4897, Integer.Sparse.eval_collectBalanced, rawRowCheck4897]

def rawRow4898 : Integer.Sparse Key := [(key1799, -1), (key1788, -1), (key1799, -1), (key1296, -1), (key1788, -1), (key1296, -1), (key1791, 2), (key1791, 2), (key1303, 2), (key1826, 1), (key1813, 1), (key1826, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1840, -1), (key1775, -1), (key1840, -1), (key1340, -1), (key1775, -1), (key1340, -1), (key1818, -2), (key1818, -2), (key1330, -2), (key1842, 1), (key1781, 1), (key1842, 1), (key1346, 1), (key1781, 1), (key1346, 1)]

theorem rawRowCheck4898 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form5 = rawRow4898 := by decide +kernel

def row4898 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1775, -2), (key1781, 2), (key1788, -2), (key1791, 4), (key1799, -2), (key1813, 2), (key1818, -4), (key1826, 2), (key1840, -2), (key1842, 2)]

theorem rowCheck4898 : row4898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4898 := by decide +kernel

theorem rowEval4898 (x : Key → ℝ) : Integer.Sparse.eval row4898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck4898, Integer.Sparse.eval_collectBalanced, rawRowCheck4898]

def rawRow4899 : Integer.Sparse Key := [(key1316, -1), (key1316, -1), (key1813, -1), (key1813, -1), (key1826, -1), (key1826, -1), (key1330, 2), (key1818, 2), (key1818, 2), (key1296, 1), (key1296, 1), (key1788, 1), (key1788, 1), (key1799, 1), (key1799, 1), (key1346, -1), (key1346, -1), (key1781, -1), (key1781, -1), (key1842, -1), (key1842, -1), (key1303, -2), (key1791, -2), (key1791, -2), (key1340, 1), (key1340, 1), (key1775, 1), (key1775, 1), (key1840, 1), (key1840, 1)]

theorem rawRowCheck4899 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form5 = rawRow4899 := by decide +kernel

def row4899 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1775, 2), (key1781, -2), (key1788, 2), (key1791, -4), (key1799, 2), (key1813, -2), (key1818, 4), (key1826, -2), (key1840, 2), (key1842, -2)]

theorem rowCheck4899 : row4899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4899 := by decide +kernel

theorem rowEval4899 (x : Key → ℝ) : Integer.Sparse.eval row4899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4899, Integer.Sparse.eval_collectBalanced, rawRowCheck4899]

def rawRow4900 : Integer.Sparse Key := [(key1813, -1), (key1826, -1), (key1316, -1), (key1826, -1), (key1316, -1), (key1813, -1), (key1818, 2), (key1330, 2), (key1818, 2), (key1788, 1), (key1799, 1), (key1296, 1), (key1799, 1), (key1296, 1), (key1788, 1), (key1781, -1), (key1842, -1), (key1346, -1), (key1842, -1), (key1346, -1), (key1781, -1), (key1791, -2), (key1303, -2), (key1791, -2), (key1775, 1), (key1840, 1), (key1340, 1), (key1840, 1), (key1340, 1), (key1775, 1)]

theorem rawRowCheck4900 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form5 = rawRow4900 := by decide +kernel

def row4900 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1775, 2), (key1781, -2), (key1788, 2), (key1791, -4), (key1799, 2), (key1813, -2), (key1818, 4), (key1826, -2), (key1840, 2), (key1842, -2)]

theorem rowCheck4900 : row4900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4900 := by decide +kernel

theorem rowEval4900 (x : Key → ℝ) : Integer.Sparse.eval row4900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4900, Integer.Sparse.eval_collectBalanced, rawRowCheck4900]

def rawRow4901 : Integer.Sparse Key := [(key1826, -1), (key1813, -1), (key1826, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1818, 2), (key1818, 2), (key1330, 2), (key1799, 1), (key1788, 1), (key1799, 1), (key1296, 1), (key1788, 1), (key1296, 1), (key1842, -1), (key1781, -1), (key1842, -1), (key1346, -1), (key1781, -1), (key1346, -1), (key1791, -2), (key1791, -2), (key1303, -2), (key1840, 1), (key1775, 1), (key1840, 1), (key1340, 1), (key1775, 1), (key1340, 1)]

theorem rawRowCheck4901 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form5 = rawRow4901 := by decide +kernel

def row4901 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1775, 2), (key1781, -2), (key1788, 2), (key1791, -4), (key1799, 2), (key1813, -2), (key1818, 4), (key1826, -2), (key1840, 2), (key1842, -2)]

theorem rowCheck4901 : row4901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4901 := by decide +kernel

theorem rowEval4901 (x : Key → ℝ) : Integer.Sparse.eval row4901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck4901, Integer.Sparse.eval_collectBalanced, rawRowCheck4901]

def rawRow4902 : Integer.Sparse Key := [(key2719, -2), (key2719, -2), (key2733, -2), (key2756, 2), (key2756, 2), (key2759, 2), (key2822, 2), (key2822, 2), (key2836, 2), (key2924, -6), (key3015, -2), (key3015, -2), (key3018, -2), (key3027, 6)]

theorem rawRowCheck4902 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form6 = rawRow4902 := by decide +kernel

def row4902 : Integer.Sparse Key := [(key2719, -4), (key2733, -2), (key2756, 4), (key2759, 2), (key2822, 4), (key2836, 2), (key2924, -6), (key3015, -4), (key3018, -2), (key3027, 6)]

theorem rowCheck4902 : row4902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4902 := by decide +kernel

theorem rowEval4902 (x : Key → ℝ) : Integer.Sparse.eval row4902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4902, Integer.Sparse.eval_collectBalanced, rawRowCheck4902]

def rawRow4903 : Integer.Sparse Key := [(key2719, -2), (key2733, -2), (key2719, -2), (key2756, 2), (key2759, 2), (key2756, 2), (key2822, 2), (key2836, 2), (key2822, 2), (key2924, -6), (key3015, -2), (key3018, -2), (key3015, -2), (key3027, 6)]

theorem rawRowCheck4903 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form6 = rawRow4903 := by decide +kernel

def row4903 : Integer.Sparse Key := [(key2719, -4), (key2733, -2), (key2756, 4), (key2759, 2), (key2822, 4), (key2836, 2), (key2924, -6), (key3015, -4), (key3018, -2), (key3027, 6)]

theorem rowCheck4903 : row4903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4903 := by decide +kernel

theorem rowEval4903 (x : Key → ℝ) : Integer.Sparse.eval row4903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4903, Integer.Sparse.eval_collectBalanced, rawRowCheck4903]

def rawRow4904 : Integer.Sparse Key := [(key2733, -2), (key2719, -2), (key2719, -2), (key2759, 2), (key2756, 2), (key2756, 2), (key2836, 2), (key2822, 2), (key2822, 2), (key2924, -6), (key3018, -2), (key3015, -2), (key3015, -2), (key3027, 6)]

theorem rawRowCheck4904 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form6 = rawRow4904 := by decide +kernel

def row4904 : Integer.Sparse Key := [(key2719, -4), (key2733, -2), (key2756, 4), (key2759, 2), (key2822, 4), (key2836, 2), (key2924, -6), (key3015, -4), (key3018, -2), (key3027, 6)]

theorem rowCheck4904 : row4904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4904 := by decide +kernel

theorem rowEval4904 (x : Key → ℝ) : Integer.Sparse.eval row4904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4904, Integer.Sparse.eval_collectBalanced, rawRowCheck4904]

def rawRow4905 : Integer.Sparse Key := [(key2822, -2), (key2822, -2), (key2836, -2), (key3015, 2), (key3015, 2), (key3018, 2), (key2719, 2), (key2719, 2), (key2733, 2), (key3027, -6), (key2756, -2), (key2756, -2), (key2759, -2), (key2924, 6)]

theorem rawRowCheck4905 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form6 = rawRow4905 := by decide +kernel

def row4905 : Integer.Sparse Key := [(key2719, 4), (key2733, 2), (key2756, -4), (key2759, -2), (key2822, -4), (key2836, -2), (key2924, 6), (key3015, 4), (key3018, 2), (key3027, -6)]

theorem rowCheck4905 : row4905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4905 := by decide +kernel

theorem rowEval4905 (x : Key → ℝ) : Integer.Sparse.eval row4905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4905, Integer.Sparse.eval_collectBalanced, rawRowCheck4905]

def rawRow4906 : Integer.Sparse Key := [(key2822, -2), (key2836, -2), (key2822, -2), (key3015, 2), (key3018, 2), (key3015, 2), (key2719, 2), (key2733, 2), (key2719, 2), (key3027, -6), (key2756, -2), (key2759, -2), (key2756, -2), (key2924, 6)]

theorem rawRowCheck4906 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form6 = rawRow4906 := by decide +kernel

def row4906 : Integer.Sparse Key := [(key2719, 4), (key2733, 2), (key2756, -4), (key2759, -2), (key2822, -4), (key2836, -2), (key2924, 6), (key3015, 4), (key3018, 2), (key3027, -6)]

theorem rowCheck4906 : row4906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4906 := by decide +kernel

theorem rowEval4906 (x : Key → ℝ) : Integer.Sparse.eval row4906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4906, Integer.Sparse.eval_collectBalanced, rawRowCheck4906]

def rawRow4907 : Integer.Sparse Key := [(key2836, -2), (key2822, -2), (key2822, -2), (key3018, 2), (key3015, 2), (key3015, 2), (key2733, 2), (key2719, 2), (key2719, 2), (key3027, -6), (key2759, -2), (key2756, -2), (key2756, -2), (key2924, 6)]

theorem rawRowCheck4907 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form6 = rawRow4907 := by decide +kernel

def row4907 : Integer.Sparse Key := [(key2719, 4), (key2733, 2), (key2756, -4), (key2759, -2), (key2822, -4), (key2836, -2), (key2924, 6), (key3015, 4), (key3018, 2), (key3027, -6)]

theorem rowCheck4907 : row4907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4907 := by decide +kernel

theorem rowEval4907 (x : Key → ℝ) : Integer.Sparse.eval row4907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4907, Integer.Sparse.eval_collectBalanced, rawRowCheck4907]

def rawRow4908 : Integer.Sparse Key := [(key2693, -2), (key2693, -2), (key3018, -2), (key2695, 2), (key2695, 2), (key2836, 2), (key2719, 2), (key2719, 2), (key3027, 2), (key2733, -6), (key2756, -2), (key2756, -2), (key2924, -2), (key2759, 6)]

theorem rawRowCheck4908 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form6 = rawRow4908 := by decide +kernel

def row4908 : Integer.Sparse Key := [(key2693, -4), (key2695, 4), (key2719, 4), (key2733, -6), (key2756, -4), (key2759, 6), (key2836, 2), (key2924, -2), (key3018, -2), (key3027, 2)]

theorem rowCheck4908 : row4908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4908 := by decide +kernel

theorem rowEval4908 (x : Key → ℝ) : Integer.Sparse.eval row4908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4908, Integer.Sparse.eval_collectBalanced, rawRowCheck4908]

def rawRow4909 : Integer.Sparse Key := [(key3055, -2), (key3117, -2), (key2693, -2), (key2695, 2), (key2836, 2), (key2695, 2), (key2719, 2), (key3027, 2), (key2719, 2), (key2733, -6), (key2756, -2), (key2924, -2), (key2756, -2), (key2759, 6)]

theorem rawRowCheck4909 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form6 = rawRow4909 := by decide +kernel

def row4909 : Integer.Sparse Key := [(key2693, -2), (key2695, 4), (key2719, 4), (key2733, -6), (key2756, -4), (key2759, 6), (key2836, 2), (key2924, -2), (key3027, 2), (key3055, -2), (key3117, -2)]

theorem rowCheck4909 : row4909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4909 := by decide +kernel

theorem rowEval4909 (x : Key → ℝ) : Integer.Sparse.eval row4909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4909, Integer.Sparse.eval_collectBalanced, rawRowCheck4909]

def rawRow4910 : Integer.Sparse Key := [(key3117, -2), (key3055, -2), (key2693, -2), (key2836, 2), (key2695, 2), (key2695, 2), (key3027, 2), (key2719, 2), (key2719, 2), (key2733, -6), (key2924, -2), (key2756, -2), (key2756, -2), (key2759, 6)]

theorem rawRowCheck4910 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form6 = rawRow4910 := by decide +kernel

def row4910 : Integer.Sparse Key := [(key2693, -2), (key2695, 4), (key2719, 4), (key2733, -6), (key2756, -4), (key2759, 6), (key2836, 2), (key2924, -2), (key3027, 2), (key3055, -2), (key3117, -2)]

theorem rowCheck4910 : row4910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4910 := by decide +kernel

theorem rowEval4910 (x : Key → ℝ) : Integer.Sparse.eval row4910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4910, Integer.Sparse.eval_collectBalanced, rawRowCheck4910]

def rawRow4911 : Integer.Sparse Key := [(key3070, -2), (key3070, -2), (key3147, -2), (key3074, 2), (key3074, 2), (key3146, 2), (key2693, 2), (key2693, 2), (key3018, 2), (key2759, -6), (key2695, -2), (key2695, -2), (key2836, -2), (key2733, 6)]

theorem rawRowCheck4911 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form6 = rawRow4911 := by decide +kernel

def row4911 : Integer.Sparse Key := [(key2693, 4), (key2695, -4), (key2733, 6), (key2759, -6), (key2836, -2), (key3018, 2), (key3070, -4), (key3074, 4), (key3146, 2), (key3147, -2)]

theorem rowCheck4911 : row4911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4911 := by decide +kernel

theorem rowEval4911 (x : Key → ℝ) : Integer.Sparse.eval row4911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4911, Integer.Sparse.eval_collectBalanced, rawRowCheck4911]

def rawRow4912 : Integer.Sparse Key := [(key3070, -2), (key3147, -2), (key3070, -2), (key3074, 2), (key3146, 2), (key3074, 2), (key3055, 2), (key3117, 2), (key2693, 2), (key2759, -6), (key2695, -2), (key2836, -2), (key2695, -2), (key2733, 6)]

theorem rawRowCheck4912 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form6 = rawRow4912 := by decide +kernel

def row4912 : Integer.Sparse Key := [(key2693, 2), (key2695, -4), (key2733, 6), (key2759, -6), (key2836, -2), (key3055, 2), (key3070, -4), (key3074, 4), (key3117, 2), (key3146, 2), (key3147, -2)]

theorem rowCheck4912 : row4912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4912 := by decide +kernel

theorem rowEval4912 (x : Key → ℝ) : Integer.Sparse.eval row4912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4912, Integer.Sparse.eval_collectBalanced, rawRowCheck4912]

def rawRow4913 : Integer.Sparse Key := [(key3147, -2), (key3070, -2), (key3070, -2), (key3146, 2), (key3074, 2), (key3074, 2), (key3117, 2), (key3055, 2), (key2693, 2), (key2759, -6), (key2836, -2), (key2695, -2), (key2695, -2), (key2733, 6)]

theorem rawRowCheck4913 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form6 = rawRow4913 := by decide +kernel

def row4913 : Integer.Sparse Key := [(key2693, 2), (key2695, -4), (key2733, 6), (key2759, -6), (key2836, -2), (key3055, 2), (key3070, -4), (key3074, 4), (key3117, 2), (key3146, 2), (key3147, -2)]

theorem rowCheck4913 : row4913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4913 := by decide +kernel

theorem rowEval4913 (x : Key → ℝ) : Integer.Sparse.eval row4913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4913, Integer.Sparse.eval_collectBalanced, rawRowCheck4913]

def rawRow4914 : Integer.Sparse Key := [(key1296, -2), (key1296, -2), (key1303, -2), (key1316, 1), (key1316, 1), (key1337, 1), (key1337, 1), (key1340, 1), (key1340, 1), (key1391, 2), (key1391, 2), (key1398, 2), (key1546, -1), (key1546, -1), (key1772, -1), (key1772, -1), (key1775, -1), (key1775, -1), (key1424, -1), (key1424, -1), (key1455, -1), (key1455, -1), (key1458, -1), (key1458, -1), (key1573, 1), (key1573, 1), (key1788, 1), (key1788, 1), (key1791, 1), (key1791, 1)]

theorem rawRowCheck4914 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form7 = rawRow4914 := by decide +kernel

def row4914 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1391, 4), (key1398, 2), (key1424, -2), (key1455, -2), (key1458, -2), (key1546, -2), (key1573, 2), (key1772, -2), (key1775, -2), (key1788, 2), (key1791, 2)]

theorem rowCheck4914 : row4914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4914 := by decide +kernel

theorem rowEval4914 (x : Key → ℝ) : Integer.Sparse.eval row4914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4914, Integer.Sparse.eval_collectBalanced, rawRowCheck4914]

def rawRow4915 : Integer.Sparse Key := [(key1296, -2), (key1303, -2), (key1296, -2), (key1337, 1), (key1340, 1), (key1316, 1), (key1340, 1), (key1316, 1), (key1337, 1), (key1391, 2), (key1398, 2), (key1391, 2), (key1772, -1), (key1775, -1), (key1546, -1), (key1775, -1), (key1546, -1), (key1772, -1), (key1455, -1), (key1458, -1), (key1424, -1), (key1458, -1), (key1424, -1), (key1455, -1), (key1788, 1), (key1791, 1), (key1573, 1), (key1791, 1), (key1573, 1), (key1788, 1)]

theorem rawRowCheck4915 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form7 = rawRow4915 := by decide +kernel

def row4915 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1391, 4), (key1398, 2), (key1424, -2), (key1455, -2), (key1458, -2), (key1546, -2), (key1573, 2), (key1772, -2), (key1775, -2), (key1788, 2), (key1791, 2)]

theorem rowCheck4915 : row4915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4915 := by decide +kernel

theorem rowEval4915 (x : Key → ℝ) : Integer.Sparse.eval row4915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4915, Integer.Sparse.eval_collectBalanced, rawRowCheck4915]

def rawRow4916 : Integer.Sparse Key := [(key1303, -2), (key1296, -2), (key1296, -2), (key1340, 1), (key1337, 1), (key1340, 1), (key1316, 1), (key1337, 1), (key1316, 1), (key1398, 2), (key1391, 2), (key1391, 2), (key1775, -1), (key1772, -1), (key1775, -1), (key1546, -1), (key1772, -1), (key1546, -1), (key1458, -1), (key1455, -1), (key1458, -1), (key1424, -1), (key1455, -1), (key1424, -1), (key1791, 1), (key1788, 1), (key1791, 1), (key1573, 1), (key1788, 1), (key1573, 1)]

theorem rawRowCheck4916 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form7 = rawRow4916 := by decide +kernel

def row4916 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1391, 4), (key1398, 2), (key1424, -2), (key1455, -2), (key1458, -2), (key1546, -2), (key1573, 2), (key1772, -2), (key1775, -2), (key1788, 2), (key1791, 2)]

theorem rowCheck4916 : row4916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4916 := by decide +kernel

theorem rowEval4916 (x : Key → ℝ) : Integer.Sparse.eval row4916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4916, Integer.Sparse.eval_collectBalanced, rawRowCheck4916]

def rawRow4917 : Integer.Sparse Key := [(key1391, -2), (key1391, -2), (key1398, -2), (key1424, 1), (key1424, 1), (key1455, 1), (key1455, 1), (key1458, 1), (key1458, 1), (key1296, 2), (key1296, 2), (key1303, 2), (key1573, -1), (key1573, -1), (key1788, -1), (key1788, -1), (key1791, -1), (key1791, -1), (key1316, -1), (key1316, -1), (key1337, -1), (key1337, -1), (key1340, -1), (key1340, -1), (key1546, 1), (key1546, 1), (key1772, 1), (key1772, 1), (key1775, 1), (key1775, 1)]

theorem rawRowCheck4917 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form7 = rawRow4917 := by decide +kernel

def row4917 : Integer.Sparse Key := [(key1296, 4), (key1303, 2), (key1316, -2), (key1337, -2), (key1340, -2), (key1391, -4), (key1398, -2), (key1424, 2), (key1455, 2), (key1458, 2), (key1546, 2), (key1573, -2), (key1772, 2), (key1775, 2), (key1788, -2), (key1791, -2)]

theorem rowCheck4917 : row4917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4917 := by decide +kernel

theorem rowEval4917 (x : Key → ℝ) : Integer.Sparse.eval row4917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4917, Integer.Sparse.eval_collectBalanced, rawRowCheck4917]

def rawRow4918 : Integer.Sparse Key := [(key1391, -2), (key1398, -2), (key1391, -2), (key1455, 1), (key1458, 1), (key1424, 1), (key1458, 1), (key1424, 1), (key1455, 1), (key1296, 2), (key1303, 2), (key1296, 2), (key1788, -1), (key1791, -1), (key1573, -1), (key1791, -1), (key1573, -1), (key1788, -1), (key1337, -1), (key1340, -1), (key1316, -1), (key1340, -1), (key1316, -1), (key1337, -1), (key1772, 1), (key1775, 1), (key1546, 1), (key1775, 1), (key1546, 1), (key1772, 1)]

theorem rawRowCheck4918 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form7 = rawRow4918 := by decide +kernel

def row4918 : Integer.Sparse Key := [(key1296, 4), (key1303, 2), (key1316, -2), (key1337, -2), (key1340, -2), (key1391, -4), (key1398, -2), (key1424, 2), (key1455, 2), (key1458, 2), (key1546, 2), (key1573, -2), (key1772, 2), (key1775, 2), (key1788, -2), (key1791, -2)]

theorem rowCheck4918 : row4918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4918 := by decide +kernel

theorem rowEval4918 (x : Key → ℝ) : Integer.Sparse.eval row4918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4918, Integer.Sparse.eval_collectBalanced, rawRowCheck4918]

def rawRow4919 : Integer.Sparse Key := [(key1398, -2), (key1391, -2), (key1391, -2), (key1458, 1), (key1455, 1), (key1458, 1), (key1424, 1), (key1455, 1), (key1424, 1), (key1303, 2), (key1296, 2), (key1296, 2), (key1791, -1), (key1788, -1), (key1791, -1), (key1573, -1), (key1788, -1), (key1573, -1), (key1340, -1), (key1337, -1), (key1340, -1), (key1316, -1), (key1337, -1), (key1316, -1), (key1775, 1), (key1772, 1), (key1775, 1), (key1546, 1), (key1772, 1), (key1546, 1)]

theorem rawRowCheck4919 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form7 = rawRow4919 := by decide +kernel

def row4919 : Integer.Sparse Key := [(key1296, 4), (key1303, 2), (key1316, -2), (key1337, -2), (key1340, -2), (key1391, -4), (key1398, -2), (key1424, 2), (key1455, 2), (key1458, 2), (key1546, 2), (key1573, -2), (key1772, 2), (key1775, 2), (key1788, -2), (key1791, -2)]

theorem rowCheck4919 : row4919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4919 := by decide +kernel

theorem rowEval4919 (x : Key → ℝ) : Integer.Sparse.eval row4919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4919, Integer.Sparse.eval_collectBalanced, rawRowCheck4919]

def rawRow4920 : Integer.Sparse Key := [(key1424, -2), (key1424, -2), (key1448, -2), (key1391, 1), (key1391, 1), (key1455, 1), (key1455, 1), (key1467, 1), (key1467, 1), (key1573, 2), (key1573, 2), (key1597, 2), (key1296, -1), (key1296, -1), (key1788, -1), (key1788, -1), (key1799, -1), (key1799, -1), (key1546, -1), (key1546, -1), (key1655, -1), (key1655, -1), (key1668, -1), (key1668, -1), (key1316, 1), (key1316, 1), (key1813, 1), (key1813, 1), (key1826, 1), (key1826, 1)]

theorem rawRowCheck4920 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form7 = rawRow4920 := by decide +kernel

def row4920 : Integer.Sparse Key := [(key1296, -2), (key1316, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1546, -2), (key1573, 4), (key1597, 2), (key1655, -2), (key1668, -2), (key1788, -2), (key1799, -2), (key1813, 2), (key1826, 2)]

theorem rowCheck4920 : row4920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4920 := by decide +kernel

theorem rowEval4920 (x : Key → ℝ) : Integer.Sparse.eval row4920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4920, Integer.Sparse.eval_collectBalanced, rawRowCheck4920]

def rawRow4921 : Integer.Sparse Key := [(key1424, -2), (key1448, -2), (key1424, -2), (key1455, 1), (key1467, 1), (key1391, 1), (key1467, 1), (key1391, 1), (key1455, 1), (key1573, 2), (key1597, 2), (key1573, 2), (key1788, -1), (key1799, -1), (key1296, -1), (key1799, -1), (key1296, -1), (key1788, -1), (key1655, -1), (key1668, -1), (key1546, -1), (key1668, -1), (key1546, -1), (key1655, -1), (key1813, 1), (key1826, 1), (key1316, 1), (key1826, 1), (key1316, 1), (key1813, 1)]

theorem rawRowCheck4921 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form7 = rawRow4921 := by decide +kernel

def row4921 : Integer.Sparse Key := [(key1296, -2), (key1316, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1546, -2), (key1573, 4), (key1597, 2), (key1655, -2), (key1668, -2), (key1788, -2), (key1799, -2), (key1813, 2), (key1826, 2)]

theorem rowCheck4921 : row4921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4921 := by decide +kernel

theorem rowEval4921 (x : Key → ℝ) : Integer.Sparse.eval row4921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4921, Integer.Sparse.eval_collectBalanced, rawRowCheck4921]

def rawRow4922 : Integer.Sparse Key := [(key1448, -2), (key1424, -2), (key1424, -2), (key1467, 1), (key1455, 1), (key1467, 1), (key1391, 1), (key1455, 1), (key1391, 1), (key1597, 2), (key1573, 2), (key1573, 2), (key1799, -1), (key1788, -1), (key1799, -1), (key1296, -1), (key1788, -1), (key1296, -1), (key1668, -1), (key1655, -1), (key1668, -1), (key1546, -1), (key1655, -1), (key1546, -1), (key1826, 1), (key1813, 1), (key1826, 1), (key1316, 1), (key1813, 1), (key1316, 1)]

theorem rawRowCheck4922 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form7 = rawRow4922 := by decide +kernel

def row4922 : Integer.Sparse Key := [(key1296, -2), (key1316, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1546, -2), (key1573, 4), (key1597, 2), (key1655, -2), (key1668, -2), (key1788, -2), (key1799, -2), (key1813, 2), (key1826, 2)]

theorem rowCheck4922 : row4922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4922 := by decide +kernel

theorem rowEval4922 (x : Key → ℝ) : Integer.Sparse.eval row4922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4922, Integer.Sparse.eval_collectBalanced, rawRowCheck4922]

def rawRow4923 : Integer.Sparse Key := [(key1573, -2), (key1573, -2), (key1597, -2), (key1546, 1), (key1546, 1), (key1655, 1), (key1655, 1), (key1668, 1), (key1668, 1), (key1424, 2), (key1424, 2), (key1448, 2), (key1316, -1), (key1316, -1), (key1813, -1), (key1813, -1), (key1826, -1), (key1826, -1), (key1391, -1), (key1391, -1), (key1455, -1), (key1455, -1), (key1467, -1), (key1467, -1), (key1296, 1), (key1296, 1), (key1788, 1), (key1788, 1), (key1799, 1), (key1799, 1)]

theorem rawRowCheck4923 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form7 = rawRow4923 := by decide +kernel

def row4923 : Integer.Sparse Key := [(key1296, 2), (key1316, -2), (key1391, -2), (key1424, 4), (key1448, 2), (key1455, -2), (key1467, -2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1788, 2), (key1799, 2), (key1813, -2), (key1826, -2)]

theorem rowCheck4923 : row4923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4923 := by decide +kernel

theorem rowEval4923 (x : Key → ℝ) : Integer.Sparse.eval row4923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4923, Integer.Sparse.eval_collectBalanced, rawRowCheck4923]

def rawRow4924 : Integer.Sparse Key := [(key1573, -2), (key1597, -2), (key1573, -2), (key1655, 1), (key1668, 1), (key1546, 1), (key1668, 1), (key1546, 1), (key1655, 1), (key1424, 2), (key1448, 2), (key1424, 2), (key1813, -1), (key1826, -1), (key1316, -1), (key1826, -1), (key1316, -1), (key1813, -1), (key1455, -1), (key1467, -1), (key1391, -1), (key1467, -1), (key1391, -1), (key1455, -1), (key1788, 1), (key1799, 1), (key1296, 1), (key1799, 1), (key1296, 1), (key1788, 1)]

theorem rawRowCheck4924 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form7 = rawRow4924 := by decide +kernel

def row4924 : Integer.Sparse Key := [(key1296, 2), (key1316, -2), (key1391, -2), (key1424, 4), (key1448, 2), (key1455, -2), (key1467, -2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1788, 2), (key1799, 2), (key1813, -2), (key1826, -2)]

theorem rowCheck4924 : row4924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4924 := by decide +kernel

theorem rowEval4924 (x : Key → ℝ) : Integer.Sparse.eval row4924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4924, Integer.Sparse.eval_collectBalanced, rawRowCheck4924]

def rawRow4925 : Integer.Sparse Key := [(key1597, -2), (key1573, -2), (key1573, -2), (key1668, 1), (key1655, 1), (key1668, 1), (key1546, 1), (key1655, 1), (key1546, 1), (key1448, 2), (key1424, 2), (key1424, 2), (key1826, -1), (key1813, -1), (key1826, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1467, -1), (key1455, -1), (key1467, -1), (key1391, -1), (key1455, -1), (key1391, -1), (key1799, 1), (key1788, 1), (key1799, 1), (key1296, 1), (key1788, 1), (key1296, 1)]

theorem rawRowCheck4925 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form7 = rawRow4925 := by decide +kernel

def row4925 : Integer.Sparse Key := [(key1296, 2), (key1316, -2), (key1391, -2), (key1424, 4), (key1448, 2), (key1455, -2), (key1467, -2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1788, 2), (key1799, 2), (key1813, -2), (key1826, -2)]

theorem rowCheck4925 : row4925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4925 := by decide +kernel

theorem rowEval4925 (x : Key → ℝ) : Integer.Sparse.eval row4925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4925, Integer.Sparse.eval_collectBalanced, rawRowCheck4925]

def rawRow4926 : Integer.Sparse Key := [(key998, -2), (key998, -2), (key1005, -2), (key1018, 6), (key1033, 2), (key1033, 2), (key1040, 2), (key1126, -2), (key1198, -2), (key1198, -2), (key1075, -6), (key1154, 2), (key1211, 2), (key1211, 2)]

theorem rawRowCheck4926 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form8 = rawRow4926 := by decide +kernel

def row4926 : Integer.Sparse Key := [(key998, -4), (key1005, -2), (key1018, 6), (key1033, 4), (key1040, 2), (key1075, -6), (key1126, -2), (key1154, 2), (key1198, -4), (key1211, 4)]

theorem rowCheck4926 : row4926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4926 := by decide +kernel

theorem rowEval4926 (x : Key → ℝ) : Integer.Sparse.eval row4926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4926, Integer.Sparse.eval_collectBalanced, rawRowCheck4926]

def rawRow4927 : Integer.Sparse Key := [(key998, -2), (key1005, -2), (key998, -2), (key1018, 6), (key1033, 2), (key1040, 2), (key1033, 2), (key1198, -2), (key1126, -2), (key1198, -2), (key1075, -6), (key1211, 2), (key1154, 2), (key1211, 2)]

theorem rawRowCheck4927 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form8 = rawRow4927 := by decide +kernel

def row4927 : Integer.Sparse Key := [(key998, -4), (key1005, -2), (key1018, 6), (key1033, 4), (key1040, 2), (key1075, -6), (key1126, -2), (key1154, 2), (key1198, -4), (key1211, 4)]

theorem rowCheck4927 : row4927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4927 := by decide +kernel

theorem rowEval4927 (x : Key → ℝ) : Integer.Sparse.eval row4927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4927, Integer.Sparse.eval_collectBalanced, rawRowCheck4927]

def rawRow4928 : Integer.Sparse Key := [(key1005, -2), (key998, -2), (key998, -2), (key1018, 6), (key1040, 2), (key1033, 2), (key1033, 2), (key1198, -2), (key1198, -2), (key1126, -2), (key1075, -6), (key1211, 2), (key1211, 2), (key1154, 2)]

theorem rawRowCheck4928 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form8 = rawRow4928 := by decide +kernel

def row4928 : Integer.Sparse Key := [(key998, -4), (key1005, -2), (key1018, 6), (key1033, 4), (key1040, 2), (key1075, -6), (key1126, -2), (key1154, 2), (key1198, -4), (key1211, 4)]

theorem rowCheck4928 : row4928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4928 := by decide +kernel

theorem rowEval4928 (x : Key → ℝ) : Integer.Sparse.eval row4928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4928, Integer.Sparse.eval_collectBalanced, rawRowCheck4928]

def rawRow4929 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1040, -2), (key1075, 6), (key998, 2), (key998, 2), (key1005, 2), (key1154, -2), (key1211, -2), (key1211, -2), (key1018, -6), (key1126, 2), (key1198, 2), (key1198, 2)]

theorem rawRowCheck4929 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form8 = rawRow4929 := by decide +kernel

def row4929 : Integer.Sparse Key := [(key998, 4), (key1005, 2), (key1018, -6), (key1033, -4), (key1040, -2), (key1075, 6), (key1126, 2), (key1154, -2), (key1198, 4), (key1211, -4)]

theorem rowCheck4929 : row4929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4929 := by decide +kernel

theorem rowEval4929 (x : Key → ℝ) : Integer.Sparse.eval row4929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4929, Integer.Sparse.eval_collectBalanced, rawRowCheck4929]

def rawRow4930 : Integer.Sparse Key := [(key1033, -2), (key1040, -2), (key1033, -2), (key1075, 6), (key998, 2), (key1005, 2), (key998, 2), (key1211, -2), (key1154, -2), (key1211, -2), (key1018, -6), (key1198, 2), (key1126, 2), (key1198, 2)]

theorem rawRowCheck4930 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form8 = rawRow4930 := by decide +kernel

def row4930 : Integer.Sparse Key := [(key998, 4), (key1005, 2), (key1018, -6), (key1033, -4), (key1040, -2), (key1075, 6), (key1126, 2), (key1154, -2), (key1198, 4), (key1211, -4)]

theorem rowCheck4930 : row4930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4930 := by decide +kernel

theorem rowEval4930 (x : Key → ℝ) : Integer.Sparse.eval row4930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4930, Integer.Sparse.eval_collectBalanced, rawRowCheck4930]

def rawRow4931 : Integer.Sparse Key := [(key1040, -2), (key1033, -2), (key1033, -2), (key1075, 6), (key1005, 2), (key998, 2), (key998, 2), (key1211, -2), (key1211, -2), (key1154, -2), (key1018, -6), (key1198, 2), (key1198, 2), (key1126, 2)]

theorem rawRowCheck4931 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form8 = rawRow4931 := by decide +kernel

def row4931 : Integer.Sparse Key := [(key998, 4), (key1005, 2), (key1018, -6), (key1033, -4), (key1040, -2), (key1075, 6), (key1126, 2), (key1154, -2), (key1198, 4), (key1211, -4)]

theorem rowCheck4931 : row4931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4931 := by decide +kernel

theorem rowEval4931 (x : Key → ℝ) : Integer.Sparse.eval row4931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4931, Integer.Sparse.eval_collectBalanced, rawRowCheck4931]

def rawRow4932 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1075, -2), (key1040, 6), (key1111, 2), (key1111, 2), (key1154, 2), (key1005, -2), (key1192, -2), (key1192, -2), (key1126, -6), (key1018, 2), (key1198, 2), (key1198, 2)]

theorem rawRowCheck4932 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form8 = rawRow4932 := by decide +kernel

def row4932 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, 4), (key1126, -6), (key1154, 2), (key1192, -4), (key1198, 4)]

theorem rowCheck4932 : row4932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4932 := by decide +kernel

theorem rowEval4932 (x : Key → ℝ) : Integer.Sparse.eval row4932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4932, Integer.Sparse.eval_collectBalanced, rawRowCheck4932]

def rawRow4933 : Integer.Sparse Key := [(key1033, -2), (key1075, -2), (key1033, -2), (key1040, 6), (key1111, 2), (key1154, 2), (key1111, 2), (key1192, -2), (key1005, -2), (key1192, -2), (key1126, -6), (key1198, 2), (key1018, 2), (key1198, 2)]

theorem rawRowCheck4933 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form8 = rawRow4933 := by decide +kernel

def row4933 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, 4), (key1126, -6), (key1154, 2), (key1192, -4), (key1198, 4)]

theorem rowCheck4933 : row4933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4933 := by decide +kernel

theorem rowEval4933 (x : Key → ℝ) : Integer.Sparse.eval row4933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4933, Integer.Sparse.eval_collectBalanced, rawRowCheck4933]

def rawRow4934 : Integer.Sparse Key := [(key1075, -2), (key1033, -2), (key1033, -2), (key1040, 6), (key1154, 2), (key1111, 2), (key1111, 2), (key1192, -2), (key1192, -2), (key1005, -2), (key1126, -6), (key1198, 2), (key1198, 2), (key1018, 2)]

theorem rawRowCheck4934 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form8 = rawRow4934 := by decide +kernel

def row4934 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, 4), (key1126, -6), (key1154, 2), (key1192, -4), (key1198, 4)]

theorem rowCheck4934 : row4934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4934 := by decide +kernel

theorem rowEval4934 (x : Key → ℝ) : Integer.Sparse.eval row4934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4934, Integer.Sparse.eval_collectBalanced, rawRowCheck4934]

def rawRow4935 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1154, -2), (key1126, 6), (key1033, 2), (key1033, 2), (key1075, 2), (key1018, -2), (key1198, -2), (key1198, -2), (key1040, -6), (key1005, 2), (key1192, 2), (key1192, 2)]

theorem rawRowCheck4935 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form8 = rawRow4935 := by decide +kernel

def row4935 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -6), (key1075, 2), (key1111, -4), (key1126, 6), (key1154, -2), (key1192, 4), (key1198, -4)]

theorem rowCheck4935 : row4935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4935 := by decide +kernel

theorem rowEval4935 (x : Key → ℝ) : Integer.Sparse.eval row4935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4935, Integer.Sparse.eval_collectBalanced, rawRowCheck4935]

def rawRow4936 : Integer.Sparse Key := [(key1111, -2), (key1154, -2), (key1111, -2), (key1126, 6), (key1033, 2), (key1075, 2), (key1033, 2), (key1198, -2), (key1018, -2), (key1198, -2), (key1040, -6), (key1192, 2), (key1005, 2), (key1192, 2)]

theorem rawRowCheck4936 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form8 = rawRow4936 := by decide +kernel

def row4936 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -6), (key1075, 2), (key1111, -4), (key1126, 6), (key1154, -2), (key1192, 4), (key1198, -4)]

theorem rowCheck4936 : row4936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4936 := by decide +kernel

theorem rowEval4936 (x : Key → ℝ) : Integer.Sparse.eval row4936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4936, Integer.Sparse.eval_collectBalanced, rawRowCheck4936]

def rawRow4937 : Integer.Sparse Key := [(key1154, -2), (key1111, -2), (key1111, -2), (key1126, 6), (key1075, 2), (key1033, 2), (key1033, 2), (key1198, -2), (key1198, -2), (key1018, -2), (key1040, -6), (key1192, 2), (key1192, 2), (key1005, 2)]

theorem rawRowCheck4937 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form8 = rawRow4937 := by decide +kernel

def row4937 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -6), (key1075, 2), (key1111, -4), (key1126, 6), (key1154, -2), (key1192, 4), (key1198, -4)]

theorem rowCheck4937 : row4937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4937 := by decide +kernel

theorem rowEval4937 (x : Key → ℝ) : Integer.Sparse.eval row4937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4937, Integer.Sparse.eval_collectBalanced, rawRowCheck4937]

def rawRow4938 : Integer.Sparse Key := [(key2633, -2), (key2643, -2), (key2643, -2), (key2650, 1), (key2650, 1), (key2655, 1), (key2655, 1), (key2656, 1), (key2656, 1), (key2787, 2), (key2797, 2), (key2797, 2), (key2899, -1), (key2899, -1), (key2906, -1), (key2906, -1), (key2915, -1), (key2915, -1), (key2940, -1), (key2940, -1), (key2945, -1), (key2945, -1), (key2946, -1), (key2946, -1), (key2978, 1), (key2978, 1), (key2985, 1), (key2985, 1), (key2994, 1), (key2994, 1)]

theorem rawRowCheck4938 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form9 = rawRow4938 := by decide +kernel

def row4938 : Integer.Sparse Key := [(key2633, -2), (key2643, -4), (key2650, 2), (key2655, 2), (key2656, 2), (key2787, 2), (key2797, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2940, -2), (key2945, -2), (key2946, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

theorem rowCheck4938 : row4938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4938 := by decide +kernel

theorem rowEval4938 (x : Key → ℝ) : Integer.Sparse.eval row4938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4938, Integer.Sparse.eval_collectBalanced, rawRowCheck4938]

def rawRow4939 : Integer.Sparse Key := [(key2643, -2), (key2633, -2), (key2643, -2), (key2655, 1), (key2656, 1), (key2650, 1), (key2656, 1), (key2650, 1), (key2655, 1), (key2797, 2), (key2787, 2), (key2797, 2), (key2906, -1), (key2915, -1), (key2899, -1), (key2915, -1), (key2899, -1), (key2906, -1), (key2945, -1), (key2946, -1), (key2940, -1), (key2946, -1), (key2940, -1), (key2945, -1), (key2985, 1), (key2994, 1), (key2978, 1), (key2994, 1), (key2978, 1), (key2985, 1)]

theorem rawRowCheck4939 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form9 = rawRow4939 := by decide +kernel

def row4939 : Integer.Sparse Key := [(key2633, -2), (key2643, -4), (key2650, 2), (key2655, 2), (key2656, 2), (key2787, 2), (key2797, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2940, -2), (key2945, -2), (key2946, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

theorem rowCheck4939 : row4939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4939 := by decide +kernel

theorem rowEval4939 (x : Key → ℝ) : Integer.Sparse.eval row4939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4939, Integer.Sparse.eval_collectBalanced, rawRowCheck4939]

def rawRow4940 : Integer.Sparse Key := [(key2643, -2), (key2643, -2), (key2633, -2), (key2656, 1), (key2655, 1), (key2656, 1), (key2650, 1), (key2655, 1), (key2650, 1), (key2797, 2), (key2797, 2), (key2787, 2), (key2915, -1), (key2906, -1), (key2915, -1), (key2899, -1), (key2906, -1), (key2899, -1), (key2946, -1), (key2945, -1), (key2946, -1), (key2940, -1), (key2945, -1), (key2940, -1), (key2994, 1), (key2985, 1), (key2994, 1), (key2978, 1), (key2985, 1), (key2978, 1)]

theorem rawRowCheck4940 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form9 = rawRow4940 := by decide +kernel

def row4940 : Integer.Sparse Key := [(key2633, -2), (key2643, -4), (key2650, 2), (key2655, 2), (key2656, 2), (key2787, 2), (key2797, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2940, -2), (key2945, -2), (key2946, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

theorem rowCheck4940 : row4940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4940 := by decide +kernel

theorem rowEval4940 (x : Key → ℝ) : Integer.Sparse.eval row4940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4940, Integer.Sparse.eval_collectBalanced, rawRowCheck4940]

def rawRow4941 : Integer.Sparse Key := [(key2707, -2), (key2739, -2), (key2739, -2), (key2730, 1), (key2730, 1), (key2749, 1), (key2749, 1), (key2751, 1), (key2751, 1), (key2633, 2), (key2643, 2), (key2643, 2), (key2978, -1), (key2978, -1), (key2985, -1), (key2985, -1), (key2994, -1), (key2994, -1), (key2650, -1), (key2650, -1), (key2655, -1), (key2655, -1), (key2656, -1), (key2656, -1), (key2899, 1), (key2899, 1), (key2906, 1), (key2906, 1), (key2915, 1), (key2915, 1)]

theorem rawRowCheck4941 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form9 = rawRow4941 := by decide +kernel

def row4941 : Integer.Sparse Key := [(key2633, 2), (key2643, 4), (key2650, -2), (key2655, -2), (key2656, -2), (key2707, -2), (key2730, 2), (key2739, -4), (key2749, 2), (key2751, 2), (key2899, 2), (key2906, 2), (key2915, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

theorem rowCheck4941 : row4941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4941 := by decide +kernel

theorem rowEval4941 (x : Key → ℝ) : Integer.Sparse.eval row4941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4941, Integer.Sparse.eval_collectBalanced, rawRowCheck4941]

def rawRow4942 : Integer.Sparse Key := [(key2739, -2), (key2707, -2), (key2739, -2), (key2749, 1), (key2751, 1), (key2730, 1), (key2751, 1), (key2730, 1), (key2749, 1), (key2643, 2), (key2633, 2), (key2643, 2), (key2985, -1), (key2994, -1), (key2978, -1), (key2994, -1), (key2978, -1), (key2985, -1), (key2655, -1), (key2656, -1), (key2650, -1), (key2656, -1), (key2650, -1), (key2655, -1), (key2906, 1), (key2915, 1), (key2899, 1), (key2915, 1), (key2899, 1), (key2906, 1)]

theorem rawRowCheck4942 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form9 = rawRow4942 := by decide +kernel

def row4942 : Integer.Sparse Key := [(key2633, 2), (key2643, 4), (key2650, -2), (key2655, -2), (key2656, -2), (key2707, -2), (key2730, 2), (key2739, -4), (key2749, 2), (key2751, 2), (key2899, 2), (key2906, 2), (key2915, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

theorem rowCheck4942 : row4942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4942 := by decide +kernel

theorem rowEval4942 (x : Key → ℝ) : Integer.Sparse.eval row4942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4942, Integer.Sparse.eval_collectBalanced, rawRowCheck4942]

def rawRow4943 : Integer.Sparse Key := [(key2739, -2), (key2739, -2), (key2707, -2), (key2751, 1), (key2749, 1), (key2751, 1), (key2730, 1), (key2749, 1), (key2730, 1), (key2643, 2), (key2643, 2), (key2633, 2), (key2994, -1), (key2985, -1), (key2994, -1), (key2978, -1), (key2985, -1), (key2978, -1), (key2656, -1), (key2655, -1), (key2656, -1), (key2650, -1), (key2655, -1), (key2650, -1), (key2915, 1), (key2906, 1), (key2915, 1), (key2899, 1), (key2906, 1), (key2899, 1)]

theorem rawRowCheck4943 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form9 = rawRow4943 := by decide +kernel

def row4943 : Integer.Sparse Key := [(key2633, 2), (key2643, 4), (key2650, -2), (key2655, -2), (key2656, -2), (key2707, -2), (key2730, 2), (key2739, -4), (key2749, 2), (key2751, 2), (key2899, 2), (key2906, 2), (key2915, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

theorem rowCheck4943 : row4943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4943 := by decide +kernel

theorem rowEval4943 (x : Key → ℝ) : Integer.Sparse.eval row4943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4943, Integer.Sparse.eval_collectBalanced, rawRowCheck4943]

def rawRow4944 : Integer.Sparse Key := [(key2672, -2), (key2749, -2), (key2749, -2), (key2675, 1), (key2675, 1), (key2739, 1), (key2739, 1), (key2751, 1), (key2751, 1), (key2707, 2), (key2978, 2), (key2978, 2), (key2643, -1), (key2643, -1), (key2730, -1), (key2730, -1), (key2994, -1), (key2994, -1), (key2739, -1), (key2739, -1), (key2899, -1), (key2899, -1), (key2999, -1), (key2999, -1), (key2655, 1), (key2655, 1), (key2749, 1), (key2749, 1), (key3004, 1), (key3004, 1)]

theorem rawRowCheck4944 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form9 = rawRow4944 := by decide +kernel

def row4944 : Integer.Sparse Key := [(key2643, -2), (key2655, 2), (key2672, -2), (key2675, 2), (key2707, 2), (key2730, -2), (key2749, -2), (key2751, 2), (key2899, -2), (key2978, 4), (key2994, -2), (key2999, -2), (key3004, 2)]

theorem rowCheck4944 : row4944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4944 := by decide +kernel

theorem rowEval4944 (x : Key → ℝ) : Integer.Sparse.eval row4944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4944, Integer.Sparse.eval_collectBalanced, rawRowCheck4944]

def rawRow4945 : Integer.Sparse Key := [(key2749, -2), (key2672, -2), (key2749, -2), (key2739, 1), (key2751, 1), (key2675, 1), (key2751, 1), (key2675, 1), (key2739, 1), (key2978, 2), (key2707, 2), (key2978, 2), (key2730, -1), (key2994, -1), (key2643, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2899, -1), (key2999, -1), (key2739, -1), (key2999, -1), (key2739, -1), (key2899, -1), (key2749, 1), (key3004, 1), (key2655, 1), (key3004, 1), (key2655, 1), (key2749, 1)]

theorem rawRowCheck4945 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form9 = rawRow4945 := by decide +kernel

def row4945 : Integer.Sparse Key := [(key2643, -2), (key2655, 2), (key2672, -2), (key2675, 2), (key2707, 2), (key2730, -2), (key2749, -2), (key2751, 2), (key2899, -2), (key2978, 4), (key2994, -2), (key2999, -2), (key3004, 2)]

theorem rowCheck4945 : row4945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4945 := by decide +kernel

theorem rowEval4945 (x : Key → ℝ) : Integer.Sparse.eval row4945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4945, Integer.Sparse.eval_collectBalanced, rawRowCheck4945]

def rawRow4946 : Integer.Sparse Key := [(key2749, -2), (key2749, -2), (key2672, -2), (key2751, 1), (key2739, 1), (key2751, 1), (key2675, 1), (key2739, 1), (key2675, 1), (key2978, 2), (key2978, 2), (key2707, 2), (key2994, -1), (key2730, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2643, -1), (key2999, -1), (key2899, -1), (key2999, -1), (key2739, -1), (key2899, -1), (key2739, -1), (key3004, 1), (key2749, 1), (key3004, 1), (key2655, 1), (key2749, 1), (key2655, 1)]

theorem rawRowCheck4946 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form9 = rawRow4946 := by decide +kernel

def row4946 : Integer.Sparse Key := [(key2643, -2), (key2655, 2), (key2672, -2), (key2675, 2), (key2707, 2), (key2730, -2), (key2749, -2), (key2751, 2), (key2899, -2), (key2978, 4), (key2994, -2), (key2999, -2), (key3004, 2)]

theorem rowCheck4946 : row4946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4946 := by decide +kernel

theorem rowEval4946 (x : Key → ℝ) : Integer.Sparse.eval row4946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4946, Integer.Sparse.eval_collectBalanced, rawRowCheck4946]

def rawRow4947 : Integer.Sparse Key := [(key2787, -2), (key2906, -2), (key2906, -2), (key2797, 1), (key2797, 1), (key2899, 1), (key2899, 1), (key2915, 1), (key2915, 1), (key2672, 2), (key2749, 2), (key2749, 2), (key2655, -1), (key2655, -1), (key2749, -1), (key2749, -1), (key3004, -1), (key3004, -1), (key2675, -1), (key2675, -1), (key2797, -1), (key2797, -1), (key2946, -1), (key2946, -1), (key2643, 1), (key2643, 1), (key2730, 1), (key2730, 1), (key2994, 1), (key2994, 1)]

theorem rawRowCheck4947 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form9 = rawRow4947 := by decide +kernel

def row4947 : Integer.Sparse Key := [(key2643, 2), (key2655, -2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, 2), (key2787, -2), (key2899, 2), (key2906, -4), (key2915, 2), (key2946, -2), (key2994, 2), (key3004, -2)]

theorem rowCheck4947 : row4947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4947 := by decide +kernel

theorem rowEval4947 (x : Key → ℝ) : Integer.Sparse.eval row4947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4947, Integer.Sparse.eval_collectBalanced, rawRowCheck4947]

def rawRow4948 : Integer.Sparse Key := [(key2906, -2), (key2787, -2), (key2906, -2), (key2899, 1), (key2915, 1), (key2797, 1), (key2915, 1), (key2797, 1), (key2899, 1), (key2749, 2), (key2672, 2), (key2749, 2), (key2749, -1), (key3004, -1), (key2655, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2797, -1), (key2946, -1), (key2675, -1), (key2946, -1), (key2675, -1), (key2797, -1), (key2730, 1), (key2994, 1), (key2643, 1), (key2994, 1), (key2643, 1), (key2730, 1)]

theorem rawRowCheck4948 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form9 = rawRow4948 := by decide +kernel

def row4948 : Integer.Sparse Key := [(key2643, 2), (key2655, -2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, 2), (key2787, -2), (key2899, 2), (key2906, -4), (key2915, 2), (key2946, -2), (key2994, 2), (key3004, -2)]

theorem rowCheck4948 : row4948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4948 := by decide +kernel

theorem rowEval4948 (x : Key → ℝ) : Integer.Sparse.eval row4948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4948, Integer.Sparse.eval_collectBalanced, rawRowCheck4948]

def rawRow4949 : Integer.Sparse Key := [(key2906, -2), (key2906, -2), (key2787, -2), (key2915, 1), (key2899, 1), (key2915, 1), (key2797, 1), (key2899, 1), (key2797, 1), (key2749, 2), (key2749, 2), (key2672, 2), (key3004, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2655, -1), (key2946, -1), (key2797, -1), (key2946, -1), (key2675, -1), (key2797, -1), (key2675, -1), (key2994, 1), (key2730, 1), (key2994, 1), (key2643, 1), (key2730, 1), (key2643, 1)]

theorem rawRowCheck4949 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form9 = rawRow4949 := by decide +kernel

def row4949 : Integer.Sparse Key := [(key2643, 2), (key2655, -2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, 2), (key2787, -2), (key2899, 2), (key2906, -4), (key2915, 2), (key2946, -2), (key2994, 2), (key3004, -2)]

theorem rowCheck4949 : row4949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4949 := by decide +kernel

theorem rowEval4949 (x : Key → ℝ) : Integer.Sparse.eval row4949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4949, Integer.Sparse.eval_collectBalanced, rawRowCheck4949]

def rawRow4950 : Integer.Sparse Key := [(key2374, -2), (key2374, -2), (key2380, -2), (key2391, 6), (key2770, 2), (key2770, 2), (key2775, 2), (key2917, -2), (key2926, -2), (key2926, -2), (key3006, -6), (key3020, 2), (key3029, 2), (key3029, 2)]

theorem rawRowCheck4950 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form10 = rawRow4950 := by decide +kernel

def row4950 : Integer.Sparse Key := [(key2374, -4), (key2380, -2), (key2391, 6), (key2770, 4), (key2775, 2), (key2917, -2), (key2926, -4), (key3006, -6), (key3020, 2), (key3029, 4)]

theorem rowCheck4950 : row4950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4950 := by decide +kernel

theorem rowEval4950 (x : Key → ℝ) : Integer.Sparse.eval row4950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4950, Integer.Sparse.eval_collectBalanced, rawRowCheck4950]

def rawRow4951 : Integer.Sparse Key := [(key2374, -2), (key2380, -2), (key2374, -2), (key2391, 6), (key2770, 2), (key2775, 2), (key2770, 2), (key2926, -2), (key2917, -2), (key2926, -2), (key3006, -6), (key3029, 2), (key3020, 2), (key3029, 2)]

theorem rawRowCheck4951 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form10 = rawRow4951 := by decide +kernel

def row4951 : Integer.Sparse Key := [(key2374, -4), (key2380, -2), (key2391, 6), (key2770, 4), (key2775, 2), (key2917, -2), (key2926, -4), (key3006, -6), (key3020, 2), (key3029, 4)]

theorem rowCheck4951 : row4951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4951 := by decide +kernel

theorem rowEval4951 (x : Key → ℝ) : Integer.Sparse.eval row4951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4951, Integer.Sparse.eval_collectBalanced, rawRowCheck4951]

def rawRow4952 : Integer.Sparse Key := [(key2380, -2), (key2374, -2), (key2374, -2), (key2391, 6), (key2775, 2), (key2770, 2), (key2770, 2), (key2926, -2), (key2926, -2), (key2917, -2), (key3006, -6), (key3029, 2), (key3029, 2), (key3020, 2)]

theorem rawRowCheck4952 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form10 = rawRow4952 := by decide +kernel

def row4952 : Integer.Sparse Key := [(key2374, -4), (key2380, -2), (key2391, 6), (key2770, 4), (key2775, 2), (key2917, -2), (key2926, -4), (key3006, -6), (key3020, 2), (key3029, 4)]

theorem rowCheck4952 : row4952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4952 := by decide +kernel

theorem rowEval4952 (x : Key → ℝ) : Integer.Sparse.eval row4952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4952, Integer.Sparse.eval_collectBalanced, rawRowCheck4952]

def rawRow4953 : Integer.Sparse Key := [(key2374, -2), (key2374, -2), (key2391, -2), (key2380, 6), (key2847, 2), (key2847, 2), (key2917, 2), (key2775, -2), (key2884, -2), (key2884, -2), (key3020, -6), (key3006, 2), (key3029, 2), (key3029, 2)]

theorem rawRowCheck4953 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form10 = rawRow4953 := by decide +kernel

def row4953 : Integer.Sparse Key := [(key2374, -4), (key2380, 6), (key2391, -2), (key2775, -2), (key2847, 4), (key2884, -4), (key2917, 2), (key3006, 2), (key3020, -6), (key3029, 4)]

theorem rowCheck4953 : row4953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4953 := by decide +kernel

theorem rowEval4953 (x : Key → ℝ) : Integer.Sparse.eval row4953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4953, Integer.Sparse.eval_collectBalanced, rawRowCheck4953]

def rawRow4954 : Integer.Sparse Key := [(key2374, -2), (key2391, -2), (key2374, -2), (key2380, 6), (key2847, 2), (key2917, 2), (key2847, 2), (key2884, -2), (key2775, -2), (key2884, -2), (key3020, -6), (key3029, 2), (key3006, 2), (key3029, 2)]

theorem rawRowCheck4954 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form10 = rawRow4954 := by decide +kernel

def row4954 : Integer.Sparse Key := [(key2374, -4), (key2380, 6), (key2391, -2), (key2775, -2), (key2847, 4), (key2884, -4), (key2917, 2), (key3006, 2), (key3020, -6), (key3029, 4)]

theorem rowCheck4954 : row4954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4954 := by decide +kernel

theorem rowEval4954 (x : Key → ℝ) : Integer.Sparse.eval row4954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4954, Integer.Sparse.eval_collectBalanced, rawRowCheck4954]

def rawRow4955 : Integer.Sparse Key := [(key2391, -2), (key2374, -2), (key2374, -2), (key2380, 6), (key2917, 2), (key2847, 2), (key2847, 2), (key2884, -2), (key2884, -2), (key2775, -2), (key3020, -6), (key3029, 2), (key3029, 2), (key3006, 2)]

theorem rawRowCheck4955 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form10 = rawRow4955 := by decide +kernel

def row4955 : Integer.Sparse Key := [(key2374, -4), (key2380, 6), (key2391, -2), (key2775, -2), (key2847, 4), (key2884, -4), (key2917, 2), (key3006, 2), (key3020, -6), (key3029, 4)]

theorem rowCheck4955 : row4955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4955 := by decide +kernel

theorem rowEval4955 (x : Key → ℝ) : Integer.Sparse.eval row4955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4955, Integer.Sparse.eval_collectBalanced, rawRowCheck4955]

def rawRow4956 : Integer.Sparse Key := [(key2402, -2), (key2402, -2), (key2408, -2), (key2439, 6), (key2591, 2), (key2591, 2), (key2596, 2), (key3020, -2), (key3029, -2), (key3029, -2), (key2605, -6), (key2917, 2), (key2926, 2), (key2926, 2)]

theorem rawRowCheck4956 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form10 = rawRow4956 := by decide +kernel

def row4956 : Integer.Sparse Key := [(key2402, -4), (key2408, -2), (key2439, 6), (key2591, 4), (key2596, 2), (key2605, -6), (key2917, 2), (key2926, 4), (key3020, -2), (key3029, -4)]

theorem rowCheck4956 : row4956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4956 := by decide +kernel

theorem rowEval4956 (x : Key → ℝ) : Integer.Sparse.eval row4956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4956, Integer.Sparse.eval_collectBalanced, rawRowCheck4956]

def rawRow4957 : Integer.Sparse Key := [(key2402, -2), (key2408, -2), (key2402, -2), (key2439, 6), (key2591, 2), (key2596, 2), (key2591, 2), (key3029, -2), (key3020, -2), (key3029, -2), (key2605, -6), (key2926, 2), (key2917, 2), (key2926, 2)]

theorem rawRowCheck4957 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form10 = rawRow4957 := by decide +kernel

def row4957 : Integer.Sparse Key := [(key2402, -4), (key2408, -2), (key2439, 6), (key2591, 4), (key2596, 2), (key2605, -6), (key2917, 2), (key2926, 4), (key3020, -2), (key3029, -4)]

theorem rowCheck4957 : row4957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4957 := by decide +kernel

theorem rowEval4957 (x : Key → ℝ) : Integer.Sparse.eval row4957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4957, Integer.Sparse.eval_collectBalanced, rawRowCheck4957]

def rawRow4958 : Integer.Sparse Key := [(key2408, -2), (key2402, -2), (key2402, -2), (key2439, 6), (key2596, 2), (key2591, 2), (key2591, 2), (key3029, -2), (key3029, -2), (key3020, -2), (key2605, -6), (key2926, 2), (key2926, 2), (key2917, 2)]

theorem rawRowCheck4958 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form10 = rawRow4958 := by decide +kernel

def row4958 : Integer.Sparse Key := [(key2402, -4), (key2408, -2), (key2439, 6), (key2591, 4), (key2596, 2), (key2605, -6), (key2917, 2), (key2926, 4), (key3020, -2), (key3029, -4)]

theorem rowCheck4958 : row4958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4958 := by decide +kernel

theorem rowEval4958 (x : Key → ℝ) : Integer.Sparse.eval row4958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4958, Integer.Sparse.eval_collectBalanced, rawRowCheck4958]

def rawRow4959 : Integer.Sparse Key := [(key2402, -2), (key2402, -2), (key2439, -2), (key2408, 6), (key2847, 2), (key2847, 2), (key3020, 2), (key2596, -2), (key2884, -2), (key2884, -2), (key2917, -6), (key2605, 2), (key2926, 2), (key2926, 2)]

theorem rawRowCheck4959 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form10 = rawRow4959 := by decide +kernel

def row4959 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2596, -2), (key2605, 2), (key2847, 4), (key2884, -4), (key2917, -6), (key2926, 4), (key3020, 2)]

theorem rowCheck4959 : row4959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4959 := by decide +kernel

theorem rowEval4959 (x : Key → ℝ) : Integer.Sparse.eval row4959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4959, Integer.Sparse.eval_collectBalanced, rawRowCheck4959]

def rawRow4960 : Integer.Sparse Key := [(key2402, -2), (key2439, -2), (key2402, -2), (key2408, 6), (key2847, 2), (key3020, 2), (key2847, 2), (key2884, -2), (key2596, -2), (key2884, -2), (key2917, -6), (key2926, 2), (key2605, 2), (key2926, 2)]

theorem rawRowCheck4960 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form10 = rawRow4960 := by decide +kernel

def row4960 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2596, -2), (key2605, 2), (key2847, 4), (key2884, -4), (key2917, -6), (key2926, 4), (key3020, 2)]

theorem rowCheck4960 : row4960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4960 := by decide +kernel

theorem rowEval4960 (x : Key → ℝ) : Integer.Sparse.eval row4960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4960, Integer.Sparse.eval_collectBalanced, rawRowCheck4960]

def rawRow4961 : Integer.Sparse Key := [(key2439, -2), (key2402, -2), (key2402, -2), (key2408, 6), (key3020, 2), (key2847, 2), (key2847, 2), (key2884, -2), (key2884, -2), (key2596, -2), (key2917, -6), (key2926, 2), (key2926, 2), (key2605, 2)]

theorem rawRowCheck4961 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form10 = rawRow4961 := by decide +kernel

def row4961 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2596, -2), (key2605, 2), (key2847, 4), (key2884, -4), (key2917, -6), (key2926, 4), (key3020, 2)]

theorem rowCheck4961 : row4961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4961 := by decide +kernel

theorem rowEval4961 (x : Key → ℝ) : Integer.Sparse.eval row4961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4961, Integer.Sparse.eval_collectBalanced, rawRowCheck4961]

def rawRow4962 : Integer.Sparse Key := [(key2468, -2), (key2468, -2), (key2481, -2), (key2505, 6), (key2374, 2), (key2374, 2), (key2391, 2), (key3006, -2), (key3029, -2), (key3029, -2), (key2596, -6), (key2775, 2), (key2884, 2), (key2884, 2)]

theorem rawRowCheck4962 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form10 = rawRow4962 := by decide +kernel

def row4962 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -4), (key2481, -2), (key2505, 6), (key2596, -6), (key2775, 2), (key2884, 4), (key3006, -2), (key3029, -4)]

theorem rowCheck4962 : row4962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4962 := by decide +kernel

theorem rowEval4962 (x : Key → ℝ) : Integer.Sparse.eval row4962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4962, Integer.Sparse.eval_collectBalanced, rawRowCheck4962]

def rawRow4963 : Integer.Sparse Key := [(key2468, -2), (key2481, -2), (key2468, -2), (key2505, 6), (key2374, 2), (key2391, 2), (key2374, 2), (key3029, -2), (key3006, -2), (key3029, -2), (key2596, -6), (key2884, 2), (key2775, 2), (key2884, 2)]

theorem rawRowCheck4963 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form10 = rawRow4963 := by decide +kernel

def row4963 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -4), (key2481, -2), (key2505, 6), (key2596, -6), (key2775, 2), (key2884, 4), (key3006, -2), (key3029, -4)]

theorem rowCheck4963 : row4963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4963 := by decide +kernel

theorem rowEval4963 (x : Key → ℝ) : Integer.Sparse.eval row4963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4963, Integer.Sparse.eval_collectBalanced, rawRowCheck4963]

def rawRow4964 : Integer.Sparse Key := [(key2481, -2), (key2468, -2), (key2468, -2), (key2505, 6), (key2391, 2), (key2374, 2), (key2374, 2), (key3029, -2), (key3029, -2), (key3006, -2), (key2596, -6), (key2884, 2), (key2884, 2), (key2775, 2)]

theorem rawRowCheck4964 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form10 = rawRow4964 := by decide +kernel

def row4964 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -4), (key2481, -2), (key2505, 6), (key2596, -6), (key2775, 2), (key2884, 4), (key3006, -2), (key3029, -4)]

theorem rowCheck4964 : row4964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4964 := by decide +kernel

theorem rowEval4964 (x : Key → ℝ) : Integer.Sparse.eval row4964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4964, Integer.Sparse.eval_collectBalanced, rawRowCheck4964]

def rawRow4965 : Integer.Sparse Key := [(key2468, -2), (key2468, -2), (key2505, -2), (key2481, 6), (key2402, 2), (key2402, 2), (key2439, 2), (key2605, -2), (key2926, -2), (key2926, -2), (key2775, -6), (key2596, 2), (key2884, 2), (key2884, 2)]

theorem rawRowCheck4965 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form10 = rawRow4965 := by decide +kernel

def row4965 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -4), (key2481, 6), (key2505, -2), (key2596, 2), (key2605, -2), (key2775, -6), (key2884, 4), (key2926, -4)]

theorem rowCheck4965 : row4965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4965 := by decide +kernel

theorem rowEval4965 (x : Key → ℝ) : Integer.Sparse.eval row4965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4965, Integer.Sparse.eval_collectBalanced, rawRowCheck4965]

def rawRow4966 : Integer.Sparse Key := [(key2468, -2), (key2505, -2), (key2468, -2), (key2481, 6), (key2402, 2), (key2439, 2), (key2402, 2), (key2926, -2), (key2605, -2), (key2926, -2), (key2775, -6), (key2884, 2), (key2596, 2), (key2884, 2)]

theorem rawRowCheck4966 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form10 = rawRow4966 := by decide +kernel

def row4966 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -4), (key2481, 6), (key2505, -2), (key2596, 2), (key2605, -2), (key2775, -6), (key2884, 4), (key2926, -4)]

theorem rowCheck4966 : row4966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4966 := by decide +kernel

theorem rowEval4966 (x : Key → ℝ) : Integer.Sparse.eval row4966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4966, Integer.Sparse.eval_collectBalanced, rawRowCheck4966]

def rawRow4967 : Integer.Sparse Key := [(key2505, -2), (key2468, -2), (key2468, -2), (key2481, 6), (key2439, 2), (key2402, 2), (key2402, 2), (key2926, -2), (key2926, -2), (key2605, -2), (key2775, -6), (key2884, 2), (key2884, 2), (key2596, 2)]

theorem rawRowCheck4967 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form10 = rawRow4967 := by decide +kernel

def row4967 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -4), (key2481, 6), (key2505, -2), (key2596, 2), (key2605, -2), (key2775, -6), (key2884, 4), (key2926, -4)]

theorem rowCheck4967 : row4967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4967 := by decide +kernel

theorem rowEval4967 (x : Key → ℝ) : Integer.Sparse.eval row4967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4967, Integer.Sparse.eval_collectBalanced, rawRowCheck4967]

def rawRow4968 : Integer.Sparse Key := [(key2591, -2), (key2591, -2), (key2594, -2), (key2601, 6), (key2770, 2), (key2770, 2), (key2773, 2), (key2890, -2), (key2911, -2), (key2911, -2), (key2932, -6), (key2969, 2), (key2990, 2), (key2990, 2)]

theorem rawRowCheck4968 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form11 = rawRow4968 := by decide +kernel

def row4968 : Integer.Sparse Key := [(key2591, -4), (key2594, -2), (key2601, 6), (key2770, 4), (key2773, 2), (key2890, -2), (key2911, -4), (key2932, -6), (key2969, 2), (key2990, 4)]

theorem rowCheck4968 : row4968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4968 := by decide +kernel

theorem rowEval4968 (x : Key → ℝ) : Integer.Sparse.eval row4968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4968, Integer.Sparse.eval_collectBalanced, rawRowCheck4968]

def rawRow4969 : Integer.Sparse Key := [(key2591, -2), (key2594, -2), (key2591, -2), (key2601, 6), (key2770, 2), (key2773, 2), (key2770, 2), (key2911, -2), (key2890, -2), (key2911, -2), (key2932, -6), (key2990, 2), (key2969, 2), (key2990, 2)]

theorem rawRowCheck4969 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form11 = rawRow4969 := by decide +kernel

def row4969 : Integer.Sparse Key := [(key2591, -4), (key2594, -2), (key2601, 6), (key2770, 4), (key2773, 2), (key2890, -2), (key2911, -4), (key2932, -6), (key2969, 2), (key2990, 4)]

theorem rowCheck4969 : row4969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4969 := by decide +kernel

theorem rowEval4969 (x : Key → ℝ) : Integer.Sparse.eval row4969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4969, Integer.Sparse.eval_collectBalanced, rawRowCheck4969]

def rawRow4970 : Integer.Sparse Key := [(key2594, -2), (key2591, -2), (key2591, -2), (key2601, 6), (key2773, 2), (key2770, 2), (key2770, 2), (key2911, -2), (key2911, -2), (key2890, -2), (key2932, -6), (key2990, 2), (key2990, 2), (key2969, 2)]

theorem rawRowCheck4970 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form11 = rawRow4970 := by decide +kernel

def row4970 : Integer.Sparse Key := [(key2591, -4), (key2594, -2), (key2601, 6), (key2770, 4), (key2773, 2), (key2890, -2), (key2911, -4), (key2932, -6), (key2969, 2), (key2990, 4)]

theorem rowCheck4970 : row4970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4970 := by decide +kernel

theorem rowEval4970 (x : Key → ℝ) : Integer.Sparse.eval row4970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4970, Integer.Sparse.eval_collectBalanced, rawRowCheck4970]

def rawRow4971 : Integer.Sparse Key := [(key2591, -2), (key2591, -2), (key2601, -2), (key2594, 6), (key2847, 2), (key2847, 2), (key2890, 2), (key2773, -2), (key2881, -2), (key2881, -2), (key2969, -6), (key2932, 2), (key2990, 2), (key2990, 2)]

theorem rawRowCheck4971 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form11 = rawRow4971 := by decide +kernel

def row4971 : Integer.Sparse Key := [(key2591, -4), (key2594, 6), (key2601, -2), (key2773, -2), (key2847, 4), (key2881, -4), (key2890, 2), (key2932, 2), (key2969, -6), (key2990, 4)]

theorem rowCheck4971 : row4971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4971 := by decide +kernel

theorem rowEval4971 (x : Key → ℝ) : Integer.Sparse.eval row4971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4971, Integer.Sparse.eval_collectBalanced, rawRowCheck4971]

def rawRow4972 : Integer.Sparse Key := [(key2591, -2), (key2601, -2), (key2591, -2), (key2594, 6), (key2847, 2), (key2890, 2), (key2847, 2), (key2881, -2), (key2773, -2), (key2881, -2), (key2969, -6), (key2990, 2), (key2932, 2), (key2990, 2)]

theorem rawRowCheck4972 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form11 = rawRow4972 := by decide +kernel

def row4972 : Integer.Sparse Key := [(key2591, -4), (key2594, 6), (key2601, -2), (key2773, -2), (key2847, 4), (key2881, -4), (key2890, 2), (key2932, 2), (key2969, -6), (key2990, 4)]

theorem rowCheck4972 : row4972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4972 := by decide +kernel

theorem rowEval4972 (x : Key → ℝ) : Integer.Sparse.eval row4972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4972, Integer.Sparse.eval_collectBalanced, rawRowCheck4972]

def rawRow4973 : Integer.Sparse Key := [(key2601, -2), (key2591, -2), (key2591, -2), (key2594, 6), (key2890, 2), (key2847, 2), (key2847, 2), (key2881, -2), (key2881, -2), (key2773, -2), (key2969, -6), (key2990, 2), (key2990, 2), (key2932, 2)]

theorem rawRowCheck4973 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form11 = rawRow4973 := by decide +kernel

def row4973 : Integer.Sparse Key := [(key2591, -4), (key2594, 6), (key2601, -2), (key2773, -2), (key2847, 4), (key2881, -4), (key2890, 2), (key2932, 2), (key2969, -6), (key2990, 4)]

theorem rowCheck4973 : row4973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4973 := by decide +kernel

theorem rowEval4973 (x : Key → ℝ) : Integer.Sparse.eval row4973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4973, Integer.Sparse.eval_collectBalanced, rawRowCheck4973]

def rawRow4974 : Integer.Sparse Key := [(key2770, -2), (key2770, -2), (key2773, -2), (key2932, 6), (key2591, 2), (key2591, 2), (key2594, 2), (key2969, -2), (key2990, -2), (key2990, -2), (key2601, -6), (key2890, 2), (key2911, 2), (key2911, 2)]

theorem rawRowCheck4974 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form11 = rawRow4974 := by decide +kernel

def row4974 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2601, -6), (key2770, -4), (key2773, -2), (key2890, 2), (key2911, 4), (key2932, 6), (key2969, -2), (key2990, -4)]

theorem rowCheck4974 : row4974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4974 := by decide +kernel

theorem rowEval4974 (x : Key → ℝ) : Integer.Sparse.eval row4974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4974, Integer.Sparse.eval_collectBalanced, rawRowCheck4974]

def rawRow4975 : Integer.Sparse Key := [(key2770, -2), (key2773, -2), (key2770, -2), (key2932, 6), (key2591, 2), (key2594, 2), (key2591, 2), (key2990, -2), (key2969, -2), (key2990, -2), (key2601, -6), (key2911, 2), (key2890, 2), (key2911, 2)]

theorem rawRowCheck4975 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form11 = rawRow4975 := by decide +kernel

def row4975 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2601, -6), (key2770, -4), (key2773, -2), (key2890, 2), (key2911, 4), (key2932, 6), (key2969, -2), (key2990, -4)]

theorem rowCheck4975 : row4975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4975 := by decide +kernel

theorem rowEval4975 (x : Key → ℝ) : Integer.Sparse.eval row4975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4975, Integer.Sparse.eval_collectBalanced, rawRowCheck4975]

def rawRow4976 : Integer.Sparse Key := [(key2773, -2), (key2770, -2), (key2770, -2), (key2932, 6), (key2594, 2), (key2591, 2), (key2591, 2), (key2990, -2), (key2990, -2), (key2969, -2), (key2601, -6), (key2911, 2), (key2911, 2), (key2890, 2)]

theorem rawRowCheck4976 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form11 = rawRow4976 := by decide +kernel

def row4976 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2601, -6), (key2770, -4), (key2773, -2), (key2890, 2), (key2911, 4), (key2932, 6), (key2969, -2), (key2990, -4)]

theorem rowCheck4976 : row4976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4976 := by decide +kernel

theorem rowEval4976 (x : Key → ℝ) : Integer.Sparse.eval row4976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4976, Integer.Sparse.eval_collectBalanced, rawRowCheck4976]

def rawRow4977 : Integer.Sparse Key := [(key2770, -2), (key2770, -2), (key2932, -2), (key2773, 6), (key2847, 2), (key2847, 2), (key2969, 2), (key2594, -2), (key2881, -2), (key2881, -2), (key2890, -6), (key2601, 2), (key2911, 2), (key2911, 2)]

theorem rawRowCheck4977 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form11 = rawRow4977 := by decide +kernel

def row4977 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2770, -4), (key2773, 6), (key2847, 4), (key2881, -4), (key2890, -6), (key2911, 4), (key2932, -2), (key2969, 2)]

theorem rowCheck4977 : row4977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4977 := by decide +kernel

theorem rowEval4977 (x : Key → ℝ) : Integer.Sparse.eval row4977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4977, Integer.Sparse.eval_collectBalanced, rawRowCheck4977]

def rawRow4978 : Integer.Sparse Key := [(key2770, -2), (key2932, -2), (key2770, -2), (key2773, 6), (key2847, 2), (key2969, 2), (key2847, 2), (key2881, -2), (key2594, -2), (key2881, -2), (key2890, -6), (key2911, 2), (key2601, 2), (key2911, 2)]

theorem rawRowCheck4978 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form11 = rawRow4978 := by decide +kernel

def row4978 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2770, -4), (key2773, 6), (key2847, 4), (key2881, -4), (key2890, -6), (key2911, 4), (key2932, -2), (key2969, 2)]

theorem rowCheck4978 : row4978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4978 := by decide +kernel

theorem rowEval4978 (x : Key → ℝ) : Integer.Sparse.eval row4978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4978, Integer.Sparse.eval_collectBalanced, rawRowCheck4978]

def rawRow4979 : Integer.Sparse Key := [(key2932, -2), (key2770, -2), (key2770, -2), (key2773, 6), (key2969, 2), (key2847, 2), (key2847, 2), (key2881, -2), (key2881, -2), (key2594, -2), (key2890, -6), (key2911, 2), (key2911, 2), (key2601, 2)]

theorem rawRowCheck4979 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form11 = rawRow4979 := by decide +kernel

def row4979 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2770, -4), (key2773, 6), (key2847, 4), (key2881, -4), (key2890, -6), (key2911, 4), (key2932, -2), (key2969, 2)]

theorem rowCheck4979 : row4979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4979 := by decide +kernel

theorem rowEval4979 (x : Key → ℝ) : Integer.Sparse.eval row4979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4979, Integer.Sparse.eval_collectBalanced, rawRowCheck4979]

def rawRow4980 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key2890, -2), (key2969, 6), (key2591, 2), (key2591, 2), (key2601, 2), (key2932, -2), (key2990, -2), (key2990, -2), (key2594, -6), (key2773, 2), (key2881, 2), (key2881, 2)]

theorem rawRowCheck4980 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form11 = rawRow4980 := by decide +kernel

def row4980 : Integer.Sparse Key := [(key2591, 4), (key2594, -6), (key2601, 2), (key2773, 2), (key2847, -4), (key2881, 4), (key2890, -2), (key2932, -2), (key2969, 6), (key2990, -4)]

theorem rowCheck4980 : row4980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4980 := by decide +kernel

theorem rowEval4980 (x : Key → ℝ) : Integer.Sparse.eval row4980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4980, Integer.Sparse.eval_collectBalanced, rawRowCheck4980]

def rawRow4981 : Integer.Sparse Key := [(key2847, -2), (key2890, -2), (key2847, -2), (key2969, 6), (key2591, 2), (key2601, 2), (key2591, 2), (key2990, -2), (key2932, -2), (key2990, -2), (key2594, -6), (key2881, 2), (key2773, 2), (key2881, 2)]

theorem rawRowCheck4981 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form11 = rawRow4981 := by decide +kernel

def row4981 : Integer.Sparse Key := [(key2591, 4), (key2594, -6), (key2601, 2), (key2773, 2), (key2847, -4), (key2881, 4), (key2890, -2), (key2932, -2), (key2969, 6), (key2990, -4)]

theorem rowCheck4981 : row4981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4981 := by decide +kernel

theorem rowEval4981 (x : Key → ℝ) : Integer.Sparse.eval row4981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4981, Integer.Sparse.eval_collectBalanced, rawRowCheck4981]

def rawRow4982 : Integer.Sparse Key := [(key2890, -2), (key2847, -2), (key2847, -2), (key2969, 6), (key2601, 2), (key2591, 2), (key2591, 2), (key2990, -2), (key2990, -2), (key2932, -2), (key2594, -6), (key2881, 2), (key2881, 2), (key2773, 2)]

theorem rawRowCheck4982 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form11 = rawRow4982 := by decide +kernel

def row4982 : Integer.Sparse Key := [(key2591, 4), (key2594, -6), (key2601, 2), (key2773, 2), (key2847, -4), (key2881, 4), (key2890, -2), (key2932, -2), (key2969, 6), (key2990, -4)]

theorem rowCheck4982 : row4982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4982 := by decide +kernel

theorem rowEval4982 (x : Key → ℝ) : Integer.Sparse.eval row4982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4982, Integer.Sparse.eval_collectBalanced, rawRowCheck4982]

def rawRow4983 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key2969, -2), (key2890, 6), (key2770, 2), (key2770, 2), (key2932, 2), (key2601, -2), (key2911, -2), (key2911, -2), (key2773, -6), (key2594, 2), (key2881, 2), (key2881, 2)]

theorem rawRowCheck4983 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form11 = rawRow4983 := by decide +kernel

def row4983 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -6), (key2847, -4), (key2881, 4), (key2890, 6), (key2911, -4), (key2932, 2), (key2969, -2)]

theorem rowCheck4983 : row4983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4983 := by decide +kernel

theorem rowEval4983 (x : Key → ℝ) : Integer.Sparse.eval row4983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4983, Integer.Sparse.eval_collectBalanced, rawRowCheck4983]

def rawRow4984 : Integer.Sparse Key := [(key2847, -2), (key2969, -2), (key2847, -2), (key2890, 6), (key2770, 2), (key2932, 2), (key2770, 2), (key2911, -2), (key2601, -2), (key2911, -2), (key2773, -6), (key2881, 2), (key2594, 2), (key2881, 2)]

theorem rawRowCheck4984 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form11 = rawRow4984 := by decide +kernel

def row4984 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -6), (key2847, -4), (key2881, 4), (key2890, 6), (key2911, -4), (key2932, 2), (key2969, -2)]

theorem rowCheck4984 : row4984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4984 := by decide +kernel

theorem rowEval4984 (x : Key → ℝ) : Integer.Sparse.eval row4984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4984, Integer.Sparse.eval_collectBalanced, rawRowCheck4984]

def rawRow4985 : Integer.Sparse Key := [(key2969, -2), (key2847, -2), (key2847, -2), (key2890, 6), (key2932, 2), (key2770, 2), (key2770, 2), (key2911, -2), (key2911, -2), (key2601, -2), (key2773, -6), (key2881, 2), (key2881, 2), (key2594, 2)]

theorem rawRowCheck4985 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form11 = rawRow4985 := by decide +kernel

def row4985 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -6), (key2847, -4), (key2881, 4), (key2890, 6), (key2911, -4), (key2932, 2), (key2969, -2)]

theorem rowCheck4985 : row4985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4985 := by decide +kernel

theorem rowEval4985 (x : Key → ℝ) : Integer.Sparse.eval row4985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4985, Integer.Sparse.eval_collectBalanced, rawRowCheck4985]

def rawRow4986 : Integer.Sparse Key := [(key2616, -2), (key2616, -2), (key2619, -2), (key2632, 1), (key2632, 1), (key2640, 1), (key2640, 1), (key2642, 1), (key2642, 1), (key2671, 2), (key2671, 2), (key2674, 2), (key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2729, -1), (key2729, -1), (key2786, -1), (key2786, -1), (key2794, -1), (key2794, -1), (key2796, -1), (key2796, -1), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2832, 1), (key2832, 1)]

theorem rawRowCheck4986 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form12 = rawRow4986 := by decide +kernel

def row4986 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, 2), (key2671, 4), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, -2), (key2786, -2), (key2794, -2), (key2796, -2), (key2809, 2), (key2829, 2), (key2832, 2)]

theorem rowCheck4986 : row4986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4986 := by decide +kernel

theorem rowEval4986 (x : Key → ℝ) : Integer.Sparse.eval row4986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4986, Integer.Sparse.eval_collectBalanced, rawRowCheck4986]

def rawRow4987 : Integer.Sparse Key := [(key2616, -2), (key2619, -2), (key2616, -2), (key2640, 1), (key2642, 1), (key2632, 1), (key2642, 1), (key2632, 1), (key2640, 1), (key2671, 2), (key2674, 2), (key2671, 2), (key2726, -1), (key2729, -1), (key2706, -1), (key2729, -1), (key2706, -1), (key2726, -1), (key2794, -1), (key2796, -1), (key2786, -1), (key2796, -1), (key2786, -1), (key2794, -1), (key2829, 1), (key2832, 1), (key2809, 1), (key2832, 1), (key2809, 1), (key2829, 1)]

theorem rawRowCheck4987 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form12 = rawRow4987 := by decide +kernel

def row4987 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, 2), (key2671, 4), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, -2), (key2786, -2), (key2794, -2), (key2796, -2), (key2809, 2), (key2829, 2), (key2832, 2)]

theorem rowCheck4987 : row4987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4987 := by decide +kernel

theorem rowEval4987 (x : Key → ℝ) : Integer.Sparse.eval row4987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4987, Integer.Sparse.eval_collectBalanced, rawRowCheck4987]

def rawRow4988 : Integer.Sparse Key := [(key2619, -2), (key2616, -2), (key2616, -2), (key2642, 1), (key2640, 1), (key2642, 1), (key2632, 1), (key2640, 1), (key2632, 1), (key2674, 2), (key2671, 2), (key2671, 2), (key2729, -1), (key2726, -1), (key2729, -1), (key2706, -1), (key2726, -1), (key2706, -1), (key2796, -1), (key2794, -1), (key2796, -1), (key2786, -1), (key2794, -1), (key2786, -1), (key2832, 1), (key2829, 1), (key2832, 1), (key2809, 1), (key2829, 1), (key2809, 1)]

theorem rawRowCheck4988 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form12 = rawRow4988 := by decide +kernel

def row4988 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, 2), (key2671, 4), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, -2), (key2786, -2), (key2794, -2), (key2796, -2), (key2809, 2), (key2829, 2), (key2832, 2)]

theorem rowCheck4988 : row4988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4988 := by decide +kernel

theorem rowEval4988 (x : Key → ℝ) : Integer.Sparse.eval row4988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4988, Integer.Sparse.eval_collectBalanced, rawRowCheck4988]

def rawRow4989 : Integer.Sparse Key := [(key2632, -2), (key2632, -2), (key2649, -2), (key2616, 1), (key2616, 1), (key2640, 1), (key2640, 1), (key2654, 1), (key2654, 1), (key2706, 2), (key2706, 2), (key2738, 2), (key2671, -1), (key2671, -1), (key2726, -1), (key2726, -1), (key2748, -1), (key2748, -1), (key2809, -1), (key2809, -1), (key2860, -1), (key2860, -1), (key2898, -1), (key2898, -1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1), (key2905, 1), (key2905, 1)]

theorem rawRowCheck4989 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form12 = rawRow4989 := by decide +kernel

def row4989 : Integer.Sparse Key := [(key2616, 2), (key2632, -4), (key2640, 2), (key2649, -2), (key2654, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2738, 2), (key2748, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2)]

theorem rowCheck4989 : row4989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4989 := by decide +kernel

theorem rowEval4989 (x : Key → ℝ) : Integer.Sparse.eval row4989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4989, Integer.Sparse.eval_collectBalanced, rawRowCheck4989]

def rawRow4990 : Integer.Sparse Key := [(key2632, -2), (key2649, -2), (key2632, -2), (key2640, 1), (key2654, 1), (key2616, 1), (key2654, 1), (key2616, 1), (key2640, 1), (key2706, 2), (key2738, 2), (key2706, 2), (key2726, -1), (key2748, -1), (key2671, -1), (key2748, -1), (key2671, -1), (key2726, -1), (key2860, -1), (key2898, -1), (key2809, -1), (key2898, -1), (key2809, -1), (key2860, -1), (key2870, 1), (key2905, 1), (key2786, 1), (key2905, 1), (key2786, 1), (key2870, 1)]

theorem rawRowCheck4990 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form12 = rawRow4990 := by decide +kernel

def row4990 : Integer.Sparse Key := [(key2616, 2), (key2632, -4), (key2640, 2), (key2649, -2), (key2654, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2738, 2), (key2748, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2)]

theorem rowCheck4990 : row4990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4990 := by decide +kernel

theorem rowEval4990 (x : Key → ℝ) : Integer.Sparse.eval row4990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4990, Integer.Sparse.eval_collectBalanced, rawRowCheck4990]

def rawRow4991 : Integer.Sparse Key := [(key2649, -2), (key2632, -2), (key2632, -2), (key2654, 1), (key2640, 1), (key2654, 1), (key2616, 1), (key2640, 1), (key2616, 1), (key2738, 2), (key2706, 2), (key2706, 2), (key2748, -1), (key2726, -1), (key2748, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2898, -1), (key2860, -1), (key2898, -1), (key2809, -1), (key2860, -1), (key2809, -1), (key2905, 1), (key2870, 1), (key2905, 1), (key2786, 1), (key2870, 1), (key2786, 1)]

theorem rawRowCheck4991 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form12 = rawRow4991 := by decide +kernel

def row4991 : Integer.Sparse Key := [(key2616, 2), (key2632, -4), (key2640, 2), (key2649, -2), (key2654, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2738, 2), (key2748, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2)]

theorem rowCheck4991 : row4991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4991 := by decide +kernel

theorem rowEval4991 (x : Key → ℝ) : Integer.Sparse.eval row4991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4991, Integer.Sparse.eval_collectBalanced, rawRowCheck4991]

end MUB6.Certificate.GramRows

end OAI
