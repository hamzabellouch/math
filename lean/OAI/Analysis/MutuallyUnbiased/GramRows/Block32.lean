import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1120 : Integer.Sparse Key := [(key2820, -2), (key2820, -2), (key2813, -2), (key2921, 1), (key2921, 1), (key2820, 1), (key2820, 1), (key2813, 1), (key2813, 1), (key2717, 2), (key2717, 2), (key2710, 2), (key3024, -1), (key3024, -1), (key2717, -1), (key2717, -1), (key2710, -1), (key2710, -1), (key2755, -1), (key2755, -1), (key2691, -1), (key2691, -1), (key2679, -1), (key2679, -1), (key3014, 1), (key3014, 1), (key2691, 1), (key2691, 1), (key2679, 1), (key3047, 1)]

theorem rawRowCheck1120 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form2 = rawRow1120 := by decide +kernel

def row1120 : Integer.Sparse Key := [(key2679, -1), (key2717, 2), (key2755, -2), (key2820, -2), (key2921, 2), (key3014, 2), (key3024, -2), (key3047, 1)]

theorem rowCheck1120 : row1120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1120 := by decide +kernel

theorem rowEval1120 (x : Key → ℝ) : Integer.Sparse.eval row1120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1120, Integer.Sparse.eval_collectBalanced, rawRowCheck1120]

def rawRow1121 : Integer.Sparse Key := [(key2921, -2), (key2921, -2), (key2921, -2), (key2820, 1), (key2820, 1), (key2820, 1), (key2820, 1), (key2820, 1), (key2820, 1), (key3024, 2), (key3024, 2), (key3024, 2), (key2717, -1), (key2717, -1), (key2717, -1), (key2717, -1), (key2717, -1), (key2717, -1), (key3014, -1), (key3014, -1), (key3014, -1), (key3014, -1), (key3014, -1), (key3014, -1), (key2755, 1), (key2755, 1), (key2755, 1), (key2755, 1), (key2755, 1), (key2755, 1)]

theorem rawRowCheck1121 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form2 = rawRow1121 := by decide +kernel

def row1121 : Integer.Sparse Key := [(key2717, -6), (key2755, 6), (key2820, 6), (key2921, -6), (key3014, -6), (key3024, 6)]

theorem rowCheck1121 : row1121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1121 := by decide +kernel

theorem rowEval1121 (x : Key → ℝ) : Integer.Sparse.eval row1121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1121, Integer.Sparse.eval_collectBalanced, rawRowCheck1121]

def rawRow1122 : Integer.Sparse Key := [(key3013, -2), (key3014, -2), (key3014, -2), (key3013, 1), (key3014, 1), (key3013, 1), (key3024, 1), (key3014, 1), (key3024, 1), (key2754, 2), (key2755, 2), (key2755, 2), (key2754, -1), (key2755, -1), (key2754, -1), (key2921, -1), (key2755, -1), (key2921, -1), (key2684, -1), (key2691, -1), (key2684, -1), (key2717, -1), (key2691, -1), (key2717, -1), (key2684, 1), (key2691, 1), (key2684, 1), (key2820, 1), (key2691, 1), (key2820, 1)]

theorem rawRowCheck1122 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form2 = rawRow1122 := by decide +kernel

def row1122 : Integer.Sparse Key := [(key2717, -2), (key2755, 2), (key2820, 2), (key2921, -2), (key3014, -2), (key3024, 2)]

theorem rowCheck1122 : row1122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1122 := by decide +kernel

theorem rowEval1122 (x : Key → ℝ) : Integer.Sparse.eval row1122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1122, Integer.Sparse.eval_collectBalanced, rawRowCheck1122]

def rawRow1123 : Integer.Sparse Key := [(key3014, -2), (key3013, -2), (key3014, -2), (key3014, 1), (key3013, 1), (key3024, 1), (key3013, 1), (key3024, 1), (key3014, 1), (key2755, 2), (key2754, 2), (key2755, 2), (key2755, -1), (key2754, -1), (key2921, -1), (key2754, -1), (key2921, -1), (key2755, -1), (key2691, -1), (key2684, -1), (key2717, -1), (key2684, -1), (key2717, -1), (key2691, -1), (key2691, 1), (key2684, 1), (key2820, 1), (key2684, 1), (key2820, 1), (key2691, 1)]

theorem rawRowCheck1123 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form2 = rawRow1123 := by decide +kernel

def row1123 : Integer.Sparse Key := [(key2717, -2), (key2755, 2), (key2820, 2), (key2921, -2), (key3014, -2), (key3024, 2)]

theorem rowCheck1123 : row1123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1123 := by decide +kernel

theorem rowEval1123 (x : Key → ℝ) : Integer.Sparse.eval row1123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1123, Integer.Sparse.eval_collectBalanced, rawRowCheck1123]

def rawRow1124 : Integer.Sparse Key := [(key3014, -2), (key3014, -2), (key3013, -2), (key3024, 1), (key3024, 1), (key3014, 1), (key3014, 1), (key3013, 1), (key3013, 1), (key2755, 2), (key2755, 2), (key2754, 2), (key2921, -1), (key2921, -1), (key2755, -1), (key2755, -1), (key2754, -1), (key2754, -1), (key2717, -1), (key2717, -1), (key2691, -1), (key2691, -1), (key2684, -1), (key2684, -1), (key2820, 1), (key2820, 1), (key2691, 1), (key2691, 1), (key2684, 1), (key2684, 1)]

theorem rawRowCheck1124 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form2 = rawRow1124 := by decide +kernel

def row1124 : Integer.Sparse Key := [(key2717, -2), (key2755, 2), (key2820, 2), (key2921, -2), (key3014, -2), (key3024, 2)]

theorem rowCheck1124 : row1124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1124 := by decide +kernel

theorem rowEval1124 (x : Key → ℝ) : Integer.Sparse.eval row1124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1124, Integer.Sparse.eval_collectBalanced, rawRowCheck1124]

def rawRow1125 : Integer.Sparse Key := [(key3024, -2), (key3024, -2), (key3024, -2), (key3014, 1), (key3014, 1), (key3014, 1), (key3014, 1), (key3014, 1), (key3014, 1), (key2921, 2), (key2921, 2), (key2921, 2), (key2755, -1), (key2755, -1), (key2755, -1), (key2755, -1), (key2755, -1), (key2755, -1), (key2820, -1), (key2820, -1), (key2820, -1), (key2820, -1), (key2820, -1), (key2820, -1), (key2717, 1), (key2717, 1), (key2717, 1), (key2717, 1), (key2717, 1), (key2717, 1)]

theorem rawRowCheck1125 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form2 = rawRow1125 := by decide +kernel

def row1125 : Integer.Sparse Key := [(key2717, 6), (key2755, -6), (key2820, -6), (key2921, 6), (key3014, 6), (key3024, -6)]

theorem rowCheck1125 : row1125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1125 := by decide +kernel

theorem rowEval1125 (x : Key → ℝ) : Integer.Sparse.eval row1125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1125, Integer.Sparse.eval_collectBalanced, rawRowCheck1125]

def rawRow1126 : Integer.Sparse Key := [(key1048, -2), (key1062, -2), (key1062, -2), (key1054, 6), (key1134, 2), (key1142, 2), (key1142, 2), (key1054, -2), (key1054, -2), (key1238, -2), (key1142, -6), (key1062, 2), (key1062, 2), (key1240, 2)]

theorem rawRowCheck1126 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form3 = rawRow1126 := by decide +kernel

def row1126 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

theorem rowCheck1126 : row1126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1126 := by decide +kernel

theorem rowEval1126 (x : Key → ℝ) : Integer.Sparse.eval row1126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1126, Integer.Sparse.eval_collectBalanced, rawRowCheck1126]

def rawRow1127 : Integer.Sparse Key := [(key1062, -2), (key1048, -2), (key1062, -2), (key1054, 6), (key1142, 2), (key1134, 2), (key1142, 2), (key1054, -2), (key1238, -2), (key1054, -2), (key1142, -6), (key1062, 2), (key1240, 2), (key1062, 2)]

theorem rawRowCheck1127 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form3 = rawRow1127 := by decide +kernel

def row1127 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

theorem rowCheck1127 : row1127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1127 := by decide +kernel

theorem rowEval1127 (x : Key → ℝ) : Integer.Sparse.eval row1127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1127, Integer.Sparse.eval_collectBalanced, rawRowCheck1127]

def rawRow1128 : Integer.Sparse Key := [(key1062, -2), (key1062, -2), (key1048, -2), (key1054, 6), (key1142, 2), (key1142, 2), (key1134, 2), (key1238, -2), (key1054, -2), (key1054, -2), (key1142, -6), (key1240, 2), (key1062, 2), (key1062, 2)]

theorem rawRowCheck1128 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form3 = rawRow1128 := by decide +kernel

def row1128 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

theorem rowCheck1128 : row1128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1128 := by decide +kernel

theorem rowEval1128 (x : Key → ℝ) : Integer.Sparse.eval row1128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1128, Integer.Sparse.eval_collectBalanced, rawRowCheck1128]

def rawRow1129 : Integer.Sparse Key := [(key1054, -2), (key1062, -2), (key1062, -2), (key1048, 6), (key1238, 2), (key1240, 2), (key1240, 2), (key1048, -2), (key1048, -2), (key1134, -2), (key1240, -6), (key1062, 2), (key1062, 2), (key1142, 2)]

theorem rawRowCheck1129 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form3 = rawRow1129 := by decide +kernel

def row1129 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

theorem rowCheck1129 : row1129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1129 := by decide +kernel

theorem rowEval1129 (x : Key → ℝ) : Integer.Sparse.eval row1129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1129, Integer.Sparse.eval_collectBalanced, rawRowCheck1129]

def rawRow1130 : Integer.Sparse Key := [(key1062, -2), (key1054, -2), (key1062, -2), (key1048, 6), (key1240, 2), (key1238, 2), (key1240, 2), (key1048, -2), (key1134, -2), (key1048, -2), (key1240, -6), (key1062, 2), (key1142, 2), (key1062, 2)]

theorem rawRowCheck1130 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form3 = rawRow1130 := by decide +kernel

def row1130 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

theorem rowCheck1130 : row1130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1130 := by decide +kernel

theorem rowEval1130 (x : Key → ℝ) : Integer.Sparse.eval row1130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1130, Integer.Sparse.eval_collectBalanced, rawRowCheck1130]

def rawRow1131 : Integer.Sparse Key := [(key1062, -2), (key1062, -2), (key1054, -2), (key1048, 6), (key1240, 2), (key1240, 2), (key1238, 2), (key1134, -2), (key1048, -2), (key1048, -2), (key1240, -6), (key1142, 2), (key1062, 2), (key1062, 2)]

theorem rawRowCheck1131 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form3 = rawRow1131 := by decide +kernel

def row1131 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

theorem rowCheck1131 : row1131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1131 := by decide +kernel

theorem rowEval1131 (x : Key → ℝ) : Integer.Sparse.eval row1131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1131, Integer.Sparse.eval_collectBalanced, rawRowCheck1131]

def rawRow1132 : Integer.Sparse Key := [(key1134, -2), (key1142, -2), (key1142, -2), (key1142, 6), (key1048, 2), (key1062, 2), (key1062, 2), (key1062, -2), (key1062, -2), (key1240, -2), (key1054, -6), (key1054, 2), (key1054, 2), (key1238, 2)]

theorem rawRowCheck1132 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form3 = rawRow1132 := by decide +kernel

def row1132 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

theorem rowCheck1132 : row1132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1132 := by decide +kernel

theorem rowEval1132 (x : Key → ℝ) : Integer.Sparse.eval row1132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1132, Integer.Sparse.eval_collectBalanced, rawRowCheck1132]

def rawRow1133 : Integer.Sparse Key := [(key1142, -2), (key1134, -2), (key1142, -2), (key1142, 6), (key1062, 2), (key1048, 2), (key1062, 2), (key1062, -2), (key1240, -2), (key1062, -2), (key1054, -6), (key1054, 2), (key1238, 2), (key1054, 2)]

theorem rawRowCheck1133 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form3 = rawRow1133 := by decide +kernel

def row1133 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

theorem rowCheck1133 : row1133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1133 := by decide +kernel

theorem rowEval1133 (x : Key → ℝ) : Integer.Sparse.eval row1133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1133, Integer.Sparse.eval_collectBalanced, rawRowCheck1133]

def rawRow1134 : Integer.Sparse Key := [(key1142, -2), (key1142, -2), (key1134, -2), (key1142, 6), (key1062, 2), (key1062, 2), (key1048, 2), (key1240, -2), (key1062, -2), (key1062, -2), (key1054, -6), (key1238, 2), (key1054, 2), (key1054, 2)]

theorem rawRowCheck1134 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form3 = rawRow1134 := by decide +kernel

def row1134 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

theorem rowCheck1134 : row1134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1134 := by decide +kernel

theorem rowEval1134 (x : Key → ℝ) : Integer.Sparse.eval row1134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1134, Integer.Sparse.eval_collectBalanced, rawRowCheck1134]

def rawRow1135 : Integer.Sparse Key := [(key1142, -2), (key1142, -2), (key1142, -2), (key1134, 6), (key1240, 2), (key1240, 2), (key1240, 2), (key1048, -2), (key1048, -2), (key1048, -2), (key1238, -6), (key1054, 2), (key1054, 2), (key1054, 2)]

theorem rawRowCheck1135 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form3 = rawRow1135 := by decide +kernel

def row1135 : Integer.Sparse Key := [(key1048, -6), (key1054, 6), (key1134, 6), (key1142, -6), (key1238, -6), (key1240, 6)]

theorem rowCheck1135 : row1135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1135 := by decide +kernel

theorem rowEval1135 (x : Key → ℝ) : Integer.Sparse.eval row1135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1135, Integer.Sparse.eval_collectBalanced, rawRowCheck1135]

def rawRow1136 : Integer.Sparse Key := [(key1238, -2), (key1240, -2), (key1240, -2), (key1240, 6), (key1054, 2), (key1062, 2), (key1062, 2), (key1062, -2), (key1062, -2), (key1142, -2), (key1048, -6), (key1048, 2), (key1048, 2), (key1134, 2)]

theorem rawRowCheck1136 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form3 = rawRow1136 := by decide +kernel

def row1136 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

theorem rowCheck1136 : row1136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1136 := by decide +kernel

theorem rowEval1136 (x : Key → ℝ) : Integer.Sparse.eval row1136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1136, Integer.Sparse.eval_collectBalanced, rawRowCheck1136]

def rawRow1137 : Integer.Sparse Key := [(key1240, -2), (key1238, -2), (key1240, -2), (key1240, 6), (key1062, 2), (key1054, 2), (key1062, 2), (key1062, -2), (key1142, -2), (key1062, -2), (key1048, -6), (key1048, 2), (key1134, 2), (key1048, 2)]

theorem rawRowCheck1137 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form3 = rawRow1137 := by decide +kernel

def row1137 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

theorem rowCheck1137 : row1137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1137 := by decide +kernel

theorem rowEval1137 (x : Key → ℝ) : Integer.Sparse.eval row1137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1137, Integer.Sparse.eval_collectBalanced, rawRowCheck1137]

def rawRow1138 : Integer.Sparse Key := [(key1240, -2), (key1240, -2), (key1238, -2), (key1240, 6), (key1062, 2), (key1062, 2), (key1054, 2), (key1142, -2), (key1062, -2), (key1062, -2), (key1048, -6), (key1134, 2), (key1048, 2), (key1048, 2)]

theorem rawRowCheck1138 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form3 = rawRow1138 := by decide +kernel

def row1138 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

theorem rowCheck1138 : row1138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1138 := by decide +kernel

theorem rowEval1138 (x : Key → ℝ) : Integer.Sparse.eval row1138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1138, Integer.Sparse.eval_collectBalanced, rawRowCheck1138]

def rawRow1139 : Integer.Sparse Key := [(key1240, -2), (key1240, -2), (key1240, -2), (key1238, 6), (key1142, 2), (key1142, 2), (key1142, 2), (key1054, -2), (key1054, -2), (key1054, -2), (key1134, -6), (key1048, 2), (key1048, 2), (key1048, 2)]

theorem rawRowCheck1139 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form3 = rawRow1139 := by decide +kernel

def row1139 : Integer.Sparse Key := [(key1048, 6), (key1054, -6), (key1134, -6), (key1142, 6), (key1238, 6), (key1240, -6)]

theorem rowCheck1139 : row1139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1139 := by decide +kernel

theorem rowEval1139 (x : Key → ℝ) : Integer.Sparse.eval row1139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1139, Integer.Sparse.eval_collectBalanced, rawRowCheck1139]

def rawRow1140 : Integer.Sparse Key := [(key3063, -6), (key3049, 2), (key3049, 2), (key3065, 2), (key3098, 6), (key3049, -2), (key3049, -2), (key3102, -2), (key3098, -2), (key3098, -2), (key3124, -2), (key3063, 2), (key3063, 2), (key3126, 2)]

theorem rawRowCheck1140 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form4 = rawRow1140 := by decide +kernel

def row1140 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

theorem rowCheck1140 : row1140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1140 := by decide +kernel

theorem rowEval1140 (x : Key → ℝ) : Integer.Sparse.eval row1140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1140, Integer.Sparse.eval_collectBalanced, rawRowCheck1140]

def rawRow1141 : Integer.Sparse Key := [(key3063, -6), (key3049, 2), (key3065, 2), (key3049, 2), (key3098, 6), (key3049, -2), (key3102, -2), (key3049, -2), (key3098, -2), (key3124, -2), (key3098, -2), (key3063, 2), (key3126, 2), (key3063, 2)]

theorem rawRowCheck1141 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form4 = rawRow1141 := by decide +kernel

def row1141 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

theorem rowCheck1141 : row1141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1141 := by decide +kernel

theorem rowEval1141 (x : Key → ℝ) : Integer.Sparse.eval row1141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1141, Integer.Sparse.eval_collectBalanced, rawRowCheck1141]

def rawRow1142 : Integer.Sparse Key := [(key3063, -6), (key3065, 2), (key3049, 2), (key3049, 2), (key3098, 6), (key3102, -2), (key3049, -2), (key3049, -2), (key3124, -2), (key3098, -2), (key3098, -2), (key3126, 2), (key3063, 2), (key3063, 2)]

theorem rawRowCheck1142 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form4 = rawRow1142 := by decide +kernel

def row1142 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

theorem rowCheck1142 : row1142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1142 := by decide +kernel

theorem rowEval1142 (x : Key → ℝ) : Integer.Sparse.eval row1142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1142, Integer.Sparse.eval_collectBalanced, rawRowCheck1142]

def rawRow1143 : Integer.Sparse Key := [(key3065, -6), (key3049, 2), (key3049, 2), (key3063, 2), (key3102, 6), (key3049, -2), (key3049, -2), (key3098, -2), (key3102, -2), (key3102, -2), (key3126, -2), (key3065, 2), (key3065, 2), (key3124, 2)]

theorem rawRowCheck1143 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form4 = rawRow1143 := by decide +kernel

def row1143 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

theorem rowCheck1143 : row1143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1143 := by decide +kernel

theorem rowEval1143 (x : Key → ℝ) : Integer.Sparse.eval row1143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1143, Integer.Sparse.eval_collectBalanced, rawRowCheck1143]

def rawRow1144 : Integer.Sparse Key := [(key3065, -6), (key3049, 2), (key3063, 2), (key3049, 2), (key3102, 6), (key3049, -2), (key3098, -2), (key3049, -2), (key3102, -2), (key3126, -2), (key3102, -2), (key3065, 2), (key3124, 2), (key3065, 2)]

theorem rawRowCheck1144 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form4 = rawRow1144 := by decide +kernel

def row1144 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

theorem rowCheck1144 : row1144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1144 := by decide +kernel

theorem rowEval1144 (x : Key → ℝ) : Integer.Sparse.eval row1144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1144, Integer.Sparse.eval_collectBalanced, rawRowCheck1144]

def rawRow1145 : Integer.Sparse Key := [(key3065, -6), (key3063, 2), (key3049, 2), (key3049, 2), (key3102, 6), (key3098, -2), (key3049, -2), (key3049, -2), (key3126, -2), (key3102, -2), (key3102, -2), (key3124, 2), (key3065, 2), (key3065, 2)]

theorem rawRowCheck1145 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form4 = rawRow1145 := by decide +kernel

def row1145 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

theorem rowCheck1145 : row1145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1145 := by decide +kernel

theorem rowEval1145 (x : Key → ℝ) : Integer.Sparse.eval row1145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1145, Integer.Sparse.eval_collectBalanced, rawRowCheck1145]

def rawRow1146 : Integer.Sparse Key := [(key3098, -6), (key3098, 2), (key3098, 2), (key3124, 2), (key3063, 6), (key3063, -2), (key3063, -2), (key3126, -2), (key3049, -2), (key3049, -2), (key3065, -2), (key3049, 2), (key3049, 2), (key3102, 2)]

theorem rawRowCheck1146 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form4 = rawRow1146 := by decide +kernel

def row1146 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

theorem rowCheck1146 : row1146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1146 := by decide +kernel

theorem rowEval1146 (x : Key → ℝ) : Integer.Sparse.eval row1146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1146, Integer.Sparse.eval_collectBalanced, rawRowCheck1146]

def rawRow1147 : Integer.Sparse Key := [(key3098, -6), (key3098, 2), (key3124, 2), (key3098, 2), (key3063, 6), (key3063, -2), (key3126, -2), (key3063, -2), (key3049, -2), (key3065, -2), (key3049, -2), (key3049, 2), (key3102, 2), (key3049, 2)]

theorem rawRowCheck1147 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form4 = rawRow1147 := by decide +kernel

def row1147 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

theorem rowCheck1147 : row1147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1147 := by decide +kernel

theorem rowEval1147 (x : Key → ℝ) : Integer.Sparse.eval row1147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1147, Integer.Sparse.eval_collectBalanced, rawRowCheck1147]

def rawRow1148 : Integer.Sparse Key := [(key3098, -6), (key3124, 2), (key3098, 2), (key3098, 2), (key3063, 6), (key3126, -2), (key3063, -2), (key3063, -2), (key3065, -2), (key3049, -2), (key3049, -2), (key3102, 2), (key3049, 2), (key3049, 2)]

theorem rawRowCheck1148 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form4 = rawRow1148 := by decide +kernel

def row1148 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

theorem rowCheck1148 : row1148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1148 := by decide +kernel

theorem rowEval1148 (x : Key → ℝ) : Integer.Sparse.eval row1148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1148, Integer.Sparse.eval_collectBalanced, rawRowCheck1148]

def rawRow1149 : Integer.Sparse Key := [(key3124, -6), (key3098, 2), (key3098, 2), (key3098, 2), (key3126, 6), (key3063, -2), (key3063, -2), (key3063, -2), (key3102, -2), (key3102, -2), (key3102, -2), (key3065, 2), (key3065, 2), (key3065, 2)]

theorem rawRowCheck1149 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form4 = rawRow1149 := by decide +kernel

def row1149 : Integer.Sparse Key := [(key3063, -6), (key3065, 6), (key3098, 6), (key3102, -6), (key3124, -6), (key3126, 6)]

theorem rowCheck1149 : row1149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1149 := by decide +kernel

theorem rowEval1149 (x : Key → ℝ) : Integer.Sparse.eval row1149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1149, Integer.Sparse.eval_collectBalanced, rawRowCheck1149]

def rawRow1150 : Integer.Sparse Key := [(key3102, -6), (key3102, 2), (key3102, 2), (key3126, 2), (key3065, 6), (key3065, -2), (key3065, -2), (key3124, -2), (key3049, -2), (key3049, -2), (key3063, -2), (key3049, 2), (key3049, 2), (key3098, 2)]

theorem rawRowCheck1150 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form4 = rawRow1150 := by decide +kernel

def row1150 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

theorem rowCheck1150 : row1150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1150 := by decide +kernel

theorem rowEval1150 (x : Key → ℝ) : Integer.Sparse.eval row1150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1150, Integer.Sparse.eval_collectBalanced, rawRowCheck1150]

def rawRow1151 : Integer.Sparse Key := [(key3102, -6), (key3102, 2), (key3126, 2), (key3102, 2), (key3065, 6), (key3065, -2), (key3124, -2), (key3065, -2), (key3049, -2), (key3063, -2), (key3049, -2), (key3049, 2), (key3098, 2), (key3049, 2)]

theorem rawRowCheck1151 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form4 = rawRow1151 := by decide +kernel

def row1151 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

theorem rowCheck1151 : row1151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1151 := by decide +kernel

theorem rowEval1151 (x : Key → ℝ) : Integer.Sparse.eval row1151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1151, Integer.Sparse.eval_collectBalanced, rawRowCheck1151]

end MUB6.Certificate.GramRows

end OAI
