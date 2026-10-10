import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9088 : Integer.Sparse Key := [(key979, -6), (key979, -6), (key979, -6), (key971, -6), (key1164, 2), (key1164, 2), (key1164, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1085, 2)]

theorem rawRowCheck9088 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow9088 := by decide +kernel

def row9088 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1164, 6)]

theorem rowCheck9088 : row9088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9088 := by decide +kernel

theorem rowEval9088 (x : Key → ℝ) : Integer.Sparse.eval row9088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9088, Integer.Sparse.eval_collectBalanced, rawRowCheck9088]

def rawRow9089 : Integer.Sparse Key := [(key1164, -6), (key1164, -6), (key1164, -6), (key1245, -6), (key979, 2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1228, 2), (key1228, 2), (key1228, 2)]

theorem rawRowCheck9089 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form4 = rawRow9089 := by decide +kernel

def row9089 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, -18), (key1228, 6), (key1245, -6)]

theorem rowCheck9089 : row9089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9089 := by decide +kernel

theorem rowEval9089 (x : Key → ℝ) : Integer.Sparse.eval row9089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9089, Integer.Sparse.eval_collectBalanced, rawRowCheck9089]

def rawRow9090 : Integer.Sparse Key := [(key1164, -6), (key1164, -6), (key1245, -6), (key1164, -6), (key1093, 2), (key1093, 2), (key1228, 2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1228, 2), (key1228, 2), (key979, 2), (key1093, 2), (key1093, 2)]

theorem rawRowCheck9090 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form4 = rawRow9090 := by decide +kernel

def row9090 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, -18), (key1228, 6), (key1245, -6)]

theorem rowCheck9090 : row9090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9090 := by decide +kernel

theorem rowEval9090 (x : Key → ℝ) : Integer.Sparse.eval row9090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9090, Integer.Sparse.eval_collectBalanced, rawRowCheck9090]

def rawRow9091 : Integer.Sparse Key := [(key1164, -6), (key1245, -6), (key1164, -6), (key1164, -6), (key1093, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1228, 2), (key979, 2), (key1228, 2), (key979, 2), (key1093, 2), (key1093, 2), (key979, 2), (key1093, 2)]

theorem rawRowCheck9091 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form4 = rawRow9091 := by decide +kernel

def row9091 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, -18), (key1228, 6), (key1245, -6)]

theorem rowCheck9091 : row9091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9091 := by decide +kernel

theorem rowEval9091 (x : Key → ℝ) : Integer.Sparse.eval row9091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9091, Integer.Sparse.eval_collectBalanced, rawRowCheck9091]

def rawRow9092 : Integer.Sparse Key := [(key1245, -6), (key1164, -6), (key1164, -6), (key1164, -6), (key1228, 2), (key1093, 2), (key1093, 2), (key1228, 2), (key1093, 2), (key1228, 2), (key979, 2), (key1093, 2), (key979, 2), (key1093, 2), (key1093, 2), (key979, 2)]

theorem rawRowCheck9092 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form4 = rawRow9092 := by decide +kernel

def row9092 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, -18), (key1228, 6), (key1245, -6)]

theorem rowCheck9092 : row9092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9092 := by decide +kernel

theorem rowEval9092 (x : Key → ℝ) : Integer.Sparse.eval row9092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck9092, Integer.Sparse.eval_collectBalanced, rawRowCheck9092]

def rawRow9093 : Integer.Sparse Key := [(key1028, -2), (key1036, -2), (key1036, -2), (key1028, -2), (key1036, -2), (key1028, -2), (key1071, -2), (key1036, -2), (key1071, -2), (key1036, -2), (key1036, -2), (key1071, -2), (key1106, 1), (key1114, 1), (key1106, 1), (key1123, 1), (key1114, 1), (key1123, 1), (key1106, 1), (key1114, 1), (key1106, 1), (key1150, 1), (key1114, 1), (key1150, 1), (key1106, 1), (key1123, 1), (key1106, 1), (key1150, 1), (key1123, 1), (key1150, 1), (key1114, 1), (key1123, 1), (key1114, 1), (key1150, 1), (key1123, 1), (key1150, 1)]

theorem rawRowCheck9093 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form5 = rawRow9093 := by decide +kernel

def row9093 : Integer.Sparse Key := [(key1028, -6), (key1036, -12), (key1071, -6), (key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6)]

theorem rowCheck9093 : row9093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9093 := by decide +kernel

theorem rowEval9093 (x : Key → ℝ) : Integer.Sparse.eval row9093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck9093, Integer.Sparse.eval_collectBalanced, rawRowCheck9093]

def rawRow9094 : Integer.Sparse Key := [(key1036, -2), (key1028, -2), (key1036, -2), (key1036, -2), (key1028, -2), (key1071, -2), (key1028, -2), (key1071, -2), (key1036, -2), (key1036, -2), (key1071, -2), (key1036, -2), (key1114, 1), (key1106, 1), (key1123, 1), (key1106, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1150, 1), (key1106, 1), (key1150, 1), (key1114, 1), (key1123, 1), (key1106, 1), (key1150, 1), (key1106, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1114, 1), (key1150, 1), (key1114, 1), (key1150, 1), (key1123, 1)]

theorem rawRowCheck9094 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form5 = rawRow9094 := by decide +kernel

def row9094 : Integer.Sparse Key := [(key1028, -6), (key1036, -12), (key1071, -6), (key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6)]

theorem rowCheck9094 : row9094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9094 := by decide +kernel

theorem rowEval9094 (x : Key → ℝ) : Integer.Sparse.eval row9094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9094, Integer.Sparse.eval_collectBalanced, rawRowCheck9094]

def rawRow9095 : Integer.Sparse Key := [(key1036, -2), (key1036, -2), (key1028, -2), (key1071, -2), (key1071, -2), (key1036, -2), (key1036, -2), (key1028, -2), (key1028, -2), (key1071, -2), (key1036, -2), (key1036, -2), (key1123, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1), (key1150, 1), (key1150, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1), (key1150, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1106, 1), (key1106, 1), (key1150, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1114, 1), (key1114, 1)]

theorem rawRowCheck9095 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form5 = rawRow9095 := by decide +kernel

def row9095 : Integer.Sparse Key := [(key1028, -6), (key1036, -12), (key1071, -6), (key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6)]

theorem rowCheck9095 : row9095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9095 := by decide +kernel

theorem rowEval9095 (x : Key → ℝ) : Integer.Sparse.eval row9095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9095, Integer.Sparse.eval_collectBalanced, rawRowCheck9095]

def rawRow9096 : Integer.Sparse Key := [(key1071, -2), (key1071, -2), (key1071, -2), (key1036, -2), (key1036, -2), (key1036, -2), (key1036, -2), (key1036, -2), (key1036, -2), (key1028, -2), (key1028, -2), (key1028, -2), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1), (key1106, 1), (key1106, 1), (key1106, 1), (key1106, 1)]

theorem rawRowCheck9096 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form5 = rawRow9096 := by decide +kernel

def row9096 : Integer.Sparse Key := [(key1028, -6), (key1036, -12), (key1071, -6), (key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6)]

theorem rowCheck9096 : row9096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9096 := by decide +kernel

theorem rowEval9096 (x : Key → ℝ) : Integer.Sparse.eval row9096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9096, Integer.Sparse.eval_collectBalanced, rawRowCheck9096]

def rawRow9097 : Integer.Sparse Key := [(key1015, -2), (key1015, -2), (key1015, -2), (key1123, -2), (key1123, -2), (key1123, -2), (key1123, -2), (key1123, -2), (key1123, -2), (key1235, -2), (key1235, -2), (key1235, -2), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1), (key1232, 1), (key1232, 1), (key1232, 1), (key1232, 1)]

theorem rawRowCheck9097 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form5 = rawRow9097 := by decide +kernel

def row9097 : Integer.Sparse Key := [(key1001, 6), (key1015, -6), (key1036, 6), (key1114, 6), (key1123, -12), (key1232, 6), (key1235, -6)]

theorem rowCheck9097 : row9097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9097 := by decide +kernel

theorem rowEval9097 (x : Key → ℝ) : Integer.Sparse.eval row9097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9097, Integer.Sparse.eval_collectBalanced, rawRowCheck9097]

def rawRow9098 : Integer.Sparse Key := [(key1123, -2), (key1123, -2), (key1235, -2), (key1015, -2), (key1015, -2), (key1123, -2), (key1123, -2), (key1235, -2), (key1235, -2), (key1015, -2), (key1123, -2), (key1123, -2), (key1036, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1), (key1001, 1), (key1001, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1), (key1001, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1232, 1), (key1232, 1), (key1001, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1114, 1), (key1114, 1)]

theorem rawRowCheck9098 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form5 = rawRow9098 := by decide +kernel

def row9098 : Integer.Sparse Key := [(key1001, 6), (key1015, -6), (key1036, 6), (key1114, 6), (key1123, -12), (key1232, 6), (key1235, -6)]

theorem rowCheck9098 : row9098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9098 := by decide +kernel

theorem rowEval9098 (x : Key → ℝ) : Integer.Sparse.eval row9098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9098, Integer.Sparse.eval_collectBalanced, rawRowCheck9098]

def rawRow9099 : Integer.Sparse Key := [(key1123, -2), (key1235, -2), (key1123, -2), (key1123, -2), (key1235, -2), (key1015, -2), (key1235, -2), (key1015, -2), (key1123, -2), (key1123, -2), (key1015, -2), (key1123, -2), (key1114, 1), (key1232, 1), (key1036, 1), (key1232, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1001, 1), (key1232, 1), (key1001, 1), (key1114, 1), (key1036, 1), (key1232, 1), (key1001, 1), (key1232, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1114, 1), (key1001, 1), (key1114, 1), (key1001, 1), (key1036, 1)]

theorem rawRowCheck9099 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form5 = rawRow9099 := by decide +kernel

def row9099 : Integer.Sparse Key := [(key1001, 6), (key1015, -6), (key1036, 6), (key1114, 6), (key1123, -12), (key1232, 6), (key1235, -6)]

theorem rowCheck9099 : row9099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9099 := by decide +kernel

theorem rowEval9099 (x : Key → ℝ) : Integer.Sparse.eval row9099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9099, Integer.Sparse.eval_collectBalanced, rawRowCheck9099]

def rawRow9100 : Integer.Sparse Key := [(key1235, -2), (key1123, -2), (key1123, -2), (key1235, -2), (key1123, -2), (key1235, -2), (key1015, -2), (key1123, -2), (key1015, -2), (key1123, -2), (key1123, -2), (key1015, -2), (key1232, 1), (key1114, 1), (key1232, 1), (key1036, 1), (key1114, 1), (key1036, 1), (key1232, 1), (key1114, 1), (key1232, 1), (key1001, 1), (key1114, 1), (key1001, 1), (key1232, 1), (key1036, 1), (key1232, 1), (key1001, 1), (key1036, 1), (key1001, 1), (key1114, 1), (key1036, 1), (key1114, 1), (key1001, 1), (key1036, 1), (key1001, 1)]

theorem rawRowCheck9100 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form5 = rawRow9100 := by decide +kernel

def row9100 : Integer.Sparse Key := [(key1001, 6), (key1015, -6), (key1036, 6), (key1114, 6), (key1123, -12), (key1232, 6), (key1235, -6)]

theorem rowCheck9100 : row9100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9100 := by decide +kernel

theorem rowEval9100 (x : Key → ℝ) : Integer.Sparse.eval row9100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck9100, Integer.Sparse.eval_collectBalanced, rawRowCheck9100]

def rawRow9101 : Integer.Sparse Key := [(key973, -24), (key1087, 6), (key1087, 6), (key1087, 6), (key1160, 6)]

theorem rawRowCheck9101 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form6 = rawRow9101 := by decide +kernel

def row9101 : Integer.Sparse Key := [(key973, -24), (key1087, 18), (key1160, 6)]

theorem rowCheck9101 : row9101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9101 := by decide +kernel

theorem rowEval9101 (x : Key → ℝ) : Integer.Sparse.eval row9101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9101, Integer.Sparse.eval_collectBalanced, rawRowCheck9101]

def rawRow9102 : Integer.Sparse Key := [(key973, -24), (key1087, 6), (key1087, 6), (key1160, 6), (key1087, 6)]

theorem rawRowCheck9102 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form6 = rawRow9102 := by decide +kernel

def row9102 : Integer.Sparse Key := [(key973, -24), (key1087, 18), (key1160, 6)]

theorem rowCheck9102 : row9102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9102 := by decide +kernel

theorem rowEval9102 (x : Key → ℝ) : Integer.Sparse.eval row9102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9102, Integer.Sparse.eval_collectBalanced, rawRowCheck9102]

def rawRow9103 : Integer.Sparse Key := [(key973, -24), (key1087, 6), (key1160, 6), (key1087, 6), (key1087, 6)]

theorem rawRowCheck9103 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form6 = rawRow9103 := by decide +kernel

def row9103 : Integer.Sparse Key := [(key973, -24), (key1087, 18), (key1160, 6)]

theorem rowCheck9103 : row9103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9103 := by decide +kernel

theorem rowEval9103 (x : Key → ℝ) : Integer.Sparse.eval row9103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9103, Integer.Sparse.eval_collectBalanced, rawRowCheck9103]

def rawRow9104 : Integer.Sparse Key := [(key973, -24), (key1160, 6), (key1087, 6), (key1087, 6), (key1087, 6)]

theorem rawRowCheck9104 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow9104 := by decide +kernel

def row9104 : Integer.Sparse Key := [(key973, -24), (key1087, 18), (key1160, 6)]

theorem rowCheck9104 : row9104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9104 := by decide +kernel

theorem rowEval9104 (x : Key → ℝ) : Integer.Sparse.eval row9104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9104, Integer.Sparse.eval_collectBalanced, rawRowCheck9104]

def rawRow9105 : Integer.Sparse Key := [(key1160, -24), (key973, 6), (key1087, 6), (key1087, 6), (key1087, 6)]

theorem rawRowCheck9105 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form6 = rawRow9105 := by decide +kernel

def row9105 : Integer.Sparse Key := [(key973, 6), (key1087, 18), (key1160, -24)]

theorem rowCheck9105 : row9105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9105 := by decide +kernel

theorem rowEval9105 (x : Key → ℝ) : Integer.Sparse.eval row9105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9105, Integer.Sparse.eval_collectBalanced, rawRowCheck9105]

def rawRow9106 : Integer.Sparse Key := [(key1160, -24), (key1087, 6), (key973, 6), (key1087, 6), (key1087, 6)]

theorem rawRowCheck9106 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form6 = rawRow9106 := by decide +kernel

def row9106 : Integer.Sparse Key := [(key973, 6), (key1087, 18), (key1160, -24)]

theorem rowCheck9106 : row9106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9106 := by decide +kernel

theorem rowEval9106 (x : Key → ℝ) : Integer.Sparse.eval row9106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9106, Integer.Sparse.eval_collectBalanced, rawRowCheck9106]

def rawRow9107 : Integer.Sparse Key := [(key1160, -24), (key1087, 6), (key1087, 6), (key973, 6), (key1087, 6)]

theorem rawRowCheck9107 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form6 = rawRow9107 := by decide +kernel

def row9107 : Integer.Sparse Key := [(key973, 6), (key1087, 18), (key1160, -24)]

theorem rowCheck9107 : row9107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9107 := by decide +kernel

theorem rowEval9107 (x : Key → ℝ) : Integer.Sparse.eval row9107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9107, Integer.Sparse.eval_collectBalanced, rawRowCheck9107]

def rawRow9108 : Integer.Sparse Key := [(key1160, -24), (key1087, 6), (key1087, 6), (key1087, 6), (key973, 6)]

theorem rawRowCheck9108 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form6 = rawRow9108 := by decide +kernel

def row9108 : Integer.Sparse Key := [(key973, 6), (key1087, 18), (key1160, -24)]

theorem rowCheck9108 : row9108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9108 := by decide +kernel

theorem rowEval9108 (x : Key → ℝ) : Integer.Sparse.eval row9108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck9108, Integer.Sparse.eval_collectBalanced, rawRowCheck9108]

def rawRow9109 : Integer.Sparse Key := [(key993, -2), (key1001, -2), (key1001, -2), (key993, -2), (key1001, -2), (key993, -2), (key1015, -2), (key1001, -2), (key1015, -2), (key1001, -2), (key1001, -2), (key1015, -2), (key1028, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1071, 2)]

theorem rawRowCheck9109 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form7 = rawRow9109 := by decide +kernel

def row9109 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 6), (key1036, 12), (key1071, 6)]

theorem rowCheck9109 : row9109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9109 := by decide +kernel

theorem rowEval9109 (x : Key → ℝ) : Integer.Sparse.eval row9109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck9109, Integer.Sparse.eval_collectBalanced, rawRowCheck9109]

def rawRow9110 : Integer.Sparse Key := [(key1001, -2), (key993, -2), (key1001, -2), (key1001, -2), (key993, -2), (key1015, -2), (key993, -2), (key1015, -2), (key1001, -2), (key1001, -2), (key1015, -2), (key1001, -2), (key1036, 2), (key1028, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1071, 2), (key1036, 2)]

theorem rawRowCheck9110 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form7 = rawRow9110 := by decide +kernel

def row9110 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 6), (key1036, 12), (key1071, 6)]

theorem rowCheck9110 : row9110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9110 := by decide +kernel

theorem rowEval9110 (x : Key → ℝ) : Integer.Sparse.eval row9110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9110, Integer.Sparse.eval_collectBalanced, rawRowCheck9110]

def rawRow9111 : Integer.Sparse Key := [(key1001, -2), (key1001, -2), (key993, -2), (key1015, -2), (key1015, -2), (key1001, -2), (key1001, -2), (key993, -2), (key993, -2), (key1015, -2), (key1001, -2), (key1001, -2), (key1036, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1036, 2)]

theorem rawRowCheck9111 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form7 = rawRow9111 := by decide +kernel

def row9111 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 6), (key1036, 12), (key1071, 6)]

theorem rowCheck9111 : row9111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9111 := by decide +kernel

theorem rowEval9111 (x : Key → ℝ) : Integer.Sparse.eval row9111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9111, Integer.Sparse.eval_collectBalanced, rawRowCheck9111]

def rawRow9112 : Integer.Sparse Key := [(key1015, -2), (key1015, -2), (key1015, -2), (key1001, -2), (key1001, -2), (key1001, -2), (key1001, -2), (key1001, -2), (key1001, -2), (key993, -2), (key993, -2), (key993, -2), (key1071, 2), (key1071, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1028, 2), (key1028, 2)]

theorem rawRowCheck9112 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow9112 := by decide +kernel

def row9112 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 6), (key1036, 12), (key1071, 6)]

theorem rowCheck9112 : row9112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9112 := by decide +kernel

theorem rowEval9112 (x : Key → ℝ) : Integer.Sparse.eval row9112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9112, Integer.Sparse.eval_collectBalanced, rawRowCheck9112]

def rawRow9113 : Integer.Sparse Key := [(key1071, -2), (key1071, -2), (key1071, -2), (key1150, -2), (key1150, -2), (key1150, -2), (key1150, -2), (key1150, -2), (key1150, -2), (key1242, -2), (key1242, -2), (key1242, -2), (key1015, 2), (key1015, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1235, 2), (key1235, 2)]

theorem rawRowCheck9113 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form7 = rawRow9113 := by decide +kernel

def row9113 : Integer.Sparse Key := [(key1015, 6), (key1071, -6), (key1123, 12), (key1150, -12), (key1235, 6), (key1242, -6)]

theorem rowCheck9113 : row9113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9113 := by decide +kernel

theorem rowEval9113 (x : Key → ℝ) : Integer.Sparse.eval row9113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9113, Integer.Sparse.eval_collectBalanced, rawRowCheck9113]

def rawRow9114 : Integer.Sparse Key := [(key1150, -2), (key1150, -2), (key1242, -2), (key1071, -2), (key1071, -2), (key1150, -2), (key1150, -2), (key1242, -2), (key1242, -2), (key1071, -2), (key1150, -2), (key1150, -2), (key1123, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1123, 2)]

theorem rawRowCheck9114 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form7 = rawRow9114 := by decide +kernel

def row9114 : Integer.Sparse Key := [(key1015, 6), (key1071, -6), (key1123, 12), (key1150, -12), (key1235, 6), (key1242, -6)]

theorem rowCheck9114 : row9114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9114 := by decide +kernel

theorem rowEval9114 (x : Key → ℝ) : Integer.Sparse.eval row9114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9114, Integer.Sparse.eval_collectBalanced, rawRowCheck9114]

def rawRow9115 : Integer.Sparse Key := [(key1150, -2), (key1242, -2), (key1150, -2), (key1150, -2), (key1242, -2), (key1071, -2), (key1242, -2), (key1071, -2), (key1150, -2), (key1150, -2), (key1071, -2), (key1150, -2), (key1123, 2), (key1235, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1015, 2), (key1123, 2)]

theorem rawRowCheck9115 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form7 = rawRow9115 := by decide +kernel

def row9115 : Integer.Sparse Key := [(key1015, 6), (key1071, -6), (key1123, 12), (key1150, -12), (key1235, 6), (key1242, -6)]

theorem rowCheck9115 : row9115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9115 := by decide +kernel

theorem rowEval9115 (x : Key → ℝ) : Integer.Sparse.eval row9115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9115, Integer.Sparse.eval_collectBalanced, rawRowCheck9115]

def rawRow9116 : Integer.Sparse Key := [(key1242, -2), (key1150, -2), (key1150, -2), (key1242, -2), (key1150, -2), (key1242, -2), (key1071, -2), (key1150, -2), (key1071, -2), (key1150, -2), (key1150, -2), (key1071, -2), (key1235, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1015, 2)]

theorem rawRowCheck9116 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form7 = rawRow9116 := by decide +kernel

def row9116 : Integer.Sparse Key := [(key1015, 6), (key1071, -6), (key1123, 12), (key1150, -12), (key1235, 6), (key1242, -6)]

theorem rowCheck9116 : row9116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9116 := by decide +kernel

theorem rowEval9116 (x : Key → ℝ) : Integer.Sparse.eval row9116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck9116, Integer.Sparse.eval_collectBalanced, rawRowCheck9116]

def rawRow9117 : Integer.Sparse Key := [(key43, -2), (key48, -2), (key48, -2), (key43, -2), (key48, -2), (key43, -2), (key74, -2), (key48, -2), (key74, -2), (key48, -2), (key48, -2), (key74, -2), (key100, 1), (key105, 1), (key100, 1), (key115, 1), (key105, 1), (key115, 1), (key100, 1), (key105, 1), (key100, 1), (key137, 1), (key105, 1), (key137, 1), (key100, 1), (key115, 1), (key100, 1), (key137, 1), (key115, 1), (key137, 1), (key105, 1), (key115, 1), (key105, 1), (key137, 1), (key115, 1), (key137, 1)]

theorem rawRowCheck9117 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form8 = rawRow9117 := by decide +kernel

def row9117 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key100, 6), (key105, 6), (key115, 6), (key137, 6)]

theorem rowCheck9117 : row9117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9117 := by decide +kernel

theorem rowEval9117 (x : Key → ℝ) : Integer.Sparse.eval row9117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck9117, Integer.Sparse.eval_collectBalanced, rawRowCheck9117]

def rawRow9118 : Integer.Sparse Key := [(key48, -2), (key43, -2), (key48, -2), (key48, -2), (key43, -2), (key74, -2), (key43, -2), (key74, -2), (key48, -2), (key48, -2), (key74, -2), (key48, -2), (key105, 1), (key100, 1), (key115, 1), (key100, 1), (key115, 1), (key105, 1), (key105, 1), (key100, 1), (key137, 1), (key100, 1), (key137, 1), (key105, 1), (key115, 1), (key100, 1), (key137, 1), (key100, 1), (key137, 1), (key115, 1), (key115, 1), (key105, 1), (key137, 1), (key105, 1), (key137, 1), (key115, 1)]

theorem rawRowCheck9118 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form8 = rawRow9118 := by decide +kernel

def row9118 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key100, 6), (key105, 6), (key115, 6), (key137, 6)]

theorem rowCheck9118 : row9118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9118 := by decide +kernel

theorem rowEval9118 (x : Key → ℝ) : Integer.Sparse.eval row9118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9118, Integer.Sparse.eval_collectBalanced, rawRowCheck9118]

def rawRow9119 : Integer.Sparse Key := [(key48, -2), (key48, -2), (key43, -2), (key74, -2), (key74, -2), (key48, -2), (key48, -2), (key43, -2), (key43, -2), (key74, -2), (key48, -2), (key48, -2), (key115, 1), (key115, 1), (key105, 1), (key105, 1), (key100, 1), (key100, 1), (key137, 1), (key137, 1), (key105, 1), (key105, 1), (key100, 1), (key100, 1), (key137, 1), (key137, 1), (key115, 1), (key115, 1), (key100, 1), (key100, 1), (key137, 1), (key137, 1), (key115, 1), (key115, 1), (key105, 1), (key105, 1)]

theorem rawRowCheck9119 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form8 = rawRow9119 := by decide +kernel

def row9119 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key100, 6), (key105, 6), (key115, 6), (key137, 6)]

theorem rowCheck9119 : row9119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9119 := by decide +kernel

theorem rowEval9119 (x : Key → ℝ) : Integer.Sparse.eval row9119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9119, Integer.Sparse.eval_collectBalanced, rawRowCheck9119]

def rawRow9120 : Integer.Sparse Key := [(key74, -2), (key74, -2), (key74, -2), (key48, -2), (key48, -2), (key48, -2), (key48, -2), (key48, -2), (key48, -2), (key43, -2), (key43, -2), (key43, -2), (key137, 1), (key137, 1), (key137, 1), (key137, 1), (key137, 1), (key137, 1), (key115, 1), (key115, 1), (key115, 1), (key115, 1), (key115, 1), (key115, 1), (key105, 1), (key105, 1), (key105, 1), (key105, 1), (key105, 1), (key105, 1), (key100, 1), (key100, 1), (key100, 1), (key100, 1), (key100, 1), (key100, 1)]

theorem rawRowCheck9120 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form8 = rawRow9120 := by decide +kernel

def row9120 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key100, 6), (key105, 6), (key115, 6), (key137, 6)]

theorem rowCheck9120 : row9120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9120 := by decide +kernel

theorem rowEval9120 (x : Key → ℝ) : Integer.Sparse.eval row9120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9120, Integer.Sparse.eval_collectBalanced, rawRowCheck9120]

def rawRow9121 : Integer.Sparse Key := [(key218, -2), (key218, -2), (key218, -2), (key486, -2), (key486, -2), (key486, -2), (key486, -2), (key486, -2), (key486, -2), (key490, -2), (key490, -2), (key490, -2), (key212, 1), (key212, 1), (key212, 1), (key212, 1), (key212, 1), (key212, 1), (key381, 1), (key381, 1), (key381, 1), (key381, 1), (key381, 1), (key381, 1), (key432, 1), (key432, 1), (key432, 1), (key432, 1), (key432, 1), (key432, 1), (key460, 1), (key460, 1), (key460, 1), (key460, 1), (key460, 1), (key460, 1)]

theorem rawRowCheck9121 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form8 = rawRow9121 := by decide +kernel

def row9121 : Integer.Sparse Key := [(key212, 6), (key218, -6), (key381, 6), (key432, 6), (key460, 6), (key486, -12), (key490, -6)]

theorem rowCheck9121 : row9121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9121 := by decide +kernel

theorem rowEval9121 (x : Key → ℝ) : Integer.Sparse.eval row9121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9121, Integer.Sparse.eval_collectBalanced, rawRowCheck9121]

def rawRow9122 : Integer.Sparse Key := [(key486, -2), (key486, -2), (key490, -2), (key218, -2), (key218, -2), (key486, -2), (key486, -2), (key490, -2), (key490, -2), (key218, -2), (key486, -2), (key486, -2), (key381, 1), (key381, 1), (key432, 1), (key432, 1), (key460, 1), (key460, 1), (key212, 1), (key212, 1), (key432, 1), (key432, 1), (key460, 1), (key460, 1), (key212, 1), (key212, 1), (key381, 1), (key381, 1), (key460, 1), (key460, 1), (key212, 1), (key212, 1), (key381, 1), (key381, 1), (key432, 1), (key432, 1)]

theorem rawRowCheck9122 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form8 = rawRow9122 := by decide +kernel

def row9122 : Integer.Sparse Key := [(key212, 6), (key218, -6), (key381, 6), (key432, 6), (key460, 6), (key486, -12), (key490, -6)]

theorem rowCheck9122 : row9122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9122 := by decide +kernel

theorem rowEval9122 (x : Key → ℝ) : Integer.Sparse.eval row9122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9122, Integer.Sparse.eval_collectBalanced, rawRowCheck9122]

def rawRow9123 : Integer.Sparse Key := [(key486, -2), (key490, -2), (key486, -2), (key486, -2), (key490, -2), (key218, -2), (key490, -2), (key218, -2), (key486, -2), (key486, -2), (key218, -2), (key486, -2), (key432, 1), (key460, 1), (key381, 1), (key460, 1), (key381, 1), (key432, 1), (key432, 1), (key460, 1), (key212, 1), (key460, 1), (key212, 1), (key432, 1), (key381, 1), (key460, 1), (key212, 1), (key460, 1), (key212, 1), (key381, 1), (key381, 1), (key432, 1), (key212, 1), (key432, 1), (key212, 1), (key381, 1)]

theorem rawRowCheck9123 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form8 = rawRow9123 := by decide +kernel

def row9123 : Integer.Sparse Key := [(key212, 6), (key218, -6), (key381, 6), (key432, 6), (key460, 6), (key486, -12), (key490, -6)]

theorem rowCheck9123 : row9123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9123 := by decide +kernel

theorem rowEval9123 (x : Key → ℝ) : Integer.Sparse.eval row9123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9123, Integer.Sparse.eval_collectBalanced, rawRowCheck9123]

def rawRow9124 : Integer.Sparse Key := [(key490, -2), (key486, -2), (key486, -2), (key490, -2), (key486, -2), (key490, -2), (key218, -2), (key486, -2), (key218, -2), (key486, -2), (key486, -2), (key218, -2), (key460, 1), (key432, 1), (key460, 1), (key381, 1), (key432, 1), (key381, 1), (key460, 1), (key432, 1), (key460, 1), (key212, 1), (key432, 1), (key212, 1), (key460, 1), (key381, 1), (key460, 1), (key212, 1), (key381, 1), (key212, 1), (key432, 1), (key381, 1), (key432, 1), (key212, 1), (key381, 1), (key212, 1)]

theorem rawRowCheck9124 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form8 = rawRow9124 := by decide +kernel

def row9124 : Integer.Sparse Key := [(key212, 6), (key218, -6), (key381, 6), (key432, 6), (key460, 6), (key486, -12), (key490, -6)]

theorem rowCheck9124 : row9124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9124 := by decide +kernel

theorem rowEval9124 (x : Key → ℝ) : Integer.Sparse.eval row9124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck9124, Integer.Sparse.eval_collectBalanced, rawRowCheck9124]

def rawRow9125 : Integer.Sparse Key := [(key1106, 1), (key1114, 1), (key1106, 1), (key1123, 1), (key1114, 1), (key1123, 1), (key1106, 1), (key1114, 1), (key1106, 1), (key1150, 1), (key1114, 1), (key1150, 1), (key1106, 1), (key1123, 1), (key1106, 1), (key1150, 1), (key1123, 1), (key1150, 1), (key1114, 1), (key1123, 1), (key1114, 1), (key1150, 1), (key1123, 1), (key1150, 1), (key1232, -2), (key1232, -2), (key1235, -2), (key1232, -2), (key1232, -2), (key1242, -2), (key1232, -2), (key1235, -2), (key1232, -2), (key1242, -2), (key1235, -2), (key1242, -2)]

theorem rawRowCheck9125 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form9 = rawRow9125 := by decide +kernel

def row9125 : Integer.Sparse Key := [(key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck9125 : row9125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9125 := by decide +kernel

theorem rowEval9125 (x : Key → ℝ) : Integer.Sparse.eval row9125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck9125, Integer.Sparse.eval_collectBalanced, rawRowCheck9125]

def rawRow9126 : Integer.Sparse Key := [(key1114, 1), (key1106, 1), (key1123, 1), (key1106, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1150, 1), (key1106, 1), (key1150, 1), (key1114, 1), (key1123, 1), (key1106, 1), (key1150, 1), (key1106, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1114, 1), (key1150, 1), (key1114, 1), (key1150, 1), (key1123, 1), (key1232, -2), (key1235, -2), (key1232, -2), (key1232, -2), (key1242, -2), (key1232, -2), (key1235, -2), (key1232, -2), (key1242, -2), (key1232, -2), (key1242, -2), (key1235, -2)]

theorem rawRowCheck9126 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form9 = rawRow9126 := by decide +kernel

def row9126 : Integer.Sparse Key := [(key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck9126 : row9126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9126 := by decide +kernel

theorem rowEval9126 (x : Key → ℝ) : Integer.Sparse.eval row9126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9126, Integer.Sparse.eval_collectBalanced, rawRowCheck9126]

def rawRow9127 : Integer.Sparse Key := [(key1123, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1), (key1150, 1), (key1150, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1), (key1150, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1106, 1), (key1106, 1), (key1150, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1235, -2), (key1232, -2), (key1232, -2), (key1242, -2), (key1232, -2), (key1232, -2), (key1242, -2), (key1242, -2), (key1235, -2), (key1235, -2), (key1232, -2), (key1232, -2)]

theorem rawRowCheck9127 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form9 = rawRow9127 := by decide +kernel

def row9127 : Integer.Sparse Key := [(key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck9127 : row9127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9127 := by decide +kernel

theorem rowEval9127 (x : Key → ℝ) : Integer.Sparse.eval row9127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9127, Integer.Sparse.eval_collectBalanced, rawRowCheck9127]

def rawRow9128 : Integer.Sparse Key := [(key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1), (key1106, 1), (key1106, 1), (key1106, 1), (key1106, 1), (key1242, -2), (key1242, -2), (key1242, -2), (key1235, -2), (key1235, -2), (key1235, -2), (key1232, -2), (key1232, -2), (key1232, -2), (key1232, -2), (key1232, -2), (key1232, -2)]

theorem rawRowCheck9128 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form9 = rawRow9128 := by decide +kernel

def row9128 : Integer.Sparse Key := [(key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck9128 : row9128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9128 := by decide +kernel

theorem rowEval9128 (x : Key → ℝ) : Integer.Sparse.eval row9128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9128, Integer.Sparse.eval_collectBalanced, rawRowCheck9128]

def rawRow9129 : Integer.Sparse Key := [(key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1), (key1232, 1), (key1232, 1), (key1232, 1), (key1232, 1), (key993, -2), (key993, -2), (key993, -2), (key1028, -2), (key1028, -2), (key1028, -2), (key1106, -2), (key1106, -2), (key1106, -2), (key1106, -2), (key1106, -2), (key1106, -2)]

theorem rawRowCheck9129 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form9 = rawRow9129 := by decide +kernel

def row9129 : Integer.Sparse Key := [(key993, -6), (key1001, 6), (key1028, -6), (key1036, 6), (key1106, -12), (key1114, 6), (key1232, 6)]

theorem rowCheck9129 : row9129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9129 := by decide +kernel

theorem rowEval9129 (x : Key → ℝ) : Integer.Sparse.eval row9129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9129, Integer.Sparse.eval_collectBalanced, rawRowCheck9129]

def rawRow9130 : Integer.Sparse Key := [(key1036, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1), (key1001, 1), (key1001, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1), (key1001, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1232, 1), (key1232, 1), (key1001, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1028, -2), (key1106, -2), (key1106, -2), (key993, -2), (key1106, -2), (key1106, -2), (key993, -2), (key993, -2), (key1028, -2), (key1028, -2), (key1106, -2), (key1106, -2)]

theorem rawRowCheck9130 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form9 = rawRow9130 := by decide +kernel

def row9130 : Integer.Sparse Key := [(key993, -6), (key1001, 6), (key1028, -6), (key1036, 6), (key1106, -12), (key1114, 6), (key1232, 6)]

theorem rowCheck9130 : row9130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9130 := by decide +kernel

theorem rowEval9130 (x : Key → ℝ) : Integer.Sparse.eval row9130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9130, Integer.Sparse.eval_collectBalanced, rawRowCheck9130]

def rawRow9131 : Integer.Sparse Key := [(key1114, 1), (key1232, 1), (key1036, 1), (key1232, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1001, 1), (key1232, 1), (key1001, 1), (key1114, 1), (key1036, 1), (key1232, 1), (key1001, 1), (key1232, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1114, 1), (key1001, 1), (key1114, 1), (key1001, 1), (key1036, 1), (key1106, -2), (key1028, -2), (key1106, -2), (key1106, -2), (key993, -2), (key1106, -2), (key1028, -2), (key1106, -2), (key993, -2), (key1106, -2), (key993, -2), (key1028, -2)]

theorem rawRowCheck9131 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form9 = rawRow9131 := by decide +kernel

def row9131 : Integer.Sparse Key := [(key993, -6), (key1001, 6), (key1028, -6), (key1036, 6), (key1106, -12), (key1114, 6), (key1232, 6)]

theorem rowCheck9131 : row9131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9131 := by decide +kernel

theorem rowEval9131 (x : Key → ℝ) : Integer.Sparse.eval row9131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9131, Integer.Sparse.eval_collectBalanced, rawRowCheck9131]

def rawRow9132 : Integer.Sparse Key := [(key1232, 1), (key1114, 1), (key1232, 1), (key1036, 1), (key1114, 1), (key1036, 1), (key1232, 1), (key1114, 1), (key1232, 1), (key1001, 1), (key1114, 1), (key1001, 1), (key1232, 1), (key1036, 1), (key1232, 1), (key1001, 1), (key1036, 1), (key1001, 1), (key1114, 1), (key1036, 1), (key1114, 1), (key1001, 1), (key1036, 1), (key1001, 1), (key1106, -2), (key1106, -2), (key1028, -2), (key1106, -2), (key1106, -2), (key993, -2), (key1106, -2), (key1028, -2), (key1106, -2), (key993, -2), (key1028, -2), (key993, -2)]

theorem rawRowCheck9132 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form9 = rawRow9132 := by decide +kernel

def row9132 : Integer.Sparse Key := [(key993, -6), (key1001, 6), (key1028, -6), (key1036, 6), (key1106, -12), (key1114, 6), (key1232, 6)]

theorem rowCheck9132 : row9132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9132 := by decide +kernel

theorem rowEval9132 (x : Key → ℝ) : Integer.Sparse.eval row9132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck9132, Integer.Sparse.eval_collectBalanced, rawRowCheck9132]

def rawRow9133 : Integer.Sparse Key := [(key45, -6), (key45, -6), (key45, -6), (key70, -6), (key102, 2), (key102, 2), (key111, 2), (key102, 2), (key102, 2), (key133, 2), (key102, 2), (key111, 2), (key102, 2), (key133, 2), (key111, 2), (key133, 2)]

theorem rawRowCheck9133 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form10 = rawRow9133 := by decide +kernel

def row9133 : Integer.Sparse Key := [(key45, -18), (key70, -6), (key102, 12), (key111, 6), (key133, 6)]

theorem rowCheck9133 : row9133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9133 := by decide +kernel

theorem rowEval9133 (x : Key → ℝ) : Integer.Sparse.eval row9133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9133, Integer.Sparse.eval_collectBalanced, rawRowCheck9133]

def rawRow9134 : Integer.Sparse Key := [(key45, -6), (key45, -6), (key70, -6), (key45, -6), (key102, 2), (key111, 2), (key102, 2), (key102, 2), (key133, 2), (key102, 2), (key111, 2), (key102, 2), (key133, 2), (key102, 2), (key133, 2), (key111, 2)]

theorem rawRowCheck9134 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form10 = rawRow9134 := by decide +kernel

def row9134 : Integer.Sparse Key := [(key45, -18), (key70, -6), (key102, 12), (key111, 6), (key133, 6)]

theorem rowCheck9134 : row9134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9134 := by decide +kernel

theorem rowEval9134 (x : Key → ℝ) : Integer.Sparse.eval row9134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9134, Integer.Sparse.eval_collectBalanced, rawRowCheck9134]

def rawRow9135 : Integer.Sparse Key := [(key45, -6), (key70, -6), (key45, -6), (key45, -6), (key111, 2), (key102, 2), (key102, 2), (key133, 2), (key102, 2), (key102, 2), (key133, 2), (key133, 2), (key111, 2), (key111, 2), (key102, 2), (key102, 2)]

theorem rawRowCheck9135 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form10 = rawRow9135 := by decide +kernel

def row9135 : Integer.Sparse Key := [(key45, -18), (key70, -6), (key102, 12), (key111, 6), (key133, 6)]

theorem rowCheck9135 : row9135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9135 := by decide +kernel

theorem rowEval9135 (x : Key → ℝ) : Integer.Sparse.eval row9135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9135, Integer.Sparse.eval_collectBalanced, rawRowCheck9135]

def rawRow9136 : Integer.Sparse Key := [(key70, -6), (key45, -6), (key45, -6), (key45, -6), (key133, 2), (key133, 2), (key133, 2), (key111, 2), (key111, 2), (key111, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2)]

theorem rawRowCheck9136 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow9136 := by decide +kernel

def row9136 : Integer.Sparse Key := [(key45, -18), (key70, -6), (key102, 12), (key111, 6), (key133, 6)]

theorem rowCheck9136 : row9136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9136 := by decide +kernel

theorem rowEval9136 (x : Key → ℝ) : Integer.Sparse.eval row9136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9136, Integer.Sparse.eval_collectBalanced, rawRowCheck9136]

def rawRow9137 : Integer.Sparse Key := [(key31, -6), (key111, -6), (key111, -6), (key111, -6), (key20, 2), (key20, 2), (key20, 2), (key45, 2), (key45, 2), (key45, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2)]

theorem rawRowCheck9137 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form10 = rawRow9137 := by decide +kernel

def row9137 : Integer.Sparse Key := [(key20, 6), (key31, -6), (key45, 6), (key102, 12), (key111, -18)]

theorem rowCheck9137 : row9137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9137 := by decide +kernel

theorem rowEval9137 (x : Key → ℝ) : Integer.Sparse.eval row9137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9137, Integer.Sparse.eval_collectBalanced, rawRowCheck9137]

def rawRow9138 : Integer.Sparse Key := [(key111, -6), (key31, -6), (key111, -6), (key111, -6), (key45, 2), (key102, 2), (key102, 2), (key20, 2), (key102, 2), (key102, 2), (key20, 2), (key20, 2), (key45, 2), (key45, 2), (key102, 2), (key102, 2)]

theorem rawRowCheck9138 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form10 = rawRow9138 := by decide +kernel

def row9138 : Integer.Sparse Key := [(key20, 6), (key31, -6), (key45, 6), (key102, 12), (key111, -18)]

theorem rowCheck9138 : row9138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9138 := by decide +kernel

theorem rowEval9138 (x : Key → ℝ) : Integer.Sparse.eval row9138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9138, Integer.Sparse.eval_collectBalanced, rawRowCheck9138]

def rawRow9139 : Integer.Sparse Key := [(key111, -6), (key111, -6), (key31, -6), (key111, -6), (key102, 2), (key45, 2), (key102, 2), (key102, 2), (key20, 2), (key102, 2), (key45, 2), (key102, 2), (key20, 2), (key102, 2), (key20, 2), (key45, 2)]

theorem rawRowCheck9139 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form10 = rawRow9139 := by decide +kernel

def row9139 : Integer.Sparse Key := [(key20, 6), (key31, -6), (key45, 6), (key102, 12), (key111, -18)]

theorem rowCheck9139 : row9139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9139 := by decide +kernel

theorem rowEval9139 (x : Key → ℝ) : Integer.Sparse.eval row9139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9139, Integer.Sparse.eval_collectBalanced, rawRowCheck9139]

def rawRow9140 : Integer.Sparse Key := [(key111, -6), (key111, -6), (key111, -6), (key31, -6), (key102, 2), (key102, 2), (key45, 2), (key102, 2), (key102, 2), (key20, 2), (key102, 2), (key45, 2), (key102, 2), (key20, 2), (key45, 2), (key20, 2)]

theorem rawRowCheck9140 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form10 = rawRow9140 := by decide +kernel

def row9140 : Integer.Sparse Key := [(key20, 6), (key31, -6), (key45, 6), (key102, 12), (key111, -18)]

theorem rowCheck9140 : row9140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9140 := by decide +kernel

theorem rowEval9140 (x : Key → ℝ) : Integer.Sparse.eval row9140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck9140, Integer.Sparse.eval_collectBalanced, rawRowCheck9140]

def rawRow9141 : Integer.Sparse Key := [(key972, 6), (key977, 6), (key977, 6), (key977, 6), (key1181, -6), (key1181, -6), (key1181, -6), (key1218, -6)]

theorem rawRowCheck9141 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form11 = rawRow9141 := by decide +kernel

def row9141 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1181, -18), (key1218, -6)]

theorem rowCheck9141 : row9141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9141 := by decide +kernel

theorem rowEval9141 (x : Key → ℝ) : Integer.Sparse.eval row9141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9141, Integer.Sparse.eval_collectBalanced, rawRowCheck9141]

def rawRow9142 : Integer.Sparse Key := [(key977, 6), (key972, 6), (key977, 6), (key977, 6), (key1181, -6), (key1181, -6), (key1218, -6), (key1181, -6)]

theorem rawRowCheck9142 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form11 = rawRow9142 := by decide +kernel

def row9142 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1181, -18), (key1218, -6)]

theorem rowCheck9142 : row9142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9142 := by decide +kernel

theorem rowEval9142 (x : Key → ℝ) : Integer.Sparse.eval row9142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9142, Integer.Sparse.eval_collectBalanced, rawRowCheck9142]

def rawRow9143 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key972, 6), (key977, 6), (key1181, -6), (key1218, -6), (key1181, -6), (key1181, -6)]

theorem rawRowCheck9143 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form11 = rawRow9143 := by decide +kernel

def row9143 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1181, -18), (key1218, -6)]

theorem rowCheck9143 : row9143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9143 := by decide +kernel

theorem rowEval9143 (x : Key → ℝ) : Integer.Sparse.eval row9143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9143, Integer.Sparse.eval_collectBalanced, rawRowCheck9143]

def rawRow9144 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key977, 6), (key972, 6), (key1218, -6), (key1181, -6), (key1181, -6), (key1181, -6)]

theorem rawRowCheck9144 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form11 = rawRow9144 := by decide +kernel

def row9144 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1181, -18), (key1218, -6)]

theorem rowCheck9144 : row9144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9144 := by decide +kernel

theorem rowEval9144 (x : Key → ℝ) : Integer.Sparse.eval row9144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9144, Integer.Sparse.eval_collectBalanced, rawRowCheck9144]

def rawRow9145 : Integer.Sparse Key := [(key1162, 6), (key1162, 6), (key1162, 6), (key1218, 6), (key972, -6), (key1086, -6), (key1086, -6), (key1086, -6)]

theorem rawRowCheck9145 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form11 = rawRow9145 := by decide +kernel

def row9145 : Integer.Sparse Key := [(key972, -6), (key1086, -18), (key1162, 18), (key1218, 6)]

theorem rowCheck9145 : row9145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9145 := by decide +kernel

theorem rowEval9145 (x : Key → ℝ) : Integer.Sparse.eval row9145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9145, Integer.Sparse.eval_collectBalanced, rawRowCheck9145]

def rawRow9146 : Integer.Sparse Key := [(key1162, 6), (key1162, 6), (key1218, 6), (key1162, 6), (key1086, -6), (key972, -6), (key1086, -6), (key1086, -6)]

theorem rawRowCheck9146 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form11 = rawRow9146 := by decide +kernel

def row9146 : Integer.Sparse Key := [(key972, -6), (key1086, -18), (key1162, 18), (key1218, 6)]

theorem rowCheck9146 : row9146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9146 := by decide +kernel

theorem rowEval9146 (x : Key → ℝ) : Integer.Sparse.eval row9146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9146, Integer.Sparse.eval_collectBalanced, rawRowCheck9146]

def rawRow9147 : Integer.Sparse Key := [(key1162, 6), (key1218, 6), (key1162, 6), (key1162, 6), (key1086, -6), (key1086, -6), (key972, -6), (key1086, -6)]

theorem rawRowCheck9147 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form11 = rawRow9147 := by decide +kernel

def row9147 : Integer.Sparse Key := [(key972, -6), (key1086, -18), (key1162, 18), (key1218, 6)]

theorem rowCheck9147 : row9147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9147 := by decide +kernel

theorem rowEval9147 (x : Key → ℝ) : Integer.Sparse.eval row9147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9147, Integer.Sparse.eval_collectBalanced, rawRowCheck9147]

def rawRow9148 : Integer.Sparse Key := [(key1218, 6), (key1162, 6), (key1162, 6), (key1162, 6), (key1086, -6), (key1086, -6), (key1086, -6), (key972, -6)]

theorem rawRowCheck9148 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form11 = rawRow9148 := by decide +kernel

def row9148 : Integer.Sparse Key := [(key972, -6), (key1086, -18), (key1162, 18), (key1218, 6)]

theorem rowCheck9148 : row9148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9148 := by decide +kernel

theorem rowEval9148 (x : Key → ℝ) : Integer.Sparse.eval row9148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck9148, Integer.Sparse.eval_collectBalanced, rawRowCheck9148]

def rawRow9149 : Integer.Sparse Key := [(key971, 6), (key979, 6), (key979, 6), (key979, 6), (key1228, -6), (key1228, -6), (key1228, -6), (key1245, -6)]

theorem rawRowCheck9149 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form12 = rawRow9149 := by decide +kernel

def row9149 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1228, -18), (key1245, -6)]

theorem rowCheck9149 : row9149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9149 := by decide +kernel

theorem rowEval9149 (x : Key → ℝ) : Integer.Sparse.eval row9149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9149, Integer.Sparse.eval_collectBalanced, rawRowCheck9149]

def rawRow9150 : Integer.Sparse Key := [(key979, 6), (key971, 6), (key979, 6), (key979, 6), (key1228, -6), (key1228, -6), (key1245, -6), (key1228, -6)]

theorem rawRowCheck9150 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form12 = rawRow9150 := by decide +kernel

def row9150 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1228, -18), (key1245, -6)]

theorem rowCheck9150 : row9150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9150 := by decide +kernel

theorem rowEval9150 (x : Key → ℝ) : Integer.Sparse.eval row9150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9150, Integer.Sparse.eval_collectBalanced, rawRowCheck9150]

def rawRow9151 : Integer.Sparse Key := [(key979, 6), (key979, 6), (key971, 6), (key979, 6), (key1228, -6), (key1245, -6), (key1228, -6), (key1228, -6)]

theorem rawRowCheck9151 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form12 = rawRow9151 := by decide +kernel

def row9151 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1228, -18), (key1245, -6)]

theorem rowCheck9151 : row9151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9151 := by decide +kernel

theorem rowEval9151 (x : Key → ℝ) : Integer.Sparse.eval row9151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9151, Integer.Sparse.eval_collectBalanced, rawRowCheck9151]

def rawRow9152 : Integer.Sparse Key := [(key979, 6), (key979, 6), (key979, 6), (key971, 6), (key1245, -6), (key1228, -6), (key1228, -6), (key1228, -6)]

theorem rawRowCheck9152 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form12 = rawRow9152 := by decide +kernel

def row9152 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1228, -18), (key1245, -6)]

theorem rowCheck9152 : row9152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9152 := by decide +kernel

theorem rowEval9152 (x : Key → ℝ) : Integer.Sparse.eval row9152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9152, Integer.Sparse.eval_collectBalanced, rawRowCheck9152]

def rawRow9153 : Integer.Sparse Key := [(key1164, 6), (key1164, 6), (key1164, 6), (key1245, 6), (key971, -6), (key1085, -6), (key1085, -6), (key1085, -6)]

theorem rawRowCheck9153 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form12 = rawRow9153 := by decide +kernel

def row9153 : Integer.Sparse Key := [(key971, -6), (key1085, -18), (key1164, 18), (key1245, 6)]

theorem rowCheck9153 : row9153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9153 := by decide +kernel

theorem rowEval9153 (x : Key → ℝ) : Integer.Sparse.eval row9153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9153, Integer.Sparse.eval_collectBalanced, rawRowCheck9153]

def rawRow9154 : Integer.Sparse Key := [(key1164, 6), (key1164, 6), (key1245, 6), (key1164, 6), (key1085, -6), (key971, -6), (key1085, -6), (key1085, -6)]

theorem rawRowCheck9154 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form12 = rawRow9154 := by decide +kernel

def row9154 : Integer.Sparse Key := [(key971, -6), (key1085, -18), (key1164, 18), (key1245, 6)]

theorem rowCheck9154 : row9154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9154 := by decide +kernel

theorem rowEval9154 (x : Key → ℝ) : Integer.Sparse.eval row9154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9154, Integer.Sparse.eval_collectBalanced, rawRowCheck9154]

def rawRow9155 : Integer.Sparse Key := [(key1164, 6), (key1245, 6), (key1164, 6), (key1164, 6), (key1085, -6), (key1085, -6), (key971, -6), (key1085, -6)]

theorem rawRowCheck9155 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form12 = rawRow9155 := by decide +kernel

def row9155 : Integer.Sparse Key := [(key971, -6), (key1085, -18), (key1164, 18), (key1245, 6)]

theorem rowCheck9155 : row9155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9155 := by decide +kernel

theorem rowEval9155 (x : Key → ℝ) : Integer.Sparse.eval row9155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9155, Integer.Sparse.eval_collectBalanced, rawRowCheck9155]

def rawRow9156 : Integer.Sparse Key := [(key1245, 6), (key1164, 6), (key1164, 6), (key1164, 6), (key1085, -6), (key1085, -6), (key1085, -6), (key971, -6)]

theorem rawRowCheck9156 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form12 = rawRow9156 := by decide +kernel

def row9156 : Integer.Sparse Key := [(key971, -6), (key1085, -18), (key1164, 18), (key1245, 6)]

theorem rowCheck9156 : row9156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9156 := by decide +kernel

theorem rowEval9156 (x : Key → ℝ) : Integer.Sparse.eval row9156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck9156, Integer.Sparse.eval_collectBalanced, rawRowCheck9156]

def rawRow9157 : Integer.Sparse Key := [(key713, -6), (key715, -6), (key715, -6), (key715, -6), (key890, 2), (key892, 2), (key892, 2), (key890, 2), (key892, 2), (key890, 2), (key959, 2), (key892, 2), (key959, 2), (key892, 2), (key892, 2), (key959, 2)]

theorem rawRowCheck9157 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form13 = rawRow9157 := by decide +kernel

def row9157 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key959, 6)]

theorem rowCheck9157 : row9157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9157 := by decide +kernel

theorem rowEval9157 (x : Key → ℝ) : Integer.Sparse.eval row9157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9157, Integer.Sparse.eval_collectBalanced, rawRowCheck9157]

def rawRow9158 : Integer.Sparse Key := [(key715, -6), (key713, -6), (key715, -6), (key715, -6), (key892, 2), (key890, 2), (key892, 2), (key892, 2), (key890, 2), (key959, 2), (key890, 2), (key959, 2), (key892, 2), (key892, 2), (key959, 2), (key892, 2)]

theorem rawRowCheck9158 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form13 = rawRow9158 := by decide +kernel

def row9158 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key959, 6)]

theorem rowCheck9158 : row9158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9158 := by decide +kernel

theorem rowEval9158 (x : Key → ℝ) : Integer.Sparse.eval row9158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9158, Integer.Sparse.eval_collectBalanced, rawRowCheck9158]

def rawRow9159 : Integer.Sparse Key := [(key715, -6), (key715, -6), (key713, -6), (key715, -6), (key892, 2), (key892, 2), (key890, 2), (key959, 2), (key959, 2), (key892, 2), (key892, 2), (key890, 2), (key890, 2), (key959, 2), (key892, 2), (key892, 2)]

theorem rawRowCheck9159 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form13 = rawRow9159 := by decide +kernel

def row9159 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key959, 6)]

theorem rowCheck9159 : row9159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9159 := by decide +kernel

theorem rowEval9159 (x : Key → ℝ) : Integer.Sparse.eval row9159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9159, Integer.Sparse.eval_collectBalanced, rawRowCheck9159]

def rawRow9160 : Integer.Sparse Key := [(key715, -6), (key715, -6), (key715, -6), (key713, -6), (key959, 2), (key959, 2), (key959, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key890, 2), (key890, 2), (key890, 2)]

theorem rawRowCheck9160 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9160 := by decide +kernel

def row9160 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key959, 6)]

theorem rowCheck9160 : row9160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9160 := by decide +kernel

theorem rowEval9160 (x : Key → ℝ) : Integer.Sparse.eval row9160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9160, Integer.Sparse.eval_collectBalanced, rawRowCheck9160]

def rawRow9161 : Integer.Sparse Key := [(key959, -6), (key959, -6), (key959, -6), (key966, -6), (key715, 2), (key715, 2), (key715, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key914, 2), (key914, 2), (key914, 2)]

theorem rawRowCheck9161 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9161 := by decide +kernel

def row9161 : Integer.Sparse Key := [(key715, 6), (key892, 12), (key914, 6), (key959, -18), (key966, -6)]

theorem rowCheck9161 : row9161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9161 := by decide +kernel

theorem rowEval9161 (x : Key → ℝ) : Integer.Sparse.eval row9161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9161, Integer.Sparse.eval_collectBalanced, rawRowCheck9161]

def rawRow9162 : Integer.Sparse Key := [(key959, -6), (key959, -6), (key966, -6), (key959, -6), (key892, 2), (key892, 2), (key914, 2), (key715, 2), (key715, 2), (key892, 2), (key892, 2), (key914, 2), (key914, 2), (key715, 2), (key892, 2), (key892, 2)]

theorem rawRowCheck9162 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form13 = rawRow9162 := by decide +kernel

def row9162 : Integer.Sparse Key := [(key715, 6), (key892, 12), (key914, 6), (key959, -18), (key966, -6)]

theorem rowCheck9162 : row9162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9162 := by decide +kernel

theorem rowEval9162 (x : Key → ℝ) : Integer.Sparse.eval row9162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9162, Integer.Sparse.eval_collectBalanced, rawRowCheck9162]

def rawRow9163 : Integer.Sparse Key := [(key959, -6), (key966, -6), (key959, -6), (key959, -6), (key892, 2), (key914, 2), (key892, 2), (key892, 2), (key914, 2), (key715, 2), (key914, 2), (key715, 2), (key892, 2), (key892, 2), (key715, 2), (key892, 2)]

theorem rawRowCheck9163 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form13 = rawRow9163 := by decide +kernel

def row9163 : Integer.Sparse Key := [(key715, 6), (key892, 12), (key914, 6), (key959, -18), (key966, -6)]

theorem rowCheck9163 : row9163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9163 := by decide +kernel

theorem rowEval9163 (x : Key → ℝ) : Integer.Sparse.eval row9163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9163, Integer.Sparse.eval_collectBalanced, rawRowCheck9163]

def rawRow9164 : Integer.Sparse Key := [(key966, -6), (key959, -6), (key959, -6), (key959, -6), (key914, 2), (key892, 2), (key892, 2), (key914, 2), (key892, 2), (key914, 2), (key715, 2), (key892, 2), (key715, 2), (key892, 2), (key892, 2), (key715, 2)]

theorem rawRowCheck9164 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form13 = rawRow9164 := by decide +kernel

def row9164 : Integer.Sparse Key := [(key715, 6), (key892, 12), (key914, 6), (key959, -18), (key966, -6)]

theorem rowCheck9164 : row9164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9164 := by decide +kernel

theorem rowEval9164 (x : Key → ℝ) : Integer.Sparse.eval row9164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck9164, Integer.Sparse.eval_collectBalanced, rawRowCheck9164]

def rawRow9165 : Integer.Sparse Key := [(key1, 6), (key7, 6), (key7, 6), (key7, 6), (key193, -6), (key193, -6), (key193, -6), (key202, -6)]

theorem rawRowCheck9165 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form14 = rawRow9165 := by decide +kernel

def row9165 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key193, -18), (key202, -6)]

theorem rowCheck9165 : row9165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9165 := by decide +kernel

theorem rowEval9165 (x : Key → ℝ) : Integer.Sparse.eval row9165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9165, Integer.Sparse.eval_collectBalanced, rawRowCheck9165]

def rawRow9166 : Integer.Sparse Key := [(key7, 6), (key1, 6), (key7, 6), (key7, 6), (key193, -6), (key193, -6), (key202, -6), (key193, -6)]

theorem rawRowCheck9166 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form14 = rawRow9166 := by decide +kernel

def row9166 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key193, -18), (key202, -6)]

theorem rowCheck9166 : row9166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9166 := by decide +kernel

theorem rowEval9166 (x : Key → ℝ) : Integer.Sparse.eval row9166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9166, Integer.Sparse.eval_collectBalanced, rawRowCheck9166]

def rawRow9167 : Integer.Sparse Key := [(key7, 6), (key7, 6), (key1, 6), (key7, 6), (key193, -6), (key202, -6), (key193, -6), (key193, -6)]

theorem rawRowCheck9167 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form14 = rawRow9167 := by decide +kernel

def row9167 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key193, -18), (key202, -6)]

theorem rowCheck9167 : row9167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9167 := by decide +kernel

theorem rowEval9167 (x : Key → ℝ) : Integer.Sparse.eval row9167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9167, Integer.Sparse.eval_collectBalanced, rawRowCheck9167]

def rawRow9168 : Integer.Sparse Key := [(key7, 6), (key7, 6), (key7, 6), (key1, 6), (key202, -6), (key193, -6), (key193, -6), (key193, -6)]

theorem rawRowCheck9168 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form14 = rawRow9168 := by decide +kernel

def row9168 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key193, -18), (key202, -6)]

theorem rowCheck9168 : row9168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9168 := by decide +kernel

theorem rowEval9168 (x : Key → ℝ) : Integer.Sparse.eval row9168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9168, Integer.Sparse.eval_collectBalanced, rawRowCheck9168]

def rawRow9169 : Integer.Sparse Key := [(key193, 6), (key193, 6), (key193, 6), (key202, 6), (key1, -6), (key84, -6), (key84, -6), (key84, -6)]

theorem rawRowCheck9169 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form14 = rawRow9169 := by decide +kernel

def row9169 : Integer.Sparse Key := [(key1, -6), (key84, -18), (key193, 18), (key202, 6)]

theorem rowCheck9169 : row9169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9169 := by decide +kernel

theorem rowEval9169 (x : Key → ℝ) : Integer.Sparse.eval row9169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9169, Integer.Sparse.eval_collectBalanced, rawRowCheck9169]

def rawRow9170 : Integer.Sparse Key := [(key193, 6), (key193, 6), (key202, 6), (key193, 6), (key84, -6), (key1, -6), (key84, -6), (key84, -6)]

theorem rawRowCheck9170 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form14 = rawRow9170 := by decide +kernel

def row9170 : Integer.Sparse Key := [(key1, -6), (key84, -18), (key193, 18), (key202, 6)]

theorem rowCheck9170 : row9170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9170 := by decide +kernel

theorem rowEval9170 (x : Key → ℝ) : Integer.Sparse.eval row9170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9170, Integer.Sparse.eval_collectBalanced, rawRowCheck9170]

def rawRow9171 : Integer.Sparse Key := [(key193, 6), (key202, 6), (key193, 6), (key193, 6), (key84, -6), (key84, -6), (key1, -6), (key84, -6)]

theorem rawRowCheck9171 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form14 = rawRow9171 := by decide +kernel

def row9171 : Integer.Sparse Key := [(key1, -6), (key84, -18), (key193, 18), (key202, 6)]

theorem rowCheck9171 : row9171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9171 := by decide +kernel

theorem rowEval9171 (x : Key → ℝ) : Integer.Sparse.eval row9171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9171, Integer.Sparse.eval_collectBalanced, rawRowCheck9171]

def rawRow9172 : Integer.Sparse Key := [(key202, 6), (key193, 6), (key193, 6), (key193, 6), (key84, -6), (key84, -6), (key84, -6), (key1, -6)]

theorem rawRowCheck9172 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form14 = rawRow9172 := by decide +kernel

def row9172 : Integer.Sparse Key := [(key1, -6), (key84, -18), (key193, 18), (key202, 6)]

theorem rowCheck9172 : row9172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9172 := by decide +kernel

theorem rowEval9172 (x : Key → ℝ) : Integer.Sparse.eval row9172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck9172, Integer.Sparse.eval_collectBalanced, rawRowCheck9172]

def rawRow9173 : Integer.Sparse Key := [(key2361, 2), (key2361, 2), (key2364, 2), (key2456, 2), (key2456, 2), (key2531, 2), (key2517, 2), (key2520, 2), (key2517, 2), (key2561, 2), (key2520, 2), (key2561, 2), (key2361, -2), (key2364, -2), (key2364, -2), (key2456, -2), (key2459, -2), (key2456, -2), (key2531, -2), (key2459, -2), (key2531, -2), (key2520, -2), (key2520, -2), (key2561, -2)]

theorem rawRowCheck9173 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form0 = rawRow9173 := by decide +kernel

def row9173 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

theorem rowCheck9173 : row9173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9173 := by decide +kernel

theorem rowEval9173 (x : Key → ℝ) : Integer.Sparse.eval row9173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9173, Integer.Sparse.eval_collectBalanced, rawRowCheck9173]

def rawRow9174 : Integer.Sparse Key := [(key2361, 2), (key2364, 2), (key2361, 2), (key2456, 2), (key2531, 2), (key2456, 2), (key2520, 2), (key2517, 2), (key2561, 2), (key2517, 2), (key2561, 2), (key2520, 2), (key2364, -2), (key2361, -2), (key2364, -2), (key2459, -2), (key2456, -2), (key2531, -2), (key2456, -2), (key2531, -2), (key2459, -2), (key2520, -2), (key2561, -2), (key2520, -2)]

theorem rawRowCheck9174 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form0 = rawRow9174 := by decide +kernel

def row9174 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

theorem rowCheck9174 : row9174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9174 := by decide +kernel

theorem rowEval9174 (x : Key → ℝ) : Integer.Sparse.eval row9174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9174, Integer.Sparse.eval_collectBalanced, rawRowCheck9174]

def rawRow9175 : Integer.Sparse Key := [(key2364, 2), (key2361, 2), (key2361, 2), (key2531, 2), (key2456, 2), (key2456, 2), (key2561, 2), (key2561, 2), (key2520, 2), (key2520, 2), (key2517, 2), (key2517, 2), (key2364, -2), (key2364, -2), (key2361, -2), (key2531, -2), (key2531, -2), (key2459, -2), (key2459, -2), (key2456, -2), (key2456, -2), (key2561, -2), (key2520, -2), (key2520, -2)]

theorem rawRowCheck9175 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form0 = rawRow9175 := by decide +kernel

def row9175 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

theorem rowCheck9175 : row9175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9175 := by decide +kernel

theorem rowEval9175 (x : Key → ℝ) : Integer.Sparse.eval row9175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9175, Integer.Sparse.eval_collectBalanced, rawRowCheck9175]

def rawRow9176 : Integer.Sparse Key := [(key2456, 2), (key2517, 2), (key2520, 2), (key2361, 2), (key2517, 2), (key2561, 2), (key2361, 2), (key2364, 2), (key2456, 2), (key2531, 2), (key2520, 2), (key2561, 2), (key2456, -2), (key2459, -2), (key2520, -2), (key2361, -2), (key2364, -2), (key2456, -2), (key2531, -2), (key2520, -2), (key2561, -2), (key2364, -2), (key2459, -2), (key2531, -2)]

theorem rawRowCheck9176 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form0 = rawRow9176 := by decide +kernel

def row9176 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

theorem rowCheck9176 : row9176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9176 := by decide +kernel

theorem rowEval9176 (x : Key → ℝ) : Integer.Sparse.eval row9176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9176, Integer.Sparse.eval_collectBalanced, rawRowCheck9176]

def rawRow9177 : Integer.Sparse Key := [(key2456, 2), (key2520, 2), (key2517, 2), (key2361, 2), (key2561, 2), (key2517, 2), (key2364, 2), (key2361, 2), (key2531, 2), (key2456, 2), (key2561, 2), (key2520, 2), (key2459, -2), (key2456, -2), (key2520, -2), (key2364, -2), (key2361, -2), (key2531, -2), (key2456, -2), (key2561, -2), (key2520, -2), (key2364, -2), (key2531, -2), (key2459, -2)]

theorem rawRowCheck9177 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form0 = rawRow9177 := by decide +kernel

def row9177 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

theorem rowCheck9177 : row9177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9177 := by decide +kernel

theorem rowEval9177 (x : Key → ℝ) : Integer.Sparse.eval row9177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9177, Integer.Sparse.eval_collectBalanced, rawRowCheck9177]

def rawRow9178 : Integer.Sparse Key := [(key2517, 2), (key2456, 2), (key2520, 2), (key2517, 2), (key2361, 2), (key2561, 2), (key2456, 2), (key2520, 2), (key2361, 2), (key2561, 2), (key2364, 2), (key2531, 2), (key2456, -2), (key2520, -2), (key2459, -2), (key2456, -2), (key2520, -2), (key2361, -2), (key2561, -2), (key2364, -2), (key2531, -2), (key2459, -2), (key2364, -2), (key2531, -2)]

theorem rawRowCheck9178 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form0 = rawRow9178 := by decide +kernel

def row9178 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

theorem rowCheck9178 : row9178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9178 := by decide +kernel

theorem rowEval9178 (x : Key → ℝ) : Integer.Sparse.eval row9178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9178, Integer.Sparse.eval_collectBalanced, rawRowCheck9178]

def rawRow9179 : Integer.Sparse Key := [(key2517, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2561, 2), (key2361, 2), (key2520, 2), (key2456, 2), (key2561, 2), (key2361, 2), (key2531, 2), (key2364, 2), (key2520, -2), (key2456, -2), (key2459, -2), (key2520, -2), (key2456, -2), (key2561, -2), (key2361, -2), (key2531, -2), (key2364, -2), (key2459, -2), (key2531, -2), (key2364, -2)]

theorem rawRowCheck9179 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form0 = rawRow9179 := by decide +kernel

def row9179 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

theorem rowCheck9179 : row9179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9179 := by decide +kernel

theorem rowEval9179 (x : Key → ℝ) : Integer.Sparse.eval row9179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9179, Integer.Sparse.eval_collectBalanced, rawRowCheck9179]

def rawRow9180 : Integer.Sparse Key := [(key2520, 2), (key2456, 2), (key2517, 2), (key2561, 2), (key2361, 2), (key2517, 2), (key2531, 2), (key2561, 2), (key2364, 2), (key2520, 2), (key2361, 2), (key2456, 2), (key2459, -2), (key2520, -2), (key2456, -2), (key2531, -2), (key2561, -2), (key2364, -2), (key2520, -2), (key2361, -2), (key2456, -2), (key2531, -2), (key2364, -2), (key2459, -2)]

theorem rawRowCheck9180 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form0 = rawRow9180 := by decide +kernel

def row9180 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

theorem rowCheck9180 : row9180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9180 := by decide +kernel

theorem rowEval9180 (x : Key → ℝ) : Integer.Sparse.eval row9180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9180, Integer.Sparse.eval_collectBalanced, rawRowCheck9180]

def rawRow9181 : Integer.Sparse Key := [(key2520, 2), (key2517, 2), (key2456, 2), (key2561, 2), (key2517, 2), (key2361, 2), (key2561, 2), (key2531, 2), (key2520, 2), (key2364, 2), (key2456, 2), (key2361, 2), (key2520, -2), (key2459, -2), (key2456, -2), (key2561, -2), (key2531, -2), (key2520, -2), (key2364, -2), (key2456, -2), (key2361, -2), (key2531, -2), (key2459, -2), (key2364, -2)]

theorem rawRowCheck9181 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form0 = rawRow9181 := by decide +kernel

def row9181 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

theorem rowCheck9181 : row9181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9181 := by decide +kernel

theorem rowEval9181 (x : Key → ℝ) : Integer.Sparse.eval row9181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9181, Integer.Sparse.eval_collectBalanced, rawRowCheck9181]

def rawRow9182 : Integer.Sparse Key := [(key2531, 2), (key2561, 2), (key2561, 2), (key2364, 2), (key2520, 2), (key2520, 2), (key2361, 2), (key2361, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2531, -2), (key2531, -2), (key2561, -2), (key2364, -2), (key2364, -2), (key2459, -2), (key2459, -2), (key2520, -2), (key2520, -2), (key2361, -2), (key2456, -2), (key2456, -2)]

theorem rawRowCheck9182 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form0 = rawRow9182 := by decide +kernel

def row9182 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

theorem rowCheck9182 : row9182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9182 := by decide +kernel

theorem rowEval9182 (x : Key → ℝ) : Integer.Sparse.eval row9182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9182, Integer.Sparse.eval_collectBalanced, rawRowCheck9182]

def rawRow9183 : Integer.Sparse Key := [(key2561, 2), (key2531, 2), (key2561, 2), (key2520, 2), (key2364, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2361, 2), (key2517, 2), (key2361, 2), (key2456, 2), (key2531, -2), (key2561, -2), (key2531, -2), (key2459, -2), (key2520, -2), (key2364, -2), (key2520, -2), (key2364, -2), (key2459, -2), (key2456, -2), (key2361, -2), (key2456, -2)]

theorem rawRowCheck9183 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form0 = rawRow9183 := by decide +kernel

def row9183 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

theorem rowCheck9183 : row9183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9183 := by decide +kernel

theorem rowEval9183 (x : Key → ℝ) : Integer.Sparse.eval row9183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9183, Integer.Sparse.eval_collectBalanced, rawRowCheck9183]

def rawRow9184 : Integer.Sparse Key := [(key2561, 2), (key2561, 2), (key2531, 2), (key2520, 2), (key2520, 2), (key2364, 2), (key2517, 2), (key2456, 2), (key2517, 2), (key2361, 2), (key2456, 2), (key2361, 2), (key2561, -2), (key2531, -2), (key2531, -2), (key2520, -2), (key2459, -2), (key2520, -2), (key2364, -2), (key2459, -2), (key2364, -2), (key2456, -2), (key2456, -2), (key2361, -2)]

theorem rawRowCheck9184 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form0 = rawRow9184 := by decide +kernel

def row9184 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

theorem rowCheck9184 : row9184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9184 := by decide +kernel

theorem rowEval9184 (x : Key → ℝ) : Integer.Sparse.eval row9184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9184, Integer.Sparse.eval_collectBalanced, rawRowCheck9184]

def rawRow9185 : Integer.Sparse Key := [(key1083, -24), (key969, 6), (key1083, 6), (key1083, 6), (key1177, 6)]

theorem rawRowCheck9185 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form1 = rawRow9185 := by decide +kernel

def row9185 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

theorem rowCheck9185 : row9185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9185 := by decide +kernel

theorem rowEval9185 (x : Key → ℝ) : Integer.Sparse.eval row9185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9185, Integer.Sparse.eval_collectBalanced, rawRowCheck9185]

def rawRow9186 : Integer.Sparse Key := [(key1083, -24), (key969, 6), (key1083, 6), (key1177, 6), (key1083, 6)]

theorem rawRowCheck9186 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form1 = rawRow9186 := by decide +kernel

def row9186 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

theorem rowCheck9186 : row9186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9186 := by decide +kernel

theorem rowEval9186 (x : Key → ℝ) : Integer.Sparse.eval row9186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9186, Integer.Sparse.eval_collectBalanced, rawRowCheck9186]

def rawRow9187 : Integer.Sparse Key := [(key1083, -24), (key969, 6), (key1177, 6), (key1083, 6), (key1083, 6)]

theorem rawRowCheck9187 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form1 = rawRow9187 := by decide +kernel

def row9187 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

theorem rowCheck9187 : row9187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9187 := by decide +kernel

theorem rowEval9187 (x : Key → ℝ) : Integer.Sparse.eval row9187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9187, Integer.Sparse.eval_collectBalanced, rawRowCheck9187]

def rawRow9188 : Integer.Sparse Key := [(key1083, -24), (key1083, 6), (key969, 6), (key1083, 6), (key1177, 6)]

theorem rawRowCheck9188 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form1 = rawRow9188 := by decide +kernel

def row9188 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

theorem rowCheck9188 : row9188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9188 := by decide +kernel

theorem rowEval9188 (x : Key → ℝ) : Integer.Sparse.eval row9188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9188, Integer.Sparse.eval_collectBalanced, rawRowCheck9188]

def rawRow9189 : Integer.Sparse Key := [(key1083, -24), (key1083, 6), (key969, 6), (key1177, 6), (key1083, 6)]

theorem rawRowCheck9189 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form1 = rawRow9189 := by decide +kernel

def row9189 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

theorem rowCheck9189 : row9189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9189 := by decide +kernel

theorem rowEval9189 (x : Key → ℝ) : Integer.Sparse.eval row9189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9189, Integer.Sparse.eval_collectBalanced, rawRowCheck9189]

def rawRow9190 : Integer.Sparse Key := [(key1083, -24), (key1083, 6), (key1083, 6), (key969, 6), (key1177, 6)]

theorem rawRowCheck9190 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form1 = rawRow9190 := by decide +kernel

def row9190 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

theorem rowCheck9190 : row9190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9190 := by decide +kernel

theorem rowEval9190 (x : Key → ℝ) : Integer.Sparse.eval row9190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9190, Integer.Sparse.eval_collectBalanced, rawRowCheck9190]

def rawRow9191 : Integer.Sparse Key := [(key1083, -24), (key1083, 6), (key1083, 6), (key1177, 6), (key969, 6)]

theorem rawRowCheck9191 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form1 = rawRow9191 := by decide +kernel

def row9191 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

theorem rowCheck9191 : row9191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9191 := by decide +kernel

theorem rowEval9191 (x : Key → ℝ) : Integer.Sparse.eval row9191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9191, Integer.Sparse.eval_collectBalanced, rawRowCheck9191]

def rawRow9192 : Integer.Sparse Key := [(key1083, -24), (key1083, 6), (key1177, 6), (key969, 6), (key1083, 6)]

theorem rawRowCheck9192 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form1 = rawRow9192 := by decide +kernel

def row9192 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

theorem rowCheck9192 : row9192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9192 := by decide +kernel

theorem rowEval9192 (x : Key → ℝ) : Integer.Sparse.eval row9192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9192, Integer.Sparse.eval_collectBalanced, rawRowCheck9192]

def rawRow9193 : Integer.Sparse Key := [(key1083, -24), (key1083, 6), (key1177, 6), (key1083, 6), (key969, 6)]

theorem rawRowCheck9193 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form1 = rawRow9193 := by decide +kernel

def row9193 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

theorem rowCheck9193 : row9193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9193 := by decide +kernel

theorem rowEval9193 (x : Key → ℝ) : Integer.Sparse.eval row9193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9193, Integer.Sparse.eval_collectBalanced, rawRowCheck9193]

def rawRow9194 : Integer.Sparse Key := [(key1083, -24), (key1177, 6), (key969, 6), (key1083, 6), (key1083, 6)]

theorem rawRowCheck9194 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form1 = rawRow9194 := by decide +kernel

def row9194 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

theorem rowCheck9194 : row9194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9194 := by decide +kernel

theorem rowEval9194 (x : Key → ℝ) : Integer.Sparse.eval row9194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9194, Integer.Sparse.eval_collectBalanced, rawRowCheck9194]

def rawRow9195 : Integer.Sparse Key := [(key1083, -24), (key1177, 6), (key1083, 6), (key969, 6), (key1083, 6)]

theorem rawRowCheck9195 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form1 = rawRow9195 := by decide +kernel

def row9195 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

theorem rowCheck9195 : row9195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9195 := by decide +kernel

theorem rowEval9195 (x : Key → ℝ) : Integer.Sparse.eval row9195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9195, Integer.Sparse.eval_collectBalanced, rawRowCheck9195]

def rawRow9196 : Integer.Sparse Key := [(key1083, -24), (key1177, 6), (key1083, 6), (key1083, 6), (key969, 6)]

theorem rawRowCheck9196 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form1 = rawRow9196 := by decide +kernel

def row9196 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

theorem rowCheck9196 : row9196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9196 := by decide +kernel

theorem rowEval9196 (x : Key → ℝ) : Integer.Sparse.eval row9196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9196, Integer.Sparse.eval_collectBalanced, rawRowCheck9196]

def rawRow9197 : Integer.Sparse Key := [(key1086, -6), (key1091, -6), (key1091, -6), (key1162, -6), (key972, 2), (key977, 2), (key977, 2), (key1086, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1181, 2), (key1162, 2), (key1162, 2), (key1218, 2)]

theorem rawRowCheck9197 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form2 = rawRow9197 := by decide +kernel

def row9197 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

theorem rowCheck9197 : row9197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9197 := by decide +kernel

theorem rowEval9197 (x : Key → ℝ) : Integer.Sparse.eval row9197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9197, Integer.Sparse.eval_collectBalanced, rawRowCheck9197]

def rawRow9198 : Integer.Sparse Key := [(key1091, -6), (key1086, -6), (key1091, -6), (key1162, -6), (key977, 2), (key972, 2), (key977, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1162, 2), (key1218, 2), (key1162, 2)]

theorem rawRowCheck9198 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form2 = rawRow9198 := by decide +kernel

def row9198 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

theorem rowCheck9198 : row9198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9198 := by decide +kernel

theorem rowEval9198 (x : Key → ℝ) : Integer.Sparse.eval row9198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9198, Integer.Sparse.eval_collectBalanced, rawRowCheck9198]

def rawRow9199 : Integer.Sparse Key := [(key1091, -6), (key1091, -6), (key1086, -6), (key1162, -6), (key977, 2), (key977, 2), (key972, 2), (key1181, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1086, 2), (key1218, 2), (key1162, 2), (key1162, 2)]

theorem rawRowCheck9199 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form2 = rawRow9199 := by decide +kernel

def row9199 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

theorem rowCheck9199 : row9199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9199 := by decide +kernel

theorem rowEval9199 (x : Key → ℝ) : Integer.Sparse.eval row9199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9199, Integer.Sparse.eval_collectBalanced, rawRowCheck9199]

def rawRow9200 : Integer.Sparse Key := [(key1086, -6), (key1091, -6), (key1162, -6), (key1091, -6), (key1086, 2), (key1091, 2), (key1162, 2), (key972, 2), (key977, 2), (key1086, 2), (key1181, 2), (key1162, 2), (key1218, 2), (key977, 2), (key1091, 2), (key1181, 2)]

theorem rawRowCheck9200 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form2 = rawRow9200 := by decide +kernel

def row9200 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

theorem rowCheck9200 : row9200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9200 := by decide +kernel

theorem rowEval9200 (x : Key → ℝ) : Integer.Sparse.eval row9200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9200, Integer.Sparse.eval_collectBalanced, rawRowCheck9200]

def rawRow9201 : Integer.Sparse Key := [(key1091, -6), (key1086, -6), (key1162, -6), (key1091, -6), (key1091, 2), (key1086, 2), (key1162, 2), (key977, 2), (key972, 2), (key1181, 2), (key1086, 2), (key1218, 2), (key1162, 2), (key977, 2), (key1181, 2), (key1091, 2)]

theorem rawRowCheck9201 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form2 = rawRow9201 := by decide +kernel

def row9201 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

theorem rowCheck9201 : row9201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9201 := by decide +kernel

theorem rowEval9201 (x : Key → ℝ) : Integer.Sparse.eval row9201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9201, Integer.Sparse.eval_collectBalanced, rawRowCheck9201]

def rawRow9202 : Integer.Sparse Key := [(key1086, -6), (key1162, -6), (key1091, -6), (key1091, -6), (key1086, 2), (key1162, 2), (key1091, 2), (key1086, 2), (key1162, 2), (key972, 2), (key1218, 2), (key977, 2), (key1181, 2), (key1091, 2), (key977, 2), (key1181, 2)]

theorem rawRowCheck9202 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form2 = rawRow9202 := by decide +kernel

def row9202 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

theorem rowCheck9202 : row9202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9202 := by decide +kernel

theorem rowEval9202 (x : Key → ℝ) : Integer.Sparse.eval row9202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9202, Integer.Sparse.eval_collectBalanced, rawRowCheck9202]

def rawRow9203 : Integer.Sparse Key := [(key1162, -6), (key1086, -6), (key1091, -6), (key1091, -6), (key1162, 2), (key1086, 2), (key1091, 2), (key1162, 2), (key1086, 2), (key1218, 2), (key972, 2), (key1181, 2), (key977, 2), (key1091, 2), (key1181, 2), (key977, 2)]

theorem rawRowCheck9203 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form2 = rawRow9203 := by decide +kernel

def row9203 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

theorem rowCheck9203 : row9203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9203 := by decide +kernel

theorem rowEval9203 (x : Key → ℝ) : Integer.Sparse.eval row9203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9203, Integer.Sparse.eval_collectBalanced, rawRowCheck9203]

def rawRow9204 : Integer.Sparse Key := [(key1091, -6), (key1162, -6), (key1086, -6), (key1091, -6), (key1091, 2), (key1162, 2), (key1086, 2), (key1181, 2), (key1218, 2), (key977, 2), (key1162, 2), (key972, 2), (key1086, 2), (key1181, 2), (key977, 2), (key1091, 2)]

theorem rawRowCheck9204 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form2 = rawRow9204 := by decide +kernel

def row9204 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

theorem rowCheck9204 : row9204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9204 := by decide +kernel

theorem rowEval9204 (x : Key → ℝ) : Integer.Sparse.eval row9204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9204, Integer.Sparse.eval_collectBalanced, rawRowCheck9204]

def rawRow9205 : Integer.Sparse Key := [(key1162, -6), (key1091, -6), (key1086, -6), (key1091, -6), (key1162, 2), (key1091, 2), (key1086, 2), (key1218, 2), (key1181, 2), (key1162, 2), (key977, 2), (key1086, 2), (key972, 2), (key1181, 2), (key1091, 2), (key977, 2)]

theorem rawRowCheck9205 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form2 = rawRow9205 := by decide +kernel

def row9205 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

theorem rowCheck9205 : row9205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9205 := by decide +kernel

theorem rowEval9205 (x : Key → ℝ) : Integer.Sparse.eval row9205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9205, Integer.Sparse.eval_collectBalanced, rawRowCheck9205]

def rawRow9206 : Integer.Sparse Key := [(key1091, -6), (key1091, -6), (key1162, -6), (key1086, -6), (key1181, 2), (key1181, 2), (key1218, 2), (key977, 2), (key977, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key1162, 2), (key972, 2), (key1086, 2), (key1086, 2)]

theorem rawRowCheck9206 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form2 = rawRow9206 := by decide +kernel

def row9206 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

theorem rowCheck9206 : row9206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9206 := by decide +kernel

theorem rowEval9206 (x : Key → ℝ) : Integer.Sparse.eval row9206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9206, Integer.Sparse.eval_collectBalanced, rawRowCheck9206]

def rawRow9207 : Integer.Sparse Key := [(key1091, -6), (key1162, -6), (key1091, -6), (key1086, -6), (key1181, 2), (key1218, 2), (key1181, 2), (key1091, 2), (key1162, 2), (key977, 2), (key1162, 2), (key977, 2), (key1091, 2), (key1086, 2), (key972, 2), (key1086, 2)]

theorem rawRowCheck9207 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form2 = rawRow9207 := by decide +kernel

def row9207 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

theorem rowCheck9207 : row9207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9207 := by decide +kernel

theorem rowEval9207 (x : Key → ℝ) : Integer.Sparse.eval row9207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9207, Integer.Sparse.eval_collectBalanced, rawRowCheck9207]

def rawRow9208 : Integer.Sparse Key := [(key1162, -6), (key1091, -6), (key1091, -6), (key1086, -6), (key1218, 2), (key1181, 2), (key1181, 2), (key1162, 2), (key1091, 2), (key1162, 2), (key977, 2), (key1091, 2), (key977, 2), (key1086, 2), (key1086, 2), (key972, 2)]

theorem rawRowCheck9208 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form2 = rawRow9208 := by decide +kernel

def row9208 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

theorem rowCheck9208 : row9208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9208 := by decide +kernel

theorem rowEval9208 (x : Key → ℝ) : Integer.Sparse.eval row9208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9208, Integer.Sparse.eval_collectBalanced, rawRowCheck9208]

def rawRow9209 : Integer.Sparse Key := [(key2369, -6), (key2463, -6), (key2463, -6), (key2497, -6), (key2369, 2), (key2369, 2), (key2384, 2), (key2397, 2), (key2397, 2), (key2431, 2), (key2463, 2), (key2474, 2), (key2463, 2), (key2497, 2), (key2474, 2), (key2497, 2)]

theorem rawRowCheck9209 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form3 = rawRow9209 := by decide +kernel

def row9209 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

theorem rowCheck9209 : row9209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9209 := by decide +kernel

theorem rowEval9209 (x : Key → ℝ) : Integer.Sparse.eval row9209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9209, Integer.Sparse.eval_collectBalanced, rawRowCheck9209]

def rawRow9210 : Integer.Sparse Key := [(key2369, -6), (key2463, -6), (key2497, -6), (key2463, -6), (key2369, 2), (key2384, 2), (key2369, 2), (key2397, 2), (key2431, 2), (key2397, 2), (key2474, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2497, 2), (key2474, 2)]

theorem rawRowCheck9210 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form3 = rawRow9210 := by decide +kernel

def row9210 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

theorem rowCheck9210 : row9210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9210 := by decide +kernel

theorem rowEval9210 (x : Key → ℝ) : Integer.Sparse.eval row9210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9210, Integer.Sparse.eval_collectBalanced, rawRowCheck9210]

def rawRow9211 : Integer.Sparse Key := [(key2369, -6), (key2497, -6), (key2463, -6), (key2463, -6), (key2384, 2), (key2369, 2), (key2369, 2), (key2431, 2), (key2397, 2), (key2397, 2), (key2497, 2), (key2497, 2), (key2474, 2), (key2474, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck9211 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form3 = rawRow9211 := by decide +kernel

def row9211 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

theorem rowCheck9211 : row9211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9211 := by decide +kernel

theorem rowEval9211 (x : Key → ℝ) : Integer.Sparse.eval row9211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9211, Integer.Sparse.eval_collectBalanced, rawRowCheck9211]

def rawRow9212 : Integer.Sparse Key := [(key2463, -6), (key2369, -6), (key2463, -6), (key2497, -6), (key2397, 2), (key2463, 2), (key2474, 2), (key2369, 2), (key2463, 2), (key2497, 2), (key2369, 2), (key2384, 2), (key2397, 2), (key2431, 2), (key2474, 2), (key2497, 2)]

theorem rawRowCheck9212 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form3 = rawRow9212 := by decide +kernel

def row9212 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

theorem rowCheck9212 : row9212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9212 := by decide +kernel

theorem rowEval9212 (x : Key → ℝ) : Integer.Sparse.eval row9212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9212, Integer.Sparse.eval_collectBalanced, rawRowCheck9212]

def rawRow9213 : Integer.Sparse Key := [(key2463, -6), (key2369, -6), (key2497, -6), (key2463, -6), (key2397, 2), (key2474, 2), (key2463, 2), (key2369, 2), (key2497, 2), (key2463, 2), (key2384, 2), (key2369, 2), (key2431, 2), (key2397, 2), (key2497, 2), (key2474, 2)]

theorem rawRowCheck9213 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form3 = rawRow9213 := by decide +kernel

def row9213 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

theorem rowCheck9213 : row9213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9213 := by decide +kernel

theorem rowEval9213 (x : Key → ℝ) : Integer.Sparse.eval row9213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9213, Integer.Sparse.eval_collectBalanced, rawRowCheck9213]

def rawRow9214 : Integer.Sparse Key := [(key2463, -6), (key2463, -6), (key2369, -6), (key2497, -6), (key2463, 2), (key2397, 2), (key2474, 2), (key2463, 2), (key2369, 2), (key2497, 2), (key2397, 2), (key2474, 2), (key2369, 2), (key2497, 2), (key2384, 2), (key2431, 2)]

theorem rawRowCheck9214 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form3 = rawRow9214 := by decide +kernel

def row9214 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

theorem rowCheck9214 : row9214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9214 := by decide +kernel

theorem rowEval9214 (x : Key → ℝ) : Integer.Sparse.eval row9214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9214, Integer.Sparse.eval_collectBalanced, rawRowCheck9214]

def rawRow9215 : Integer.Sparse Key := [(key2463, -6), (key2463, -6), (key2497, -6), (key2369, -6), (key2463, 2), (key2474, 2), (key2397, 2), (key2463, 2), (key2497, 2), (key2369, 2), (key2474, 2), (key2397, 2), (key2497, 2), (key2369, 2), (key2431, 2), (key2384, 2)]

theorem rawRowCheck9215 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form3 = rawRow9215 := by decide +kernel

def row9215 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

theorem rowCheck9215 : row9215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9215 := by decide +kernel

theorem rowEval9215 (x : Key → ℝ) : Integer.Sparse.eval row9215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck9215, Integer.Sparse.eval_collectBalanced, rawRowCheck9215]

end MUB6.Certificate.GramRows

end OAI
