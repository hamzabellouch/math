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

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow16128 : Integer.Sparse Key := [(key2445, 4), (key2526, 4), (key2395, 4), (key2441, -2), (key2410, -2), (key2507, -2), (key2382, -2), (key2483, -2), (key2393, -2), (key2441, -2), (key2410, -2), (key2507, -2), (key2382, -2), (key2483, -2), (key2393, -2), (key2407, 4), (key2848, 4), (key2592, 4)]

theorem rawRowCheck16128 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form0 = rawRow16128 := by decide +kernel

def row16128 : Integer.Sparse Key := [(key2382, -4), (key2393, -4), (key2395, 4), (key2407, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2592, 4), (key2848, 4)]

theorem rowCheck16128 : row16128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16128 := by decide +kernel

theorem rowEval16128 (x : Key → ℝ) : Integer.Sparse.eval row16128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16128, Integer.Sparse.eval_collectBalanced, rawRowCheck16128]

def rawRow16129 : Integer.Sparse Key := [(key2526, 4), (key2395, 4), (key2445, 4), (key2483, -2), (key2507, -2), (key2393, -2), (key2441, -2), (key2382, -2), (key2410, -2), (key2483, -2), (key2507, -2), (key2393, -2), (key2441, -2), (key2382, -2), (key2410, -2), (key2473, 4), (key2379, 4), (key2771, 4)]

theorem rawRowCheck16129 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form0 = rawRow16129 := by decide +kernel

def row16129 : Integer.Sparse Key := [(key2379, 4), (key2382, -4), (key2393, -4), (key2395, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2473, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2771, 4)]

theorem rowCheck16129 : row16129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16129 := by decide +kernel

theorem rowEval16129 (x : Key → ℝ) : Integer.Sparse.eval row16129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16129, Integer.Sparse.eval_collectBalanced, rawRowCheck16129]

def rawRow16130 : Integer.Sparse Key := [(key2526, 4), (key2445, 4), (key2395, 4), (key2507, -2), (key2483, -2), (key2441, -2), (key2393, -2), (key2410, -2), (key2382, -2), (key2507, -2), (key2483, -2), (key2441, -2), (key2393, -2), (key2410, -2), (key2382, -2), (key2473, 4), (key2407, 4), (key2592, 4)]

theorem rawRowCheck16130 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form0 = rawRow16130 := by decide +kernel

def row16130 : Integer.Sparse Key := [(key2382, -4), (key2393, -4), (key2395, 4), (key2407, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2473, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2592, 4)]

theorem rowCheck16130 : row16130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16130 := by decide +kernel

theorem rowEval16130 (x : Key → ℝ) : Integer.Sparse.eval row16130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16130, Integer.Sparse.eval_collectBalanced, rawRowCheck16130]

def rawRow16131 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1076, -2), (key1041, 6), (key1111, -2), (key1111, -2), (key1155, -2), (key998, 2), (key998, 2), (key1190, 2), (key1190, 2), (key1212, 2), (key1212, 2), (key1006, -2), (key1193, -2), (key1193, -2), (key1127, 6), (key1019, -2), (key1199, -2), (key1199, -2)]

theorem rawRowCheck16131 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form1 = rawRow16131 := by decide +kernel

def row16131 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

theorem rowCheck16131 : row16131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16131 := by decide +kernel

theorem rowEval16131 (x : Key → ℝ) : Integer.Sparse.eval row16131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16131, Integer.Sparse.eval_collectBalanced, rawRowCheck16131]

def rawRow16132 : Integer.Sparse Key := [(key1033, -2), (key1076, -2), (key1033, -2), (key1041, 6), (key1111, -2), (key1155, -2), (key1111, -2), (key1190, 2), (key1212, 2), (key998, 2), (key1212, 2), (key998, 2), (key1190, 2), (key1193, -2), (key1006, -2), (key1193, -2), (key1127, 6), (key1199, -2), (key1019, -2), (key1199, -2)]

theorem rawRowCheck16132 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form1 = rawRow16132 := by decide +kernel

def row16132 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

theorem rowCheck16132 : row16132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16132 := by decide +kernel

theorem rowEval16132 (x : Key → ℝ) : Integer.Sparse.eval row16132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16132, Integer.Sparse.eval_collectBalanced, rawRowCheck16132]

def rawRow16133 : Integer.Sparse Key := [(key1076, -2), (key1033, -2), (key1033, -2), (key1041, 6), (key1155, -2), (key1111, -2), (key1111, -2), (key1212, 2), (key1190, 2), (key1212, 2), (key998, 2), (key1190, 2), (key998, 2), (key1193, -2), (key1193, -2), (key1006, -2), (key1127, 6), (key1199, -2), (key1199, -2), (key1019, -2)]

theorem rawRowCheck16133 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form1 = rawRow16133 := by decide +kernel

def row16133 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

theorem rowCheck16133 : row16133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16133 := by decide +kernel

theorem rowEval16133 (x : Key → ℝ) : Integer.Sparse.eval row16133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16133, Integer.Sparse.eval_collectBalanced, rawRowCheck16133]

def rawRow16134 : Integer.Sparse Key := [(key1033, -2), (key1041, -2), (key1076, -2), (key1033, 6), (key1190, -2), (key1193, -2), (key1212, -2), (key998, 2), (key1006, 2), (key1111, 2), (key1193, 2), (key1155, 2), (key1212, 2), (key998, -2), (key1111, -2), (key1190, -2), (key1199, 6), (key1019, -2), (key1127, -2), (key1199, -2)]

theorem rawRowCheck16134 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form1 = rawRow16134 := by decide +kernel

def row16134 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

theorem rowCheck16134 : row16134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16134 := by decide +kernel

theorem rowEval16134 (x : Key → ℝ) : Integer.Sparse.eval row16134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16134, Integer.Sparse.eval_collectBalanced, rawRowCheck16134]

def rawRow16135 : Integer.Sparse Key := [(key1041, -2), (key1033, -2), (key1076, -2), (key1033, 6), (key1193, -2), (key1190, -2), (key1212, -2), (key1006, 2), (key998, 2), (key1193, 2), (key1111, 2), (key1212, 2), (key1155, 2), (key998, -2), (key1190, -2), (key1111, -2), (key1199, 6), (key1019, -2), (key1199, -2), (key1127, -2)]

theorem rawRowCheck16135 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form1 = rawRow16135 := by decide +kernel

def row16135 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

theorem rowCheck16135 : row16135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16135 := by decide +kernel

theorem rowEval16135 (x : Key → ℝ) : Integer.Sparse.eval row16135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16135, Integer.Sparse.eval_collectBalanced, rawRowCheck16135]

def rawRow16136 : Integer.Sparse Key := [(key1033, -2), (key1076, -2), (key1041, -2), (key1033, 6), (key1190, -2), (key1212, -2), (key1193, -2), (key1111, 2), (key1155, 2), (key998, 2), (key1212, 2), (key1006, 2), (key1193, 2), (key1111, -2), (key998, -2), (key1190, -2), (key1199, 6), (key1127, -2), (key1019, -2), (key1199, -2)]

theorem rawRowCheck16136 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form1 = rawRow16136 := by decide +kernel

def row16136 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

theorem rowCheck16136 : row16136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16136 := by decide +kernel

theorem rowEval16136 (x : Key → ℝ) : Integer.Sparse.eval row16136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16136, Integer.Sparse.eval_collectBalanced, rawRowCheck16136]

def rawRow16137 : Integer.Sparse Key := [(key1076, -2), (key1033, -2), (key1041, -2), (key1033, 6), (key1212, -2), (key1190, -2), (key1193, -2), (key1155, 2), (key1111, 2), (key1212, 2), (key998, 2), (key1193, 2), (key1006, 2), (key1111, -2), (key1190, -2), (key998, -2), (key1199, 6), (key1127, -2), (key1199, -2), (key1019, -2)]

theorem rawRowCheck16137 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form1 = rawRow16137 := by decide +kernel

def row16137 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

theorem rowCheck16137 : row16137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16137 := by decide +kernel

theorem rowEval16137 (x : Key → ℝ) : Integer.Sparse.eval row16137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16137, Integer.Sparse.eval_collectBalanced, rawRowCheck16137]

def rawRow16138 : Integer.Sparse Key := [(key1041, -2), (key1076, -2), (key1033, -2), (key1033, 6), (key1193, -2), (key1212, -2), (key1190, -2), (key1193, 2), (key1212, 2), (key1006, 2), (key1155, 2), (key998, 2), (key1111, 2), (key1190, -2), (key998, -2), (key1111, -2), (key1199, 6), (key1199, -2), (key1019, -2), (key1127, -2)]

theorem rawRowCheck16138 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form1 = rawRow16138 := by decide +kernel

def row16138 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

theorem rowCheck16138 : row16138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16138 := by decide +kernel

theorem rowEval16138 (x : Key → ℝ) : Integer.Sparse.eval row16138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16138, Integer.Sparse.eval_collectBalanced, rawRowCheck16138]

def rawRow16139 : Integer.Sparse Key := [(key1076, -2), (key1041, -2), (key1033, -2), (key1033, 6), (key1212, -2), (key1193, -2), (key1190, -2), (key1212, 2), (key1193, 2), (key1155, 2), (key1006, 2), (key1111, 2), (key998, 2), (key1190, -2), (key1111, -2), (key998, -2), (key1199, 6), (key1199, -2), (key1127, -2), (key1019, -2)]

theorem rawRowCheck16139 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form1 = rawRow16139 := by decide +kernel

def row16139 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

theorem rowCheck16139 : row16139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16139 := by decide +kernel

theorem rowEval16139 (x : Key → ℝ) : Integer.Sparse.eval row16139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16139, Integer.Sparse.eval_collectBalanced, rawRowCheck16139]

def rawRow16140 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1155, -2), (key1127, 6), (key1033, -2), (key1033, -2), (key1076, -2), (key998, 2), (key998, 2), (key1190, 2), (key1190, 2), (key1212, 2), (key1212, 2), (key1019, -2), (key1199, -2), (key1199, -2), (key1041, 6), (key1006, -2), (key1193, -2), (key1193, -2)]

theorem rawRowCheck16140 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form1 = rawRow16140 := by decide +kernel

def row16140 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

theorem rowCheck16140 : row16140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16140 := by decide +kernel

theorem rowEval16140 (x : Key → ℝ) : Integer.Sparse.eval row16140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16140, Integer.Sparse.eval_collectBalanced, rawRowCheck16140]

def rawRow16141 : Integer.Sparse Key := [(key1111, -2), (key1155, -2), (key1111, -2), (key1127, 6), (key1033, -2), (key1076, -2), (key1033, -2), (key1190, 2), (key1212, 2), (key998, 2), (key1212, 2), (key998, 2), (key1190, 2), (key1199, -2), (key1019, -2), (key1199, -2), (key1041, 6), (key1193, -2), (key1006, -2), (key1193, -2)]

theorem rawRowCheck16141 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form1 = rawRow16141 := by decide +kernel

def row16141 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

theorem rowCheck16141 : row16141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16141 := by decide +kernel

theorem rowEval16141 (x : Key → ℝ) : Integer.Sparse.eval row16141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16141, Integer.Sparse.eval_collectBalanced, rawRowCheck16141]

def rawRow16142 : Integer.Sparse Key := [(key1155, -2), (key1111, -2), (key1111, -2), (key1127, 6), (key1076, -2), (key1033, -2), (key1033, -2), (key1212, 2), (key1190, 2), (key1212, 2), (key998, 2), (key1190, 2), (key998, 2), (key1199, -2), (key1199, -2), (key1019, -2), (key1041, 6), (key1193, -2), (key1193, -2), (key1006, -2)]

theorem rawRowCheck16142 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form1 = rawRow16142 := by decide +kernel

def row16142 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

theorem rowCheck16142 : row16142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16142 := by decide +kernel

theorem rowEval16142 (x : Key → ℝ) : Integer.Sparse.eval row16142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16142, Integer.Sparse.eval_collectBalanced, rawRowCheck16142]

def rawRow16143 : Integer.Sparse Key := [(key1111, -2), (key1127, -2), (key1155, -2), (key1111, 6), (key1190, -2), (key1199, -2), (key1212, -2), (key998, 2), (key1019, 2), (key1033, 2), (key1199, 2), (key1076, 2), (key1212, 2), (key998, -2), (key1033, -2), (key1190, -2), (key1193, 6), (key1006, -2), (key1041, -2), (key1193, -2)]

theorem rawRowCheck16143 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form1 = rawRow16143 := by decide +kernel

def row16143 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

theorem rowCheck16143 : row16143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16143 := by decide +kernel

theorem rowEval16143 (x : Key → ℝ) : Integer.Sparse.eval row16143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16143, Integer.Sparse.eval_collectBalanced, rawRowCheck16143]

def rawRow16144 : Integer.Sparse Key := [(key1127, -2), (key1111, -2), (key1155, -2), (key1111, 6), (key1199, -2), (key1190, -2), (key1212, -2), (key1019, 2), (key998, 2), (key1199, 2), (key1033, 2), (key1212, 2), (key1076, 2), (key998, -2), (key1190, -2), (key1033, -2), (key1193, 6), (key1006, -2), (key1193, -2), (key1041, -2)]

theorem rawRowCheck16144 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form1 = rawRow16144 := by decide +kernel

def row16144 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

theorem rowCheck16144 : row16144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16144 := by decide +kernel

theorem rowEval16144 (x : Key → ℝ) : Integer.Sparse.eval row16144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16144, Integer.Sparse.eval_collectBalanced, rawRowCheck16144]

def rawRow16145 : Integer.Sparse Key := [(key1111, -2), (key1155, -2), (key1127, -2), (key1111, 6), (key1190, -2), (key1212, -2), (key1199, -2), (key1033, 2), (key1076, 2), (key998, 2), (key1212, 2), (key1019, 2), (key1199, 2), (key1033, -2), (key998, -2), (key1190, -2), (key1193, 6), (key1041, -2), (key1006, -2), (key1193, -2)]

theorem rawRowCheck16145 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form1 = rawRow16145 := by decide +kernel

def row16145 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

theorem rowCheck16145 : row16145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16145 := by decide +kernel

theorem rowEval16145 (x : Key → ℝ) : Integer.Sparse.eval row16145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16145, Integer.Sparse.eval_collectBalanced, rawRowCheck16145]

def rawRow16146 : Integer.Sparse Key := [(key1155, -2), (key1111, -2), (key1127, -2), (key1111, 6), (key1212, -2), (key1190, -2), (key1199, -2), (key1076, 2), (key1033, 2), (key1212, 2), (key998, 2), (key1199, 2), (key1019, 2), (key1033, -2), (key1190, -2), (key998, -2), (key1193, 6), (key1041, -2), (key1193, -2), (key1006, -2)]

theorem rawRowCheck16146 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form1 = rawRow16146 := by decide +kernel

def row16146 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

theorem rowCheck16146 : row16146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16146 := by decide +kernel

theorem rowEval16146 (x : Key → ℝ) : Integer.Sparse.eval row16146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16146, Integer.Sparse.eval_collectBalanced, rawRowCheck16146]

def rawRow16147 : Integer.Sparse Key := [(key1127, -2), (key1155, -2), (key1111, -2), (key1111, 6), (key1199, -2), (key1212, -2), (key1190, -2), (key1199, 2), (key1212, 2), (key1019, 2), (key1076, 2), (key998, 2), (key1033, 2), (key1190, -2), (key998, -2), (key1033, -2), (key1193, 6), (key1193, -2), (key1006, -2), (key1041, -2)]

theorem rawRowCheck16147 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form1 = rawRow16147 := by decide +kernel

def row16147 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

theorem rowCheck16147 : row16147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16147 := by decide +kernel

theorem rowEval16147 (x : Key → ℝ) : Integer.Sparse.eval row16147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16147, Integer.Sparse.eval_collectBalanced, rawRowCheck16147]

def rawRow16148 : Integer.Sparse Key := [(key1155, -2), (key1127, -2), (key1111, -2), (key1111, 6), (key1212, -2), (key1199, -2), (key1190, -2), (key1212, 2), (key1199, 2), (key1076, 2), (key1019, 2), (key1033, 2), (key998, 2), (key1190, -2), (key1033, -2), (key998, -2), (key1193, 6), (key1193, -2), (key1041, -2), (key1006, -2)]

theorem rawRowCheck16148 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form1 = rawRow16148 := by decide +kernel

def row16148 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

theorem rowCheck16148 : row16148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16148 := by decide +kernel

theorem rowEval16148 (x : Key → ℝ) : Integer.Sparse.eval row16148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16148, Integer.Sparse.eval_collectBalanced, rawRowCheck16148]

def rawRow16149 : Integer.Sparse Key := [(key1190, -2), (key1193, -2), (key1212, -2), (key1199, 6), (key1033, -2), (key1041, -2), (key1076, -2), (key998, 2), (key1006, 2), (key1111, 2), (key1193, 2), (key1155, 2), (key1212, 2), (key1019, -2), (key1127, -2), (key1199, -2), (key1033, 6), (key998, -2), (key1111, -2), (key1190, -2)]

theorem rawRowCheck16149 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form1 = rawRow16149 := by decide +kernel

def row16149 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

theorem rowCheck16149 : row16149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16149 := by decide +kernel

theorem rowEval16149 (x : Key → ℝ) : Integer.Sparse.eval row16149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16149, Integer.Sparse.eval_collectBalanced, rawRowCheck16149]

def rawRow16150 : Integer.Sparse Key := [(key1193, -2), (key1190, -2), (key1212, -2), (key1199, 6), (key1041, -2), (key1033, -2), (key1076, -2), (key1006, 2), (key998, 2), (key1193, 2), (key1111, 2), (key1212, 2), (key1155, 2), (key1019, -2), (key1199, -2), (key1127, -2), (key1033, 6), (key998, -2), (key1190, -2), (key1111, -2)]

theorem rawRowCheck16150 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form1 = rawRow16150 := by decide +kernel

def row16150 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

theorem rowCheck16150 : row16150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16150 := by decide +kernel

theorem rowEval16150 (x : Key → ℝ) : Integer.Sparse.eval row16150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16150, Integer.Sparse.eval_collectBalanced, rawRowCheck16150]

def rawRow16151 : Integer.Sparse Key := [(key1190, -2), (key1212, -2), (key1193, -2), (key1199, 6), (key1033, -2), (key1076, -2), (key1041, -2), (key1111, 2), (key1155, 2), (key998, 2), (key1212, 2), (key1006, 2), (key1193, 2), (key1127, -2), (key1019, -2), (key1199, -2), (key1033, 6), (key1111, -2), (key998, -2), (key1190, -2)]

theorem rawRowCheck16151 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form1 = rawRow16151 := by decide +kernel

def row16151 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

theorem rowCheck16151 : row16151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16151 := by decide +kernel

theorem rowEval16151 (x : Key → ℝ) : Integer.Sparse.eval row16151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16151, Integer.Sparse.eval_collectBalanced, rawRowCheck16151]

def rawRow16152 : Integer.Sparse Key := [(key1212, -2), (key1190, -2), (key1193, -2), (key1199, 6), (key1076, -2), (key1033, -2), (key1041, -2), (key1155, 2), (key1111, 2), (key1212, 2), (key998, 2), (key1193, 2), (key1006, 2), (key1127, -2), (key1199, -2), (key1019, -2), (key1033, 6), (key1111, -2), (key1190, -2), (key998, -2)]

theorem rawRowCheck16152 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form1 = rawRow16152 := by decide +kernel

def row16152 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

theorem rowCheck16152 : row16152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16152 := by decide +kernel

theorem rowEval16152 (x : Key → ℝ) : Integer.Sparse.eval row16152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16152, Integer.Sparse.eval_collectBalanced, rawRowCheck16152]

def rawRow16153 : Integer.Sparse Key := [(key1193, -2), (key1212, -2), (key1190, -2), (key1199, 6), (key1041, -2), (key1076, -2), (key1033, -2), (key1193, 2), (key1212, 2), (key1006, 2), (key1155, 2), (key998, 2), (key1111, 2), (key1199, -2), (key1019, -2), (key1127, -2), (key1033, 6), (key1190, -2), (key998, -2), (key1111, -2)]

theorem rawRowCheck16153 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form1 = rawRow16153 := by decide +kernel

def row16153 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

theorem rowCheck16153 : row16153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16153 := by decide +kernel

theorem rowEval16153 (x : Key → ℝ) : Integer.Sparse.eval row16153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16153, Integer.Sparse.eval_collectBalanced, rawRowCheck16153]

def rawRow16154 : Integer.Sparse Key := [(key1212, -2), (key1193, -2), (key1190, -2), (key1199, 6), (key1076, -2), (key1041, -2), (key1033, -2), (key1212, 2), (key1193, 2), (key1155, 2), (key1006, 2), (key1111, 2), (key998, 2), (key1199, -2), (key1127, -2), (key1019, -2), (key1033, 6), (key1190, -2), (key1111, -2), (key998, -2)]

theorem rawRowCheck16154 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form1 = rawRow16154 := by decide +kernel

def row16154 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

theorem rowCheck16154 : row16154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16154 := by decide +kernel

theorem rowEval16154 (x : Key → ℝ) : Integer.Sparse.eval row16154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16154, Integer.Sparse.eval_collectBalanced, rawRowCheck16154]

def rawRow16155 : Integer.Sparse Key := [(key1190, -2), (key1199, -2), (key1212, -2), (key1193, 6), (key1111, -2), (key1127, -2), (key1155, -2), (key998, 2), (key1019, 2), (key1033, 2), (key1199, 2), (key1076, 2), (key1212, 2), (key1006, -2), (key1041, -2), (key1193, -2), (key1111, 6), (key998, -2), (key1033, -2), (key1190, -2)]

theorem rawRowCheck16155 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form1 = rawRow16155 := by decide +kernel

def row16155 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

theorem rowCheck16155 : row16155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16155 := by decide +kernel

theorem rowEval16155 (x : Key → ℝ) : Integer.Sparse.eval row16155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16155, Integer.Sparse.eval_collectBalanced, rawRowCheck16155]

def rawRow16156 : Integer.Sparse Key := [(key1199, -2), (key1190, -2), (key1212, -2), (key1193, 6), (key1127, -2), (key1111, -2), (key1155, -2), (key1019, 2), (key998, 2), (key1199, 2), (key1033, 2), (key1212, 2), (key1076, 2), (key1006, -2), (key1193, -2), (key1041, -2), (key1111, 6), (key998, -2), (key1190, -2), (key1033, -2)]

theorem rawRowCheck16156 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form1 = rawRow16156 := by decide +kernel

def row16156 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

theorem rowCheck16156 : row16156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16156 := by decide +kernel

theorem rowEval16156 (x : Key → ℝ) : Integer.Sparse.eval row16156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16156, Integer.Sparse.eval_collectBalanced, rawRowCheck16156]

def rawRow16157 : Integer.Sparse Key := [(key1190, -2), (key1212, -2), (key1199, -2), (key1193, 6), (key1111, -2), (key1155, -2), (key1127, -2), (key1033, 2), (key1076, 2), (key998, 2), (key1212, 2), (key1019, 2), (key1199, 2), (key1041, -2), (key1006, -2), (key1193, -2), (key1111, 6), (key1033, -2), (key998, -2), (key1190, -2)]

theorem rawRowCheck16157 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form1 = rawRow16157 := by decide +kernel

def row16157 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

theorem rowCheck16157 : row16157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16157 := by decide +kernel

theorem rowEval16157 (x : Key → ℝ) : Integer.Sparse.eval row16157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16157, Integer.Sparse.eval_collectBalanced, rawRowCheck16157]

def rawRow16158 : Integer.Sparse Key := [(key1212, -2), (key1190, -2), (key1199, -2), (key1193, 6), (key1155, -2), (key1111, -2), (key1127, -2), (key1076, 2), (key1033, 2), (key1212, 2), (key998, 2), (key1199, 2), (key1019, 2), (key1041, -2), (key1193, -2), (key1006, -2), (key1111, 6), (key1033, -2), (key1190, -2), (key998, -2)]

theorem rawRowCheck16158 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form1 = rawRow16158 := by decide +kernel

def row16158 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

theorem rowCheck16158 : row16158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16158 := by decide +kernel

theorem rowEval16158 (x : Key → ℝ) : Integer.Sparse.eval row16158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16158, Integer.Sparse.eval_collectBalanced, rawRowCheck16158]

def rawRow16159 : Integer.Sparse Key := [(key1199, -2), (key1212, -2), (key1190, -2), (key1193, 6), (key1127, -2), (key1155, -2), (key1111, -2), (key1199, 2), (key1212, 2), (key1019, 2), (key1076, 2), (key998, 2), (key1033, 2), (key1193, -2), (key1006, -2), (key1041, -2), (key1111, 6), (key1190, -2), (key998, -2), (key1033, -2)]

theorem rawRowCheck16159 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form1 = rawRow16159 := by decide +kernel

def row16159 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

theorem rowCheck16159 : row16159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16159 := by decide +kernel

theorem rowEval16159 (x : Key → ℝ) : Integer.Sparse.eval row16159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16159, Integer.Sparse.eval_collectBalanced, rawRowCheck16159]

def rawRow16160 : Integer.Sparse Key := [(key1212, -2), (key1199, -2), (key1190, -2), (key1193, 6), (key1155, -2), (key1127, -2), (key1111, -2), (key1212, 2), (key1199, 2), (key1076, 2), (key1019, 2), (key1033, 2), (key998, 2), (key1193, -2), (key1041, -2), (key1006, -2), (key1111, 6), (key1190, -2), (key1033, -2), (key998, -2)]

theorem rawRowCheck16160 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form1 = rawRow16160 := by decide +kernel

def row16160 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

theorem rowCheck16160 : row16160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16160 := by decide +kernel

theorem rowEval16160 (x : Key → ℝ) : Integer.Sparse.eval row16160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16160, Integer.Sparse.eval_collectBalanced, rawRowCheck16160]

def rawRow16161 : Integer.Sparse Key := [(key1193, -2), (key1199, -2), (key1212, -2), (key1190, 6), (key1193, -2), (key1199, -2), (key1212, -2), (key1006, 2), (key1019, 2), (key1041, 2), (key1127, 2), (key1076, 2), (key1155, 2), (key998, -2), (key1033, -2), (key1111, -2), (key1190, 6), (key998, -2), (key1033, -2), (key1111, -2)]

theorem rawRowCheck16161 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form1 = rawRow16161 := by decide +kernel

def row16161 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

theorem rowCheck16161 : row16161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16161 := by decide +kernel

theorem rowEval16161 (x : Key → ℝ) : Integer.Sparse.eval row16161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16161, Integer.Sparse.eval_collectBalanced, rawRowCheck16161]

def rawRow16162 : Integer.Sparse Key := [(key1199, -2), (key1193, -2), (key1212, -2), (key1190, 6), (key1199, -2), (key1193, -2), (key1212, -2), (key1019, 2), (key1006, 2), (key1127, 2), (key1041, 2), (key1155, 2), (key1076, 2), (key998, -2), (key1111, -2), (key1033, -2), (key1190, 6), (key998, -2), (key1111, -2), (key1033, -2)]

theorem rawRowCheck16162 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form1 = rawRow16162 := by decide +kernel

def row16162 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

theorem rowCheck16162 : row16162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16162 := by decide +kernel

theorem rowEval16162 (x : Key → ℝ) : Integer.Sparse.eval row16162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16162, Integer.Sparse.eval_collectBalanced, rawRowCheck16162]

def rawRow16163 : Integer.Sparse Key := [(key1193, -2), (key1212, -2), (key1199, -2), (key1190, 6), (key1193, -2), (key1212, -2), (key1199, -2), (key1041, 2), (key1076, 2), (key1006, 2), (key1155, 2), (key1019, 2), (key1127, 2), (key1033, -2), (key998, -2), (key1111, -2), (key1190, 6), (key1033, -2), (key998, -2), (key1111, -2)]

theorem rawRowCheck16163 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form1 = rawRow16163 := by decide +kernel

def row16163 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

theorem rowCheck16163 : row16163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16163 := by decide +kernel

theorem rowEval16163 (x : Key → ℝ) : Integer.Sparse.eval row16163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16163, Integer.Sparse.eval_collectBalanced, rawRowCheck16163]

def rawRow16164 : Integer.Sparse Key := [(key1212, -2), (key1193, -2), (key1199, -2), (key1190, 6), (key1212, -2), (key1193, -2), (key1199, -2), (key1076, 2), (key1041, 2), (key1155, 2), (key1006, 2), (key1127, 2), (key1019, 2), (key1033, -2), (key1111, -2), (key998, -2), (key1190, 6), (key1033, -2), (key1111, -2), (key998, -2)]

theorem rawRowCheck16164 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form1 = rawRow16164 := by decide +kernel

def row16164 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

theorem rowCheck16164 : row16164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16164 := by decide +kernel

theorem rowEval16164 (x : Key → ℝ) : Integer.Sparse.eval row16164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16164, Integer.Sparse.eval_collectBalanced, rawRowCheck16164]

def rawRow16165 : Integer.Sparse Key := [(key1199, -2), (key1212, -2), (key1193, -2), (key1190, 6), (key1199, -2), (key1212, -2), (key1193, -2), (key1127, 2), (key1155, 2), (key1019, 2), (key1076, 2), (key1006, 2), (key1041, 2), (key1111, -2), (key998, -2), (key1033, -2), (key1190, 6), (key1111, -2), (key998, -2), (key1033, -2)]

theorem rawRowCheck16165 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form1 = rawRow16165 := by decide +kernel

def row16165 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

theorem rowCheck16165 : row16165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16165 := by decide +kernel

theorem rowEval16165 (x : Key → ℝ) : Integer.Sparse.eval row16165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16165, Integer.Sparse.eval_collectBalanced, rawRowCheck16165]

def rawRow16166 : Integer.Sparse Key := [(key1212, -2), (key1199, -2), (key1193, -2), (key1190, 6), (key1212, -2), (key1199, -2), (key1193, -2), (key1155, 2), (key1127, 2), (key1076, 2), (key1019, 2), (key1041, 2), (key1006, 2), (key1111, -2), (key1033, -2), (key998, -2), (key1190, 6), (key1111, -2), (key1033, -2), (key998, -2)]

theorem rawRowCheck16166 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form1 = rawRow16166 := by decide +kernel

def row16166 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

theorem rowCheck16166 : row16166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16166 := by decide +kernel

theorem rowEval16166 (x : Key → ℝ) : Integer.Sparse.eval row16166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16166, Integer.Sparse.eval_collectBalanced, rawRowCheck16166]

def rawRow16167 : Integer.Sparse Key := [(key2402, -2), (key2402, -2), (key2439, -2), (key2408, 6), (key2847, -2), (key2847, -2), (key3020, -2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key3029, 2), (key3029, 2), (key2596, -2), (key2884, -2), (key2884, -2), (key2917, 6), (key2605, -2), (key2926, -2), (key2926, -2)]

theorem rawRowCheck16167 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form2 = rawRow16167 := by decide +kernel

def row16167 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2847, -4), (key2878, 4), (key2884, -4), (key2917, 6), (key2926, -4), (key3020, -2), (key3029, 4)]

theorem rowCheck16167 : row16167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16167 := by decide +kernel

theorem rowEval16167 (x : Key → ℝ) : Integer.Sparse.eval row16167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16167, Integer.Sparse.eval_collectBalanced, rawRowCheck16167]

def rawRow16168 : Integer.Sparse Key := [(key2402, -2), (key2439, -2), (key2402, -2), (key2408, 6), (key2847, -2), (key3020, -2), (key2847, -2), (key2878, 2), (key3029, 2), (key2591, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2884, -2), (key2596, -2), (key2884, -2), (key2917, 6), (key2926, -2), (key2605, -2), (key2926, -2)]

theorem rawRowCheck16168 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form2 = rawRow16168 := by decide +kernel

def row16168 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2847, -4), (key2878, 4), (key2884, -4), (key2917, 6), (key2926, -4), (key3020, -2), (key3029, 4)]

theorem rowCheck16168 : row16168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16168 := by decide +kernel

theorem rowEval16168 (x : Key → ℝ) : Integer.Sparse.eval row16168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16168, Integer.Sparse.eval_collectBalanced, rawRowCheck16168]

def rawRow16169 : Integer.Sparse Key := [(key2439, -2), (key2402, -2), (key2402, -2), (key2408, 6), (key3020, -2), (key2847, -2), (key2847, -2), (key3029, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2884, -2), (key2884, -2), (key2596, -2), (key2917, 6), (key2926, -2), (key2926, -2), (key2605, -2)]

theorem rawRowCheck16169 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form2 = rawRow16169 := by decide +kernel

def row16169 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2847, -4), (key2878, 4), (key2884, -4), (key2917, 6), (key2926, -4), (key3020, -2), (key3029, 4)]

theorem rowCheck16169 : row16169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16169 := by decide +kernel

theorem rowEval16169 (x : Key → ℝ) : Integer.Sparse.eval row16169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16169, Integer.Sparse.eval_collectBalanced, rawRowCheck16169]

def rawRow16170 : Integer.Sparse Key := [(key2402, -2), (key2408, -2), (key2439, -2), (key2402, 6), (key2878, -2), (key2884, -2), (key3029, -2), (key2591, 2), (key2596, 2), (key2847, 2), (key2884, 2), (key3020, 2), (key3029, 2), (key2591, -2), (key2847, -2), (key2878, -2), (key2926, 6), (key2605, -2), (key2917, -2), (key2926, -2)]

theorem rawRowCheck16170 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form2 = rawRow16170 := by decide +kernel

def row16170 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

theorem rowCheck16170 : row16170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16170 := by decide +kernel

theorem rowEval16170 (x : Key → ℝ) : Integer.Sparse.eval row16170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16170, Integer.Sparse.eval_collectBalanced, rawRowCheck16170]

def rawRow16171 : Integer.Sparse Key := [(key2408, -2), (key2402, -2), (key2439, -2), (key2402, 6), (key2884, -2), (key2878, -2), (key3029, -2), (key2596, 2), (key2591, 2), (key2884, 2), (key2847, 2), (key3029, 2), (key3020, 2), (key2591, -2), (key2878, -2), (key2847, -2), (key2926, 6), (key2605, -2), (key2926, -2), (key2917, -2)]

theorem rawRowCheck16171 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form2 = rawRow16171 := by decide +kernel

def row16171 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

theorem rowCheck16171 : row16171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16171 := by decide +kernel

theorem rowEval16171 (x : Key → ℝ) : Integer.Sparse.eval row16171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16171, Integer.Sparse.eval_collectBalanced, rawRowCheck16171]

def rawRow16172 : Integer.Sparse Key := [(key2402, -2), (key2439, -2), (key2408, -2), (key2402, 6), (key2878, -2), (key3029, -2), (key2884, -2), (key2847, 2), (key3020, 2), (key2591, 2), (key3029, 2), (key2596, 2), (key2884, 2), (key2847, -2), (key2591, -2), (key2878, -2), (key2926, 6), (key2917, -2), (key2605, -2), (key2926, -2)]

theorem rawRowCheck16172 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form2 = rawRow16172 := by decide +kernel

def row16172 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

theorem rowCheck16172 : row16172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16172 := by decide +kernel

theorem rowEval16172 (x : Key → ℝ) : Integer.Sparse.eval row16172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16172, Integer.Sparse.eval_collectBalanced, rawRowCheck16172]

def rawRow16173 : Integer.Sparse Key := [(key2439, -2), (key2402, -2), (key2408, -2), (key2402, 6), (key3029, -2), (key2878, -2), (key2884, -2), (key3020, 2), (key2847, 2), (key3029, 2), (key2591, 2), (key2884, 2), (key2596, 2), (key2847, -2), (key2878, -2), (key2591, -2), (key2926, 6), (key2917, -2), (key2926, -2), (key2605, -2)]

theorem rawRowCheck16173 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form2 = rawRow16173 := by decide +kernel

def row16173 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

theorem rowCheck16173 : row16173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16173 := by decide +kernel

theorem rowEval16173 (x : Key → ℝ) : Integer.Sparse.eval row16173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16173, Integer.Sparse.eval_collectBalanced, rawRowCheck16173]

def rawRow16174 : Integer.Sparse Key := [(key2408, -2), (key2439, -2), (key2402, -2), (key2402, 6), (key2884, -2), (key3029, -2), (key2878, -2), (key2884, 2), (key3029, 2), (key2596, 2), (key3020, 2), (key2591, 2), (key2847, 2), (key2878, -2), (key2591, -2), (key2847, -2), (key2926, 6), (key2926, -2), (key2605, -2), (key2917, -2)]

theorem rawRowCheck16174 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form2 = rawRow16174 := by decide +kernel

def row16174 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

theorem rowCheck16174 : row16174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16174 := by decide +kernel

theorem rowEval16174 (x : Key → ℝ) : Integer.Sparse.eval row16174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16174, Integer.Sparse.eval_collectBalanced, rawRowCheck16174]

def rawRow16175 : Integer.Sparse Key := [(key2439, -2), (key2408, -2), (key2402, -2), (key2402, 6), (key3029, -2), (key2884, -2), (key2878, -2), (key3029, 2), (key2884, 2), (key3020, 2), (key2596, 2), (key2847, 2), (key2591, 2), (key2878, -2), (key2847, -2), (key2591, -2), (key2926, 6), (key2926, -2), (key2917, -2), (key2605, -2)]

theorem rawRowCheck16175 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form2 = rawRow16175 := by decide +kernel

def row16175 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

theorem rowCheck16175 : row16175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16175 := by decide +kernel

theorem rowEval16175 (x : Key → ℝ) : Integer.Sparse.eval row16175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16175, Integer.Sparse.eval_collectBalanced, rawRowCheck16175]

def rawRow16176 : Integer.Sparse Key := [(key2468, -2), (key2468, -2), (key2505, -2), (key2481, 6), (key2402, -2), (key2402, -2), (key2439, -2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key3029, 2), (key3029, 2), (key2605, -2), (key2926, -2), (key2926, -2), (key2775, 6), (key2596, -2), (key2884, -2), (key2884, -2)]

theorem rawRowCheck16176 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form2 = rawRow16176 := by decide +kernel

def row16176 : Integer.Sparse Key := [(key2402, -4), (key2439, -2), (key2468, -4), (key2481, 6), (key2505, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2775, 6), (key2878, 4), (key2884, -4), (key2926, -4), (key3029, 4)]

theorem rowCheck16176 : row16176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16176 := by decide +kernel

theorem rowEval16176 (x : Key → ℝ) : Integer.Sparse.eval row16176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16176, Integer.Sparse.eval_collectBalanced, rawRowCheck16176]

def rawRow16177 : Integer.Sparse Key := [(key2468, -2), (key2505, -2), (key2468, -2), (key2481, 6), (key2402, -2), (key2439, -2), (key2402, -2), (key2878, 2), (key3029, 2), (key2591, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2926, -2), (key2605, -2), (key2926, -2), (key2775, 6), (key2884, -2), (key2596, -2), (key2884, -2)]

theorem rawRowCheck16177 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form2 = rawRow16177 := by decide +kernel

def row16177 : Integer.Sparse Key := [(key2402, -4), (key2439, -2), (key2468, -4), (key2481, 6), (key2505, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2775, 6), (key2878, 4), (key2884, -4), (key2926, -4), (key3029, 4)]

theorem rowCheck16177 : row16177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16177 := by decide +kernel

theorem rowEval16177 (x : Key → ℝ) : Integer.Sparse.eval row16177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16177, Integer.Sparse.eval_collectBalanced, rawRowCheck16177]

def rawRow16178 : Integer.Sparse Key := [(key2505, -2), (key2468, -2), (key2468, -2), (key2481, 6), (key2439, -2), (key2402, -2), (key2402, -2), (key3029, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2926, -2), (key2926, -2), (key2605, -2), (key2775, 6), (key2884, -2), (key2884, -2), (key2596, -2)]

theorem rawRowCheck16178 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form2 = rawRow16178 := by decide +kernel

def row16178 : Integer.Sparse Key := [(key2402, -4), (key2439, -2), (key2468, -4), (key2481, 6), (key2505, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2775, 6), (key2878, 4), (key2884, -4), (key2926, -4), (key3029, 4)]

theorem rowCheck16178 : row16178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16178 := by decide +kernel

theorem rowEval16178 (x : Key → ℝ) : Integer.Sparse.eval row16178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16178, Integer.Sparse.eval_collectBalanced, rawRowCheck16178]

def rawRow16179 : Integer.Sparse Key := [(key2468, -2), (key2481, -2), (key2505, -2), (key2468, 6), (key2535, -2), (key2542, -2), (key2553, -2), (key2374, 2), (key2391, 2), (key2402, 2), (key2542, 2), (key2439, 2), (key2553, 2), (key2591, -2), (key2770, -2), (key2878, -2), (key2884, 6), (key2596, -2), (key2775, -2), (key2884, -2)]

theorem rawRowCheck16179 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form2 = rawRow16179 := by decide +kernel

def row16179 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

theorem rowCheck16179 : row16179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16179 := by decide +kernel

theorem rowEval16179 (x : Key → ℝ) : Integer.Sparse.eval row16179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16179, Integer.Sparse.eval_collectBalanced, rawRowCheck16179]

def rawRow16180 : Integer.Sparse Key := [(key2481, -2), (key2468, -2), (key2505, -2), (key2468, 6), (key2542, -2), (key2535, -2), (key2553, -2), (key2391, 2), (key2374, 2), (key2542, 2), (key2402, 2), (key2553, 2), (key2439, 2), (key2591, -2), (key2878, -2), (key2770, -2), (key2884, 6), (key2596, -2), (key2884, -2), (key2775, -2)]

theorem rawRowCheck16180 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form2 = rawRow16180 := by decide +kernel

def row16180 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

theorem rowCheck16180 : row16180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16180 := by decide +kernel

theorem rowEval16180 (x : Key → ℝ) : Integer.Sparse.eval row16180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16180, Integer.Sparse.eval_collectBalanced, rawRowCheck16180]

def rawRow16181 : Integer.Sparse Key := [(key2468, -2), (key2505, -2), (key2481, -2), (key2468, 6), (key2535, -2), (key2553, -2), (key2542, -2), (key2402, 2), (key2439, 2), (key2374, 2), (key2553, 2), (key2391, 2), (key2542, 2), (key2770, -2), (key2591, -2), (key2878, -2), (key2884, 6), (key2775, -2), (key2596, -2), (key2884, -2)]

theorem rawRowCheck16181 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form2 = rawRow16181 := by decide +kernel

def row16181 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

theorem rowCheck16181 : row16181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16181 := by decide +kernel

theorem rowEval16181 (x : Key → ℝ) : Integer.Sparse.eval row16181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16181, Integer.Sparse.eval_collectBalanced, rawRowCheck16181]

def rawRow16182 : Integer.Sparse Key := [(key2505, -2), (key2468, -2), (key2481, -2), (key2468, 6), (key2553, -2), (key2535, -2), (key2542, -2), (key2439, 2), (key2402, 2), (key2553, 2), (key2374, 2), (key2542, 2), (key2391, 2), (key2770, -2), (key2878, -2), (key2591, -2), (key2884, 6), (key2775, -2), (key2884, -2), (key2596, -2)]

theorem rawRowCheck16182 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form2 = rawRow16182 := by decide +kernel

def row16182 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

theorem rowCheck16182 : row16182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16182 := by decide +kernel

theorem rowEval16182 (x : Key → ℝ) : Integer.Sparse.eval row16182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16182, Integer.Sparse.eval_collectBalanced, rawRowCheck16182]

def rawRow16183 : Integer.Sparse Key := [(key2481, -2), (key2505, -2), (key2468, -2), (key2468, 6), (key2542, -2), (key2553, -2), (key2535, -2), (key2542, 2), (key2553, 2), (key2391, 2), (key2439, 2), (key2374, 2), (key2402, 2), (key2878, -2), (key2591, -2), (key2770, -2), (key2884, 6), (key2884, -2), (key2596, -2), (key2775, -2)]

theorem rawRowCheck16183 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form2 = rawRow16183 := by decide +kernel

def row16183 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

theorem rowCheck16183 : row16183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16183 := by decide +kernel

theorem rowEval16183 (x : Key → ℝ) : Integer.Sparse.eval row16183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16183, Integer.Sparse.eval_collectBalanced, rawRowCheck16183]

def rawRow16184 : Integer.Sparse Key := [(key2505, -2), (key2481, -2), (key2468, -2), (key2468, 6), (key2553, -2), (key2542, -2), (key2535, -2), (key2553, 2), (key2542, 2), (key2439, 2), (key2391, 2), (key2402, 2), (key2374, 2), (key2878, -2), (key2770, -2), (key2591, -2), (key2884, 6), (key2884, -2), (key2775, -2), (key2596, -2)]

theorem rawRowCheck16184 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form2 = rawRow16184 := by decide +kernel

def row16184 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

theorem rowCheck16184 : row16184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16184 := by decide +kernel

theorem rowEval16184 (x : Key → ℝ) : Integer.Sparse.eval row16184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16184, Integer.Sparse.eval_collectBalanced, rawRowCheck16184]

def rawRow16185 : Integer.Sparse Key := [(key2535, -2), (key2537, -2), (key2553, -2), (key2542, 6), (key2402, -2), (key2408, -2), (key2439, -2), (key2374, 2), (key2380, 2), (key2468, 2), (key2537, 2), (key2505, 2), (key2553, 2), (key2391, -2), (key2481, -2), (key2542, -2), (key2770, 6), (key2591, -2), (key2847, -2), (key2878, -2)]

theorem rawRowCheck16185 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form2 = rawRow16185 := by decide +kernel

def row16185 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

theorem rowCheck16185 : row16185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16185 := by decide +kernel

theorem rowEval16185 (x : Key → ℝ) : Integer.Sparse.eval row16185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16185, Integer.Sparse.eval_collectBalanced, rawRowCheck16185]

def rawRow16186 : Integer.Sparse Key := [(key2537, -2), (key2535, -2), (key2553, -2), (key2542, 6), (key2408, -2), (key2402, -2), (key2439, -2), (key2380, 2), (key2374, 2), (key2537, 2), (key2468, 2), (key2553, 2), (key2505, 2), (key2391, -2), (key2542, -2), (key2481, -2), (key2770, 6), (key2591, -2), (key2878, -2), (key2847, -2)]

theorem rawRowCheck16186 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form2 = rawRow16186 := by decide +kernel

def row16186 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

theorem rowCheck16186 : row16186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16186 := by decide +kernel

theorem rowEval16186 (x : Key → ℝ) : Integer.Sparse.eval row16186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16186, Integer.Sparse.eval_collectBalanced, rawRowCheck16186]

def rawRow16187 : Integer.Sparse Key := [(key2535, -2), (key2553, -2), (key2537, -2), (key2542, 6), (key2402, -2), (key2439, -2), (key2408, -2), (key2468, 2), (key2505, 2), (key2374, 2), (key2553, 2), (key2380, 2), (key2537, 2), (key2481, -2), (key2391, -2), (key2542, -2), (key2770, 6), (key2847, -2), (key2591, -2), (key2878, -2)]

theorem rawRowCheck16187 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form2 = rawRow16187 := by decide +kernel

def row16187 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

theorem rowCheck16187 : row16187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16187 := by decide +kernel

theorem rowEval16187 (x : Key → ℝ) : Integer.Sparse.eval row16187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16187, Integer.Sparse.eval_collectBalanced, rawRowCheck16187]

def rawRow16188 : Integer.Sparse Key := [(key2553, -2), (key2535, -2), (key2537, -2), (key2542, 6), (key2439, -2), (key2402, -2), (key2408, -2), (key2505, 2), (key2468, 2), (key2553, 2), (key2374, 2), (key2537, 2), (key2380, 2), (key2481, -2), (key2542, -2), (key2391, -2), (key2770, 6), (key2847, -2), (key2878, -2), (key2591, -2)]

theorem rawRowCheck16188 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form2 = rawRow16188 := by decide +kernel

def row16188 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

theorem rowCheck16188 : row16188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16188 := by decide +kernel

theorem rowEval16188 (x : Key → ℝ) : Integer.Sparse.eval row16188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16188, Integer.Sparse.eval_collectBalanced, rawRowCheck16188]

def rawRow16189 : Integer.Sparse Key := [(key2537, -2), (key2553, -2), (key2535, -2), (key2542, 6), (key2408, -2), (key2439, -2), (key2402, -2), (key2537, 2), (key2553, 2), (key2380, 2), (key2505, 2), (key2374, 2), (key2468, 2), (key2542, -2), (key2391, -2), (key2481, -2), (key2770, 6), (key2878, -2), (key2591, -2), (key2847, -2)]

theorem rawRowCheck16189 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form2 = rawRow16189 := by decide +kernel

def row16189 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

theorem rowCheck16189 : row16189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16189 := by decide +kernel

theorem rowEval16189 (x : Key → ℝ) : Integer.Sparse.eval row16189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16189, Integer.Sparse.eval_collectBalanced, rawRowCheck16189]

def rawRow16190 : Integer.Sparse Key := [(key2553, -2), (key2537, -2), (key2535, -2), (key2542, 6), (key2439, -2), (key2408, -2), (key2402, -2), (key2553, 2), (key2537, 2), (key2505, 2), (key2380, 2), (key2468, 2), (key2374, 2), (key2542, -2), (key2481, -2), (key2391, -2), (key2770, 6), (key2878, -2), (key2847, -2), (key2591, -2)]

theorem rawRowCheck16190 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form2 = rawRow16190 := by decide +kernel

def row16190 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

theorem rowCheck16190 : row16190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16190 := by decide +kernel

theorem rowEval16190 (x : Key → ℝ) : Integer.Sparse.eval row16190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16190, Integer.Sparse.eval_collectBalanced, rawRowCheck16190]

def rawRow16191 : Integer.Sparse Key := [(key2535, -2), (key2542, -2), (key2553, -2), (key2537, 6), (key2468, -2), (key2481, -2), (key2505, -2), (key2374, 2), (key2391, 2), (key2402, 2), (key2542, 2), (key2439, 2), (key2553, 2), (key2380, -2), (key2408, -2), (key2537, -2), (key2847, 6), (key2591, -2), (key2770, -2), (key2878, -2)]

theorem rawRowCheck16191 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form2 = rawRow16191 := by decide +kernel

def row16191 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

theorem rowCheck16191 : row16191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16191 := by decide +kernel

theorem rowEval16191 (x : Key → ℝ) : Integer.Sparse.eval row16191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16191, Integer.Sparse.eval_collectBalanced, rawRowCheck16191]

def rawRow16192 : Integer.Sparse Key := [(key2542, -2), (key2535, -2), (key2553, -2), (key2537, 6), (key2481, -2), (key2468, -2), (key2505, -2), (key2391, 2), (key2374, 2), (key2542, 2), (key2402, 2), (key2553, 2), (key2439, 2), (key2380, -2), (key2537, -2), (key2408, -2), (key2847, 6), (key2591, -2), (key2878, -2), (key2770, -2)]

theorem rawRowCheck16192 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form2 = rawRow16192 := by decide +kernel

def row16192 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

theorem rowCheck16192 : row16192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16192 := by decide +kernel

theorem rowEval16192 (x : Key → ℝ) : Integer.Sparse.eval row16192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16192, Integer.Sparse.eval_collectBalanced, rawRowCheck16192]

def rawRow16193 : Integer.Sparse Key := [(key2535, -2), (key2553, -2), (key2542, -2), (key2537, 6), (key2468, -2), (key2505, -2), (key2481, -2), (key2402, 2), (key2439, 2), (key2374, 2), (key2553, 2), (key2391, 2), (key2542, 2), (key2408, -2), (key2380, -2), (key2537, -2), (key2847, 6), (key2770, -2), (key2591, -2), (key2878, -2)]

theorem rawRowCheck16193 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form2 = rawRow16193 := by decide +kernel

def row16193 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

theorem rowCheck16193 : row16193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16193 := by decide +kernel

theorem rowEval16193 (x : Key → ℝ) : Integer.Sparse.eval row16193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16193, Integer.Sparse.eval_collectBalanced, rawRowCheck16193]

def rawRow16194 : Integer.Sparse Key := [(key2553, -2), (key2535, -2), (key2542, -2), (key2537, 6), (key2505, -2), (key2468, -2), (key2481, -2), (key2439, 2), (key2402, 2), (key2553, 2), (key2374, 2), (key2542, 2), (key2391, 2), (key2408, -2), (key2537, -2), (key2380, -2), (key2847, 6), (key2770, -2), (key2878, -2), (key2591, -2)]

theorem rawRowCheck16194 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form2 = rawRow16194 := by decide +kernel

def row16194 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

theorem rowCheck16194 : row16194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16194 := by decide +kernel

theorem rowEval16194 (x : Key → ℝ) : Integer.Sparse.eval row16194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16194, Integer.Sparse.eval_collectBalanced, rawRowCheck16194]

def rawRow16195 : Integer.Sparse Key := [(key2542, -2), (key2553, -2), (key2535, -2), (key2537, 6), (key2481, -2), (key2505, -2), (key2468, -2), (key2542, 2), (key2553, 2), (key2391, 2), (key2439, 2), (key2374, 2), (key2402, 2), (key2537, -2), (key2380, -2), (key2408, -2), (key2847, 6), (key2878, -2), (key2591, -2), (key2770, -2)]

theorem rawRowCheck16195 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form2 = rawRow16195 := by decide +kernel

def row16195 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

theorem rowCheck16195 : row16195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16195 := by decide +kernel

theorem rowEval16195 (x : Key → ℝ) : Integer.Sparse.eval row16195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16195, Integer.Sparse.eval_collectBalanced, rawRowCheck16195]

def rawRow16196 : Integer.Sparse Key := [(key2553, -2), (key2542, -2), (key2535, -2), (key2537, 6), (key2505, -2), (key2481, -2), (key2468, -2), (key2553, 2), (key2542, 2), (key2439, 2), (key2391, 2), (key2402, 2), (key2374, 2), (key2537, -2), (key2408, -2), (key2380, -2), (key2847, 6), (key2878, -2), (key2770, -2), (key2591, -2)]

theorem rawRowCheck16196 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form2 = rawRow16196 := by decide +kernel

def row16196 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

theorem rowCheck16196 : row16196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16196 := by decide +kernel

theorem rowEval16196 (x : Key → ℝ) : Integer.Sparse.eval row16196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16196, Integer.Sparse.eval_collectBalanced, rawRowCheck16196]

def rawRow16197 : Integer.Sparse Key := [(key2537, -2), (key2542, -2), (key2553, -2), (key2535, 6), (key2537, -2), (key2542, -2), (key2553, -2), (key2380, 2), (key2391, 2), (key2408, 2), (key2481, 2), (key2439, 2), (key2505, 2), (key2374, -2), (key2402, -2), (key2468, -2), (key2878, 6), (key2591, -2), (key2770, -2), (key2847, -2)]

theorem rawRowCheck16197 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form2 = rawRow16197 := by decide +kernel

def row16197 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

theorem rowCheck16197 : row16197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16197 := by decide +kernel

theorem rowEval16197 (x : Key → ℝ) : Integer.Sparse.eval row16197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16197, Integer.Sparse.eval_collectBalanced, rawRowCheck16197]

def rawRow16198 : Integer.Sparse Key := [(key2542, -2), (key2537, -2), (key2553, -2), (key2535, 6), (key2542, -2), (key2537, -2), (key2553, -2), (key2391, 2), (key2380, 2), (key2481, 2), (key2408, 2), (key2505, 2), (key2439, 2), (key2374, -2), (key2468, -2), (key2402, -2), (key2878, 6), (key2591, -2), (key2847, -2), (key2770, -2)]

theorem rawRowCheck16198 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form2 = rawRow16198 := by decide +kernel

def row16198 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

theorem rowCheck16198 : row16198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16198 := by decide +kernel

theorem rowEval16198 (x : Key → ℝ) : Integer.Sparse.eval row16198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16198, Integer.Sparse.eval_collectBalanced, rawRowCheck16198]

def rawRow16199 : Integer.Sparse Key := [(key2537, -2), (key2553, -2), (key2542, -2), (key2535, 6), (key2537, -2), (key2553, -2), (key2542, -2), (key2408, 2), (key2439, 2), (key2380, 2), (key2505, 2), (key2391, 2), (key2481, 2), (key2402, -2), (key2374, -2), (key2468, -2), (key2878, 6), (key2770, -2), (key2591, -2), (key2847, -2)]

theorem rawRowCheck16199 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form2 = rawRow16199 := by decide +kernel

def row16199 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

theorem rowCheck16199 : row16199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16199 := by decide +kernel

theorem rowEval16199 (x : Key → ℝ) : Integer.Sparse.eval row16199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16199, Integer.Sparse.eval_collectBalanced, rawRowCheck16199]

def rawRow16200 : Integer.Sparse Key := [(key2553, -2), (key2537, -2), (key2542, -2), (key2535, 6), (key2553, -2), (key2537, -2), (key2542, -2), (key2439, 2), (key2408, 2), (key2505, 2), (key2380, 2), (key2481, 2), (key2391, 2), (key2402, -2), (key2468, -2), (key2374, -2), (key2878, 6), (key2770, -2), (key2847, -2), (key2591, -2)]

theorem rawRowCheck16200 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form2 = rawRow16200 := by decide +kernel

def row16200 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

theorem rowCheck16200 : row16200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16200 := by decide +kernel

theorem rowEval16200 (x : Key → ℝ) : Integer.Sparse.eval row16200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16200, Integer.Sparse.eval_collectBalanced, rawRowCheck16200]

def rawRow16201 : Integer.Sparse Key := [(key2542, -2), (key2553, -2), (key2537, -2), (key2535, 6), (key2542, -2), (key2553, -2), (key2537, -2), (key2481, 2), (key2505, 2), (key2391, 2), (key2439, 2), (key2380, 2), (key2408, 2), (key2468, -2), (key2374, -2), (key2402, -2), (key2878, 6), (key2847, -2), (key2591, -2), (key2770, -2)]

theorem rawRowCheck16201 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form2 = rawRow16201 := by decide +kernel

def row16201 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

theorem rowCheck16201 : row16201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16201 := by decide +kernel

theorem rowEval16201 (x : Key → ℝ) : Integer.Sparse.eval row16201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16201, Integer.Sparse.eval_collectBalanced, rawRowCheck16201]

def rawRow16202 : Integer.Sparse Key := [(key2553, -2), (key2542, -2), (key2537, -2), (key2535, 6), (key2553, -2), (key2542, -2), (key2537, -2), (key2505, 2), (key2481, 2), (key2439, 2), (key2391, 2), (key2408, 2), (key2380, 2), (key2468, -2), (key2402, -2), (key2374, -2), (key2878, 6), (key2847, -2), (key2770, -2), (key2591, -2)]

theorem rawRowCheck16202 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form2 = rawRow16202 := by decide +kernel

def row16202 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

theorem rowCheck16202 : row16202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16202 := by decide +kernel

theorem rowEval16202 (x : Key → ℝ) : Integer.Sparse.eval row16202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16202, Integer.Sparse.eval_collectBalanced, rawRowCheck16202]

def rawRow16203 : Integer.Sparse Key := [(key2785, 6), (key2670, -2), (key2793, -2), (key2793, -2), (key2808, 6), (key2615, -2), (key2828, -2), (key2828, -2), (key2705, -2), (key2859, -2), (key2859, -2), (key2631, -2), (key2869, -2), (key2869, -2), (key2639, 2), (key2639, 2), (key2725, 2), (key2725, 2), (key2879, 2), (key2879, 2)]

theorem rawRowCheck16203 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form3 = rawRow16203 := by decide +kernel

def row16203 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

theorem rowCheck16203 : row16203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16203 := by decide +kernel

theorem rowEval16203 (x : Key → ℝ) : Integer.Sparse.eval row16203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16203, Integer.Sparse.eval_collectBalanced, rawRowCheck16203]

def rawRow16204 : Integer.Sparse Key := [(key2785, 6), (key2793, -2), (key2670, -2), (key2793, -2), (key2808, 6), (key2828, -2), (key2615, -2), (key2828, -2), (key2859, -2), (key2705, -2), (key2859, -2), (key2869, -2), (key2631, -2), (key2869, -2), (key2725, 2), (key2879, 2), (key2639, 2), (key2879, 2), (key2639, 2), (key2725, 2)]

theorem rawRowCheck16204 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form3 = rawRow16204 := by decide +kernel

def row16204 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

theorem rowCheck16204 : row16204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16204 := by decide +kernel

theorem rowEval16204 (x : Key → ℝ) : Integer.Sparse.eval row16204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16204, Integer.Sparse.eval_collectBalanced, rawRowCheck16204]

def rawRow16205 : Integer.Sparse Key := [(key2785, 6), (key2793, -2), (key2793, -2), (key2670, -2), (key2808, 6), (key2828, -2), (key2828, -2), (key2615, -2), (key2859, -2), (key2859, -2), (key2705, -2), (key2869, -2), (key2869, -2), (key2631, -2), (key2879, 2), (key2725, 2), (key2879, 2), (key2639, 2), (key2725, 2), (key2639, 2)]

theorem rawRowCheck16205 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form3 = rawRow16205 := by decide +kernel

def row16205 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

theorem rowCheck16205 : row16205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16205 := by decide +kernel

theorem rowEval16205 (x : Key → ℝ) : Integer.Sparse.eval row16205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16205, Integer.Sparse.eval_collectBalanced, rawRowCheck16205]

def rawRow16206 : Integer.Sparse Key := [(key2793, 6), (key2670, -2), (key2785, -2), (key2793, -2), (key2828, 6), (key2615, -2), (key2808, -2), (key2828, -2), (key2725, -2), (key2869, -2), (key2879, -2), (key2639, -2), (key2859, -2), (key2879, -2), (key2631, 2), (key2639, 2), (key2705, 2), (key2725, 2), (key2859, 2), (key2869, 2)]

theorem rawRowCheck16206 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form3 = rawRow16206 := by decide +kernel

def row16206 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

theorem rowCheck16206 : row16206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16206 := by decide +kernel

theorem rowEval16206 (x : Key → ℝ) : Integer.Sparse.eval row16206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16206, Integer.Sparse.eval_collectBalanced, rawRowCheck16206]

def rawRow16207 : Integer.Sparse Key := [(key2793, 6), (key2670, -2), (key2793, -2), (key2785, -2), (key2828, 6), (key2615, -2), (key2828, -2), (key2808, -2), (key2725, -2), (key2879, -2), (key2869, -2), (key2639, -2), (key2879, -2), (key2859, -2), (key2639, 2), (key2631, 2), (key2725, 2), (key2705, 2), (key2869, 2), (key2859, 2)]

theorem rawRowCheck16207 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form3 = rawRow16207 := by decide +kernel

def row16207 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

theorem rowCheck16207 : row16207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16207 := by decide +kernel

theorem rowEval16207 (x : Key → ℝ) : Integer.Sparse.eval row16207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16207, Integer.Sparse.eval_collectBalanced, rawRowCheck16207]

def rawRow16208 : Integer.Sparse Key := [(key2793, 6), (key2785, -2), (key2670, -2), (key2793, -2), (key2828, 6), (key2808, -2), (key2615, -2), (key2828, -2), (key2869, -2), (key2725, -2), (key2879, -2), (key2859, -2), (key2639, -2), (key2879, -2), (key2705, 2), (key2859, 2), (key2631, 2), (key2869, 2), (key2639, 2), (key2725, 2)]

theorem rawRowCheck16208 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form3 = rawRow16208 := by decide +kernel

def row16208 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

theorem rowCheck16208 : row16208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16208 := by decide +kernel

theorem rowEval16208 (x : Key → ℝ) : Integer.Sparse.eval row16208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16208, Integer.Sparse.eval_collectBalanced, rawRowCheck16208]

def rawRow16209 : Integer.Sparse Key := [(key2793, 6), (key2785, -2), (key2793, -2), (key2670, -2), (key2828, 6), (key2808, -2), (key2828, -2), (key2615, -2), (key2869, -2), (key2879, -2), (key2725, -2), (key2859, -2), (key2879, -2), (key2639, -2), (key2859, 2), (key2705, 2), (key2869, 2), (key2631, 2), (key2725, 2), (key2639, 2)]

theorem rawRowCheck16209 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form3 = rawRow16209 := by decide +kernel

def row16209 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

theorem rowCheck16209 : row16209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16209 := by decide +kernel

theorem rowEval16209 (x : Key → ℝ) : Integer.Sparse.eval row16209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16209, Integer.Sparse.eval_collectBalanced, rawRowCheck16209]

def rawRow16210 : Integer.Sparse Key := [(key2793, 6), (key2793, -2), (key2670, -2), (key2785, -2), (key2828, 6), (key2828, -2), (key2615, -2), (key2808, -2), (key2879, -2), (key2725, -2), (key2869, -2), (key2879, -2), (key2639, -2), (key2859, -2), (key2725, 2), (key2869, 2), (key2639, 2), (key2859, 2), (key2631, 2), (key2705, 2)]

theorem rawRowCheck16210 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form3 = rawRow16210 := by decide +kernel

def row16210 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

theorem rowCheck16210 : row16210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16210 := by decide +kernel

theorem rowEval16210 (x : Key → ℝ) : Integer.Sparse.eval row16210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16210, Integer.Sparse.eval_collectBalanced, rawRowCheck16210]

def rawRow16211 : Integer.Sparse Key := [(key2793, 6), (key2793, -2), (key2785, -2), (key2670, -2), (key2828, 6), (key2828, -2), (key2808, -2), (key2615, -2), (key2879, -2), (key2869, -2), (key2725, -2), (key2879, -2), (key2859, -2), (key2639, -2), (key2869, 2), (key2725, 2), (key2859, 2), (key2639, 2), (key2705, 2), (key2631, 2)]

theorem rawRowCheck16211 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form3 = rawRow16211 := by decide +kernel

def row16211 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

theorem rowCheck16211 : row16211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16211 := by decide +kernel

theorem rowEval16211 (x : Key → ℝ) : Integer.Sparse.eval row16211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16211, Integer.Sparse.eval_collectBalanced, rawRowCheck16211]

def rawRow16212 : Integer.Sparse Key := [(key2808, 6), (key2705, -2), (key2859, -2), (key2859, -2), (key2785, 6), (key2631, -2), (key2869, -2), (key2869, -2), (key2670, -2), (key2793, -2), (key2793, -2), (key2615, -2), (key2828, -2), (key2828, -2), (key2639, 2), (key2639, 2), (key2725, 2), (key2725, 2), (key2879, 2), (key2879, 2)]

theorem rawRowCheck16212 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form3 = rawRow16212 := by decide +kernel

def row16212 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

theorem rowCheck16212 : row16212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16212 := by decide +kernel

theorem rowEval16212 (x : Key → ℝ) : Integer.Sparse.eval row16212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16212, Integer.Sparse.eval_collectBalanced, rawRowCheck16212]

def rawRow16213 : Integer.Sparse Key := [(key2808, 6), (key2859, -2), (key2705, -2), (key2859, -2), (key2785, 6), (key2869, -2), (key2631, -2), (key2869, -2), (key2793, -2), (key2670, -2), (key2793, -2), (key2828, -2), (key2615, -2), (key2828, -2), (key2725, 2), (key2879, 2), (key2639, 2), (key2879, 2), (key2639, 2), (key2725, 2)]

theorem rawRowCheck16213 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form3 = rawRow16213 := by decide +kernel

def row16213 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

theorem rowCheck16213 : row16213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16213 := by decide +kernel

theorem rowEval16213 (x : Key → ℝ) : Integer.Sparse.eval row16213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16213, Integer.Sparse.eval_collectBalanced, rawRowCheck16213]

def rawRow16214 : Integer.Sparse Key := [(key2808, 6), (key2859, -2), (key2859, -2), (key2705, -2), (key2785, 6), (key2869, -2), (key2869, -2), (key2631, -2), (key2793, -2), (key2793, -2), (key2670, -2), (key2828, -2), (key2828, -2), (key2615, -2), (key2879, 2), (key2725, 2), (key2879, 2), (key2639, 2), (key2725, 2), (key2639, 2)]

theorem rawRowCheck16214 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form3 = rawRow16214 := by decide +kernel

def row16214 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

theorem rowCheck16214 : row16214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16214 := by decide +kernel

theorem rowEval16214 (x : Key → ℝ) : Integer.Sparse.eval row16214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16214, Integer.Sparse.eval_collectBalanced, rawRowCheck16214]

def rawRow16215 : Integer.Sparse Key := [(key2859, 6), (key2705, -2), (key2808, -2), (key2859, -2), (key2869, 6), (key2631, -2), (key2785, -2), (key2869, -2), (key2725, -2), (key2828, -2), (key2879, -2), (key2639, -2), (key2793, -2), (key2879, -2), (key2615, 2), (key2639, 2), (key2670, 2), (key2725, 2), (key2793, 2), (key2828, 2)]

theorem rawRowCheck16215 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form3 = rawRow16215 := by decide +kernel

def row16215 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

theorem rowCheck16215 : row16215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16215 := by decide +kernel

theorem rowEval16215 (x : Key → ℝ) : Integer.Sparse.eval row16215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16215, Integer.Sparse.eval_collectBalanced, rawRowCheck16215]

def rawRow16216 : Integer.Sparse Key := [(key2859, 6), (key2705, -2), (key2859, -2), (key2808, -2), (key2869, 6), (key2631, -2), (key2869, -2), (key2785, -2), (key2725, -2), (key2879, -2), (key2828, -2), (key2639, -2), (key2879, -2), (key2793, -2), (key2639, 2), (key2615, 2), (key2725, 2), (key2670, 2), (key2828, 2), (key2793, 2)]

theorem rawRowCheck16216 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form3 = rawRow16216 := by decide +kernel

def row16216 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

theorem rowCheck16216 : row16216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16216 := by decide +kernel

theorem rowEval16216 (x : Key → ℝ) : Integer.Sparse.eval row16216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16216, Integer.Sparse.eval_collectBalanced, rawRowCheck16216]

def rawRow16217 : Integer.Sparse Key := [(key2859, 6), (key2808, -2), (key2705, -2), (key2859, -2), (key2869, 6), (key2785, -2), (key2631, -2), (key2869, -2), (key2828, -2), (key2725, -2), (key2879, -2), (key2793, -2), (key2639, -2), (key2879, -2), (key2670, 2), (key2793, 2), (key2615, 2), (key2828, 2), (key2639, 2), (key2725, 2)]

theorem rawRowCheck16217 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form3 = rawRow16217 := by decide +kernel

def row16217 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

theorem rowCheck16217 : row16217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16217 := by decide +kernel

theorem rowEval16217 (x : Key → ℝ) : Integer.Sparse.eval row16217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16217, Integer.Sparse.eval_collectBalanced, rawRowCheck16217]

def rawRow16218 : Integer.Sparse Key := [(key2859, 6), (key2808, -2), (key2859, -2), (key2705, -2), (key2869, 6), (key2785, -2), (key2869, -2), (key2631, -2), (key2828, -2), (key2879, -2), (key2725, -2), (key2793, -2), (key2879, -2), (key2639, -2), (key2793, 2), (key2670, 2), (key2828, 2), (key2615, 2), (key2725, 2), (key2639, 2)]

theorem rawRowCheck16218 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form3 = rawRow16218 := by decide +kernel

def row16218 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

theorem rowCheck16218 : row16218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16218 := by decide +kernel

theorem rowEval16218 (x : Key → ℝ) : Integer.Sparse.eval row16218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16218, Integer.Sparse.eval_collectBalanced, rawRowCheck16218]

def rawRow16219 : Integer.Sparse Key := [(key2859, 6), (key2859, -2), (key2705, -2), (key2808, -2), (key2869, 6), (key2869, -2), (key2631, -2), (key2785, -2), (key2879, -2), (key2725, -2), (key2828, -2), (key2879, -2), (key2639, -2), (key2793, -2), (key2725, 2), (key2828, 2), (key2639, 2), (key2793, 2), (key2615, 2), (key2670, 2)]

theorem rawRowCheck16219 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form3 = rawRow16219 := by decide +kernel

def row16219 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

theorem rowCheck16219 : row16219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16219 := by decide +kernel

theorem rowEval16219 (x : Key → ℝ) : Integer.Sparse.eval row16219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16219, Integer.Sparse.eval_collectBalanced, rawRowCheck16219]

def rawRow16220 : Integer.Sparse Key := [(key2859, 6), (key2859, -2), (key2808, -2), (key2705, -2), (key2869, 6), (key2869, -2), (key2785, -2), (key2631, -2), (key2879, -2), (key2828, -2), (key2725, -2), (key2879, -2), (key2793, -2), (key2639, -2), (key2828, 2), (key2725, 2), (key2793, 2), (key2639, 2), (key2670, 2), (key2615, 2)]

theorem rawRowCheck16220 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form3 = rawRow16220 := by decide +kernel

def row16220 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

theorem rowCheck16220 : row16220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16220 := by decide +kernel

theorem rowEval16220 (x : Key → ℝ) : Integer.Sparse.eval row16220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16220, Integer.Sparse.eval_collectBalanced, rawRowCheck16220]

def rawRow16221 : Integer.Sparse Key := [(key2828, 6), (key2725, -2), (key2869, -2), (key2879, -2), (key2793, 6), (key2639, -2), (key2859, -2), (key2879, -2), (key2670, -2), (key2785, -2), (key2793, -2), (key2615, -2), (key2808, -2), (key2828, -2), (key2631, 2), (key2639, 2), (key2705, 2), (key2725, 2), (key2859, 2), (key2869, 2)]

theorem rawRowCheck16221 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form3 = rawRow16221 := by decide +kernel

def row16221 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

theorem rowCheck16221 : row16221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16221 := by decide +kernel

theorem rowEval16221 (x : Key → ℝ) : Integer.Sparse.eval row16221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16221, Integer.Sparse.eval_collectBalanced, rawRowCheck16221]

def rawRow16222 : Integer.Sparse Key := [(key2828, 6), (key2725, -2), (key2879, -2), (key2869, -2), (key2793, 6), (key2639, -2), (key2879, -2), (key2859, -2), (key2670, -2), (key2793, -2), (key2785, -2), (key2615, -2), (key2828, -2), (key2808, -2), (key2639, 2), (key2631, 2), (key2725, 2), (key2705, 2), (key2869, 2), (key2859, 2)]

theorem rawRowCheck16222 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form3 = rawRow16222 := by decide +kernel

def row16222 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

theorem rowCheck16222 : row16222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16222 := by decide +kernel

theorem rowEval16222 (x : Key → ℝ) : Integer.Sparse.eval row16222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16222, Integer.Sparse.eval_collectBalanced, rawRowCheck16222]

def rawRow16223 : Integer.Sparse Key := [(key2828, 6), (key2869, -2), (key2725, -2), (key2879, -2), (key2793, 6), (key2859, -2), (key2639, -2), (key2879, -2), (key2785, -2), (key2670, -2), (key2793, -2), (key2808, -2), (key2615, -2), (key2828, -2), (key2705, 2), (key2859, 2), (key2631, 2), (key2869, 2), (key2639, 2), (key2725, 2)]

theorem rawRowCheck16223 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form3 = rawRow16223 := by decide +kernel

def row16223 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

theorem rowCheck16223 : row16223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16223 := by decide +kernel

theorem rowEval16223 (x : Key → ℝ) : Integer.Sparse.eval row16223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16223, Integer.Sparse.eval_collectBalanced, rawRowCheck16223]

def rawRow16224 : Integer.Sparse Key := [(key2828, 6), (key2869, -2), (key2879, -2), (key2725, -2), (key2793, 6), (key2859, -2), (key2879, -2), (key2639, -2), (key2785, -2), (key2793, -2), (key2670, -2), (key2808, -2), (key2828, -2), (key2615, -2), (key2859, 2), (key2705, 2), (key2869, 2), (key2631, 2), (key2725, 2), (key2639, 2)]

theorem rawRowCheck16224 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form3 = rawRow16224 := by decide +kernel

def row16224 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

theorem rowCheck16224 : row16224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16224 := by decide +kernel

theorem rowEval16224 (x : Key → ℝ) : Integer.Sparse.eval row16224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16224, Integer.Sparse.eval_collectBalanced, rawRowCheck16224]

def rawRow16225 : Integer.Sparse Key := [(key2828, 6), (key2879, -2), (key2725, -2), (key2869, -2), (key2793, 6), (key2879, -2), (key2639, -2), (key2859, -2), (key2793, -2), (key2670, -2), (key2785, -2), (key2828, -2), (key2615, -2), (key2808, -2), (key2725, 2), (key2869, 2), (key2639, 2), (key2859, 2), (key2631, 2), (key2705, 2)]

theorem rawRowCheck16225 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form3 = rawRow16225 := by decide +kernel

def row16225 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

theorem rowCheck16225 : row16225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16225 := by decide +kernel

theorem rowEval16225 (x : Key → ℝ) : Integer.Sparse.eval row16225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16225, Integer.Sparse.eval_collectBalanced, rawRowCheck16225]

def rawRow16226 : Integer.Sparse Key := [(key2828, 6), (key2879, -2), (key2869, -2), (key2725, -2), (key2793, 6), (key2879, -2), (key2859, -2), (key2639, -2), (key2793, -2), (key2785, -2), (key2670, -2), (key2828, -2), (key2808, -2), (key2615, -2), (key2869, 2), (key2725, 2), (key2859, 2), (key2639, 2), (key2705, 2), (key2631, 2)]

theorem rawRowCheck16226 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form3 = rawRow16226 := by decide +kernel

def row16226 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

theorem rowCheck16226 : row16226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16226 := by decide +kernel

theorem rowEval16226 (x : Key → ℝ) : Integer.Sparse.eval row16226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16226, Integer.Sparse.eval_collectBalanced, rawRowCheck16226]

def rawRow16227 : Integer.Sparse Key := [(key2869, 6), (key2725, -2), (key2828, -2), (key2879, -2), (key2859, 6), (key2639, -2), (key2793, -2), (key2879, -2), (key2705, -2), (key2808, -2), (key2859, -2), (key2631, -2), (key2785, -2), (key2869, -2), (key2615, 2), (key2639, 2), (key2670, 2), (key2725, 2), (key2793, 2), (key2828, 2)]

theorem rawRowCheck16227 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form3 = rawRow16227 := by decide +kernel

def row16227 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

theorem rowCheck16227 : row16227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16227 := by decide +kernel

theorem rowEval16227 (x : Key → ℝ) : Integer.Sparse.eval row16227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16227, Integer.Sparse.eval_collectBalanced, rawRowCheck16227]

def rawRow16228 : Integer.Sparse Key := [(key2869, 6), (key2725, -2), (key2879, -2), (key2828, -2), (key2859, 6), (key2639, -2), (key2879, -2), (key2793, -2), (key2705, -2), (key2859, -2), (key2808, -2), (key2631, -2), (key2869, -2), (key2785, -2), (key2639, 2), (key2615, 2), (key2725, 2), (key2670, 2), (key2828, 2), (key2793, 2)]

theorem rawRowCheck16228 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form3 = rawRow16228 := by decide +kernel

def row16228 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

theorem rowCheck16228 : row16228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16228 := by decide +kernel

theorem rowEval16228 (x : Key → ℝ) : Integer.Sparse.eval row16228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16228, Integer.Sparse.eval_collectBalanced, rawRowCheck16228]

def rawRow16229 : Integer.Sparse Key := [(key2869, 6), (key2828, -2), (key2725, -2), (key2879, -2), (key2859, 6), (key2793, -2), (key2639, -2), (key2879, -2), (key2808, -2), (key2705, -2), (key2859, -2), (key2785, -2), (key2631, -2), (key2869, -2), (key2670, 2), (key2793, 2), (key2615, 2), (key2828, 2), (key2639, 2), (key2725, 2)]

theorem rawRowCheck16229 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form3 = rawRow16229 := by decide +kernel

def row16229 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

theorem rowCheck16229 : row16229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16229 := by decide +kernel

theorem rowEval16229 (x : Key → ℝ) : Integer.Sparse.eval row16229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16229, Integer.Sparse.eval_collectBalanced, rawRowCheck16229]

def rawRow16230 : Integer.Sparse Key := [(key2869, 6), (key2828, -2), (key2879, -2), (key2725, -2), (key2859, 6), (key2793, -2), (key2879, -2), (key2639, -2), (key2808, -2), (key2859, -2), (key2705, -2), (key2785, -2), (key2869, -2), (key2631, -2), (key2793, 2), (key2670, 2), (key2828, 2), (key2615, 2), (key2725, 2), (key2639, 2)]

theorem rawRowCheck16230 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form3 = rawRow16230 := by decide +kernel

def row16230 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

theorem rowCheck16230 : row16230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16230 := by decide +kernel

theorem rowEval16230 (x : Key → ℝ) : Integer.Sparse.eval row16230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16230, Integer.Sparse.eval_collectBalanced, rawRowCheck16230]

def rawRow16231 : Integer.Sparse Key := [(key2869, 6), (key2879, -2), (key2725, -2), (key2828, -2), (key2859, 6), (key2879, -2), (key2639, -2), (key2793, -2), (key2859, -2), (key2705, -2), (key2808, -2), (key2869, -2), (key2631, -2), (key2785, -2), (key2725, 2), (key2828, 2), (key2639, 2), (key2793, 2), (key2615, 2), (key2670, 2)]

theorem rawRowCheck16231 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form3 = rawRow16231 := by decide +kernel

def row16231 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

theorem rowCheck16231 : row16231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16231 := by decide +kernel

theorem rowEval16231 (x : Key → ℝ) : Integer.Sparse.eval row16231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16231, Integer.Sparse.eval_collectBalanced, rawRowCheck16231]

def rawRow16232 : Integer.Sparse Key := [(key2869, 6), (key2879, -2), (key2828, -2), (key2725, -2), (key2859, 6), (key2879, -2), (key2793, -2), (key2639, -2), (key2859, -2), (key2808, -2), (key2705, -2), (key2869, -2), (key2785, -2), (key2631, -2), (key2828, 2), (key2725, 2), (key2793, 2), (key2639, 2), (key2670, 2), (key2615, 2)]

theorem rawRowCheck16232 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form3 = rawRow16232 := by decide +kernel

def row16232 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

theorem rowCheck16232 : row16232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16232 := by decide +kernel

theorem rowEval16232 (x : Key → ℝ) : Integer.Sparse.eval row16232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16232, Integer.Sparse.eval_collectBalanced, rawRowCheck16232]

def rawRow16233 : Integer.Sparse Key := [(key2879, 6), (key2725, -2), (key2828, -2), (key2869, -2), (key2879, 6), (key2639, -2), (key2793, -2), (key2859, -2), (key2725, -2), (key2828, -2), (key2869, -2), (key2639, -2), (key2793, -2), (key2859, -2), (key2615, 2), (key2631, 2), (key2670, 2), (key2705, 2), (key2785, 2), (key2808, 2)]

theorem rawRowCheck16233 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form3 = rawRow16233 := by decide +kernel

def row16233 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

theorem rowCheck16233 : row16233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16233 := by decide +kernel

theorem rowEval16233 (x : Key → ℝ) : Integer.Sparse.eval row16233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16233, Integer.Sparse.eval_collectBalanced, rawRowCheck16233]

def rawRow16234 : Integer.Sparse Key := [(key2879, 6), (key2725, -2), (key2869, -2), (key2828, -2), (key2879, 6), (key2639, -2), (key2859, -2), (key2793, -2), (key2725, -2), (key2869, -2), (key2828, -2), (key2639, -2), (key2859, -2), (key2793, -2), (key2631, 2), (key2615, 2), (key2705, 2), (key2670, 2), (key2808, 2), (key2785, 2)]

theorem rawRowCheck16234 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form3 = rawRow16234 := by decide +kernel

def row16234 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

theorem rowCheck16234 : row16234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16234 := by decide +kernel

theorem rowEval16234 (x : Key → ℝ) : Integer.Sparse.eval row16234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16234, Integer.Sparse.eval_collectBalanced, rawRowCheck16234]

def rawRow16235 : Integer.Sparse Key := [(key2879, 6), (key2828, -2), (key2725, -2), (key2869, -2), (key2879, 6), (key2793, -2), (key2639, -2), (key2859, -2), (key2828, -2), (key2725, -2), (key2869, -2), (key2793, -2), (key2639, -2), (key2859, -2), (key2670, 2), (key2785, 2), (key2615, 2), (key2808, 2), (key2631, 2), (key2705, 2)]

theorem rawRowCheck16235 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form3 = rawRow16235 := by decide +kernel

def row16235 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

theorem rowCheck16235 : row16235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16235 := by decide +kernel

theorem rowEval16235 (x : Key → ℝ) : Integer.Sparse.eval row16235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16235, Integer.Sparse.eval_collectBalanced, rawRowCheck16235]

def rawRow16236 : Integer.Sparse Key := [(key2879, 6), (key2828, -2), (key2869, -2), (key2725, -2), (key2879, 6), (key2793, -2), (key2859, -2), (key2639, -2), (key2828, -2), (key2869, -2), (key2725, -2), (key2793, -2), (key2859, -2), (key2639, -2), (key2785, 2), (key2670, 2), (key2808, 2), (key2615, 2), (key2705, 2), (key2631, 2)]

theorem rawRowCheck16236 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form3 = rawRow16236 := by decide +kernel

def row16236 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

theorem rowCheck16236 : row16236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16236 := by decide +kernel

theorem rowEval16236 (x : Key → ℝ) : Integer.Sparse.eval row16236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16236, Integer.Sparse.eval_collectBalanced, rawRowCheck16236]

def rawRow16237 : Integer.Sparse Key := [(key2879, 6), (key2869, -2), (key2725, -2), (key2828, -2), (key2879, 6), (key2859, -2), (key2639, -2), (key2793, -2), (key2869, -2), (key2725, -2), (key2828, -2), (key2859, -2), (key2639, -2), (key2793, -2), (key2705, 2), (key2808, 2), (key2631, 2), (key2785, 2), (key2615, 2), (key2670, 2)]

theorem rawRowCheck16237 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form3 = rawRow16237 := by decide +kernel

def row16237 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

theorem rowCheck16237 : row16237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16237 := by decide +kernel

theorem rowEval16237 (x : Key → ℝ) : Integer.Sparse.eval row16237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16237, Integer.Sparse.eval_collectBalanced, rawRowCheck16237]

def rawRow16238 : Integer.Sparse Key := [(key2879, 6), (key2869, -2), (key2828, -2), (key2725, -2), (key2879, 6), (key2859, -2), (key2793, -2), (key2639, -2), (key2869, -2), (key2828, -2), (key2725, -2), (key2859, -2), (key2793, -2), (key2639, -2), (key2808, 2), (key2705, 2), (key2785, 2), (key2631, 2), (key2670, 2), (key2615, 2)]

theorem rawRowCheck16238 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form3 = rawRow16238 := by decide +kernel

def row16238 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

theorem rowCheck16238 : row16238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16238 := by decide +kernel

theorem rowEval16238 (x : Key → ℝ) : Integer.Sparse.eval row16238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16238, Integer.Sparse.eval_collectBalanced, rawRowCheck16238]

def rawRow16239 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1075, -2), (key1040, 6), (key1111, -2), (key1111, -2), (key1154, -2), (key998, 2), (key998, 2), (key1190, 2), (key1190, 2), (key1211, 2), (key1211, 2), (key1005, -2), (key1192, -2), (key1192, -2), (key1126, 6), (key1018, -2), (key1198, -2), (key1198, -2)]

theorem rawRowCheck16239 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form4 = rawRow16239 := by decide +kernel

def row16239 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

theorem rowCheck16239 : row16239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16239 := by decide +kernel

theorem rowEval16239 (x : Key → ℝ) : Integer.Sparse.eval row16239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16239, Integer.Sparse.eval_collectBalanced, rawRowCheck16239]

def rawRow16240 : Integer.Sparse Key := [(key1033, -2), (key1075, -2), (key1033, -2), (key1040, 6), (key1111, -2), (key1154, -2), (key1111, -2), (key1190, 2), (key1211, 2), (key998, 2), (key1211, 2), (key998, 2), (key1190, 2), (key1192, -2), (key1005, -2), (key1192, -2), (key1126, 6), (key1198, -2), (key1018, -2), (key1198, -2)]

theorem rawRowCheck16240 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form4 = rawRow16240 := by decide +kernel

def row16240 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

theorem rowCheck16240 : row16240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16240 := by decide +kernel

theorem rowEval16240 (x : Key → ℝ) : Integer.Sparse.eval row16240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16240, Integer.Sparse.eval_collectBalanced, rawRowCheck16240]

def rawRow16241 : Integer.Sparse Key := [(key1075, -2), (key1033, -2), (key1033, -2), (key1040, 6), (key1154, -2), (key1111, -2), (key1111, -2), (key1211, 2), (key1190, 2), (key1211, 2), (key998, 2), (key1190, 2), (key998, 2), (key1192, -2), (key1192, -2), (key1005, -2), (key1126, 6), (key1198, -2), (key1198, -2), (key1018, -2)]

theorem rawRowCheck16241 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form4 = rawRow16241 := by decide +kernel

def row16241 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

theorem rowCheck16241 : row16241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16241 := by decide +kernel

theorem rowEval16241 (x : Key → ℝ) : Integer.Sparse.eval row16241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16241, Integer.Sparse.eval_collectBalanced, rawRowCheck16241]

def rawRow16242 : Integer.Sparse Key := [(key1033, -2), (key1040, -2), (key1075, -2), (key1033, 6), (key1190, -2), (key1192, -2), (key1211, -2), (key998, 2), (key1005, 2), (key1111, 2), (key1192, 2), (key1154, 2), (key1211, 2), (key998, -2), (key1111, -2), (key1190, -2), (key1198, 6), (key1018, -2), (key1126, -2), (key1198, -2)]

theorem rawRowCheck16242 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form4 = rawRow16242 := by decide +kernel

def row16242 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

theorem rowCheck16242 : row16242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16242 := by decide +kernel

theorem rowEval16242 (x : Key → ℝ) : Integer.Sparse.eval row16242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16242, Integer.Sparse.eval_collectBalanced, rawRowCheck16242]

def rawRow16243 : Integer.Sparse Key := [(key1040, -2), (key1033, -2), (key1075, -2), (key1033, 6), (key1192, -2), (key1190, -2), (key1211, -2), (key1005, 2), (key998, 2), (key1192, 2), (key1111, 2), (key1211, 2), (key1154, 2), (key998, -2), (key1190, -2), (key1111, -2), (key1198, 6), (key1018, -2), (key1198, -2), (key1126, -2)]

theorem rawRowCheck16243 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form4 = rawRow16243 := by decide +kernel

def row16243 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

theorem rowCheck16243 : row16243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16243 := by decide +kernel

theorem rowEval16243 (x : Key → ℝ) : Integer.Sparse.eval row16243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16243, Integer.Sparse.eval_collectBalanced, rawRowCheck16243]

def rawRow16244 : Integer.Sparse Key := [(key1033, -2), (key1075, -2), (key1040, -2), (key1033, 6), (key1190, -2), (key1211, -2), (key1192, -2), (key1111, 2), (key1154, 2), (key998, 2), (key1211, 2), (key1005, 2), (key1192, 2), (key1111, -2), (key998, -2), (key1190, -2), (key1198, 6), (key1126, -2), (key1018, -2), (key1198, -2)]

theorem rawRowCheck16244 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form4 = rawRow16244 := by decide +kernel

def row16244 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

theorem rowCheck16244 : row16244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16244 := by decide +kernel

theorem rowEval16244 (x : Key → ℝ) : Integer.Sparse.eval row16244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16244, Integer.Sparse.eval_collectBalanced, rawRowCheck16244]

def rawRow16245 : Integer.Sparse Key := [(key1075, -2), (key1033, -2), (key1040, -2), (key1033, 6), (key1211, -2), (key1190, -2), (key1192, -2), (key1154, 2), (key1111, 2), (key1211, 2), (key998, 2), (key1192, 2), (key1005, 2), (key1111, -2), (key1190, -2), (key998, -2), (key1198, 6), (key1126, -2), (key1198, -2), (key1018, -2)]

theorem rawRowCheck16245 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form4 = rawRow16245 := by decide +kernel

def row16245 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

theorem rowCheck16245 : row16245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16245 := by decide +kernel

theorem rowEval16245 (x : Key → ℝ) : Integer.Sparse.eval row16245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16245, Integer.Sparse.eval_collectBalanced, rawRowCheck16245]

def rawRow16246 : Integer.Sparse Key := [(key1040, -2), (key1075, -2), (key1033, -2), (key1033, 6), (key1192, -2), (key1211, -2), (key1190, -2), (key1192, 2), (key1211, 2), (key1005, 2), (key1154, 2), (key998, 2), (key1111, 2), (key1190, -2), (key998, -2), (key1111, -2), (key1198, 6), (key1198, -2), (key1018, -2), (key1126, -2)]

theorem rawRowCheck16246 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form4 = rawRow16246 := by decide +kernel

def row16246 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

theorem rowCheck16246 : row16246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16246 := by decide +kernel

theorem rowEval16246 (x : Key → ℝ) : Integer.Sparse.eval row16246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16246, Integer.Sparse.eval_collectBalanced, rawRowCheck16246]

def rawRow16247 : Integer.Sparse Key := [(key1075, -2), (key1040, -2), (key1033, -2), (key1033, 6), (key1211, -2), (key1192, -2), (key1190, -2), (key1211, 2), (key1192, 2), (key1154, 2), (key1005, 2), (key1111, 2), (key998, 2), (key1190, -2), (key1111, -2), (key998, -2), (key1198, 6), (key1198, -2), (key1126, -2), (key1018, -2)]

theorem rawRowCheck16247 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form4 = rawRow16247 := by decide +kernel

def row16247 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

theorem rowCheck16247 : row16247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16247 := by decide +kernel

theorem rowEval16247 (x : Key → ℝ) : Integer.Sparse.eval row16247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16247, Integer.Sparse.eval_collectBalanced, rawRowCheck16247]

def rawRow16248 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1154, -2), (key1126, 6), (key1033, -2), (key1033, -2), (key1075, -2), (key998, 2), (key998, 2), (key1190, 2), (key1190, 2), (key1211, 2), (key1211, 2), (key1018, -2), (key1198, -2), (key1198, -2), (key1040, 6), (key1005, -2), (key1192, -2), (key1192, -2)]

theorem rawRowCheck16248 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form4 = rawRow16248 := by decide +kernel

def row16248 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

theorem rowCheck16248 : row16248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16248 := by decide +kernel

theorem rowEval16248 (x : Key → ℝ) : Integer.Sparse.eval row16248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16248, Integer.Sparse.eval_collectBalanced, rawRowCheck16248]

def rawRow16249 : Integer.Sparse Key := [(key1111, -2), (key1154, -2), (key1111, -2), (key1126, 6), (key1033, -2), (key1075, -2), (key1033, -2), (key1190, 2), (key1211, 2), (key998, 2), (key1211, 2), (key998, 2), (key1190, 2), (key1198, -2), (key1018, -2), (key1198, -2), (key1040, 6), (key1192, -2), (key1005, -2), (key1192, -2)]

theorem rawRowCheck16249 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form4 = rawRow16249 := by decide +kernel

def row16249 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

theorem rowCheck16249 : row16249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16249 := by decide +kernel

theorem rowEval16249 (x : Key → ℝ) : Integer.Sparse.eval row16249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16249, Integer.Sparse.eval_collectBalanced, rawRowCheck16249]

def rawRow16250 : Integer.Sparse Key := [(key1154, -2), (key1111, -2), (key1111, -2), (key1126, 6), (key1075, -2), (key1033, -2), (key1033, -2), (key1211, 2), (key1190, 2), (key1211, 2), (key998, 2), (key1190, 2), (key998, 2), (key1198, -2), (key1198, -2), (key1018, -2), (key1040, 6), (key1192, -2), (key1192, -2), (key1005, -2)]

theorem rawRowCheck16250 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form4 = rawRow16250 := by decide +kernel

def row16250 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

theorem rowCheck16250 : row16250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16250 := by decide +kernel

theorem rowEval16250 (x : Key → ℝ) : Integer.Sparse.eval row16250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16250, Integer.Sparse.eval_collectBalanced, rawRowCheck16250]

def rawRow16251 : Integer.Sparse Key := [(key1111, -2), (key1126, -2), (key1154, -2), (key1111, 6), (key1190, -2), (key1198, -2), (key1211, -2), (key998, 2), (key1018, 2), (key1033, 2), (key1198, 2), (key1075, 2), (key1211, 2), (key998, -2), (key1033, -2), (key1190, -2), (key1192, 6), (key1005, -2), (key1040, -2), (key1192, -2)]

theorem rawRowCheck16251 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form4 = rawRow16251 := by decide +kernel

def row16251 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

theorem rowCheck16251 : row16251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16251 := by decide +kernel

theorem rowEval16251 (x : Key → ℝ) : Integer.Sparse.eval row16251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16251, Integer.Sparse.eval_collectBalanced, rawRowCheck16251]

def rawRow16252 : Integer.Sparse Key := [(key1126, -2), (key1111, -2), (key1154, -2), (key1111, 6), (key1198, -2), (key1190, -2), (key1211, -2), (key1018, 2), (key998, 2), (key1198, 2), (key1033, 2), (key1211, 2), (key1075, 2), (key998, -2), (key1190, -2), (key1033, -2), (key1192, 6), (key1005, -2), (key1192, -2), (key1040, -2)]

theorem rawRowCheck16252 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form4 = rawRow16252 := by decide +kernel

def row16252 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

theorem rowCheck16252 : row16252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16252 := by decide +kernel

theorem rowEval16252 (x : Key → ℝ) : Integer.Sparse.eval row16252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16252, Integer.Sparse.eval_collectBalanced, rawRowCheck16252]

def rawRow16253 : Integer.Sparse Key := [(key1111, -2), (key1154, -2), (key1126, -2), (key1111, 6), (key1190, -2), (key1211, -2), (key1198, -2), (key1033, 2), (key1075, 2), (key998, 2), (key1211, 2), (key1018, 2), (key1198, 2), (key1033, -2), (key998, -2), (key1190, -2), (key1192, 6), (key1040, -2), (key1005, -2), (key1192, -2)]

theorem rawRowCheck16253 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form4 = rawRow16253 := by decide +kernel

def row16253 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

theorem rowCheck16253 : row16253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16253 := by decide +kernel

theorem rowEval16253 (x : Key → ℝ) : Integer.Sparse.eval row16253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16253, Integer.Sparse.eval_collectBalanced, rawRowCheck16253]

def rawRow16254 : Integer.Sparse Key := [(key1154, -2), (key1111, -2), (key1126, -2), (key1111, 6), (key1211, -2), (key1190, -2), (key1198, -2), (key1075, 2), (key1033, 2), (key1211, 2), (key998, 2), (key1198, 2), (key1018, 2), (key1033, -2), (key1190, -2), (key998, -2), (key1192, 6), (key1040, -2), (key1192, -2), (key1005, -2)]

theorem rawRowCheck16254 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form4 = rawRow16254 := by decide +kernel

def row16254 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

theorem rowCheck16254 : row16254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16254 := by decide +kernel

theorem rowEval16254 (x : Key → ℝ) : Integer.Sparse.eval row16254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16254, Integer.Sparse.eval_collectBalanced, rawRowCheck16254]

def rawRow16255 : Integer.Sparse Key := [(key1126, -2), (key1154, -2), (key1111, -2), (key1111, 6), (key1198, -2), (key1211, -2), (key1190, -2), (key1198, 2), (key1211, 2), (key1018, 2), (key1075, 2), (key998, 2), (key1033, 2), (key1190, -2), (key998, -2), (key1033, -2), (key1192, 6), (key1192, -2), (key1005, -2), (key1040, -2)]

theorem rawRowCheck16255 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form4 = rawRow16255 := by decide +kernel

def row16255 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

theorem rowCheck16255 : row16255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16255 := by decide +kernel

theorem rowEval16255 (x : Key → ℝ) : Integer.Sparse.eval row16255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16255, Integer.Sparse.eval_collectBalanced, rawRowCheck16255]

end MUB6.Certificate.GramRows

end OAI
