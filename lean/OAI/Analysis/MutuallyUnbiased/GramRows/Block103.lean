import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10112 : Integer.Sparse Key := [(key1236, -2), (key1130, -2), (key1125, -2), (key1236, -2), (key1130, -2), (key1233, -2), (key1044, -2), (key1116, -2), (key1038, -2), (key1125, -2), (key1116, -2), (key1038, -2), (key1243, 2), (key1159, 2), (key1152, 2), (key1243, 2), (key1159, 2), (key1233, 2), (key1009, 2), (key1116, 2), (key1003, 2), (key1152, 2), (key1116, 2), (key1003, 2)]

theorem rawRowCheck10112 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form7 = rawRow10112 := by decide +kernel

def row10112 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

theorem rowCheck10112 : row10112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10112 := by decide +kernel

theorem rowEval10112 (x : Key → ℝ) : Integer.Sparse.eval row10112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck10112, Integer.Sparse.eval_collectBalanced, rawRowCheck10112]

def rawRow10113 : Integer.Sparse Key := [(key1073, -2), (key1080, -2), (key1080, -2), (key1152, -2), (key1159, -2), (key1152, -2), (key1174, -2), (key1159, -2), (key1174, -2), (key1243, -2), (key1243, -2), (key1247, -2), (key1017, 2), (key1022, 2), (key1022, 2), (key1125, 2), (key1130, 2), (key1125, 2), (key1174, 2), (key1130, 2), (key1174, 2), (key1236, 2), (key1236, 2), (key1247, 2)]

theorem rawRowCheck10113 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form7 = rawRow10113 := by decide +kernel

def row10113 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

theorem rowCheck10113 : row10113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10113 := by decide +kernel

theorem rowEval10113 (x : Key → ℝ) : Integer.Sparse.eval row10113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10113, Integer.Sparse.eval_collectBalanced, rawRowCheck10113]

def rawRow10114 : Integer.Sparse Key := [(key1080, -2), (key1073, -2), (key1080, -2), (key1159, -2), (key1152, -2), (key1174, -2), (key1152, -2), (key1174, -2), (key1159, -2), (key1243, -2), (key1247, -2), (key1243, -2), (key1022, 2), (key1017, 2), (key1022, 2), (key1130, 2), (key1125, 2), (key1174, 2), (key1125, 2), (key1174, 2), (key1130, 2), (key1236, 2), (key1247, 2), (key1236, 2)]

theorem rawRowCheck10114 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form7 = rawRow10114 := by decide +kernel

def row10114 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

theorem rowCheck10114 : row10114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10114 := by decide +kernel

theorem rowEval10114 (x : Key → ℝ) : Integer.Sparse.eval row10114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10114, Integer.Sparse.eval_collectBalanced, rawRowCheck10114]

def rawRow10115 : Integer.Sparse Key := [(key1080, -2), (key1080, -2), (key1073, -2), (key1174, -2), (key1174, -2), (key1159, -2), (key1159, -2), (key1152, -2), (key1152, -2), (key1247, -2), (key1243, -2), (key1243, -2), (key1022, 2), (key1022, 2), (key1017, 2), (key1174, 2), (key1174, 2), (key1130, 2), (key1130, 2), (key1125, 2), (key1125, 2), (key1247, 2), (key1236, 2), (key1236, 2)]

theorem rawRowCheck10115 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form7 = rawRow10115 := by decide +kernel

def row10115 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

theorem rowCheck10115 : row10115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10115 := by decide +kernel

theorem rowEval10115 (x : Key → ℝ) : Integer.Sparse.eval row10115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10115, Integer.Sparse.eval_collectBalanced, rawRowCheck10115]

def rawRow10116 : Integer.Sparse Key := [(key1152, -2), (key1159, -2), (key1243, -2), (key1073, -2), (key1080, -2), (key1152, -2), (key1174, -2), (key1243, -2), (key1247, -2), (key1080, -2), (key1159, -2), (key1174, -2), (key1125, 2), (key1130, 2), (key1236, 2), (key1017, 2), (key1022, 2), (key1125, 2), (key1174, 2), (key1236, 2), (key1247, 2), (key1022, 2), (key1130, 2), (key1174, 2)]

theorem rawRowCheck10116 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form7 = rawRow10116 := by decide +kernel

def row10116 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

theorem rowCheck10116 : row10116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10116 := by decide +kernel

theorem rowEval10116 (x : Key → ℝ) : Integer.Sparse.eval row10116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10116, Integer.Sparse.eval_collectBalanced, rawRowCheck10116]

def rawRow10117 : Integer.Sparse Key := [(key1159, -2), (key1152, -2), (key1243, -2), (key1080, -2), (key1073, -2), (key1174, -2), (key1152, -2), (key1247, -2), (key1243, -2), (key1080, -2), (key1174, -2), (key1159, -2), (key1130, 2), (key1125, 2), (key1236, 2), (key1022, 2), (key1017, 2), (key1174, 2), (key1125, 2), (key1247, 2), (key1236, 2), (key1022, 2), (key1174, 2), (key1130, 2)]

theorem rawRowCheck10117 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form7 = rawRow10117 := by decide +kernel

def row10117 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

theorem rowCheck10117 : row10117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10117 := by decide +kernel

theorem rowEval10117 (x : Key → ℝ) : Integer.Sparse.eval row10117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10117, Integer.Sparse.eval_collectBalanced, rawRowCheck10117]

def rawRow10118 : Integer.Sparse Key := [(key1152, -2), (key1243, -2), (key1159, -2), (key1152, -2), (key1243, -2), (key1073, -2), (key1247, -2), (key1080, -2), (key1174, -2), (key1159, -2), (key1080, -2), (key1174, -2), (key1125, 2), (key1236, 2), (key1130, 2), (key1125, 2), (key1236, 2), (key1017, 2), (key1247, 2), (key1022, 2), (key1174, 2), (key1130, 2), (key1022, 2), (key1174, 2)]

theorem rawRowCheck10118 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form7 = rawRow10118 := by decide +kernel

def row10118 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

theorem rowCheck10118 : row10118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10118 := by decide +kernel

theorem rowEval10118 (x : Key → ℝ) : Integer.Sparse.eval row10118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10118, Integer.Sparse.eval_collectBalanced, rawRowCheck10118]

def rawRow10119 : Integer.Sparse Key := [(key1243, -2), (key1152, -2), (key1159, -2), (key1243, -2), (key1152, -2), (key1247, -2), (key1073, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1174, -2), (key1080, -2), (key1236, 2), (key1125, 2), (key1130, 2), (key1236, 2), (key1125, 2), (key1247, 2), (key1017, 2), (key1174, 2), (key1022, 2), (key1130, 2), (key1174, 2), (key1022, 2)]

theorem rawRowCheck10119 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form7 = rawRow10119 := by decide +kernel

def row10119 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

theorem rowCheck10119 : row10119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10119 := by decide +kernel

theorem rowEval10119 (x : Key → ℝ) : Integer.Sparse.eval row10119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck10119, Integer.Sparse.eval_collectBalanced, rawRowCheck10119]

def rawRow10120 : Integer.Sparse Key := [(key1159, -2), (key1243, -2), (key1152, -2), (key1174, -2), (key1247, -2), (key1080, -2), (key1243, -2), (key1073, -2), (key1152, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1130, 2), (key1236, 2), (key1125, 2), (key1174, 2), (key1247, 2), (key1022, 2), (key1236, 2), (key1017, 2), (key1125, 2), (key1174, 2), (key1022, 2), (key1130, 2)]

theorem rawRowCheck10120 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form7 = rawRow10120 := by decide +kernel

def row10120 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

theorem rowCheck10120 : row10120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10120 := by decide +kernel

theorem rowEval10120 (x : Key → ℝ) : Integer.Sparse.eval row10120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10120, Integer.Sparse.eval_collectBalanced, rawRowCheck10120]

def rawRow10121 : Integer.Sparse Key := [(key1243, -2), (key1159, -2), (key1152, -2), (key1247, -2), (key1174, -2), (key1243, -2), (key1080, -2), (key1152, -2), (key1073, -2), (key1174, -2), (key1159, -2), (key1080, -2), (key1236, 2), (key1130, 2), (key1125, 2), (key1247, 2), (key1174, 2), (key1236, 2), (key1022, 2), (key1125, 2), (key1017, 2), (key1174, 2), (key1130, 2), (key1022, 2)]

theorem rawRowCheck10121 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form7 = rawRow10121 := by decide +kernel

def row10121 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

theorem rowCheck10121 : row10121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10121 := by decide +kernel

theorem rowEval10121 (x : Key → ℝ) : Integer.Sparse.eval row10121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck10121, Integer.Sparse.eval_collectBalanced, rawRowCheck10121]

def rawRow10122 : Integer.Sparse Key := [(key1174, -2), (key1174, -2), (key1247, -2), (key1080, -2), (key1080, -2), (key1159, -2), (key1159, -2), (key1243, -2), (key1243, -2), (key1073, -2), (key1152, -2), (key1152, -2), (key1174, 2), (key1174, 2), (key1247, 2), (key1022, 2), (key1022, 2), (key1130, 2), (key1130, 2), (key1236, 2), (key1236, 2), (key1017, 2), (key1125, 2), (key1125, 2)]

theorem rawRowCheck10122 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form7 = rawRow10122 := by decide +kernel

def row10122 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

theorem rowCheck10122 : row10122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10122 := by decide +kernel

theorem rowEval10122 (x : Key → ℝ) : Integer.Sparse.eval row10122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10122, Integer.Sparse.eval_collectBalanced, rawRowCheck10122]

def rawRow10123 : Integer.Sparse Key := [(key1174, -2), (key1247, -2), (key1174, -2), (key1159, -2), (key1243, -2), (key1080, -2), (key1243, -2), (key1080, -2), (key1159, -2), (key1152, -2), (key1073, -2), (key1152, -2), (key1174, 2), (key1247, 2), (key1174, 2), (key1130, 2), (key1236, 2), (key1022, 2), (key1236, 2), (key1022, 2), (key1130, 2), (key1125, 2), (key1017, 2), (key1125, 2)]

theorem rawRowCheck10123 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form7 = rawRow10123 := by decide +kernel

def row10123 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

theorem rowCheck10123 : row10123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10123 := by decide +kernel

theorem rowEval10123 (x : Key → ℝ) : Integer.Sparse.eval row10123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10123, Integer.Sparse.eval_collectBalanced, rawRowCheck10123]

def rawRow10124 : Integer.Sparse Key := [(key1247, -2), (key1174, -2), (key1174, -2), (key1243, -2), (key1159, -2), (key1243, -2), (key1080, -2), (key1159, -2), (key1080, -2), (key1152, -2), (key1152, -2), (key1073, -2), (key1247, 2), (key1174, 2), (key1174, 2), (key1236, 2), (key1130, 2), (key1236, 2), (key1022, 2), (key1130, 2), (key1022, 2), (key1125, 2), (key1125, 2), (key1017, 2)]

theorem rawRowCheck10124 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form7 = rawRow10124 := by decide +kernel

def row10124 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

theorem rowCheck10124 : row10124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10124 := by decide +kernel

theorem rowEval10124 (x : Key → ℝ) : Integer.Sparse.eval row10124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck10124, Integer.Sparse.eval_collectBalanced, rawRowCheck10124]

def rawRow10125 : Integer.Sparse Key := [(key210, -2), (key210, -2), (key213, -2), (key430, -2), (key430, -2), (key590, -2), (key590, -2), (key592, -2), (key592, -2), (key461, -2), (key609, -2), (key609, -2), (key25, 1), (key25, 1), (key37, 1), (key37, 1), (key40, 1), (key40, 1), (key50, 1), (key50, 1), (key76, 1), (key76, 1), (key81, 1), (key81, 1), (key117, 1), (key117, 1), (key139, 1), (key139, 1), (key162, 1), (key162, 1), (key197, 1), (key197, 1), (key201, 1), (key201, 1), (key204, 1), (key204, 1)]

theorem rawRowCheck10125 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form8 = rawRow10125 := by decide +kernel

def row10125 : Integer.Sparse Key := [(key25, 2), (key37, 2), (key40, 2), (key50, 2), (key76, 2), (key81, 2), (key117, 2), (key139, 2), (key162, 2), (key197, 2), (key201, 2), (key204, 2), (key210, -4), (key213, -2), (key430, -4), (key461, -2), (key590, -4), (key592, -4), (key609, -4)]

theorem rowCheck10125 : row10125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10125 := by decide +kernel

theorem rowEval10125 (x : Key → ℝ) : Integer.Sparse.eval row10125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10125, Integer.Sparse.eval_collectBalanced, rawRowCheck10125]

def rawRow10126 : Integer.Sparse Key := [(key210, -2), (key213, -2), (key210, -2), (key590, -2), (key592, -2), (key430, -2), (key592, -2), (key430, -2), (key590, -2), (key609, -2), (key461, -2), (key609, -2), (key37, 1), (key40, 1), (key25, 1), (key40, 1), (key25, 1), (key37, 1), (key76, 1), (key81, 1), (key50, 1), (key81, 1), (key50, 1), (key76, 1), (key139, 1), (key162, 1), (key117, 1), (key162, 1), (key117, 1), (key139, 1), (key201, 1), (key204, 1), (key197, 1), (key204, 1), (key197, 1), (key201, 1)]

theorem rawRowCheck10126 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form8 = rawRow10126 := by decide +kernel

def row10126 : Integer.Sparse Key := [(key25, 2), (key37, 2), (key40, 2), (key50, 2), (key76, 2), (key81, 2), (key117, 2), (key139, 2), (key162, 2), (key197, 2), (key201, 2), (key204, 2), (key210, -4), (key213, -2), (key430, -4), (key461, -2), (key590, -4), (key592, -4), (key609, -4)]

theorem rowCheck10126 : row10126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10126 := by decide +kernel

theorem rowEval10126 (x : Key → ℝ) : Integer.Sparse.eval row10126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10126, Integer.Sparse.eval_collectBalanced, rawRowCheck10126]

def rawRow10127 : Integer.Sparse Key := [(key213, -2), (key210, -2), (key210, -2), (key592, -2), (key590, -2), (key592, -2), (key430, -2), (key590, -2), (key430, -2), (key609, -2), (key609, -2), (key461, -2), (key40, 1), (key37, 1), (key40, 1), (key25, 1), (key37, 1), (key25, 1), (key81, 1), (key76, 1), (key81, 1), (key50, 1), (key76, 1), (key50, 1), (key162, 1), (key139, 1), (key162, 1), (key117, 1), (key139, 1), (key117, 1), (key204, 1), (key201, 1), (key204, 1), (key197, 1), (key201, 1), (key197, 1)]

theorem rawRowCheck10127 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form8 = rawRow10127 := by decide +kernel

def row10127 : Integer.Sparse Key := [(key25, 2), (key37, 2), (key40, 2), (key50, 2), (key76, 2), (key81, 2), (key117, 2), (key139, 2), (key162, 2), (key197, 2), (key201, 2), (key204, 2), (key210, -4), (key213, -2), (key430, -4), (key461, -2), (key590, -4), (key592, -4), (key609, -4)]

theorem rowCheck10127 : row10127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10127 := by decide +kernel

theorem rowEval10127 (x : Key → ℝ) : Integer.Sparse.eval row10127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10127, Integer.Sparse.eval_collectBalanced, rawRowCheck10127]

def rawRow10128 : Integer.Sparse Key := [(key430, -2), (key430, -2), (key461, -2), (key210, -2), (key210, -2), (key590, -2), (key590, -2), (key609, -2), (key609, -2), (key213, -2), (key592, -2), (key592, -2), (key379, 1), (key379, 1), (key464, 1), (key464, 1), (key483, 1), (key483, 1), (key210, 1), (key210, 1), (key590, 1), (key590, 1), (key609, 1), (key609, 1), (key37, 1), (key37, 1), (key76, 1), (key76, 1), (key204, 1), (key204, 1), (key40, 1), (key40, 1), (key81, 1), (key81, 1), (key162, 1), (key162, 1)]

theorem rawRowCheck10128 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form8 = rawRow10128 := by decide +kernel

def row10128 : Integer.Sparse Key := [(key37, 2), (key40, 2), (key76, 2), (key81, 2), (key162, 2), (key204, 2), (key210, -2), (key213, -2), (key379, 2), (key430, -4), (key461, -2), (key464, 2), (key483, 2), (key590, -2), (key592, -4), (key609, -2)]

theorem rowCheck10128 : row10128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10128 := by decide +kernel

theorem rowEval10128 (x : Key → ℝ) : Integer.Sparse.eval row10128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10128, Integer.Sparse.eval_collectBalanced, rawRowCheck10128]

def rawRow10129 : Integer.Sparse Key := [(key430, -2), (key461, -2), (key430, -2), (key590, -2), (key609, -2), (key210, -2), (key609, -2), (key210, -2), (key590, -2), (key592, -2), (key213, -2), (key592, -2), (key464, 1), (key483, 1), (key379, 1), (key483, 1), (key379, 1), (key464, 1), (key590, 1), (key609, 1), (key210, 1), (key609, 1), (key210, 1), (key590, 1), (key565, 1), (key615, 1), (key215, 1), (key615, 1), (key37, 1), (key76, 1), (key81, 1), (key162, 1), (key40, 1), (key162, 1), (key40, 1), (key81, 1)]

theorem rawRowCheck10129 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form8 = rawRow10129 := by decide +kernel

def row10129 : Integer.Sparse Key := [(key37, 1), (key40, 2), (key76, 1), (key81, 2), (key162, 2), (key210, -2), (key213, -2), (key215, 1), (key379, 2), (key430, -4), (key461, -2), (key464, 2), (key483, 2), (key565, 1), (key590, -2), (key592, -4), (key609, -2), (key615, 2)]

theorem rowCheck10129 : row10129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10129 := by decide +kernel

theorem rowEval10129 (x : Key → ℝ) : Integer.Sparse.eval row10129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10129, Integer.Sparse.eval_collectBalanced, rawRowCheck10129]

def rawRow10130 : Integer.Sparse Key := [(key461, -2), (key430, -2), (key430, -2), (key609, -2), (key590, -2), (key609, -2), (key210, -2), (key590, -2), (key210, -2), (key592, -2), (key592, -2), (key213, -2), (key483, 1), (key464, 1), (key483, 1), (key379, 1), (key464, 1), (key379, 1), (key609, 1), (key590, 1), (key609, 1), (key210, 1), (key590, 1), (key210, 1), (key615, 1), (key565, 1), (key615, 1), (key215, 1), (key76, 1), (key37, 1), (key162, 1), (key81, 1), (key162, 1), (key40, 1), (key81, 1), (key40, 1)]

theorem rawRowCheck10130 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form8 = rawRow10130 := by decide +kernel

def row10130 : Integer.Sparse Key := [(key37, 1), (key40, 2), (key76, 1), (key81, 2), (key162, 2), (key210, -2), (key213, -2), (key215, 1), (key379, 2), (key430, -4), (key461, -2), (key464, 2), (key483, 2), (key565, 1), (key590, -2), (key592, -4), (key609, -2), (key615, 2)]

theorem rowCheck10130 : row10130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10130 := by decide +kernel

theorem rowEval10130 (x : Key → ℝ) : Integer.Sparse.eval row10130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck10130, Integer.Sparse.eval_collectBalanced, rawRowCheck10130]

def rawRow10131 : Integer.Sparse Key := [(key590, -2), (key592, -2), (key609, -2), (key210, -2), (key213, -2), (key430, -2), (key592, -2), (key461, -2), (key609, -2), (key210, -2), (key430, -2), (key590, -2), (key565, 1), (key567, 1), (key590, 1), (key612, 1), (key609, 1), (key615, 1), (key215, 1), (key217, 1), (key464, 1), (key612, 1), (key483, 1), (key615, 1), (key210, 1), (key217, 1), (key379, 1), (key567, 1), (key483, 1), (key609, 1), (key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1)]

theorem rawRowCheck10131 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form8 = rawRow10131 := by decide +kernel

def row10131 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

theorem rowCheck10131 : row10131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10131 := by decide +kernel

theorem rowEval10131 (x : Key → ℝ) : Integer.Sparse.eval row10131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10131, Integer.Sparse.eval_collectBalanced, rawRowCheck10131]

def rawRow10132 : Integer.Sparse Key := [(key592, -2), (key590, -2), (key609, -2), (key213, -2), (key210, -2), (key592, -2), (key430, -2), (key609, -2), (key461, -2), (key210, -2), (key590, -2), (key430, -2), (key567, 1), (key565, 1), (key612, 1), (key590, 1), (key615, 1), (key609, 1), (key217, 1), (key215, 1), (key612, 1), (key464, 1), (key615, 1), (key483, 1), (key217, 1), (key210, 1), (key567, 1), (key379, 1), (key609, 1), (key483, 1), (key37, 1), (key25, 1), (key76, 1), (key50, 1), (key139, 1), (key117, 1)]

theorem rawRowCheck10132 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form8 = rawRow10132 := by decide +kernel

def row10132 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

theorem rowCheck10132 : row10132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10132 := by decide +kernel

theorem rowEval10132 (x : Key → ℝ) : Integer.Sparse.eval row10132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10132, Integer.Sparse.eval_collectBalanced, rawRowCheck10132]

def rawRow10133 : Integer.Sparse Key := [(key590, -2), (key609, -2), (key592, -2), (key430, -2), (key461, -2), (key210, -2), (key609, -2), (key213, -2), (key592, -2), (key430, -2), (key210, -2), (key590, -2), (key590, 1), (key609, 1), (key565, 1), (key615, 1), (key567, 1), (key612, 1), (key464, 1), (key483, 1), (key215, 1), (key615, 1), (key217, 1), (key612, 1), (key379, 1), (key483, 1), (key210, 1), (key609, 1), (key217, 1), (key567, 1), (key50, 1), (key117, 1), (key25, 1), (key139, 1), (key37, 1), (key76, 1)]

theorem rawRowCheck10133 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form8 = rawRow10133 := by decide +kernel

def row10133 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

theorem rowCheck10133 : row10133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10133 := by decide +kernel

theorem rowEval10133 (x : Key → ℝ) : Integer.Sparse.eval row10133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10133, Integer.Sparse.eval_collectBalanced, rawRowCheck10133]

def rawRow10134 : Integer.Sparse Key := [(key609, -2), (key590, -2), (key592, -2), (key461, -2), (key430, -2), (key609, -2), (key210, -2), (key592, -2), (key213, -2), (key430, -2), (key590, -2), (key210, -2), (key609, 1), (key590, 1), (key615, 1), (key565, 1), (key612, 1), (key567, 1), (key483, 1), (key464, 1), (key615, 1), (key215, 1), (key612, 1), (key217, 1), (key483, 1), (key379, 1), (key609, 1), (key210, 1), (key567, 1), (key217, 1), (key117, 1), (key50, 1), (key139, 1), (key25, 1), (key76, 1), (key37, 1)]

theorem rawRowCheck10134 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form8 = rawRow10134 := by decide +kernel

def row10134 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

theorem rowCheck10134 : row10134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10134 := by decide +kernel

theorem rowEval10134 (x : Key → ℝ) : Integer.Sparse.eval row10134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck10134, Integer.Sparse.eval_collectBalanced, rawRowCheck10134]

def rawRow10135 : Integer.Sparse Key := [(key592, -2), (key609, -2), (key590, -2), (key592, -2), (key609, -2), (key213, -2), (key461, -2), (key210, -2), (key430, -2), (key590, -2), (key210, -2), (key430, -2), (key612, 1), (key615, 1), (key567, 1), (key609, 1), (key565, 1), (key590, 1), (key612, 1), (key615, 1), (key217, 1), (key483, 1), (key215, 1), (key464, 1), (key567, 1), (key609, 1), (key217, 1), (key483, 1), (key210, 1), (key379, 1), (key76, 1), (key139, 1), (key37, 1), (key117, 1), (key25, 1), (key50, 1)]

theorem rawRowCheck10135 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form8 = rawRow10135 := by decide +kernel

def row10135 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

theorem rowCheck10135 : row10135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10135 := by decide +kernel

theorem rowEval10135 (x : Key → ℝ) : Integer.Sparse.eval row10135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10135, Integer.Sparse.eval_collectBalanced, rawRowCheck10135]

def rawRow10136 : Integer.Sparse Key := [(key609, -2), (key592, -2), (key590, -2), (key609, -2), (key592, -2), (key461, -2), (key213, -2), (key430, -2), (key210, -2), (key590, -2), (key430, -2), (key210, -2), (key615, 1), (key612, 1), (key609, 1), (key567, 1), (key590, 1), (key565, 1), (key615, 1), (key612, 1), (key483, 1), (key217, 1), (key464, 1), (key215, 1), (key609, 1), (key567, 1), (key483, 1), (key217, 1), (key379, 1), (key210, 1), (key139, 1), (key76, 1), (key117, 1), (key37, 1), (key50, 1), (key25, 1)]

theorem rawRowCheck10136 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form8 = rawRow10136 := by decide +kernel

def row10136 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

theorem rowCheck10136 : row10136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10136 := by decide +kernel

theorem rowEval10136 (x : Key → ℝ) : Integer.Sparse.eval row10136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck10136, Integer.Sparse.eval_collectBalanced, rawRowCheck10136]

def rawRow10137 : Integer.Sparse Key := [(key215, -2), (key217, -2), (key217, -2), (key464, -2), (key466, -2), (key464, -2), (key612, -2), (key466, -2), (key612, -2), (key483, -2), (key483, -2), (key615, -2), (key210, 1), (key213, 1), (key210, 1), (key217, 1), (key213, 1), (key217, 1), (key379, 1), (key382, 1), (key379, 1), (key567, 1), (key382, 1), (key567, 1), (key430, 1), (key466, 1), (key430, 1), (key592, 1), (key466, 1), (key592, 1), (key461, 1), (key483, 1), (key461, 1), (key609, 1), (key483, 1), (key609, 1)]

theorem rawRowCheck10137 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form8 = rawRow10137 := by decide +kernel

def row10137 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

theorem rowCheck10137 : row10137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10137 := by decide +kernel

theorem rowEval10137 (x : Key → ℝ) : Integer.Sparse.eval row10137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10137, Integer.Sparse.eval_collectBalanced, rawRowCheck10137]

def rawRow10138 : Integer.Sparse Key := [(key217, -2), (key215, -2), (key217, -2), (key466, -2), (key464, -2), (key612, -2), (key464, -2), (key612, -2), (key466, -2), (key483, -2), (key615, -2), (key483, -2), (key213, 1), (key210, 1), (key217, 1), (key210, 1), (key217, 1), (key213, 1), (key382, 1), (key379, 1), (key567, 1), (key379, 1), (key567, 1), (key382, 1), (key466, 1), (key430, 1), (key592, 1), (key430, 1), (key592, 1), (key466, 1), (key483, 1), (key461, 1), (key609, 1), (key461, 1), (key609, 1), (key483, 1)]

theorem rawRowCheck10138 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form8 = rawRow10138 := by decide +kernel

def row10138 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

theorem rowCheck10138 : row10138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10138 := by decide +kernel

theorem rowEval10138 (x : Key → ℝ) : Integer.Sparse.eval row10138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10138, Integer.Sparse.eval_collectBalanced, rawRowCheck10138]

def rawRow10139 : Integer.Sparse Key := [(key217, -2), (key217, -2), (key215, -2), (key612, -2), (key612, -2), (key466, -2), (key466, -2), (key464, -2), (key464, -2), (key615, -2), (key483, -2), (key483, -2), (key217, 1), (key217, 1), (key213, 1), (key213, 1), (key210, 1), (key210, 1), (key567, 1), (key567, 1), (key382, 1), (key382, 1), (key379, 1), (key379, 1), (key592, 1), (key592, 1), (key466, 1), (key466, 1), (key430, 1), (key430, 1), (key609, 1), (key609, 1), (key483, 1), (key483, 1), (key461, 1), (key461, 1)]

theorem rawRowCheck10139 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form8 = rawRow10139 := by decide +kernel

def row10139 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

theorem rowCheck10139 : row10139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10139 := by decide +kernel

theorem rowEval10139 (x : Key → ℝ) : Integer.Sparse.eval row10139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10139, Integer.Sparse.eval_collectBalanced, rawRowCheck10139]

def rawRow10140 : Integer.Sparse Key := [(key464, -2), (key466, -2), (key483, -2), (key215, -2), (key217, -2), (key464, -2), (key612, -2), (key483, -2), (key615, -2), (key217, -2), (key466, -2), (key612, -2), (key379, 1), (key382, 1), (key430, 1), (key466, 1), (key461, 1), (key483, 1), (key210, 1), (key213, 1), (key430, 1), (key592, 1), (key461, 1), (key609, 1), (key210, 1), (key217, 1), (key379, 1), (key567, 1), (key483, 1), (key609, 1), (key213, 1), (key217, 1), (key382, 1), (key567, 1), (key466, 1), (key592, 1)]

theorem rawRowCheck10140 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form8 = rawRow10140 := by decide +kernel

def row10140 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

theorem rowCheck10140 : row10140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10140 := by decide +kernel

theorem rowEval10140 (x : Key → ℝ) : Integer.Sparse.eval row10140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10140, Integer.Sparse.eval_collectBalanced, rawRowCheck10140]

def rawRow10141 : Integer.Sparse Key := [(key466, -2), (key464, -2), (key483, -2), (key217, -2), (key215, -2), (key612, -2), (key464, -2), (key615, -2), (key483, -2), (key217, -2), (key612, -2), (key466, -2), (key382, 1), (key379, 1), (key466, 1), (key430, 1), (key483, 1), (key461, 1), (key213, 1), (key210, 1), (key592, 1), (key430, 1), (key609, 1), (key461, 1), (key217, 1), (key210, 1), (key567, 1), (key379, 1), (key609, 1), (key483, 1), (key217, 1), (key213, 1), (key567, 1), (key382, 1), (key592, 1), (key466, 1)]

theorem rawRowCheck10141 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form8 = rawRow10141 := by decide +kernel

def row10141 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

theorem rowCheck10141 : row10141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10141 := by decide +kernel

theorem rowEval10141 (x : Key → ℝ) : Integer.Sparse.eval row10141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10141, Integer.Sparse.eval_collectBalanced, rawRowCheck10141]

def rawRow10142 : Integer.Sparse Key := [(key464, -2), (key483, -2), (key466, -2), (key464, -2), (key483, -2), (key215, -2), (key615, -2), (key217, -2), (key612, -2), (key466, -2), (key217, -2), (key612, -2), (key430, 1), (key461, 1), (key379, 1), (key483, 1), (key382, 1), (key466, 1), (key430, 1), (key461, 1), (key210, 1), (key609, 1), (key213, 1), (key592, 1), (key379, 1), (key483, 1), (key210, 1), (key609, 1), (key217, 1), (key567, 1), (key382, 1), (key466, 1), (key213, 1), (key592, 1), (key217, 1), (key567, 1)]

theorem rawRowCheck10142 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form8 = rawRow10142 := by decide +kernel

def row10142 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

theorem rowCheck10142 : row10142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10142 := by decide +kernel

theorem rowEval10142 (x : Key → ℝ) : Integer.Sparse.eval row10142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10142, Integer.Sparse.eval_collectBalanced, rawRowCheck10142]

def rawRow10143 : Integer.Sparse Key := [(key483, -2), (key464, -2), (key466, -2), (key483, -2), (key464, -2), (key615, -2), (key215, -2), (key612, -2), (key217, -2), (key466, -2), (key612, -2), (key217, -2), (key461, 1), (key430, 1), (key483, 1), (key379, 1), (key466, 1), (key382, 1), (key461, 1), (key430, 1), (key609, 1), (key210, 1), (key592, 1), (key213, 1), (key483, 1), (key379, 1), (key609, 1), (key210, 1), (key567, 1), (key217, 1), (key466, 1), (key382, 1), (key592, 1), (key213, 1), (key567, 1), (key217, 1)]

theorem rawRowCheck10143 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form8 = rawRow10143 := by decide +kernel

def row10143 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

theorem rowCheck10143 : row10143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10143 := by decide +kernel

theorem rowEval10143 (x : Key → ℝ) : Integer.Sparse.eval row10143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck10143, Integer.Sparse.eval_collectBalanced, rawRowCheck10143]

def rawRow10144 : Integer.Sparse Key := [(key466, -2), (key483, -2), (key464, -2), (key612, -2), (key615, -2), (key217, -2), (key483, -2), (key215, -2), (key464, -2), (key612, -2), (key217, -2), (key466, -2), (key466, 1), (key483, 1), (key382, 1), (key461, 1), (key379, 1), (key430, 1), (key592, 1), (key609, 1), (key213, 1), (key461, 1), (key210, 1), (key430, 1), (key567, 1), (key609, 1), (key217, 1), (key483, 1), (key210, 1), (key379, 1), (key567, 1), (key592, 1), (key217, 1), (key466, 1), (key213, 1), (key382, 1)]

theorem rawRowCheck10144 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form8 = rawRow10144 := by decide +kernel

def row10144 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

theorem rowCheck10144 : row10144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10144 := by decide +kernel

theorem rowEval10144 (x : Key → ℝ) : Integer.Sparse.eval row10144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10144, Integer.Sparse.eval_collectBalanced, rawRowCheck10144]

def rawRow10145 : Integer.Sparse Key := [(key483, -2), (key466, -2), (key464, -2), (key615, -2), (key612, -2), (key483, -2), (key217, -2), (key464, -2), (key215, -2), (key612, -2), (key466, -2), (key217, -2), (key483, 1), (key466, 1), (key461, 1), (key382, 1), (key430, 1), (key379, 1), (key609, 1), (key592, 1), (key461, 1), (key213, 1), (key430, 1), (key210, 1), (key609, 1), (key567, 1), (key483, 1), (key217, 1), (key379, 1), (key210, 1), (key592, 1), (key567, 1), (key466, 1), (key217, 1), (key382, 1), (key213, 1)]

theorem rawRowCheck10145 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form8 = rawRow10145 := by decide +kernel

def row10145 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

theorem rowCheck10145 : row10145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10145 := by decide +kernel

theorem rowEval10145 (x : Key → ℝ) : Integer.Sparse.eval row10145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck10145, Integer.Sparse.eval_collectBalanced, rawRowCheck10145]

def rawRow10146 : Integer.Sparse Key := [(key612, -2), (key612, -2), (key615, -2), (key217, -2), (key217, -2), (key466, -2), (key466, -2), (key483, -2), (key483, -2), (key215, -2), (key464, -2), (key464, -2), (key567, 1), (key567, 1), (key592, 1), (key592, 1), (key609, 1), (key609, 1), (key217, 1), (key217, 1), (key466, 1), (key466, 1), (key483, 1), (key483, 1), (key213, 1), (key213, 1), (key382, 1), (key382, 1), (key461, 1), (key461, 1), (key210, 1), (key210, 1), (key379, 1), (key379, 1), (key430, 1), (key430, 1)]

theorem rawRowCheck10146 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form8 = rawRow10146 := by decide +kernel

def row10146 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

theorem rowCheck10146 : row10146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10146 := by decide +kernel

theorem rowEval10146 (x : Key → ℝ) : Integer.Sparse.eval row10146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10146, Integer.Sparse.eval_collectBalanced, rawRowCheck10146]

def rawRow10147 : Integer.Sparse Key := [(key612, -2), (key615, -2), (key612, -2), (key466, -2), (key483, -2), (key217, -2), (key483, -2), (key217, -2), (key466, -2), (key464, -2), (key215, -2), (key464, -2), (key592, 1), (key609, 1), (key567, 1), (key609, 1), (key567, 1), (key592, 1), (key466, 1), (key483, 1), (key217, 1), (key483, 1), (key217, 1), (key466, 1), (key382, 1), (key461, 1), (key213, 1), (key461, 1), (key213, 1), (key382, 1), (key379, 1), (key430, 1), (key210, 1), (key430, 1), (key210, 1), (key379, 1)]

theorem rawRowCheck10147 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form8 = rawRow10147 := by decide +kernel

def row10147 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

theorem rowCheck10147 : row10147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10147 := by decide +kernel

theorem rowEval10147 (x : Key → ℝ) : Integer.Sparse.eval row10147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10147, Integer.Sparse.eval_collectBalanced, rawRowCheck10147]

def rawRow10148 : Integer.Sparse Key := [(key615, -2), (key612, -2), (key612, -2), (key483, -2), (key466, -2), (key483, -2), (key217, -2), (key466, -2), (key217, -2), (key464, -2), (key464, -2), (key215, -2), (key609, 1), (key592, 1), (key609, 1), (key567, 1), (key592, 1), (key567, 1), (key483, 1), (key466, 1), (key483, 1), (key217, 1), (key466, 1), (key217, 1), (key461, 1), (key382, 1), (key461, 1), (key213, 1), (key382, 1), (key213, 1), (key430, 1), (key379, 1), (key430, 1), (key210, 1), (key379, 1), (key210, 1)]

theorem rawRowCheck10148 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form8 = rawRow10148 := by decide +kernel

def row10148 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

theorem rowCheck10148 : row10148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10148 := by decide +kernel

theorem rowEval10148 (x : Key → ℝ) : Integer.Sparse.eval row10148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck10148, Integer.Sparse.eval_collectBalanced, rawRowCheck10148]

def rawRow10149 : Integer.Sparse Key := [(key1003, 1), (key1003, 1), (key1017, 1), (key1017, 1), (key1022, 1), (key1022, 1), (key1038, 1), (key1038, 1), (key1073, 1), (key1073, 1), (key1080, 1), (key1080, 1), (key1125, 1), (key1125, 1), (key1152, 1), (key1152, 1), (key1174, 1), (key1174, 1), (key1236, 1), (key1236, 1), (key1243, 1), (key1243, 1), (key1247, 1), (key1247, 1), (key1009, -2), (key1022, -2), (key1022, -2), (key1044, -2), (key1080, -2), (key1080, -2), (key1130, -2), (key1130, -2), (key1159, -2), (key1159, -2), (key1174, -2), (key1174, -2)]

theorem rawRowCheck10149 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form9 = rawRow10149 := by decide +kernel

def row10149 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

theorem rowCheck10149 : row10149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10149 := by decide +kernel

theorem rowEval10149 (x : Key → ℝ) : Integer.Sparse.eval row10149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10149, Integer.Sparse.eval_collectBalanced, rawRowCheck10149]

def rawRow10150 : Integer.Sparse Key := [(key1017, 1), (key1022, 1), (key1003, 1), (key1022, 1), (key1003, 1), (key1017, 1), (key1073, 1), (key1080, 1), (key1038, 1), (key1080, 1), (key1038, 1), (key1073, 1), (key1152, 1), (key1174, 1), (key1125, 1), (key1174, 1), (key1125, 1), (key1152, 1), (key1243, 1), (key1247, 1), (key1236, 1), (key1247, 1), (key1236, 1), (key1243, 1), (key1022, -2), (key1009, -2), (key1022, -2), (key1080, -2), (key1044, -2), (key1080, -2), (key1159, -2), (key1174, -2), (key1130, -2), (key1174, -2), (key1130, -2), (key1159, -2)]

theorem rawRowCheck10150 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form9 = rawRow10150 := by decide +kernel

def row10150 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

theorem rowCheck10150 : row10150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10150 := by decide +kernel

theorem rowEval10150 (x : Key → ℝ) : Integer.Sparse.eval row10150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10150, Integer.Sparse.eval_collectBalanced, rawRowCheck10150]

def rawRow10151 : Integer.Sparse Key := [(key1022, 1), (key1017, 1), (key1022, 1), (key1003, 1), (key1017, 1), (key1003, 1), (key1080, 1), (key1073, 1), (key1080, 1), (key1038, 1), (key1073, 1), (key1038, 1), (key1174, 1), (key1152, 1), (key1174, 1), (key1125, 1), (key1152, 1), (key1125, 1), (key1247, 1), (key1243, 1), (key1247, 1), (key1236, 1), (key1243, 1), (key1236, 1), (key1022, -2), (key1022, -2), (key1009, -2), (key1080, -2), (key1080, -2), (key1044, -2), (key1174, -2), (key1159, -2), (key1174, -2), (key1130, -2), (key1159, -2), (key1130, -2)]

theorem rawRowCheck10151 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form9 = rawRow10151 := by decide +kernel

def row10151 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

theorem rowCheck10151 : row10151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10151 := by decide +kernel

theorem rowEval10151 (x : Key → ℝ) : Integer.Sparse.eval row10151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10151, Integer.Sparse.eval_collectBalanced, rawRowCheck10151]

def rawRow10152 : Integer.Sparse Key := [(key1038, 1), (key1038, 1), (key1125, 1), (key1125, 1), (key1236, 1), (key1236, 1), (key1003, 1), (key1003, 1), (key1152, 1), (key1152, 1), (key1243, 1), (key1243, 1), (key1017, 1), (key1017, 1), (key1073, 1), (key1073, 1), (key1247, 1), (key1247, 1), (key1022, 1), (key1022, 1), (key1080, 1), (key1080, 1), (key1174, 1), (key1174, 1), (key1044, -2), (key1130, -2), (key1130, -2), (key1009, -2), (key1159, -2), (key1159, -2), (key1022, -2), (key1022, -2), (key1080, -2), (key1080, -2), (key1174, -2), (key1174, -2)]

theorem rawRowCheck10152 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form9 = rawRow10152 := by decide +kernel

def row10152 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

theorem rowCheck10152 : row10152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10152 := by decide +kernel

theorem rowEval10152 (x : Key → ℝ) : Integer.Sparse.eval row10152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10152, Integer.Sparse.eval_collectBalanced, rawRowCheck10152]

def rawRow10153 : Integer.Sparse Key := [(key1125, 1), (key1236, 1), (key1038, 1), (key1236, 1), (key1038, 1), (key1125, 1), (key1152, 1), (key1243, 1), (key1003, 1), (key1243, 1), (key1003, 1), (key1152, 1), (key1073, 1), (key1247, 1), (key1017, 1), (key1247, 1), (key1017, 1), (key1073, 1), (key1080, 1), (key1174, 1), (key1022, 1), (key1174, 1), (key1022, 1), (key1080, 1), (key1130, -2), (key1044, -2), (key1130, -2), (key1159, -2), (key1009, -2), (key1159, -2), (key1080, -2), (key1174, -2), (key1022, -2), (key1174, -2), (key1022, -2), (key1080, -2)]

theorem rawRowCheck10153 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form9 = rawRow10153 := by decide +kernel

def row10153 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

theorem rowCheck10153 : row10153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10153 := by decide +kernel

theorem rowEval10153 (x : Key → ℝ) : Integer.Sparse.eval row10153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10153, Integer.Sparse.eval_collectBalanced, rawRowCheck10153]

def rawRow10154 : Integer.Sparse Key := [(key1236, 1), (key1125, 1), (key1236, 1), (key1038, 1), (key1125, 1), (key1038, 1), (key1243, 1), (key1152, 1), (key1243, 1), (key1003, 1), (key1152, 1), (key1003, 1), (key1247, 1), (key1073, 1), (key1247, 1), (key1017, 1), (key1073, 1), (key1017, 1), (key1174, 1), (key1080, 1), (key1174, 1), (key1022, 1), (key1080, 1), (key1022, 1), (key1130, -2), (key1130, -2), (key1044, -2), (key1159, -2), (key1159, -2), (key1009, -2), (key1174, -2), (key1080, -2), (key1174, -2), (key1022, -2), (key1080, -2), (key1022, -2)]

theorem rawRowCheck10154 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form9 = rawRow10154 := by decide +kernel

def row10154 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

theorem rowCheck10154 : row10154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10154 := by decide +kernel

theorem rowEval10154 (x : Key → ℝ) : Integer.Sparse.eval row10154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck10154, Integer.Sparse.eval_collectBalanced, rawRowCheck10154]

def rawRow10155 : Integer.Sparse Key := [(key1073, 1), (key1080, 1), (key1152, 1), (key1174, 1), (key1243, 1), (key1247, 1), (key1017, 1), (key1022, 1), (key1125, 1), (key1174, 1), (key1236, 1), (key1247, 1), (key1003, 1), (key1022, 1), (key1038, 1), (key1080, 1), (key1236, 1), (key1243, 1), (key1003, 1), (key1017, 1), (key1038, 1), (key1073, 1), (key1125, 1), (key1152, 1), (key1080, -2), (key1159, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1174, -2), (key1009, -2), (key1022, -2), (key1044, -2), (key1080, -2), (key1130, -2), (key1159, -2)]

theorem rawRowCheck10155 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form9 = rawRow10155 := by decide +kernel

def row10155 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

theorem rowCheck10155 : row10155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10155 := by decide +kernel

theorem rowEval10155 (x : Key → ℝ) : Integer.Sparse.eval row10155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10155, Integer.Sparse.eval_collectBalanced, rawRowCheck10155]

def rawRow10156 : Integer.Sparse Key := [(key1080, 1), (key1073, 1), (key1174, 1), (key1152, 1), (key1247, 1), (key1243, 1), (key1022, 1), (key1017, 1), (key1174, 1), (key1125, 1), (key1247, 1), (key1236, 1), (key1022, 1), (key1003, 1), (key1080, 1), (key1038, 1), (key1243, 1), (key1236, 1), (key1017, 1), (key1003, 1), (key1073, 1), (key1038, 1), (key1152, 1), (key1125, 1), (key1080, -2), (key1174, -2), (key1159, -2), (key1022, -2), (key1174, -2), (key1130, -2), (key1022, -2), (key1009, -2), (key1080, -2), (key1044, -2), (key1159, -2), (key1130, -2)]

theorem rawRowCheck10156 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form9 = rawRow10156 := by decide +kernel

def row10156 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

theorem rowCheck10156 : row10156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10156 := by decide +kernel

theorem rowEval10156 (x : Key → ℝ) : Integer.Sparse.eval row10156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10156, Integer.Sparse.eval_collectBalanced, rawRowCheck10156]

def rawRow10157 : Integer.Sparse Key := [(key1152, 1), (key1243, 1), (key1073, 1), (key1247, 1), (key1080, 1), (key1174, 1), (key1125, 1), (key1236, 1), (key1017, 1), (key1247, 1), (key1022, 1), (key1174, 1), (key1038, 1), (key1236, 1), (key1003, 1), (key1243, 1), (key1022, 1), (key1080, 1), (key1038, 1), (key1125, 1), (key1003, 1), (key1152, 1), (key1017, 1), (key1073, 1), (key1159, -2), (key1080, -2), (key1174, -2), (key1130, -2), (key1022, -2), (key1174, -2), (key1044, -2), (key1130, -2), (key1009, -2), (key1159, -2), (key1022, -2), (key1080, -2)]

theorem rawRowCheck10157 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form9 = rawRow10157 := by decide +kernel

def row10157 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

theorem rowCheck10157 : row10157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10157 := by decide +kernel

theorem rowEval10157 (x : Key → ℝ) : Integer.Sparse.eval row10157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10157, Integer.Sparse.eval_collectBalanced, rawRowCheck10157]

def rawRow10158 : Integer.Sparse Key := [(key1243, 1), (key1152, 1), (key1247, 1), (key1073, 1), (key1174, 1), (key1080, 1), (key1236, 1), (key1125, 1), (key1247, 1), (key1017, 1), (key1174, 1), (key1022, 1), (key1236, 1), (key1038, 1), (key1243, 1), (key1003, 1), (key1080, 1), (key1022, 1), (key1125, 1), (key1038, 1), (key1152, 1), (key1003, 1), (key1073, 1), (key1017, 1), (key1159, -2), (key1174, -2), (key1080, -2), (key1130, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1044, -2), (key1159, -2), (key1009, -2), (key1080, -2), (key1022, -2)]

theorem rawRowCheck10158 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form9 = rawRow10158 := by decide +kernel

def row10158 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

theorem rowCheck10158 : row10158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10158 := by decide +kernel

theorem rowEval10158 (x : Key → ℝ) : Integer.Sparse.eval row10158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck10158, Integer.Sparse.eval_collectBalanced, rawRowCheck10158]

def rawRow10159 : Integer.Sparse Key := [(key1174, 1), (key1247, 1), (key1080, 1), (key1243, 1), (key1073, 1), (key1152, 1), (key1174, 1), (key1247, 1), (key1022, 1), (key1236, 1), (key1017, 1), (key1125, 1), (key1080, 1), (key1243, 1), (key1022, 1), (key1236, 1), (key1003, 1), (key1038, 1), (key1073, 1), (key1152, 1), (key1017, 1), (key1125, 1), (key1003, 1), (key1038, 1), (key1174, -2), (key1080, -2), (key1159, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1080, -2), (key1159, -2), (key1022, -2), (key1130, -2), (key1009, -2), (key1044, -2)]

theorem rawRowCheck10159 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form9 = rawRow10159 := by decide +kernel

def row10159 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

theorem rowCheck10159 : row10159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10159 := by decide +kernel

theorem rowEval10159 (x : Key → ℝ) : Integer.Sparse.eval row10159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10159, Integer.Sparse.eval_collectBalanced, rawRowCheck10159]

def rawRow10160 : Integer.Sparse Key := [(key1247, 1), (key1174, 1), (key1243, 1), (key1080, 1), (key1152, 1), (key1073, 1), (key1247, 1), (key1174, 1), (key1236, 1), (key1022, 1), (key1125, 1), (key1017, 1), (key1243, 1), (key1080, 1), (key1236, 1), (key1022, 1), (key1038, 1), (key1003, 1), (key1152, 1), (key1073, 1), (key1125, 1), (key1017, 1), (key1038, 1), (key1003, 1), (key1174, -2), (key1159, -2), (key1080, -2), (key1174, -2), (key1130, -2), (key1022, -2), (key1159, -2), (key1080, -2), (key1130, -2), (key1022, -2), (key1044, -2), (key1009, -2)]

theorem rawRowCheck10160 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form9 = rawRow10160 := by decide +kernel

def row10160 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

theorem rowCheck10160 : row10160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10160 := by decide +kernel

theorem rowEval10160 (x : Key → ℝ) : Integer.Sparse.eval row10160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck10160, Integer.Sparse.eval_collectBalanced, rawRowCheck10160]

def rawRow10161 : Integer.Sparse Key := [(key1003, 1), (key1009, 1), (key1003, 1), (key1022, 1), (key1009, 1), (key1022, 1), (key1038, 1), (key1044, 1), (key1038, 1), (key1080, 1), (key1044, 1), (key1080, 1), (key1116, 1), (key1130, 1), (key1116, 1), (key1159, 1), (key1130, 1), (key1159, 1), (key1233, 1), (key1236, 1), (key1233, 1), (key1243, 1), (key1236, 1), (key1243, 1), (key1003, -2), (key1003, -2), (key1017, -2), (key1038, -2), (key1038, -2), (key1073, -2), (key1116, -2), (key1125, -2), (key1116, -2), (key1152, -2), (key1125, -2), (key1152, -2)]

theorem rawRowCheck10161 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form9 = rawRow10161 := by decide +kernel

def row10161 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

theorem rowCheck10161 : row10161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10161 := by decide +kernel

theorem rowEval10161 (x : Key → ℝ) : Integer.Sparse.eval row10161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10161, Integer.Sparse.eval_collectBalanced, rawRowCheck10161]

def rawRow10162 : Integer.Sparse Key := [(key1009, 1), (key1003, 1), (key1022, 1), (key1003, 1), (key1022, 1), (key1009, 1), (key1044, 1), (key1038, 1), (key1080, 1), (key1038, 1), (key1080, 1), (key1044, 1), (key1130, 1), (key1116, 1), (key1159, 1), (key1116, 1), (key1159, 1), (key1130, 1), (key1236, 1), (key1233, 1), (key1243, 1), (key1233, 1), (key1243, 1), (key1236, 1), (key1003, -2), (key1017, -2), (key1003, -2), (key1038, -2), (key1073, -2), (key1038, -2), (key1125, -2), (key1116, -2), (key1152, -2), (key1116, -2), (key1152, -2), (key1125, -2)]

theorem rawRowCheck10162 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form9 = rawRow10162 := by decide +kernel

def row10162 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

theorem rowCheck10162 : row10162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10162 := by decide +kernel

theorem rowEval10162 (x : Key → ℝ) : Integer.Sparse.eval row10162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10162, Integer.Sparse.eval_collectBalanced, rawRowCheck10162]

def rawRow10163 : Integer.Sparse Key := [(key1022, 1), (key1022, 1), (key1009, 1), (key1009, 1), (key1003, 1), (key1003, 1), (key1080, 1), (key1080, 1), (key1044, 1), (key1044, 1), (key1038, 1), (key1038, 1), (key1159, 1), (key1159, 1), (key1130, 1), (key1130, 1), (key1116, 1), (key1116, 1), (key1243, 1), (key1243, 1), (key1236, 1), (key1236, 1), (key1233, 1), (key1233, 1), (key1017, -2), (key1003, -2), (key1003, -2), (key1073, -2), (key1038, -2), (key1038, -2), (key1152, -2), (key1152, -2), (key1125, -2), (key1125, -2), (key1116, -2), (key1116, -2)]

theorem rawRowCheck10163 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form9 = rawRow10163 := by decide +kernel

def row10163 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

theorem rowCheck10163 : row10163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10163 := by decide +kernel

theorem rowEval10163 (x : Key → ℝ) : Integer.Sparse.eval row10163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10163, Integer.Sparse.eval_collectBalanced, rawRowCheck10163]

def rawRow10164 : Integer.Sparse Key := [(key1038, 1), (key1044, 1), (key1116, 1), (key1130, 1), (key1233, 1), (key1236, 1), (key1003, 1), (key1009, 1), (key1116, 1), (key1159, 1), (key1233, 1), (key1243, 1), (key1003, 1), (key1022, 1), (key1038, 1), (key1080, 1), (key1236, 1), (key1243, 1), (key1009, 1), (key1022, 1), (key1044, 1), (key1080, 1), (key1130, 1), (key1159, 1), (key1038, -2), (key1116, -2), (key1125, -2), (key1003, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1017, -2), (key1038, -2), (key1073, -2), (key1125, -2), (key1152, -2)]

theorem rawRowCheck10164 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form9 = rawRow10164 := by decide +kernel

def row10164 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

theorem rowCheck10164 : row10164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10164 := by decide +kernel

theorem rowEval10164 (x : Key → ℝ) : Integer.Sparse.eval row10164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10164, Integer.Sparse.eval_collectBalanced, rawRowCheck10164]

def rawRow10165 : Integer.Sparse Key := [(key1044, 1), (key1038, 1), (key1130, 1), (key1116, 1), (key1236, 1), (key1233, 1), (key1009, 1), (key1003, 1), (key1159, 1), (key1116, 1), (key1243, 1), (key1233, 1), (key1022, 1), (key1003, 1), (key1080, 1), (key1038, 1), (key1243, 1), (key1236, 1), (key1022, 1), (key1009, 1), (key1080, 1), (key1044, 1), (key1159, 1), (key1130, 1), (key1038, -2), (key1125, -2), (key1116, -2), (key1003, -2), (key1152, -2), (key1116, -2), (key1017, -2), (key1003, -2), (key1073, -2), (key1038, -2), (key1152, -2), (key1125, -2)]

theorem rawRowCheck10165 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form9 = rawRow10165 := by decide +kernel

def row10165 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

theorem rowCheck10165 : row10165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10165 := by decide +kernel

theorem rowEval10165 (x : Key → ℝ) : Integer.Sparse.eval row10165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10165, Integer.Sparse.eval_collectBalanced, rawRowCheck10165]

def rawRow10166 : Integer.Sparse Key := [(key1116, 1), (key1233, 1), (key1038, 1), (key1236, 1), (key1044, 1), (key1130, 1), (key1116, 1), (key1233, 1), (key1003, 1), (key1243, 1), (key1009, 1), (key1159, 1), (key1038, 1), (key1236, 1), (key1003, 1), (key1243, 1), (key1022, 1), (key1080, 1), (key1044, 1), (key1130, 1), (key1009, 1), (key1159, 1), (key1022, 1), (key1080, 1), (key1116, -2), (key1038, -2), (key1125, -2), (key1116, -2), (key1003, -2), (key1152, -2), (key1038, -2), (key1125, -2), (key1003, -2), (key1152, -2), (key1017, -2), (key1073, -2)]

theorem rawRowCheck10166 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form9 = rawRow10166 := by decide +kernel

def row10166 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

theorem rowCheck10166 : row10166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10166 := by decide +kernel

theorem rowEval10166 (x : Key → ℝ) : Integer.Sparse.eval row10166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10166, Integer.Sparse.eval_collectBalanced, rawRowCheck10166]

def rawRow10167 : Integer.Sparse Key := [(key1233, 1), (key1116, 1), (key1236, 1), (key1038, 1), (key1130, 1), (key1044, 1), (key1233, 1), (key1116, 1), (key1243, 1), (key1003, 1), (key1159, 1), (key1009, 1), (key1236, 1), (key1038, 1), (key1243, 1), (key1003, 1), (key1080, 1), (key1022, 1), (key1130, 1), (key1044, 1), (key1159, 1), (key1009, 1), (key1080, 1), (key1022, 1), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1125, -2), (key1038, -2), (key1152, -2), (key1003, -2), (key1073, -2), (key1017, -2)]

theorem rawRowCheck10167 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form9 = rawRow10167 := by decide +kernel

def row10167 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

theorem rowCheck10167 : row10167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10167 := by decide +kernel

theorem rowEval10167 (x : Key → ℝ) : Integer.Sparse.eval row10167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck10167, Integer.Sparse.eval_collectBalanced, rawRowCheck10167]

def rawRow10168 : Integer.Sparse Key := [(key1130, 1), (key1236, 1), (key1044, 1), (key1233, 1), (key1038, 1), (key1116, 1), (key1159, 1), (key1243, 1), (key1009, 1), (key1233, 1), (key1003, 1), (key1116, 1), (key1080, 1), (key1243, 1), (key1022, 1), (key1236, 1), (key1003, 1), (key1038, 1), (key1080, 1), (key1159, 1), (key1022, 1), (key1130, 1), (key1009, 1), (key1044, 1), (key1125, -2), (key1038, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1073, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1003, -2), (key1038, -2)]

theorem rawRowCheck10168 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form9 = rawRow10168 := by decide +kernel

def row10168 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

theorem rowCheck10168 : row10168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10168 := by decide +kernel

theorem rowEval10168 (x : Key → ℝ) : Integer.Sparse.eval row10168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10168, Integer.Sparse.eval_collectBalanced, rawRowCheck10168]

def rawRow10169 : Integer.Sparse Key := [(key1236, 1), (key1130, 1), (key1233, 1), (key1044, 1), (key1116, 1), (key1038, 1), (key1243, 1), (key1159, 1), (key1233, 1), (key1009, 1), (key1116, 1), (key1003, 1), (key1243, 1), (key1080, 1), (key1236, 1), (key1022, 1), (key1038, 1), (key1003, 1), (key1159, 1), (key1080, 1), (key1130, 1), (key1022, 1), (key1044, 1), (key1009, 1), (key1125, -2), (key1116, -2), (key1038, -2), (key1152, -2), (key1116, -2), (key1003, -2), (key1152, -2), (key1073, -2), (key1125, -2), (key1017, -2), (key1038, -2), (key1003, -2)]

theorem rawRowCheck10169 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form9 = rawRow10169 := by decide +kernel

def row10169 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

theorem rowCheck10169 : row10169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10169 := by decide +kernel

theorem rowEval10169 (x : Key → ℝ) : Integer.Sparse.eval row10169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck10169, Integer.Sparse.eval_collectBalanced, rawRowCheck10169]

def rawRow10170 : Integer.Sparse Key := [(key1080, 1), (key1080, 1), (key1159, 1), (key1159, 1), (key1243, 1), (key1243, 1), (key1022, 1), (key1022, 1), (key1130, 1), (key1130, 1), (key1236, 1), (key1236, 1), (key1009, 1), (key1009, 1), (key1044, 1), (key1044, 1), (key1233, 1), (key1233, 1), (key1003, 1), (key1003, 1), (key1038, 1), (key1038, 1), (key1116, 1), (key1116, 1), (key1073, -2), (key1152, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1125, -2), (key1003, -2), (key1003, -2), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2)]

theorem rawRowCheck10170 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form9 = rawRow10170 := by decide +kernel

def row10170 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

theorem rowCheck10170 : row10170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10170 := by decide +kernel

theorem rowEval10170 (x : Key → ℝ) : Integer.Sparse.eval row10170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10170, Integer.Sparse.eval_collectBalanced, rawRowCheck10170]

def rawRow10171 : Integer.Sparse Key := [(key1159, 1), (key1243, 1), (key1080, 1), (key1243, 1), (key1080, 1), (key1159, 1), (key1130, 1), (key1236, 1), (key1022, 1), (key1236, 1), (key1022, 1), (key1130, 1), (key1044, 1), (key1233, 1), (key1009, 1), (key1233, 1), (key1009, 1), (key1044, 1), (key1038, 1), (key1116, 1), (key1003, 1), (key1116, 1), (key1003, 1), (key1038, 1), (key1152, -2), (key1073, -2), (key1152, -2), (key1125, -2), (key1017, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1003, -2), (key1116, -2), (key1003, -2), (key1038, -2)]

theorem rawRowCheck10171 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form9 = rawRow10171 := by decide +kernel

def row10171 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

theorem rowCheck10171 : row10171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10171 := by decide +kernel

theorem rowEval10171 (x : Key → ℝ) : Integer.Sparse.eval row10171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10171, Integer.Sparse.eval_collectBalanced, rawRowCheck10171]

def rawRow10172 : Integer.Sparse Key := [(key1243, 1), (key1159, 1), (key1243, 1), (key1080, 1), (key1159, 1), (key1080, 1), (key1236, 1), (key1130, 1), (key1236, 1), (key1022, 1), (key1130, 1), (key1022, 1), (key1233, 1), (key1044, 1), (key1233, 1), (key1009, 1), (key1044, 1), (key1009, 1), (key1116, 1), (key1038, 1), (key1116, 1), (key1003, 1), (key1038, 1), (key1003, 1), (key1152, -2), (key1152, -2), (key1073, -2), (key1125, -2), (key1125, -2), (key1017, -2), (key1116, -2), (key1038, -2), (key1116, -2), (key1003, -2), (key1038, -2), (key1003, -2)]

theorem rawRowCheck10172 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form9 = rawRow10172 := by decide +kernel

def row10172 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

theorem rowCheck10172 : row10172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10172 := by decide +kernel

theorem rowEval10172 (x : Key → ℝ) : Integer.Sparse.eval row10172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck10172, Integer.Sparse.eval_collectBalanced, rawRowCheck10172]

def rawRow10173 : Integer.Sparse Key := [(key24, -6), (key106, -6), (key138, -6), (key138, -6), (key24, 2), (key36, 2), (key36, 2), (key49, 2), (key75, 2), (key75, 2), (key116, 2), (key116, 2), (key138, 2), (key138, 2), (key154, 2), (key154, 2)]

theorem rawRowCheck10173 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form10 = rawRow10173 := by decide +kernel

def row10173 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

theorem rowCheck10173 : row10173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10173 := by decide +kernel

theorem rowEval10173 (x : Key → ℝ) : Integer.Sparse.eval row10173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10173, Integer.Sparse.eval_collectBalanced, rawRowCheck10173]

def rawRow10174 : Integer.Sparse Key := [(key24, -6), (key138, -6), (key106, -6), (key138, -6), (key36, 2), (key24, 2), (key36, 2), (key75, 2), (key49, 2), (key75, 2), (key138, 2), (key154, 2), (key116, 2), (key154, 2), (key116, 2), (key138, 2)]

theorem rawRowCheck10174 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form10 = rawRow10174 := by decide +kernel

def row10174 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

theorem rowCheck10174 : row10174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10174 := by decide +kernel

theorem rowEval10174 (x : Key → ℝ) : Integer.Sparse.eval row10174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10174, Integer.Sparse.eval_collectBalanced, rawRowCheck10174]

def rawRow10175 : Integer.Sparse Key := [(key24, -6), (key138, -6), (key138, -6), (key106, -6), (key36, 2), (key36, 2), (key24, 2), (key75, 2), (key75, 2), (key49, 2), (key154, 2), (key138, 2), (key154, 2), (key116, 2), (key138, 2), (key116, 2)]

theorem rawRowCheck10175 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form10 = rawRow10175 := by decide +kernel

def row10175 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

theorem rowCheck10175 : row10175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10175 := by decide +kernel

theorem rowEval10175 (x : Key → ℝ) : Integer.Sparse.eval row10175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10175, Integer.Sparse.eval_collectBalanced, rawRowCheck10175]

def rawRow10176 : Integer.Sparse Key := [(key106, -6), (key24, -6), (key138, -6), (key138, -6), (key49, 2), (key116, 2), (key116, 2), (key24, 2), (key138, 2), (key138, 2), (key36, 2), (key36, 2), (key75, 2), (key75, 2), (key154, 2), (key154, 2)]

theorem rawRowCheck10176 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form10 = rawRow10176 := by decide +kernel

def row10176 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

theorem rowCheck10176 : row10176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10176 := by decide +kernel

theorem rowEval10176 (x : Key → ℝ) : Integer.Sparse.eval row10176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10176, Integer.Sparse.eval_collectBalanced, rawRowCheck10176]

def rawRow10177 : Integer.Sparse Key := [(key106, -6), (key138, -6), (key24, -6), (key138, -6), (key116, 2), (key49, 2), (key116, 2), (key138, 2), (key24, 2), (key138, 2), (key75, 2), (key154, 2), (key36, 2), (key154, 2), (key36, 2), (key75, 2)]

theorem rawRowCheck10177 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form10 = rawRow10177 := by decide +kernel

def row10177 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

theorem rowCheck10177 : row10177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10177 := by decide +kernel

theorem rowEval10177 (x : Key → ℝ) : Integer.Sparse.eval row10177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10177, Integer.Sparse.eval_collectBalanced, rawRowCheck10177]

def rawRow10178 : Integer.Sparse Key := [(key106, -6), (key138, -6), (key138, -6), (key24, -6), (key116, 2), (key116, 2), (key49, 2), (key138, 2), (key138, 2), (key24, 2), (key154, 2), (key75, 2), (key154, 2), (key36, 2), (key75, 2), (key36, 2)]

theorem rawRowCheck10178 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form10 = rawRow10178 := by decide +kernel

def row10178 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

theorem rowCheck10178 : row10178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10178 := by decide +kernel

theorem rowEval10178 (x : Key → ℝ) : Integer.Sparse.eval row10178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck10178, Integer.Sparse.eval_collectBalanced, rawRowCheck10178]

def rawRow10179 : Integer.Sparse Key := [(key138, -6), (key24, -6), (key106, -6), (key138, -6), (key75, 2), (key138, 2), (key154, 2), (key36, 2), (key116, 2), (key154, 2), (key24, 2), (key36, 2), (key49, 2), (key75, 2), (key116, 2), (key138, 2)]

theorem rawRowCheck10179 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form10 = rawRow10179 := by decide +kernel

def row10179 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

theorem rowCheck10179 : row10179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10179 := by decide +kernel

theorem rowEval10179 (x : Key → ℝ) : Integer.Sparse.eval row10179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10179, Integer.Sparse.eval_collectBalanced, rawRowCheck10179]

def rawRow10180 : Integer.Sparse Key := [(key138, -6), (key24, -6), (key138, -6), (key106, -6), (key75, 2), (key154, 2), (key138, 2), (key36, 2), (key154, 2), (key116, 2), (key36, 2), (key24, 2), (key75, 2), (key49, 2), (key138, 2), (key116, 2)]

theorem rawRowCheck10180 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form10 = rawRow10180 := by decide +kernel

def row10180 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

theorem rowCheck10180 : row10180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10180 := by decide +kernel

theorem rowEval10180 (x : Key → ℝ) : Integer.Sparse.eval row10180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10180, Integer.Sparse.eval_collectBalanced, rawRowCheck10180]

def rawRow10181 : Integer.Sparse Key := [(key138, -6), (key106, -6), (key24, -6), (key138, -6), (key138, 2), (key75, 2), (key154, 2), (key116, 2), (key36, 2), (key154, 2), (key49, 2), (key116, 2), (key24, 2), (key138, 2), (key36, 2), (key75, 2)]

theorem rawRowCheck10181 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form10 = rawRow10181 := by decide +kernel

def row10181 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

theorem rowCheck10181 : row10181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10181 := by decide +kernel

theorem rowEval10181 (x : Key → ℝ) : Integer.Sparse.eval row10181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10181, Integer.Sparse.eval_collectBalanced, rawRowCheck10181]

def rawRow10182 : Integer.Sparse Key := [(key138, -6), (key106, -6), (key138, -6), (key24, -6), (key138, 2), (key154, 2), (key75, 2), (key116, 2), (key154, 2), (key36, 2), (key116, 2), (key49, 2), (key138, 2), (key24, 2), (key75, 2), (key36, 2)]

theorem rawRowCheck10182 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form10 = rawRow10182 := by decide +kernel

def row10182 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

theorem rowCheck10182 : row10182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10182 := by decide +kernel

theorem rowEval10182 (x : Key → ℝ) : Integer.Sparse.eval row10182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck10182, Integer.Sparse.eval_collectBalanced, rawRowCheck10182]

def rawRow10183 : Integer.Sparse Key := [(key138, -6), (key138, -6), (key24, -6), (key106, -6), (key154, 2), (key75, 2), (key138, 2), (key154, 2), (key36, 2), (key116, 2), (key75, 2), (key138, 2), (key36, 2), (key116, 2), (key24, 2), (key49, 2)]

theorem rawRowCheck10183 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form10 = rawRow10183 := by decide +kernel

def row10183 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

theorem rowCheck10183 : row10183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10183 := by decide +kernel

theorem rowEval10183 (x : Key → ℝ) : Integer.Sparse.eval row10183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10183, Integer.Sparse.eval_collectBalanced, rawRowCheck10183]

def rawRow10184 : Integer.Sparse Key := [(key138, -6), (key138, -6), (key106, -6), (key24, -6), (key154, 2), (key138, 2), (key75, 2), (key154, 2), (key116, 2), (key36, 2), (key138, 2), (key75, 2), (key116, 2), (key36, 2), (key49, 2), (key24, 2)]

theorem rawRowCheck10184 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form10 = rawRow10184 := by decide +kernel

def row10184 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

theorem rowCheck10184 : row10184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10184 := by decide +kernel

theorem rowEval10184 (x : Key → ℝ) : Integer.Sparse.eval row10184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck10184, Integer.Sparse.eval_collectBalanced, rawRowCheck10184]

def rawRow10185 : Integer.Sparse Key := [(key36, -6), (key116, -6), (key116, -6), (key154, -6), (key24, 2), (key24, 2), (key36, 2), (key49, 2), (key49, 2), (key75, 2), (key106, 2), (key116, 2), (key106, 2), (key138, 2), (key116, 2), (key138, 2)]

theorem rawRowCheck10185 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form10 = rawRow10185 := by decide +kernel

def row10185 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

theorem rowCheck10185 : row10185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10185 := by decide +kernel

theorem rowEval10185 (x : Key → ℝ) : Integer.Sparse.eval row10185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10185, Integer.Sparse.eval_collectBalanced, rawRowCheck10185]

def rawRow10186 : Integer.Sparse Key := [(key36, -6), (key116, -6), (key154, -6), (key116, -6), (key24, 2), (key36, 2), (key24, 2), (key49, 2), (key75, 2), (key49, 2), (key116, 2), (key106, 2), (key138, 2), (key106, 2), (key138, 2), (key116, 2)]

theorem rawRowCheck10186 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form10 = rawRow10186 := by decide +kernel

def row10186 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

theorem rowCheck10186 : row10186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10186 := by decide +kernel

theorem rowEval10186 (x : Key → ℝ) : Integer.Sparse.eval row10186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10186, Integer.Sparse.eval_collectBalanced, rawRowCheck10186]

def rawRow10187 : Integer.Sparse Key := [(key36, -6), (key154, -6), (key116, -6), (key116, -6), (key36, 2), (key24, 2), (key24, 2), (key75, 2), (key49, 2), (key49, 2), (key138, 2), (key138, 2), (key116, 2), (key116, 2), (key106, 2), (key106, 2)]

theorem rawRowCheck10187 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form10 = rawRow10187 := by decide +kernel

def row10187 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

theorem rowCheck10187 : row10187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10187 := by decide +kernel

theorem rowEval10187 (x : Key → ℝ) : Integer.Sparse.eval row10187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10187, Integer.Sparse.eval_collectBalanced, rawRowCheck10187]

def rawRow10188 : Integer.Sparse Key := [(key116, -6), (key36, -6), (key116, -6), (key154, -6), (key49, 2), (key106, 2), (key116, 2), (key24, 2), (key106, 2), (key138, 2), (key24, 2), (key36, 2), (key49, 2), (key75, 2), (key116, 2), (key138, 2)]

theorem rawRowCheck10188 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form10 = rawRow10188 := by decide +kernel

def row10188 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

theorem rowCheck10188 : row10188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10188 := by decide +kernel

theorem rowEval10188 (x : Key → ℝ) : Integer.Sparse.eval row10188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10188, Integer.Sparse.eval_collectBalanced, rawRowCheck10188]

def rawRow10189 : Integer.Sparse Key := [(key116, -6), (key36, -6), (key154, -6), (key116, -6), (key49, 2), (key116, 2), (key106, 2), (key24, 2), (key138, 2), (key106, 2), (key36, 2), (key24, 2), (key75, 2), (key49, 2), (key138, 2), (key116, 2)]

theorem rawRowCheck10189 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form10 = rawRow10189 := by decide +kernel

def row10189 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

theorem rowCheck10189 : row10189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10189 := by decide +kernel

theorem rowEval10189 (x : Key → ℝ) : Integer.Sparse.eval row10189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10189, Integer.Sparse.eval_collectBalanced, rawRowCheck10189]

def rawRow10190 : Integer.Sparse Key := [(key116, -6), (key116, -6), (key36, -6), (key154, -6), (key106, 2), (key49, 2), (key116, 2), (key106, 2), (key24, 2), (key138, 2), (key49, 2), (key116, 2), (key24, 2), (key138, 2), (key36, 2), (key75, 2)]

theorem rawRowCheck10190 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form10 = rawRow10190 := by decide +kernel

def row10190 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

theorem rowCheck10190 : row10190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10190 := by decide +kernel

theorem rowEval10190 (x : Key → ℝ) : Integer.Sparse.eval row10190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10190, Integer.Sparse.eval_collectBalanced, rawRowCheck10190]

def rawRow10191 : Integer.Sparse Key := [(key116, -6), (key116, -6), (key154, -6), (key36, -6), (key106, 2), (key116, 2), (key49, 2), (key106, 2), (key138, 2), (key24, 2), (key116, 2), (key49, 2), (key138, 2), (key24, 2), (key75, 2), (key36, 2)]

theorem rawRowCheck10191 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form10 = rawRow10191 := by decide +kernel

def row10191 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

theorem rowCheck10191 : row10191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10191 := by decide +kernel

theorem rowEval10191 (x : Key → ℝ) : Integer.Sparse.eval row10191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck10191, Integer.Sparse.eval_collectBalanced, rawRowCheck10191]

def rawRow10192 : Integer.Sparse Key := [(key116, -6), (key154, -6), (key36, -6), (key116, -6), (key116, 2), (key49, 2), (key106, 2), (key138, 2), (key24, 2), (key106, 2), (key75, 2), (key138, 2), (key36, 2), (key116, 2), (key24, 2), (key49, 2)]

theorem rawRowCheck10192 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form10 = rawRow10192 := by decide +kernel

def row10192 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

theorem rowCheck10192 : row10192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10192 := by decide +kernel

theorem rowEval10192 (x : Key → ℝ) : Integer.Sparse.eval row10192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10192, Integer.Sparse.eval_collectBalanced, rawRowCheck10192]

def rawRow10193 : Integer.Sparse Key := [(key116, -6), (key154, -6), (key116, -6), (key36, -6), (key116, 2), (key106, 2), (key49, 2), (key138, 2), (key106, 2), (key24, 2), (key138, 2), (key75, 2), (key116, 2), (key36, 2), (key49, 2), (key24, 2)]

theorem rawRowCheck10193 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form10 = rawRow10193 := by decide +kernel

def row10193 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

theorem rowCheck10193 : row10193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10193 := by decide +kernel

theorem rowEval10193 (x : Key → ℝ) : Integer.Sparse.eval row10193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck10193, Integer.Sparse.eval_collectBalanced, rawRowCheck10193]

def rawRow10194 : Integer.Sparse Key := [(key154, -6), (key36, -6), (key116, -6), (key116, -6), (key75, 2), (key138, 2), (key138, 2), (key36, 2), (key116, 2), (key116, 2), (key24, 2), (key24, 2), (key49, 2), (key49, 2), (key106, 2), (key106, 2)]

theorem rawRowCheck10194 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form10 = rawRow10194 := by decide +kernel

def row10194 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

theorem rowCheck10194 : row10194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10194 := by decide +kernel

theorem rowEval10194 (x : Key → ℝ) : Integer.Sparse.eval row10194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10194, Integer.Sparse.eval_collectBalanced, rawRowCheck10194]

def rawRow10195 : Integer.Sparse Key := [(key154, -6), (key116, -6), (key36, -6), (key116, -6), (key138, 2), (key75, 2), (key138, 2), (key116, 2), (key36, 2), (key116, 2), (key49, 2), (key106, 2), (key24, 2), (key106, 2), (key24, 2), (key49, 2)]

theorem rawRowCheck10195 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form10 = rawRow10195 := by decide +kernel

def row10195 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

theorem rowCheck10195 : row10195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10195 := by decide +kernel

theorem rowEval10195 (x : Key → ℝ) : Integer.Sparse.eval row10195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10195, Integer.Sparse.eval_collectBalanced, rawRowCheck10195]

def rawRow10196 : Integer.Sparse Key := [(key154, -6), (key116, -6), (key116, -6), (key36, -6), (key138, 2), (key138, 2), (key75, 2), (key116, 2), (key116, 2), (key36, 2), (key106, 2), (key49, 2), (key106, 2), (key24, 2), (key49, 2), (key24, 2)]

theorem rawRowCheck10196 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form10 = rawRow10196 := by decide +kernel

def row10196 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

theorem rowCheck10196 : row10196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10196 := by decide +kernel

theorem rowEval10196 (x : Key → ℝ) : Integer.Sparse.eval row10196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck10196, Integer.Sparse.eval_collectBalanced, rawRowCheck10196]

def rawRow10197 : Integer.Sparse Key := [(key1095, 6), (key1095, 6), (key1099, 6), (key1184, 6), (key985, -6), (key1099, -6), (key1170, -6), (key1170, -6)]

theorem rawRowCheck10197 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form11 = rawRow10197 := by decide +kernel

def row10197 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

theorem rowCheck10197 : row10197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10197 := by decide +kernel

theorem rowEval10197 (x : Key → ℝ) : Integer.Sparse.eval row10197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10197, Integer.Sparse.eval_collectBalanced, rawRowCheck10197]

def rawRow10198 : Integer.Sparse Key := [(key1095, 6), (key1099, 6), (key1095, 6), (key1184, 6), (key985, -6), (key1170, -6), (key1099, -6), (key1170, -6)]

theorem rawRowCheck10198 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form11 = rawRow10198 := by decide +kernel

def row10198 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

theorem rowCheck10198 : row10198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10198 := by decide +kernel

theorem rowEval10198 (x : Key → ℝ) : Integer.Sparse.eval row10198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10198, Integer.Sparse.eval_collectBalanced, rawRowCheck10198]

def rawRow10199 : Integer.Sparse Key := [(key1099, 6), (key1095, 6), (key1095, 6), (key1184, 6), (key985, -6), (key1170, -6), (key1170, -6), (key1099, -6)]

theorem rawRowCheck10199 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form11 = rawRow10199 := by decide +kernel

def row10199 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

theorem rowCheck10199 : row10199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10199 := by decide +kernel

theorem rowEval10199 (x : Key → ℝ) : Integer.Sparse.eval row10199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10199, Integer.Sparse.eval_collectBalanced, rawRowCheck10199]

def rawRow10200 : Integer.Sparse Key := [(key1095, 6), (key1095, 6), (key1184, 6), (key1099, 6), (key1099, -6), (key985, -6), (key1170, -6), (key1170, -6)]

theorem rawRowCheck10200 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form11 = rawRow10200 := by decide +kernel

def row10200 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

theorem rowCheck10200 : row10200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10200 := by decide +kernel

theorem rowEval10200 (x : Key → ℝ) : Integer.Sparse.eval row10200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10200, Integer.Sparse.eval_collectBalanced, rawRowCheck10200]

def rawRow10201 : Integer.Sparse Key := [(key1095, 6), (key1184, 6), (key1095, 6), (key1099, 6), (key1099, -6), (key1170, -6), (key985, -6), (key1170, -6)]

theorem rawRowCheck10201 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form11 = rawRow10201 := by decide +kernel

def row10201 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

theorem rowCheck10201 : row10201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10201 := by decide +kernel

theorem rowEval10201 (x : Key → ℝ) : Integer.Sparse.eval row10201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10201, Integer.Sparse.eval_collectBalanced, rawRowCheck10201]

def rawRow10202 : Integer.Sparse Key := [(key1184, 6), (key1095, 6), (key1095, 6), (key1099, 6), (key1099, -6), (key1170, -6), (key1170, -6), (key985, -6)]

theorem rawRowCheck10202 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form11 = rawRow10202 := by decide +kernel

def row10202 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

theorem rowCheck10202 : row10202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10202 := by decide +kernel

theorem rowEval10202 (x : Key → ℝ) : Integer.Sparse.eval row10202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck10202, Integer.Sparse.eval_collectBalanced, rawRowCheck10202]

def rawRow10203 : Integer.Sparse Key := [(key1095, 6), (key1099, 6), (key1184, 6), (key1095, 6), (key1170, -6), (key985, -6), (key1099, -6), (key1170, -6)]

theorem rawRowCheck10203 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form11 = rawRow10203 := by decide +kernel

def row10203 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

theorem rowCheck10203 : row10203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10203 := by decide +kernel

theorem rowEval10203 (x : Key → ℝ) : Integer.Sparse.eval row10203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10203, Integer.Sparse.eval_collectBalanced, rawRowCheck10203]

def rawRow10204 : Integer.Sparse Key := [(key1099, 6), (key1095, 6), (key1184, 6), (key1095, 6), (key1170, -6), (key985, -6), (key1170, -6), (key1099, -6)]

theorem rawRowCheck10204 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form11 = rawRow10204 := by decide +kernel

def row10204 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

theorem rowCheck10204 : row10204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10204 := by decide +kernel

theorem rowEval10204 (x : Key → ℝ) : Integer.Sparse.eval row10204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10204, Integer.Sparse.eval_collectBalanced, rawRowCheck10204]

def rawRow10205 : Integer.Sparse Key := [(key1095, 6), (key1184, 6), (key1099, 6), (key1095, 6), (key1170, -6), (key1099, -6), (key985, -6), (key1170, -6)]

theorem rawRowCheck10205 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form11 = rawRow10205 := by decide +kernel

def row10205 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

theorem rowCheck10205 : row10205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10205 := by decide +kernel

theorem rowEval10205 (x : Key → ℝ) : Integer.Sparse.eval row10205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10205, Integer.Sparse.eval_collectBalanced, rawRowCheck10205]

def rawRow10206 : Integer.Sparse Key := [(key1184, 6), (key1095, 6), (key1099, 6), (key1095, 6), (key1170, -6), (key1099, -6), (key1170, -6), (key985, -6)]

theorem rawRowCheck10206 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form11 = rawRow10206 := by decide +kernel

def row10206 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

theorem rowCheck10206 : row10206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10206 := by decide +kernel

theorem rowEval10206 (x : Key → ℝ) : Integer.Sparse.eval row10206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck10206, Integer.Sparse.eval_collectBalanced, rawRowCheck10206]

def rawRow10207 : Integer.Sparse Key := [(key1099, 6), (key1184, 6), (key1095, 6), (key1095, 6), (key1170, -6), (key1170, -6), (key985, -6), (key1099, -6)]

theorem rawRowCheck10207 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form11 = rawRow10207 := by decide +kernel

def row10207 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

theorem rowCheck10207 : row10207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10207 := by decide +kernel

theorem rowEval10207 (x : Key → ℝ) : Integer.Sparse.eval row10207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10207, Integer.Sparse.eval_collectBalanced, rawRowCheck10207]

def rawRow10208 : Integer.Sparse Key := [(key1184, 6), (key1099, 6), (key1095, 6), (key1095, 6), (key1170, -6), (key1170, -6), (key1099, -6), (key985, -6)]

theorem rawRowCheck10208 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form11 = rawRow10208 := by decide +kernel

def row10208 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

theorem rowCheck10208 : row10208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10208 := by decide +kernel

theorem rowEval10208 (x : Key → ℝ) : Integer.Sparse.eval row10208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck10208, Integer.Sparse.eval_collectBalanced, rawRowCheck10208]

def rawRow10209 : Integer.Sparse Key := [(key1166, 6), (key1170, 6), (key1170, 6), (key1221, 6), (key981, -6), (key1095, -6), (key1095, -6), (key1166, -6)]

theorem rawRowCheck10209 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form11 = rawRow10209 := by decide +kernel

def row10209 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

theorem rowCheck10209 : row10209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10209 := by decide +kernel

theorem rowEval10209 (x : Key → ℝ) : Integer.Sparse.eval row10209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10209, Integer.Sparse.eval_collectBalanced, rawRowCheck10209]

def rawRow10210 : Integer.Sparse Key := [(key1170, 6), (key1166, 6), (key1170, 6), (key1221, 6), (key981, -6), (key1095, -6), (key1166, -6), (key1095, -6)]

theorem rawRowCheck10210 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form11 = rawRow10210 := by decide +kernel

def row10210 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

theorem rowCheck10210 : row10210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10210 := by decide +kernel

theorem rowEval10210 (x : Key → ℝ) : Integer.Sparse.eval row10210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10210, Integer.Sparse.eval_collectBalanced, rawRowCheck10210]

def rawRow10211 : Integer.Sparse Key := [(key1170, 6), (key1170, 6), (key1166, 6), (key1221, 6), (key981, -6), (key1166, -6), (key1095, -6), (key1095, -6)]

theorem rawRowCheck10211 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form11 = rawRow10211 := by decide +kernel

def row10211 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

theorem rowCheck10211 : row10211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10211 := by decide +kernel

theorem rowEval10211 (x : Key → ℝ) : Integer.Sparse.eval row10211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10211, Integer.Sparse.eval_collectBalanced, rawRowCheck10211]

def rawRow10212 : Integer.Sparse Key := [(key1166, 6), (key1170, 6), (key1221, 6), (key1170, 6), (key1095, -6), (key981, -6), (key1095, -6), (key1166, -6)]

theorem rawRowCheck10212 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form11 = rawRow10212 := by decide +kernel

def row10212 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

theorem rowCheck10212 : row10212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10212 := by decide +kernel

theorem rowEval10212 (x : Key → ℝ) : Integer.Sparse.eval row10212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10212, Integer.Sparse.eval_collectBalanced, rawRowCheck10212]

def rawRow10213 : Integer.Sparse Key := [(key1170, 6), (key1166, 6), (key1221, 6), (key1170, 6), (key1095, -6), (key981, -6), (key1166, -6), (key1095, -6)]

theorem rawRowCheck10213 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form11 = rawRow10213 := by decide +kernel

def row10213 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

theorem rowCheck10213 : row10213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10213 := by decide +kernel

theorem rowEval10213 (x : Key → ℝ) : Integer.Sparse.eval row10213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10213, Integer.Sparse.eval_collectBalanced, rawRowCheck10213]

def rawRow10214 : Integer.Sparse Key := [(key1166, 6), (key1221, 6), (key1170, 6), (key1170, 6), (key1095, -6), (key1095, -6), (key981, -6), (key1166, -6)]

theorem rawRowCheck10214 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form11 = rawRow10214 := by decide +kernel

def row10214 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

theorem rowCheck10214 : row10214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10214 := by decide +kernel

theorem rowEval10214 (x : Key → ℝ) : Integer.Sparse.eval row10214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10214, Integer.Sparse.eval_collectBalanced, rawRowCheck10214]

def rawRow10215 : Integer.Sparse Key := [(key1221, 6), (key1166, 6), (key1170, 6), (key1170, 6), (key1095, -6), (key1095, -6), (key1166, -6), (key981, -6)]

theorem rawRowCheck10215 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form11 = rawRow10215 := by decide +kernel

def row10215 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

theorem rowCheck10215 : row10215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10215 := by decide +kernel

theorem rowEval10215 (x : Key → ℝ) : Integer.Sparse.eval row10215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck10215, Integer.Sparse.eval_collectBalanced, rawRowCheck10215]

def rawRow10216 : Integer.Sparse Key := [(key1170, 6), (key1221, 6), (key1166, 6), (key1170, 6), (key1095, -6), (key1166, -6), (key981, -6), (key1095, -6)]

theorem rawRowCheck10216 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form11 = rawRow10216 := by decide +kernel

def row10216 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

theorem rowCheck10216 : row10216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10216 := by decide +kernel

theorem rowEval10216 (x : Key → ℝ) : Integer.Sparse.eval row10216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10216, Integer.Sparse.eval_collectBalanced, rawRowCheck10216]

def rawRow10217 : Integer.Sparse Key := [(key1221, 6), (key1170, 6), (key1166, 6), (key1170, 6), (key1095, -6), (key1166, -6), (key1095, -6), (key981, -6)]

theorem rawRowCheck10217 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form11 = rawRow10217 := by decide +kernel

def row10217 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

theorem rowCheck10217 : row10217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10217 := by decide +kernel

theorem rowEval10217 (x : Key → ℝ) : Integer.Sparse.eval row10217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck10217, Integer.Sparse.eval_collectBalanced, rawRowCheck10217]

def rawRow10218 : Integer.Sparse Key := [(key1170, 6), (key1170, 6), (key1221, 6), (key1166, 6), (key1166, -6), (key981, -6), (key1095, -6), (key1095, -6)]

theorem rawRowCheck10218 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form11 = rawRow10218 := by decide +kernel

def row10218 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

theorem rowCheck10218 : row10218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10218 := by decide +kernel

theorem rowEval10218 (x : Key → ℝ) : Integer.Sparse.eval row10218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10218, Integer.Sparse.eval_collectBalanced, rawRowCheck10218]

def rawRow10219 : Integer.Sparse Key := [(key1170, 6), (key1221, 6), (key1170, 6), (key1166, 6), (key1166, -6), (key1095, -6), (key981, -6), (key1095, -6)]

theorem rawRowCheck10219 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form11 = rawRow10219 := by decide +kernel

def row10219 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

theorem rowCheck10219 : row10219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10219 := by decide +kernel

theorem rowEval10219 (x : Key → ℝ) : Integer.Sparse.eval row10219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10219, Integer.Sparse.eval_collectBalanced, rawRowCheck10219]

def rawRow10220 : Integer.Sparse Key := [(key1221, 6), (key1170, 6), (key1170, 6), (key1166, 6), (key1166, -6), (key1095, -6), (key1095, -6), (key981, -6)]

theorem rawRowCheck10220 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form11 = rawRow10220 := by decide +kernel

def row10220 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

theorem rowCheck10220 : row10220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10220 := by decide +kernel

theorem rowEval10220 (x : Key → ℝ) : Integer.Sparse.eval row10220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck10220, Integer.Sparse.eval_collectBalanced, rawRowCheck10220]

def rawRow10221 : Integer.Sparse Key := [(key1095, 6), (key1095, 6), (key1101, 6), (key1229, 6), (key987, -6), (key1101, -6), (key1173, -6), (key1173, -6)]

theorem rawRowCheck10221 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form12 = rawRow10221 := by decide +kernel

def row10221 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

theorem rowCheck10221 : row10221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10221 := by decide +kernel

theorem rowEval10221 (x : Key → ℝ) : Integer.Sparse.eval row10221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10221, Integer.Sparse.eval_collectBalanced, rawRowCheck10221]

def rawRow10222 : Integer.Sparse Key := [(key1095, 6), (key1101, 6), (key1095, 6), (key1229, 6), (key987, -6), (key1173, -6), (key1101, -6), (key1173, -6)]

theorem rawRowCheck10222 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form12 = rawRow10222 := by decide +kernel

def row10222 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

theorem rowCheck10222 : row10222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10222 := by decide +kernel

theorem rowEval10222 (x : Key → ℝ) : Integer.Sparse.eval row10222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10222, Integer.Sparse.eval_collectBalanced, rawRowCheck10222]

def rawRow10223 : Integer.Sparse Key := [(key1101, 6), (key1095, 6), (key1095, 6), (key1229, 6), (key987, -6), (key1173, -6), (key1173, -6), (key1101, -6)]

theorem rawRowCheck10223 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form12 = rawRow10223 := by decide +kernel

def row10223 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

theorem rowCheck10223 : row10223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10223 := by decide +kernel

theorem rowEval10223 (x : Key → ℝ) : Integer.Sparse.eval row10223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10223, Integer.Sparse.eval_collectBalanced, rawRowCheck10223]

def rawRow10224 : Integer.Sparse Key := [(key1095, 6), (key1095, 6), (key1229, 6), (key1101, 6), (key1101, -6), (key987, -6), (key1173, -6), (key1173, -6)]

theorem rawRowCheck10224 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form12 = rawRow10224 := by decide +kernel

def row10224 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

theorem rowCheck10224 : row10224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10224 := by decide +kernel

theorem rowEval10224 (x : Key → ℝ) : Integer.Sparse.eval row10224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10224, Integer.Sparse.eval_collectBalanced, rawRowCheck10224]

def rawRow10225 : Integer.Sparse Key := [(key1095, 6), (key1229, 6), (key1095, 6), (key1101, 6), (key1101, -6), (key1173, -6), (key987, -6), (key1173, -6)]

theorem rawRowCheck10225 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form12 = rawRow10225 := by decide +kernel

def row10225 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

theorem rowCheck10225 : row10225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10225 := by decide +kernel

theorem rowEval10225 (x : Key → ℝ) : Integer.Sparse.eval row10225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10225, Integer.Sparse.eval_collectBalanced, rawRowCheck10225]

def rawRow10226 : Integer.Sparse Key := [(key1229, 6), (key1095, 6), (key1095, 6), (key1101, 6), (key1101, -6), (key1173, -6), (key1173, -6), (key987, -6)]

theorem rawRowCheck10226 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form12 = rawRow10226 := by decide +kernel

def row10226 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

theorem rowCheck10226 : row10226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10226 := by decide +kernel

theorem rowEval10226 (x : Key → ℝ) : Integer.Sparse.eval row10226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck10226, Integer.Sparse.eval_collectBalanced, rawRowCheck10226]

def rawRow10227 : Integer.Sparse Key := [(key1095, 6), (key1101, 6), (key1229, 6), (key1095, 6), (key1173, -6), (key987, -6), (key1101, -6), (key1173, -6)]

theorem rawRowCheck10227 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form12 = rawRow10227 := by decide +kernel

def row10227 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

theorem rowCheck10227 : row10227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10227 := by decide +kernel

theorem rowEval10227 (x : Key → ℝ) : Integer.Sparse.eval row10227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10227, Integer.Sparse.eval_collectBalanced, rawRowCheck10227]

def rawRow10228 : Integer.Sparse Key := [(key1101, 6), (key1095, 6), (key1229, 6), (key1095, 6), (key1173, -6), (key987, -6), (key1173, -6), (key1101, -6)]

theorem rawRowCheck10228 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form12 = rawRow10228 := by decide +kernel

def row10228 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

theorem rowCheck10228 : row10228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10228 := by decide +kernel

theorem rowEval10228 (x : Key → ℝ) : Integer.Sparse.eval row10228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10228, Integer.Sparse.eval_collectBalanced, rawRowCheck10228]

def rawRow10229 : Integer.Sparse Key := [(key1095, 6), (key1229, 6), (key1101, 6), (key1095, 6), (key1173, -6), (key1101, -6), (key987, -6), (key1173, -6)]

theorem rawRowCheck10229 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form12 = rawRow10229 := by decide +kernel

def row10229 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

theorem rowCheck10229 : row10229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10229 := by decide +kernel

theorem rowEval10229 (x : Key → ℝ) : Integer.Sparse.eval row10229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10229, Integer.Sparse.eval_collectBalanced, rawRowCheck10229]

def rawRow10230 : Integer.Sparse Key := [(key1229, 6), (key1095, 6), (key1101, 6), (key1095, 6), (key1173, -6), (key1101, -6), (key1173, -6), (key987, -6)]

theorem rawRowCheck10230 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form12 = rawRow10230 := by decide +kernel

def row10230 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

theorem rowCheck10230 : row10230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10230 := by decide +kernel

theorem rowEval10230 (x : Key → ℝ) : Integer.Sparse.eval row10230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck10230, Integer.Sparse.eval_collectBalanced, rawRowCheck10230]

def rawRow10231 : Integer.Sparse Key := [(key1101, 6), (key1229, 6), (key1095, 6), (key1095, 6), (key1173, -6), (key1173, -6), (key987, -6), (key1101, -6)]

theorem rawRowCheck10231 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form12 = rawRow10231 := by decide +kernel

def row10231 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

theorem rowCheck10231 : row10231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10231 := by decide +kernel

theorem rowEval10231 (x : Key → ℝ) : Integer.Sparse.eval row10231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10231, Integer.Sparse.eval_collectBalanced, rawRowCheck10231]

def rawRow10232 : Integer.Sparse Key := [(key1229, 6), (key1101, 6), (key1095, 6), (key1095, 6), (key1173, -6), (key1173, -6), (key1101, -6), (key987, -6)]

theorem rawRowCheck10232 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form12 = rawRow10232 := by decide +kernel

def row10232 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

theorem rowCheck10232 : row10232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10232 := by decide +kernel

theorem rowEval10232 (x : Key → ℝ) : Integer.Sparse.eval row10232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck10232, Integer.Sparse.eval_collectBalanced, rawRowCheck10232]

def rawRow10233 : Integer.Sparse Key := [(key1166, 6), (key1173, 6), (key1173, 6), (key1246, 6), (key981, -6), (key1095, -6), (key1095, -6), (key1166, -6)]

theorem rawRowCheck10233 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form12 = rawRow10233 := by decide +kernel

def row10233 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

theorem rowCheck10233 : row10233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10233 := by decide +kernel

theorem rowEval10233 (x : Key → ℝ) : Integer.Sparse.eval row10233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10233, Integer.Sparse.eval_collectBalanced, rawRowCheck10233]

def rawRow10234 : Integer.Sparse Key := [(key1173, 6), (key1166, 6), (key1173, 6), (key1246, 6), (key981, -6), (key1095, -6), (key1166, -6), (key1095, -6)]

theorem rawRowCheck10234 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form12 = rawRow10234 := by decide +kernel

def row10234 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

theorem rowCheck10234 : row10234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10234 := by decide +kernel

theorem rowEval10234 (x : Key → ℝ) : Integer.Sparse.eval row10234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10234, Integer.Sparse.eval_collectBalanced, rawRowCheck10234]

def rawRow10235 : Integer.Sparse Key := [(key1173, 6), (key1173, 6), (key1166, 6), (key1246, 6), (key981, -6), (key1166, -6), (key1095, -6), (key1095, -6)]

theorem rawRowCheck10235 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form12 = rawRow10235 := by decide +kernel

def row10235 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

theorem rowCheck10235 : row10235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10235 := by decide +kernel

theorem rowEval10235 (x : Key → ℝ) : Integer.Sparse.eval row10235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10235, Integer.Sparse.eval_collectBalanced, rawRowCheck10235]

def rawRow10236 : Integer.Sparse Key := [(key1166, 6), (key1173, 6), (key1246, 6), (key1173, 6), (key1095, -6), (key981, -6), (key1095, -6), (key1166, -6)]

theorem rawRowCheck10236 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form12 = rawRow10236 := by decide +kernel

def row10236 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

theorem rowCheck10236 : row10236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10236 := by decide +kernel

theorem rowEval10236 (x : Key → ℝ) : Integer.Sparse.eval row10236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10236, Integer.Sparse.eval_collectBalanced, rawRowCheck10236]

def rawRow10237 : Integer.Sparse Key := [(key1173, 6), (key1166, 6), (key1246, 6), (key1173, 6), (key1095, -6), (key981, -6), (key1166, -6), (key1095, -6)]

theorem rawRowCheck10237 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form12 = rawRow10237 := by decide +kernel

def row10237 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

theorem rowCheck10237 : row10237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10237 := by decide +kernel

theorem rowEval10237 (x : Key → ℝ) : Integer.Sparse.eval row10237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10237, Integer.Sparse.eval_collectBalanced, rawRowCheck10237]

def rawRow10238 : Integer.Sparse Key := [(key1166, 6), (key1246, 6), (key1173, 6), (key1173, 6), (key1095, -6), (key1095, -6), (key981, -6), (key1166, -6)]

theorem rawRowCheck10238 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form12 = rawRow10238 := by decide +kernel

def row10238 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

theorem rowCheck10238 : row10238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10238 := by decide +kernel

theorem rowEval10238 (x : Key → ℝ) : Integer.Sparse.eval row10238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10238, Integer.Sparse.eval_collectBalanced, rawRowCheck10238]

def rawRow10239 : Integer.Sparse Key := [(key1246, 6), (key1166, 6), (key1173, 6), (key1173, 6), (key1095, -6), (key1095, -6), (key1166, -6), (key981, -6)]

theorem rawRowCheck10239 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form12 = rawRow10239 := by decide +kernel

def row10239 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

theorem rowCheck10239 : row10239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10239 := by decide +kernel

theorem rowEval10239 (x : Key → ℝ) : Integer.Sparse.eval row10239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck10239, Integer.Sparse.eval_collectBalanced, rawRowCheck10239]

end MUB6.Certificate.GramRows

end OAI
