import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow13440 : Integer.Sparse Key := [(key1227, -2), (key1092, -2), (key1092, -2), (key1086, 6), (key1244, -2), (key1163, -2), (key1163, -2), (key1227, 2), (key1092, 2), (key1227, 2), (key978, 2), (key1092, 2), (key978, 2), (key1086, -2), (key1086, -2), (key972, -2), (key1163, 6), (key1092, -2), (key1092, -2), (key978, -2)]

theorem rawRowCheck13440 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13440 := by decide +kernel

def row13440 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck13440 : row13440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13440 := by decide +kernel

theorem rowEval13440 (x : Key → ℝ) : Integer.Sparse.eval row13440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13440, Integer.Sparse.eval_collectBalanced, rawRowCheck13440]

def rawRow13441 : Integer.Sparse Key := [(key1163, -2), (key1163, -2), (key1163, -2), (key1244, 6), (key978, -2), (key978, -2), (key978, -2), (key1092, 2), (key1092, 2), (key1092, 2), (key1092, 2), (key1092, 2), (key1092, 2), (key1227, -2), (key1227, -2), (key1227, -2), (key972, 6), (key1086, -2), (key1086, -2), (key1086, -2)]

theorem rawRowCheck13441 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13441 := by decide +kernel

def row13441 : Integer.Sparse Key := [(key972, 6), (key978, -6), (key1086, -6), (key1092, 12), (key1163, -6), (key1227, -6), (key1244, 6)]

theorem rowCheck13441 : row13441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13441 := by decide +kernel

theorem rowEval13441 (x : Key → ℝ) : Integer.Sparse.eval row13441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13441, Integer.Sparse.eval_collectBalanced, rawRowCheck13441]

def rawRow13442 : Integer.Sparse Key := [(key1163, -2), (key1163, -2), (key1244, -2), (key1163, 6), (key1092, -2), (key1092, -2), (key1227, -2), (key978, 2), (key978, 2), (key1092, 2), (key1092, 2), (key1227, 2), (key1227, 2), (key978, -2), (key1092, -2), (key1092, -2), (key1086, 6), (key972, -2), (key1086, -2), (key1086, -2)]

theorem rawRowCheck13442 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13442 := by decide +kernel

def row13442 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck13442 : row13442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13442 := by decide +kernel

theorem rowEval13442 (x : Key → ℝ) : Integer.Sparse.eval row13442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13442, Integer.Sparse.eval_collectBalanced, rawRowCheck13442]

def rawRow13443 : Integer.Sparse Key := [(key1163, -2), (key1244, -2), (key1163, -2), (key1163, 6), (key1092, -2), (key1227, -2), (key1092, -2), (key1092, 2), (key1227, 2), (key978, 2), (key1227, 2), (key978, 2), (key1092, 2), (key1092, -2), (key978, -2), (key1092, -2), (key1086, 6), (key1086, -2), (key972, -2), (key1086, -2)]

theorem rawRowCheck13443 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13443 := by decide +kernel

def row13443 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck13443 : row13443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13443 := by decide +kernel

theorem rowEval13443 (x : Key → ℝ) : Integer.Sparse.eval row13443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13443, Integer.Sparse.eval_collectBalanced, rawRowCheck13443]

def rawRow13444 : Integer.Sparse Key := [(key1244, -2), (key1163, -2), (key1163, -2), (key1163, 6), (key1227, -2), (key1092, -2), (key1092, -2), (key1227, 2), (key1092, 2), (key1227, 2), (key978, 2), (key1092, 2), (key978, 2), (key1092, -2), (key1092, -2), (key978, -2), (key1086, 6), (key1086, -2), (key1086, -2), (key972, -2)]

theorem rawRowCheck13444 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13444 := by decide +kernel

def row13444 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck13444 : row13444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13444 := by decide +kernel

theorem rowEval13444 (x : Key → ℝ) : Integer.Sparse.eval row13444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13444, Integer.Sparse.eval_collectBalanced, rawRowCheck13444]

def rawRow13445 : Integer.Sparse Key := [(key992, 6), (key992, -2), (key992, -2), (key1010, -2), (key1027, 6), (key1027, -2), (key1027, -2), (key1066, -2), (key1105, -2), (key1105, -2), (key1118, -2), (key1105, -2), (key1105, -2), (key1145, -2), (key1105, 2), (key1118, 2), (key1105, 2), (key1145, 2), (key1118, 2), (key1145, 2)]

theorem rawRowCheck13445 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form3 = rawRow13445 := by decide +kernel

def row13445 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

theorem rowCheck13445 : row13445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13445 := by decide +kernel

theorem rowEval13445 (x : Key → ℝ) : Integer.Sparse.eval row13445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13445, Integer.Sparse.eval_collectBalanced, rawRowCheck13445]

def rawRow13446 : Integer.Sparse Key := [(key992, 6), (key992, -2), (key1010, -2), (key992, -2), (key1027, 6), (key1027, -2), (key1066, -2), (key1027, -2), (key1105, -2), (key1118, -2), (key1105, -2), (key1105, -2), (key1145, -2), (key1105, -2), (key1118, 2), (key1105, 2), (key1145, 2), (key1105, 2), (key1145, 2), (key1118, 2)]

theorem rawRowCheck13446 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form3 = rawRow13446 := by decide +kernel

def row13446 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

theorem rowCheck13446 : row13446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13446 := by decide +kernel

theorem rowEval13446 (x : Key → ℝ) : Integer.Sparse.eval row13446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13446, Integer.Sparse.eval_collectBalanced, rawRowCheck13446]

def rawRow13447 : Integer.Sparse Key := [(key992, 6), (key1010, -2), (key992, -2), (key992, -2), (key1027, 6), (key1066, -2), (key1027, -2), (key1027, -2), (key1118, -2), (key1105, -2), (key1105, -2), (key1145, -2), (key1105, -2), (key1105, -2), (key1145, 2), (key1145, 2), (key1118, 2), (key1118, 2), (key1105, 2), (key1105, 2)]

theorem rawRowCheck13447 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form3 = rawRow13447 := by decide +kernel

def row13447 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

theorem rowCheck13447 : row13447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13447 := by decide +kernel

theorem rowEval13447 (x : Key → ℝ) : Integer.Sparse.eval row13447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13447, Integer.Sparse.eval_collectBalanced, rawRowCheck13447]

def rawRow13448 : Integer.Sparse Key := [(key1010, 6), (key992, -2), (key992, -2), (key992, -2), (key1066, 6), (key1027, -2), (key1027, -2), (key1027, -2), (key1145, -2), (key1145, -2), (key1145, -2), (key1118, -2), (key1118, -2), (key1118, -2), (key1105, 2), (key1105, 2), (key1105, 2), (key1105, 2), (key1105, 2), (key1105, 2)]

theorem rawRowCheck13448 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form3 = rawRow13448 := by decide +kernel

def row13448 : Integer.Sparse Key := [(key992, -6), (key1010, 6), (key1027, -6), (key1066, 6), (key1105, 12), (key1118, -6), (key1145, -6)]

theorem rowCheck13448 : row13448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13448 := by decide +kernel

theorem rowEval13448 (x : Key → ℝ) : Integer.Sparse.eval row13448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13448, Integer.Sparse.eval_collectBalanced, rawRowCheck13448]

def rawRow13449 : Integer.Sparse Key := [(key1027, 6), (key1105, -2), (key1105, -2), (key1118, -2), (key992, 6), (key1105, -2), (key1105, -2), (key1145, -2), (key992, -2), (key992, -2), (key1010, -2), (key1027, -2), (key1027, -2), (key1066, -2), (key1105, 2), (key1118, 2), (key1105, 2), (key1145, 2), (key1118, 2), (key1145, 2)]

theorem rawRowCheck13449 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form3 = rawRow13449 := by decide +kernel

def row13449 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

theorem rowCheck13449 : row13449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13449 := by decide +kernel

theorem rowEval13449 (x : Key → ℝ) : Integer.Sparse.eval row13449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13449, Integer.Sparse.eval_collectBalanced, rawRowCheck13449]

def rawRow13450 : Integer.Sparse Key := [(key1027, 6), (key1105, -2), (key1118, -2), (key1105, -2), (key992, 6), (key1105, -2), (key1145, -2), (key1105, -2), (key992, -2), (key1010, -2), (key992, -2), (key1027, -2), (key1066, -2), (key1027, -2), (key1118, 2), (key1105, 2), (key1145, 2), (key1105, 2), (key1145, 2), (key1118, 2)]

theorem rawRowCheck13450 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form3 = rawRow13450 := by decide +kernel

def row13450 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

theorem rowCheck13450 : row13450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13450 := by decide +kernel

theorem rowEval13450 (x : Key → ℝ) : Integer.Sparse.eval row13450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13450, Integer.Sparse.eval_collectBalanced, rawRowCheck13450]

def rawRow13451 : Integer.Sparse Key := [(key1027, 6), (key1118, -2), (key1105, -2), (key1105, -2), (key992, 6), (key1145, -2), (key1105, -2), (key1105, -2), (key1010, -2), (key992, -2), (key992, -2), (key1066, -2), (key1027, -2), (key1027, -2), (key1145, 2), (key1145, 2), (key1118, 2), (key1118, 2), (key1105, 2), (key1105, 2)]

theorem rawRowCheck13451 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form3 = rawRow13451 := by decide +kernel

def row13451 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

theorem rowCheck13451 : row13451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13451 := by decide +kernel

theorem rowEval13451 (x : Key → ℝ) : Integer.Sparse.eval row13451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13451, Integer.Sparse.eval_collectBalanced, rawRowCheck13451]

def rawRow13452 : Integer.Sparse Key := [(key1105, 6), (key1027, -2), (key1105, -2), (key1118, -2), (key1105, 6), (key992, -2), (key1105, -2), (key1145, -2), (key1027, -2), (key1105, -2), (key1118, -2), (key992, -2), (key1105, -2), (key1145, -2), (key992, 2), (key1010, 2), (key1027, 2), (key1066, 2), (key1118, 2), (key1145, 2)]

theorem rawRowCheck13452 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form3 = rawRow13452 := by decide +kernel

def row13452 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, -2), (key1066, 2), (key1105, 4), (key1118, -2), (key1145, -2)]

theorem rowCheck13452 : row13452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13452 := by decide +kernel

theorem rowEval13452 (x : Key → ℝ) : Integer.Sparse.eval row13452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13452, Integer.Sparse.eval_collectBalanced, rawRowCheck13452]

def rawRow13453 : Integer.Sparse Key := [(key1105, 6), (key1027, -2), (key1118, -2), (key1105, -2), (key1105, 6), (key992, -2), (key1145, -2), (key1105, -2), (key1027, -2), (key1118, -2), (key1105, -2), (key992, -2), (key1145, -2), (key1105, -2), (key1010, 2), (key992, 2), (key1066, 2), (key1027, 2), (key1145, 2), (key1118, 2)]

theorem rawRowCheck13453 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form3 = rawRow13453 := by decide +kernel

def row13453 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, -2), (key1066, 2), (key1105, 4), (key1118, -2), (key1145, -2)]

theorem rowCheck13453 : row13453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13453 := by decide +kernel

theorem rowEval13453 (x : Key → ℝ) : Integer.Sparse.eval row13453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13453, Integer.Sparse.eval_collectBalanced, rawRowCheck13453]

def rawRow13454 : Integer.Sparse Key := [(key1105, 6), (key1105, -2), (key1027, -2), (key1118, -2), (key1105, 6), (key1105, -2), (key992, -2), (key1145, -2), (key1105, -2), (key1027, -2), (key1118, -2), (key1105, -2), (key992, -2), (key1145, -2), (key1027, 2), (key1118, 2), (key992, 2), (key1145, 2), (key1010, 2), (key1066, 2)]

theorem rawRowCheck13454 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form3 = rawRow13454 := by decide +kernel

def row13454 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, -2), (key1066, 2), (key1105, 4), (key1118, -2), (key1145, -2)]

theorem rowCheck13454 : row13454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13454 := by decide +kernel

theorem rowEval13454 (x : Key → ℝ) : Integer.Sparse.eval row13454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13454, Integer.Sparse.eval_collectBalanced, rawRowCheck13454]

def rawRow13455 : Integer.Sparse Key := [(key1105, 6), (key1105, -2), (key1118, -2), (key1027, -2), (key1105, 6), (key1105, -2), (key1145, -2), (key992, -2), (key1105, -2), (key1118, -2), (key1027, -2), (key1105, -2), (key1145, -2), (key992, -2), (key1118, 2), (key1027, 2), (key1145, 2), (key992, 2), (key1066, 2), (key1010, 2)]

theorem rawRowCheck13455 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form3 = rawRow13455 := by decide +kernel

def row13455 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, -2), (key1066, 2), (key1105, 4), (key1118, -2), (key1145, -2)]

theorem rowCheck13455 : row13455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13455 := by decide +kernel

theorem rowEval13455 (x : Key → ℝ) : Integer.Sparse.eval row13455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13455, Integer.Sparse.eval_collectBalanced, rawRowCheck13455]

def rawRow13456 : Integer.Sparse Key := [(key1105, 6), (key1118, -2), (key1027, -2), (key1105, -2), (key1105, 6), (key1145, -2), (key992, -2), (key1105, -2), (key1118, -2), (key1027, -2), (key1105, -2), (key1145, -2), (key992, -2), (key1105, -2), (key1066, 2), (key1145, 2), (key1010, 2), (key1118, 2), (key992, 2), (key1027, 2)]

theorem rawRowCheck13456 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form3 = rawRow13456 := by decide +kernel

def row13456 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, -2), (key1066, 2), (key1105, 4), (key1118, -2), (key1145, -2)]

theorem rowCheck13456 : row13456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13456 := by decide +kernel

theorem rowEval13456 (x : Key → ℝ) : Integer.Sparse.eval row13456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13456, Integer.Sparse.eval_collectBalanced, rawRowCheck13456]

def rawRow13457 : Integer.Sparse Key := [(key1105, 6), (key1118, -2), (key1105, -2), (key1027, -2), (key1105, 6), (key1145, -2), (key1105, -2), (key992, -2), (key1118, -2), (key1105, -2), (key1027, -2), (key1145, -2), (key1105, -2), (key992, -2), (key1145, 2), (key1066, 2), (key1118, 2), (key1010, 2), (key1027, 2), (key992, 2)]

theorem rawRowCheck13457 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form3 = rawRow13457 := by decide +kernel

def row13457 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, -2), (key1066, 2), (key1105, 4), (key1118, -2), (key1145, -2)]

theorem rowCheck13457 : row13457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13457 := by decide +kernel

theorem rowEval13457 (x : Key → ℝ) : Integer.Sparse.eval row13457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13457, Integer.Sparse.eval_collectBalanced, rawRowCheck13457]

def rawRow13458 : Integer.Sparse Key := [(key1118, 6), (key1027, -2), (key1105, -2), (key1105, -2), (key1145, 6), (key992, -2), (key1105, -2), (key1105, -2), (key1066, -2), (key1145, -2), (key1145, -2), (key1010, -2), (key1118, -2), (key1118, -2), (key992, 2), (key992, 2), (key1027, 2), (key1027, 2), (key1105, 2), (key1105, 2)]

theorem rawRowCheck13458 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form3 = rawRow13458 := by decide +kernel

def row13458 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

theorem rowCheck13458 : row13458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13458 := by decide +kernel

theorem rowEval13458 (x : Key → ℝ) : Integer.Sparse.eval row13458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13458, Integer.Sparse.eval_collectBalanced, rawRowCheck13458]

def rawRow13459 : Integer.Sparse Key := [(key1118, 6), (key1105, -2), (key1027, -2), (key1105, -2), (key1145, 6), (key1105, -2), (key992, -2), (key1105, -2), (key1145, -2), (key1066, -2), (key1145, -2), (key1118, -2), (key1010, -2), (key1118, -2), (key1027, 2), (key1105, 2), (key992, 2), (key1105, 2), (key992, 2), (key1027, 2)]

theorem rawRowCheck13459 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form3 = rawRow13459 := by decide +kernel

def row13459 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

theorem rowCheck13459 : row13459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13459 := by decide +kernel

theorem rowEval13459 (x : Key → ℝ) : Integer.Sparse.eval row13459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13459, Integer.Sparse.eval_collectBalanced, rawRowCheck13459]

def rawRow13460 : Integer.Sparse Key := [(key1118, 6), (key1105, -2), (key1105, -2), (key1027, -2), (key1145, 6), (key1105, -2), (key1105, -2), (key992, -2), (key1145, -2), (key1145, -2), (key1066, -2), (key1118, -2), (key1118, -2), (key1010, -2), (key1105, 2), (key1027, 2), (key1105, 2), (key992, 2), (key1027, 2), (key992, 2)]

theorem rawRowCheck13460 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form3 = rawRow13460 := by decide +kernel

def row13460 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

theorem rowCheck13460 : row13460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13460 := by decide +kernel

theorem rowEval13460 (x : Key → ℝ) : Integer.Sparse.eval row13460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13460, Integer.Sparse.eval_collectBalanced, rawRowCheck13460]

def rawRow13461 : Integer.Sparse Key := [(key1066, 6), (key1145, -2), (key1145, -2), (key1145, -2), (key1010, 6), (key1118, -2), (key1118, -2), (key1118, -2), (key992, -2), (key992, -2), (key992, -2), (key1027, -2), (key1027, -2), (key1027, -2), (key1105, 2), (key1105, 2), (key1105, 2), (key1105, 2), (key1105, 2), (key1105, 2)]

theorem rawRowCheck13461 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form3 = rawRow13461 := by decide +kernel

def row13461 : Integer.Sparse Key := [(key992, -6), (key1010, 6), (key1027, -6), (key1066, 6), (key1105, 12), (key1118, -6), (key1145, -6)]

theorem rowCheck13461 : row13461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13461 := by decide +kernel

theorem rowEval13461 (x : Key → ℝ) : Integer.Sparse.eval row13461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13461, Integer.Sparse.eval_collectBalanced, rawRowCheck13461]

def rawRow13462 : Integer.Sparse Key := [(key1145, 6), (key1066, -2), (key1145, -2), (key1145, -2), (key1118, 6), (key1010, -2), (key1118, -2), (key1118, -2), (key1027, -2), (key1105, -2), (key1105, -2), (key992, -2), (key1105, -2), (key1105, -2), (key992, 2), (key992, 2), (key1027, 2), (key1027, 2), (key1105, 2), (key1105, 2)]

theorem rawRowCheck13462 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form3 = rawRow13462 := by decide +kernel

def row13462 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

theorem rowCheck13462 : row13462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13462 := by decide +kernel

theorem rowEval13462 (x : Key → ℝ) : Integer.Sparse.eval row13462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13462, Integer.Sparse.eval_collectBalanced, rawRowCheck13462]

def rawRow13463 : Integer.Sparse Key := [(key1145, 6), (key1145, -2), (key1066, -2), (key1145, -2), (key1118, 6), (key1118, -2), (key1010, -2), (key1118, -2), (key1105, -2), (key1027, -2), (key1105, -2), (key1105, -2), (key992, -2), (key1105, -2), (key1027, 2), (key1105, 2), (key992, 2), (key1105, 2), (key992, 2), (key1027, 2)]

theorem rawRowCheck13463 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form3 = rawRow13463 := by decide +kernel

def row13463 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

theorem rowCheck13463 : row13463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13463 := by decide +kernel

theorem rowEval13463 (x : Key → ℝ) : Integer.Sparse.eval row13463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13463, Integer.Sparse.eval_collectBalanced, rawRowCheck13463]

def rawRow13464 : Integer.Sparse Key := [(key1145, 6), (key1145, -2), (key1145, -2), (key1066, -2), (key1118, 6), (key1118, -2), (key1118, -2), (key1010, -2), (key1105, -2), (key1105, -2), (key1027, -2), (key1105, -2), (key1105, -2), (key992, -2), (key1105, 2), (key1027, 2), (key1105, 2), (key992, 2), (key1027, 2), (key992, 2)]

theorem rawRowCheck13464 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form3 = rawRow13464 := by decide +kernel

def row13464 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

theorem rowCheck13464 : row13464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13464 := by decide +kernel

theorem rowEval13464 (x : Key → ℝ) : Integer.Sparse.eval row13464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13464, Integer.Sparse.eval_collectBalanced, rawRowCheck13464]

def rawRow13465 : Integer.Sparse Key := [(key1, -2), (key4, -2), (key4, -2), (key4, 6), (key84, -2), (key87, -2), (key87, -2), (key84, 2), (key87, 2), (key84, 2), (key148, 2), (key87, 2), (key148, 2), (key87, -2), (key87, -2), (key148, -2), (key164, 6), (key164, -2), (key164, -2), (key184, -2)]

theorem rawRowCheck13465 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form4 = rawRow13465 := by decide +kernel

def row13465 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 2), (key164, 2), (key184, -2)]

theorem rowCheck13465 : row13465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13465 := by decide +kernel

theorem rowEval13465 (x : Key → ℝ) : Integer.Sparse.eval row13465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13465, Integer.Sparse.eval_collectBalanced, rawRowCheck13465]

def rawRow13466 : Integer.Sparse Key := [(key4, -2), (key1, -2), (key4, -2), (key4, 6), (key87, -2), (key84, -2), (key87, -2), (key87, 2), (key84, 2), (key148, 2), (key84, 2), (key148, 2), (key87, 2), (key87, -2), (key148, -2), (key87, -2), (key164, 6), (key164, -2), (key184, -2), (key164, -2)]

theorem rawRowCheck13466 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form4 = rawRow13466 := by decide +kernel

def row13466 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 2), (key164, 2), (key184, -2)]

theorem rowCheck13466 : row13466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13466 := by decide +kernel

theorem rowEval13466 (x : Key → ℝ) : Integer.Sparse.eval row13466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13466, Integer.Sparse.eval_collectBalanced, rawRowCheck13466]

def rawRow13467 : Integer.Sparse Key := [(key4, -2), (key4, -2), (key1, -2), (key4, 6), (key87, -2), (key87, -2), (key84, -2), (key148, 2), (key148, 2), (key87, 2), (key87, 2), (key84, 2), (key84, 2), (key148, -2), (key87, -2), (key87, -2), (key164, 6), (key184, -2), (key164, -2), (key164, -2)]

theorem rawRowCheck13467 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form4 = rawRow13467 := by decide +kernel

def row13467 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 2), (key164, 2), (key184, -2)]

theorem rowCheck13467 : row13467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13467 := by decide +kernel

theorem rowEval13467 (x : Key → ℝ) : Integer.Sparse.eval row13467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13467, Integer.Sparse.eval_collectBalanced, rawRowCheck13467]

def rawRow13468 : Integer.Sparse Key := [(key4, -2), (key4, -2), (key4, -2), (key1, 6), (key148, -2), (key148, -2), (key148, -2), (key87, 2), (key87, 2), (key87, 2), (key87, 2), (key87, 2), (key87, 2), (key84, -2), (key84, -2), (key84, -2), (key184, 6), (key164, -2), (key164, -2), (key164, -2)]

theorem rawRowCheck13468 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form4 = rawRow13468 := by decide +kernel

def row13468 : Integer.Sparse Key := [(key1, 6), (key4, -6), (key84, -6), (key87, 12), (key148, -6), (key164, -6), (key184, 6)]

theorem rowCheck13468 : row13468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13468 := by decide +kernel

theorem rowEval13468 (x : Key → ℝ) : Integer.Sparse.eval row13468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13468, Integer.Sparse.eval_collectBalanced, rawRowCheck13468]

def rawRow13469 : Integer.Sparse Key := [(key84, -2), (key87, -2), (key87, -2), (key148, 6), (key1, -2), (key4, -2), (key4, -2), (key84, 2), (key87, 2), (key84, 2), (key148, 2), (key87, 2), (key148, 2), (key164, -2), (key164, -2), (key184, -2), (key4, 6), (key87, -2), (key87, -2), (key148, -2)]

theorem rawRowCheck13469 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form4 = rawRow13469 := by decide +kernel

def row13469 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 8), (key164, -4), (key184, -2)]

theorem rowCheck13469 : row13469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13469 := by decide +kernel

theorem rowEval13469 (x : Key → ℝ) : Integer.Sparse.eval row13469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13469, Integer.Sparse.eval_collectBalanced, rawRowCheck13469]

def rawRow13470 : Integer.Sparse Key := [(key87, -2), (key84, -2), (key87, -2), (key148, 6), (key4, -2), (key1, -2), (key4, -2), (key87, 2), (key84, 2), (key148, 2), (key84, 2), (key148, 2), (key87, 2), (key164, -2), (key184, -2), (key164, -2), (key4, 6), (key87, -2), (key148, -2), (key87, -2)]

theorem rawRowCheck13470 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form4 = rawRow13470 := by decide +kernel

def row13470 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 8), (key164, -4), (key184, -2)]

theorem rowCheck13470 : row13470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13470 := by decide +kernel

theorem rowEval13470 (x : Key → ℝ) : Integer.Sparse.eval row13470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13470, Integer.Sparse.eval_collectBalanced, rawRowCheck13470]

def rawRow13471 : Integer.Sparse Key := [(key87, -2), (key87, -2), (key84, -2), (key148, 6), (key4, -2), (key4, -2), (key1, -2), (key148, 2), (key148, 2), (key87, 2), (key87, 2), (key84, 2), (key84, 2), (key184, -2), (key164, -2), (key164, -2), (key4, 6), (key148, -2), (key87, -2), (key87, -2)]

theorem rawRowCheck13471 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form4 = rawRow13471 := by decide +kernel

def row13471 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 8), (key164, -4), (key184, -2)]

theorem rowCheck13471 : row13471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13471 := by decide +kernel

theorem rowEval13471 (x : Key → ℝ) : Integer.Sparse.eval row13471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13471, Integer.Sparse.eval_collectBalanced, rawRowCheck13471]

def rawRow13472 : Integer.Sparse Key := [(key84, -2), (key87, -2), (key148, -2), (key87, 6), (key84, -2), (key87, -2), (key148, -2), (key1, 2), (key4, 2), (key84, 2), (key148, 2), (key164, 2), (key184, 2), (key4, -2), (key87, -2), (key148, -2), (key87, 6), (key4, -2), (key87, -2), (key148, -2)]

theorem rawRowCheck13472 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form4 = rawRow13472 := by decide +kernel

def row13472 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key87, 4), (key148, -6), (key164, 2), (key184, 2)]

theorem rowCheck13472 : row13472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13472 := by decide +kernel

theorem rowEval13472 (x : Key → ℝ) : Integer.Sparse.eval row13472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13472, Integer.Sparse.eval_collectBalanced, rawRowCheck13472]

def rawRow13473 : Integer.Sparse Key := [(key87, -2), (key84, -2), (key148, -2), (key87, 6), (key87, -2), (key84, -2), (key148, -2), (key4, 2), (key1, 2), (key148, 2), (key84, 2), (key184, 2), (key164, 2), (key4, -2), (key148, -2), (key87, -2), (key87, 6), (key4, -2), (key148, -2), (key87, -2)]

theorem rawRowCheck13473 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form4 = rawRow13473 := by decide +kernel

def row13473 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key87, 4), (key148, -6), (key164, 2), (key184, 2)]

theorem rowCheck13473 : row13473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13473 := by decide +kernel

theorem rowEval13473 (x : Key → ℝ) : Integer.Sparse.eval row13473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13473, Integer.Sparse.eval_collectBalanced, rawRowCheck13473]

def rawRow13474 : Integer.Sparse Key := [(key84, -2), (key148, -2), (key87, -2), (key87, 6), (key84, -2), (key148, -2), (key87, -2), (key84, 2), (key148, 2), (key1, 2), (key184, 2), (key4, 2), (key148, 2), (key87, -2), (key4, -2), (key148, -2), (key87, 6), (key87, -2), (key4, -2), (key148, -2)]

theorem rawRowCheck13474 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form4 = rawRow13474 := by decide +kernel

def row13474 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key87, 4), (key148, -4), (key184, 2)]

theorem rowCheck13474 : row13474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13474 := by decide +kernel

theorem rowEval13474 (x : Key → ℝ) : Integer.Sparse.eval row13474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13474, Integer.Sparse.eval_collectBalanced, rawRowCheck13474]

def rawRow13475 : Integer.Sparse Key := [(key148, -2), (key84, -2), (key87, -2), (key87, 6), (key148, -2), (key84, -2), (key87, -2), (key148, 2), (key84, 2), (key184, 2), (key1, 2), (key148, 2), (key4, 2), (key87, -2), (key148, -2), (key4, -2), (key87, 6), (key87, -2), (key148, -2), (key4, -2)]

theorem rawRowCheck13475 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form4 = rawRow13475 := by decide +kernel

def row13475 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key87, 4), (key148, -4), (key184, 2)]

theorem rowCheck13475 : row13475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13475 := by decide +kernel

theorem rowEval13475 (x : Key → ℝ) : Integer.Sparse.eval row13475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13475, Integer.Sparse.eval_collectBalanced, rawRowCheck13475]

def rawRow13476 : Integer.Sparse Key := [(key87, -2), (key148, -2), (key84, -2), (key87, 6), (key87, -2), (key148, -2), (key84, -2), (key164, 2), (key184, 2), (key4, 2), (key148, 2), (key1, 2), (key84, 2), (key148, -2), (key4, -2), (key87, -2), (key87, 6), (key148, -2), (key4, -2), (key87, -2)]

theorem rawRowCheck13476 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form4 = rawRow13476 := by decide +kernel

def row13476 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key87, 4), (key148, -6), (key164, 2), (key184, 2)]

theorem rowCheck13476 : row13476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13476 := by decide +kernel

theorem rowEval13476 (x : Key → ℝ) : Integer.Sparse.eval row13476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13476, Integer.Sparse.eval_collectBalanced, rawRowCheck13476]

def rawRow13477 : Integer.Sparse Key := [(key148, -2), (key87, -2), (key84, -2), (key87, 6), (key148, -2), (key87, -2), (key84, -2), (key184, 2), (key164, 2), (key148, 2), (key4, 2), (key84, 2), (key1, 2), (key148, -2), (key87, -2), (key4, -2), (key87, 6), (key148, -2), (key87, -2), (key4, -2)]

theorem rawRowCheck13477 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form4 = rawRow13477 := by decide +kernel

def row13477 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key87, 4), (key148, -6), (key164, 2), (key184, 2)]

theorem rowCheck13477 : row13477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13477 := by decide +kernel

theorem rowEval13477 (x : Key → ℝ) : Integer.Sparse.eval row13477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13477, Integer.Sparse.eval_collectBalanced, rawRowCheck13477]

def rawRow13478 : Integer.Sparse Key := [(key87, -2), (key87, -2), (key148, -2), (key84, 6), (key164, -2), (key164, -2), (key184, -2), (key4, 2), (key4, 2), (key87, 2), (key87, 2), (key148, 2), (key148, 2), (key1, -2), (key84, -2), (key84, -2), (key148, 6), (key4, -2), (key87, -2), (key87, -2)]

theorem rawRowCheck13478 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form4 = rawRow13478 := by decide +kernel

def row13478 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 8), (key164, -4), (key184, -2)]

theorem rowCheck13478 : row13478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13478 := by decide +kernel

theorem rowEval13478 (x : Key → ℝ) : Integer.Sparse.eval row13478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13478, Integer.Sparse.eval_collectBalanced, rawRowCheck13478]

def rawRow13479 : Integer.Sparse Key := [(key87, -2), (key148, -2), (key87, -2), (key84, 6), (key164, -2), (key184, -2), (key164, -2), (key87, 2), (key148, 2), (key4, 2), (key148, 2), (key4, 2), (key87, 2), (key84, -2), (key1, -2), (key84, -2), (key148, 6), (key87, -2), (key4, -2), (key87, -2)]

theorem rawRowCheck13479 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form4 = rawRow13479 := by decide +kernel

def row13479 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 8), (key164, -4), (key184, -2)]

theorem rowCheck13479 : row13479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13479 := by decide +kernel

theorem rowEval13479 (x : Key → ℝ) : Integer.Sparse.eval row13479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13479, Integer.Sparse.eval_collectBalanced, rawRowCheck13479]

def rawRow13480 : Integer.Sparse Key := [(key148, -2), (key87, -2), (key87, -2), (key84, 6), (key184, -2), (key164, -2), (key164, -2), (key148, 2), (key87, 2), (key148, 2), (key4, 2), (key87, 2), (key4, 2), (key84, -2), (key84, -2), (key1, -2), (key148, 6), (key87, -2), (key87, -2), (key4, -2)]

theorem rawRowCheck13480 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form4 = rawRow13480 := by decide +kernel

def row13480 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 8), (key164, -4), (key184, -2)]

theorem rowCheck13480 : row13480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13480 := by decide +kernel

theorem rowEval13480 (x : Key → ℝ) : Integer.Sparse.eval row13480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13480, Integer.Sparse.eval_collectBalanced, rawRowCheck13480]

def rawRow13481 : Integer.Sparse Key := [(key164, -2), (key164, -2), (key164, -2), (key184, 6), (key4, -2), (key4, -2), (key4, -2), (key87, 2), (key87, 2), (key87, 2), (key87, 2), (key87, 2), (key87, 2), (key148, -2), (key148, -2), (key148, -2), (key1, 6), (key84, -2), (key84, -2), (key84, -2)]

theorem rawRowCheck13481 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form4 = rawRow13481 := by decide +kernel

def row13481 : Integer.Sparse Key := [(key1, 6), (key4, -6), (key84, -6), (key87, 12), (key148, -6), (key164, -6), (key184, 6)]

theorem rowCheck13481 : row13481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13481 := by decide +kernel

theorem rowEval13481 (x : Key → ℝ) : Integer.Sparse.eval row13481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13481, Integer.Sparse.eval_collectBalanced, rawRowCheck13481]

def rawRow13482 : Integer.Sparse Key := [(key164, -2), (key164, -2), (key184, -2), (key164, 6), (key87, -2), (key87, -2), (key148, -2), (key4, 2), (key4, 2), (key87, 2), (key87, 2), (key148, 2), (key148, 2), (key4, -2), (key87, -2), (key87, -2), (key84, 6), (key1, -2), (key84, -2), (key84, -2)]

theorem rawRowCheck13482 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form4 = rawRow13482 := by decide +kernel

def row13482 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 2), (key164, 2), (key184, -2)]

theorem rowCheck13482 : row13482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13482 := by decide +kernel

theorem rowEval13482 (x : Key → ℝ) : Integer.Sparse.eval row13482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13482, Integer.Sparse.eval_collectBalanced, rawRowCheck13482]

def rawRow13483 : Integer.Sparse Key := [(key164, -2), (key184, -2), (key164, -2), (key164, 6), (key87, -2), (key148, -2), (key87, -2), (key87, 2), (key148, 2), (key4, 2), (key148, 2), (key4, 2), (key87, 2), (key87, -2), (key4, -2), (key87, -2), (key84, 6), (key84, -2), (key1, -2), (key84, -2)]

theorem rawRowCheck13483 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form4 = rawRow13483 := by decide +kernel

def row13483 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 2), (key164, 2), (key184, -2)]

theorem rowCheck13483 : row13483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13483 := by decide +kernel

theorem rowEval13483 (x : Key → ℝ) : Integer.Sparse.eval row13483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13483, Integer.Sparse.eval_collectBalanced, rawRowCheck13483]

def rawRow13484 : Integer.Sparse Key := [(key184, -2), (key164, -2), (key164, -2), (key164, 6), (key148, -2), (key87, -2), (key87, -2), (key148, 2), (key87, 2), (key148, 2), (key4, 2), (key87, 2), (key4, 2), (key87, -2), (key87, -2), (key4, -2), (key84, 6), (key84, -2), (key84, -2), (key1, -2)]

theorem rawRowCheck13484 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form4 = rawRow13484 := by decide +kernel

def row13484 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 2), (key164, 2), (key184, -2)]

theorem rowCheck13484 : row13484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13484 := by decide +kernel

theorem rowEval13484 (x : Key → ℝ) : Integer.Sparse.eval row13484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13484, Integer.Sparse.eval_collectBalanced, rawRowCheck13484]

def rawRow13485 : Integer.Sparse Key := [(key982, 4), (key1222, 4), (key1222, 4), (key986, -2), (key986, -2), (key1171, -2), (key1171, -2), (key1224, -2), (key1224, -2), (key986, -2), (key986, -2), (key1171, -2), (key1171, -2), (key1224, -2), (key1224, -2), (key988, 4), (key1175, 4), (key1175, 4)]

theorem rawRowCheck13485 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form0 = rawRow13485 := by decide +kernel

def row13485 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1171, -8), (key1175, 8), (key1222, 8), (key1224, -8)]

theorem rowCheck13485 : row13485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13485 := by decide +kernel

theorem rowEval13485 (x : Key → ℝ) : Integer.Sparse.eval row13485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13485, Integer.Sparse.eval_collectBalanced, rawRowCheck13485]

def rawRow13486 : Integer.Sparse Key := [(key1222, 4), (key982, 4), (key1222, 4), (key1171, -2), (key1224, -2), (key986, -2), (key1224, -2), (key986, -2), (key1171, -2), (key1171, -2), (key1224, -2), (key986, -2), (key1224, -2), (key986, -2), (key1171, -2), (key1175, 4), (key988, 4), (key1175, 4)]

theorem rawRowCheck13486 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form0 = rawRow13486 := by decide +kernel

def row13486 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1171, -8), (key1175, 8), (key1222, 8), (key1224, -8)]

theorem rowCheck13486 : row13486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13486 := by decide +kernel

theorem rowEval13486 (x : Key → ℝ) : Integer.Sparse.eval row13486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13486, Integer.Sparse.eval_collectBalanced, rawRowCheck13486]

def rawRow13487 : Integer.Sparse Key := [(key1222, 4), (key1222, 4), (key982, 4), (key1224, -2), (key1171, -2), (key1224, -2), (key986, -2), (key1171, -2), (key986, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key986, -2), (key1171, -2), (key986, -2), (key1175, 4), (key1175, 4), (key988, 4)]

theorem rawRowCheck13487 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form0 = rawRow13487 := by decide +kernel

def row13487 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1171, -8), (key1175, 8), (key1222, 8), (key1224, -8)]

theorem rowCheck13487 : row13487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13487 := by decide +kernel

theorem rowEval13487 (x : Key → ℝ) : Integer.Sparse.eval row13487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13487, Integer.Sparse.eval_collectBalanced, rawRowCheck13487]

def rawRow13488 : Integer.Sparse Key := [(key986, 4), (key1185, 4), (key1224, 4), (key982, -2), (key986, -2), (key1096, -2), (key1171, -2), (key1185, -2), (key1222, -2), (key986, -2), (key988, -2), (key1100, -2), (key1175, -2), (key1186, -2), (key1224, -2), (key986, 4), (key1100, 4), (key1171, 4)]

theorem rawRowCheck13488 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13488 := by decide +kernel

def row13488 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck13488 : row13488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13488 := by decide +kernel

theorem rowEval13488 (x : Key → ℝ) : Integer.Sparse.eval row13488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13488, Integer.Sparse.eval_collectBalanced, rawRowCheck13488]

def rawRow13489 : Integer.Sparse Key := [(key986, 4), (key1224, 4), (key1185, 4), (key986, -2), (key982, -2), (key1171, -2), (key1096, -2), (key1222, -2), (key1185, -2), (key988, -2), (key986, -2), (key1175, -2), (key1100, -2), (key1224, -2), (key1186, -2), (key986, 4), (key1171, 4), (key1100, 4)]

theorem rawRowCheck13489 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13489 := by decide +kernel

def row13489 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck13489 : row13489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13489 := by decide +kernel

theorem rowEval13489 (x : Key → ℝ) : Integer.Sparse.eval row13489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13489, Integer.Sparse.eval_collectBalanced, rawRowCheck13489]

def rawRow13490 : Integer.Sparse Key := [(key1185, 4), (key986, 4), (key1224, 4), (key1096, -2), (key1185, -2), (key982, -2), (key1222, -2), (key986, -2), (key1171, -2), (key1100, -2), (key1186, -2), (key986, -2), (key1224, -2), (key988, -2), (key1175, -2), (key1100, 4), (key986, 4), (key1171, 4)]

theorem rawRowCheck13490 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13490 := by decide +kernel

def row13490 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck13490 : row13490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13490 := by decide +kernel

theorem rowEval13490 (x : Key → ℝ) : Integer.Sparse.eval row13490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13490, Integer.Sparse.eval_collectBalanced, rawRowCheck13490]

def rawRow13491 : Integer.Sparse Key := [(key1185, 4), (key1224, 4), (key986, 4), (key1185, -2), (key1096, -2), (key1222, -2), (key982, -2), (key1171, -2), (key986, -2), (key1186, -2), (key1100, -2), (key1224, -2), (key986, -2), (key1175, -2), (key988, -2), (key1100, 4), (key1171, 4), (key986, 4)]

theorem rawRowCheck13491 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13491 := by decide +kernel

def row13491 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck13491 : row13491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13491 := by decide +kernel

theorem rowEval13491 (x : Key → ℝ) : Integer.Sparse.eval row13491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13491, Integer.Sparse.eval_collectBalanced, rawRowCheck13491]

def rawRow13492 : Integer.Sparse Key := [(key1224, 4), (key986, 4), (key1185, 4), (key1171, -2), (key1222, -2), (key986, -2), (key1185, -2), (key982, -2), (key1096, -2), (key1175, -2), (key1224, -2), (key988, -2), (key1186, -2), (key986, -2), (key1100, -2), (key1171, 4), (key986, 4), (key1100, 4)]

theorem rawRowCheck13492 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13492 := by decide +kernel

def row13492 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck13492 : row13492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13492 := by decide +kernel

theorem rowEval13492 (x : Key → ℝ) : Integer.Sparse.eval row13492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13492, Integer.Sparse.eval_collectBalanced, rawRowCheck13492]

def rawRow13493 : Integer.Sparse Key := [(key1224, 4), (key1185, 4), (key986, 4), (key1222, -2), (key1171, -2), (key1185, -2), (key986, -2), (key1096, -2), (key982, -2), (key1224, -2), (key1175, -2), (key1186, -2), (key988, -2), (key1100, -2), (key986, -2), (key1171, 4), (key1100, 4), (key986, 4)]

theorem rawRowCheck13493 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13493 := by decide +kernel

def row13493 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck13493 : row13493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13493 := by decide +kernel

theorem rowEval13493 (x : Key → ℝ) : Integer.Sparse.eval row13493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13493, Integer.Sparse.eval_collectBalanced, rawRowCheck13493]

def rawRow13494 : Integer.Sparse Key := [(key986, 4), (key1185, 4), (key1224, 4), (key986, -2), (key988, -2), (key1100, -2), (key1175, -2), (key1186, -2), (key1224, -2), (key982, -2), (key986, -2), (key1096, -2), (key1171, -2), (key1185, -2), (key1222, -2), (key986, 4), (key1100, 4), (key1171, 4)]

theorem rawRowCheck13494 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13494 := by decide +kernel

def row13494 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck13494 : row13494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13494 := by decide +kernel

theorem rowEval13494 (x : Key → ℝ) : Integer.Sparse.eval row13494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13494, Integer.Sparse.eval_collectBalanced, rawRowCheck13494]

def rawRow13495 : Integer.Sparse Key := [(key986, 4), (key1224, 4), (key1185, 4), (key988, -2), (key986, -2), (key1175, -2), (key1100, -2), (key1224, -2), (key1186, -2), (key986, -2), (key982, -2), (key1171, -2), (key1096, -2), (key1222, -2), (key1185, -2), (key986, 4), (key1171, 4), (key1100, 4)]

theorem rawRowCheck13495 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13495 := by decide +kernel

def row13495 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck13495 : row13495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13495 := by decide +kernel

theorem rowEval13495 (x : Key → ℝ) : Integer.Sparse.eval row13495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13495, Integer.Sparse.eval_collectBalanced, rawRowCheck13495]

def rawRow13496 : Integer.Sparse Key := [(key1185, 4), (key986, 4), (key1224, 4), (key1100, -2), (key1186, -2), (key986, -2), (key1224, -2), (key988, -2), (key1175, -2), (key1096, -2), (key1185, -2), (key982, -2), (key1222, -2), (key986, -2), (key1171, -2), (key1100, 4), (key986, 4), (key1171, 4)]

theorem rawRowCheck13496 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13496 := by decide +kernel

def row13496 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck13496 : row13496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13496 := by decide +kernel

theorem rowEval13496 (x : Key → ℝ) : Integer.Sparse.eval row13496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13496, Integer.Sparse.eval_collectBalanced, rawRowCheck13496]

def rawRow13497 : Integer.Sparse Key := [(key1185, 4), (key1224, 4), (key986, 4), (key1186, -2), (key1100, -2), (key1224, -2), (key986, -2), (key1175, -2), (key988, -2), (key1185, -2), (key1096, -2), (key1222, -2), (key982, -2), (key1171, -2), (key986, -2), (key1100, 4), (key1171, 4), (key986, 4)]

theorem rawRowCheck13497 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13497 := by decide +kernel

def row13497 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck13497 : row13497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13497 := by decide +kernel

theorem rowEval13497 (x : Key → ℝ) : Integer.Sparse.eval row13497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13497, Integer.Sparse.eval_collectBalanced, rawRowCheck13497]

def rawRow13498 : Integer.Sparse Key := [(key1224, 4), (key986, 4), (key1185, 4), (key1175, -2), (key1224, -2), (key988, -2), (key1186, -2), (key986, -2), (key1100, -2), (key1171, -2), (key1222, -2), (key986, -2), (key1185, -2), (key982, -2), (key1096, -2), (key1171, 4), (key986, 4), (key1100, 4)]

theorem rawRowCheck13498 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13498 := by decide +kernel

def row13498 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck13498 : row13498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13498 := by decide +kernel

theorem rowEval13498 (x : Key → ℝ) : Integer.Sparse.eval row13498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13498, Integer.Sparse.eval_collectBalanced, rawRowCheck13498]

def rawRow13499 : Integer.Sparse Key := [(key1224, 4), (key1185, 4), (key986, 4), (key1224, -2), (key1175, -2), (key1186, -2), (key988, -2), (key1100, -2), (key986, -2), (key1222, -2), (key1171, -2), (key1185, -2), (key986, -2), (key1096, -2), (key982, -2), (key1171, 4), (key1100, 4), (key986, 4)]

theorem rawRowCheck13499 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13499 := by decide +kernel

def row13499 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck13499 : row13499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13499 := by decide +kernel

theorem rowEval13499 (x : Key → ℝ) : Integer.Sparse.eval row13499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13499, Integer.Sparse.eval_collectBalanced, rawRowCheck13499]

def rawRow13500 : Integer.Sparse Key := [(key988, 4), (key1186, 4), (key1186, 4), (key986, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1185, -2), (key1185, -2), (key986, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1185, -2), (key1185, -2), (key982, 4), (key1096, 4), (key1096, 4)]

theorem rawRowCheck13500 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13500 := by decide +kernel

def row13500 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1096, 8), (key1100, -8), (key1185, -8), (key1186, 8)]

theorem rowCheck13500 : row13500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13500 := by decide +kernel

theorem rowEval13500 (x : Key → ℝ) : Integer.Sparse.eval row13500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13500, Integer.Sparse.eval_collectBalanced, rawRowCheck13500]

def rawRow13501 : Integer.Sparse Key := [(key1186, 4), (key988, 4), (key1186, 4), (key1100, -2), (key1185, -2), (key986, -2), (key1185, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1185, -2), (key986, -2), (key1185, -2), (key986, -2), (key1100, -2), (key1096, 4), (key982, 4), (key1096, 4)]

theorem rawRowCheck13501 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13501 := by decide +kernel

def row13501 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1096, 8), (key1100, -8), (key1185, -8), (key1186, 8)]

theorem rowCheck13501 : row13501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13501 := by decide +kernel

theorem rowEval13501 (x : Key → ℝ) : Integer.Sparse.eval row13501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13501, Integer.Sparse.eval_collectBalanced, rawRowCheck13501]

def rawRow13502 : Integer.Sparse Key := [(key1186, 4), (key1186, 4), (key988, 4), (key1185, -2), (key1100, -2), (key1185, -2), (key986, -2), (key1100, -2), (key986, -2), (key1185, -2), (key1100, -2), (key1185, -2), (key986, -2), (key1100, -2), (key986, -2), (key1096, 4), (key1096, 4), (key982, 4)]

theorem rawRowCheck13502 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13502 := by decide +kernel

def row13502 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1096, 8), (key1100, -8), (key1185, -8), (key1186, 8)]

theorem rowCheck13502 : row13502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13502 := by decide +kernel

theorem rowEval13502 (x : Key → ℝ) : Integer.Sparse.eval row13502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13502, Integer.Sparse.eval_collectBalanced, rawRowCheck13502]

def rawRow13503 : Integer.Sparse Key := [(key88, -2), (key88, -2), (key156, -2), (key94, 6), (key88, -2), (key88, -2), (key156, -2), (key5, 2), (key9, 2), (key153, 2), (key153, 2), (key203, 2), (key203, 2), (key14, -2), (key161, -2), (key161, -2), (key97, 6), (key14, -2), (key161, -2), (key161, -2)]

theorem rawRowCheck13503 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form1 = rawRow13503 := by decide +kernel

def row13503 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, -4), (key88, -8), (key94, 6), (key97, 6), (key153, 4), (key156, -4), (key161, -8), (key203, 4)]

theorem rowCheck13503 : row13503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13503 := by decide +kernel

theorem rowEval13503 (x : Key → ℝ) : Integer.Sparse.eval row13503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13503, Integer.Sparse.eval_collectBalanced, rawRowCheck13503]

def rawRow13504 : Integer.Sparse Key := [(key88, -2), (key156, -2), (key88, -2), (key94, 6), (key88, -2), (key156, -2), (key88, -2), (key165, 2), (key187, 2), (key5, 2), (key187, 2), (key9, 2), (key153, 2), (key161, -2), (key14, -2), (key161, -2), (key97, 6), (key161, -2), (key14, -2), (key161, -2)]

theorem rawRowCheck13504 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form1 = rawRow13504 := by decide +kernel

def row13504 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, -4), (key88, -8), (key94, 6), (key97, 6), (key153, 2), (key156, -4), (key161, -8), (key165, 2), (key187, 4)]

theorem rowCheck13504 : row13504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13504 := by decide +kernel

theorem rowEval13504 (x : Key → ℝ) : Integer.Sparse.eval row13504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13504, Integer.Sparse.eval_collectBalanced, rawRowCheck13504]

def rawRow13505 : Integer.Sparse Key := [(key156, -2), (key88, -2), (key88, -2), (key94, 6), (key156, -2), (key88, -2), (key88, -2), (key187, 2), (key165, 2), (key187, 2), (key5, 2), (key153, 2), (key9, 2), (key161, -2), (key161, -2), (key14, -2), (key97, 6), (key161, -2), (key161, -2), (key14, -2)]

theorem rawRowCheck13505 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form1 = rawRow13505 := by decide +kernel

def row13505 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, -4), (key88, -8), (key94, 6), (key97, 6), (key153, 2), (key156, -4), (key161, -8), (key165, 2), (key187, 4)]

theorem rowCheck13505 : row13505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13505 := by decide +kernel

theorem rowEval13505 (x : Key → ℝ) : Integer.Sparse.eval row13505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13505, Integer.Sparse.eval_collectBalanced, rawRowCheck13505]

def rawRow13506 : Integer.Sparse Key := [(key88, -2), (key94, -2), (key156, -2), (key88, 6), (key165, -2), (key167, -2), (key187, -2), (key5, 2), (key11, 2), (key88, 2), (key167, 2), (key156, 2), (key187, 2), (key9, -2), (key92, -2), (key153, -2), (key161, 6), (key14, -2), (key97, -2), (key161, -2)]

theorem rawRowCheck13506 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form1 = rawRow13506 := by decide +kernel

def row13506 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key11, 2), (key14, -2), (key88, 6), (key92, -2), (key94, -2), (key97, -2), (key153, -2), (key161, 4), (key165, -2)]

theorem rowCheck13506 : row13506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13506 := by decide +kernel

theorem rowEval13506 (x : Key → ℝ) : Integer.Sparse.eval row13506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13506, Integer.Sparse.eval_collectBalanced, rawRowCheck13506]

def rawRow13507 : Integer.Sparse Key := [(key94, -2), (key88, -2), (key156, -2), (key88, 6), (key167, -2), (key165, -2), (key187, -2), (key11, 2), (key5, 2), (key167, 2), (key88, 2), (key187, 2), (key156, 2), (key9, -2), (key153, -2), (key92, -2), (key161, 6), (key14, -2), (key161, -2), (key97, -2)]

theorem rawRowCheck13507 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form1 = rawRow13507 := by decide +kernel

def row13507 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key11, 2), (key14, -2), (key88, 6), (key92, -2), (key94, -2), (key97, -2), (key153, -2), (key161, 4), (key165, -2)]

theorem rowCheck13507 : row13507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13507 := by decide +kernel

theorem rowEval13507 (x : Key → ℝ) : Integer.Sparse.eval row13507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13507, Integer.Sparse.eval_collectBalanced, rawRowCheck13507]

def rawRow13508 : Integer.Sparse Key := [(key88, -2), (key156, -2), (key94, -2), (key88, 6), (key165, -2), (key187, -2), (key167, -2), (key88, 2), (key156, 2), (key5, 2), (key187, 2), (key11, 2), (key167, 2), (key92, -2), (key9, -2), (key153, -2), (key161, 6), (key97, -2), (key14, -2), (key161, -2)]

theorem rawRowCheck13508 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form1 = rawRow13508 := by decide +kernel

def row13508 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key11, 2), (key14, -2), (key88, 6), (key92, -2), (key94, -2), (key97, -2), (key153, -2), (key161, 4), (key165, -2)]

theorem rowCheck13508 : row13508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13508 := by decide +kernel

theorem rowEval13508 (x : Key → ℝ) : Integer.Sparse.eval row13508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13508, Integer.Sparse.eval_collectBalanced, rawRowCheck13508]

def rawRow13509 : Integer.Sparse Key := [(key156, -2), (key88, -2), (key94, -2), (key88, 6), (key187, -2), (key165, -2), (key167, -2), (key156, 2), (key88, 2), (key187, 2), (key5, 2), (key167, 2), (key11, 2), (key92, -2), (key153, -2), (key9, -2), (key161, 6), (key97, -2), (key161, -2), (key14, -2)]

theorem rawRowCheck13509 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form1 = rawRow13509 := by decide +kernel

def row13509 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key11, 2), (key14, -2), (key88, 6), (key92, -2), (key94, -2), (key97, -2), (key153, -2), (key161, 4), (key165, -2)]

theorem rowCheck13509 : row13509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13509 := by decide +kernel

theorem rowEval13509 (x : Key → ℝ) : Integer.Sparse.eval row13509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13509, Integer.Sparse.eval_collectBalanced, rawRowCheck13509]

def rawRow13510 : Integer.Sparse Key := [(key94, -2), (key156, -2), (key88, -2), (key88, 6), (key167, -2), (key187, -2), (key165, -2), (key167, 2), (key187, 2), (key11, 2), (key156, 2), (key5, 2), (key88, 2), (key153, -2), (key9, -2), (key92, -2), (key161, 6), (key161, -2), (key14, -2), (key97, -2)]

theorem rawRowCheck13510 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form1 = rawRow13510 := by decide +kernel

def row13510 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key11, 2), (key14, -2), (key88, 6), (key92, -2), (key94, -2), (key97, -2), (key153, -2), (key161, 4), (key165, -2)]

theorem rowCheck13510 : row13510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13510 := by decide +kernel

theorem rowEval13510 (x : Key → ℝ) : Integer.Sparse.eval row13510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13510, Integer.Sparse.eval_collectBalanced, rawRowCheck13510]

def rawRow13511 : Integer.Sparse Key := [(key156, -2), (key94, -2), (key88, -2), (key88, 6), (key187, -2), (key167, -2), (key165, -2), (key187, 2), (key167, 2), (key156, 2), (key11, 2), (key88, 2), (key5, 2), (key153, -2), (key92, -2), (key9, -2), (key161, 6), (key161, -2), (key97, -2), (key14, -2)]

theorem rawRowCheck13511 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form1 = rawRow13511 := by decide +kernel

def row13511 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key11, 2), (key14, -2), (key88, 6), (key92, -2), (key94, -2), (key97, -2), (key153, -2), (key161, 4), (key165, -2)]

theorem rowCheck13511 : row13511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13511 := by decide +kernel

theorem rowEval13511 (x : Key → ℝ) : Integer.Sparse.eval row13511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13511, Integer.Sparse.eval_collectBalanced, rawRowCheck13511]

def rawRow13512 : Integer.Sparse Key := [(key165, -2), (key167, -2), (key187, -2), (key167, 6), (key88, -2), (key94, -2), (key156, -2), (key5, 2), (key11, 2), (key88, 2), (key167, 2), (key156, 2), (key187, 2), (key11, -2), (key94, -2), (key167, -2), (key92, 6), (key9, -2), (key92, -2), (key153, -2)]

theorem rawRowCheck13512 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form1 = rawRow13512 := by decide +kernel

def row13512 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key92, 4), (key94, -4), (key153, -2), (key165, -2), (key167, 4)]

theorem rowCheck13512 : row13512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13512 := by decide +kernel

theorem rowEval13512 (x : Key → ℝ) : Integer.Sparse.eval row13512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13512, Integer.Sparse.eval_collectBalanced, rawRowCheck13512]

def rawRow13513 : Integer.Sparse Key := [(key167, -2), (key165, -2), (key187, -2), (key167, 6), (key94, -2), (key88, -2), (key156, -2), (key11, 2), (key5, 2), (key167, 2), (key88, 2), (key187, 2), (key156, 2), (key11, -2), (key167, -2), (key94, -2), (key92, 6), (key9, -2), (key153, -2), (key92, -2)]

theorem rawRowCheck13513 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form1 = rawRow13513 := by decide +kernel

def row13513 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key92, 4), (key94, -4), (key153, -2), (key165, -2), (key167, 4)]

theorem rowCheck13513 : row13513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13513 := by decide +kernel

theorem rowEval13513 (x : Key → ℝ) : Integer.Sparse.eval row13513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13513, Integer.Sparse.eval_collectBalanced, rawRowCheck13513]

def rawRow13514 : Integer.Sparse Key := [(key165, -2), (key187, -2), (key167, -2), (key167, 6), (key88, -2), (key156, -2), (key94, -2), (key88, 2), (key156, 2), (key5, 2), (key187, 2), (key11, 2), (key167, 2), (key94, -2), (key11, -2), (key167, -2), (key92, 6), (key92, -2), (key9, -2), (key153, -2)]

theorem rawRowCheck13514 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form1 = rawRow13514 := by decide +kernel

def row13514 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key92, 4), (key94, -4), (key153, -2), (key165, -2), (key167, 4)]

theorem rowCheck13514 : row13514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13514 := by decide +kernel

theorem rowEval13514 (x : Key → ℝ) : Integer.Sparse.eval row13514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13514, Integer.Sparse.eval_collectBalanced, rawRowCheck13514]

def rawRow13515 : Integer.Sparse Key := [(key187, -2), (key165, -2), (key167, -2), (key167, 6), (key156, -2), (key88, -2), (key94, -2), (key156, 2), (key88, 2), (key187, 2), (key5, 2), (key167, 2), (key11, 2), (key94, -2), (key167, -2), (key11, -2), (key92, 6), (key92, -2), (key153, -2), (key9, -2)]

theorem rawRowCheck13515 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form1 = rawRow13515 := by decide +kernel

def row13515 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key92, 4), (key94, -4), (key153, -2), (key165, -2), (key167, 4)]

theorem rowCheck13515 : row13515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13515 := by decide +kernel

theorem rowEval13515 (x : Key → ℝ) : Integer.Sparse.eval row13515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13515, Integer.Sparse.eval_collectBalanced, rawRowCheck13515]

def rawRow13516 : Integer.Sparse Key := [(key167, -2), (key187, -2), (key165, -2), (key167, 6), (key94, -2), (key156, -2), (key88, -2), (key167, 2), (key187, 2), (key11, 2), (key156, 2), (key5, 2), (key88, 2), (key167, -2), (key11, -2), (key94, -2), (key92, 6), (key153, -2), (key9, -2), (key92, -2)]

theorem rawRowCheck13516 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form1 = rawRow13516 := by decide +kernel

def row13516 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key92, 4), (key94, -4), (key153, -2), (key165, -2), (key167, 4)]

theorem rowCheck13516 : row13516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13516 := by decide +kernel

theorem rowEval13516 (x : Key → ℝ) : Integer.Sparse.eval row13516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13516, Integer.Sparse.eval_collectBalanced, rawRowCheck13516]

def rawRow13517 : Integer.Sparse Key := [(key187, -2), (key167, -2), (key165, -2), (key167, 6), (key156, -2), (key94, -2), (key88, -2), (key187, 2), (key167, 2), (key156, 2), (key11, 2), (key88, 2), (key5, 2), (key167, -2), (key94, -2), (key11, -2), (key92, 6), (key153, -2), (key92, -2), (key9, -2)]

theorem rawRowCheck13517 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form1 = rawRow13517 := by decide +kernel

def row13517 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key92, 4), (key94, -4), (key153, -2), (key165, -2), (key167, 4)]

theorem rowCheck13517 : row13517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13517 := by decide +kernel

theorem rowEval13517 (x : Key → ℝ) : Integer.Sparse.eval row13517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13517, Integer.Sparse.eval_collectBalanced, rawRowCheck13517]

def rawRow13518 : Integer.Sparse Key := [(key167, -2), (key167, -2), (key187, -2), (key165, 6), (key167, -2), (key167, -2), (key187, -2), (key11, 2), (key11, 2), (key94, 2), (key94, 2), (key156, 2), (key156, 2), (key5, -2), (key88, -2), (key88, -2), (key153, 6), (key9, -2), (key92, -2), (key92, -2)]

theorem rawRowCheck13518 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13518 := by decide +kernel

def row13518 : Integer.Sparse Key := [(key5, -2), (key9, -2), (key11, 4), (key88, -4), (key92, -4), (key94, 4), (key153, 6), (key156, 4), (key165, 6), (key167, -8), (key187, -4)]

theorem rowCheck13518 : row13518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13518 := by decide +kernel

theorem rowEval13518 (x : Key → ℝ) : Integer.Sparse.eval row13518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13518, Integer.Sparse.eval_collectBalanced, rawRowCheck13518]

def rawRow13519 : Integer.Sparse Key := [(key167, -2), (key187, -2), (key167, -2), (key165, 6), (key167, -2), (key187, -2), (key167, -2), (key94, 2), (key156, 2), (key11, 2), (key156, 2), (key11, 2), (key94, 2), (key88, -2), (key5, -2), (key88, -2), (key153, 6), (key92, -2), (key9, -2), (key92, -2)]

theorem rawRowCheck13519 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13519 := by decide +kernel

def row13519 : Integer.Sparse Key := [(key5, -2), (key9, -2), (key11, 4), (key88, -4), (key92, -4), (key94, 4), (key153, 6), (key156, 4), (key165, 6), (key167, -8), (key187, -4)]

theorem rowCheck13519 : row13519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13519 := by decide +kernel

theorem rowEval13519 (x : Key → ℝ) : Integer.Sparse.eval row13519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13519, Integer.Sparse.eval_collectBalanced, rawRowCheck13519]

def rawRow13520 : Integer.Sparse Key := [(key187, -2), (key167, -2), (key167, -2), (key165, 6), (key187, -2), (key167, -2), (key167, -2), (key156, 2), (key94, 2), (key156, 2), (key11, 2), (key94, 2), (key11, 2), (key88, -2), (key88, -2), (key5, -2), (key153, 6), (key92, -2), (key92, -2), (key9, -2)]

theorem rawRowCheck13520 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13520 := by decide +kernel

def row13520 : Integer.Sparse Key := [(key5, -2), (key9, -2), (key11, 4), (key88, -4), (key92, -4), (key94, 4), (key153, 6), (key156, 4), (key165, 6), (key167, -8), (key187, -4)]

theorem rowCheck13520 : row13520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13520 := by decide +kernel

theorem rowEval13520 (x : Key → ℝ) : Integer.Sparse.eval row13520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13520, Integer.Sparse.eval_collectBalanced, rawRowCheck13520]

def rawRow13521 : Integer.Sparse Key := [(key1095, -2), (key1095, -2), (key1229, -2), (key1101, 6), (key1095, -2), (key1095, -2), (key1229, -2), (key981, 2), (key981, 2), (key1166, 2), (key1166, 2), (key1246, 2), (key1246, 2), (key987, -2), (key1173, -2), (key1173, -2), (key1101, 6), (key987, -2), (key1173, -2), (key1173, -2)]

theorem rawRowCheck13521 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form2 = rawRow13521 := by decide +kernel

def row13521 : Integer.Sparse Key := [(key981, 4), (key987, -4), (key1095, -8), (key1101, 12), (key1166, 4), (key1173, -8), (key1229, -4), (key1246, 4)]

theorem rowCheck13521 : row13521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13521 := by decide +kernel

theorem rowEval13521 (x : Key → ℝ) : Integer.Sparse.eval row13521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13521, Integer.Sparse.eval_collectBalanced, rawRowCheck13521]

def rawRow13522 : Integer.Sparse Key := [(key1095, -2), (key1229, -2), (key1095, -2), (key1101, 6), (key1095, -2), (key1229, -2), (key1095, -2), (key1166, 2), (key1246, 2), (key981, 2), (key1246, 2), (key981, 2), (key1166, 2), (key1173, -2), (key987, -2), (key1173, -2), (key1101, 6), (key1173, -2), (key987, -2), (key1173, -2)]

theorem rawRowCheck13522 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form2 = rawRow13522 := by decide +kernel

def row13522 : Integer.Sparse Key := [(key981, 4), (key987, -4), (key1095, -8), (key1101, 12), (key1166, 4), (key1173, -8), (key1229, -4), (key1246, 4)]

theorem rowCheck13522 : row13522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13522 := by decide +kernel

theorem rowEval13522 (x : Key → ℝ) : Integer.Sparse.eval row13522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13522, Integer.Sparse.eval_collectBalanced, rawRowCheck13522]

def rawRow13523 : Integer.Sparse Key := [(key1229, -2), (key1095, -2), (key1095, -2), (key1101, 6), (key1229, -2), (key1095, -2), (key1095, -2), (key1246, 2), (key1166, 2), (key1246, 2), (key981, 2), (key1166, 2), (key981, 2), (key1173, -2), (key1173, -2), (key987, -2), (key1101, 6), (key1173, -2), (key1173, -2), (key987, -2)]

theorem rawRowCheck13523 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form2 = rawRow13523 := by decide +kernel

def row13523 : Integer.Sparse Key := [(key981, 4), (key987, -4), (key1095, -8), (key1101, 12), (key1166, 4), (key1173, -8), (key1229, -4), (key1246, 4)]

theorem rowCheck13523 : row13523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13523 := by decide +kernel

theorem rowEval13523 (x : Key → ℝ) : Integer.Sparse.eval row13523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13523, Integer.Sparse.eval_collectBalanced, rawRowCheck13523]

def rawRow13524 : Integer.Sparse Key := [(key1095, -2), (key1101, -2), (key1229, -2), (key1095, 6), (key1166, -2), (key1173, -2), (key1246, -2), (key981, 2), (key987, 2), (key1095, 2), (key1173, 2), (key1229, 2), (key1246, 2), (key981, -2), (key1095, -2), (key1166, -2), (key1173, 6), (key987, -2), (key1101, -2), (key1173, -2)]

theorem rawRowCheck13524 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form2 = rawRow13524 := by decide +kernel

def row13524 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

theorem rowCheck13524 : row13524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13524 := by decide +kernel

theorem rowEval13524 (x : Key → ℝ) : Integer.Sparse.eval row13524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13524, Integer.Sparse.eval_collectBalanced, rawRowCheck13524]

def rawRow13525 : Integer.Sparse Key := [(key1101, -2), (key1095, -2), (key1229, -2), (key1095, 6), (key1173, -2), (key1166, -2), (key1246, -2), (key987, 2), (key981, 2), (key1173, 2), (key1095, 2), (key1246, 2), (key1229, 2), (key981, -2), (key1166, -2), (key1095, -2), (key1173, 6), (key987, -2), (key1173, -2), (key1101, -2)]

theorem rawRowCheck13525 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form2 = rawRow13525 := by decide +kernel

def row13525 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

theorem rowCheck13525 : row13525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13525 := by decide +kernel

theorem rowEval13525 (x : Key → ℝ) : Integer.Sparse.eval row13525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13525, Integer.Sparse.eval_collectBalanced, rawRowCheck13525]

def rawRow13526 : Integer.Sparse Key := [(key1095, -2), (key1229, -2), (key1101, -2), (key1095, 6), (key1166, -2), (key1246, -2), (key1173, -2), (key1095, 2), (key1229, 2), (key981, 2), (key1246, 2), (key987, 2), (key1173, 2), (key1095, -2), (key981, -2), (key1166, -2), (key1173, 6), (key1101, -2), (key987, -2), (key1173, -2)]

theorem rawRowCheck13526 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form2 = rawRow13526 := by decide +kernel

def row13526 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

theorem rowCheck13526 : row13526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13526 := by decide +kernel

theorem rowEval13526 (x : Key → ℝ) : Integer.Sparse.eval row13526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13526, Integer.Sparse.eval_collectBalanced, rawRowCheck13526]

def rawRow13527 : Integer.Sparse Key := [(key1229, -2), (key1095, -2), (key1101, -2), (key1095, 6), (key1246, -2), (key1166, -2), (key1173, -2), (key1229, 2), (key1095, 2), (key1246, 2), (key981, 2), (key1173, 2), (key987, 2), (key1095, -2), (key1166, -2), (key981, -2), (key1173, 6), (key1101, -2), (key1173, -2), (key987, -2)]

theorem rawRowCheck13527 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form2 = rawRow13527 := by decide +kernel

def row13527 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

theorem rowCheck13527 : row13527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13527 := by decide +kernel

theorem rowEval13527 (x : Key → ℝ) : Integer.Sparse.eval row13527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13527, Integer.Sparse.eval_collectBalanced, rawRowCheck13527]

def rawRow13528 : Integer.Sparse Key := [(key1101, -2), (key1229, -2), (key1095, -2), (key1095, 6), (key1173, -2), (key1246, -2), (key1166, -2), (key1173, 2), (key1246, 2), (key987, 2), (key1229, 2), (key981, 2), (key1095, 2), (key1166, -2), (key981, -2), (key1095, -2), (key1173, 6), (key1173, -2), (key987, -2), (key1101, -2)]

theorem rawRowCheck13528 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form2 = rawRow13528 := by decide +kernel

def row13528 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

theorem rowCheck13528 : row13528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13528 := by decide +kernel

theorem rowEval13528 (x : Key → ℝ) : Integer.Sparse.eval row13528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13528, Integer.Sparse.eval_collectBalanced, rawRowCheck13528]

def rawRow13529 : Integer.Sparse Key := [(key1229, -2), (key1101, -2), (key1095, -2), (key1095, 6), (key1246, -2), (key1173, -2), (key1166, -2), (key1246, 2), (key1173, 2), (key1229, 2), (key987, 2), (key1095, 2), (key981, 2), (key1166, -2), (key1095, -2), (key981, -2), (key1173, 6), (key1173, -2), (key1101, -2), (key987, -2)]

theorem rawRowCheck13529 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form2 = rawRow13529 := by decide +kernel

def row13529 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

theorem rowCheck13529 : row13529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13529 := by decide +kernel

theorem rowEval13529 (x : Key → ℝ) : Integer.Sparse.eval row13529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13529, Integer.Sparse.eval_collectBalanced, rawRowCheck13529]

def rawRow13530 : Integer.Sparse Key := [(key1166, -2), (key1173, -2), (key1246, -2), (key1173, 6), (key1095, -2), (key1101, -2), (key1229, -2), (key981, 2), (key987, 2), (key1095, 2), (key1173, 2), (key1229, 2), (key1246, 2), (key987, -2), (key1101, -2), (key1173, -2), (key1095, 6), (key981, -2), (key1095, -2), (key1166, -2)]

theorem rawRowCheck13530 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form2 = rawRow13530 := by decide +kernel

def row13530 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

theorem rowCheck13530 : row13530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13530 := by decide +kernel

theorem rowEval13530 (x : Key → ℝ) : Integer.Sparse.eval row13530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13530, Integer.Sparse.eval_collectBalanced, rawRowCheck13530]

def rawRow13531 : Integer.Sparse Key := [(key1173, -2), (key1166, -2), (key1246, -2), (key1173, 6), (key1101, -2), (key1095, -2), (key1229, -2), (key987, 2), (key981, 2), (key1173, 2), (key1095, 2), (key1246, 2), (key1229, 2), (key987, -2), (key1173, -2), (key1101, -2), (key1095, 6), (key981, -2), (key1166, -2), (key1095, -2)]

theorem rawRowCheck13531 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form2 = rawRow13531 := by decide +kernel

def row13531 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

theorem rowCheck13531 : row13531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13531 := by decide +kernel

theorem rowEval13531 (x : Key → ℝ) : Integer.Sparse.eval row13531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13531, Integer.Sparse.eval_collectBalanced, rawRowCheck13531]

def rawRow13532 : Integer.Sparse Key := [(key1166, -2), (key1246, -2), (key1173, -2), (key1173, 6), (key1095, -2), (key1229, -2), (key1101, -2), (key1095, 2), (key1229, 2), (key981, 2), (key1246, 2), (key987, 2), (key1173, 2), (key1101, -2), (key987, -2), (key1173, -2), (key1095, 6), (key1095, -2), (key981, -2), (key1166, -2)]

theorem rawRowCheck13532 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form2 = rawRow13532 := by decide +kernel

def row13532 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

theorem rowCheck13532 : row13532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13532 := by decide +kernel

theorem rowEval13532 (x : Key → ℝ) : Integer.Sparse.eval row13532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13532, Integer.Sparse.eval_collectBalanced, rawRowCheck13532]

def rawRow13533 : Integer.Sparse Key := [(key1246, -2), (key1166, -2), (key1173, -2), (key1173, 6), (key1229, -2), (key1095, -2), (key1101, -2), (key1229, 2), (key1095, 2), (key1246, 2), (key981, 2), (key1173, 2), (key987, 2), (key1101, -2), (key1173, -2), (key987, -2), (key1095, 6), (key1095, -2), (key1166, -2), (key981, -2)]

theorem rawRowCheck13533 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form2 = rawRow13533 := by decide +kernel

def row13533 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

theorem rowCheck13533 : row13533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13533 := by decide +kernel

theorem rowEval13533 (x : Key → ℝ) : Integer.Sparse.eval row13533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13533, Integer.Sparse.eval_collectBalanced, rawRowCheck13533]

def rawRow13534 : Integer.Sparse Key := [(key1173, -2), (key1246, -2), (key1166, -2), (key1173, 6), (key1101, -2), (key1229, -2), (key1095, -2), (key1173, 2), (key1246, 2), (key987, 2), (key1229, 2), (key981, 2), (key1095, 2), (key1173, -2), (key987, -2), (key1101, -2), (key1095, 6), (key1166, -2), (key981, -2), (key1095, -2)]

theorem rawRowCheck13534 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form2 = rawRow13534 := by decide +kernel

def row13534 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

theorem rowCheck13534 : row13534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13534 := by decide +kernel

theorem rowEval13534 (x : Key → ℝ) : Integer.Sparse.eval row13534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13534, Integer.Sparse.eval_collectBalanced, rawRowCheck13534]

def rawRow13535 : Integer.Sparse Key := [(key1246, -2), (key1173, -2), (key1166, -2), (key1173, 6), (key1229, -2), (key1101, -2), (key1095, -2), (key1246, 2), (key1173, 2), (key1229, 2), (key987, 2), (key1095, 2), (key981, 2), (key1173, -2), (key1101, -2), (key987, -2), (key1095, 6), (key1166, -2), (key1095, -2), (key981, -2)]

theorem rawRowCheck13535 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form2 = rawRow13535 := by decide +kernel

def row13535 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

theorem rowCheck13535 : row13535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13535 := by decide +kernel

theorem rowEval13535 (x : Key → ℝ) : Integer.Sparse.eval row13535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13535, Integer.Sparse.eval_collectBalanced, rawRowCheck13535]

def rawRow13536 : Integer.Sparse Key := [(key1173, -2), (key1173, -2), (key1246, -2), (key1166, 6), (key1173, -2), (key1173, -2), (key1246, -2), (key987, 2), (key987, 2), (key1101, 2), (key1101, 2), (key1229, 2), (key1229, 2), (key981, -2), (key1095, -2), (key1095, -2), (key1166, 6), (key981, -2), (key1095, -2), (key1095, -2)]

theorem rawRowCheck13536 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13536 := by decide +kernel

def row13536 : Integer.Sparse Key := [(key981, -4), (key987, 4), (key1095, -8), (key1101, 4), (key1166, 12), (key1173, -8), (key1229, 4), (key1246, -4)]

theorem rowCheck13536 : row13536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13536 := by decide +kernel

theorem rowEval13536 (x : Key → ℝ) : Integer.Sparse.eval row13536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13536, Integer.Sparse.eval_collectBalanced, rawRowCheck13536]

def rawRow13537 : Integer.Sparse Key := [(key1173, -2), (key1246, -2), (key1173, -2), (key1166, 6), (key1173, -2), (key1246, -2), (key1173, -2), (key1101, 2), (key1229, 2), (key987, 2), (key1229, 2), (key987, 2), (key1101, 2), (key1095, -2), (key981, -2), (key1095, -2), (key1166, 6), (key1095, -2), (key981, -2), (key1095, -2)]

theorem rawRowCheck13537 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13537 := by decide +kernel

def row13537 : Integer.Sparse Key := [(key981, -4), (key987, 4), (key1095, -8), (key1101, 4), (key1166, 12), (key1173, -8), (key1229, 4), (key1246, -4)]

theorem rowCheck13537 : row13537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13537 := by decide +kernel

theorem rowEval13537 (x : Key → ℝ) : Integer.Sparse.eval row13537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13537, Integer.Sparse.eval_collectBalanced, rawRowCheck13537]

def rawRow13538 : Integer.Sparse Key := [(key1246, -2), (key1173, -2), (key1173, -2), (key1166, 6), (key1246, -2), (key1173, -2), (key1173, -2), (key1229, 2), (key1101, 2), (key1229, 2), (key987, 2), (key1101, 2), (key987, 2), (key1095, -2), (key1095, -2), (key981, -2), (key1166, 6), (key1095, -2), (key1095, -2), (key981, -2)]

theorem rawRowCheck13538 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13538 := by decide +kernel

def row13538 : Integer.Sparse Key := [(key981, -4), (key987, 4), (key1095, -8), (key1101, 4), (key1166, 12), (key1173, -8), (key1229, 4), (key1246, -4)]

theorem rowCheck13538 : row13538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13538 := by decide +kernel

theorem rowEval13538 (x : Key → ℝ) : Integer.Sparse.eval row13538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13538, Integer.Sparse.eval_collectBalanced, rawRowCheck13538]

def rawRow13539 : Integer.Sparse Key := [(key1115, 6), (key1037, -2), (key1124, -2), (key1124, -2), (key1115, 6), (key1002, -2), (key1151, -2), (key1151, -2), (key1037, -2), (key1124, -2), (key1124, -2), (key1002, -2), (key1151, -2), (key1151, -2), (key1016, 2), (key1016, 2), (key1072, 2), (key1072, 2), (key1167, 2), (key1167, 2)]

theorem rawRowCheck13539 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form3 = rawRow13539 := by decide +kernel

def row13539 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, -4), (key1072, 4), (key1115, 12), (key1124, -8), (key1151, -8), (key1167, 4)]

theorem rowCheck13539 : row13539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13539 := by decide +kernel

theorem rowEval13539 (x : Key → ℝ) : Integer.Sparse.eval row13539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13539, Integer.Sparse.eval_collectBalanced, rawRowCheck13539]

def rawRow13540 : Integer.Sparse Key := [(key1115, 6), (key1124, -2), (key1037, -2), (key1124, -2), (key1115, 6), (key1151, -2), (key1002, -2), (key1151, -2), (key1124, -2), (key1037, -2), (key1124, -2), (key1151, -2), (key1002, -2), (key1151, -2), (key1072, 2), (key1167, 2), (key1016, 2), (key1167, 2), (key1016, 2), (key1072, 2)]

theorem rawRowCheck13540 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form3 = rawRow13540 := by decide +kernel

def row13540 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, -4), (key1072, 4), (key1115, 12), (key1124, -8), (key1151, -8), (key1167, 4)]

theorem rowCheck13540 : row13540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13540 := by decide +kernel

theorem rowEval13540 (x : Key → ℝ) : Integer.Sparse.eval row13540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13540, Integer.Sparse.eval_collectBalanced, rawRowCheck13540]

def rawRow13541 : Integer.Sparse Key := [(key1115, 6), (key1124, -2), (key1124, -2), (key1037, -2), (key1115, 6), (key1151, -2), (key1151, -2), (key1002, -2), (key1124, -2), (key1124, -2), (key1037, -2), (key1151, -2), (key1151, -2), (key1002, -2), (key1167, 2), (key1072, 2), (key1167, 2), (key1016, 2), (key1072, 2), (key1016, 2)]

theorem rawRowCheck13541 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form3 = rawRow13541 := by decide +kernel

def row13541 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, -4), (key1072, 4), (key1115, 12), (key1124, -8), (key1151, -8), (key1167, 4)]

theorem rowCheck13541 : row13541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13541 := by decide +kernel

theorem rowEval13541 (x : Key → ℝ) : Integer.Sparse.eval row13541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13541, Integer.Sparse.eval_collectBalanced, rawRowCheck13541]

def rawRow13542 : Integer.Sparse Key := [(key1124, 6), (key1037, -2), (key1115, -2), (key1124, -2), (key1151, 6), (key1002, -2), (key1115, -2), (key1151, -2), (key1072, -2), (key1151, -2), (key1167, -2), (key1016, -2), (key1124, -2), (key1167, -2), (key1002, 2), (key1016, 2), (key1037, 2), (key1072, 2), (key1124, 2), (key1151, 2)]

theorem rawRowCheck13542 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form3 = rawRow13542 := by decide +kernel

def row13542 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

theorem rowCheck13542 : row13542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13542 := by decide +kernel

theorem rowEval13542 (x : Key → ℝ) : Integer.Sparse.eval row13542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13542, Integer.Sparse.eval_collectBalanced, rawRowCheck13542]

def rawRow13543 : Integer.Sparse Key := [(key1124, 6), (key1037, -2), (key1124, -2), (key1115, -2), (key1151, 6), (key1002, -2), (key1151, -2), (key1115, -2), (key1072, -2), (key1167, -2), (key1151, -2), (key1016, -2), (key1167, -2), (key1124, -2), (key1016, 2), (key1002, 2), (key1072, 2), (key1037, 2), (key1151, 2), (key1124, 2)]

theorem rawRowCheck13543 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form3 = rawRow13543 := by decide +kernel

def row13543 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

theorem rowCheck13543 : row13543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13543 := by decide +kernel

theorem rowEval13543 (x : Key → ℝ) : Integer.Sparse.eval row13543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13543, Integer.Sparse.eval_collectBalanced, rawRowCheck13543]

def rawRow13544 : Integer.Sparse Key := [(key1124, 6), (key1115, -2), (key1037, -2), (key1124, -2), (key1151, 6), (key1115, -2), (key1002, -2), (key1151, -2), (key1151, -2), (key1072, -2), (key1167, -2), (key1124, -2), (key1016, -2), (key1167, -2), (key1037, 2), (key1124, 2), (key1002, 2), (key1151, 2), (key1016, 2), (key1072, 2)]

theorem rawRowCheck13544 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form3 = rawRow13544 := by decide +kernel

def row13544 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

theorem rowCheck13544 : row13544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13544 := by decide +kernel

theorem rowEval13544 (x : Key → ℝ) : Integer.Sparse.eval row13544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13544, Integer.Sparse.eval_collectBalanced, rawRowCheck13544]

def rawRow13545 : Integer.Sparse Key := [(key1124, 6), (key1115, -2), (key1124, -2), (key1037, -2), (key1151, 6), (key1115, -2), (key1151, -2), (key1002, -2), (key1151, -2), (key1167, -2), (key1072, -2), (key1124, -2), (key1167, -2), (key1016, -2), (key1124, 2), (key1037, 2), (key1151, 2), (key1002, 2), (key1072, 2), (key1016, 2)]

theorem rawRowCheck13545 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form3 = rawRow13545 := by decide +kernel

def row13545 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

theorem rowCheck13545 : row13545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13545 := by decide +kernel

theorem rowEval13545 (x : Key → ℝ) : Integer.Sparse.eval row13545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13545, Integer.Sparse.eval_collectBalanced, rawRowCheck13545]

def rawRow13546 : Integer.Sparse Key := [(key1124, 6), (key1124, -2), (key1037, -2), (key1115, -2), (key1151, 6), (key1151, -2), (key1002, -2), (key1115, -2), (key1167, -2), (key1072, -2), (key1151, -2), (key1167, -2), (key1016, -2), (key1124, -2), (key1072, 2), (key1151, 2), (key1016, 2), (key1124, 2), (key1002, 2), (key1037, 2)]

theorem rawRowCheck13546 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form3 = rawRow13546 := by decide +kernel

def row13546 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

theorem rowCheck13546 : row13546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13546 := by decide +kernel

theorem rowEval13546 (x : Key → ℝ) : Integer.Sparse.eval row13546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13546, Integer.Sparse.eval_collectBalanced, rawRowCheck13546]

def rawRow13547 : Integer.Sparse Key := [(key1124, 6), (key1124, -2), (key1115, -2), (key1037, -2), (key1151, 6), (key1151, -2), (key1115, -2), (key1002, -2), (key1167, -2), (key1151, -2), (key1072, -2), (key1167, -2), (key1124, -2), (key1016, -2), (key1151, 2), (key1072, 2), (key1124, 2), (key1016, 2), (key1037, 2), (key1002, 2)]

theorem rawRowCheck13547 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form3 = rawRow13547 := by decide +kernel

def row13547 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

theorem rowCheck13547 : row13547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13547 := by decide +kernel

theorem rowEval13547 (x : Key → ℝ) : Integer.Sparse.eval row13547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13547, Integer.Sparse.eval_collectBalanced, rawRowCheck13547]

def rawRow13548 : Integer.Sparse Key := [(key1151, 6), (key1072, -2), (key1151, -2), (key1167, -2), (key1124, 6), (key1016, -2), (key1124, -2), (key1167, -2), (key1037, -2), (key1115, -2), (key1124, -2), (key1002, -2), (key1115, -2), (key1151, -2), (key1002, 2), (key1016, 2), (key1037, 2), (key1072, 2), (key1124, 2), (key1151, 2)]

theorem rawRowCheck13548 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form3 = rawRow13548 := by decide +kernel

def row13548 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

theorem rowCheck13548 : row13548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13548 := by decide +kernel

theorem rowEval13548 (x : Key → ℝ) : Integer.Sparse.eval row13548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13548, Integer.Sparse.eval_collectBalanced, rawRowCheck13548]

def rawRow13549 : Integer.Sparse Key := [(key1151, 6), (key1072, -2), (key1167, -2), (key1151, -2), (key1124, 6), (key1016, -2), (key1167, -2), (key1124, -2), (key1037, -2), (key1124, -2), (key1115, -2), (key1002, -2), (key1151, -2), (key1115, -2), (key1016, 2), (key1002, 2), (key1072, 2), (key1037, 2), (key1151, 2), (key1124, 2)]

theorem rawRowCheck13549 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form3 = rawRow13549 := by decide +kernel

def row13549 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

theorem rowCheck13549 : row13549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13549 := by decide +kernel

theorem rowEval13549 (x : Key → ℝ) : Integer.Sparse.eval row13549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13549, Integer.Sparse.eval_collectBalanced, rawRowCheck13549]

def rawRow13550 : Integer.Sparse Key := [(key1151, 6), (key1151, -2), (key1072, -2), (key1167, -2), (key1124, 6), (key1124, -2), (key1016, -2), (key1167, -2), (key1115, -2), (key1037, -2), (key1124, -2), (key1115, -2), (key1002, -2), (key1151, -2), (key1037, 2), (key1124, 2), (key1002, 2), (key1151, 2), (key1016, 2), (key1072, 2)]

theorem rawRowCheck13550 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form3 = rawRow13550 := by decide +kernel

def row13550 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

theorem rowCheck13550 : row13550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13550 := by decide +kernel

theorem rowEval13550 (x : Key → ℝ) : Integer.Sparse.eval row13550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13550, Integer.Sparse.eval_collectBalanced, rawRowCheck13550]

def rawRow13551 : Integer.Sparse Key := [(key1151, 6), (key1151, -2), (key1167, -2), (key1072, -2), (key1124, 6), (key1124, -2), (key1167, -2), (key1016, -2), (key1115, -2), (key1124, -2), (key1037, -2), (key1115, -2), (key1151, -2), (key1002, -2), (key1124, 2), (key1037, 2), (key1151, 2), (key1002, 2), (key1072, 2), (key1016, 2)]

theorem rawRowCheck13551 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form3 = rawRow13551 := by decide +kernel

def row13551 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

theorem rowCheck13551 : row13551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13551 := by decide +kernel

theorem rowEval13551 (x : Key → ℝ) : Integer.Sparse.eval row13551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13551, Integer.Sparse.eval_collectBalanced, rawRowCheck13551]

def rawRow13552 : Integer.Sparse Key := [(key1151, 6), (key1167, -2), (key1072, -2), (key1151, -2), (key1124, 6), (key1167, -2), (key1016, -2), (key1124, -2), (key1124, -2), (key1037, -2), (key1115, -2), (key1151, -2), (key1002, -2), (key1115, -2), (key1072, 2), (key1151, 2), (key1016, 2), (key1124, 2), (key1002, 2), (key1037, 2)]

theorem rawRowCheck13552 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form3 = rawRow13552 := by decide +kernel

def row13552 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

theorem rowCheck13552 : row13552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13552 := by decide +kernel

theorem rowEval13552 (x : Key → ℝ) : Integer.Sparse.eval row13552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13552, Integer.Sparse.eval_collectBalanced, rawRowCheck13552]

def rawRow13553 : Integer.Sparse Key := [(key1151, 6), (key1167, -2), (key1151, -2), (key1072, -2), (key1124, 6), (key1167, -2), (key1124, -2), (key1016, -2), (key1124, -2), (key1115, -2), (key1037, -2), (key1151, -2), (key1115, -2), (key1002, -2), (key1151, 2), (key1072, 2), (key1124, 2), (key1016, 2), (key1037, 2), (key1002, 2)]

theorem rawRowCheck13553 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form3 = rawRow13553 := by decide +kernel

def row13553 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

theorem rowCheck13553 : row13553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13553 := by decide +kernel

theorem rowEval13553 (x : Key → ℝ) : Integer.Sparse.eval row13553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13553, Integer.Sparse.eval_collectBalanced, rawRowCheck13553]

def rawRow13554 : Integer.Sparse Key := [(key1167, 6), (key1072, -2), (key1151, -2), (key1151, -2), (key1167, 6), (key1016, -2), (key1124, -2), (key1124, -2), (key1072, -2), (key1151, -2), (key1151, -2), (key1016, -2), (key1124, -2), (key1124, -2), (key1002, 2), (key1002, 2), (key1037, 2), (key1037, 2), (key1115, 2), (key1115, 2)]

theorem rawRowCheck13554 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form3 = rawRow13554 := by decide +kernel

def row13554 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, -4), (key1115, 4), (key1124, -8), (key1151, -8), (key1167, 12)]

theorem rowCheck13554 : row13554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13554 := by decide +kernel

theorem rowEval13554 (x : Key → ℝ) : Integer.Sparse.eval row13554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13554, Integer.Sparse.eval_collectBalanced, rawRowCheck13554]

def rawRow13555 : Integer.Sparse Key := [(key1167, 6), (key1151, -2), (key1072, -2), (key1151, -2), (key1167, 6), (key1124, -2), (key1016, -2), (key1124, -2), (key1151, -2), (key1072, -2), (key1151, -2), (key1124, -2), (key1016, -2), (key1124, -2), (key1037, 2), (key1115, 2), (key1002, 2), (key1115, 2), (key1002, 2), (key1037, 2)]

theorem rawRowCheck13555 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form3 = rawRow13555 := by decide +kernel

def row13555 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, -4), (key1115, 4), (key1124, -8), (key1151, -8), (key1167, 12)]

theorem rowCheck13555 : row13555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13555 := by decide +kernel

theorem rowEval13555 (x : Key → ℝ) : Integer.Sparse.eval row13555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13555, Integer.Sparse.eval_collectBalanced, rawRowCheck13555]

def rawRow13556 : Integer.Sparse Key := [(key1167, 6), (key1151, -2), (key1151, -2), (key1072, -2), (key1167, 6), (key1124, -2), (key1124, -2), (key1016, -2), (key1151, -2), (key1151, -2), (key1072, -2), (key1124, -2), (key1124, -2), (key1016, -2), (key1115, 2), (key1037, 2), (key1115, 2), (key1002, 2), (key1037, 2), (key1002, 2)]

theorem rawRowCheck13556 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form3 = rawRow13556 := by decide +kernel

def row13556 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, -4), (key1115, 4), (key1124, -8), (key1151, -8), (key1167, 12)]

theorem rowCheck13556 : row13556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13556 := by decide +kernel

theorem rowEval13556 (x : Key → ℝ) : Integer.Sparse.eval row13556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13556, Integer.Sparse.eval_collectBalanced, rawRowCheck13556]

def rawRow13557 : Integer.Sparse Key := [(key92, -2), (key92, -2), (key168, -2), (key95, 6), (key92, -2), (key92, -2), (key168, -2), (key9, 2), (key9, 2), (key153, 2), (key153, 2), (key188, 2), (key188, 2), (key12, -2), (key157, -2), (key157, -2), (key95, 6), (key12, -2), (key157, -2), (key157, -2)]

theorem rawRowCheck13557 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form4 = rawRow13557 := by decide +kernel

def row13557 : Integer.Sparse Key := [(key9, 4), (key12, -4), (key92, -8), (key95, 12), (key153, 4), (key157, -8), (key168, -4), (key188, 4)]

theorem rowCheck13557 : row13557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13557 := by decide +kernel

theorem rowEval13557 (x : Key → ℝ) : Integer.Sparse.eval row13557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13557, Integer.Sparse.eval_collectBalanced, rawRowCheck13557]

def rawRow13558 : Integer.Sparse Key := [(key92, -2), (key168, -2), (key92, -2), (key95, 6), (key92, -2), (key168, -2), (key92, -2), (key153, 2), (key188, 2), (key9, 2), (key188, 2), (key9, 2), (key153, 2), (key157, -2), (key12, -2), (key157, -2), (key95, 6), (key157, -2), (key12, -2), (key157, -2)]

theorem rawRowCheck13558 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form4 = rawRow13558 := by decide +kernel

def row13558 : Integer.Sparse Key := [(key9, 4), (key12, -4), (key92, -8), (key95, 12), (key153, 4), (key157, -8), (key168, -4), (key188, 4)]

theorem rowCheck13558 : row13558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13558 := by decide +kernel

theorem rowEval13558 (x : Key → ℝ) : Integer.Sparse.eval row13558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13558, Integer.Sparse.eval_collectBalanced, rawRowCheck13558]

def rawRow13559 : Integer.Sparse Key := [(key168, -2), (key92, -2), (key92, -2), (key95, 6), (key168, -2), (key92, -2), (key92, -2), (key188, 2), (key153, 2), (key188, 2), (key9, 2), (key153, 2), (key9, 2), (key157, -2), (key157, -2), (key12, -2), (key95, 6), (key157, -2), (key157, -2), (key12, -2)]

theorem rawRowCheck13559 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form4 = rawRow13559 := by decide +kernel

def row13559 : Integer.Sparse Key := [(key9, 4), (key12, -4), (key92, -8), (key95, 12), (key153, 4), (key157, -8), (key168, -4), (key188, 4)]

theorem rowCheck13559 : row13559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13559 := by decide +kernel

theorem rowEval13559 (x : Key → ℝ) : Integer.Sparse.eval row13559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13559, Integer.Sparse.eval_collectBalanced, rawRowCheck13559]

def rawRow13560 : Integer.Sparse Key := [(key92, -2), (key95, -2), (key168, -2), (key92, 6), (key153, -2), (key157, -2), (key188, -2), (key9, 2), (key12, 2), (key92, 2), (key157, 2), (key168, 2), (key188, 2), (key9, -2), (key92, -2), (key153, -2), (key157, 6), (key12, -2), (key95, -2), (key157, -2)]

theorem rawRowCheck13560 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form4 = rawRow13560 := by decide +kernel

def row13560 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

theorem rowCheck13560 : row13560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13560 := by decide +kernel

theorem rowEval13560 (x : Key → ℝ) : Integer.Sparse.eval row13560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13560, Integer.Sparse.eval_collectBalanced, rawRowCheck13560]

def rawRow13561 : Integer.Sparse Key := [(key95, -2), (key92, -2), (key168, -2), (key92, 6), (key157, -2), (key153, -2), (key188, -2), (key12, 2), (key9, 2), (key157, 2), (key92, 2), (key188, 2), (key168, 2), (key9, -2), (key153, -2), (key92, -2), (key157, 6), (key12, -2), (key157, -2), (key95, -2)]

theorem rawRowCheck13561 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form4 = rawRow13561 := by decide +kernel

def row13561 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

theorem rowCheck13561 : row13561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13561 := by decide +kernel

theorem rowEval13561 (x : Key → ℝ) : Integer.Sparse.eval row13561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13561, Integer.Sparse.eval_collectBalanced, rawRowCheck13561]

def rawRow13562 : Integer.Sparse Key := [(key92, -2), (key168, -2), (key95, -2), (key92, 6), (key153, -2), (key188, -2), (key157, -2), (key92, 2), (key168, 2), (key9, 2), (key188, 2), (key12, 2), (key157, 2), (key92, -2), (key9, -2), (key153, -2), (key157, 6), (key95, -2), (key12, -2), (key157, -2)]

theorem rawRowCheck13562 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form4 = rawRow13562 := by decide +kernel

def row13562 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

theorem rowCheck13562 : row13562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13562 := by decide +kernel

theorem rowEval13562 (x : Key → ℝ) : Integer.Sparse.eval row13562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13562, Integer.Sparse.eval_collectBalanced, rawRowCheck13562]

def rawRow13563 : Integer.Sparse Key := [(key168, -2), (key92, -2), (key95, -2), (key92, 6), (key188, -2), (key153, -2), (key157, -2), (key168, 2), (key92, 2), (key188, 2), (key9, 2), (key157, 2), (key12, 2), (key92, -2), (key153, -2), (key9, -2), (key157, 6), (key95, -2), (key157, -2), (key12, -2)]

theorem rawRowCheck13563 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form4 = rawRow13563 := by decide +kernel

def row13563 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

theorem rowCheck13563 : row13563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13563 := by decide +kernel

theorem rowEval13563 (x : Key → ℝ) : Integer.Sparse.eval row13563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13563, Integer.Sparse.eval_collectBalanced, rawRowCheck13563]

def rawRow13564 : Integer.Sparse Key := [(key95, -2), (key168, -2), (key92, -2), (key92, 6), (key157, -2), (key188, -2), (key153, -2), (key157, 2), (key188, 2), (key12, 2), (key168, 2), (key9, 2), (key92, 2), (key153, -2), (key9, -2), (key92, -2), (key157, 6), (key157, -2), (key12, -2), (key95, -2)]

theorem rawRowCheck13564 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form4 = rawRow13564 := by decide +kernel

def row13564 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

theorem rowCheck13564 : row13564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13564 := by decide +kernel

theorem rowEval13564 (x : Key → ℝ) : Integer.Sparse.eval row13564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13564, Integer.Sparse.eval_collectBalanced, rawRowCheck13564]

def rawRow13565 : Integer.Sparse Key := [(key168, -2), (key95, -2), (key92, -2), (key92, 6), (key188, -2), (key157, -2), (key153, -2), (key188, 2), (key157, 2), (key168, 2), (key12, 2), (key92, 2), (key9, 2), (key153, -2), (key92, -2), (key9, -2), (key157, 6), (key157, -2), (key95, -2), (key12, -2)]

theorem rawRowCheck13565 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form4 = rawRow13565 := by decide +kernel

def row13565 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

theorem rowCheck13565 : row13565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13565 := by decide +kernel

theorem rowEval13565 (x : Key → ℝ) : Integer.Sparse.eval row13565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13565, Integer.Sparse.eval_collectBalanced, rawRowCheck13565]

def rawRow13566 : Integer.Sparse Key := [(key153, -2), (key157, -2), (key188, -2), (key157, 6), (key92, -2), (key95, -2), (key168, -2), (key9, 2), (key12, 2), (key92, 2), (key157, 2), (key168, 2), (key188, 2), (key12, -2), (key95, -2), (key157, -2), (key92, 6), (key9, -2), (key92, -2), (key153, -2)]

theorem rawRowCheck13566 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form4 = rawRow13566 := by decide +kernel

def row13566 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

theorem rowCheck13566 : row13566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13566 := by decide +kernel

theorem rowEval13566 (x : Key → ℝ) : Integer.Sparse.eval row13566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13566, Integer.Sparse.eval_collectBalanced, rawRowCheck13566]

def rawRow13567 : Integer.Sparse Key := [(key157, -2), (key153, -2), (key188, -2), (key157, 6), (key95, -2), (key92, -2), (key168, -2), (key12, 2), (key9, 2), (key157, 2), (key92, 2), (key188, 2), (key168, 2), (key12, -2), (key157, -2), (key95, -2), (key92, 6), (key9, -2), (key153, -2), (key92, -2)]

theorem rawRowCheck13567 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form4 = rawRow13567 := by decide +kernel

def row13567 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

theorem rowCheck13567 : row13567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13567 := by decide +kernel

theorem rowEval13567 (x : Key → ℝ) : Integer.Sparse.eval row13567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13567, Integer.Sparse.eval_collectBalanced, rawRowCheck13567]

end MUB6.Certificate.GramRows

end OAI
