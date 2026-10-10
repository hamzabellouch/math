import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow6016 : Integer.Sparse Key := [(key1622, -1), (key1815, -1), (key1657, 2), (key1572, -1), (key1787, -1), (key1423, 2), (key1812, 2), (key1454, -1), (key1654, -1), (key1568, 2), (key1419, -1), (key1617, -1), (key1631, 1), (key1823, 1), (key1665, -2), (key1545, 1), (key1771, 1), (key1315, -2), (key1812, -2), (key1336, 1), (key1654, 1), (key1541, -2), (key1311, 1), (key1617, 1), (key1442, -1), (key1823, -1), (key1464, 1), (key1665, 1), (key1324, 1), (key1815, 1), (key1343, -1), (key1657, -1), (key1390, -1), (key1771, -1), (key1295, 1), (key1787, 1), (key1386, 1), (key1541, 1), (key1291, -1), (key1568, -1)]

theorem rawRowCheck6016 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form2 = rawRow6016 := by decide +kernel

def row6016 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck6016 : row6016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6016 := by decide +kernel

theorem rowEval6016 (x : Key → ℝ) : Integer.Sparse.eval row6016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6016, Integer.Sparse.eval_collectBalanced, rawRowCheck6016]

def rawRow6017 : Integer.Sparse Key := [(key1815, -1), (key1622, -1), (key1657, 2), (key1787, -1), (key1572, -1), (key1812, 2), (key1423, 2), (key1654, -1), (key1454, -1), (key1568, 2), (key1617, -1), (key1419, -1), (key1823, 1), (key1631, 1), (key1665, -2), (key1771, 1), (key1545, 1), (key1812, -2), (key1315, -2), (key1654, 1), (key1336, 1), (key1541, -2), (key1617, 1), (key1311, 1), (key1823, -1), (key1442, -1), (key1665, 1), (key1464, 1), (key1815, 1), (key1324, 1), (key1657, -1), (key1343, -1), (key1771, -1), (key1390, -1), (key1787, 1), (key1295, 1), (key1541, 1), (key1386, 1), (key1568, -1), (key1291, -1)]

theorem rawRowCheck6017 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form2 = rawRow6017 := by decide +kernel

def row6017 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

theorem rowCheck6017 : row6017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6017 := by decide +kernel

theorem rowEval6017 (x : Key → ℝ) : Integer.Sparse.eval row6017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6017, Integer.Sparse.eval_collectBalanced, rawRowCheck6017]

def rawRow6018 : Integer.Sparse Key := [(key25, -4), (key25, 2), (key26, 2), (key37, 2), (key39, 2), (key39, -4), (key50, 2), (key50, -1), (key51, -1), (key107, 2), (key107, -1), (key173, -1), (key117, -1), (key119, -1), (key117, -1), (key177, -1), (key119, 2), (key177, 2), (key76, -1), (key79, -1), (key79, 2), (key139, -1), (key142, -1), (key139, 2), (key182, 2), (key142, -1), (key182, -1), (key159, 2), (key159, -1), (key190, -1)]

theorem rawRowCheck6018 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form3 = rawRow6018 := by decide +kernel

def row6018 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6018 : row6018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6018 := by decide +kernel

theorem rowEval6018 (x : Key → ℝ) : Integer.Sparse.eval row6018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6018, Integer.Sparse.eval_collectBalanced, rawRowCheck6018]

def rawRow6019 : Integer.Sparse Key := [(key25, -4), (key26, 2), (key25, 2), (key39, 2), (key37, 2), (key39, -4), (key50, 2), (key51, -1), (key50, -1), (key107, 2), (key173, -1), (key107, -1), (key119, -1), (key117, -1), (key177, -1), (key117, -1), (key177, 2), (key119, 2), (key79, -1), (key76, -1), (key79, 2), (key142, -1), (key139, -1), (key182, 2), (key139, 2), (key182, -1), (key142, -1), (key159, 2), (key190, -1), (key159, -1)]

theorem rawRowCheck6019 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form3 = rawRow6019 := by decide +kernel

def row6019 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6019 : row6019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6019 := by decide +kernel

theorem rowEval6019 (x : Key → ℝ) : Integer.Sparse.eval row6019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6019, Integer.Sparse.eval_collectBalanced, rawRowCheck6019]

def rawRow6020 : Integer.Sparse Key := [(key26, -4), (key25, 2), (key25, 2), (key39, 2), (key39, 2), (key37, -4), (key51, 2), (key50, -1), (key50, -1), (key173, 2), (key107, -1), (key107, -1), (key177, -1), (key177, -1), (key119, -1), (key119, -1), (key117, 2), (key117, 2), (key79, -1), (key79, -1), (key76, 2), (key182, -1), (key182, -1), (key142, 2), (key142, 2), (key139, -1), (key139, -1), (key190, 2), (key159, -1), (key159, -1)]

theorem rawRowCheck6020 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form3 = rawRow6020 := by decide +kernel

def row6020 : Integer.Sparse Key := [(key25, 4), (key26, -4), (key37, -4), (key39, 4), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, -2), (key117, 4), (key119, -2), (key139, -2), (key142, 4), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

theorem rowCheck6020 : row6020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6020 := by decide +kernel

theorem rowEval6020 (x : Key → ℝ) : Integer.Sparse.eval row6020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6020, Integer.Sparse.eval_collectBalanced, rawRowCheck6020]

def rawRow6021 : Integer.Sparse Key := [(key25, -4), (key37, 2), (key39, 2), (key25, 2), (key26, 2), (key39, -4), (key107, 2), (key117, -1), (key119, -1), (key50, 2), (key117, -1), (key177, -1), (key50, -1), (key51, -1), (key107, -1), (key173, -1), (key119, 2), (key177, 2), (key139, -1), (key142, -1), (key159, 2), (key76, -1), (key79, -1), (key139, 2), (key182, 2), (key159, -1), (key190, -1), (key79, 2), (key142, -1), (key182, -1)]

theorem rawRowCheck6021 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form3 = rawRow6021 := by decide +kernel

def row6021 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6021 : row6021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6021 := by decide +kernel

theorem rowEval6021 (x : Key → ℝ) : Integer.Sparse.eval row6021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6021, Integer.Sparse.eval_collectBalanced, rawRowCheck6021]

def rawRow6022 : Integer.Sparse Key := [(key25, -4), (key39, 2), (key37, 2), (key26, 2), (key25, 2), (key39, -4), (key107, 2), (key119, -1), (key117, -1), (key50, 2), (key177, -1), (key117, -1), (key51, -1), (key50, -1), (key173, -1), (key107, -1), (key177, 2), (key119, 2), (key142, -1), (key139, -1), (key159, 2), (key79, -1), (key76, -1), (key182, 2), (key139, 2), (key190, -1), (key159, -1), (key79, 2), (key182, -1), (key142, -1)]

theorem rawRowCheck6022 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form3 = rawRow6022 := by decide +kernel

def row6022 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6022 : row6022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6022 := by decide +kernel

theorem rowEval6022 (x : Key → ℝ) : Integer.Sparse.eval row6022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6022, Integer.Sparse.eval_collectBalanced, rawRowCheck6022]

def rawRow6023 : Integer.Sparse Key := [(key37, -4), (key25, 2), (key39, 2), (key25, 2), (key39, 2), (key26, -4), (key117, 2), (key107, -1), (key119, -1), (key117, 2), (key50, -1), (key177, -1), (key107, -1), (key119, -1), (key50, -1), (key177, -1), (key51, 2), (key173, 2), (key139, -1), (key159, -1), (key142, 2), (key139, -1), (key159, -1), (key76, 2), (key190, 2), (key79, -1), (key182, -1), (key142, 2), (key79, -1), (key182, -1)]

theorem rawRowCheck6023 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form3 = rawRow6023 := by decide +kernel

def row6023 : Integer.Sparse Key := [(key25, 4), (key26, -4), (key37, -4), (key39, 4), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, -2), (key117, 4), (key119, -2), (key139, -2), (key142, 4), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

theorem rowCheck6023 : row6023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6023 := by decide +kernel

theorem rowEval6023 (x : Key → ℝ) : Integer.Sparse.eval row6023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6023, Integer.Sparse.eval_collectBalanced, rawRowCheck6023]

def rawRow6024 : Integer.Sparse Key := [(key37, -4), (key39, 2), (key25, 2), (key39, 2), (key25, 2), (key26, -4), (key117, 2), (key119, -1), (key107, -1), (key117, 2), (key177, -1), (key50, -1), (key119, -1), (key107, -1), (key177, -1), (key50, -1), (key173, 2), (key51, 2), (key159, -1), (key139, -1), (key142, 2), (key159, -1), (key139, -1), (key190, 2), (key76, 2), (key182, -1), (key79, -1), (key142, 2), (key182, -1), (key79, -1)]

theorem rawRowCheck6024 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form3 = rawRow6024 := by decide +kernel

def row6024 : Integer.Sparse Key := [(key25, 4), (key26, -4), (key37, -4), (key39, 4), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, -2), (key117, 4), (key119, -2), (key139, -2), (key142, 4), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

theorem rowCheck6024 : row6024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6024 := by decide +kernel

theorem rowEval6024 (x : Key → ℝ) : Integer.Sparse.eval row6024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6024, Integer.Sparse.eval_collectBalanced, rawRowCheck6024]

def rawRow6025 : Integer.Sparse Key := [(key39, -4), (key25, 2), (key37, 2), (key26, 2), (key39, 2), (key25, -4), (key119, 2), (key107, -1), (key117, -1), (key177, 2), (key50, -1), (key117, -1), (key173, -1), (key177, -1), (key51, -1), (key119, -1), (key50, 2), (key107, 2), (key142, -1), (key159, -1), (key139, 2), (key182, -1), (key190, -1), (key79, 2), (key159, 2), (key76, -1), (key139, -1), (key182, 2), (key79, -1), (key142, -1)]

theorem rawRowCheck6025 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form3 = rawRow6025 := by decide +kernel

def row6025 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6025 : row6025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6025 := by decide +kernel

theorem rowEval6025 (x : Key → ℝ) : Integer.Sparse.eval row6025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6025, Integer.Sparse.eval_collectBalanced, rawRowCheck6025]

def rawRow6026 : Integer.Sparse Key := [(key39, -4), (key37, 2), (key25, 2), (key39, 2), (key26, 2), (key25, -4), (key119, 2), (key117, -1), (key107, -1), (key177, 2), (key117, -1), (key50, -1), (key177, -1), (key173, -1), (key119, -1), (key51, -1), (key107, 2), (key50, 2), (key159, -1), (key142, -1), (key139, 2), (key190, -1), (key182, -1), (key159, 2), (key79, 2), (key139, -1), (key76, -1), (key182, 2), (key142, -1), (key79, -1)]

theorem rawRowCheck6026 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form3 = rawRow6026 := by decide +kernel

def row6026 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6026 : row6026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6026 := by decide +kernel

theorem rowEval6026 (x : Key → ℝ) : Integer.Sparse.eval row6026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6026, Integer.Sparse.eval_collectBalanced, rawRowCheck6026]

def rawRow6027 : Integer.Sparse Key := [(key26, -4), (key39, 2), (key39, 2), (key25, 2), (key25, 2), (key37, -4), (key173, 2), (key177, -1), (key177, -1), (key51, 2), (key119, -1), (key119, -1), (key50, -1), (key50, -1), (key107, -1), (key107, -1), (key117, 2), (key117, 2), (key182, -1), (key182, -1), (key190, 2), (key79, -1), (key79, -1), (key142, 2), (key142, 2), (key159, -1), (key159, -1), (key76, 2), (key139, -1), (key139, -1)]

theorem rawRowCheck6027 : GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form3 = rawRow6027 := by decide +kernel

def row6027 : Integer.Sparse Key := [(key25, 4), (key26, -4), (key37, -4), (key39, 4), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, -2), (key117, 4), (key119, -2), (key139, -2), (key142, 4), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

theorem rowCheck6027 : row6027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6027 := by decide +kernel

theorem rowEval6027 (x : Key → ℝ) : Integer.Sparse.eval row6027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6027, Integer.Sparse.eval_collectBalanced, rawRowCheck6027]

def rawRow6028 : Integer.Sparse Key := [(key39, -4), (key26, 2), (key39, 2), (key25, 2), (key37, 2), (key25, -4), (key177, 2), (key173, -1), (key177, -1), (key119, 2), (key51, -1), (key119, -1), (key107, -1), (key117, -1), (key50, -1), (key117, -1), (key50, 2), (key107, 2), (key182, -1), (key190, -1), (key182, 2), (key142, -1), (key159, -1), (key79, 2), (key159, 2), (key79, -1), (key142, -1), (key139, 2), (key76, -1), (key139, -1)]

theorem rawRowCheck6028 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form3 = rawRow6028 := by decide +kernel

def row6028 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6028 : row6028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6028 := by decide +kernel

theorem rowEval6028 (x : Key → ℝ) : Integer.Sparse.eval row6028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6028, Integer.Sparse.eval_collectBalanced, rawRowCheck6028]

def rawRow6029 : Integer.Sparse Key := [(key39, -4), (key39, 2), (key26, 2), (key37, 2), (key25, 2), (key25, -4), (key177, 2), (key177, -1), (key173, -1), (key119, 2), (key119, -1), (key51, -1), (key117, -1), (key107, -1), (key117, -1), (key50, -1), (key107, 2), (key50, 2), (key190, -1), (key182, -1), (key182, 2), (key159, -1), (key142, -1), (key159, 2), (key79, 2), (key142, -1), (key79, -1), (key139, 2), (key139, -1), (key76, -1)]

theorem rawRowCheck6029 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form3 = rawRow6029 := by decide +kernel

def row6029 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6029 : row6029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6029 := by decide +kernel

theorem rowEval6029 (x : Key → ℝ) : Integer.Sparse.eval row6029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6029, Integer.Sparse.eval_collectBalanced, rawRowCheck6029]

def rawRow6030 : Integer.Sparse Key := [(key50, -4), (key50, 2), (key51, 2), (key76, 2), (key79, 2), (key79, -4), (key25, 2), (key25, -1), (key26, -1), (key107, 2), (key107, -1), (key173, -1), (key139, -1), (key142, -1), (key139, -1), (key182, -1), (key142, 2), (key182, 2), (key37, -1), (key39, -1), (key39, 2), (key117, -1), (key119, -1), (key117, 2), (key177, 2), (key119, -1), (key177, -1), (key159, 2), (key159, -1), (key190, -1)]

theorem rawRowCheck6030 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form3 = rawRow6030 := by decide +kernel

def row6030 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6030 : row6030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6030 := by decide +kernel

theorem rowEval6030 (x : Key → ℝ) : Integer.Sparse.eval row6030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6030, Integer.Sparse.eval_collectBalanced, rawRowCheck6030]

def rawRow6031 : Integer.Sparse Key := [(key50, -4), (key51, 2), (key50, 2), (key79, 2), (key76, 2), (key79, -4), (key25, 2), (key26, -1), (key25, -1), (key107, 2), (key173, -1), (key107, -1), (key142, -1), (key139, -1), (key182, -1), (key139, -1), (key182, 2), (key142, 2), (key39, -1), (key37, -1), (key39, 2), (key119, -1), (key117, -1), (key177, 2), (key117, 2), (key177, -1), (key119, -1), (key159, 2), (key190, -1), (key159, -1)]

theorem rawRowCheck6031 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form3 = rawRow6031 := by decide +kernel

def row6031 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6031 : row6031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6031 := by decide +kernel

theorem rowEval6031 (x : Key → ℝ) : Integer.Sparse.eval row6031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6031, Integer.Sparse.eval_collectBalanced, rawRowCheck6031]

def rawRow6032 : Integer.Sparse Key := [(key51, -4), (key50, 2), (key50, 2), (key79, 2), (key79, 2), (key76, -4), (key26, 2), (key25, -1), (key25, -1), (key173, 2), (key107, -1), (key107, -1), (key182, -1), (key182, -1), (key142, -1), (key142, -1), (key139, 2), (key139, 2), (key39, -1), (key39, -1), (key37, 2), (key177, -1), (key177, -1), (key119, 2), (key119, 2), (key117, -1), (key117, -1), (key190, 2), (key159, -1), (key159, -1)]

theorem rawRowCheck6032 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form3 = rawRow6032 := by decide +kernel

def row6032 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 4), (key51, -4), (key76, -4), (key79, 4), (key107, -2), (key117, -2), (key119, 4), (key139, 4), (key142, -2), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

theorem rowCheck6032 : row6032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6032 := by decide +kernel

theorem rowEval6032 (x : Key → ℝ) : Integer.Sparse.eval row6032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6032, Integer.Sparse.eval_collectBalanced, rawRowCheck6032]

def rawRow6033 : Integer.Sparse Key := [(key50, -4), (key76, 2), (key79, 2), (key50, 2), (key51, 2), (key79, -4), (key107, 2), (key139, -1), (key142, -1), (key25, 2), (key139, -1), (key182, -1), (key25, -1), (key26, -1), (key107, -1), (key173, -1), (key142, 2), (key182, 2), (key117, -1), (key119, -1), (key159, 2), (key37, -1), (key39, -1), (key117, 2), (key177, 2), (key159, -1), (key190, -1), (key39, 2), (key119, -1), (key177, -1)]

theorem rawRowCheck6033 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form3 = rawRow6033 := by decide +kernel

def row6033 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6033 : row6033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6033 := by decide +kernel

theorem rowEval6033 (x : Key → ℝ) : Integer.Sparse.eval row6033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6033, Integer.Sparse.eval_collectBalanced, rawRowCheck6033]

def rawRow6034 : Integer.Sparse Key := [(key50, -4), (key79, 2), (key76, 2), (key51, 2), (key50, 2), (key79, -4), (key107, 2), (key142, -1), (key139, -1), (key25, 2), (key182, -1), (key139, -1), (key26, -1), (key25, -1), (key173, -1), (key107, -1), (key182, 2), (key142, 2), (key119, -1), (key117, -1), (key159, 2), (key39, -1), (key37, -1), (key177, 2), (key117, 2), (key190, -1), (key159, -1), (key39, 2), (key177, -1), (key119, -1)]

theorem rawRowCheck6034 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form3 = rawRow6034 := by decide +kernel

def row6034 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6034 : row6034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6034 := by decide +kernel

theorem rowEval6034 (x : Key → ℝ) : Integer.Sparse.eval row6034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6034, Integer.Sparse.eval_collectBalanced, rawRowCheck6034]

def rawRow6035 : Integer.Sparse Key := [(key76, -4), (key50, 2), (key79, 2), (key50, 2), (key79, 2), (key51, -4), (key139, 2), (key107, -1), (key142, -1), (key139, 2), (key25, -1), (key182, -1), (key107, -1), (key142, -1), (key25, -1), (key182, -1), (key26, 2), (key173, 2), (key117, -1), (key159, -1), (key119, 2), (key117, -1), (key159, -1), (key37, 2), (key190, 2), (key39, -1), (key177, -1), (key119, 2), (key39, -1), (key177, -1)]

theorem rawRowCheck6035 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form3 = rawRow6035 := by decide +kernel

def row6035 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 4), (key51, -4), (key76, -4), (key79, 4), (key107, -2), (key117, -2), (key119, 4), (key139, 4), (key142, -2), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

theorem rowCheck6035 : row6035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6035 := by decide +kernel

theorem rowEval6035 (x : Key → ℝ) : Integer.Sparse.eval row6035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6035, Integer.Sparse.eval_collectBalanced, rawRowCheck6035]

def rawRow6036 : Integer.Sparse Key := [(key76, -4), (key79, 2), (key50, 2), (key79, 2), (key50, 2), (key51, -4), (key139, 2), (key142, -1), (key107, -1), (key139, 2), (key182, -1), (key25, -1), (key142, -1), (key107, -1), (key182, -1), (key25, -1), (key173, 2), (key26, 2), (key159, -1), (key117, -1), (key119, 2), (key159, -1), (key117, -1), (key190, 2), (key37, 2), (key177, -1), (key39, -1), (key119, 2), (key177, -1), (key39, -1)]

theorem rawRowCheck6036 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form3 = rawRow6036 := by decide +kernel

def row6036 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 4), (key51, -4), (key76, -4), (key79, 4), (key107, -2), (key117, -2), (key119, 4), (key139, 4), (key142, -2), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

theorem rowCheck6036 : row6036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6036 := by decide +kernel

theorem rowEval6036 (x : Key → ℝ) : Integer.Sparse.eval row6036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6036, Integer.Sparse.eval_collectBalanced, rawRowCheck6036]

def rawRow6037 : Integer.Sparse Key := [(key79, -4), (key50, 2), (key76, 2), (key51, 2), (key79, 2), (key50, -4), (key142, 2), (key107, -1), (key139, -1), (key182, 2), (key25, -1), (key139, -1), (key173, -1), (key182, -1), (key26, -1), (key142, -1), (key25, 2), (key107, 2), (key119, -1), (key159, -1), (key117, 2), (key177, -1), (key190, -1), (key39, 2), (key159, 2), (key37, -1), (key117, -1), (key177, 2), (key39, -1), (key119, -1)]

theorem rawRowCheck6037 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form3 = rawRow6037 := by decide +kernel

def row6037 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6037 : row6037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6037 := by decide +kernel

theorem rowEval6037 (x : Key → ℝ) : Integer.Sparse.eval row6037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6037, Integer.Sparse.eval_collectBalanced, rawRowCheck6037]

def rawRow6038 : Integer.Sparse Key := [(key79, -4), (key76, 2), (key50, 2), (key79, 2), (key51, 2), (key50, -4), (key142, 2), (key139, -1), (key107, -1), (key182, 2), (key139, -1), (key25, -1), (key182, -1), (key173, -1), (key142, -1), (key26, -1), (key107, 2), (key25, 2), (key159, -1), (key119, -1), (key117, 2), (key190, -1), (key177, -1), (key159, 2), (key39, 2), (key117, -1), (key37, -1), (key177, 2), (key119, -1), (key39, -1)]

theorem rawRowCheck6038 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form3 = rawRow6038 := by decide +kernel

def row6038 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6038 : row6038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6038 := by decide +kernel

theorem rowEval6038 (x : Key → ℝ) : Integer.Sparse.eval row6038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6038, Integer.Sparse.eval_collectBalanced, rawRowCheck6038]

def rawRow6039 : Integer.Sparse Key := [(key51, -4), (key79, 2), (key79, 2), (key50, 2), (key50, 2), (key76, -4), (key173, 2), (key182, -1), (key182, -1), (key26, 2), (key142, -1), (key142, -1), (key25, -1), (key25, -1), (key107, -1), (key107, -1), (key139, 2), (key139, 2), (key177, -1), (key177, -1), (key190, 2), (key39, -1), (key39, -1), (key119, 2), (key119, 2), (key159, -1), (key159, -1), (key37, 2), (key117, -1), (key117, -1)]

theorem rawRowCheck6039 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form3 = rawRow6039 := by decide +kernel

def row6039 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 4), (key51, -4), (key76, -4), (key79, 4), (key107, -2), (key117, -2), (key119, 4), (key139, 4), (key142, -2), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

theorem rowCheck6039 : row6039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6039 := by decide +kernel

theorem rowEval6039 (x : Key → ℝ) : Integer.Sparse.eval row6039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6039, Integer.Sparse.eval_collectBalanced, rawRowCheck6039]

def rawRow6040 : Integer.Sparse Key := [(key79, -4), (key51, 2), (key79, 2), (key50, 2), (key76, 2), (key50, -4), (key182, 2), (key173, -1), (key182, -1), (key142, 2), (key26, -1), (key142, -1), (key107, -1), (key139, -1), (key25, -1), (key139, -1), (key25, 2), (key107, 2), (key177, -1), (key190, -1), (key177, 2), (key119, -1), (key159, -1), (key39, 2), (key159, 2), (key39, -1), (key119, -1), (key117, 2), (key37, -1), (key117, -1)]

theorem rawRowCheck6040 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form3 = rawRow6040 := by decide +kernel

def row6040 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6040 : row6040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6040 := by decide +kernel

theorem rowEval6040 (x : Key → ℝ) : Integer.Sparse.eval row6040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6040, Integer.Sparse.eval_collectBalanced, rawRowCheck6040]

def rawRow6041 : Integer.Sparse Key := [(key79, -4), (key79, 2), (key51, 2), (key76, 2), (key50, 2), (key50, -4), (key182, 2), (key182, -1), (key173, -1), (key142, 2), (key142, -1), (key26, -1), (key139, -1), (key107, -1), (key139, -1), (key25, -1), (key107, 2), (key25, 2), (key190, -1), (key177, -1), (key177, 2), (key159, -1), (key119, -1), (key159, 2), (key39, 2), (key119, -1), (key39, -1), (key117, 2), (key117, -1), (key37, -1)]

theorem rawRowCheck6041 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form3 = rawRow6041 := by decide +kernel

def row6041 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6041 : row6041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6041 := by decide +kernel

theorem rowEval6041 (x : Key → ℝ) : Integer.Sparse.eval row6041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6041, Integer.Sparse.eval_collectBalanced, rawRowCheck6041]

def rawRow6042 : Integer.Sparse Key := [(key117, -4), (key107, 2), (key119, 2), (key139, 2), (key159, 2), (key142, -4), (key37, 2), (key25, -1), (key39, -1), (key117, 2), (key50, -1), (key177, -1), (key139, -1), (key159, -1), (key76, -1), (key190, -1), (key79, 2), (key182, 2), (key25, -1), (key39, -1), (key26, 2), (key107, -1), (key119, -1), (key50, 2), (key177, 2), (key51, -1), (key173, -1), (key142, 2), (key79, -1), (key182, -1)]

theorem rawRowCheck6042 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form3 = rawRow6042 := by decide +kernel

def row6042 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6042 : row6042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6042 := by decide +kernel

theorem rowEval6042 (x : Key → ℝ) : Integer.Sparse.eval row6042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6042, Integer.Sparse.eval_collectBalanced, rawRowCheck6042]

def rawRow6043 : Integer.Sparse Key := [(key117, -4), (key119, 2), (key107, 2), (key159, 2), (key139, 2), (key142, -4), (key37, 2), (key39, -1), (key25, -1), (key117, 2), (key177, -1), (key50, -1), (key159, -1), (key139, -1), (key190, -1), (key76, -1), (key182, 2), (key79, 2), (key39, -1), (key25, -1), (key26, 2), (key119, -1), (key107, -1), (key177, 2), (key50, 2), (key173, -1), (key51, -1), (key142, 2), (key182, -1), (key79, -1)]

theorem rawRowCheck6043 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form3 = rawRow6043 := by decide +kernel

def row6043 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6043 : row6043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6043 := by decide +kernel

theorem rowEval6043 (x : Key → ℝ) : Integer.Sparse.eval row6043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6043, Integer.Sparse.eval_collectBalanced, rawRowCheck6043]

def rawRow6044 : Integer.Sparse Key := [(key119, -4), (key107, 2), (key117, 2), (key142, 2), (key159, 2), (key139, -4), (key39, 2), (key25, -1), (key37, -1), (key177, 2), (key50, -1), (key117, -1), (key182, -1), (key190, -1), (key79, -1), (key159, -1), (key76, 2), (key139, 2), (key26, -1), (key39, -1), (key25, 2), (key173, -1), (key177, -1), (key51, 2), (key119, 2), (key50, -1), (key107, -1), (key182, 2), (key79, -1), (key142, -1)]

theorem rawRowCheck6044 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form3 = rawRow6044 := by decide +kernel

def row6044 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6044 : row6044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6044 := by decide +kernel

theorem rowEval6044 (x : Key → ℝ) : Integer.Sparse.eval row6044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6044, Integer.Sparse.eval_collectBalanced, rawRowCheck6044]

def rawRow6045 : Integer.Sparse Key := [(key119, -4), (key117, 2), (key107, 2), (key159, 2), (key142, 2), (key139, -4), (key39, 2), (key37, -1), (key25, -1), (key177, 2), (key117, -1), (key50, -1), (key190, -1), (key182, -1), (key159, -1), (key79, -1), (key139, 2), (key76, 2), (key39, -1), (key26, -1), (key25, 2), (key177, -1), (key173, -1), (key119, 2), (key51, 2), (key107, -1), (key50, -1), (key182, 2), (key142, -1), (key79, -1)]

theorem rawRowCheck6045 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form3 = rawRow6045 := by decide +kernel

def row6045 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6045 : row6045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6045 := by decide +kernel

theorem rowEval6045 (x : Key → ℝ) : Integer.Sparse.eval row6045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6045, Integer.Sparse.eval_collectBalanced, rawRowCheck6045]

def rawRow6046 : Integer.Sparse Key := [(key139, -4), (key107, 2), (key142, 2), (key117, 2), (key159, 2), (key119, -4), (key76, 2), (key50, -1), (key79, -1), (key139, 2), (key25, -1), (key182, -1), (key117, -1), (key159, -1), (key37, -1), (key190, -1), (key39, 2), (key177, 2), (key50, -1), (key79, -1), (key51, 2), (key107, -1), (key142, -1), (key25, 2), (key182, 2), (key26, -1), (key173, -1), (key119, 2), (key39, -1), (key177, -1)]

theorem rawRowCheck6046 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form3 = rawRow6046 := by decide +kernel

def row6046 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6046 : row6046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6046 := by decide +kernel

theorem rowEval6046 (x : Key → ℝ) : Integer.Sparse.eval row6046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6046, Integer.Sparse.eval_collectBalanced, rawRowCheck6046]

def rawRow6047 : Integer.Sparse Key := [(key139, -4), (key142, 2), (key107, 2), (key159, 2), (key117, 2), (key119, -4), (key76, 2), (key79, -1), (key50, -1), (key139, 2), (key182, -1), (key25, -1), (key159, -1), (key117, -1), (key190, -1), (key37, -1), (key177, 2), (key39, 2), (key79, -1), (key50, -1), (key51, 2), (key142, -1), (key107, -1), (key182, 2), (key25, 2), (key173, -1), (key26, -1), (key119, 2), (key177, -1), (key39, -1)]

theorem rawRowCheck6047 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form3 = rawRow6047 := by decide +kernel

def row6047 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6047 : row6047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6047 := by decide +kernel

theorem rowEval6047 (x : Key → ℝ) : Integer.Sparse.eval row6047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6047, Integer.Sparse.eval_collectBalanced, rawRowCheck6047]

def rawRow6048 : Integer.Sparse Key := [(key142, -4), (key107, 2), (key139, 2), (key119, 2), (key159, 2), (key117, -4), (key79, 2), (key50, -1), (key76, -1), (key182, 2), (key25, -1), (key139, -1), (key177, -1), (key190, -1), (key39, -1), (key159, -1), (key37, 2), (key117, 2), (key51, -1), (key79, -1), (key50, 2), (key173, -1), (key182, -1), (key26, 2), (key142, 2), (key25, -1), (key107, -1), (key177, 2), (key39, -1), (key119, -1)]

theorem rawRowCheck6048 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form3 = rawRow6048 := by decide +kernel

def row6048 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6048 : row6048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6048 := by decide +kernel

theorem rowEval6048 (x : Key → ℝ) : Integer.Sparse.eval row6048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6048, Integer.Sparse.eval_collectBalanced, rawRowCheck6048]

def rawRow6049 : Integer.Sparse Key := [(key142, -4), (key139, 2), (key107, 2), (key159, 2), (key119, 2), (key117, -4), (key79, 2), (key76, -1), (key50, -1), (key182, 2), (key139, -1), (key25, -1), (key190, -1), (key177, -1), (key159, -1), (key39, -1), (key117, 2), (key37, 2), (key79, -1), (key51, -1), (key50, 2), (key182, -1), (key173, -1), (key142, 2), (key26, 2), (key107, -1), (key25, -1), (key177, 2), (key119, -1), (key39, -1)]

theorem rawRowCheck6049 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form3 = rawRow6049 := by decide +kernel

def row6049 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6049 : row6049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6049 := by decide +kernel

theorem rowEval6049 (x : Key → ℝ) : Integer.Sparse.eval row6049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6049, Integer.Sparse.eval_collectBalanced, rawRowCheck6049]

def rawRow6050 : Integer.Sparse Key := [(key117, -4), (key139, 2), (key159, 2), (key107, 2), (key119, 2), (key142, -4), (key117, 2), (key139, -1), (key159, -1), (key37, 2), (key76, -1), (key190, -1), (key25, -1), (key39, -1), (key50, -1), (key177, -1), (key79, 2), (key182, 2), (key107, -1), (key119, -1), (key142, 2), (key25, -1), (key39, -1), (key50, 2), (key177, 2), (key79, -1), (key182, -1), (key26, 2), (key51, -1), (key173, -1)]

theorem rawRowCheck6050 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form3 = rawRow6050 := by decide +kernel

def row6050 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6050 : row6050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6050 := by decide +kernel

theorem rowEval6050 (x : Key → ℝ) : Integer.Sparse.eval row6050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6050, Integer.Sparse.eval_collectBalanced, rawRowCheck6050]

def rawRow6051 : Integer.Sparse Key := [(key117, -4), (key159, 2), (key139, 2), (key119, 2), (key107, 2), (key142, -4), (key117, 2), (key159, -1), (key139, -1), (key37, 2), (key190, -1), (key76, -1), (key39, -1), (key25, -1), (key177, -1), (key50, -1), (key182, 2), (key79, 2), (key119, -1), (key107, -1), (key142, 2), (key39, -1), (key25, -1), (key177, 2), (key50, 2), (key182, -1), (key79, -1), (key26, 2), (key173, -1), (key51, -1)]

theorem rawRowCheck6051 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form3 = rawRow6051 := by decide +kernel

def row6051 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6051 : row6051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6051 := by decide +kernel

theorem rowEval6051 (x : Key → ℝ) : Integer.Sparse.eval row6051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6051, Integer.Sparse.eval_collectBalanced, rawRowCheck6051]

def rawRow6052 : Integer.Sparse Key := [(key139, -4), (key117, 2), (key159, 2), (key107, 2), (key142, 2), (key119, -4), (key139, 2), (key117, -1), (key159, -1), (key76, 2), (key37, -1), (key190, -1), (key50, -1), (key79, -1), (key25, -1), (key182, -1), (key39, 2), (key177, 2), (key107, -1), (key142, -1), (key119, 2), (key50, -1), (key79, -1), (key25, 2), (key182, 2), (key39, -1), (key177, -1), (key51, 2), (key26, -1), (key173, -1)]

theorem rawRowCheck6052 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form3 = rawRow6052 := by decide +kernel

def row6052 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6052 : row6052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6052 := by decide +kernel

theorem rowEval6052 (x : Key → ℝ) : Integer.Sparse.eval row6052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6052, Integer.Sparse.eval_collectBalanced, rawRowCheck6052]

def rawRow6053 : Integer.Sparse Key := [(key139, -4), (key159, 2), (key117, 2), (key142, 2), (key107, 2), (key119, -4), (key139, 2), (key159, -1), (key117, -1), (key76, 2), (key190, -1), (key37, -1), (key79, -1), (key50, -1), (key182, -1), (key25, -1), (key177, 2), (key39, 2), (key142, -1), (key107, -1), (key119, 2), (key79, -1), (key50, -1), (key182, 2), (key25, 2), (key177, -1), (key39, -1), (key51, 2), (key173, -1), (key26, -1)]

theorem rawRowCheck6053 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form3 = rawRow6053 := by decide +kernel

def row6053 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6053 : row6053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6053 := by decide +kernel

theorem rowEval6053 (x : Key → ℝ) : Integer.Sparse.eval row6053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6053, Integer.Sparse.eval_collectBalanced, rawRowCheck6053]

def rawRow6054 : Integer.Sparse Key := [(key119, -4), (key142, 2), (key159, 2), (key107, 2), (key117, 2), (key139, -4), (key177, 2), (key182, -1), (key190, -1), (key39, 2), (key79, -1), (key159, -1), (key25, -1), (key37, -1), (key50, -1), (key117, -1), (key76, 2), (key139, 2), (key173, -1), (key177, -1), (key182, 2), (key26, -1), (key39, -1), (key51, 2), (key119, 2), (key79, -1), (key142, -1), (key25, 2), (key50, -1), (key107, -1)]

theorem rawRowCheck6054 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form3 = rawRow6054 := by decide +kernel

def row6054 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6054 : row6054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6054 := by decide +kernel

theorem rowEval6054 (x : Key → ℝ) : Integer.Sparse.eval row6054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6054, Integer.Sparse.eval_collectBalanced, rawRowCheck6054]

def rawRow6055 : Integer.Sparse Key := [(key119, -4), (key159, 2), (key142, 2), (key117, 2), (key107, 2), (key139, -4), (key177, 2), (key190, -1), (key182, -1), (key39, 2), (key159, -1), (key79, -1), (key37, -1), (key25, -1), (key117, -1), (key50, -1), (key139, 2), (key76, 2), (key177, -1), (key173, -1), (key182, 2), (key39, -1), (key26, -1), (key119, 2), (key51, 2), (key142, -1), (key79, -1), (key25, 2), (key107, -1), (key50, -1)]

theorem rawRowCheck6055 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form3 = rawRow6055 := by decide +kernel

def row6055 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6055 : row6055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6055 := by decide +kernel

theorem rowEval6055 (x : Key → ℝ) : Integer.Sparse.eval row6055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6055, Integer.Sparse.eval_collectBalanced, rawRowCheck6055]

def rawRow6056 : Integer.Sparse Key := [(key142, -4), (key119, 2), (key159, 2), (key107, 2), (key139, 2), (key117, -4), (key182, 2), (key177, -1), (key190, -1), (key79, 2), (key39, -1), (key159, -1), (key50, -1), (key76, -1), (key25, -1), (key139, -1), (key37, 2), (key117, 2), (key173, -1), (key182, -1), (key177, 2), (key51, -1), (key79, -1), (key26, 2), (key142, 2), (key39, -1), (key119, -1), (key50, 2), (key25, -1), (key107, -1)]

theorem rawRowCheck6056 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form3 = rawRow6056 := by decide +kernel

def row6056 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6056 : row6056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6056 := by decide +kernel

theorem rowEval6056 (x : Key → ℝ) : Integer.Sparse.eval row6056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6056, Integer.Sparse.eval_collectBalanced, rawRowCheck6056]

def rawRow6057 : Integer.Sparse Key := [(key142, -4), (key159, 2), (key119, 2), (key139, 2), (key107, 2), (key117, -4), (key182, 2), (key190, -1), (key177, -1), (key79, 2), (key159, -1), (key39, -1), (key76, -1), (key50, -1), (key139, -1), (key25, -1), (key117, 2), (key37, 2), (key182, -1), (key173, -1), (key177, 2), (key79, -1), (key51, -1), (key142, 2), (key26, 2), (key119, -1), (key39, -1), (key50, 2), (key107, -1), (key25, -1)]

theorem rawRowCheck6057 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form3 = rawRow6057 := by decide +kernel

def row6057 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

theorem rowCheck6057 : row6057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6057 := by decide +kernel

theorem rowEval6057 (x : Key → ℝ) : Integer.Sparse.eval row6057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6057, Integer.Sparse.eval_collectBalanced, rawRowCheck6057]

def rawRow6058 : Integer.Sparse Key := [(key1256, -4), (key1256, 2), (key1260, 2), (key1265, 2), (key1267, 2), (key1267, -4), (key1531, 2), (key1531, -1), (key1535, -1), (key1609, 2), (key1609, -1), (key1641, -1), (key1648, -1), (key1650, -1), (key1648, -1), (key1673, -1), (key1650, 2), (key1673, 2), (key1765, -1), (key1767, -1), (key1767, 2), (key1806, -1), (key1808, -1), (key1806, 2), (key1831, 2), (key1808, -1), (key1831, -1), (key1836, 2), (key1836, -1), (key1847, -1)]

theorem rawRowCheck6058 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form4 = rawRow6058 := by decide +kernel

def row6058 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6058 : row6058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6058 := by decide +kernel

theorem rowEval6058 (x : Key → ℝ) : Integer.Sparse.eval row6058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6058, Integer.Sparse.eval_collectBalanced, rawRowCheck6058]

def rawRow6059 : Integer.Sparse Key := [(key1256, -4), (key1260, 2), (key1256, 2), (key1267, 2), (key1265, 2), (key1267, -4), (key1531, 2), (key1535, -1), (key1531, -1), (key1609, 2), (key1641, -1), (key1609, -1), (key1650, -1), (key1648, -1), (key1673, -1), (key1648, -1), (key1673, 2), (key1650, 2), (key1767, -1), (key1765, -1), (key1767, 2), (key1808, -1), (key1806, -1), (key1831, 2), (key1806, 2), (key1831, -1), (key1808, -1), (key1836, 2), (key1847, -1), (key1836, -1)]

theorem rawRowCheck6059 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form4 = rawRow6059 := by decide +kernel

def row6059 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6059 : row6059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6059 := by decide +kernel

theorem rowEval6059 (x : Key → ℝ) : Integer.Sparse.eval row6059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6059, Integer.Sparse.eval_collectBalanced, rawRowCheck6059]

def rawRow6060 : Integer.Sparse Key := [(key1260, -4), (key1256, 2), (key1256, 2), (key1267, 2), (key1267, 2), (key1265, -4), (key1535, 2), (key1531, -1), (key1531, -1), (key1641, 2), (key1609, -1), (key1609, -1), (key1673, -1), (key1673, -1), (key1650, -1), (key1650, -1), (key1648, 2), (key1648, 2), (key1767, -1), (key1767, -1), (key1765, 2), (key1831, -1), (key1831, -1), (key1808, 2), (key1808, 2), (key1806, -1), (key1806, -1), (key1847, 2), (key1836, -1), (key1836, -1)]

theorem rawRowCheck6060 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form4 = rawRow6060 := by decide +kernel

def row6060 : Integer.Sparse Key := [(key1256, 4), (key1260, -4), (key1265, -4), (key1267, 4), (key1531, -2), (key1535, 2), (key1609, -2), (key1641, 2), (key1648, 4), (key1650, -2), (key1673, -2), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 4), (key1831, -2), (key1836, -2), (key1847, 2)]

theorem rowCheck6060 : row6060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6060 := by decide +kernel

theorem rowEval6060 (x : Key → ℝ) : Integer.Sparse.eval row6060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6060, Integer.Sparse.eval_collectBalanced, rawRowCheck6060]

def rawRow6061 : Integer.Sparse Key := [(key1256, -4), (key1265, 2), (key1267, 2), (key1256, 2), (key1260, 2), (key1267, -4), (key1609, 2), (key1648, -1), (key1650, -1), (key1531, 2), (key1648, -1), (key1673, -1), (key1531, -1), (key1535, -1), (key1609, -1), (key1641, -1), (key1650, 2), (key1673, 2), (key1806, -1), (key1808, -1), (key1836, 2), (key1765, -1), (key1767, -1), (key1806, 2), (key1831, 2), (key1836, -1), (key1847, -1), (key1767, 2), (key1808, -1), (key1831, -1)]

theorem rawRowCheck6061 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form4 = rawRow6061 := by decide +kernel

def row6061 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6061 : row6061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6061 := by decide +kernel

theorem rowEval6061 (x : Key → ℝ) : Integer.Sparse.eval row6061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6061, Integer.Sparse.eval_collectBalanced, rawRowCheck6061]

def rawRow6062 : Integer.Sparse Key := [(key1256, -4), (key1267, 2), (key1265, 2), (key1260, 2), (key1256, 2), (key1267, -4), (key1609, 2), (key1650, -1), (key1648, -1), (key1531, 2), (key1673, -1), (key1648, -1), (key1535, -1), (key1531, -1), (key1641, -1), (key1609, -1), (key1673, 2), (key1650, 2), (key1808, -1), (key1806, -1), (key1836, 2), (key1767, -1), (key1765, -1), (key1831, 2), (key1806, 2), (key1847, -1), (key1836, -1), (key1767, 2), (key1831, -1), (key1808, -1)]

theorem rawRowCheck6062 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form4 = rawRow6062 := by decide +kernel

def row6062 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6062 : row6062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6062 := by decide +kernel

theorem rowEval6062 (x : Key → ℝ) : Integer.Sparse.eval row6062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6062, Integer.Sparse.eval_collectBalanced, rawRowCheck6062]

def rawRow6063 : Integer.Sparse Key := [(key1265, -4), (key1256, 2), (key1267, 2), (key1256, 2), (key1267, 2), (key1260, -4), (key1648, 2), (key1609, -1), (key1650, -1), (key1648, 2), (key1531, -1), (key1673, -1), (key1609, -1), (key1650, -1), (key1531, -1), (key1673, -1), (key1535, 2), (key1641, 2), (key1806, -1), (key1836, -1), (key1808, 2), (key1806, -1), (key1836, -1), (key1765, 2), (key1847, 2), (key1767, -1), (key1831, -1), (key1808, 2), (key1767, -1), (key1831, -1)]

theorem rawRowCheck6063 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form4 = rawRow6063 := by decide +kernel

def row6063 : Integer.Sparse Key := [(key1256, 4), (key1260, -4), (key1265, -4), (key1267, 4), (key1531, -2), (key1535, 2), (key1609, -2), (key1641, 2), (key1648, 4), (key1650, -2), (key1673, -2), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 4), (key1831, -2), (key1836, -2), (key1847, 2)]

theorem rowCheck6063 : row6063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6063 := by decide +kernel

theorem rowEval6063 (x : Key → ℝ) : Integer.Sparse.eval row6063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6063, Integer.Sparse.eval_collectBalanced, rawRowCheck6063]

def rawRow6064 : Integer.Sparse Key := [(key1265, -4), (key1267, 2), (key1256, 2), (key1267, 2), (key1256, 2), (key1260, -4), (key1648, 2), (key1650, -1), (key1609, -1), (key1648, 2), (key1673, -1), (key1531, -1), (key1650, -1), (key1609, -1), (key1673, -1), (key1531, -1), (key1641, 2), (key1535, 2), (key1836, -1), (key1806, -1), (key1808, 2), (key1836, -1), (key1806, -1), (key1847, 2), (key1765, 2), (key1831, -1), (key1767, -1), (key1808, 2), (key1831, -1), (key1767, -1)]

theorem rawRowCheck6064 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form4 = rawRow6064 := by decide +kernel

def row6064 : Integer.Sparse Key := [(key1256, 4), (key1260, -4), (key1265, -4), (key1267, 4), (key1531, -2), (key1535, 2), (key1609, -2), (key1641, 2), (key1648, 4), (key1650, -2), (key1673, -2), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 4), (key1831, -2), (key1836, -2), (key1847, 2)]

theorem rowCheck6064 : row6064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6064 := by decide +kernel

theorem rowEval6064 (x : Key → ℝ) : Integer.Sparse.eval row6064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6064, Integer.Sparse.eval_collectBalanced, rawRowCheck6064]

def rawRow6065 : Integer.Sparse Key := [(key1267, -4), (key1256, 2), (key1265, 2), (key1260, 2), (key1267, 2), (key1256, -4), (key1650, 2), (key1609, -1), (key1648, -1), (key1673, 2), (key1531, -1), (key1648, -1), (key1641, -1), (key1673, -1), (key1535, -1), (key1650, -1), (key1531, 2), (key1609, 2), (key1808, -1), (key1836, -1), (key1806, 2), (key1831, -1), (key1847, -1), (key1767, 2), (key1836, 2), (key1765, -1), (key1806, -1), (key1831, 2), (key1767, -1), (key1808, -1)]

theorem rawRowCheck6065 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form4 = rawRow6065 := by decide +kernel

def row6065 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6065 : row6065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6065 := by decide +kernel

theorem rowEval6065 (x : Key → ℝ) : Integer.Sparse.eval row6065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6065, Integer.Sparse.eval_collectBalanced, rawRowCheck6065]

def rawRow6066 : Integer.Sparse Key := [(key1267, -4), (key1265, 2), (key1256, 2), (key1267, 2), (key1260, 2), (key1256, -4), (key1650, 2), (key1648, -1), (key1609, -1), (key1673, 2), (key1648, -1), (key1531, -1), (key1673, -1), (key1641, -1), (key1650, -1), (key1535, -1), (key1609, 2), (key1531, 2), (key1836, -1), (key1808, -1), (key1806, 2), (key1847, -1), (key1831, -1), (key1836, 2), (key1767, 2), (key1806, -1), (key1765, -1), (key1831, 2), (key1808, -1), (key1767, -1)]

theorem rawRowCheck6066 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form4 = rawRow6066 := by decide +kernel

def row6066 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6066 : row6066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6066 := by decide +kernel

theorem rowEval6066 (x : Key → ℝ) : Integer.Sparse.eval row6066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6066, Integer.Sparse.eval_collectBalanced, rawRowCheck6066]

def rawRow6067 : Integer.Sparse Key := [(key1260, -4), (key1267, 2), (key1267, 2), (key1256, 2), (key1256, 2), (key1265, -4), (key1641, 2), (key1673, -1), (key1673, -1), (key1535, 2), (key1650, -1), (key1650, -1), (key1531, -1), (key1531, -1), (key1609, -1), (key1609, -1), (key1648, 2), (key1648, 2), (key1831, -1), (key1831, -1), (key1847, 2), (key1767, -1), (key1767, -1), (key1808, 2), (key1808, 2), (key1836, -1), (key1836, -1), (key1765, 2), (key1806, -1), (key1806, -1)]

theorem rawRowCheck6067 : GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form4 = rawRow6067 := by decide +kernel

def row6067 : Integer.Sparse Key := [(key1256, 4), (key1260, -4), (key1265, -4), (key1267, 4), (key1531, -2), (key1535, 2), (key1609, -2), (key1641, 2), (key1648, 4), (key1650, -2), (key1673, -2), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 4), (key1831, -2), (key1836, -2), (key1847, 2)]

theorem rowCheck6067 : row6067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6067 := by decide +kernel

theorem rowEval6067 (x : Key → ℝ) : Integer.Sparse.eval row6067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6067, Integer.Sparse.eval_collectBalanced, rawRowCheck6067]

def rawRow6068 : Integer.Sparse Key := [(key1267, -4), (key1260, 2), (key1267, 2), (key1256, 2), (key1265, 2), (key1256, -4), (key1673, 2), (key1641, -1), (key1673, -1), (key1650, 2), (key1535, -1), (key1650, -1), (key1609, -1), (key1648, -1), (key1531, -1), (key1648, -1), (key1531, 2), (key1609, 2), (key1831, -1), (key1847, -1), (key1831, 2), (key1808, -1), (key1836, -1), (key1767, 2), (key1836, 2), (key1767, -1), (key1808, -1), (key1806, 2), (key1765, -1), (key1806, -1)]

theorem rawRowCheck6068 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form4 = rawRow6068 := by decide +kernel

def row6068 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6068 : row6068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6068 := by decide +kernel

theorem rowEval6068 (x : Key → ℝ) : Integer.Sparse.eval row6068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6068, Integer.Sparse.eval_collectBalanced, rawRowCheck6068]

def rawRow6069 : Integer.Sparse Key := [(key1267, -4), (key1267, 2), (key1260, 2), (key1265, 2), (key1256, 2), (key1256, -4), (key1673, 2), (key1673, -1), (key1641, -1), (key1650, 2), (key1650, -1), (key1535, -1), (key1648, -1), (key1609, -1), (key1648, -1), (key1531, -1), (key1609, 2), (key1531, 2), (key1847, -1), (key1831, -1), (key1831, 2), (key1836, -1), (key1808, -1), (key1836, 2), (key1767, 2), (key1808, -1), (key1767, -1), (key1806, 2), (key1806, -1), (key1765, -1)]

theorem rawRowCheck6069 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form4 = rawRow6069 := by decide +kernel

def row6069 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6069 : row6069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6069 := by decide +kernel

theorem rowEval6069 (x : Key → ℝ) : Integer.Sparse.eval row6069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6069, Integer.Sparse.eval_collectBalanced, rawRowCheck6069]

def rawRow6070 : Integer.Sparse Key := [(key1531, -4), (key1531, 2), (key1535, 2), (key1765, 2), (key1767, 2), (key1767, -4), (key1256, 2), (key1256, -1), (key1260, -1), (key1609, 2), (key1609, -1), (key1641, -1), (key1806, -1), (key1808, -1), (key1806, -1), (key1831, -1), (key1808, 2), (key1831, 2), (key1265, -1), (key1267, -1), (key1267, 2), (key1648, -1), (key1650, -1), (key1648, 2), (key1673, 2), (key1650, -1), (key1673, -1), (key1836, 2), (key1836, -1), (key1847, -1)]

theorem rawRowCheck6070 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form4 = rawRow6070 := by decide +kernel

def row6070 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6070 : row6070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6070 := by decide +kernel

theorem rowEval6070 (x : Key → ℝ) : Integer.Sparse.eval row6070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6070, Integer.Sparse.eval_collectBalanced, rawRowCheck6070]

def rawRow6071 : Integer.Sparse Key := [(key1531, -4), (key1535, 2), (key1531, 2), (key1767, 2), (key1765, 2), (key1767, -4), (key1256, 2), (key1260, -1), (key1256, -1), (key1609, 2), (key1641, -1), (key1609, -1), (key1808, -1), (key1806, -1), (key1831, -1), (key1806, -1), (key1831, 2), (key1808, 2), (key1267, -1), (key1265, -1), (key1267, 2), (key1650, -1), (key1648, -1), (key1673, 2), (key1648, 2), (key1673, -1), (key1650, -1), (key1836, 2), (key1847, -1), (key1836, -1)]

theorem rawRowCheck6071 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form4 = rawRow6071 := by decide +kernel

def row6071 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6071 : row6071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6071 := by decide +kernel

theorem rowEval6071 (x : Key → ℝ) : Integer.Sparse.eval row6071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6071, Integer.Sparse.eval_collectBalanced, rawRowCheck6071]

def rawRow6072 : Integer.Sparse Key := [(key1535, -4), (key1531, 2), (key1531, 2), (key1767, 2), (key1767, 2), (key1765, -4), (key1260, 2), (key1256, -1), (key1256, -1), (key1641, 2), (key1609, -1), (key1609, -1), (key1831, -1), (key1831, -1), (key1808, -1), (key1808, -1), (key1806, 2), (key1806, 2), (key1267, -1), (key1267, -1), (key1265, 2), (key1673, -1), (key1673, -1), (key1650, 2), (key1650, 2), (key1648, -1), (key1648, -1), (key1847, 2), (key1836, -1), (key1836, -1)]

theorem rawRowCheck6072 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form4 = rawRow6072 := by decide +kernel

def row6072 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 4), (key1535, -4), (key1609, -2), (key1641, 2), (key1648, -2), (key1650, 4), (key1673, -2), (key1765, -4), (key1767, 4), (key1806, 4), (key1808, -2), (key1831, -2), (key1836, -2), (key1847, 2)]

theorem rowCheck6072 : row6072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6072 := by decide +kernel

theorem rowEval6072 (x : Key → ℝ) : Integer.Sparse.eval row6072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6072, Integer.Sparse.eval_collectBalanced, rawRowCheck6072]

def rawRow6073 : Integer.Sparse Key := [(key1531, -4), (key1765, 2), (key1767, 2), (key1531, 2), (key1535, 2), (key1767, -4), (key1609, 2), (key1806, -1), (key1808, -1), (key1256, 2), (key1806, -1), (key1831, -1), (key1256, -1), (key1260, -1), (key1609, -1), (key1641, -1), (key1808, 2), (key1831, 2), (key1648, -1), (key1650, -1), (key1836, 2), (key1265, -1), (key1267, -1), (key1648, 2), (key1673, 2), (key1836, -1), (key1847, -1), (key1267, 2), (key1650, -1), (key1673, -1)]

theorem rawRowCheck6073 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form4 = rawRow6073 := by decide +kernel

def row6073 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6073 : row6073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6073 := by decide +kernel

theorem rowEval6073 (x : Key → ℝ) : Integer.Sparse.eval row6073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6073, Integer.Sparse.eval_collectBalanced, rawRowCheck6073]

def rawRow6074 : Integer.Sparse Key := [(key1531, -4), (key1767, 2), (key1765, 2), (key1535, 2), (key1531, 2), (key1767, -4), (key1609, 2), (key1808, -1), (key1806, -1), (key1256, 2), (key1831, -1), (key1806, -1), (key1260, -1), (key1256, -1), (key1641, -1), (key1609, -1), (key1831, 2), (key1808, 2), (key1650, -1), (key1648, -1), (key1836, 2), (key1267, -1), (key1265, -1), (key1673, 2), (key1648, 2), (key1847, -1), (key1836, -1), (key1267, 2), (key1673, -1), (key1650, -1)]

theorem rawRowCheck6074 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form4 = rawRow6074 := by decide +kernel

def row6074 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6074 : row6074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6074 := by decide +kernel

theorem rowEval6074 (x : Key → ℝ) : Integer.Sparse.eval row6074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6074, Integer.Sparse.eval_collectBalanced, rawRowCheck6074]

def rawRow6075 : Integer.Sparse Key := [(key1765, -4), (key1531, 2), (key1767, 2), (key1531, 2), (key1767, 2), (key1535, -4), (key1806, 2), (key1609, -1), (key1808, -1), (key1806, 2), (key1256, -1), (key1831, -1), (key1609, -1), (key1808, -1), (key1256, -1), (key1831, -1), (key1260, 2), (key1641, 2), (key1648, -1), (key1836, -1), (key1650, 2), (key1648, -1), (key1836, -1), (key1265, 2), (key1847, 2), (key1267, -1), (key1673, -1), (key1650, 2), (key1267, -1), (key1673, -1)]

theorem rawRowCheck6075 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form4 = rawRow6075 := by decide +kernel

def row6075 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 4), (key1535, -4), (key1609, -2), (key1641, 2), (key1648, -2), (key1650, 4), (key1673, -2), (key1765, -4), (key1767, 4), (key1806, 4), (key1808, -2), (key1831, -2), (key1836, -2), (key1847, 2)]

theorem rowCheck6075 : row6075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6075 := by decide +kernel

theorem rowEval6075 (x : Key → ℝ) : Integer.Sparse.eval row6075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6075, Integer.Sparse.eval_collectBalanced, rawRowCheck6075]

def rawRow6076 : Integer.Sparse Key := [(key1765, -4), (key1767, 2), (key1531, 2), (key1767, 2), (key1531, 2), (key1535, -4), (key1806, 2), (key1808, -1), (key1609, -1), (key1806, 2), (key1831, -1), (key1256, -1), (key1808, -1), (key1609, -1), (key1831, -1), (key1256, -1), (key1641, 2), (key1260, 2), (key1836, -1), (key1648, -1), (key1650, 2), (key1836, -1), (key1648, -1), (key1847, 2), (key1265, 2), (key1673, -1), (key1267, -1), (key1650, 2), (key1673, -1), (key1267, -1)]

theorem rawRowCheck6076 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form4 = rawRow6076 := by decide +kernel

def row6076 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 4), (key1535, -4), (key1609, -2), (key1641, 2), (key1648, -2), (key1650, 4), (key1673, -2), (key1765, -4), (key1767, 4), (key1806, 4), (key1808, -2), (key1831, -2), (key1836, -2), (key1847, 2)]

theorem rowCheck6076 : row6076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6076 := by decide +kernel

theorem rowEval6076 (x : Key → ℝ) : Integer.Sparse.eval row6076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6076, Integer.Sparse.eval_collectBalanced, rawRowCheck6076]

def rawRow6077 : Integer.Sparse Key := [(key1767, -4), (key1531, 2), (key1765, 2), (key1535, 2), (key1767, 2), (key1531, -4), (key1808, 2), (key1609, -1), (key1806, -1), (key1831, 2), (key1256, -1), (key1806, -1), (key1641, -1), (key1831, -1), (key1260, -1), (key1808, -1), (key1256, 2), (key1609, 2), (key1650, -1), (key1836, -1), (key1648, 2), (key1673, -1), (key1847, -1), (key1267, 2), (key1836, 2), (key1265, -1), (key1648, -1), (key1673, 2), (key1267, -1), (key1650, -1)]

theorem rawRowCheck6077 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form4 = rawRow6077 := by decide +kernel

def row6077 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6077 : row6077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6077 := by decide +kernel

theorem rowEval6077 (x : Key → ℝ) : Integer.Sparse.eval row6077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6077, Integer.Sparse.eval_collectBalanced, rawRowCheck6077]

def rawRow6078 : Integer.Sparse Key := [(key1767, -4), (key1765, 2), (key1531, 2), (key1767, 2), (key1535, 2), (key1531, -4), (key1808, 2), (key1806, -1), (key1609, -1), (key1831, 2), (key1806, -1), (key1256, -1), (key1831, -1), (key1641, -1), (key1808, -1), (key1260, -1), (key1609, 2), (key1256, 2), (key1836, -1), (key1650, -1), (key1648, 2), (key1847, -1), (key1673, -1), (key1836, 2), (key1267, 2), (key1648, -1), (key1265, -1), (key1673, 2), (key1650, -1), (key1267, -1)]

theorem rawRowCheck6078 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form4 = rawRow6078 := by decide +kernel

def row6078 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6078 : row6078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6078 := by decide +kernel

theorem rowEval6078 (x : Key → ℝ) : Integer.Sparse.eval row6078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6078, Integer.Sparse.eval_collectBalanced, rawRowCheck6078]

def rawRow6079 : Integer.Sparse Key := [(key1535, -4), (key1767, 2), (key1767, 2), (key1531, 2), (key1531, 2), (key1765, -4), (key1641, 2), (key1831, -1), (key1831, -1), (key1260, 2), (key1808, -1), (key1808, -1), (key1256, -1), (key1256, -1), (key1609, -1), (key1609, -1), (key1806, 2), (key1806, 2), (key1673, -1), (key1673, -1), (key1847, 2), (key1267, -1), (key1267, -1), (key1650, 2), (key1650, 2), (key1836, -1), (key1836, -1), (key1265, 2), (key1648, -1), (key1648, -1)]

theorem rawRowCheck6079 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form4 = rawRow6079 := by decide +kernel

def row6079 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 4), (key1535, -4), (key1609, -2), (key1641, 2), (key1648, -2), (key1650, 4), (key1673, -2), (key1765, -4), (key1767, 4), (key1806, 4), (key1808, -2), (key1831, -2), (key1836, -2), (key1847, 2)]

theorem rowCheck6079 : row6079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6079 := by decide +kernel

theorem rowEval6079 (x : Key → ℝ) : Integer.Sparse.eval row6079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6079, Integer.Sparse.eval_collectBalanced, rawRowCheck6079]

def rawRow6080 : Integer.Sparse Key := [(key1767, -4), (key1535, 2), (key1767, 2), (key1531, 2), (key1765, 2), (key1531, -4), (key1831, 2), (key1641, -1), (key1831, -1), (key1808, 2), (key1260, -1), (key1808, -1), (key1609, -1), (key1806, -1), (key1256, -1), (key1806, -1), (key1256, 2), (key1609, 2), (key1673, -1), (key1847, -1), (key1673, 2), (key1650, -1), (key1836, -1), (key1267, 2), (key1836, 2), (key1267, -1), (key1650, -1), (key1648, 2), (key1265, -1), (key1648, -1)]

theorem rawRowCheck6080 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form4 = rawRow6080 := by decide +kernel

def row6080 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6080 : row6080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6080 := by decide +kernel

theorem rowEval6080 (x : Key → ℝ) : Integer.Sparse.eval row6080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6080, Integer.Sparse.eval_collectBalanced, rawRowCheck6080]

def rawRow6081 : Integer.Sparse Key := [(key1767, -4), (key1767, 2), (key1535, 2), (key1765, 2), (key1531, 2), (key1531, -4), (key1831, 2), (key1831, -1), (key1641, -1), (key1808, 2), (key1808, -1), (key1260, -1), (key1806, -1), (key1609, -1), (key1806, -1), (key1256, -1), (key1609, 2), (key1256, 2), (key1847, -1), (key1673, -1), (key1673, 2), (key1836, -1), (key1650, -1), (key1836, 2), (key1267, 2), (key1650, -1), (key1267, -1), (key1648, 2), (key1648, -1), (key1265, -1)]

theorem rawRowCheck6081 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form4 = rawRow6081 := by decide +kernel

def row6081 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6081 : row6081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6081 := by decide +kernel

theorem rowEval6081 (x : Key → ℝ) : Integer.Sparse.eval row6081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6081, Integer.Sparse.eval_collectBalanced, rawRowCheck6081]

def rawRow6082 : Integer.Sparse Key := [(key1648, -4), (key1609, 2), (key1650, 2), (key1806, 2), (key1836, 2), (key1808, -4), (key1265, 2), (key1256, -1), (key1267, -1), (key1648, 2), (key1531, -1), (key1673, -1), (key1806, -1), (key1836, -1), (key1765, -1), (key1847, -1), (key1767, 2), (key1831, 2), (key1256, -1), (key1267, -1), (key1260, 2), (key1609, -1), (key1650, -1), (key1531, 2), (key1673, 2), (key1535, -1), (key1641, -1), (key1808, 2), (key1767, -1), (key1831, -1)]

theorem rawRowCheck6082 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form4 = rawRow6082 := by decide +kernel

def row6082 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6082 : row6082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6082 := by decide +kernel

theorem rowEval6082 (x : Key → ℝ) : Integer.Sparse.eval row6082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6082, Integer.Sparse.eval_collectBalanced, rawRowCheck6082]

def rawRow6083 : Integer.Sparse Key := [(key1648, -4), (key1650, 2), (key1609, 2), (key1836, 2), (key1806, 2), (key1808, -4), (key1265, 2), (key1267, -1), (key1256, -1), (key1648, 2), (key1673, -1), (key1531, -1), (key1836, -1), (key1806, -1), (key1847, -1), (key1765, -1), (key1831, 2), (key1767, 2), (key1267, -1), (key1256, -1), (key1260, 2), (key1650, -1), (key1609, -1), (key1673, 2), (key1531, 2), (key1641, -1), (key1535, -1), (key1808, 2), (key1831, -1), (key1767, -1)]

theorem rawRowCheck6083 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form4 = rawRow6083 := by decide +kernel

def row6083 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6083 : row6083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6083 := by decide +kernel

theorem rowEval6083 (x : Key → ℝ) : Integer.Sparse.eval row6083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6083, Integer.Sparse.eval_collectBalanced, rawRowCheck6083]

def rawRow6084 : Integer.Sparse Key := [(key1650, -4), (key1609, 2), (key1648, 2), (key1808, 2), (key1836, 2), (key1806, -4), (key1267, 2), (key1256, -1), (key1265, -1), (key1673, 2), (key1531, -1), (key1648, -1), (key1831, -1), (key1847, -1), (key1767, -1), (key1836, -1), (key1765, 2), (key1806, 2), (key1260, -1), (key1267, -1), (key1256, 2), (key1641, -1), (key1673, -1), (key1535, 2), (key1650, 2), (key1531, -1), (key1609, -1), (key1831, 2), (key1767, -1), (key1808, -1)]

theorem rawRowCheck6084 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form4 = rawRow6084 := by decide +kernel

def row6084 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6084 : row6084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6084 := by decide +kernel

theorem rowEval6084 (x : Key → ℝ) : Integer.Sparse.eval row6084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6084, Integer.Sparse.eval_collectBalanced, rawRowCheck6084]

def rawRow6085 : Integer.Sparse Key := [(key1650, -4), (key1648, 2), (key1609, 2), (key1836, 2), (key1808, 2), (key1806, -4), (key1267, 2), (key1265, -1), (key1256, -1), (key1673, 2), (key1648, -1), (key1531, -1), (key1847, -1), (key1831, -1), (key1836, -1), (key1767, -1), (key1806, 2), (key1765, 2), (key1267, -1), (key1260, -1), (key1256, 2), (key1673, -1), (key1641, -1), (key1650, 2), (key1535, 2), (key1609, -1), (key1531, -1), (key1831, 2), (key1808, -1), (key1767, -1)]

theorem rawRowCheck6085 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form4 = rawRow6085 := by decide +kernel

def row6085 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6085 : row6085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6085 := by decide +kernel

theorem rowEval6085 (x : Key → ℝ) : Integer.Sparse.eval row6085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6085, Integer.Sparse.eval_collectBalanced, rawRowCheck6085]

def rawRow6086 : Integer.Sparse Key := [(key1806, -4), (key1609, 2), (key1808, 2), (key1648, 2), (key1836, 2), (key1650, -4), (key1765, 2), (key1531, -1), (key1767, -1), (key1806, 2), (key1256, -1), (key1831, -1), (key1648, -1), (key1836, -1), (key1265, -1), (key1847, -1), (key1267, 2), (key1673, 2), (key1531, -1), (key1767, -1), (key1535, 2), (key1609, -1), (key1808, -1), (key1256, 2), (key1831, 2), (key1260, -1), (key1641, -1), (key1650, 2), (key1267, -1), (key1673, -1)]

theorem rawRowCheck6086 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form4 = rawRow6086 := by decide +kernel

def row6086 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6086 : row6086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6086 := by decide +kernel

theorem rowEval6086 (x : Key → ℝ) : Integer.Sparse.eval row6086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6086, Integer.Sparse.eval_collectBalanced, rawRowCheck6086]

def rawRow6087 : Integer.Sparse Key := [(key1806, -4), (key1808, 2), (key1609, 2), (key1836, 2), (key1648, 2), (key1650, -4), (key1765, 2), (key1767, -1), (key1531, -1), (key1806, 2), (key1831, -1), (key1256, -1), (key1836, -1), (key1648, -1), (key1847, -1), (key1265, -1), (key1673, 2), (key1267, 2), (key1767, -1), (key1531, -1), (key1535, 2), (key1808, -1), (key1609, -1), (key1831, 2), (key1256, 2), (key1641, -1), (key1260, -1), (key1650, 2), (key1673, -1), (key1267, -1)]

theorem rawRowCheck6087 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form4 = rawRow6087 := by decide +kernel

def row6087 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6087 : row6087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6087 := by decide +kernel

theorem rowEval6087 (x : Key → ℝ) : Integer.Sparse.eval row6087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6087, Integer.Sparse.eval_collectBalanced, rawRowCheck6087]

def rawRow6088 : Integer.Sparse Key := [(key1808, -4), (key1609, 2), (key1806, 2), (key1650, 2), (key1836, 2), (key1648, -4), (key1767, 2), (key1531, -1), (key1765, -1), (key1831, 2), (key1256, -1), (key1806, -1), (key1673, -1), (key1847, -1), (key1267, -1), (key1836, -1), (key1265, 2), (key1648, 2), (key1535, -1), (key1767, -1), (key1531, 2), (key1641, -1), (key1831, -1), (key1260, 2), (key1808, 2), (key1256, -1), (key1609, -1), (key1673, 2), (key1267, -1), (key1650, -1)]

theorem rawRowCheck6088 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form4 = rawRow6088 := by decide +kernel

def row6088 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6088 : row6088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6088 := by decide +kernel

theorem rowEval6088 (x : Key → ℝ) : Integer.Sparse.eval row6088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6088, Integer.Sparse.eval_collectBalanced, rawRowCheck6088]

def rawRow6089 : Integer.Sparse Key := [(key1808, -4), (key1806, 2), (key1609, 2), (key1836, 2), (key1650, 2), (key1648, -4), (key1767, 2), (key1765, -1), (key1531, -1), (key1831, 2), (key1806, -1), (key1256, -1), (key1847, -1), (key1673, -1), (key1836, -1), (key1267, -1), (key1648, 2), (key1265, 2), (key1767, -1), (key1535, -1), (key1531, 2), (key1831, -1), (key1641, -1), (key1808, 2), (key1260, 2), (key1609, -1), (key1256, -1), (key1673, 2), (key1650, -1), (key1267, -1)]

theorem rawRowCheck6089 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form4 = rawRow6089 := by decide +kernel

def row6089 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6089 : row6089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6089 := by decide +kernel

theorem rowEval6089 (x : Key → ℝ) : Integer.Sparse.eval row6089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6089, Integer.Sparse.eval_collectBalanced, rawRowCheck6089]

def rawRow6090 : Integer.Sparse Key := [(key1648, -4), (key1806, 2), (key1836, 2), (key1609, 2), (key1650, 2), (key1808, -4), (key1648, 2), (key1806, -1), (key1836, -1), (key1265, 2), (key1765, -1), (key1847, -1), (key1256, -1), (key1267, -1), (key1531, -1), (key1673, -1), (key1767, 2), (key1831, 2), (key1609, -1), (key1650, -1), (key1808, 2), (key1256, -1), (key1267, -1), (key1531, 2), (key1673, 2), (key1767, -1), (key1831, -1), (key1260, 2), (key1535, -1), (key1641, -1)]

theorem rawRowCheck6090 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form4 = rawRow6090 := by decide +kernel

def row6090 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6090 : row6090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6090 := by decide +kernel

theorem rowEval6090 (x : Key → ℝ) : Integer.Sparse.eval row6090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6090, Integer.Sparse.eval_collectBalanced, rawRowCheck6090]

def rawRow6091 : Integer.Sparse Key := [(key1648, -4), (key1836, 2), (key1806, 2), (key1650, 2), (key1609, 2), (key1808, -4), (key1648, 2), (key1836, -1), (key1806, -1), (key1265, 2), (key1847, -1), (key1765, -1), (key1267, -1), (key1256, -1), (key1673, -1), (key1531, -1), (key1831, 2), (key1767, 2), (key1650, -1), (key1609, -1), (key1808, 2), (key1267, -1), (key1256, -1), (key1673, 2), (key1531, 2), (key1831, -1), (key1767, -1), (key1260, 2), (key1641, -1), (key1535, -1)]

theorem rawRowCheck6091 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form4 = rawRow6091 := by decide +kernel

def row6091 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6091 : row6091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6091 := by decide +kernel

theorem rowEval6091 (x : Key → ℝ) : Integer.Sparse.eval row6091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6091, Integer.Sparse.eval_collectBalanced, rawRowCheck6091]

def rawRow6092 : Integer.Sparse Key := [(key1806, -4), (key1648, 2), (key1836, 2), (key1609, 2), (key1808, 2), (key1650, -4), (key1806, 2), (key1648, -1), (key1836, -1), (key1765, 2), (key1265, -1), (key1847, -1), (key1531, -1), (key1767, -1), (key1256, -1), (key1831, -1), (key1267, 2), (key1673, 2), (key1609, -1), (key1808, -1), (key1650, 2), (key1531, -1), (key1767, -1), (key1256, 2), (key1831, 2), (key1267, -1), (key1673, -1), (key1535, 2), (key1260, -1), (key1641, -1)]

theorem rawRowCheck6092 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form4 = rawRow6092 := by decide +kernel

def row6092 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6092 : row6092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6092 := by decide +kernel

theorem rowEval6092 (x : Key → ℝ) : Integer.Sparse.eval row6092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6092, Integer.Sparse.eval_collectBalanced, rawRowCheck6092]

def rawRow6093 : Integer.Sparse Key := [(key1806, -4), (key1836, 2), (key1648, 2), (key1808, 2), (key1609, 2), (key1650, -4), (key1806, 2), (key1836, -1), (key1648, -1), (key1765, 2), (key1847, -1), (key1265, -1), (key1767, -1), (key1531, -1), (key1831, -1), (key1256, -1), (key1673, 2), (key1267, 2), (key1808, -1), (key1609, -1), (key1650, 2), (key1767, -1), (key1531, -1), (key1831, 2), (key1256, 2), (key1673, -1), (key1267, -1), (key1535, 2), (key1641, -1), (key1260, -1)]

theorem rawRowCheck6093 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form4 = rawRow6093 := by decide +kernel

def row6093 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6093 : row6093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6093 := by decide +kernel

theorem rowEval6093 (x : Key → ℝ) : Integer.Sparse.eval row6093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6093, Integer.Sparse.eval_collectBalanced, rawRowCheck6093]

def rawRow6094 : Integer.Sparse Key := [(key1650, -4), (key1808, 2), (key1836, 2), (key1609, 2), (key1648, 2), (key1806, -4), (key1673, 2), (key1831, -1), (key1847, -1), (key1267, 2), (key1767, -1), (key1836, -1), (key1256, -1), (key1265, -1), (key1531, -1), (key1648, -1), (key1765, 2), (key1806, 2), (key1641, -1), (key1673, -1), (key1831, 2), (key1260, -1), (key1267, -1), (key1535, 2), (key1650, 2), (key1767, -1), (key1808, -1), (key1256, 2), (key1531, -1), (key1609, -1)]

theorem rawRowCheck6094 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form4 = rawRow6094 := by decide +kernel

def row6094 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6094 : row6094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6094 := by decide +kernel

theorem rowEval6094 (x : Key → ℝ) : Integer.Sparse.eval row6094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6094, Integer.Sparse.eval_collectBalanced, rawRowCheck6094]

def rawRow6095 : Integer.Sparse Key := [(key1650, -4), (key1836, 2), (key1808, 2), (key1648, 2), (key1609, 2), (key1806, -4), (key1673, 2), (key1847, -1), (key1831, -1), (key1267, 2), (key1836, -1), (key1767, -1), (key1265, -1), (key1256, -1), (key1648, -1), (key1531, -1), (key1806, 2), (key1765, 2), (key1673, -1), (key1641, -1), (key1831, 2), (key1267, -1), (key1260, -1), (key1650, 2), (key1535, 2), (key1808, -1), (key1767, -1), (key1256, 2), (key1609, -1), (key1531, -1)]

theorem rawRowCheck6095 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form4 = rawRow6095 := by decide +kernel

def row6095 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6095 : row6095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6095 := by decide +kernel

theorem rowEval6095 (x : Key → ℝ) : Integer.Sparse.eval row6095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6095, Integer.Sparse.eval_collectBalanced, rawRowCheck6095]

def rawRow6096 : Integer.Sparse Key := [(key1808, -4), (key1650, 2), (key1836, 2), (key1609, 2), (key1806, 2), (key1648, -4), (key1831, 2), (key1673, -1), (key1847, -1), (key1767, 2), (key1267, -1), (key1836, -1), (key1531, -1), (key1765, -1), (key1256, -1), (key1806, -1), (key1265, 2), (key1648, 2), (key1641, -1), (key1831, -1), (key1673, 2), (key1535, -1), (key1767, -1), (key1260, 2), (key1808, 2), (key1267, -1), (key1650, -1), (key1531, 2), (key1256, -1), (key1609, -1)]

theorem rawRowCheck6096 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form4 = rawRow6096 := by decide +kernel

def row6096 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6096 : row6096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6096 := by decide +kernel

theorem rowEval6096 (x : Key → ℝ) : Integer.Sparse.eval row6096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6096, Integer.Sparse.eval_collectBalanced, rawRowCheck6096]

def rawRow6097 : Integer.Sparse Key := [(key1808, -4), (key1836, 2), (key1650, 2), (key1806, 2), (key1609, 2), (key1648, -4), (key1831, 2), (key1847, -1), (key1673, -1), (key1767, 2), (key1836, -1), (key1267, -1), (key1765, -1), (key1531, -1), (key1806, -1), (key1256, -1), (key1648, 2), (key1265, 2), (key1831, -1), (key1641, -1), (key1673, 2), (key1767, -1), (key1535, -1), (key1808, 2), (key1260, 2), (key1650, -1), (key1267, -1), (key1531, 2), (key1609, -1), (key1256, -1)]

theorem rawRowCheck6097 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form4 = rawRow6097 := by decide +kernel

def row6097 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck6097 : row6097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6097 := by decide +kernel

theorem rowEval6097 (x : Key → ℝ) : Integer.Sparse.eval row6097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6097, Integer.Sparse.eval_collectBalanced, rawRowCheck6097]

def rawRow6098 : Integer.Sparse Key := [(key1391, -2), (key1391, 1), (key1397, 1), (key1424, -2), (key1424, 1), (key1447, 1), (key1455, 1), (key1457, 1), (key1455, 1), (key1466, 1), (key1457, -2), (key1466, -2), (key1546, 2), (key1546, -1), (key1559, -1), (key1573, 2), (key1573, -1), (key1596, -1), (key1655, -1), (key1659, -1), (key1655, -1), (key1667, -1), (key1659, 2), (key1667, 2), (key1772, -1), (key1774, -1), (key1772, 1), (key1780, 1), (key1788, -1), (key1790, -1), (key1790, 1), (key1798, 1), (key1813, 1), (key1817, 1), (key1817, -1), (key1825, -1), (key1839, 1), (key1844, 1), (key1841, -1), (key1844, -1)]

theorem rawRowCheck6098 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form5 = rawRow6098 := by decide +kernel

def row6098 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6098 : row6098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6098 := by decide +kernel

theorem rowEval6098 (x : Key → ℝ) : Integer.Sparse.eval row6098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6098, Integer.Sparse.eval_collectBalanced, rawRowCheck6098]

def rawRow6099 : Integer.Sparse Key := [(key1391, -2), (key1397, 1), (key1391, 1), (key1424, -2), (key1447, 1), (key1424, 1), (key1457, 1), (key1455, 1), (key1466, 1), (key1455, 1), (key1466, -2), (key1457, -2), (key1546, 2), (key1559, -1), (key1546, -1), (key1573, 2), (key1596, -1), (key1573, -1), (key1659, -1), (key1655, -1), (key1667, -1), (key1655, -1), (key1667, 2), (key1659, 2), (key1774, -1), (key1772, -1), (key1780, 1), (key1772, 1), (key1790, -1), (key1788, -1), (key1798, 1), (key1790, 1), (key1817, 1), (key1813, 1), (key1825, -1), (key1817, -1), (key1844, 1), (key1839, 1), (key1844, -1), (key1841, -1)]

theorem rawRowCheck6099 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form5 = rawRow6099 := by decide +kernel

def row6099 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6099 : row6099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6099 := by decide +kernel

theorem rowEval6099 (x : Key → ℝ) : Integer.Sparse.eval row6099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6099, Integer.Sparse.eval_collectBalanced, rawRowCheck6099]

def rawRow6100 : Integer.Sparse Key := [(key1397, -2), (key1391, 1), (key1391, 1), (key1447, -2), (key1424, 1), (key1424, 1), (key1466, 1), (key1466, 1), (key1457, 1), (key1457, 1), (key1455, -2), (key1455, -2), (key1559, 2), (key1546, -1), (key1546, -1), (key1596, 2), (key1573, -1), (key1573, -1), (key1667, -1), (key1667, -1), (key1659, -1), (key1659, -1), (key1655, 2), (key1655, 2), (key1780, -1), (key1780, -1), (key1774, 1), (key1774, 1), (key1798, -1), (key1798, -1), (key1788, 1), (key1788, 1), (key1825, 1), (key1825, 1), (key1813, -1), (key1813, -1), (key1841, 1), (key1841, 1), (key1839, -1), (key1839, -1)]

theorem rawRowCheck6100 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form5 = rawRow6100 := by decide +kernel

def row6100 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, 2), (key1447, -2), (key1455, -4), (key1457, 2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -2), (key1825, 2), (key1839, -2), (key1841, 2)]

theorem rowCheck6100 : row6100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6100 := by decide +kernel

theorem rowEval6100 (x : Key → ℝ) : Integer.Sparse.eval row6100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6100, Integer.Sparse.eval_collectBalanced, rawRowCheck6100]

def rawRow6101 : Integer.Sparse Key := [(key1424, -2), (key1455, 1), (key1457, 1), (key1391, -2), (key1455, 1), (key1466, 1), (key1391, 1), (key1397, 1), (key1424, 1), (key1447, 1), (key1457, -2), (key1466, -2), (key1573, 2), (key1655, -1), (key1659, -1), (key1546, 2), (key1655, -1), (key1667, -1), (key1546, -1), (key1559, -1), (key1573, -1), (key1596, -1), (key1659, 2), (key1667, 2), (key1788, -1), (key1790, -1), (key1813, 1), (key1817, 1), (key1772, -1), (key1774, -1), (key1839, 1), (key1844, 1), (key1772, 1), (key1780, 1), (key1841, -1), (key1844, -1), (key1790, 1), (key1798, 1), (key1817, -1), (key1825, -1)]

theorem rawRowCheck6101 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form5 = rawRow6101 := by decide +kernel

def row6101 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6101 : row6101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6101 := by decide +kernel

theorem rowEval6101 (x : Key → ℝ) : Integer.Sparse.eval row6101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6101, Integer.Sparse.eval_collectBalanced, rawRowCheck6101]

def rawRow6102 : Integer.Sparse Key := [(key1424, -2), (key1457, 1), (key1455, 1), (key1391, -2), (key1466, 1), (key1455, 1), (key1397, 1), (key1391, 1), (key1447, 1), (key1424, 1), (key1466, -2), (key1457, -2), (key1573, 2), (key1659, -1), (key1655, -1), (key1546, 2), (key1667, -1), (key1655, -1), (key1559, -1), (key1546, -1), (key1596, -1), (key1573, -1), (key1667, 2), (key1659, 2), (key1790, -1), (key1788, -1), (key1817, 1), (key1813, 1), (key1774, -1), (key1772, -1), (key1844, 1), (key1839, 1), (key1780, 1), (key1772, 1), (key1844, -1), (key1841, -1), (key1798, 1), (key1790, 1), (key1825, -1), (key1817, -1)]

theorem rawRowCheck6102 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form5 = rawRow6102 := by decide +kernel

def row6102 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6102 : row6102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6102 := by decide +kernel

theorem rowEval6102 (x : Key → ℝ) : Integer.Sparse.eval row6102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6102, Integer.Sparse.eval_collectBalanced, rawRowCheck6102]

def rawRow6103 : Integer.Sparse Key := [(key1455, -2), (key1424, 1), (key1457, 1), (key1455, -2), (key1391, 1), (key1466, 1), (key1424, 1), (key1457, 1), (key1391, 1), (key1466, 1), (key1397, -2), (key1447, -2), (key1655, 2), (key1573, -1), (key1659, -1), (key1655, 2), (key1546, -1), (key1667, -1), (key1573, -1), (key1659, -1), (key1546, -1), (key1667, -1), (key1559, 2), (key1596, 2), (key1813, -1), (key1839, -1), (key1788, 1), (key1841, 1), (key1813, -1), (key1839, -1), (key1774, 1), (key1825, 1), (key1788, 1), (key1841, 1), (key1780, -1), (key1798, -1), (key1774, 1), (key1825, 1), (key1780, -1), (key1798, -1)]

theorem rawRowCheck6103 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form5 = rawRow6103 := by decide +kernel

def row6103 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, 2), (key1447, -2), (key1455, -4), (key1457, 2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -2), (key1825, 2), (key1839, -2), (key1841, 2)]

theorem rowCheck6103 : row6103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6103 := by decide +kernel

theorem rowEval6103 (x : Key → ℝ) : Integer.Sparse.eval row6103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6103, Integer.Sparse.eval_collectBalanced, rawRowCheck6103]

def rawRow6104 : Integer.Sparse Key := [(key1455, -2), (key1457, 1), (key1424, 1), (key1455, -2), (key1466, 1), (key1391, 1), (key1457, 1), (key1424, 1), (key1466, 1), (key1391, 1), (key1447, -2), (key1397, -2), (key1655, 2), (key1659, -1), (key1573, -1), (key1655, 2), (key1667, -1), (key1546, -1), (key1659, -1), (key1573, -1), (key1667, -1), (key1546, -1), (key1596, 2), (key1559, 2), (key1839, -1), (key1813, -1), (key1841, 1), (key1788, 1), (key1839, -1), (key1813, -1), (key1825, 1), (key1774, 1), (key1841, 1), (key1788, 1), (key1798, -1), (key1780, -1), (key1825, 1), (key1774, 1), (key1798, -1), (key1780, -1)]

theorem rawRowCheck6104 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form5 = rawRow6104 := by decide +kernel

def row6104 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, 2), (key1447, -2), (key1455, -4), (key1457, 2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -2), (key1825, 2), (key1839, -2), (key1841, 2)]

theorem rowCheck6104 : row6104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6104 := by decide +kernel

theorem rowEval6104 (x : Key → ℝ) : Integer.Sparse.eval row6104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6104, Integer.Sparse.eval_collectBalanced, rawRowCheck6104]

def rawRow6105 : Integer.Sparse Key := [(key1457, -2), (key1424, 1), (key1455, 1), (key1466, -2), (key1391, 1), (key1455, 1), (key1447, 1), (key1466, 1), (key1397, 1), (key1457, 1), (key1391, -2), (key1424, -2), (key1659, 2), (key1573, -1), (key1655, -1), (key1667, 2), (key1546, -1), (key1655, -1), (key1596, -1), (key1667, -1), (key1559, -1), (key1659, -1), (key1546, 2), (key1573, 2), (key1817, -1), (key1841, -1), (key1790, 1), (key1839, 1), (key1825, -1), (key1844, -1), (key1772, 1), (key1813, 1), (key1798, 1), (key1844, 1), (key1772, -1), (key1788, -1), (key1780, 1), (key1817, 1), (key1774, -1), (key1790, -1)]

theorem rawRowCheck6105 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form5 = rawRow6105 := by decide +kernel

def row6105 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6105 : row6105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6105 := by decide +kernel

theorem rowEval6105 (x : Key → ℝ) : Integer.Sparse.eval row6105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6105, Integer.Sparse.eval_collectBalanced, rawRowCheck6105]

def rawRow6106 : Integer.Sparse Key := [(key1457, -2), (key1455, 1), (key1424, 1), (key1466, -2), (key1455, 1), (key1391, 1), (key1466, 1), (key1447, 1), (key1457, 1), (key1397, 1), (key1424, -2), (key1391, -2), (key1659, 2), (key1655, -1), (key1573, -1), (key1667, 2), (key1655, -1), (key1546, -1), (key1667, -1), (key1596, -1), (key1659, -1), (key1559, -1), (key1573, 2), (key1546, 2), (key1841, -1), (key1817, -1), (key1839, 1), (key1790, 1), (key1844, -1), (key1825, -1), (key1813, 1), (key1772, 1), (key1844, 1), (key1798, 1), (key1788, -1), (key1772, -1), (key1817, 1), (key1780, 1), (key1790, -1), (key1774, -1)]

theorem rawRowCheck6106 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form5 = rawRow6106 := by decide +kernel

def row6106 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6106 : row6106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6106 := by decide +kernel

theorem rowEval6106 (x : Key → ℝ) : Integer.Sparse.eval row6106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6106, Integer.Sparse.eval_collectBalanced, rawRowCheck6106]

def rawRow6107 : Integer.Sparse Key := [(key1447, -2), (key1466, 1), (key1466, 1), (key1397, -2), (key1457, 1), (key1457, 1), (key1391, 1), (key1391, 1), (key1424, 1), (key1424, 1), (key1455, -2), (key1455, -2), (key1596, 2), (key1667, -1), (key1667, -1), (key1559, 2), (key1659, -1), (key1659, -1), (key1546, -1), (key1546, -1), (key1573, -1), (key1573, -1), (key1655, 2), (key1655, 2), (key1798, -1), (key1798, -1), (key1825, 1), (key1825, 1), (key1780, -1), (key1780, -1), (key1841, 1), (key1841, 1), (key1774, 1), (key1774, 1), (key1839, -1), (key1839, -1), (key1788, 1), (key1788, 1), (key1813, -1), (key1813, -1)]

theorem rawRowCheck6107 : GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form5 = rawRow6107 := by decide +kernel

def row6107 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, 2), (key1447, -2), (key1455, -4), (key1457, 2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -2), (key1825, 2), (key1839, -2), (key1841, 2)]

theorem rowCheck6107 : row6107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6107 := by decide +kernel

theorem rowEval6107 (x : Key → ℝ) : Integer.Sparse.eval row6107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6107, Integer.Sparse.eval_collectBalanced, rawRowCheck6107]

def rawRow6108 : Integer.Sparse Key := [(key1466, -2), (key1447, 1), (key1466, 1), (key1457, -2), (key1397, 1), (key1457, 1), (key1424, 1), (key1455, 1), (key1391, 1), (key1455, 1), (key1391, -2), (key1424, -2), (key1667, 2), (key1596, -1), (key1667, -1), (key1659, 2), (key1559, -1), (key1659, -1), (key1573, -1), (key1655, -1), (key1546, -1), (key1655, -1), (key1546, 2), (key1573, 2), (key1825, -1), (key1844, -1), (key1798, 1), (key1844, 1), (key1817, -1), (key1841, -1), (key1780, 1), (key1817, 1), (key1790, 1), (key1839, 1), (key1774, -1), (key1790, -1), (key1772, 1), (key1813, 1), (key1772, -1), (key1788, -1)]

theorem rawRowCheck6108 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form5 = rawRow6108 := by decide +kernel

def row6108 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6108 : row6108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6108 := by decide +kernel

theorem rowEval6108 (x : Key → ℝ) : Integer.Sparse.eval row6108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6108, Integer.Sparse.eval_collectBalanced, rawRowCheck6108]

def rawRow6109 : Integer.Sparse Key := [(key1466, -2), (key1466, 1), (key1447, 1), (key1457, -2), (key1457, 1), (key1397, 1), (key1455, 1), (key1424, 1), (key1455, 1), (key1391, 1), (key1424, -2), (key1391, -2), (key1667, 2), (key1667, -1), (key1596, -1), (key1659, 2), (key1659, -1), (key1559, -1), (key1655, -1), (key1573, -1), (key1655, -1), (key1546, -1), (key1573, 2), (key1546, 2), (key1844, -1), (key1825, -1), (key1844, 1), (key1798, 1), (key1841, -1), (key1817, -1), (key1817, 1), (key1780, 1), (key1839, 1), (key1790, 1), (key1790, -1), (key1774, -1), (key1813, 1), (key1772, 1), (key1788, -1), (key1772, -1)]

theorem rawRowCheck6109 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form5 = rawRow6109 := by decide +kernel

def row6109 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6109 : row6109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6109 := by decide +kernel

theorem rowEval6109 (x : Key → ℝ) : Integer.Sparse.eval row6109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6109, Integer.Sparse.eval_collectBalanced, rawRowCheck6109]

def rawRow6110 : Integer.Sparse Key := [(key1296, -2), (key1296, 1), (key1302, 1), (key1573, -2), (key1573, 1), (key1596, 1), (key1788, 1), (key1790, 1), (key1788, 1), (key1798, 1), (key1790, -2), (key1798, -2), (key1316, 2), (key1316, -1), (key1329, -1), (key1424, 2), (key1424, -1), (key1447, -1), (key1813, -1), (key1817, -1), (key1813, -1), (key1825, -1), (key1817, 2), (key1825, 2), (key1337, -1), (key1339, -1), (key1337, 1), (key1345, 1), (key1455, -1), (key1457, -1), (key1457, 1), (key1466, 1), (key1655, 1), (key1659, 1), (key1659, -1), (key1667, -1), (key1839, 1), (key1844, 1), (key1841, -1), (key1844, -1)]

theorem rawRowCheck6110 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form5 = rawRow6110 := by decide +kernel

def row6110 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6110 : row6110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6110 := by decide +kernel

theorem rowEval6110 (x : Key → ℝ) : Integer.Sparse.eval row6110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6110, Integer.Sparse.eval_collectBalanced, rawRowCheck6110]

def rawRow6111 : Integer.Sparse Key := [(key1296, -2), (key1302, 1), (key1296, 1), (key1573, -2), (key1596, 1), (key1573, 1), (key1790, 1), (key1788, 1), (key1798, 1), (key1788, 1), (key1798, -2), (key1790, -2), (key1316, 2), (key1329, -1), (key1316, -1), (key1424, 2), (key1447, -1), (key1424, -1), (key1817, -1), (key1813, -1), (key1825, -1), (key1813, -1), (key1825, 2), (key1817, 2), (key1339, -1), (key1337, -1), (key1345, 1), (key1337, 1), (key1457, -1), (key1455, -1), (key1466, 1), (key1457, 1), (key1659, 1), (key1655, 1), (key1667, -1), (key1659, -1), (key1844, 1), (key1839, 1), (key1844, -1), (key1841, -1)]

theorem rawRowCheck6111 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form5 = rawRow6111 := by decide +kernel

def row6111 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6111 : row6111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6111 := by decide +kernel

theorem rowEval6111 (x : Key → ℝ) : Integer.Sparse.eval row6111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6111, Integer.Sparse.eval_collectBalanced, rawRowCheck6111]

def rawRow6112 : Integer.Sparse Key := [(key1302, -2), (key1296, 1), (key1296, 1), (key1596, -2), (key1573, 1), (key1573, 1), (key1798, 1), (key1798, 1), (key1790, 1), (key1790, 1), (key1788, -2), (key1788, -2), (key1329, 2), (key1316, -1), (key1316, -1), (key1447, 2), (key1424, -1), (key1424, -1), (key1825, -1), (key1825, -1), (key1817, -1), (key1817, -1), (key1813, 2), (key1813, 2), (key1345, -1), (key1345, -1), (key1339, 1), (key1339, 1), (key1466, -1), (key1466, -1), (key1455, 1), (key1455, 1), (key1667, 1), (key1667, 1), (key1655, -1), (key1655, -1), (key1841, 1), (key1841, 1), (key1839, -1), (key1839, -1)]

theorem rawRowCheck6112 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form5 = rawRow6112 := by decide +kernel

def row6112 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1447, 2), (key1455, 2), (key1466, -2), (key1573, 2), (key1596, -2), (key1655, -2), (key1667, 2), (key1788, -4), (key1790, 2), (key1798, 2), (key1813, 4), (key1817, -2), (key1825, -2), (key1839, -2), (key1841, 2)]

theorem rowCheck6112 : row6112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6112 := by decide +kernel

theorem rowEval6112 (x : Key → ℝ) : Integer.Sparse.eval row6112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6112, Integer.Sparse.eval_collectBalanced, rawRowCheck6112]

def rawRow6113 : Integer.Sparse Key := [(key1573, -2), (key1788, 1), (key1790, 1), (key1296, -2), (key1788, 1), (key1798, 1), (key1296, 1), (key1302, 1), (key1573, 1), (key1596, 1), (key1790, -2), (key1798, -2), (key1424, 2), (key1813, -1), (key1817, -1), (key1316, 2), (key1813, -1), (key1825, -1), (key1316, -1), (key1329, -1), (key1424, -1), (key1447, -1), (key1817, 2), (key1825, 2), (key1455, -1), (key1457, -1), (key1655, 1), (key1659, 1), (key1337, -1), (key1339, -1), (key1839, 1), (key1844, 1), (key1337, 1), (key1345, 1), (key1841, -1), (key1844, -1), (key1457, 1), (key1466, 1), (key1659, -1), (key1667, -1)]

theorem rawRowCheck6113 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form5 = rawRow6113 := by decide +kernel

def row6113 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6113 : row6113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6113 := by decide +kernel

theorem rowEval6113 (x : Key → ℝ) : Integer.Sparse.eval row6113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6113, Integer.Sparse.eval_collectBalanced, rawRowCheck6113]

def rawRow6114 : Integer.Sparse Key := [(key1573, -2), (key1790, 1), (key1788, 1), (key1296, -2), (key1798, 1), (key1788, 1), (key1302, 1), (key1296, 1), (key1596, 1), (key1573, 1), (key1798, -2), (key1790, -2), (key1424, 2), (key1817, -1), (key1813, -1), (key1316, 2), (key1825, -1), (key1813, -1), (key1329, -1), (key1316, -1), (key1447, -1), (key1424, -1), (key1825, 2), (key1817, 2), (key1457, -1), (key1455, -1), (key1659, 1), (key1655, 1), (key1339, -1), (key1337, -1), (key1844, 1), (key1839, 1), (key1345, 1), (key1337, 1), (key1844, -1), (key1841, -1), (key1466, 1), (key1457, 1), (key1667, -1), (key1659, -1)]

theorem rawRowCheck6114 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form5 = rawRow6114 := by decide +kernel

def row6114 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6114 : row6114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6114 := by decide +kernel

theorem rowEval6114 (x : Key → ℝ) : Integer.Sparse.eval row6114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6114, Integer.Sparse.eval_collectBalanced, rawRowCheck6114]

def rawRow6115 : Integer.Sparse Key := [(key1788, -2), (key1573, 1), (key1790, 1), (key1788, -2), (key1296, 1), (key1798, 1), (key1573, 1), (key1790, 1), (key1296, 1), (key1798, 1), (key1302, -2), (key1596, -2), (key1813, 2), (key1424, -1), (key1817, -1), (key1813, 2), (key1316, -1), (key1825, -1), (key1424, -1), (key1817, -1), (key1316, -1), (key1825, -1), (key1329, 2), (key1447, 2), (key1655, -1), (key1839, -1), (key1455, 1), (key1841, 1), (key1655, -1), (key1839, -1), (key1339, 1), (key1667, 1), (key1455, 1), (key1841, 1), (key1345, -1), (key1466, -1), (key1339, 1), (key1667, 1), (key1345, -1), (key1466, -1)]

theorem rawRowCheck6115 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form5 = rawRow6115 := by decide +kernel

def row6115 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1447, 2), (key1455, 2), (key1466, -2), (key1573, 2), (key1596, -2), (key1655, -2), (key1667, 2), (key1788, -4), (key1790, 2), (key1798, 2), (key1813, 4), (key1817, -2), (key1825, -2), (key1839, -2), (key1841, 2)]

theorem rowCheck6115 : row6115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6115 := by decide +kernel

theorem rowEval6115 (x : Key → ℝ) : Integer.Sparse.eval row6115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6115, Integer.Sparse.eval_collectBalanced, rawRowCheck6115]

def rawRow6116 : Integer.Sparse Key := [(key1788, -2), (key1790, 1), (key1573, 1), (key1788, -2), (key1798, 1), (key1296, 1), (key1790, 1), (key1573, 1), (key1798, 1), (key1296, 1), (key1596, -2), (key1302, -2), (key1813, 2), (key1817, -1), (key1424, -1), (key1813, 2), (key1825, -1), (key1316, -1), (key1817, -1), (key1424, -1), (key1825, -1), (key1316, -1), (key1447, 2), (key1329, 2), (key1839, -1), (key1655, -1), (key1841, 1), (key1455, 1), (key1839, -1), (key1655, -1), (key1667, 1), (key1339, 1), (key1841, 1), (key1455, 1), (key1466, -1), (key1345, -1), (key1667, 1), (key1339, 1), (key1466, -1), (key1345, -1)]

theorem rawRowCheck6116 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form5 = rawRow6116 := by decide +kernel

def row6116 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1447, 2), (key1455, 2), (key1466, -2), (key1573, 2), (key1596, -2), (key1655, -2), (key1667, 2), (key1788, -4), (key1790, 2), (key1798, 2), (key1813, 4), (key1817, -2), (key1825, -2), (key1839, -2), (key1841, 2)]

theorem rowCheck6116 : row6116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6116 := by decide +kernel

theorem rowEval6116 (x : Key → ℝ) : Integer.Sparse.eval row6116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6116, Integer.Sparse.eval_collectBalanced, rawRowCheck6116]

def rawRow6117 : Integer.Sparse Key := [(key1790, -2), (key1573, 1), (key1788, 1), (key1798, -2), (key1296, 1), (key1788, 1), (key1596, 1), (key1798, 1), (key1302, 1), (key1790, 1), (key1296, -2), (key1573, -2), (key1817, 2), (key1424, -1), (key1813, -1), (key1825, 2), (key1316, -1), (key1813, -1), (key1447, -1), (key1825, -1), (key1329, -1), (key1817, -1), (key1316, 2), (key1424, 2), (key1659, -1), (key1841, -1), (key1457, 1), (key1839, 1), (key1667, -1), (key1844, -1), (key1337, 1), (key1655, 1), (key1466, 1), (key1844, 1), (key1337, -1), (key1455, -1), (key1345, 1), (key1659, 1), (key1339, -1), (key1457, -1)]

theorem rawRowCheck6117 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form5 = rawRow6117 := by decide +kernel

def row6117 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6117 : row6117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6117 := by decide +kernel

theorem rowEval6117 (x : Key → ℝ) : Integer.Sparse.eval row6117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6117, Integer.Sparse.eval_collectBalanced, rawRowCheck6117]

def rawRow6118 : Integer.Sparse Key := [(key1790, -2), (key1788, 1), (key1573, 1), (key1798, -2), (key1788, 1), (key1296, 1), (key1798, 1), (key1596, 1), (key1790, 1), (key1302, 1), (key1573, -2), (key1296, -2), (key1817, 2), (key1813, -1), (key1424, -1), (key1825, 2), (key1813, -1), (key1316, -1), (key1825, -1), (key1447, -1), (key1817, -1), (key1329, -1), (key1424, 2), (key1316, 2), (key1841, -1), (key1659, -1), (key1839, 1), (key1457, 1), (key1844, -1), (key1667, -1), (key1655, 1), (key1337, 1), (key1844, 1), (key1466, 1), (key1455, -1), (key1337, -1), (key1659, 1), (key1345, 1), (key1457, -1), (key1339, -1)]

theorem rawRowCheck6118 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form5 = rawRow6118 := by decide +kernel

def row6118 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6118 : row6118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6118 := by decide +kernel

theorem rowEval6118 (x : Key → ℝ) : Integer.Sparse.eval row6118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6118, Integer.Sparse.eval_collectBalanced, rawRowCheck6118]

def rawRow6119 : Integer.Sparse Key := [(key1596, -2), (key1798, 1), (key1798, 1), (key1302, -2), (key1790, 1), (key1790, 1), (key1296, 1), (key1296, 1), (key1573, 1), (key1573, 1), (key1788, -2), (key1788, -2), (key1447, 2), (key1825, -1), (key1825, -1), (key1329, 2), (key1817, -1), (key1817, -1), (key1316, -1), (key1316, -1), (key1424, -1), (key1424, -1), (key1813, 2), (key1813, 2), (key1466, -1), (key1466, -1), (key1667, 1), (key1667, 1), (key1345, -1), (key1345, -1), (key1841, 1), (key1841, 1), (key1339, 1), (key1339, 1), (key1839, -1), (key1839, -1), (key1455, 1), (key1455, 1), (key1655, -1), (key1655, -1)]

theorem rawRowCheck6119 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form5 = rawRow6119 := by decide +kernel

def row6119 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1447, 2), (key1455, 2), (key1466, -2), (key1573, 2), (key1596, -2), (key1655, -2), (key1667, 2), (key1788, -4), (key1790, 2), (key1798, 2), (key1813, 4), (key1817, -2), (key1825, -2), (key1839, -2), (key1841, 2)]

theorem rowCheck6119 : row6119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6119 := by decide +kernel

theorem rowEval6119 (x : Key → ℝ) : Integer.Sparse.eval row6119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6119, Integer.Sparse.eval_collectBalanced, rawRowCheck6119]

def rawRow6120 : Integer.Sparse Key := [(key1798, -2), (key1596, 1), (key1798, 1), (key1790, -2), (key1302, 1), (key1790, 1), (key1573, 1), (key1788, 1), (key1296, 1), (key1788, 1), (key1296, -2), (key1573, -2), (key1825, 2), (key1447, -1), (key1825, -1), (key1817, 2), (key1329, -1), (key1817, -1), (key1424, -1), (key1813, -1), (key1316, -1), (key1813, -1), (key1316, 2), (key1424, 2), (key1667, -1), (key1844, -1), (key1466, 1), (key1844, 1), (key1659, -1), (key1841, -1), (key1345, 1), (key1659, 1), (key1457, 1), (key1839, 1), (key1339, -1), (key1457, -1), (key1337, 1), (key1655, 1), (key1337, -1), (key1455, -1)]

theorem rawRowCheck6120 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form5 = rawRow6120 := by decide +kernel

def row6120 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6120 : row6120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6120 := by decide +kernel

theorem rowEval6120 (x : Key → ℝ) : Integer.Sparse.eval row6120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6120, Integer.Sparse.eval_collectBalanced, rawRowCheck6120]

def rawRow6121 : Integer.Sparse Key := [(key1798, -2), (key1798, 1), (key1596, 1), (key1790, -2), (key1790, 1), (key1302, 1), (key1788, 1), (key1573, 1), (key1788, 1), (key1296, 1), (key1573, -2), (key1296, -2), (key1825, 2), (key1825, -1), (key1447, -1), (key1817, 2), (key1817, -1), (key1329, -1), (key1813, -1), (key1424, -1), (key1813, -1), (key1316, -1), (key1424, 2), (key1316, 2), (key1844, -1), (key1667, -1), (key1844, 1), (key1466, 1), (key1841, -1), (key1659, -1), (key1659, 1), (key1345, 1), (key1839, 1), (key1457, 1), (key1457, -1), (key1339, -1), (key1655, 1), (key1337, 1), (key1455, -1), (key1337, -1)]

theorem rawRowCheck6121 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form5 = rawRow6121 := by decide +kernel

def row6121 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6121 : row6121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6121 := by decide +kernel

theorem rowEval6121 (x : Key → ℝ) : Integer.Sparse.eval row6121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6121, Integer.Sparse.eval_collectBalanced, rawRowCheck6121]

def rawRow6122 : Integer.Sparse Key := [(key1337, -2), (key1316, 1), (key1339, 1), (key1655, -2), (key1546, 1), (key1667, 1), (key1813, 1), (key1839, 1), (key1772, 1), (key1844, 1), (key1774, -2), (key1825, -2), (key1337, 2), (key1296, -1), (key1345, -1), (key1455, 2), (key1391, -1), (key1466, -1), (key1788, -1), (key1841, -1), (key1772, -1), (key1844, -1), (key1780, 2), (key1798, 2), (key1316, -1), (key1339, -1), (key1296, 1), (key1345, 1), (key1424, -1), (key1457, -1), (key1397, 1), (key1447, 1), (key1573, 1), (key1659, 1), (key1559, -1), (key1596, -1), (key1774, 1), (key1825, 1), (key1780, -1), (key1798, -1)]

theorem rawRowCheck6122 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form5 = rawRow6122 := by decide +kernel

def row6122 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6122 : row6122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6122 := by decide +kernel

theorem rowEval6122 (x : Key → ℝ) : Integer.Sparse.eval row6122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6122, Integer.Sparse.eval_collectBalanced, rawRowCheck6122]

def rawRow6123 : Integer.Sparse Key := [(key1337, -2), (key1339, 1), (key1316, 1), (key1655, -2), (key1667, 1), (key1546, 1), (key1839, 1), (key1813, 1), (key1844, 1), (key1772, 1), (key1825, -2), (key1774, -2), (key1337, 2), (key1345, -1), (key1296, -1), (key1455, 2), (key1466, -1), (key1391, -1), (key1841, -1), (key1788, -1), (key1844, -1), (key1772, -1), (key1798, 2), (key1780, 2), (key1339, -1), (key1316, -1), (key1345, 1), (key1296, 1), (key1457, -1), (key1424, -1), (key1447, 1), (key1397, 1), (key1659, 1), (key1573, 1), (key1596, -1), (key1559, -1), (key1825, 1), (key1774, 1), (key1798, -1), (key1780, -1)]

theorem rawRowCheck6123 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form5 = rawRow6123 := by decide +kernel

def row6123 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6123 : row6123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6123 := by decide +kernel

theorem rowEval6123 (x : Key → ℝ) : Integer.Sparse.eval row6123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6123, Integer.Sparse.eval_collectBalanced, rawRowCheck6123]

def rawRow6124 : Integer.Sparse Key := [(key1339, -2), (key1316, 1), (key1337, 1), (key1667, -2), (key1546, 1), (key1655, 1), (key1825, 1), (key1844, 1), (key1774, 1), (key1839, 1), (key1772, -2), (key1813, -2), (key1345, 2), (key1296, -1), (key1337, -1), (key1466, 2), (key1391, -1), (key1455, -1), (key1798, -1), (key1844, -1), (key1780, -1), (key1841, -1), (key1772, 2), (key1788, 2), (key1329, -1), (key1345, -1), (key1302, 1), (key1339, 1), (key1447, -1), (key1466, -1), (key1391, 1), (key1424, 1), (key1596, 1), (key1667, 1), (key1546, -1), (key1573, -1), (key1780, 1), (key1817, 1), (key1774, -1), (key1790, -1)]

theorem rawRowCheck6124 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form5 = rawRow6124 := by decide +kernel

def row6124 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6124 : row6124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6124 := by decide +kernel

theorem rowEval6124 (x : Key → ℝ) : Integer.Sparse.eval row6124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6124, Integer.Sparse.eval_collectBalanced, rawRowCheck6124]

def rawRow6125 : Integer.Sparse Key := [(key1339, -2), (key1337, 1), (key1316, 1), (key1667, -2), (key1655, 1), (key1546, 1), (key1844, 1), (key1825, 1), (key1839, 1), (key1774, 1), (key1813, -2), (key1772, -2), (key1345, 2), (key1337, -1), (key1296, -1), (key1466, 2), (key1455, -1), (key1391, -1), (key1844, -1), (key1798, -1), (key1841, -1), (key1780, -1), (key1788, 2), (key1772, 2), (key1345, -1), (key1329, -1), (key1339, 1), (key1302, 1), (key1466, -1), (key1447, -1), (key1424, 1), (key1391, 1), (key1667, 1), (key1596, 1), (key1573, -1), (key1546, -1), (key1817, 1), (key1780, 1), (key1790, -1), (key1774, -1)]

theorem rawRowCheck6125 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form5 = rawRow6125 := by decide +kernel

def row6125 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6125 : row6125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6125 := by decide +kernel

theorem rowEval6125 (x : Key → ℝ) : Integer.Sparse.eval row6125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6125, Integer.Sparse.eval_collectBalanced, rawRowCheck6125]

def rawRow6126 : Integer.Sparse Key := [(key1772, -2), (key1546, 1), (key1774, 1), (key1813, -2), (key1316, 1), (key1825, 1), (key1655, 1), (key1839, 1), (key1337, 1), (key1844, 1), (key1339, -2), (key1667, -2), (key1772, 2), (key1391, -1), (key1780, -1), (key1788, 2), (key1296, -1), (key1798, -1), (key1455, -1), (key1841, -1), (key1337, -1), (key1844, -1), (key1345, 2), (key1466, 2), (key1546, -1), (key1774, -1), (key1391, 1), (key1780, 1), (key1573, -1), (key1790, -1), (key1302, 1), (key1596, 1), (key1424, 1), (key1817, 1), (key1329, -1), (key1447, -1), (key1339, 1), (key1667, 1), (key1345, -1), (key1466, -1)]

theorem rawRowCheck6126 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form5 = rawRow6126 := by decide +kernel

def row6126 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6126 : row6126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6126 := by decide +kernel

theorem rowEval6126 (x : Key → ℝ) : Integer.Sparse.eval row6126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6126, Integer.Sparse.eval_collectBalanced, rawRowCheck6126]

def rawRow6127 : Integer.Sparse Key := [(key1772, -2), (key1774, 1), (key1546, 1), (key1813, -2), (key1825, 1), (key1316, 1), (key1839, 1), (key1655, 1), (key1844, 1), (key1337, 1), (key1667, -2), (key1339, -2), (key1772, 2), (key1780, -1), (key1391, -1), (key1788, 2), (key1798, -1), (key1296, -1), (key1841, -1), (key1455, -1), (key1844, -1), (key1337, -1), (key1466, 2), (key1345, 2), (key1774, -1), (key1546, -1), (key1780, 1), (key1391, 1), (key1790, -1), (key1573, -1), (key1596, 1), (key1302, 1), (key1817, 1), (key1424, 1), (key1447, -1), (key1329, -1), (key1667, 1), (key1339, 1), (key1466, -1), (key1345, -1)]

theorem rawRowCheck6127 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form5 = rawRow6127 := by decide +kernel

def row6127 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6127 : row6127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6127 := by decide +kernel

theorem rowEval6127 (x : Key → ℝ) : Integer.Sparse.eval row6127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6127, Integer.Sparse.eval_collectBalanced, rawRowCheck6127]

def rawRow6128 : Integer.Sparse Key := [(key1774, -2), (key1546, 1), (key1772, 1), (key1825, -2), (key1316, 1), (key1813, 1), (key1667, 1), (key1844, 1), (key1339, 1), (key1839, 1), (key1337, -2), (key1655, -2), (key1780, 2), (key1391, -1), (key1772, -1), (key1798, 2), (key1296, -1), (key1788, -1), (key1466, -1), (key1844, -1), (key1345, -1), (key1841, -1), (key1337, 2), (key1455, 2), (key1559, -1), (key1780, -1), (key1397, 1), (key1774, 1), (key1596, -1), (key1798, -1), (key1296, 1), (key1573, 1), (key1447, 1), (key1825, 1), (key1316, -1), (key1424, -1), (key1345, 1), (key1659, 1), (key1339, -1), (key1457, -1)]

theorem rawRowCheck6128 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form5 = rawRow6128 := by decide +kernel

def row6128 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6128 : row6128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6128 := by decide +kernel

theorem rowEval6128 (x : Key → ℝ) : Integer.Sparse.eval row6128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6128, Integer.Sparse.eval_collectBalanced, rawRowCheck6128]

def rawRow6129 : Integer.Sparse Key := [(key1774, -2), (key1772, 1), (key1546, 1), (key1825, -2), (key1813, 1), (key1316, 1), (key1844, 1), (key1667, 1), (key1839, 1), (key1339, 1), (key1655, -2), (key1337, -2), (key1780, 2), (key1772, -1), (key1391, -1), (key1798, 2), (key1788, -1), (key1296, -1), (key1844, -1), (key1466, -1), (key1841, -1), (key1345, -1), (key1455, 2), (key1337, 2), (key1780, -1), (key1559, -1), (key1774, 1), (key1397, 1), (key1798, -1), (key1596, -1), (key1573, 1), (key1296, 1), (key1825, 1), (key1447, 1), (key1424, -1), (key1316, -1), (key1659, 1), (key1345, 1), (key1457, -1), (key1339, -1)]

theorem rawRowCheck6129 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form5 = rawRow6129 := by decide +kernel

def row6129 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6129 : row6129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6129 := by decide +kernel

theorem rowEval6129 (x : Key → ℝ) : Integer.Sparse.eval row6129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6129, Integer.Sparse.eval_collectBalanced, rawRowCheck6129]

def rawRow6130 : Integer.Sparse Key := [(key1655, -2), (key1813, 1), (key1839, 1), (key1337, -2), (key1772, 1), (key1844, 1), (key1316, 1), (key1339, 1), (key1546, 1), (key1667, 1), (key1774, -2), (key1825, -2), (key1455, 2), (key1788, -1), (key1841, -1), (key1337, 2), (key1772, -1), (key1844, -1), (key1296, -1), (key1345, -1), (key1391, -1), (key1466, -1), (key1780, 2), (key1798, 2), (key1424, -1), (key1457, -1), (key1573, 1), (key1659, 1), (key1316, -1), (key1339, -1), (key1774, 1), (key1825, 1), (key1296, 1), (key1345, 1), (key1780, -1), (key1798, -1), (key1397, 1), (key1447, 1), (key1559, -1), (key1596, -1)]

theorem rawRowCheck6130 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form5 = rawRow6130 := by decide +kernel

def row6130 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6130 : row6130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6130 := by decide +kernel

theorem rowEval6130 (x : Key → ℝ) : Integer.Sparse.eval row6130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6130, Integer.Sparse.eval_collectBalanced, rawRowCheck6130]

def rawRow6131 : Integer.Sparse Key := [(key1655, -2), (key1839, 1), (key1813, 1), (key1337, -2), (key1844, 1), (key1772, 1), (key1339, 1), (key1316, 1), (key1667, 1), (key1546, 1), (key1825, -2), (key1774, -2), (key1455, 2), (key1841, -1), (key1788, -1), (key1337, 2), (key1844, -1), (key1772, -1), (key1345, -1), (key1296, -1), (key1466, -1), (key1391, -1), (key1798, 2), (key1780, 2), (key1457, -1), (key1424, -1), (key1659, 1), (key1573, 1), (key1339, -1), (key1316, -1), (key1825, 1), (key1774, 1), (key1345, 1), (key1296, 1), (key1798, -1), (key1780, -1), (key1447, 1), (key1397, 1), (key1596, -1), (key1559, -1)]

theorem rawRowCheck6131 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form5 = rawRow6131 := by decide +kernel

def row6131 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6131 : row6131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6131 := by decide +kernel

theorem rowEval6131 (x : Key → ℝ) : Integer.Sparse.eval row6131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6131, Integer.Sparse.eval_collectBalanced, rawRowCheck6131]

def rawRow6132 : Integer.Sparse Key := [(key1813, -2), (key1655, 1), (key1839, 1), (key1772, -2), (key1337, 1), (key1844, 1), (key1546, 1), (key1774, 1), (key1316, 1), (key1825, 1), (key1339, -2), (key1667, -2), (key1788, 2), (key1455, -1), (key1841, -1), (key1772, 2), (key1337, -1), (key1844, -1), (key1391, -1), (key1780, -1), (key1296, -1), (key1798, -1), (key1345, 2), (key1466, 2), (key1573, -1), (key1790, -1), (key1424, 1), (key1817, 1), (key1546, -1), (key1774, -1), (key1339, 1), (key1667, 1), (key1391, 1), (key1780, 1), (key1345, -1), (key1466, -1), (key1302, 1), (key1596, 1), (key1329, -1), (key1447, -1)]

theorem rawRowCheck6132 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form5 = rawRow6132 := by decide +kernel

def row6132 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6132 : row6132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6132 := by decide +kernel

theorem rowEval6132 (x : Key → ℝ) : Integer.Sparse.eval row6132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6132, Integer.Sparse.eval_collectBalanced, rawRowCheck6132]

def rawRow6133 : Integer.Sparse Key := [(key1813, -2), (key1839, 1), (key1655, 1), (key1772, -2), (key1844, 1), (key1337, 1), (key1774, 1), (key1546, 1), (key1825, 1), (key1316, 1), (key1667, -2), (key1339, -2), (key1788, 2), (key1841, -1), (key1455, -1), (key1772, 2), (key1844, -1), (key1337, -1), (key1780, -1), (key1391, -1), (key1798, -1), (key1296, -1), (key1466, 2), (key1345, 2), (key1790, -1), (key1573, -1), (key1817, 1), (key1424, 1), (key1774, -1), (key1546, -1), (key1667, 1), (key1339, 1), (key1780, 1), (key1391, 1), (key1466, -1), (key1345, -1), (key1596, 1), (key1302, 1), (key1447, -1), (key1329, -1)]

theorem rawRowCheck6133 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form5 = rawRow6133 := by decide +kernel

def row6133 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6133 : row6133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6133 := by decide +kernel

theorem rowEval6133 (x : Key → ℝ) : Integer.Sparse.eval row6133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6133, Integer.Sparse.eval_collectBalanced, rawRowCheck6133]

def rawRow6134 : Integer.Sparse Key := [(key1667, -2), (key1825, 1), (key1844, 1), (key1339, -2), (key1774, 1), (key1839, 1), (key1316, 1), (key1337, 1), (key1546, 1), (key1655, 1), (key1772, -2), (key1813, -2), (key1466, 2), (key1798, -1), (key1844, -1), (key1345, 2), (key1780, -1), (key1841, -1), (key1296, -1), (key1337, -1), (key1391, -1), (key1455, -1), (key1772, 2), (key1788, 2), (key1447, -1), (key1466, -1), (key1596, 1), (key1667, 1), (key1329, -1), (key1345, -1), (key1780, 1), (key1817, 1), (key1302, 1), (key1339, 1), (key1774, -1), (key1790, -1), (key1391, 1), (key1424, 1), (key1546, -1), (key1573, -1)]

theorem rawRowCheck6134 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form5 = rawRow6134 := by decide +kernel

def row6134 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6134 : row6134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6134 := by decide +kernel

theorem rowEval6134 (x : Key → ℝ) : Integer.Sparse.eval row6134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6134, Integer.Sparse.eval_collectBalanced, rawRowCheck6134]

def rawRow6135 : Integer.Sparse Key := [(key1667, -2), (key1844, 1), (key1825, 1), (key1339, -2), (key1839, 1), (key1774, 1), (key1337, 1), (key1316, 1), (key1655, 1), (key1546, 1), (key1813, -2), (key1772, -2), (key1466, 2), (key1844, -1), (key1798, -1), (key1345, 2), (key1841, -1), (key1780, -1), (key1337, -1), (key1296, -1), (key1455, -1), (key1391, -1), (key1788, 2), (key1772, 2), (key1466, -1), (key1447, -1), (key1667, 1), (key1596, 1), (key1345, -1), (key1329, -1), (key1817, 1), (key1780, 1), (key1339, 1), (key1302, 1), (key1790, -1), (key1774, -1), (key1424, 1), (key1391, 1), (key1573, -1), (key1546, -1)]

theorem rawRowCheck6135 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form5 = rawRow6135 := by decide +kernel

def row6135 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

theorem rowCheck6135 : row6135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6135 := by decide +kernel

theorem rowEval6135 (x : Key → ℝ) : Integer.Sparse.eval row6135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6135, Integer.Sparse.eval_collectBalanced, rawRowCheck6135]

def rawRow6136 : Integer.Sparse Key := [(key1825, -2), (key1667, 1), (key1844, 1), (key1774, -2), (key1339, 1), (key1839, 1), (key1546, 1), (key1772, 1), (key1316, 1), (key1813, 1), (key1337, -2), (key1655, -2), (key1798, 2), (key1466, -1), (key1844, -1), (key1780, 2), (key1345, -1), (key1841, -1), (key1391, -1), (key1772, -1), (key1296, -1), (key1788, -1), (key1337, 2), (key1455, 2), (key1596, -1), (key1798, -1), (key1447, 1), (key1825, 1), (key1559, -1), (key1780, -1), (key1345, 1), (key1659, 1), (key1397, 1), (key1774, 1), (key1339, -1), (key1457, -1), (key1296, 1), (key1573, 1), (key1316, -1), (key1424, -1)]

theorem rawRowCheck6136 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form5 = rawRow6136 := by decide +kernel

def row6136 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6136 : row6136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6136 := by decide +kernel

theorem rowEval6136 (x : Key → ℝ) : Integer.Sparse.eval row6136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6136, Integer.Sparse.eval_collectBalanced, rawRowCheck6136]

def rawRow6137 : Integer.Sparse Key := [(key1825, -2), (key1844, 1), (key1667, 1), (key1774, -2), (key1839, 1), (key1339, 1), (key1772, 1), (key1546, 1), (key1813, 1), (key1316, 1), (key1655, -2), (key1337, -2), (key1798, 2), (key1844, -1), (key1466, -1), (key1780, 2), (key1841, -1), (key1345, -1), (key1772, -1), (key1391, -1), (key1788, -1), (key1296, -1), (key1455, 2), (key1337, 2), (key1798, -1), (key1596, -1), (key1825, 1), (key1447, 1), (key1780, -1), (key1559, -1), (key1659, 1), (key1345, 1), (key1774, 1), (key1397, 1), (key1457, -1), (key1339, -1), (key1573, 1), (key1296, 1), (key1424, -1), (key1316, -1)]

theorem rawRowCheck6137 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form5 = rawRow6137 := by decide +kernel

def row6137 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

theorem rowCheck6137 : row6137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6137 := by decide +kernel

theorem rowEval6137 (x : Key → ℝ) : Integer.Sparse.eval row6137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6137, Integer.Sparse.eval_collectBalanced, rawRowCheck6137]

def rawRow6138 : Integer.Sparse Key := [(key236, -1), (key239, -1), (key239, 2), (key248, -1), (key251, -1), (key248, 2), (key260, 2), (key251, -1), (key260, -1), (key267, 2), (key267, -1), (key271, -1), (key302, 1), (key305, 1), (key305, -2), (key316, 1), (key319, 1), (key316, -2), (key328, -2), (key319, 1), (key328, 1), (key335, -2), (key335, 1), (key340, 1), (key385, -1), (key397, -1), (key388, 1), (key397, 1), (key406, 1), (key418, 1), (key409, -1), (key418, -1), (key435, -1), (key442, -1), (key435, 1), (key450, 1), (key467, 1), (key469, 1), (key467, -1), (key475, -1)]

theorem rawRowCheck6138 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form6 = rawRow6138 := by decide +kernel

def row6138 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

theorem rowCheck6138 : row6138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6138 := by decide +kernel

theorem rowEval6138 (x : Key → ℝ) : Integer.Sparse.eval row6138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6138, Integer.Sparse.eval_collectBalanced, rawRowCheck6138]

def rawRow6139 : Integer.Sparse Key := [(key239, -1), (key236, -1), (key239, 2), (key251, -1), (key248, -1), (key260, 2), (key248, 2), (key260, -1), (key251, -1), (key267, 2), (key271, -1), (key267, -1), (key305, 1), (key302, 1), (key305, -2), (key319, 1), (key316, 1), (key328, -2), (key316, -2), (key328, 1), (key319, 1), (key335, -2), (key340, 1), (key335, 1), (key397, -1), (key385, -1), (key397, 1), (key388, 1), (key418, 1), (key406, 1), (key418, -1), (key409, -1), (key442, -1), (key435, -1), (key450, 1), (key435, 1), (key469, 1), (key467, 1), (key475, -1), (key467, -1)]

theorem rawRowCheck6139 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form6 = rawRow6139 := by decide +kernel

def row6139 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

theorem rowCheck6139 : row6139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6139 := by decide +kernel

theorem rowEval6139 (x : Key → ℝ) : Integer.Sparse.eval row6139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6139, Integer.Sparse.eval_collectBalanced, rawRowCheck6139]

def rawRow6140 : Integer.Sparse Key := [(key239, -1), (key239, -1), (key236, 2), (key260, -1), (key260, -1), (key251, 2), (key251, 2), (key248, -1), (key248, -1), (key271, 2), (key267, -1), (key267, -1), (key305, 1), (key305, 1), (key302, -2), (key328, 1), (key328, 1), (key319, -2), (key319, -2), (key316, 1), (key316, 1), (key340, -2), (key335, 1), (key335, 1), (key388, -1), (key388, -1), (key385, 1), (key385, 1), (key409, 1), (key409, 1), (key406, -1), (key406, -1), (key450, -1), (key450, -1), (key442, 1), (key442, 1), (key475, 1), (key475, 1), (key469, -1), (key469, -1)]

theorem rawRowCheck6140 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form6 = rawRow6140 := by decide +kernel

def row6140 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key251, 4), (key260, -2), (key267, -2), (key271, 2), (key302, -2), (key305, 2), (key316, 2), (key319, -4), (key328, 2), (key335, 2), (key340, -2), (key385, 2), (key388, -2), (key406, -2), (key409, 2), (key442, 2), (key450, -2), (key469, -2), (key475, 2)]

theorem rowCheck6140 : row6140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6140 := by decide +kernel

theorem rowEval6140 (x : Key → ℝ) : Integer.Sparse.eval row6140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6140, Integer.Sparse.eval_collectBalanced, rawRowCheck6140]

def rawRow6141 : Integer.Sparse Key := [(key248, -1), (key251, -1), (key260, 2), (key236, -1), (key239, -1), (key248, 2), (key260, 2), (key267, -1), (key271, -1), (key239, 2), (key251, -1), (key260, -1), (key316, 1), (key319, 1), (key335, -2), (key302, 1), (key305, 1), (key316, -2), (key328, -2), (key335, 1), (key340, 1), (key305, -2), (key319, 1), (key328, 1), (key435, -1), (key442, -1), (key467, 1), (key469, 1), (key435, 1), (key450, 1), (key467, -1), (key475, -1), (key385, -1), (key397, -1), (key406, 1), (key418, 1), (key388, 1), (key397, 1), (key409, -1), (key418, -1)]

theorem rawRowCheck6141 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form6 = rawRow6141 := by decide +kernel

def row6141 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 3), (key267, -1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

theorem rowCheck6141 : row6141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6141 := by decide +kernel

theorem rowEval6141 (x : Key → ℝ) : Integer.Sparse.eval row6141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6141, Integer.Sparse.eval_collectBalanced, rawRowCheck6141]

def rawRow6142 : Integer.Sparse Key := [(key251, -1), (key248, -1), (key260, 2), (key239, -1), (key236, -1), (key260, 2), (key248, 2), (key271, -1), (key267, -1), (key239, 2), (key260, -1), (key251, -1), (key319, 1), (key316, 1), (key335, -2), (key305, 1), (key302, 1), (key328, -2), (key316, -2), (key340, 1), (key335, 1), (key305, -2), (key328, 1), (key319, 1), (key442, -1), (key435, -1), (key469, 1), (key467, 1), (key450, 1), (key435, 1), (key475, -1), (key467, -1), (key397, -1), (key385, -1), (key418, 1), (key406, 1), (key397, 1), (key388, 1), (key418, -1), (key409, -1)]

theorem rawRowCheck6142 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form6 = rawRow6142 := by decide +kernel

def row6142 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 3), (key267, -1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

theorem rowCheck6142 : row6142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6142 := by decide +kernel

theorem rowEval6142 (x : Key → ℝ) : Integer.Sparse.eval row6142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6142, Integer.Sparse.eval_collectBalanced, rawRowCheck6142]

def rawRow6143 : Integer.Sparse Key := [(key248, -1), (key260, -1), (key251, 2), (key248, -1), (key260, -1), (key236, 2), (key271, 2), (key239, -1), (key260, -1), (key251, 2), (key239, -1), (key260, -1), (key316, 1), (key335, 1), (key319, -2), (key316, 1), (key335, 1), (key302, -2), (key340, -2), (key305, 1), (key328, 1), (key319, -2), (key305, 1), (key328, 1), (key406, -1), (key469, -1), (key409, 1), (key442, 1), (key385, 1), (key475, 1), (key388, -1), (key450, -1), (key406, -1), (key469, -1), (key385, 1), (key475, 1), (key409, 1), (key442, 1), (key388, -1), (key450, -1)]

theorem rawRowCheck6143 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form6 = rawRow6143 := by decide +kernel

def row6143 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key251, 4), (key260, -4), (key271, 2), (key302, -2), (key305, 2), (key316, 2), (key319, -4), (key328, 2), (key335, 2), (key340, -2), (key385, 2), (key388, -2), (key406, -2), (key409, 2), (key442, 2), (key450, -2), (key469, -2), (key475, 2)]

theorem rowCheck6143 : row6143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6143 := by decide +kernel

theorem rowEval6143 (x : Key → ℝ) : Integer.Sparse.eval row6143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6143, Integer.Sparse.eval_collectBalanced, rawRowCheck6143]

end MUB6.Certificate.GramRows

end OAI
