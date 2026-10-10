import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow12672 : Integer.Sparse Key := [(key1380, -2), (key1375, -2), (key1380, -2), (key1729, -2), (key1724, -2), (key1759, -2), (key1724, -2), (key1759, -2), (key1729, -2), (key1942, -2), (key1956, -2), (key1942, -2), (key1371, 1), (key1365, 1), (key1380, 1), (key1365, 1), (key1380, 1), (key1371, 1), (key1497, 1), (key1491, 1), (key1520, 1), (key1491, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1717, 1), (key1748, 1), (key1717, 1), (key1748, 1), (key1729, 1), (key1942, 1), (key1939, 1), (key1951, 1), (key1939, 1), (key1951, 1), (key1942, 1)]

theorem rawRowCheck12672 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form5 = rawRow12672 := by decide +kernel

def row12672 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

theorem rowCheck12672 : row12672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12672 := by decide +kernel

theorem rowEval12672 (x : Key → ℝ) : Integer.Sparse.eval row12672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12672, Integer.Sparse.eval_collectBalanced, rawRowCheck12672]

def rawRow12673 : Integer.Sparse Key := [(key1380, -2), (key1380, -2), (key1375, -2), (key1759, -2), (key1759, -2), (key1729, -2), (key1729, -2), (key1724, -2), (key1724, -2), (key1956, -2), (key1942, -2), (key1942, -2), (key1380, 1), (key1380, 1), (key1371, 1), (key1371, 1), (key1365, 1), (key1365, 1), (key1520, 1), (key1520, 1), (key1497, 1), (key1497, 1), (key1491, 1), (key1491, 1), (key1748, 1), (key1748, 1), (key1729, 1), (key1729, 1), (key1717, 1), (key1717, 1), (key1951, 1), (key1951, 1), (key1942, 1), (key1942, 1), (key1939, 1), (key1939, 1)]

theorem rawRowCheck12673 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form5 = rawRow12673 := by decide +kernel

def row12673 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

theorem rowCheck12673 : row12673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12673 := by decide +kernel

theorem rowEval12673 (x : Key → ℝ) : Integer.Sparse.eval row12673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12673, Integer.Sparse.eval_collectBalanced, rawRowCheck12673]

def rawRow12674 : Integer.Sparse Key := [(key1724, -2), (key1729, -2), (key1942, -2), (key1375, -2), (key1380, -2), (key1724, -2), (key1759, -2), (key1942, -2), (key1956, -2), (key1380, -2), (key1729, -2), (key1759, -2), (key1491, 1), (key1497, 1), (key1717, 1), (key1729, 1), (key1939, 1), (key1942, 1), (key1365, 1), (key1371, 1), (key1717, 1), (key1748, 1), (key1939, 1), (key1951, 1), (key1365, 1), (key1380, 1), (key1491, 1), (key1520, 1), (key1942, 1), (key1951, 1), (key1371, 1), (key1380, 1), (key1497, 1), (key1520, 1), (key1729, 1), (key1748, 1)]

theorem rawRowCheck12674 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form5 = rawRow12674 := by decide +kernel

def row12674 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

theorem rowCheck12674 : row12674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12674 := by decide +kernel

theorem rowEval12674 (x : Key → ℝ) : Integer.Sparse.eval row12674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12674, Integer.Sparse.eval_collectBalanced, rawRowCheck12674]

def rawRow12675 : Integer.Sparse Key := [(key1729, -2), (key1724, -2), (key1942, -2), (key1380, -2), (key1375, -2), (key1759, -2), (key1724, -2), (key1956, -2), (key1942, -2), (key1380, -2), (key1759, -2), (key1729, -2), (key1497, 1), (key1491, 1), (key1729, 1), (key1717, 1), (key1942, 1), (key1939, 1), (key1371, 1), (key1365, 1), (key1748, 1), (key1717, 1), (key1951, 1), (key1939, 1), (key1380, 1), (key1365, 1), (key1520, 1), (key1491, 1), (key1951, 1), (key1942, 1), (key1380, 1), (key1371, 1), (key1520, 1), (key1497, 1), (key1748, 1), (key1729, 1)]

theorem rawRowCheck12675 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form5 = rawRow12675 := by decide +kernel

def row12675 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

theorem rowCheck12675 : row12675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12675 := by decide +kernel

theorem rowEval12675 (x : Key → ℝ) : Integer.Sparse.eval row12675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12675, Integer.Sparse.eval_collectBalanced, rawRowCheck12675]

def rawRow12676 : Integer.Sparse Key := [(key1724, -2), (key1942, -2), (key1729, -2), (key1724, -2), (key1942, -2), (key1375, -2), (key1956, -2), (key1380, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1759, -2), (key1717, 1), (key1939, 1), (key1491, 1), (key1942, 1), (key1497, 1), (key1729, 1), (key1717, 1), (key1939, 1), (key1365, 1), (key1951, 1), (key1371, 1), (key1748, 1), (key1491, 1), (key1942, 1), (key1365, 1), (key1951, 1), (key1380, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1371, 1), (key1748, 1), (key1380, 1), (key1520, 1)]

theorem rawRowCheck12676 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form5 = rawRow12676 := by decide +kernel

def row12676 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

theorem rowCheck12676 : row12676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12676 := by decide +kernel

theorem rowEval12676 (x : Key → ℝ) : Integer.Sparse.eval row12676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12676, Integer.Sparse.eval_collectBalanced, rawRowCheck12676]

def rawRow12677 : Integer.Sparse Key := [(key1942, -2), (key1724, -2), (key1729, -2), (key1942, -2), (key1724, -2), (key1956, -2), (key1375, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1759, -2), (key1380, -2), (key1939, 1), (key1717, 1), (key1942, 1), (key1491, 1), (key1729, 1), (key1497, 1), (key1939, 1), (key1717, 1), (key1951, 1), (key1365, 1), (key1748, 1), (key1371, 1), (key1942, 1), (key1491, 1), (key1951, 1), (key1365, 1), (key1520, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1748, 1), (key1371, 1), (key1520, 1), (key1380, 1)]

theorem rawRowCheck12677 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form5 = rawRow12677 := by decide +kernel

def row12677 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

theorem rowCheck12677 : row12677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12677 := by decide +kernel

theorem rowEval12677 (x : Key → ℝ) : Integer.Sparse.eval row12677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck12677, Integer.Sparse.eval_collectBalanced, rawRowCheck12677]

def rawRow12678 : Integer.Sparse Key := [(key1729, -2), (key1942, -2), (key1724, -2), (key1759, -2), (key1956, -2), (key1380, -2), (key1942, -2), (key1375, -2), (key1724, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1729, 1), (key1942, 1), (key1497, 1), (key1939, 1), (key1491, 1), (key1717, 1), (key1748, 1), (key1951, 1), (key1371, 1), (key1939, 1), (key1365, 1), (key1717, 1), (key1520, 1), (key1951, 1), (key1380, 1), (key1942, 1), (key1365, 1), (key1491, 1), (key1520, 1), (key1748, 1), (key1380, 1), (key1729, 1), (key1371, 1), (key1497, 1)]

theorem rawRowCheck12678 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form5 = rawRow12678 := by decide +kernel

def row12678 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

theorem rowCheck12678 : row12678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12678 := by decide +kernel

theorem rowEval12678 (x : Key → ℝ) : Integer.Sparse.eval row12678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12678, Integer.Sparse.eval_collectBalanced, rawRowCheck12678]

def rawRow12679 : Integer.Sparse Key := [(key1942, -2), (key1729, -2), (key1724, -2), (key1956, -2), (key1759, -2), (key1942, -2), (key1380, -2), (key1724, -2), (key1375, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1942, 1), (key1729, 1), (key1939, 1), (key1497, 1), (key1717, 1), (key1491, 1), (key1951, 1), (key1748, 1), (key1939, 1), (key1371, 1), (key1717, 1), (key1365, 1), (key1951, 1), (key1520, 1), (key1942, 1), (key1380, 1), (key1491, 1), (key1365, 1), (key1748, 1), (key1520, 1), (key1729, 1), (key1380, 1), (key1497, 1), (key1371, 1)]

theorem rawRowCheck12679 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form5 = rawRow12679 := by decide +kernel

def row12679 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

theorem rowCheck12679 : row12679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12679 := by decide +kernel

theorem rowEval12679 (x : Key → ℝ) : Integer.Sparse.eval row12679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck12679, Integer.Sparse.eval_collectBalanced, rawRowCheck12679]

def rawRow12680 : Integer.Sparse Key := [(key1759, -2), (key1759, -2), (key1956, -2), (key1380, -2), (key1380, -2), (key1729, -2), (key1729, -2), (key1942, -2), (key1942, -2), (key1375, -2), (key1724, -2), (key1724, -2), (key1520, 1), (key1520, 1), (key1748, 1), (key1748, 1), (key1951, 1), (key1951, 1), (key1380, 1), (key1380, 1), (key1729, 1), (key1729, 1), (key1942, 1), (key1942, 1), (key1371, 1), (key1371, 1), (key1497, 1), (key1497, 1), (key1939, 1), (key1939, 1), (key1365, 1), (key1365, 1), (key1491, 1), (key1491, 1), (key1717, 1), (key1717, 1)]

theorem rawRowCheck12680 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form5 = rawRow12680 := by decide +kernel

def row12680 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

theorem rowCheck12680 : row12680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12680 := by decide +kernel

theorem rowEval12680 (x : Key → ℝ) : Integer.Sparse.eval row12680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12680, Integer.Sparse.eval_collectBalanced, rawRowCheck12680]

def rawRow12681 : Integer.Sparse Key := [(key1759, -2), (key1956, -2), (key1759, -2), (key1729, -2), (key1942, -2), (key1380, -2), (key1942, -2), (key1380, -2), (key1729, -2), (key1724, -2), (key1375, -2), (key1724, -2), (key1748, 1), (key1951, 1), (key1520, 1), (key1951, 1), (key1520, 1), (key1748, 1), (key1729, 1), (key1942, 1), (key1380, 1), (key1942, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1939, 1), (key1371, 1), (key1939, 1), (key1371, 1), (key1497, 1), (key1491, 1), (key1717, 1), (key1365, 1), (key1717, 1), (key1365, 1), (key1491, 1)]

theorem rawRowCheck12681 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form5 = rawRow12681 := by decide +kernel

def row12681 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

theorem rowCheck12681 : row12681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12681 := by decide +kernel

theorem rowEval12681 (x : Key → ℝ) : Integer.Sparse.eval row12681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12681, Integer.Sparse.eval_collectBalanced, rawRowCheck12681]

def rawRow12682 : Integer.Sparse Key := [(key1956, -2), (key1759, -2), (key1759, -2), (key1942, -2), (key1729, -2), (key1942, -2), (key1380, -2), (key1729, -2), (key1380, -2), (key1724, -2), (key1724, -2), (key1375, -2), (key1951, 1), (key1748, 1), (key1951, 1), (key1520, 1), (key1748, 1), (key1520, 1), (key1942, 1), (key1729, 1), (key1942, 1), (key1380, 1), (key1729, 1), (key1380, 1), (key1939, 1), (key1497, 1), (key1939, 1), (key1371, 1), (key1497, 1), (key1371, 1), (key1717, 1), (key1491, 1), (key1717, 1), (key1365, 1), (key1491, 1), (key1365, 1)]

theorem rawRowCheck12682 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form5 = rawRow12682 := by decide +kernel

def row12682 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

theorem rowCheck12682 : row12682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12682 := by decide +kernel

theorem rowEval12682 (x : Key → ℝ) : Integer.Sparse.eval row12682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck12682, Integer.Sparse.eval_collectBalanced, rawRowCheck12682]

def rawRow12683 : Integer.Sparse Key := [(key1705, -24), (key1282, 6), (key1705, 6), (key1754, 6), (key1754, 6)]

theorem rawRowCheck12683 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form6 = rawRow12683 := by decide +kernel

def row12683 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

theorem rowCheck12683 : row12683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12683 := by decide +kernel

theorem rowEval12683 (x : Key → ℝ) : Integer.Sparse.eval row12683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12683, Integer.Sparse.eval_collectBalanced, rawRowCheck12683]

def rawRow12684 : Integer.Sparse Key := [(key1705, -24), (key1282, 6), (key1754, 6), (key1705, 6), (key1754, 6)]

theorem rawRowCheck12684 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form6 = rawRow12684 := by decide +kernel

def row12684 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

theorem rowCheck12684 : row12684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12684 := by decide +kernel

theorem rowEval12684 (x : Key → ℝ) : Integer.Sparse.eval row12684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12684, Integer.Sparse.eval_collectBalanced, rawRowCheck12684]

def rawRow12685 : Integer.Sparse Key := [(key1705, -24), (key1282, 6), (key1754, 6), (key1754, 6), (key1705, 6)]

theorem rawRowCheck12685 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form6 = rawRow12685 := by decide +kernel

def row12685 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

theorem rowCheck12685 : row12685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12685 := by decide +kernel

theorem rowEval12685 (x : Key → ℝ) : Integer.Sparse.eval row12685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12685, Integer.Sparse.eval_collectBalanced, rawRowCheck12685]

def rawRow12686 : Integer.Sparse Key := [(key1705, -24), (key1705, 6), (key1282, 6), (key1754, 6), (key1754, 6)]

theorem rawRowCheck12686 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form6 = rawRow12686 := by decide +kernel

def row12686 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

theorem rowCheck12686 : row12686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12686 := by decide +kernel

theorem rowEval12686 (x : Key → ℝ) : Integer.Sparse.eval row12686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12686, Integer.Sparse.eval_collectBalanced, rawRowCheck12686]

def rawRow12687 : Integer.Sparse Key := [(key1705, -24), (key1705, 6), (key1754, 6), (key1282, 6), (key1754, 6)]

theorem rawRowCheck12687 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form6 = rawRow12687 := by decide +kernel

def row12687 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

theorem rowCheck12687 : row12687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12687 := by decide +kernel

theorem rowEval12687 (x : Key → ℝ) : Integer.Sparse.eval row12687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12687, Integer.Sparse.eval_collectBalanced, rawRowCheck12687]

def rawRow12688 : Integer.Sparse Key := [(key1705, -24), (key1705, 6), (key1754, 6), (key1754, 6), (key1282, 6)]

theorem rawRowCheck12688 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form6 = rawRow12688 := by decide +kernel

def row12688 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

theorem rowCheck12688 : row12688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12688 := by decide +kernel

theorem rowEval12688 (x : Key → ℝ) : Integer.Sparse.eval row12688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12688, Integer.Sparse.eval_collectBalanced, rawRowCheck12688]

def rawRow12689 : Integer.Sparse Key := [(key1705, -24), (key1754, 6), (key1282, 6), (key1705, 6), (key1754, 6)]

theorem rawRowCheck12689 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form6 = rawRow12689 := by decide +kernel

def row12689 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

theorem rowCheck12689 : row12689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12689 := by decide +kernel

theorem rowEval12689 (x : Key → ℝ) : Integer.Sparse.eval row12689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12689, Integer.Sparse.eval_collectBalanced, rawRowCheck12689]

def rawRow12690 : Integer.Sparse Key := [(key1705, -24), (key1754, 6), (key1282, 6), (key1754, 6), (key1705, 6)]

theorem rawRowCheck12690 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form6 = rawRow12690 := by decide +kernel

def row12690 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

theorem rowCheck12690 : row12690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12690 := by decide +kernel

theorem rowEval12690 (x : Key → ℝ) : Integer.Sparse.eval row12690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12690, Integer.Sparse.eval_collectBalanced, rawRowCheck12690]

def rawRow12691 : Integer.Sparse Key := [(key1705, -24), (key1754, 6), (key1705, 6), (key1282, 6), (key1754, 6)]

theorem rawRowCheck12691 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form6 = rawRow12691 := by decide +kernel

def row12691 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

theorem rowCheck12691 : row12691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12691 := by decide +kernel

theorem rowEval12691 (x : Key → ℝ) : Integer.Sparse.eval row12691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12691, Integer.Sparse.eval_collectBalanced, rawRowCheck12691]

def rawRow12692 : Integer.Sparse Key := [(key1705, -24), (key1754, 6), (key1705, 6), (key1754, 6), (key1282, 6)]

theorem rawRowCheck12692 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form6 = rawRow12692 := by decide +kernel

def row12692 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

theorem rowCheck12692 : row12692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12692 := by decide +kernel

theorem rowEval12692 (x : Key → ℝ) : Integer.Sparse.eval row12692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12692, Integer.Sparse.eval_collectBalanced, rawRowCheck12692]

def rawRow12693 : Integer.Sparse Key := [(key1705, -24), (key1754, 6), (key1754, 6), (key1282, 6), (key1705, 6)]

theorem rawRowCheck12693 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form6 = rawRow12693 := by decide +kernel

def row12693 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

theorem rowCheck12693 : row12693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12693 := by decide +kernel

theorem rowEval12693 (x : Key → ℝ) : Integer.Sparse.eval row12693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12693, Integer.Sparse.eval_collectBalanced, rawRowCheck12693]

def rawRow12694 : Integer.Sparse Key := [(key1705, -24), (key1754, 6), (key1754, 6), (key1705, 6), (key1282, 6)]

theorem rawRowCheck12694 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form6 = rawRow12694 := by decide +kernel

def row12694 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

theorem rowCheck12694 : row12694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12694 := by decide +kernel

theorem rowEval12694 (x : Key → ℝ) : Integer.Sparse.eval row12694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12694, Integer.Sparse.eval_collectBalanced, rawRowCheck12694]

def rawRow12695 : Integer.Sparse Key := [(key1754, -24), (key1282, 6), (key1705, 6), (key1705, 6), (key1754, 6)]

theorem rawRowCheck12695 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form6 = rawRow12695 := by decide +kernel

def row12695 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

theorem rowCheck12695 : row12695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12695 := by decide +kernel

theorem rowEval12695 (x : Key → ℝ) : Integer.Sparse.eval row12695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12695, Integer.Sparse.eval_collectBalanced, rawRowCheck12695]

def rawRow12696 : Integer.Sparse Key := [(key1754, -24), (key1282, 6), (key1705, 6), (key1754, 6), (key1705, 6)]

theorem rawRowCheck12696 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form6 = rawRow12696 := by decide +kernel

def row12696 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

theorem rowCheck12696 : row12696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12696 := by decide +kernel

theorem rowEval12696 (x : Key → ℝ) : Integer.Sparse.eval row12696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12696, Integer.Sparse.eval_collectBalanced, rawRowCheck12696]

def rawRow12697 : Integer.Sparse Key := [(key1754, -24), (key1282, 6), (key1754, 6), (key1705, 6), (key1705, 6)]

theorem rawRowCheck12697 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form6 = rawRow12697 := by decide +kernel

def row12697 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

theorem rowCheck12697 : row12697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12697 := by decide +kernel

theorem rowEval12697 (x : Key → ℝ) : Integer.Sparse.eval row12697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12697, Integer.Sparse.eval_collectBalanced, rawRowCheck12697]

def rawRow12698 : Integer.Sparse Key := [(key1754, -24), (key1705, 6), (key1282, 6), (key1705, 6), (key1754, 6)]

theorem rawRowCheck12698 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form6 = rawRow12698 := by decide +kernel

def row12698 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

theorem rowCheck12698 : row12698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12698 := by decide +kernel

theorem rowEval12698 (x : Key → ℝ) : Integer.Sparse.eval row12698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12698, Integer.Sparse.eval_collectBalanced, rawRowCheck12698]

def rawRow12699 : Integer.Sparse Key := [(key1754, -24), (key1705, 6), (key1282, 6), (key1754, 6), (key1705, 6)]

theorem rawRowCheck12699 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form6 = rawRow12699 := by decide +kernel

def row12699 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

theorem rowCheck12699 : row12699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12699 := by decide +kernel

theorem rowEval12699 (x : Key → ℝ) : Integer.Sparse.eval row12699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12699, Integer.Sparse.eval_collectBalanced, rawRowCheck12699]

def rawRow12700 : Integer.Sparse Key := [(key1754, -24), (key1705, 6), (key1705, 6), (key1282, 6), (key1754, 6)]

theorem rawRowCheck12700 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form6 = rawRow12700 := by decide +kernel

def row12700 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

theorem rowCheck12700 : row12700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12700 := by decide +kernel

theorem rowEval12700 (x : Key → ℝ) : Integer.Sparse.eval row12700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12700, Integer.Sparse.eval_collectBalanced, rawRowCheck12700]

def rawRow12701 : Integer.Sparse Key := [(key1754, -24), (key1705, 6), (key1705, 6), (key1754, 6), (key1282, 6)]

theorem rawRowCheck12701 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form6 = rawRow12701 := by decide +kernel

def row12701 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

theorem rowCheck12701 : row12701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12701 := by decide +kernel

theorem rowEval12701 (x : Key → ℝ) : Integer.Sparse.eval row12701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12701, Integer.Sparse.eval_collectBalanced, rawRowCheck12701]

def rawRow12702 : Integer.Sparse Key := [(key1754, -24), (key1705, 6), (key1754, 6), (key1282, 6), (key1705, 6)]

theorem rawRowCheck12702 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form6 = rawRow12702 := by decide +kernel

def row12702 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

theorem rowCheck12702 : row12702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12702 := by decide +kernel

theorem rowEval12702 (x : Key → ℝ) : Integer.Sparse.eval row12702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12702, Integer.Sparse.eval_collectBalanced, rawRowCheck12702]

def rawRow12703 : Integer.Sparse Key := [(key1754, -24), (key1705, 6), (key1754, 6), (key1705, 6), (key1282, 6)]

theorem rawRowCheck12703 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form6 = rawRow12703 := by decide +kernel

def row12703 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

theorem rowCheck12703 : row12703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12703 := by decide +kernel

theorem rowEval12703 (x : Key → ℝ) : Integer.Sparse.eval row12703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12703, Integer.Sparse.eval_collectBalanced, rawRowCheck12703]

def rawRow12704 : Integer.Sparse Key := [(key1754, -24), (key1754, 6), (key1282, 6), (key1705, 6), (key1705, 6)]

theorem rawRowCheck12704 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form6 = rawRow12704 := by decide +kernel

def row12704 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

theorem rowCheck12704 : row12704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12704 := by decide +kernel

theorem rowEval12704 (x : Key → ℝ) : Integer.Sparse.eval row12704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12704, Integer.Sparse.eval_collectBalanced, rawRowCheck12704]

def rawRow12705 : Integer.Sparse Key := [(key1754, -24), (key1754, 6), (key1705, 6), (key1282, 6), (key1705, 6)]

theorem rawRowCheck12705 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form6 = rawRow12705 := by decide +kernel

def row12705 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

theorem rowCheck12705 : row12705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12705 := by decide +kernel

theorem rowEval12705 (x : Key → ℝ) : Integer.Sparse.eval row12705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12705, Integer.Sparse.eval_collectBalanced, rawRowCheck12705]

def rawRow12706 : Integer.Sparse Key := [(key1754, -24), (key1754, 6), (key1705, 6), (key1705, 6), (key1282, 6)]

theorem rawRowCheck12706 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form6 = rawRow12706 := by decide +kernel

def row12706 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

theorem rowCheck12706 : row12706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12706 := by decide +kernel

theorem rowEval12706 (x : Key → ℝ) : Integer.Sparse.eval row12706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12706, Integer.Sparse.eval_collectBalanced, rawRowCheck12706]

def rawRow12707 : Integer.Sparse Key := [(key1491, -2), (key1491, -2), (key1497, -2), (key1717, -2), (key1717, -2), (key1724, -2), (key1724, -2), (key1729, -2), (key1729, -2), (key1939, -2), (key1942, -2), (key1942, -2), (key1365, 2), (key1365, 2), (key1371, 2), (key1717, 2), (key1717, 2), (key1742, 2), (key1742, 2), (key1748, 2), (key1748, 2), (key1939, 2), (key1951, 2), (key1951, 2)]

theorem rawRowCheck12707 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form7 = rawRow12707 := by decide +kernel

def row12707 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

theorem rowCheck12707 : row12707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12707 := by decide +kernel

theorem rowEval12707 (x : Key → ℝ) : Integer.Sparse.eval row12707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12707, Integer.Sparse.eval_collectBalanced, rawRowCheck12707]

def rawRow12708 : Integer.Sparse Key := [(key1491, -2), (key1497, -2), (key1491, -2), (key1724, -2), (key1729, -2), (key1717, -2), (key1729, -2), (key1717, -2), (key1724, -2), (key1942, -2), (key1939, -2), (key1942, -2), (key1365, 2), (key1371, 2), (key1365, 2), (key1742, 2), (key1748, 2), (key1717, 2), (key1748, 2), (key1717, 2), (key1742, 2), (key1951, 2), (key1939, 2), (key1951, 2)]

theorem rawRowCheck12708 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form7 = rawRow12708 := by decide +kernel

def row12708 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

theorem rowCheck12708 : row12708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12708 := by decide +kernel

theorem rowEval12708 (x : Key → ℝ) : Integer.Sparse.eval row12708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12708, Integer.Sparse.eval_collectBalanced, rawRowCheck12708]

def rawRow12709 : Integer.Sparse Key := [(key1497, -2), (key1491, -2), (key1491, -2), (key1729, -2), (key1724, -2), (key1729, -2), (key1717, -2), (key1724, -2), (key1717, -2), (key1942, -2), (key1942, -2), (key1939, -2), (key1371, 2), (key1365, 2), (key1365, 2), (key1748, 2), (key1742, 2), (key1748, 2), (key1717, 2), (key1742, 2), (key1717, 2), (key1951, 2), (key1951, 2), (key1939, 2)]

theorem rawRowCheck12709 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form7 = rawRow12709 := by decide +kernel

def row12709 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

theorem rowCheck12709 : row12709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12709 := by decide +kernel

theorem rowEval12709 (x : Key → ℝ) : Integer.Sparse.eval row12709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12709, Integer.Sparse.eval_collectBalanced, rawRowCheck12709]

def rawRow12710 : Integer.Sparse Key := [(key1717, -2), (key1717, -2), (key1939, -2), (key1491, -2), (key1491, -2), (key1724, -2), (key1724, -2), (key1942, -2), (key1942, -2), (key1497, -2), (key1729, -2), (key1729, -2), (key1717, 2), (key1717, 2), (key1939, 2), (key1365, 2), (key1365, 2), (key1742, 2), (key1742, 2), (key1951, 2), (key1951, 2), (key1371, 2), (key1748, 2), (key1748, 2)]

theorem rawRowCheck12710 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form7 = rawRow12710 := by decide +kernel

def row12710 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

theorem rowCheck12710 : row12710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12710 := by decide +kernel

theorem rowEval12710 (x : Key → ℝ) : Integer.Sparse.eval row12710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12710, Integer.Sparse.eval_collectBalanced, rawRowCheck12710]

def rawRow12711 : Integer.Sparse Key := [(key1717, -2), (key1939, -2), (key1717, -2), (key1724, -2), (key1942, -2), (key1491, -2), (key1942, -2), (key1491, -2), (key1724, -2), (key1729, -2), (key1497, -2), (key1729, -2), (key1717, 2), (key1939, 2), (key1717, 2), (key1742, 2), (key1951, 2), (key1365, 2), (key1951, 2), (key1365, 2), (key1742, 2), (key1748, 2), (key1371, 2), (key1748, 2)]

theorem rawRowCheck12711 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form7 = rawRow12711 := by decide +kernel

def row12711 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

theorem rowCheck12711 : row12711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12711 := by decide +kernel

theorem rowEval12711 (x : Key → ℝ) : Integer.Sparse.eval row12711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12711, Integer.Sparse.eval_collectBalanced, rawRowCheck12711]

def rawRow12712 : Integer.Sparse Key := [(key1939, -2), (key1717, -2), (key1717, -2), (key1942, -2), (key1724, -2), (key1942, -2), (key1491, -2), (key1724, -2), (key1491, -2), (key1729, -2), (key1729, -2), (key1497, -2), (key1939, 2), (key1717, 2), (key1717, 2), (key1951, 2), (key1742, 2), (key1951, 2), (key1365, 2), (key1742, 2), (key1365, 2), (key1748, 2), (key1748, 2), (key1371, 2)]

theorem rawRowCheck12712 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form7 = rawRow12712 := by decide +kernel

def row12712 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

theorem rowCheck12712 : row12712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12712 := by decide +kernel

theorem rowEval12712 (x : Key → ℝ) : Integer.Sparse.eval row12712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck12712, Integer.Sparse.eval_collectBalanced, rawRowCheck12712]

def rawRow12713 : Integer.Sparse Key := [(key1724, -2), (key1729, -2), (key1942, -2), (key1491, -2), (key1497, -2), (key1717, -2), (key1729, -2), (key1939, -2), (key1942, -2), (key1491, -2), (key1717, -2), (key1724, -2), (key1742, 2), (key1748, 2), (key1951, 2), (key1365, 2), (key1371, 2), (key1717, 2), (key1748, 2), (key1939, 2), (key1951, 2), (key1365, 2), (key1717, 2), (key1742, 2)]

theorem rawRowCheck12713 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form7 = rawRow12713 := by decide +kernel

def row12713 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

theorem rowCheck12713 : row12713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12713 := by decide +kernel

theorem rowEval12713 (x : Key → ℝ) : Integer.Sparse.eval row12713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12713, Integer.Sparse.eval_collectBalanced, rawRowCheck12713]

def rawRow12714 : Integer.Sparse Key := [(key1729, -2), (key1724, -2), (key1942, -2), (key1497, -2), (key1491, -2), (key1729, -2), (key1717, -2), (key1942, -2), (key1939, -2), (key1491, -2), (key1724, -2), (key1717, -2), (key1748, 2), (key1742, 2), (key1951, 2), (key1371, 2), (key1365, 2), (key1748, 2), (key1717, 2), (key1951, 2), (key1939, 2), (key1365, 2), (key1742, 2), (key1717, 2)]

theorem rawRowCheck12714 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form7 = rawRow12714 := by decide +kernel

def row12714 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

theorem rowCheck12714 : row12714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12714 := by decide +kernel

theorem rowEval12714 (x : Key → ℝ) : Integer.Sparse.eval row12714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12714, Integer.Sparse.eval_collectBalanced, rawRowCheck12714]

def rawRow12715 : Integer.Sparse Key := [(key1724, -2), (key1942, -2), (key1729, -2), (key1717, -2), (key1939, -2), (key1491, -2), (key1942, -2), (key1497, -2), (key1729, -2), (key1717, -2), (key1491, -2), (key1724, -2), (key1742, 2), (key1951, 2), (key1748, 2), (key1717, 2), (key1939, 2), (key1365, 2), (key1951, 2), (key1371, 2), (key1748, 2), (key1717, 2), (key1365, 2), (key1742, 2)]

theorem rawRowCheck12715 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form7 = rawRow12715 := by decide +kernel

def row12715 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

theorem rowCheck12715 : row12715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12715 := by decide +kernel

theorem rowEval12715 (x : Key → ℝ) : Integer.Sparse.eval row12715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12715, Integer.Sparse.eval_collectBalanced, rawRowCheck12715]

def rawRow12716 : Integer.Sparse Key := [(key1942, -2), (key1724, -2), (key1729, -2), (key1939, -2), (key1717, -2), (key1942, -2), (key1491, -2), (key1729, -2), (key1497, -2), (key1717, -2), (key1724, -2), (key1491, -2), (key1951, 2), (key1742, 2), (key1748, 2), (key1939, 2), (key1717, 2), (key1951, 2), (key1365, 2), (key1748, 2), (key1371, 2), (key1717, 2), (key1742, 2), (key1365, 2)]

theorem rawRowCheck12716 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form7 = rawRow12716 := by decide +kernel

def row12716 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

theorem rowCheck12716 : row12716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12716 := by decide +kernel

theorem rowEval12716 (x : Key → ℝ) : Integer.Sparse.eval row12716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck12716, Integer.Sparse.eval_collectBalanced, rawRowCheck12716]

def rawRow12717 : Integer.Sparse Key := [(key1729, -2), (key1942, -2), (key1724, -2), (key1729, -2), (key1942, -2), (key1497, -2), (key1939, -2), (key1491, -2), (key1717, -2), (key1724, -2), (key1491, -2), (key1717, -2), (key1748, 2), (key1951, 2), (key1742, 2), (key1748, 2), (key1951, 2), (key1371, 2), (key1939, 2), (key1365, 2), (key1717, 2), (key1742, 2), (key1365, 2), (key1717, 2)]

theorem rawRowCheck12717 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form7 = rawRow12717 := by decide +kernel

def row12717 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

theorem rowCheck12717 : row12717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12717 := by decide +kernel

theorem rowEval12717 (x : Key → ℝ) : Integer.Sparse.eval row12717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12717, Integer.Sparse.eval_collectBalanced, rawRowCheck12717]

def rawRow12718 : Integer.Sparse Key := [(key1942, -2), (key1729, -2), (key1724, -2), (key1942, -2), (key1729, -2), (key1939, -2), (key1497, -2), (key1717, -2), (key1491, -2), (key1724, -2), (key1717, -2), (key1491, -2), (key1951, 2), (key1748, 2), (key1742, 2), (key1951, 2), (key1748, 2), (key1939, 2), (key1371, 2), (key1717, 2), (key1365, 2), (key1742, 2), (key1717, 2), (key1365, 2)]

theorem rawRowCheck12718 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form7 = rawRow12718 := by decide +kernel

def row12718 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

theorem rowCheck12718 : row12718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12718 := by decide +kernel

theorem rowEval12718 (x : Key → ℝ) : Integer.Sparse.eval row12718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck12718, Integer.Sparse.eval_collectBalanced, rawRowCheck12718]

def rawRow12719 : Integer.Sparse Key := [(key1514, -2), (key1520, -2), (key1520, -2), (key1742, -2), (key1748, -2), (key1742, -2), (key1759, -2), (key1748, -2), (key1759, -2), (key1951, -2), (key1951, -2), (key1956, -2), (key1375, 2), (key1380, 2), (key1380, 2), (key1724, 2), (key1729, 2), (key1724, 2), (key1759, 2), (key1729, 2), (key1759, 2), (key1942, 2), (key1942, 2), (key1956, 2)]

theorem rawRowCheck12719 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form7 = rawRow12719 := by decide +kernel

def row12719 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

theorem rowCheck12719 : row12719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12719 := by decide +kernel

theorem rowEval12719 (x : Key → ℝ) : Integer.Sparse.eval row12719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12719, Integer.Sparse.eval_collectBalanced, rawRowCheck12719]

def rawRow12720 : Integer.Sparse Key := [(key1520, -2), (key1514, -2), (key1520, -2), (key1748, -2), (key1742, -2), (key1759, -2), (key1742, -2), (key1759, -2), (key1748, -2), (key1951, -2), (key1956, -2), (key1951, -2), (key1380, 2), (key1375, 2), (key1380, 2), (key1729, 2), (key1724, 2), (key1759, 2), (key1724, 2), (key1759, 2), (key1729, 2), (key1942, 2), (key1956, 2), (key1942, 2)]

theorem rawRowCheck12720 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form7 = rawRow12720 := by decide +kernel

def row12720 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

theorem rowCheck12720 : row12720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12720 := by decide +kernel

theorem rowEval12720 (x : Key → ℝ) : Integer.Sparse.eval row12720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12720, Integer.Sparse.eval_collectBalanced, rawRowCheck12720]

def rawRow12721 : Integer.Sparse Key := [(key1520, -2), (key1520, -2), (key1514, -2), (key1759, -2), (key1759, -2), (key1748, -2), (key1748, -2), (key1742, -2), (key1742, -2), (key1956, -2), (key1951, -2), (key1951, -2), (key1380, 2), (key1380, 2), (key1375, 2), (key1759, 2), (key1759, 2), (key1729, 2), (key1729, 2), (key1724, 2), (key1724, 2), (key1956, 2), (key1942, 2), (key1942, 2)]

theorem rawRowCheck12721 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form7 = rawRow12721 := by decide +kernel

def row12721 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

theorem rowCheck12721 : row12721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12721 := by decide +kernel

theorem rowEval12721 (x : Key → ℝ) : Integer.Sparse.eval row12721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12721, Integer.Sparse.eval_collectBalanced, rawRowCheck12721]

def rawRow12722 : Integer.Sparse Key := [(key1742, -2), (key1748, -2), (key1951, -2), (key1514, -2), (key1520, -2), (key1742, -2), (key1759, -2), (key1951, -2), (key1956, -2), (key1520, -2), (key1748, -2), (key1759, -2), (key1724, 2), (key1729, 2), (key1942, 2), (key1375, 2), (key1380, 2), (key1724, 2), (key1759, 2), (key1942, 2), (key1956, 2), (key1380, 2), (key1729, 2), (key1759, 2)]

theorem rawRowCheck12722 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form7 = rawRow12722 := by decide +kernel

def row12722 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

theorem rowCheck12722 : row12722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12722 := by decide +kernel

theorem rowEval12722 (x : Key → ℝ) : Integer.Sparse.eval row12722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12722, Integer.Sparse.eval_collectBalanced, rawRowCheck12722]

def rawRow12723 : Integer.Sparse Key := [(key1748, -2), (key1742, -2), (key1951, -2), (key1520, -2), (key1514, -2), (key1759, -2), (key1742, -2), (key1956, -2), (key1951, -2), (key1520, -2), (key1759, -2), (key1748, -2), (key1729, 2), (key1724, 2), (key1942, 2), (key1380, 2), (key1375, 2), (key1759, 2), (key1724, 2), (key1956, 2), (key1942, 2), (key1380, 2), (key1759, 2), (key1729, 2)]

theorem rawRowCheck12723 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form7 = rawRow12723 := by decide +kernel

def row12723 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

theorem rowCheck12723 : row12723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12723 := by decide +kernel

theorem rowEval12723 (x : Key → ℝ) : Integer.Sparse.eval row12723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12723, Integer.Sparse.eval_collectBalanced, rawRowCheck12723]

def rawRow12724 : Integer.Sparse Key := [(key1742, -2), (key1951, -2), (key1748, -2), (key1742, -2), (key1951, -2), (key1514, -2), (key1956, -2), (key1520, -2), (key1759, -2), (key1748, -2), (key1520, -2), (key1759, -2), (key1724, 2), (key1942, 2), (key1729, 2), (key1724, 2), (key1942, 2), (key1375, 2), (key1956, 2), (key1380, 2), (key1759, 2), (key1729, 2), (key1380, 2), (key1759, 2)]

theorem rawRowCheck12724 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form7 = rawRow12724 := by decide +kernel

def row12724 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

theorem rowCheck12724 : row12724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12724 := by decide +kernel

theorem rowEval12724 (x : Key → ℝ) : Integer.Sparse.eval row12724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12724, Integer.Sparse.eval_collectBalanced, rawRowCheck12724]

def rawRow12725 : Integer.Sparse Key := [(key1951, -2), (key1742, -2), (key1748, -2), (key1951, -2), (key1742, -2), (key1956, -2), (key1514, -2), (key1759, -2), (key1520, -2), (key1748, -2), (key1759, -2), (key1520, -2), (key1942, 2), (key1724, 2), (key1729, 2), (key1942, 2), (key1724, 2), (key1956, 2), (key1375, 2), (key1759, 2), (key1380, 2), (key1729, 2), (key1759, 2), (key1380, 2)]

theorem rawRowCheck12725 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form7 = rawRow12725 := by decide +kernel

def row12725 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

theorem rowCheck12725 : row12725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12725 := by decide +kernel

theorem rowEval12725 (x : Key → ℝ) : Integer.Sparse.eval row12725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck12725, Integer.Sparse.eval_collectBalanced, rawRowCheck12725]

def rawRow12726 : Integer.Sparse Key := [(key1748, -2), (key1951, -2), (key1742, -2), (key1759, -2), (key1956, -2), (key1520, -2), (key1951, -2), (key1514, -2), (key1742, -2), (key1759, -2), (key1520, -2), (key1748, -2), (key1729, 2), (key1942, 2), (key1724, 2), (key1759, 2), (key1956, 2), (key1380, 2), (key1942, 2), (key1375, 2), (key1724, 2), (key1759, 2), (key1380, 2), (key1729, 2)]

theorem rawRowCheck12726 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form7 = rawRow12726 := by decide +kernel

def row12726 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

theorem rowCheck12726 : row12726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12726 := by decide +kernel

theorem rowEval12726 (x : Key → ℝ) : Integer.Sparse.eval row12726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12726, Integer.Sparse.eval_collectBalanced, rawRowCheck12726]

def rawRow12727 : Integer.Sparse Key := [(key1951, -2), (key1748, -2), (key1742, -2), (key1956, -2), (key1759, -2), (key1951, -2), (key1520, -2), (key1742, -2), (key1514, -2), (key1759, -2), (key1748, -2), (key1520, -2), (key1942, 2), (key1729, 2), (key1724, 2), (key1956, 2), (key1759, 2), (key1942, 2), (key1380, 2), (key1724, 2), (key1375, 2), (key1759, 2), (key1729, 2), (key1380, 2)]

theorem rawRowCheck12727 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form7 = rawRow12727 := by decide +kernel

def row12727 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

theorem rowCheck12727 : row12727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12727 := by decide +kernel

theorem rowEval12727 (x : Key → ℝ) : Integer.Sparse.eval row12727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck12727, Integer.Sparse.eval_collectBalanced, rawRowCheck12727]

def rawRow12728 : Integer.Sparse Key := [(key1759, -2), (key1759, -2), (key1956, -2), (key1520, -2), (key1520, -2), (key1748, -2), (key1748, -2), (key1951, -2), (key1951, -2), (key1514, -2), (key1742, -2), (key1742, -2), (key1759, 2), (key1759, 2), (key1956, 2), (key1380, 2), (key1380, 2), (key1729, 2), (key1729, 2), (key1942, 2), (key1942, 2), (key1375, 2), (key1724, 2), (key1724, 2)]

theorem rawRowCheck12728 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form7 = rawRow12728 := by decide +kernel

def row12728 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

theorem rowCheck12728 : row12728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12728 := by decide +kernel

theorem rowEval12728 (x : Key → ℝ) : Integer.Sparse.eval row12728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12728, Integer.Sparse.eval_collectBalanced, rawRowCheck12728]

def rawRow12729 : Integer.Sparse Key := [(key1759, -2), (key1956, -2), (key1759, -2), (key1748, -2), (key1951, -2), (key1520, -2), (key1951, -2), (key1520, -2), (key1748, -2), (key1742, -2), (key1514, -2), (key1742, -2), (key1759, 2), (key1956, 2), (key1759, 2), (key1729, 2), (key1942, 2), (key1380, 2), (key1942, 2), (key1380, 2), (key1729, 2), (key1724, 2), (key1375, 2), (key1724, 2)]

theorem rawRowCheck12729 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form7 = rawRow12729 := by decide +kernel

def row12729 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

theorem rowCheck12729 : row12729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12729 := by decide +kernel

theorem rowEval12729 (x : Key → ℝ) : Integer.Sparse.eval row12729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12729, Integer.Sparse.eval_collectBalanced, rawRowCheck12729]

def rawRow12730 : Integer.Sparse Key := [(key1956, -2), (key1759, -2), (key1759, -2), (key1951, -2), (key1748, -2), (key1951, -2), (key1520, -2), (key1748, -2), (key1520, -2), (key1742, -2), (key1742, -2), (key1514, -2), (key1956, 2), (key1759, 2), (key1759, 2), (key1942, 2), (key1729, 2), (key1942, 2), (key1380, 2), (key1729, 2), (key1380, 2), (key1724, 2), (key1724, 2), (key1375, 2)]

theorem rawRowCheck12730 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form7 = rawRow12730 := by decide +kernel

def row12730 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

theorem rowCheck12730 : row12730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12730 := by decide +kernel

theorem rowEval12730 (x : Key → ℝ) : Integer.Sparse.eval row12730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck12730, Integer.Sparse.eval_collectBalanced, rawRowCheck12730]

def rawRow12731 : Integer.Sparse Key := [(key284, -2), (key284, -2), (key287, -2), (key510, -2), (key510, -2), (key542, -2), (key542, -2), (key546, -2), (key546, -2), (key669, -2), (key679, -2), (key679, -2), (key284, 1), (key284, 1), (key293, 1), (key293, 1), (key299, 1), (key299, 1), (key353, 1), (key353, 1), (key370, 1), (key370, 1), (key373, 1), (key373, 1), (key521, 1), (key521, 1), (key542, 1), (key542, 1), (key563, 1), (key563, 1), (key673, 1), (key673, 1), (key679, 1), (key679, 1), (key684, 1), (key684, 1)]

theorem rawRowCheck12731 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form8 = rawRow12731 := by decide +kernel

def row12731 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

theorem rowCheck12731 : row12731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12731 := by decide +kernel

theorem rowEval12731 (x : Key → ℝ) : Integer.Sparse.eval row12731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12731, Integer.Sparse.eval_collectBalanced, rawRowCheck12731]

def rawRow12732 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key284, -2), (key542, -2), (key546, -2), (key510, -2), (key546, -2), (key510, -2), (key542, -2), (key679, -2), (key669, -2), (key679, -2), (key293, 1), (key299, 1), (key284, 1), (key299, 1), (key284, 1), (key293, 1), (key370, 1), (key373, 1), (key353, 1), (key373, 1), (key353, 1), (key370, 1), (key542, 1), (key563, 1), (key521, 1), (key563, 1), (key521, 1), (key542, 1), (key679, 1), (key684, 1), (key673, 1), (key684, 1), (key673, 1), (key679, 1)]

theorem rawRowCheck12732 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form8 = rawRow12732 := by decide +kernel

def row12732 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

theorem rowCheck12732 : row12732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12732 := by decide +kernel

theorem rowEval12732 (x : Key → ℝ) : Integer.Sparse.eval row12732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12732, Integer.Sparse.eval_collectBalanced, rawRowCheck12732]

def rawRow12733 : Integer.Sparse Key := [(key287, -2), (key284, -2), (key284, -2), (key546, -2), (key542, -2), (key546, -2), (key510, -2), (key542, -2), (key510, -2), (key679, -2), (key679, -2), (key669, -2), (key299, 1), (key293, 1), (key299, 1), (key284, 1), (key293, 1), (key284, 1), (key373, 1), (key370, 1), (key373, 1), (key353, 1), (key370, 1), (key353, 1), (key563, 1), (key542, 1), (key563, 1), (key521, 1), (key542, 1), (key521, 1), (key684, 1), (key679, 1), (key684, 1), (key673, 1), (key679, 1), (key673, 1)]

theorem rawRowCheck12733 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form8 = rawRow12733 := by decide +kernel

def row12733 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

theorem rowCheck12733 : row12733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12733 := by decide +kernel

theorem rowEval12733 (x : Key → ℝ) : Integer.Sparse.eval row12733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12733, Integer.Sparse.eval_collectBalanced, rawRowCheck12733]

def rawRow12734 : Integer.Sparse Key := [(key510, -2), (key510, -2), (key669, -2), (key284, -2), (key284, -2), (key542, -2), (key542, -2), (key679, -2), (key679, -2), (key287, -2), (key546, -2), (key546, -2), (key353, 1), (key353, 1), (key521, 1), (key521, 1), (key673, 1), (key673, 1), (key284, 1), (key284, 1), (key542, 1), (key542, 1), (key679, 1), (key679, 1), (key293, 1), (key293, 1), (key370, 1), (key370, 1), (key684, 1), (key684, 1), (key299, 1), (key299, 1), (key373, 1), (key373, 1), (key563, 1), (key563, 1)]

theorem rawRowCheck12734 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form8 = rawRow12734 := by decide +kernel

def row12734 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

theorem rowCheck12734 : row12734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12734 := by decide +kernel

theorem rowEval12734 (x : Key → ℝ) : Integer.Sparse.eval row12734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12734, Integer.Sparse.eval_collectBalanced, rawRowCheck12734]

def rawRow12735 : Integer.Sparse Key := [(key510, -2), (key669, -2), (key510, -2), (key542, -2), (key679, -2), (key284, -2), (key679, -2), (key284, -2), (key542, -2), (key546, -2), (key287, -2), (key546, -2), (key521, 1), (key673, 1), (key353, 1), (key673, 1), (key353, 1), (key521, 1), (key542, 1), (key679, 1), (key284, 1), (key679, 1), (key284, 1), (key542, 1), (key370, 1), (key684, 1), (key293, 1), (key684, 1), (key293, 1), (key370, 1), (key373, 1), (key563, 1), (key299, 1), (key563, 1), (key299, 1), (key373, 1)]

theorem rawRowCheck12735 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form8 = rawRow12735 := by decide +kernel

def row12735 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

theorem rowCheck12735 : row12735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12735 := by decide +kernel

theorem rowEval12735 (x : Key → ℝ) : Integer.Sparse.eval row12735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12735, Integer.Sparse.eval_collectBalanced, rawRowCheck12735]

def rawRow12736 : Integer.Sparse Key := [(key669, -2), (key510, -2), (key510, -2), (key679, -2), (key542, -2), (key679, -2), (key284, -2), (key542, -2), (key284, -2), (key546, -2), (key546, -2), (key287, -2), (key673, 1), (key521, 1), (key673, 1), (key353, 1), (key521, 1), (key353, 1), (key679, 1), (key542, 1), (key679, 1), (key284, 1), (key542, 1), (key284, 1), (key684, 1), (key370, 1), (key684, 1), (key293, 1), (key370, 1), (key293, 1), (key563, 1), (key373, 1), (key563, 1), (key299, 1), (key373, 1), (key299, 1)]

theorem rawRowCheck12736 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form8 = rawRow12736 := by decide +kernel

def row12736 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

theorem rowCheck12736 : row12736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12736 := by decide +kernel

theorem rowEval12736 (x : Key → ℝ) : Integer.Sparse.eval row12736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck12736, Integer.Sparse.eval_collectBalanced, rawRowCheck12736]

def rawRow12737 : Integer.Sparse Key := [(key542, -2), (key546, -2), (key679, -2), (key284, -2), (key287, -2), (key510, -2), (key546, -2), (key669, -2), (key679, -2), (key284, -2), (key510, -2), (key542, -2), (key370, 1), (key373, 1), (key542, 1), (key563, 1), (key679, 1), (key684, 1), (key293, 1), (key299, 1), (key521, 1), (key563, 1), (key673, 1), (key684, 1), (key284, 1), (key299, 1), (key353, 1), (key373, 1), (key673, 1), (key679, 1), (key284, 1), (key293, 1), (key353, 1), (key370, 1), (key521, 1), (key542, 1)]

theorem rawRowCheck12737 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form8 = rawRow12737 := by decide +kernel

def row12737 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

theorem rowCheck12737 : row12737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12737 := by decide +kernel

theorem rowEval12737 (x : Key → ℝ) : Integer.Sparse.eval row12737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12737, Integer.Sparse.eval_collectBalanced, rawRowCheck12737]

def rawRow12738 : Integer.Sparse Key := [(key546, -2), (key542, -2), (key679, -2), (key287, -2), (key284, -2), (key546, -2), (key510, -2), (key679, -2), (key669, -2), (key284, -2), (key542, -2), (key510, -2), (key373, 1), (key370, 1), (key563, 1), (key542, 1), (key684, 1), (key679, 1), (key299, 1), (key293, 1), (key563, 1), (key521, 1), (key684, 1), (key673, 1), (key299, 1), (key284, 1), (key373, 1), (key353, 1), (key679, 1), (key673, 1), (key293, 1), (key284, 1), (key370, 1), (key353, 1), (key542, 1), (key521, 1)]

theorem rawRowCheck12738 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form8 = rawRow12738 := by decide +kernel

def row12738 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

theorem rowCheck12738 : row12738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12738 := by decide +kernel

theorem rowEval12738 (x : Key → ℝ) : Integer.Sparse.eval row12738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12738, Integer.Sparse.eval_collectBalanced, rawRowCheck12738]

def rawRow12739 : Integer.Sparse Key := [(key542, -2), (key679, -2), (key546, -2), (key510, -2), (key669, -2), (key284, -2), (key679, -2), (key287, -2), (key546, -2), (key510, -2), (key284, -2), (key542, -2), (key542, 1), (key679, 1), (key370, 1), (key684, 1), (key373, 1), (key563, 1), (key521, 1), (key673, 1), (key293, 1), (key684, 1), (key299, 1), (key563, 1), (key353, 1), (key673, 1), (key284, 1), (key679, 1), (key299, 1), (key373, 1), (key353, 1), (key521, 1), (key284, 1), (key542, 1), (key293, 1), (key370, 1)]

theorem rawRowCheck12739 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form8 = rawRow12739 := by decide +kernel

def row12739 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

theorem rowCheck12739 : row12739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12739 := by decide +kernel

theorem rowEval12739 (x : Key → ℝ) : Integer.Sparse.eval row12739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12739, Integer.Sparse.eval_collectBalanced, rawRowCheck12739]

def rawRow12740 : Integer.Sparse Key := [(key679, -2), (key542, -2), (key546, -2), (key669, -2), (key510, -2), (key679, -2), (key284, -2), (key546, -2), (key287, -2), (key510, -2), (key542, -2), (key284, -2), (key679, 1), (key542, 1), (key684, 1), (key370, 1), (key563, 1), (key373, 1), (key673, 1), (key521, 1), (key684, 1), (key293, 1), (key563, 1), (key299, 1), (key673, 1), (key353, 1), (key679, 1), (key284, 1), (key373, 1), (key299, 1), (key521, 1), (key353, 1), (key542, 1), (key284, 1), (key370, 1), (key293, 1)]

theorem rawRowCheck12740 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form8 = rawRow12740 := by decide +kernel

def row12740 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

theorem rowCheck12740 : row12740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12740 := by decide +kernel

theorem rowEval12740 (x : Key → ℝ) : Integer.Sparse.eval row12740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck12740, Integer.Sparse.eval_collectBalanced, rawRowCheck12740]

def rawRow12741 : Integer.Sparse Key := [(key546, -2), (key679, -2), (key542, -2), (key546, -2), (key679, -2), (key287, -2), (key669, -2), (key284, -2), (key510, -2), (key542, -2), (key284, -2), (key510, -2), (key563, 1), (key684, 1), (key373, 1), (key679, 1), (key370, 1), (key542, 1), (key563, 1), (key684, 1), (key299, 1), (key673, 1), (key293, 1), (key521, 1), (key373, 1), (key679, 1), (key299, 1), (key673, 1), (key284, 1), (key353, 1), (key370, 1), (key542, 1), (key293, 1), (key521, 1), (key284, 1), (key353, 1)]

theorem rawRowCheck12741 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form8 = rawRow12741 := by decide +kernel

def row12741 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

theorem rowCheck12741 : row12741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12741 := by decide +kernel

theorem rowEval12741 (x : Key → ℝ) : Integer.Sparse.eval row12741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12741, Integer.Sparse.eval_collectBalanced, rawRowCheck12741]

def rawRow12742 : Integer.Sparse Key := [(key679, -2), (key546, -2), (key542, -2), (key679, -2), (key546, -2), (key669, -2), (key287, -2), (key510, -2), (key284, -2), (key542, -2), (key510, -2), (key284, -2), (key684, 1), (key563, 1), (key679, 1), (key373, 1), (key542, 1), (key370, 1), (key684, 1), (key563, 1), (key673, 1), (key299, 1), (key521, 1), (key293, 1), (key679, 1), (key373, 1), (key673, 1), (key299, 1), (key353, 1), (key284, 1), (key542, 1), (key370, 1), (key521, 1), (key293, 1), (key353, 1), (key284, 1)]

theorem rawRowCheck12742 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form8 = rawRow12742 := by decide +kernel

def row12742 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

theorem rowCheck12742 : row12742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12742 := by decide +kernel

theorem rowEval12742 (x : Key → ℝ) : Integer.Sparse.eval row12742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck12742, Integer.Sparse.eval_collectBalanced, rawRowCheck12742]

def rawRow12743 : Integer.Sparse Key := [(key293, -2), (key299, -2), (key299, -2), (key521, -2), (key526, -2), (key521, -2), (key563, -2), (key526, -2), (key563, -2), (key673, -2), (key673, -2), (key684, -2), (key284, 1), (key287, 1), (key284, 1), (key299, 1), (key287, 1), (key299, 1), (key353, 1), (key356, 1), (key353, 1), (key373, 1), (key356, 1), (key373, 1), (key510, 1), (key526, 1), (key510, 1), (key546, 1), (key526, 1), (key546, 1), (key669, 1), (key673, 1), (key669, 1), (key679, 1), (key673, 1), (key679, 1)]

theorem rawRowCheck12743 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form8 = rawRow12743 := by decide +kernel

def row12743 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

theorem rowCheck12743 : row12743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12743 := by decide +kernel

theorem rowEval12743 (x : Key → ℝ) : Integer.Sparse.eval row12743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12743, Integer.Sparse.eval_collectBalanced, rawRowCheck12743]

def rawRow12744 : Integer.Sparse Key := [(key299, -2), (key293, -2), (key299, -2), (key526, -2), (key521, -2), (key563, -2), (key521, -2), (key563, -2), (key526, -2), (key673, -2), (key684, -2), (key673, -2), (key287, 1), (key284, 1), (key299, 1), (key284, 1), (key299, 1), (key287, 1), (key356, 1), (key353, 1), (key373, 1), (key353, 1), (key373, 1), (key356, 1), (key526, 1), (key510, 1), (key546, 1), (key510, 1), (key546, 1), (key526, 1), (key673, 1), (key669, 1), (key679, 1), (key669, 1), (key679, 1), (key673, 1)]

theorem rawRowCheck12744 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form8 = rawRow12744 := by decide +kernel

def row12744 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

theorem rowCheck12744 : row12744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12744 := by decide +kernel

theorem rowEval12744 (x : Key → ℝ) : Integer.Sparse.eval row12744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12744, Integer.Sparse.eval_collectBalanced, rawRowCheck12744]

def rawRow12745 : Integer.Sparse Key := [(key299, -2), (key299, -2), (key293, -2), (key563, -2), (key563, -2), (key526, -2), (key526, -2), (key521, -2), (key521, -2), (key684, -2), (key673, -2), (key673, -2), (key299, 1), (key299, 1), (key287, 1), (key287, 1), (key284, 1), (key284, 1), (key373, 1), (key373, 1), (key356, 1), (key356, 1), (key353, 1), (key353, 1), (key546, 1), (key546, 1), (key526, 1), (key526, 1), (key510, 1), (key510, 1), (key679, 1), (key679, 1), (key673, 1), (key673, 1), (key669, 1), (key669, 1)]

theorem rawRowCheck12745 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form8 = rawRow12745 := by decide +kernel

def row12745 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

theorem rowCheck12745 : row12745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12745 := by decide +kernel

theorem rowEval12745 (x : Key → ℝ) : Integer.Sparse.eval row12745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12745, Integer.Sparse.eval_collectBalanced, rawRowCheck12745]

def rawRow12746 : Integer.Sparse Key := [(key521, -2), (key526, -2), (key673, -2), (key293, -2), (key299, -2), (key521, -2), (key563, -2), (key673, -2), (key684, -2), (key299, -2), (key526, -2), (key563, -2), (key353, 1), (key356, 1), (key510, 1), (key526, 1), (key669, 1), (key673, 1), (key284, 1), (key287, 1), (key510, 1), (key546, 1), (key669, 1), (key679, 1), (key284, 1), (key299, 1), (key353, 1), (key373, 1), (key673, 1), (key679, 1), (key287, 1), (key299, 1), (key356, 1), (key373, 1), (key526, 1), (key546, 1)]

theorem rawRowCheck12746 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form8 = rawRow12746 := by decide +kernel

def row12746 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

theorem rowCheck12746 : row12746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12746 := by decide +kernel

theorem rowEval12746 (x : Key → ℝ) : Integer.Sparse.eval row12746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12746, Integer.Sparse.eval_collectBalanced, rawRowCheck12746]

def rawRow12747 : Integer.Sparse Key := [(key526, -2), (key521, -2), (key673, -2), (key299, -2), (key293, -2), (key563, -2), (key521, -2), (key684, -2), (key673, -2), (key299, -2), (key563, -2), (key526, -2), (key356, 1), (key353, 1), (key526, 1), (key510, 1), (key673, 1), (key669, 1), (key287, 1), (key284, 1), (key546, 1), (key510, 1), (key679, 1), (key669, 1), (key299, 1), (key284, 1), (key373, 1), (key353, 1), (key679, 1), (key673, 1), (key299, 1), (key287, 1), (key373, 1), (key356, 1), (key546, 1), (key526, 1)]

theorem rawRowCheck12747 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form8 = rawRow12747 := by decide +kernel

def row12747 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

theorem rowCheck12747 : row12747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12747 := by decide +kernel

theorem rowEval12747 (x : Key → ℝ) : Integer.Sparse.eval row12747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12747, Integer.Sparse.eval_collectBalanced, rawRowCheck12747]

def rawRow12748 : Integer.Sparse Key := [(key521, -2), (key673, -2), (key526, -2), (key521, -2), (key673, -2), (key293, -2), (key684, -2), (key299, -2), (key563, -2), (key526, -2), (key299, -2), (key563, -2), (key510, 1), (key669, 1), (key353, 1), (key673, 1), (key356, 1), (key526, 1), (key510, 1), (key669, 1), (key284, 1), (key679, 1), (key287, 1), (key546, 1), (key353, 1), (key673, 1), (key284, 1), (key679, 1), (key299, 1), (key373, 1), (key356, 1), (key526, 1), (key287, 1), (key546, 1), (key299, 1), (key373, 1)]

theorem rawRowCheck12748 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form8 = rawRow12748 := by decide +kernel

def row12748 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

theorem rowCheck12748 : row12748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12748 := by decide +kernel

theorem rowEval12748 (x : Key → ℝ) : Integer.Sparse.eval row12748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12748, Integer.Sparse.eval_collectBalanced, rawRowCheck12748]

def rawRow12749 : Integer.Sparse Key := [(key673, -2), (key521, -2), (key526, -2), (key673, -2), (key521, -2), (key684, -2), (key293, -2), (key563, -2), (key299, -2), (key526, -2), (key563, -2), (key299, -2), (key669, 1), (key510, 1), (key673, 1), (key353, 1), (key526, 1), (key356, 1), (key669, 1), (key510, 1), (key679, 1), (key284, 1), (key546, 1), (key287, 1), (key673, 1), (key353, 1), (key679, 1), (key284, 1), (key373, 1), (key299, 1), (key526, 1), (key356, 1), (key546, 1), (key287, 1), (key373, 1), (key299, 1)]

theorem rawRowCheck12749 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form8 = rawRow12749 := by decide +kernel

def row12749 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

theorem rowCheck12749 : row12749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12749 := by decide +kernel

theorem rowEval12749 (x : Key → ℝ) : Integer.Sparse.eval row12749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck12749, Integer.Sparse.eval_collectBalanced, rawRowCheck12749]

def rawRow12750 : Integer.Sparse Key := [(key526, -2), (key673, -2), (key521, -2), (key563, -2), (key684, -2), (key299, -2), (key673, -2), (key293, -2), (key521, -2), (key563, -2), (key299, -2), (key526, -2), (key526, 1), (key673, 1), (key356, 1), (key669, 1), (key353, 1), (key510, 1), (key546, 1), (key679, 1), (key287, 1), (key669, 1), (key284, 1), (key510, 1), (key373, 1), (key679, 1), (key299, 1), (key673, 1), (key284, 1), (key353, 1), (key373, 1), (key546, 1), (key299, 1), (key526, 1), (key287, 1), (key356, 1)]

theorem rawRowCheck12750 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form8 = rawRow12750 := by decide +kernel

def row12750 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

theorem rowCheck12750 : row12750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12750 := by decide +kernel

theorem rowEval12750 (x : Key → ℝ) : Integer.Sparse.eval row12750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12750, Integer.Sparse.eval_collectBalanced, rawRowCheck12750]

def rawRow12751 : Integer.Sparse Key := [(key673, -2), (key526, -2), (key521, -2), (key684, -2), (key563, -2), (key673, -2), (key299, -2), (key521, -2), (key293, -2), (key563, -2), (key526, -2), (key299, -2), (key673, 1), (key526, 1), (key669, 1), (key356, 1), (key510, 1), (key353, 1), (key679, 1), (key546, 1), (key669, 1), (key287, 1), (key510, 1), (key284, 1), (key679, 1), (key373, 1), (key673, 1), (key299, 1), (key353, 1), (key284, 1), (key546, 1), (key373, 1), (key526, 1), (key299, 1), (key356, 1), (key287, 1)]

theorem rawRowCheck12751 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form8 = rawRow12751 := by decide +kernel

def row12751 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

theorem rowCheck12751 : row12751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12751 := by decide +kernel

theorem rowEval12751 (x : Key → ℝ) : Integer.Sparse.eval row12751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck12751, Integer.Sparse.eval_collectBalanced, rawRowCheck12751]

def rawRow12752 : Integer.Sparse Key := [(key563, -2), (key563, -2), (key684, -2), (key299, -2), (key299, -2), (key526, -2), (key526, -2), (key673, -2), (key673, -2), (key293, -2), (key521, -2), (key521, -2), (key373, 1), (key373, 1), (key546, 1), (key546, 1), (key679, 1), (key679, 1), (key299, 1), (key299, 1), (key526, 1), (key526, 1), (key673, 1), (key673, 1), (key287, 1), (key287, 1), (key356, 1), (key356, 1), (key669, 1), (key669, 1), (key284, 1), (key284, 1), (key353, 1), (key353, 1), (key510, 1), (key510, 1)]

theorem rawRowCheck12752 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form8 = rawRow12752 := by decide +kernel

def row12752 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

theorem rowCheck12752 : row12752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12752 := by decide +kernel

theorem rowEval12752 (x : Key → ℝ) : Integer.Sparse.eval row12752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12752, Integer.Sparse.eval_collectBalanced, rawRowCheck12752]

def rawRow12753 : Integer.Sparse Key := [(key563, -2), (key684, -2), (key563, -2), (key526, -2), (key673, -2), (key299, -2), (key673, -2), (key299, -2), (key526, -2), (key521, -2), (key293, -2), (key521, -2), (key546, 1), (key679, 1), (key373, 1), (key679, 1), (key373, 1), (key546, 1), (key526, 1), (key673, 1), (key299, 1), (key673, 1), (key299, 1), (key526, 1), (key356, 1), (key669, 1), (key287, 1), (key669, 1), (key287, 1), (key356, 1), (key353, 1), (key510, 1), (key284, 1), (key510, 1), (key284, 1), (key353, 1)]

theorem rawRowCheck12753 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form8 = rawRow12753 := by decide +kernel

def row12753 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

theorem rowCheck12753 : row12753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12753 := by decide +kernel

theorem rowEval12753 (x : Key → ℝ) : Integer.Sparse.eval row12753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12753, Integer.Sparse.eval_collectBalanced, rawRowCheck12753]

def rawRow12754 : Integer.Sparse Key := [(key684, -2), (key563, -2), (key563, -2), (key673, -2), (key526, -2), (key673, -2), (key299, -2), (key526, -2), (key299, -2), (key521, -2), (key521, -2), (key293, -2), (key679, 1), (key546, 1), (key679, 1), (key373, 1), (key546, 1), (key373, 1), (key673, 1), (key526, 1), (key673, 1), (key299, 1), (key526, 1), (key299, 1), (key669, 1), (key356, 1), (key669, 1), (key287, 1), (key356, 1), (key287, 1), (key510, 1), (key353, 1), (key510, 1), (key284, 1), (key353, 1), (key284, 1)]

theorem rawRowCheck12754 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form8 = rawRow12754 := by decide +kernel

def row12754 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

theorem rowCheck12754 : row12754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12754 := by decide +kernel

theorem rowEval12754 (x : Key → ℝ) : Integer.Sparse.eval row12754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck12754, Integer.Sparse.eval_collectBalanced, rawRowCheck12754]

def rawRow12755 : Integer.Sparse Key := [(key1365, 1), (key1365, 1), (key1375, 1), (key1375, 1), (key1380, 1), (key1380, 1), (key1491, 1), (key1491, 1), (key1514, 1), (key1514, 1), (key1520, 1), (key1520, 1), (key1724, 1), (key1724, 1), (key1742, 1), (key1742, 1), (key1759, 1), (key1759, 1), (key1942, 1), (key1942, 1), (key1951, 1), (key1951, 1), (key1956, 1), (key1956, 1), (key1371, -2), (key1380, -2), (key1380, -2), (key1497, -2), (key1520, -2), (key1520, -2), (key1729, -2), (key1729, -2), (key1748, -2), (key1748, -2), (key1759, -2), (key1759, -2)]

theorem rawRowCheck12755 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form9 = rawRow12755 := by decide +kernel

def row12755 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

theorem rowCheck12755 : row12755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12755 := by decide +kernel

theorem rowEval12755 (x : Key → ℝ) : Integer.Sparse.eval row12755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12755, Integer.Sparse.eval_collectBalanced, rawRowCheck12755]

def rawRow12756 : Integer.Sparse Key := [(key1375, 1), (key1380, 1), (key1365, 1), (key1380, 1), (key1365, 1), (key1375, 1), (key1514, 1), (key1520, 1), (key1491, 1), (key1520, 1), (key1491, 1), (key1514, 1), (key1742, 1), (key1759, 1), (key1724, 1), (key1759, 1), (key1724, 1), (key1742, 1), (key1951, 1), (key1956, 1), (key1942, 1), (key1956, 1), (key1942, 1), (key1951, 1), (key1380, -2), (key1371, -2), (key1380, -2), (key1520, -2), (key1497, -2), (key1520, -2), (key1748, -2), (key1759, -2), (key1729, -2), (key1759, -2), (key1729, -2), (key1748, -2)]

theorem rawRowCheck12756 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form9 = rawRow12756 := by decide +kernel

def row12756 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

theorem rowCheck12756 : row12756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12756 := by decide +kernel

theorem rowEval12756 (x : Key → ℝ) : Integer.Sparse.eval row12756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12756, Integer.Sparse.eval_collectBalanced, rawRowCheck12756]

def rawRow12757 : Integer.Sparse Key := [(key1380, 1), (key1375, 1), (key1380, 1), (key1365, 1), (key1375, 1), (key1365, 1), (key1520, 1), (key1514, 1), (key1520, 1), (key1491, 1), (key1514, 1), (key1491, 1), (key1759, 1), (key1742, 1), (key1759, 1), (key1724, 1), (key1742, 1), (key1724, 1), (key1956, 1), (key1951, 1), (key1956, 1), (key1942, 1), (key1951, 1), (key1942, 1), (key1380, -2), (key1380, -2), (key1371, -2), (key1520, -2), (key1520, -2), (key1497, -2), (key1759, -2), (key1748, -2), (key1759, -2), (key1729, -2), (key1748, -2), (key1729, -2)]

theorem rawRowCheck12757 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form9 = rawRow12757 := by decide +kernel

def row12757 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

theorem rowCheck12757 : row12757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12757 := by decide +kernel

theorem rowEval12757 (x : Key → ℝ) : Integer.Sparse.eval row12757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12757, Integer.Sparse.eval_collectBalanced, rawRowCheck12757]

def rawRow12758 : Integer.Sparse Key := [(key1491, 1), (key1491, 1), (key1724, 1), (key1724, 1), (key1942, 1), (key1942, 1), (key1365, 1), (key1365, 1), (key1742, 1), (key1742, 1), (key1951, 1), (key1951, 1), (key1375, 1), (key1375, 1), (key1514, 1), (key1514, 1), (key1956, 1), (key1956, 1), (key1380, 1), (key1380, 1), (key1520, 1), (key1520, 1), (key1759, 1), (key1759, 1), (key1497, -2), (key1729, -2), (key1729, -2), (key1371, -2), (key1748, -2), (key1748, -2), (key1380, -2), (key1380, -2), (key1520, -2), (key1520, -2), (key1759, -2), (key1759, -2)]

theorem rawRowCheck12758 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form9 = rawRow12758 := by decide +kernel

def row12758 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

theorem rowCheck12758 : row12758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12758 := by decide +kernel

theorem rowEval12758 (x : Key → ℝ) : Integer.Sparse.eval row12758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12758, Integer.Sparse.eval_collectBalanced, rawRowCheck12758]

def rawRow12759 : Integer.Sparse Key := [(key1724, 1), (key1942, 1), (key1491, 1), (key1942, 1), (key1491, 1), (key1724, 1), (key1742, 1), (key1951, 1), (key1365, 1), (key1951, 1), (key1365, 1), (key1742, 1), (key1514, 1), (key1956, 1), (key1375, 1), (key1956, 1), (key1375, 1), (key1514, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1759, 1), (key1380, 1), (key1520, 1), (key1729, -2), (key1497, -2), (key1729, -2), (key1748, -2), (key1371, -2), (key1748, -2), (key1520, -2), (key1759, -2), (key1380, -2), (key1759, -2), (key1380, -2), (key1520, -2)]

theorem rawRowCheck12759 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form9 = rawRow12759 := by decide +kernel

def row12759 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

theorem rowCheck12759 : row12759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12759 := by decide +kernel

theorem rowEval12759 (x : Key → ℝ) : Integer.Sparse.eval row12759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12759, Integer.Sparse.eval_collectBalanced, rawRowCheck12759]

def rawRow12760 : Integer.Sparse Key := [(key1942, 1), (key1724, 1), (key1942, 1), (key1491, 1), (key1724, 1), (key1491, 1), (key1951, 1), (key1742, 1), (key1951, 1), (key1365, 1), (key1742, 1), (key1365, 1), (key1956, 1), (key1514, 1), (key1956, 1), (key1375, 1), (key1514, 1), (key1375, 1), (key1759, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1520, 1), (key1380, 1), (key1729, -2), (key1729, -2), (key1497, -2), (key1748, -2), (key1748, -2), (key1371, -2), (key1759, -2), (key1520, -2), (key1759, -2), (key1380, -2), (key1520, -2), (key1380, -2)]

theorem rawRowCheck12760 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form9 = rawRow12760 := by decide +kernel

def row12760 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

theorem rowCheck12760 : row12760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12760 := by decide +kernel

theorem rowEval12760 (x : Key → ℝ) : Integer.Sparse.eval row12760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck12760, Integer.Sparse.eval_collectBalanced, rawRowCheck12760]

def rawRow12761 : Integer.Sparse Key := [(key1514, 1), (key1520, 1), (key1742, 1), (key1759, 1), (key1951, 1), (key1956, 1), (key1375, 1), (key1380, 1), (key1724, 1), (key1759, 1), (key1942, 1), (key1956, 1), (key1365, 1), (key1380, 1), (key1491, 1), (key1520, 1), (key1942, 1), (key1951, 1), (key1365, 1), (key1375, 1), (key1491, 1), (key1514, 1), (key1724, 1), (key1742, 1), (key1520, -2), (key1748, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1759, -2), (key1371, -2), (key1380, -2), (key1497, -2), (key1520, -2), (key1729, -2), (key1748, -2)]

theorem rawRowCheck12761 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form9 = rawRow12761 := by decide +kernel

def row12761 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

theorem rowCheck12761 : row12761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12761 := by decide +kernel

theorem rowEval12761 (x : Key → ℝ) : Integer.Sparse.eval row12761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12761, Integer.Sparse.eval_collectBalanced, rawRowCheck12761]

def rawRow12762 : Integer.Sparse Key := [(key1520, 1), (key1514, 1), (key1759, 1), (key1742, 1), (key1956, 1), (key1951, 1), (key1380, 1), (key1375, 1), (key1759, 1), (key1724, 1), (key1956, 1), (key1942, 1), (key1380, 1), (key1365, 1), (key1520, 1), (key1491, 1), (key1951, 1), (key1942, 1), (key1375, 1), (key1365, 1), (key1514, 1), (key1491, 1), (key1742, 1), (key1724, 1), (key1520, -2), (key1759, -2), (key1748, -2), (key1380, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1371, -2), (key1520, -2), (key1497, -2), (key1748, -2), (key1729, -2)]

theorem rawRowCheck12762 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form9 = rawRow12762 := by decide +kernel

def row12762 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

theorem rowCheck12762 : row12762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12762 := by decide +kernel

theorem rowEval12762 (x : Key → ℝ) : Integer.Sparse.eval row12762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12762, Integer.Sparse.eval_collectBalanced, rawRowCheck12762]

def rawRow12763 : Integer.Sparse Key := [(key1742, 1), (key1951, 1), (key1514, 1), (key1956, 1), (key1520, 1), (key1759, 1), (key1724, 1), (key1942, 1), (key1375, 1), (key1956, 1), (key1380, 1), (key1759, 1), (key1491, 1), (key1942, 1), (key1365, 1), (key1951, 1), (key1380, 1), (key1520, 1), (key1491, 1), (key1724, 1), (key1365, 1), (key1742, 1), (key1375, 1), (key1514, 1), (key1748, -2), (key1520, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1759, -2), (key1497, -2), (key1729, -2), (key1371, -2), (key1748, -2), (key1380, -2), (key1520, -2)]

theorem rawRowCheck12763 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form9 = rawRow12763 := by decide +kernel

def row12763 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

theorem rowCheck12763 : row12763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12763 := by decide +kernel

theorem rowEval12763 (x : Key → ℝ) : Integer.Sparse.eval row12763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12763, Integer.Sparse.eval_collectBalanced, rawRowCheck12763]

def rawRow12764 : Integer.Sparse Key := [(key1951, 1), (key1742, 1), (key1956, 1), (key1514, 1), (key1759, 1), (key1520, 1), (key1942, 1), (key1724, 1), (key1956, 1), (key1375, 1), (key1759, 1), (key1380, 1), (key1942, 1), (key1491, 1), (key1951, 1), (key1365, 1), (key1520, 1), (key1380, 1), (key1724, 1), (key1491, 1), (key1742, 1), (key1365, 1), (key1514, 1), (key1375, 1), (key1748, -2), (key1759, -2), (key1520, -2), (key1729, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1497, -2), (key1748, -2), (key1371, -2), (key1520, -2), (key1380, -2)]

theorem rawRowCheck12764 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form9 = rawRow12764 := by decide +kernel

def row12764 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

theorem rowCheck12764 : row12764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12764 := by decide +kernel

theorem rowEval12764 (x : Key → ℝ) : Integer.Sparse.eval row12764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck12764, Integer.Sparse.eval_collectBalanced, rawRowCheck12764]

def rawRow12765 : Integer.Sparse Key := [(key1759, 1), (key1956, 1), (key1520, 1), (key1951, 1), (key1514, 1), (key1742, 1), (key1759, 1), (key1956, 1), (key1380, 1), (key1942, 1), (key1375, 1), (key1724, 1), (key1520, 1), (key1951, 1), (key1380, 1), (key1942, 1), (key1365, 1), (key1491, 1), (key1514, 1), (key1742, 1), (key1375, 1), (key1724, 1), (key1365, 1), (key1491, 1), (key1759, -2), (key1520, -2), (key1748, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1520, -2), (key1748, -2), (key1380, -2), (key1729, -2), (key1371, -2), (key1497, -2)]

theorem rawRowCheck12765 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form9 = rawRow12765 := by decide +kernel

def row12765 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

theorem rowCheck12765 : row12765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12765 := by decide +kernel

theorem rowEval12765 (x : Key → ℝ) : Integer.Sparse.eval row12765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12765, Integer.Sparse.eval_collectBalanced, rawRowCheck12765]

def rawRow12766 : Integer.Sparse Key := [(key1956, 1), (key1759, 1), (key1951, 1), (key1520, 1), (key1742, 1), (key1514, 1), (key1956, 1), (key1759, 1), (key1942, 1), (key1380, 1), (key1724, 1), (key1375, 1), (key1951, 1), (key1520, 1), (key1942, 1), (key1380, 1), (key1491, 1), (key1365, 1), (key1742, 1), (key1514, 1), (key1724, 1), (key1375, 1), (key1491, 1), (key1365, 1), (key1759, -2), (key1748, -2), (key1520, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1748, -2), (key1520, -2), (key1729, -2), (key1380, -2), (key1497, -2), (key1371, -2)]

theorem rawRowCheck12766 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form9 = rawRow12766 := by decide +kernel

def row12766 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

theorem rowCheck12766 : row12766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12766 := by decide +kernel

theorem rowEval12766 (x : Key → ℝ) : Integer.Sparse.eval row12766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck12766, Integer.Sparse.eval_collectBalanced, rawRowCheck12766]

def rawRow12767 : Integer.Sparse Key := [(key1365, 1), (key1371, 1), (key1365, 1), (key1380, 1), (key1371, 1), (key1380, 1), (key1491, 1), (key1497, 1), (key1491, 1), (key1520, 1), (key1497, 1), (key1520, 1), (key1717, 1), (key1729, 1), (key1717, 1), (key1748, 1), (key1729, 1), (key1748, 1), (key1939, 1), (key1942, 1), (key1939, 1), (key1951, 1), (key1942, 1), (key1951, 1), (key1365, -2), (key1365, -2), (key1375, -2), (key1491, -2), (key1491, -2), (key1514, -2), (key1717, -2), (key1724, -2), (key1717, -2), (key1742, -2), (key1724, -2), (key1742, -2)]

theorem rawRowCheck12767 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form9 = rawRow12767 := by decide +kernel

def row12767 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

theorem rowCheck12767 : row12767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12767 := by decide +kernel

theorem rowEval12767 (x : Key → ℝ) : Integer.Sparse.eval row12767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12767, Integer.Sparse.eval_collectBalanced, rawRowCheck12767]

def rawRow12768 : Integer.Sparse Key := [(key1371, 1), (key1365, 1), (key1380, 1), (key1365, 1), (key1380, 1), (key1371, 1), (key1497, 1), (key1491, 1), (key1520, 1), (key1491, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1717, 1), (key1748, 1), (key1717, 1), (key1748, 1), (key1729, 1), (key1942, 1), (key1939, 1), (key1951, 1), (key1939, 1), (key1951, 1), (key1942, 1), (key1365, -2), (key1375, -2), (key1365, -2), (key1491, -2), (key1514, -2), (key1491, -2), (key1724, -2), (key1717, -2), (key1742, -2), (key1717, -2), (key1742, -2), (key1724, -2)]

theorem rawRowCheck12768 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form9 = rawRow12768 := by decide +kernel

def row12768 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

theorem rowCheck12768 : row12768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12768 := by decide +kernel

theorem rowEval12768 (x : Key → ℝ) : Integer.Sparse.eval row12768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12768, Integer.Sparse.eval_collectBalanced, rawRowCheck12768]

def rawRow12769 : Integer.Sparse Key := [(key1380, 1), (key1380, 1), (key1371, 1), (key1371, 1), (key1365, 1), (key1365, 1), (key1520, 1), (key1520, 1), (key1497, 1), (key1497, 1), (key1491, 1), (key1491, 1), (key1748, 1), (key1748, 1), (key1729, 1), (key1729, 1), (key1717, 1), (key1717, 1), (key1951, 1), (key1951, 1), (key1942, 1), (key1942, 1), (key1939, 1), (key1939, 1), (key1375, -2), (key1365, -2), (key1365, -2), (key1514, -2), (key1491, -2), (key1491, -2), (key1742, -2), (key1742, -2), (key1724, -2), (key1724, -2), (key1717, -2), (key1717, -2)]

theorem rawRowCheck12769 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form9 = rawRow12769 := by decide +kernel

def row12769 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

theorem rowCheck12769 : row12769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12769 := by decide +kernel

theorem rowEval12769 (x : Key → ℝ) : Integer.Sparse.eval row12769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12769, Integer.Sparse.eval_collectBalanced, rawRowCheck12769]

def rawRow12770 : Integer.Sparse Key := [(key1491, 1), (key1497, 1), (key1717, 1), (key1729, 1), (key1939, 1), (key1942, 1), (key1365, 1), (key1371, 1), (key1717, 1), (key1748, 1), (key1939, 1), (key1951, 1), (key1365, 1), (key1380, 1), (key1491, 1), (key1520, 1), (key1942, 1), (key1951, 1), (key1371, 1), (key1380, 1), (key1497, 1), (key1520, 1), (key1729, 1), (key1748, 1), (key1491, -2), (key1717, -2), (key1724, -2), (key1365, -2), (key1717, -2), (key1742, -2), (key1365, -2), (key1375, -2), (key1491, -2), (key1514, -2), (key1724, -2), (key1742, -2)]

theorem rawRowCheck12770 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form9 = rawRow12770 := by decide +kernel

def row12770 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

theorem rowCheck12770 : row12770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12770 := by decide +kernel

theorem rowEval12770 (x : Key → ℝ) : Integer.Sparse.eval row12770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12770, Integer.Sparse.eval_collectBalanced, rawRowCheck12770]

def rawRow12771 : Integer.Sparse Key := [(key1497, 1), (key1491, 1), (key1729, 1), (key1717, 1), (key1942, 1), (key1939, 1), (key1371, 1), (key1365, 1), (key1748, 1), (key1717, 1), (key1951, 1), (key1939, 1), (key1380, 1), (key1365, 1), (key1520, 1), (key1491, 1), (key1951, 1), (key1942, 1), (key1380, 1), (key1371, 1), (key1520, 1), (key1497, 1), (key1748, 1), (key1729, 1), (key1491, -2), (key1724, -2), (key1717, -2), (key1365, -2), (key1742, -2), (key1717, -2), (key1375, -2), (key1365, -2), (key1514, -2), (key1491, -2), (key1742, -2), (key1724, -2)]

theorem rawRowCheck12771 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form9 = rawRow12771 := by decide +kernel

def row12771 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

theorem rowCheck12771 : row12771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12771 := by decide +kernel

theorem rowEval12771 (x : Key → ℝ) : Integer.Sparse.eval row12771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12771, Integer.Sparse.eval_collectBalanced, rawRowCheck12771]

def rawRow12772 : Integer.Sparse Key := [(key1717, 1), (key1939, 1), (key1491, 1), (key1942, 1), (key1497, 1), (key1729, 1), (key1717, 1), (key1939, 1), (key1365, 1), (key1951, 1), (key1371, 1), (key1748, 1), (key1491, 1), (key1942, 1), (key1365, 1), (key1951, 1), (key1380, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1371, 1), (key1748, 1), (key1380, 1), (key1520, 1), (key1717, -2), (key1491, -2), (key1724, -2), (key1717, -2), (key1365, -2), (key1742, -2), (key1491, -2), (key1724, -2), (key1365, -2), (key1742, -2), (key1375, -2), (key1514, -2)]

theorem rawRowCheck12772 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form9 = rawRow12772 := by decide +kernel

def row12772 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

theorem rowCheck12772 : row12772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12772 := by decide +kernel

theorem rowEval12772 (x : Key → ℝ) : Integer.Sparse.eval row12772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12772, Integer.Sparse.eval_collectBalanced, rawRowCheck12772]

def rawRow12773 : Integer.Sparse Key := [(key1939, 1), (key1717, 1), (key1942, 1), (key1491, 1), (key1729, 1), (key1497, 1), (key1939, 1), (key1717, 1), (key1951, 1), (key1365, 1), (key1748, 1), (key1371, 1), (key1942, 1), (key1491, 1), (key1951, 1), (key1365, 1), (key1520, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1748, 1), (key1371, 1), (key1520, 1), (key1380, 1), (key1717, -2), (key1724, -2), (key1491, -2), (key1717, -2), (key1742, -2), (key1365, -2), (key1724, -2), (key1491, -2), (key1742, -2), (key1365, -2), (key1514, -2), (key1375, -2)]

theorem rawRowCheck12773 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form9 = rawRow12773 := by decide +kernel

def row12773 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

theorem rowCheck12773 : row12773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12773 := by decide +kernel

theorem rowEval12773 (x : Key → ℝ) : Integer.Sparse.eval row12773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck12773, Integer.Sparse.eval_collectBalanced, rawRowCheck12773]

def rawRow12774 : Integer.Sparse Key := [(key1729, 1), (key1942, 1), (key1497, 1), (key1939, 1), (key1491, 1), (key1717, 1), (key1748, 1), (key1951, 1), (key1371, 1), (key1939, 1), (key1365, 1), (key1717, 1), (key1520, 1), (key1951, 1), (key1380, 1), (key1942, 1), (key1365, 1), (key1491, 1), (key1520, 1), (key1748, 1), (key1380, 1), (key1729, 1), (key1371, 1), (key1497, 1), (key1724, -2), (key1491, -2), (key1717, -2), (key1742, -2), (key1365, -2), (key1717, -2), (key1514, -2), (key1742, -2), (key1375, -2), (key1724, -2), (key1365, -2), (key1491, -2)]

theorem rawRowCheck12774 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form9 = rawRow12774 := by decide +kernel

def row12774 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

theorem rowCheck12774 : row12774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12774 := by decide +kernel

theorem rowEval12774 (x : Key → ℝ) : Integer.Sparse.eval row12774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12774, Integer.Sparse.eval_collectBalanced, rawRowCheck12774]

def rawRow12775 : Integer.Sparse Key := [(key1942, 1), (key1729, 1), (key1939, 1), (key1497, 1), (key1717, 1), (key1491, 1), (key1951, 1), (key1748, 1), (key1939, 1), (key1371, 1), (key1717, 1), (key1365, 1), (key1951, 1), (key1520, 1), (key1942, 1), (key1380, 1), (key1491, 1), (key1365, 1), (key1748, 1), (key1520, 1), (key1729, 1), (key1380, 1), (key1497, 1), (key1371, 1), (key1724, -2), (key1717, -2), (key1491, -2), (key1742, -2), (key1717, -2), (key1365, -2), (key1742, -2), (key1514, -2), (key1724, -2), (key1375, -2), (key1491, -2), (key1365, -2)]

theorem rawRowCheck12775 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form9 = rawRow12775 := by decide +kernel

def row12775 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

theorem rowCheck12775 : row12775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12775 := by decide +kernel

theorem rowEval12775 (x : Key → ℝ) : Integer.Sparse.eval row12775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck12775, Integer.Sparse.eval_collectBalanced, rawRowCheck12775]

def rawRow12776 : Integer.Sparse Key := [(key1520, 1), (key1520, 1), (key1748, 1), (key1748, 1), (key1951, 1), (key1951, 1), (key1380, 1), (key1380, 1), (key1729, 1), (key1729, 1), (key1942, 1), (key1942, 1), (key1371, 1), (key1371, 1), (key1497, 1), (key1497, 1), (key1939, 1), (key1939, 1), (key1365, 1), (key1365, 1), (key1491, 1), (key1491, 1), (key1717, 1), (key1717, 1), (key1514, -2), (key1742, -2), (key1742, -2), (key1375, -2), (key1724, -2), (key1724, -2), (key1365, -2), (key1365, -2), (key1491, -2), (key1491, -2), (key1717, -2), (key1717, -2)]

theorem rawRowCheck12776 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form9 = rawRow12776 := by decide +kernel

def row12776 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

theorem rowCheck12776 : row12776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12776 := by decide +kernel

theorem rowEval12776 (x : Key → ℝ) : Integer.Sparse.eval row12776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12776, Integer.Sparse.eval_collectBalanced, rawRowCheck12776]

def rawRow12777 : Integer.Sparse Key := [(key1748, 1), (key1951, 1), (key1520, 1), (key1951, 1), (key1520, 1), (key1748, 1), (key1729, 1), (key1942, 1), (key1380, 1), (key1942, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1939, 1), (key1371, 1), (key1939, 1), (key1371, 1), (key1497, 1), (key1491, 1), (key1717, 1), (key1365, 1), (key1717, 1), (key1365, 1), (key1491, 1), (key1742, -2), (key1514, -2), (key1742, -2), (key1724, -2), (key1375, -2), (key1724, -2), (key1491, -2), (key1717, -2), (key1365, -2), (key1717, -2), (key1365, -2), (key1491, -2)]

theorem rawRowCheck12777 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form9 = rawRow12777 := by decide +kernel

def row12777 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

theorem rowCheck12777 : row12777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12777 := by decide +kernel

theorem rowEval12777 (x : Key → ℝ) : Integer.Sparse.eval row12777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12777, Integer.Sparse.eval_collectBalanced, rawRowCheck12777]

def rawRow12778 : Integer.Sparse Key := [(key1951, 1), (key1748, 1), (key1951, 1), (key1520, 1), (key1748, 1), (key1520, 1), (key1942, 1), (key1729, 1), (key1942, 1), (key1380, 1), (key1729, 1), (key1380, 1), (key1939, 1), (key1497, 1), (key1939, 1), (key1371, 1), (key1497, 1), (key1371, 1), (key1717, 1), (key1491, 1), (key1717, 1), (key1365, 1), (key1491, 1), (key1365, 1), (key1742, -2), (key1742, -2), (key1514, -2), (key1724, -2), (key1724, -2), (key1375, -2), (key1717, -2), (key1491, -2), (key1717, -2), (key1365, -2), (key1491, -2), (key1365, -2)]

theorem rawRowCheck12778 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form9 = rawRow12778 := by decide +kernel

def row12778 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

theorem rowCheck12778 : row12778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12778 := by decide +kernel

theorem rowEval12778 (x : Key → ℝ) : Integer.Sparse.eval row12778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck12778, Integer.Sparse.eval_collectBalanced, rawRowCheck12778]

def rawRow12779 : Integer.Sparse Key := [(key286, -6), (key512, -6), (key545, -6), (key545, -6), (key286, 2), (key297, 2), (key297, 2), (key355, 2), (key372, 2), (key372, 2), (key525, 2), (key525, 2), (key545, 2), (key545, 2), (key558, 2), (key558, 2)]

theorem rawRowCheck12779 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form10 = rawRow12779 := by decide +kernel

def row12779 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

theorem rowCheck12779 : row12779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12779 := by decide +kernel

theorem rowEval12779 (x : Key → ℝ) : Integer.Sparse.eval row12779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12779, Integer.Sparse.eval_collectBalanced, rawRowCheck12779]

def rawRow12780 : Integer.Sparse Key := [(key286, -6), (key545, -6), (key512, -6), (key545, -6), (key297, 2), (key286, 2), (key297, 2), (key372, 2), (key355, 2), (key372, 2), (key545, 2), (key558, 2), (key525, 2), (key558, 2), (key525, 2), (key545, 2)]

theorem rawRowCheck12780 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form10 = rawRow12780 := by decide +kernel

def row12780 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

theorem rowCheck12780 : row12780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12780 := by decide +kernel

theorem rowEval12780 (x : Key → ℝ) : Integer.Sparse.eval row12780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12780, Integer.Sparse.eval_collectBalanced, rawRowCheck12780]

def rawRow12781 : Integer.Sparse Key := [(key286, -6), (key545, -6), (key545, -6), (key512, -6), (key297, 2), (key297, 2), (key286, 2), (key372, 2), (key372, 2), (key355, 2), (key558, 2), (key545, 2), (key558, 2), (key525, 2), (key545, 2), (key525, 2)]

theorem rawRowCheck12781 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form10 = rawRow12781 := by decide +kernel

def row12781 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

theorem rowCheck12781 : row12781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12781 := by decide +kernel

theorem rowEval12781 (x : Key → ℝ) : Integer.Sparse.eval row12781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12781, Integer.Sparse.eval_collectBalanced, rawRowCheck12781]

def rawRow12782 : Integer.Sparse Key := [(key512, -6), (key286, -6), (key545, -6), (key545, -6), (key355, 2), (key525, 2), (key525, 2), (key286, 2), (key545, 2), (key545, 2), (key297, 2), (key297, 2), (key372, 2), (key372, 2), (key558, 2), (key558, 2)]

theorem rawRowCheck12782 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form10 = rawRow12782 := by decide +kernel

def row12782 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

theorem rowCheck12782 : row12782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12782 := by decide +kernel

theorem rowEval12782 (x : Key → ℝ) : Integer.Sparse.eval row12782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12782, Integer.Sparse.eval_collectBalanced, rawRowCheck12782]

def rawRow12783 : Integer.Sparse Key := [(key512, -6), (key545, -6), (key286, -6), (key545, -6), (key525, 2), (key355, 2), (key525, 2), (key545, 2), (key286, 2), (key545, 2), (key372, 2), (key558, 2), (key297, 2), (key558, 2), (key297, 2), (key372, 2)]

theorem rawRowCheck12783 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form10 = rawRow12783 := by decide +kernel

def row12783 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

theorem rowCheck12783 : row12783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12783 := by decide +kernel

theorem rowEval12783 (x : Key → ℝ) : Integer.Sparse.eval row12783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12783, Integer.Sparse.eval_collectBalanced, rawRowCheck12783]

def rawRow12784 : Integer.Sparse Key := [(key512, -6), (key545, -6), (key545, -6), (key286, -6), (key525, 2), (key525, 2), (key355, 2), (key545, 2), (key545, 2), (key286, 2), (key558, 2), (key372, 2), (key558, 2), (key297, 2), (key372, 2), (key297, 2)]

theorem rawRowCheck12784 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form10 = rawRow12784 := by decide +kernel

def row12784 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

theorem rowCheck12784 : row12784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12784 := by decide +kernel

theorem rowEval12784 (x : Key → ℝ) : Integer.Sparse.eval row12784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck12784, Integer.Sparse.eval_collectBalanced, rawRowCheck12784]

def rawRow12785 : Integer.Sparse Key := [(key545, -6), (key286, -6), (key512, -6), (key545, -6), (key372, 2), (key545, 2), (key558, 2), (key297, 2), (key525, 2), (key558, 2), (key286, 2), (key297, 2), (key355, 2), (key372, 2), (key525, 2), (key545, 2)]

theorem rawRowCheck12785 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form10 = rawRow12785 := by decide +kernel

def row12785 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

theorem rowCheck12785 : row12785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12785 := by decide +kernel

theorem rowEval12785 (x : Key → ℝ) : Integer.Sparse.eval row12785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12785, Integer.Sparse.eval_collectBalanced, rawRowCheck12785]

def rawRow12786 : Integer.Sparse Key := [(key545, -6), (key286, -6), (key545, -6), (key512, -6), (key372, 2), (key558, 2), (key545, 2), (key297, 2), (key558, 2), (key525, 2), (key297, 2), (key286, 2), (key372, 2), (key355, 2), (key545, 2), (key525, 2)]

theorem rawRowCheck12786 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form10 = rawRow12786 := by decide +kernel

def row12786 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

theorem rowCheck12786 : row12786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12786 := by decide +kernel

theorem rowEval12786 (x : Key → ℝ) : Integer.Sparse.eval row12786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12786, Integer.Sparse.eval_collectBalanced, rawRowCheck12786]

def rawRow12787 : Integer.Sparse Key := [(key545, -6), (key512, -6), (key286, -6), (key545, -6), (key545, 2), (key372, 2), (key558, 2), (key525, 2), (key297, 2), (key558, 2), (key355, 2), (key525, 2), (key286, 2), (key545, 2), (key297, 2), (key372, 2)]

theorem rawRowCheck12787 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form10 = rawRow12787 := by decide +kernel

def row12787 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

theorem rowCheck12787 : row12787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12787 := by decide +kernel

theorem rowEval12787 (x : Key → ℝ) : Integer.Sparse.eval row12787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12787, Integer.Sparse.eval_collectBalanced, rawRowCheck12787]

def rawRow12788 : Integer.Sparse Key := [(key545, -6), (key512, -6), (key545, -6), (key286, -6), (key545, 2), (key558, 2), (key372, 2), (key525, 2), (key558, 2), (key297, 2), (key525, 2), (key355, 2), (key545, 2), (key286, 2), (key372, 2), (key297, 2)]

theorem rawRowCheck12788 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form10 = rawRow12788 := by decide +kernel

def row12788 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

theorem rowCheck12788 : row12788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12788 := by decide +kernel

theorem rowEval12788 (x : Key → ℝ) : Integer.Sparse.eval row12788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck12788, Integer.Sparse.eval_collectBalanced, rawRowCheck12788]

def rawRow12789 : Integer.Sparse Key := [(key545, -6), (key545, -6), (key286, -6), (key512, -6), (key558, 2), (key372, 2), (key545, 2), (key558, 2), (key297, 2), (key525, 2), (key372, 2), (key545, 2), (key297, 2), (key525, 2), (key286, 2), (key355, 2)]

theorem rawRowCheck12789 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form10 = rawRow12789 := by decide +kernel

def row12789 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

theorem rowCheck12789 : row12789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12789 := by decide +kernel

theorem rowEval12789 (x : Key → ℝ) : Integer.Sparse.eval row12789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12789, Integer.Sparse.eval_collectBalanced, rawRowCheck12789]

def rawRow12790 : Integer.Sparse Key := [(key545, -6), (key545, -6), (key512, -6), (key286, -6), (key558, 2), (key545, 2), (key372, 2), (key558, 2), (key525, 2), (key297, 2), (key545, 2), (key372, 2), (key525, 2), (key297, 2), (key355, 2), (key286, 2)]

theorem rawRowCheck12790 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form10 = rawRow12790 := by decide +kernel

def row12790 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

theorem rowCheck12790 : row12790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12790 := by decide +kernel

theorem rowEval12790 (x : Key → ℝ) : Integer.Sparse.eval row12790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck12790, Integer.Sparse.eval_collectBalanced, rawRowCheck12790]

def rawRow12791 : Integer.Sparse Key := [(key297, -6), (key525, -6), (key525, -6), (key558, -6), (key286, 2), (key286, 2), (key297, 2), (key355, 2), (key355, 2), (key372, 2), (key512, 2), (key525, 2), (key512, 2), (key545, 2), (key525, 2), (key545, 2)]

theorem rawRowCheck12791 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form10 = rawRow12791 := by decide +kernel

def row12791 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

theorem rowCheck12791 : row12791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12791 := by decide +kernel

theorem rowEval12791 (x : Key → ℝ) : Integer.Sparse.eval row12791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12791, Integer.Sparse.eval_collectBalanced, rawRowCheck12791]

def rawRow12792 : Integer.Sparse Key := [(key297, -6), (key525, -6), (key558, -6), (key525, -6), (key286, 2), (key297, 2), (key286, 2), (key355, 2), (key372, 2), (key355, 2), (key525, 2), (key512, 2), (key545, 2), (key512, 2), (key545, 2), (key525, 2)]

theorem rawRowCheck12792 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form10 = rawRow12792 := by decide +kernel

def row12792 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

theorem rowCheck12792 : row12792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12792 := by decide +kernel

theorem rowEval12792 (x : Key → ℝ) : Integer.Sparse.eval row12792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12792, Integer.Sparse.eval_collectBalanced, rawRowCheck12792]

def rawRow12793 : Integer.Sparse Key := [(key297, -6), (key558, -6), (key525, -6), (key525, -6), (key297, 2), (key286, 2), (key286, 2), (key372, 2), (key355, 2), (key355, 2), (key545, 2), (key545, 2), (key525, 2), (key525, 2), (key512, 2), (key512, 2)]

theorem rawRowCheck12793 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form10 = rawRow12793 := by decide +kernel

def row12793 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

theorem rowCheck12793 : row12793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12793 := by decide +kernel

theorem rowEval12793 (x : Key → ℝ) : Integer.Sparse.eval row12793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12793, Integer.Sparse.eval_collectBalanced, rawRowCheck12793]

def rawRow12794 : Integer.Sparse Key := [(key525, -6), (key297, -6), (key525, -6), (key558, -6), (key355, 2), (key512, 2), (key525, 2), (key286, 2), (key512, 2), (key545, 2), (key286, 2), (key297, 2), (key355, 2), (key372, 2), (key525, 2), (key545, 2)]

theorem rawRowCheck12794 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form10 = rawRow12794 := by decide +kernel

def row12794 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

theorem rowCheck12794 : row12794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12794 := by decide +kernel

theorem rowEval12794 (x : Key → ℝ) : Integer.Sparse.eval row12794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12794, Integer.Sparse.eval_collectBalanced, rawRowCheck12794]

def rawRow12795 : Integer.Sparse Key := [(key525, -6), (key297, -6), (key558, -6), (key525, -6), (key355, 2), (key525, 2), (key512, 2), (key286, 2), (key545, 2), (key512, 2), (key297, 2), (key286, 2), (key372, 2), (key355, 2), (key545, 2), (key525, 2)]

theorem rawRowCheck12795 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form10 = rawRow12795 := by decide +kernel

def row12795 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

theorem rowCheck12795 : row12795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12795 := by decide +kernel

theorem rowEval12795 (x : Key → ℝ) : Integer.Sparse.eval row12795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12795, Integer.Sparse.eval_collectBalanced, rawRowCheck12795]

def rawRow12796 : Integer.Sparse Key := [(key525, -6), (key525, -6), (key297, -6), (key558, -6), (key512, 2), (key355, 2), (key525, 2), (key512, 2), (key286, 2), (key545, 2), (key355, 2), (key525, 2), (key286, 2), (key545, 2), (key297, 2), (key372, 2)]

theorem rawRowCheck12796 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form10 = rawRow12796 := by decide +kernel

def row12796 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

theorem rowCheck12796 : row12796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12796 := by decide +kernel

theorem rowEval12796 (x : Key → ℝ) : Integer.Sparse.eval row12796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12796, Integer.Sparse.eval_collectBalanced, rawRowCheck12796]

def rawRow12797 : Integer.Sparse Key := [(key525, -6), (key525, -6), (key558, -6), (key297, -6), (key512, 2), (key525, 2), (key355, 2), (key512, 2), (key545, 2), (key286, 2), (key525, 2), (key355, 2), (key545, 2), (key286, 2), (key372, 2), (key297, 2)]

theorem rawRowCheck12797 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form10 = rawRow12797 := by decide +kernel

def row12797 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

theorem rowCheck12797 : row12797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12797 := by decide +kernel

theorem rowEval12797 (x : Key → ℝ) : Integer.Sparse.eval row12797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck12797, Integer.Sparse.eval_collectBalanced, rawRowCheck12797]

def rawRow12798 : Integer.Sparse Key := [(key525, -6), (key558, -6), (key297, -6), (key525, -6), (key525, 2), (key355, 2), (key512, 2), (key545, 2), (key286, 2), (key512, 2), (key372, 2), (key545, 2), (key297, 2), (key525, 2), (key286, 2), (key355, 2)]

theorem rawRowCheck12798 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form10 = rawRow12798 := by decide +kernel

def row12798 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

theorem rowCheck12798 : row12798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12798 := by decide +kernel

theorem rowEval12798 (x : Key → ℝ) : Integer.Sparse.eval row12798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12798, Integer.Sparse.eval_collectBalanced, rawRowCheck12798]

def rawRow12799 : Integer.Sparse Key := [(key525, -6), (key558, -6), (key525, -6), (key297, -6), (key525, 2), (key512, 2), (key355, 2), (key545, 2), (key512, 2), (key286, 2), (key545, 2), (key372, 2), (key525, 2), (key297, 2), (key355, 2), (key286, 2)]

theorem rawRowCheck12799 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form10 = rawRow12799 := by decide +kernel

def row12799 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

theorem rowCheck12799 : row12799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12799 := by decide +kernel

theorem rowEval12799 (x : Key → ℝ) : Integer.Sparse.eval row12799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck12799, Integer.Sparse.eval_collectBalanced, rawRowCheck12799]

end MUB6.Certificate.GramRows

end OAI
