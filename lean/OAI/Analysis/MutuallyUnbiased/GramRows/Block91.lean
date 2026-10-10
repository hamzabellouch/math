import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
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

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8576 : Integer.Sparse Key := [(key1680, -2), (key1615, -2), (key1917, -2), (key1350, -2), (key1309, -2), (key1680, -2), (key1539, -2), (key1917, -2), (key1895, -2), (key1309, -2), (key1615, -2), (key1539, -2), (key1471, 1), (key1417, 1), (key1680, 1), (key1566, 1), (key1917, 1), (key1902, 1), (key1350, 1), (key1309, 1), (key1680, 1), (key1539, 1), (key1917, 1), (key1895, 1), (key1350, 1), (key1289, 1), (key1471, 1), (key1384, 1), (key1902, 1), (key1895, 1), (key1309, 1), (key1289, 1), (key1417, 1), (key1384, 1), (key1566, 1), (key1539, 1)]

theorem rawRowCheck8576 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form5 = rawRow8576 := by decide +kernel

def row8576 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

theorem rowCheck8576 : row8576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8576 := by decide +kernel

theorem rowEval8576 (x : Key → ℝ) : Integer.Sparse.eval row8576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8576, Integer.Sparse.eval_collectBalanced, rawRowCheck8576]

def rawRow8577 : Integer.Sparse Key := [(key1615, -2), (key1917, -2), (key1680, -2), (key1539, -2), (key1895, -2), (key1309, -2), (key1917, -2), (key1350, -2), (key1680, -2), (key1539, -2), (key1309, -2), (key1615, -2), (key1566, 1), (key1902, 1), (key1417, 1), (key1917, 1), (key1471, 1), (key1680, 1), (key1539, 1), (key1895, 1), (key1309, 1), (key1917, 1), (key1350, 1), (key1680, 1), (key1384, 1), (key1895, 1), (key1289, 1), (key1902, 1), (key1350, 1), (key1471, 1), (key1384, 1), (key1539, 1), (key1289, 1), (key1566, 1), (key1309, 1), (key1417, 1)]

theorem rawRowCheck8577 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form5 = rawRow8577 := by decide +kernel

def row8577 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

theorem rowCheck8577 : row8577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8577 := by decide +kernel

theorem rowEval8577 (x : Key → ℝ) : Integer.Sparse.eval row8577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8577, Integer.Sparse.eval_collectBalanced, rawRowCheck8577]

def rawRow8578 : Integer.Sparse Key := [(key1917, -2), (key1615, -2), (key1680, -2), (key1895, -2), (key1539, -2), (key1917, -2), (key1309, -2), (key1680, -2), (key1350, -2), (key1539, -2), (key1615, -2), (key1309, -2), (key1902, 1), (key1566, 1), (key1917, 1), (key1417, 1), (key1680, 1), (key1471, 1), (key1895, 1), (key1539, 1), (key1917, 1), (key1309, 1), (key1680, 1), (key1350, 1), (key1895, 1), (key1384, 1), (key1902, 1), (key1289, 1), (key1471, 1), (key1350, 1), (key1539, 1), (key1384, 1), (key1566, 1), (key1289, 1), (key1417, 1), (key1309, 1)]

theorem rawRowCheck8578 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form5 = rawRow8578 := by decide +kernel

def row8578 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

theorem rowCheck8578 : row8578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8578 := by decide +kernel

theorem rowEval8578 (x : Key → ℝ) : Integer.Sparse.eval row8578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8578, Integer.Sparse.eval_collectBalanced, rawRowCheck8578]

def rawRow8579 : Integer.Sparse Key := [(key1680, -2), (key1917, -2), (key1615, -2), (key1680, -2), (key1917, -2), (key1350, -2), (key1895, -2), (key1309, -2), (key1539, -2), (key1615, -2), (key1309, -2), (key1539, -2), (key1680, 1), (key1917, 1), (key1471, 1), (key1902, 1), (key1417, 1), (key1566, 1), (key1680, 1), (key1917, 1), (key1350, 1), (key1895, 1), (key1309, 1), (key1539, 1), (key1471, 1), (key1902, 1), (key1350, 1), (key1895, 1), (key1289, 1), (key1384, 1), (key1417, 1), (key1566, 1), (key1309, 1), (key1539, 1), (key1289, 1), (key1384, 1)]

theorem rawRowCheck8579 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form5 = rawRow8579 := by decide +kernel

def row8579 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

theorem rowCheck8579 : row8579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8579 := by decide +kernel

theorem rowEval8579 (x : Key → ℝ) : Integer.Sparse.eval row8579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8579, Integer.Sparse.eval_collectBalanced, rawRowCheck8579]

def rawRow8580 : Integer.Sparse Key := [(key1917, -2), (key1680, -2), (key1615, -2), (key1917, -2), (key1680, -2), (key1895, -2), (key1350, -2), (key1539, -2), (key1309, -2), (key1615, -2), (key1539, -2), (key1309, -2), (key1917, 1), (key1680, 1), (key1902, 1), (key1471, 1), (key1566, 1), (key1417, 1), (key1917, 1), (key1680, 1), (key1895, 1), (key1350, 1), (key1539, 1), (key1309, 1), (key1902, 1), (key1471, 1), (key1895, 1), (key1350, 1), (key1384, 1), (key1289, 1), (key1566, 1), (key1417, 1), (key1539, 1), (key1309, 1), (key1384, 1), (key1289, 1)]

theorem rawRowCheck8580 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form5 = rawRow8580 := by decide +kernel

def row8580 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

theorem rowCheck8580 : row8580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8580 := by decide +kernel

theorem rowEval8580 (x : Key → ℝ) : Integer.Sparse.eval row8580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8580, Integer.Sparse.eval_collectBalanced, rawRowCheck8580]

def rawRow8581 : Integer.Sparse Key := [(key1523, -24), (key1248, 6), (key1601, 6), (key1601, 6), (key1601, 6)]

theorem rawRowCheck8581 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow8581 := by decide +kernel

def row8581 : Integer.Sparse Key := [(key1248, 6), (key1523, -24), (key1601, 18)]

theorem rowCheck8581 : row8581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8581 := by decide +kernel

theorem rowEval8581 (x : Key → ℝ) : Integer.Sparse.eval row8581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8581, Integer.Sparse.eval_collectBalanced, rawRowCheck8581]

def rawRow8582 : Integer.Sparse Key := [(key1523, -24), (key1601, 6), (key1248, 6), (key1601, 6), (key1601, 6)]

theorem rawRowCheck8582 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form6 = rawRow8582 := by decide +kernel

def row8582 : Integer.Sparse Key := [(key1248, 6), (key1523, -24), (key1601, 18)]

theorem rowCheck8582 : row8582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8582 := by decide +kernel

theorem rowEval8582 (x : Key → ℝ) : Integer.Sparse.eval row8582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8582, Integer.Sparse.eval_collectBalanced, rawRowCheck8582]

def rawRow8583 : Integer.Sparse Key := [(key1523, -24), (key1601, 6), (key1601, 6), (key1248, 6), (key1601, 6)]

theorem rawRowCheck8583 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form6 = rawRow8583 := by decide +kernel

def row8583 : Integer.Sparse Key := [(key1248, 6), (key1523, -24), (key1601, 18)]

theorem rowCheck8583 : row8583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8583 := by decide +kernel

theorem rowEval8583 (x : Key → ℝ) : Integer.Sparse.eval row8583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8583, Integer.Sparse.eval_collectBalanced, rawRowCheck8583]

def rawRow8584 : Integer.Sparse Key := [(key1523, -24), (key1601, 6), (key1601, 6), (key1601, 6), (key1248, 6)]

theorem rawRowCheck8584 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form6 = rawRow8584 := by decide +kernel

def row8584 : Integer.Sparse Key := [(key1248, 6), (key1523, -24), (key1601, 18)]

theorem rowCheck8584 : row8584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8584 := by decide +kernel

theorem rowEval8584 (x : Key → ℝ) : Integer.Sparse.eval row8584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8584, Integer.Sparse.eval_collectBalanced, rawRowCheck8584]

def rawRow8585 : Integer.Sparse Key := [(key1601, -24), (key1248, 6), (key1523, 6), (key1601, 6), (key1601, 6)]

theorem rawRowCheck8585 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form6 = rawRow8585 := by decide +kernel

def row8585 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

theorem rowCheck8585 : row8585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8585 := by decide +kernel

theorem rowEval8585 (x : Key → ℝ) : Integer.Sparse.eval row8585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8585, Integer.Sparse.eval_collectBalanced, rawRowCheck8585]

def rawRow8586 : Integer.Sparse Key := [(key1601, -24), (key1248, 6), (key1601, 6), (key1523, 6), (key1601, 6)]

theorem rawRowCheck8586 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form6 = rawRow8586 := by decide +kernel

def row8586 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

theorem rowCheck8586 : row8586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8586 := by decide +kernel

theorem rowEval8586 (x : Key → ℝ) : Integer.Sparse.eval row8586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8586, Integer.Sparse.eval_collectBalanced, rawRowCheck8586]

def rawRow8587 : Integer.Sparse Key := [(key1601, -24), (key1248, 6), (key1601, 6), (key1601, 6), (key1523, 6)]

theorem rawRowCheck8587 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form6 = rawRow8587 := by decide +kernel

def row8587 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

theorem rowCheck8587 : row8587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8587 := by decide +kernel

theorem rowEval8587 (x : Key → ℝ) : Integer.Sparse.eval row8587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8587, Integer.Sparse.eval_collectBalanced, rawRowCheck8587]

def rawRow8588 : Integer.Sparse Key := [(key1601, -24), (key1523, 6), (key1248, 6), (key1601, 6), (key1601, 6)]

theorem rawRowCheck8588 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form6 = rawRow8588 := by decide +kernel

def row8588 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

theorem rowCheck8588 : row8588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8588 := by decide +kernel

theorem rowEval8588 (x : Key → ℝ) : Integer.Sparse.eval row8588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8588, Integer.Sparse.eval_collectBalanced, rawRowCheck8588]

def rawRow8589 : Integer.Sparse Key := [(key1601, -24), (key1523, 6), (key1601, 6), (key1248, 6), (key1601, 6)]

theorem rawRowCheck8589 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form6 = rawRow8589 := by decide +kernel

def row8589 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

theorem rowCheck8589 : row8589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8589 := by decide +kernel

theorem rowEval8589 (x : Key → ℝ) : Integer.Sparse.eval row8589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8589, Integer.Sparse.eval_collectBalanced, rawRowCheck8589]

def rawRow8590 : Integer.Sparse Key := [(key1601, -24), (key1523, 6), (key1601, 6), (key1601, 6), (key1248, 6)]

theorem rawRowCheck8590 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form6 = rawRow8590 := by decide +kernel

def row8590 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

theorem rowCheck8590 : row8590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8590 := by decide +kernel

theorem rowEval8590 (x : Key → ℝ) : Integer.Sparse.eval row8590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8590, Integer.Sparse.eval_collectBalanced, rawRowCheck8590]

def rawRow8591 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1248, 6), (key1523, 6), (key1601, 6)]

theorem rawRowCheck8591 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form6 = rawRow8591 := by decide +kernel

def row8591 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

theorem rowCheck8591 : row8591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8591 := by decide +kernel

theorem rowEval8591 (x : Key → ℝ) : Integer.Sparse.eval row8591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8591, Integer.Sparse.eval_collectBalanced, rawRowCheck8591]

def rawRow8592 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1248, 6), (key1601, 6), (key1523, 6)]

theorem rawRowCheck8592 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form6 = rawRow8592 := by decide +kernel

def row8592 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

theorem rowCheck8592 : row8592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8592 := by decide +kernel

theorem rowEval8592 (x : Key → ℝ) : Integer.Sparse.eval row8592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8592, Integer.Sparse.eval_collectBalanced, rawRowCheck8592]

def rawRow8593 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1523, 6), (key1248, 6), (key1601, 6)]

theorem rawRowCheck8593 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form6 = rawRow8593 := by decide +kernel

def row8593 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

theorem rowCheck8593 : row8593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8593 := by decide +kernel

theorem rowEval8593 (x : Key → ℝ) : Integer.Sparse.eval row8593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8593, Integer.Sparse.eval_collectBalanced, rawRowCheck8593]

def rawRow8594 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1523, 6), (key1601, 6), (key1248, 6)]

theorem rawRowCheck8594 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form6 = rawRow8594 := by decide +kernel

def row8594 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

theorem rowCheck8594 : row8594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8594 := by decide +kernel

theorem rowEval8594 (x : Key → ℝ) : Integer.Sparse.eval row8594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8594, Integer.Sparse.eval_collectBalanced, rawRowCheck8594]

def rawRow8595 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1601, 6), (key1248, 6), (key1523, 6)]

theorem rawRowCheck8595 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form6 = rawRow8595 := by decide +kernel

def row8595 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

theorem rowCheck8595 : row8595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8595 := by decide +kernel

theorem rowEval8595 (x : Key → ℝ) : Integer.Sparse.eval row8595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8595, Integer.Sparse.eval_collectBalanced, rawRowCheck8595]

def rawRow8596 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1601, 6), (key1523, 6), (key1248, 6)]

theorem rawRowCheck8596 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form6 = rawRow8596 := by decide +kernel

def row8596 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

theorem rowCheck8596 : row8596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8596 := by decide +kernel

theorem rowEval8596 (x : Key → ℝ) : Integer.Sparse.eval row8596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8596, Integer.Sparse.eval_collectBalanced, rawRowCheck8596]

def rawRow8597 : Integer.Sparse Key := [(key1384, -2), (key1384, -2), (key1384, -2), (key1539, -2), (key1539, -2), (key1539, -2), (key1539, -2), (key1539, -2), (key1539, -2), (key1895, -2), (key1895, -2), (key1895, -2), (key1289, 2), (key1289, 2), (key1289, 2), (key1566, 2), (key1566, 2), (key1566, 2), (key1566, 2), (key1566, 2), (key1566, 2), (key1902, 2), (key1902, 2), (key1902, 2)]

theorem rawRowCheck8597 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8597 := by decide +kernel

def row8597 : Integer.Sparse Key := [(key1289, 6), (key1384, -6), (key1539, -12), (key1566, 12), (key1895, -6), (key1902, 6)]

theorem rowCheck8597 : row8597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8597 := by decide +kernel

theorem rowEval8597 (x : Key → ℝ) : Integer.Sparse.eval row8597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8597, Integer.Sparse.eval_collectBalanced, rawRowCheck8597]

def rawRow8598 : Integer.Sparse Key := [(key1539, -2), (key1539, -2), (key1895, -2), (key1384, -2), (key1384, -2), (key1539, -2), (key1539, -2), (key1895, -2), (key1895, -2), (key1384, -2), (key1539, -2), (key1539, -2), (key1566, 2), (key1566, 2), (key1902, 2), (key1289, 2), (key1289, 2), (key1566, 2), (key1566, 2), (key1902, 2), (key1902, 2), (key1289, 2), (key1566, 2), (key1566, 2)]

theorem rawRowCheck8598 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form7 = rawRow8598 := by decide +kernel

def row8598 : Integer.Sparse Key := [(key1289, 6), (key1384, -6), (key1539, -12), (key1566, 12), (key1895, -6), (key1902, 6)]

theorem rowCheck8598 : row8598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8598 := by decide +kernel

theorem rowEval8598 (x : Key → ℝ) : Integer.Sparse.eval row8598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8598, Integer.Sparse.eval_collectBalanced, rawRowCheck8598]

def rawRow8599 : Integer.Sparse Key := [(key1539, -2), (key1895, -2), (key1539, -2), (key1539, -2), (key1895, -2), (key1384, -2), (key1895, -2), (key1384, -2), (key1539, -2), (key1539, -2), (key1384, -2), (key1539, -2), (key1566, 2), (key1902, 2), (key1566, 2), (key1566, 2), (key1902, 2), (key1289, 2), (key1902, 2), (key1289, 2), (key1566, 2), (key1566, 2), (key1289, 2), (key1566, 2)]

theorem rawRowCheck8599 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form7 = rawRow8599 := by decide +kernel

def row8599 : Integer.Sparse Key := [(key1289, 6), (key1384, -6), (key1539, -12), (key1566, 12), (key1895, -6), (key1902, 6)]

theorem rowCheck8599 : row8599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8599 := by decide +kernel

theorem rowEval8599 (x : Key → ℝ) : Integer.Sparse.eval row8599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8599, Integer.Sparse.eval_collectBalanced, rawRowCheck8599]

def rawRow8600 : Integer.Sparse Key := [(key1895, -2), (key1539, -2), (key1539, -2), (key1895, -2), (key1539, -2), (key1895, -2), (key1384, -2), (key1539, -2), (key1384, -2), (key1539, -2), (key1539, -2), (key1384, -2), (key1902, 2), (key1566, 2), (key1566, 2), (key1902, 2), (key1566, 2), (key1902, 2), (key1289, 2), (key1566, 2), (key1289, 2), (key1566, 2), (key1566, 2), (key1289, 2)]

theorem rawRowCheck8600 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form7 = rawRow8600 := by decide +kernel

def row8600 : Integer.Sparse Key := [(key1289, 6), (key1384, -6), (key1539, -12), (key1566, 12), (key1895, -6), (key1902, 6)]

theorem rowCheck8600 : row8600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8600 := by decide +kernel

theorem rowEval8600 (x : Key → ℝ) : Integer.Sparse.eval row8600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8600, Integer.Sparse.eval_collectBalanced, rawRowCheck8600]

def rawRow8601 : Integer.Sparse Key := [(key1417, -2), (key1417, -2), (key1471, -2), (key1566, -2), (key1566, -2), (key1615, -2), (key1615, -2), (key1680, -2), (key1680, -2), (key1902, -2), (key1917, -2), (key1917, -2), (key1309, 2), (key1309, 2), (key1350, 2), (key1539, 2), (key1539, 2), (key1615, 2), (key1615, 2), (key1680, 2), (key1680, 2), (key1895, 2), (key1917, 2), (key1917, 2)]

theorem rawRowCheck8601 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form7 = rawRow8601 := by decide +kernel

def row8601 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

theorem rowCheck8601 : row8601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8601 := by decide +kernel

theorem rowEval8601 (x : Key → ℝ) : Integer.Sparse.eval row8601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8601, Integer.Sparse.eval_collectBalanced, rawRowCheck8601]

def rawRow8602 : Integer.Sparse Key := [(key1417, -2), (key1471, -2), (key1417, -2), (key1615, -2), (key1680, -2), (key1566, -2), (key1680, -2), (key1566, -2), (key1615, -2), (key1917, -2), (key1902, -2), (key1917, -2), (key1309, 2), (key1350, 2), (key1309, 2), (key1615, 2), (key1680, 2), (key1539, 2), (key1680, 2), (key1539, 2), (key1615, 2), (key1917, 2), (key1895, 2), (key1917, 2)]

theorem rawRowCheck8602 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form7 = rawRow8602 := by decide +kernel

def row8602 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

theorem rowCheck8602 : row8602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8602 := by decide +kernel

theorem rowEval8602 (x : Key → ℝ) : Integer.Sparse.eval row8602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8602, Integer.Sparse.eval_collectBalanced, rawRowCheck8602]

def rawRow8603 : Integer.Sparse Key := [(key1471, -2), (key1417, -2), (key1417, -2), (key1680, -2), (key1615, -2), (key1680, -2), (key1566, -2), (key1615, -2), (key1566, -2), (key1917, -2), (key1917, -2), (key1902, -2), (key1350, 2), (key1309, 2), (key1309, 2), (key1680, 2), (key1615, 2), (key1680, 2), (key1539, 2), (key1615, 2), (key1539, 2), (key1917, 2), (key1917, 2), (key1895, 2)]

theorem rawRowCheck8603 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form7 = rawRow8603 := by decide +kernel

def row8603 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

theorem rowCheck8603 : row8603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8603 := by decide +kernel

theorem rowEval8603 (x : Key → ℝ) : Integer.Sparse.eval row8603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8603, Integer.Sparse.eval_collectBalanced, rawRowCheck8603]

def rawRow8604 : Integer.Sparse Key := [(key1566, -2), (key1566, -2), (key1902, -2), (key1417, -2), (key1417, -2), (key1615, -2), (key1615, -2), (key1917, -2), (key1917, -2), (key1471, -2), (key1680, -2), (key1680, -2), (key1539, 2), (key1539, 2), (key1895, 2), (key1309, 2), (key1309, 2), (key1615, 2), (key1615, 2), (key1917, 2), (key1917, 2), (key1350, 2), (key1680, 2), (key1680, 2)]

theorem rawRowCheck8604 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form7 = rawRow8604 := by decide +kernel

def row8604 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

theorem rowCheck8604 : row8604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8604 := by decide +kernel

theorem rowEval8604 (x : Key → ℝ) : Integer.Sparse.eval row8604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8604, Integer.Sparse.eval_collectBalanced, rawRowCheck8604]

def rawRow8605 : Integer.Sparse Key := [(key1566, -2), (key1902, -2), (key1566, -2), (key1615, -2), (key1917, -2), (key1417, -2), (key1917, -2), (key1417, -2), (key1615, -2), (key1680, -2), (key1471, -2), (key1680, -2), (key1539, 2), (key1895, 2), (key1539, 2), (key1615, 2), (key1917, 2), (key1309, 2), (key1917, 2), (key1309, 2), (key1615, 2), (key1680, 2), (key1350, 2), (key1680, 2)]

theorem rawRowCheck8605 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form7 = rawRow8605 := by decide +kernel

def row8605 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

theorem rowCheck8605 : row8605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8605 := by decide +kernel

theorem rowEval8605 (x : Key → ℝ) : Integer.Sparse.eval row8605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8605, Integer.Sparse.eval_collectBalanced, rawRowCheck8605]

def rawRow8606 : Integer.Sparse Key := [(key1902, -2), (key1566, -2), (key1566, -2), (key1917, -2), (key1615, -2), (key1917, -2), (key1417, -2), (key1615, -2), (key1417, -2), (key1680, -2), (key1680, -2), (key1471, -2), (key1895, 2), (key1539, 2), (key1539, 2), (key1917, 2), (key1615, 2), (key1917, 2), (key1309, 2), (key1615, 2), (key1309, 2), (key1680, 2), (key1680, 2), (key1350, 2)]

theorem rawRowCheck8606 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form7 = rawRow8606 := by decide +kernel

def row8606 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

theorem rowCheck8606 : row8606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8606 := by decide +kernel

theorem rowEval8606 (x : Key → ℝ) : Integer.Sparse.eval row8606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8606, Integer.Sparse.eval_collectBalanced, rawRowCheck8606]

def rawRow8607 : Integer.Sparse Key := [(key1615, -2), (key1680, -2), (key1917, -2), (key1417, -2), (key1471, -2), (key1566, -2), (key1680, -2), (key1902, -2), (key1917, -2), (key1417, -2), (key1566, -2), (key1615, -2), (key1615, 2), (key1680, 2), (key1917, 2), (key1309, 2), (key1350, 2), (key1539, 2), (key1680, 2), (key1895, 2), (key1917, 2), (key1309, 2), (key1539, 2), (key1615, 2)]

theorem rawRowCheck8607 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form7 = rawRow8607 := by decide +kernel

def row8607 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

theorem rowCheck8607 : row8607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8607 := by decide +kernel

theorem rowEval8607 (x : Key → ℝ) : Integer.Sparse.eval row8607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8607, Integer.Sparse.eval_collectBalanced, rawRowCheck8607]

def rawRow8608 : Integer.Sparse Key := [(key1680, -2), (key1615, -2), (key1917, -2), (key1471, -2), (key1417, -2), (key1680, -2), (key1566, -2), (key1917, -2), (key1902, -2), (key1417, -2), (key1615, -2), (key1566, -2), (key1680, 2), (key1615, 2), (key1917, 2), (key1350, 2), (key1309, 2), (key1680, 2), (key1539, 2), (key1917, 2), (key1895, 2), (key1309, 2), (key1615, 2), (key1539, 2)]

theorem rawRowCheck8608 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form7 = rawRow8608 := by decide +kernel

def row8608 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

theorem rowCheck8608 : row8608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8608 := by decide +kernel

theorem rowEval8608 (x : Key → ℝ) : Integer.Sparse.eval row8608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8608, Integer.Sparse.eval_collectBalanced, rawRowCheck8608]

def rawRow8609 : Integer.Sparse Key := [(key1615, -2), (key1917, -2), (key1680, -2), (key1566, -2), (key1902, -2), (key1417, -2), (key1917, -2), (key1471, -2), (key1680, -2), (key1566, -2), (key1417, -2), (key1615, -2), (key1615, 2), (key1917, 2), (key1680, 2), (key1539, 2), (key1895, 2), (key1309, 2), (key1917, 2), (key1350, 2), (key1680, 2), (key1539, 2), (key1309, 2), (key1615, 2)]

theorem rawRowCheck8609 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form7 = rawRow8609 := by decide +kernel

def row8609 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

theorem rowCheck8609 : row8609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8609 := by decide +kernel

theorem rowEval8609 (x : Key → ℝ) : Integer.Sparse.eval row8609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8609, Integer.Sparse.eval_collectBalanced, rawRowCheck8609]

def rawRow8610 : Integer.Sparse Key := [(key1917, -2), (key1615, -2), (key1680, -2), (key1902, -2), (key1566, -2), (key1917, -2), (key1417, -2), (key1680, -2), (key1471, -2), (key1566, -2), (key1615, -2), (key1417, -2), (key1917, 2), (key1615, 2), (key1680, 2), (key1895, 2), (key1539, 2), (key1917, 2), (key1309, 2), (key1680, 2), (key1350, 2), (key1539, 2), (key1615, 2), (key1309, 2)]

theorem rawRowCheck8610 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form7 = rawRow8610 := by decide +kernel

def row8610 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

theorem rowCheck8610 : row8610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8610 := by decide +kernel

theorem rowEval8610 (x : Key → ℝ) : Integer.Sparse.eval row8610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8610, Integer.Sparse.eval_collectBalanced, rawRowCheck8610]

def rawRow8611 : Integer.Sparse Key := [(key1680, -2), (key1917, -2), (key1615, -2), (key1680, -2), (key1917, -2), (key1471, -2), (key1902, -2), (key1417, -2), (key1566, -2), (key1615, -2), (key1417, -2), (key1566, -2), (key1680, 2), (key1917, 2), (key1615, 2), (key1680, 2), (key1917, 2), (key1350, 2), (key1895, 2), (key1309, 2), (key1539, 2), (key1615, 2), (key1309, 2), (key1539, 2)]

theorem rawRowCheck8611 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form7 = rawRow8611 := by decide +kernel

def row8611 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

theorem rowCheck8611 : row8611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8611 := by decide +kernel

theorem rowEval8611 (x : Key → ℝ) : Integer.Sparse.eval row8611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8611, Integer.Sparse.eval_collectBalanced, rawRowCheck8611]

def rawRow8612 : Integer.Sparse Key := [(key1917, -2), (key1680, -2), (key1615, -2), (key1917, -2), (key1680, -2), (key1902, -2), (key1471, -2), (key1566, -2), (key1417, -2), (key1615, -2), (key1566, -2), (key1417, -2), (key1917, 2), (key1680, 2), (key1615, 2), (key1917, 2), (key1680, 2), (key1895, 2), (key1350, 2), (key1539, 2), (key1309, 2), (key1615, 2), (key1539, 2), (key1309, 2)]

theorem rawRowCheck8612 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form7 = rawRow8612 := by decide +kernel

def row8612 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

theorem rowCheck8612 : row8612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8612 := by decide +kernel

theorem rowEval8612 (x : Key → ℝ) : Integer.Sparse.eval row8612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8612, Integer.Sparse.eval_collectBalanced, rawRowCheck8612]

def rawRow8613 : Integer.Sparse Key := [(key238, -2), (key238, -2), (key238, -2), (key408, -2), (key408, -2), (key408, -2), (key408, -2), (key408, -2), (key408, -2), (key417, -2), (key417, -2), (key417, -2), (key250, 1), (key250, 1), (key250, 1), (key250, 1), (key250, 1), (key250, 1), (key387, 1), (key387, 1), (key387, 1), (key387, 1), (key387, 1), (key387, 1), (key437, 1), (key437, 1), (key437, 1), (key437, 1), (key437, 1), (key437, 1), (key449, 1), (key449, 1), (key449, 1), (key449, 1), (key449, 1), (key449, 1)]

theorem rawRowCheck8613 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form8 = rawRow8613 := by decide +kernel

def row8613 : Integer.Sparse Key := [(key238, -6), (key250, 6), (key387, 6), (key408, -12), (key417, -6), (key437, 6), (key449, 6)]

theorem rowCheck8613 : row8613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8613 := by decide +kernel

theorem rowEval8613 (x : Key → ℝ) : Integer.Sparse.eval row8613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8613, Integer.Sparse.eval_collectBalanced, rawRowCheck8613]

def rawRow8614 : Integer.Sparse Key := [(key408, -2), (key408, -2), (key417, -2), (key238, -2), (key238, -2), (key408, -2), (key408, -2), (key417, -2), (key417, -2), (key238, -2), (key408, -2), (key408, -2), (key387, 1), (key387, 1), (key437, 1), (key437, 1), (key449, 1), (key449, 1), (key250, 1), (key250, 1), (key437, 1), (key437, 1), (key449, 1), (key449, 1), (key250, 1), (key250, 1), (key387, 1), (key387, 1), (key449, 1), (key449, 1), (key250, 1), (key250, 1), (key387, 1), (key387, 1), (key437, 1), (key437, 1)]

theorem rawRowCheck8614 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form8 = rawRow8614 := by decide +kernel

def row8614 : Integer.Sparse Key := [(key238, -6), (key250, 6), (key387, 6), (key408, -12), (key417, -6), (key437, 6), (key449, 6)]

theorem rowCheck8614 : row8614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8614 := by decide +kernel

theorem rowEval8614 (x : Key → ℝ) : Integer.Sparse.eval row8614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8614, Integer.Sparse.eval_collectBalanced, rawRowCheck8614]

def rawRow8615 : Integer.Sparse Key := [(key408, -2), (key417, -2), (key408, -2), (key408, -2), (key417, -2), (key238, -2), (key417, -2), (key238, -2), (key408, -2), (key408, -2), (key238, -2), (key408, -2), (key437, 1), (key449, 1), (key387, 1), (key449, 1), (key387, 1), (key437, 1), (key437, 1), (key449, 1), (key250, 1), (key449, 1), (key250, 1), (key437, 1), (key387, 1), (key449, 1), (key250, 1), (key449, 1), (key250, 1), (key387, 1), (key387, 1), (key437, 1), (key250, 1), (key437, 1), (key250, 1), (key387, 1)]

theorem rawRowCheck8615 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form8 = rawRow8615 := by decide +kernel

def row8615 : Integer.Sparse Key := [(key238, -6), (key250, 6), (key387, 6), (key408, -12), (key417, -6), (key437, 6), (key449, 6)]

theorem rowCheck8615 : row8615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8615 := by decide +kernel

theorem rowEval8615 (x : Key → ℝ) : Integer.Sparse.eval row8615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8615, Integer.Sparse.eval_collectBalanced, rawRowCheck8615]

def rawRow8616 : Integer.Sparse Key := [(key417, -2), (key408, -2), (key408, -2), (key417, -2), (key408, -2), (key417, -2), (key238, -2), (key408, -2), (key238, -2), (key408, -2), (key408, -2), (key238, -2), (key449, 1), (key437, 1), (key449, 1), (key387, 1), (key437, 1), (key387, 1), (key449, 1), (key437, 1), (key449, 1), (key250, 1), (key437, 1), (key250, 1), (key449, 1), (key387, 1), (key449, 1), (key250, 1), (key387, 1), (key250, 1), (key437, 1), (key387, 1), (key437, 1), (key250, 1), (key387, 1), (key250, 1)]

theorem rawRowCheck8616 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form8 = rawRow8616 := by decide +kernel

def row8616 : Integer.Sparse Key := [(key238, -6), (key250, 6), (key387, 6), (key408, -12), (key417, -6), (key437, 6), (key449, 6)]

theorem rowCheck8616 : row8616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8616 := by decide +kernel

theorem rowEval8616 (x : Key → ℝ) : Integer.Sparse.eval row8616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8616, Integer.Sparse.eval_collectBalanced, rawRowCheck8616]

def rawRow8617 : Integer.Sparse Key := [(key250, -2), (key250, -2), (key259, -2), (key318, -2), (key318, -2), (key437, -2), (key437, -2), (key441, -2), (key441, -2), (key327, -2), (key449, -2), (key449, -2), (key238, 1), (key238, 1), (key250, 1), (key250, 1), (key259, 1), (key259, 1), (key304, 1), (key304, 1), (key387, 1), (key387, 1), (key396, 1), (key396, 1), (key318, 1), (key318, 1), (key408, 1), (key408, 1), (key441, 1), (key441, 1), (key327, 1), (key327, 1), (key417, 1), (key417, 1), (key449, 1), (key449, 1)]

theorem rawRowCheck8617 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form8 = rawRow8617 := by decide +kernel

def row8617 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

theorem rowCheck8617 : row8617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8617 := by decide +kernel

theorem rowEval8617 (x : Key → ℝ) : Integer.Sparse.eval row8617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8617, Integer.Sparse.eval_collectBalanced, rawRowCheck8617]

def rawRow8618 : Integer.Sparse Key := [(key250, -2), (key259, -2), (key250, -2), (key437, -2), (key441, -2), (key318, -2), (key441, -2), (key318, -2), (key437, -2), (key449, -2), (key327, -2), (key449, -2), (key250, 1), (key259, 1), (key238, 1), (key259, 1), (key238, 1), (key250, 1), (key387, 1), (key396, 1), (key304, 1), (key396, 1), (key304, 1), (key387, 1), (key408, 1), (key441, 1), (key318, 1), (key441, 1), (key318, 1), (key408, 1), (key417, 1), (key449, 1), (key327, 1), (key449, 1), (key327, 1), (key417, 1)]

theorem rawRowCheck8618 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form8 = rawRow8618 := by decide +kernel

def row8618 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

theorem rowCheck8618 : row8618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8618 := by decide +kernel

theorem rowEval8618 (x : Key → ℝ) : Integer.Sparse.eval row8618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8618, Integer.Sparse.eval_collectBalanced, rawRowCheck8618]

def rawRow8619 : Integer.Sparse Key := [(key259, -2), (key250, -2), (key250, -2), (key441, -2), (key437, -2), (key441, -2), (key318, -2), (key437, -2), (key318, -2), (key449, -2), (key449, -2), (key327, -2), (key259, 1), (key250, 1), (key259, 1), (key238, 1), (key250, 1), (key238, 1), (key396, 1), (key387, 1), (key396, 1), (key304, 1), (key387, 1), (key304, 1), (key441, 1), (key408, 1), (key441, 1), (key318, 1), (key408, 1), (key318, 1), (key449, 1), (key417, 1), (key449, 1), (key327, 1), (key417, 1), (key327, 1)]

theorem rawRowCheck8619 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form8 = rawRow8619 := by decide +kernel

def row8619 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

theorem rowCheck8619 : row8619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8619 := by decide +kernel

theorem rowEval8619 (x : Key → ℝ) : Integer.Sparse.eval row8619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8619, Integer.Sparse.eval_collectBalanced, rawRowCheck8619]

def rawRow8620 : Integer.Sparse Key := [(key318, -2), (key318, -2), (key327, -2), (key250, -2), (key250, -2), (key437, -2), (key437, -2), (key449, -2), (key449, -2), (key259, -2), (key441, -2), (key441, -2), (key304, 1), (key304, 1), (key318, 1), (key318, 1), (key327, 1), (key327, 1), (key238, 1), (key238, 1), (key408, 1), (key408, 1), (key417, 1), (key417, 1), (key250, 1), (key250, 1), (key387, 1), (key387, 1), (key449, 1), (key449, 1), (key259, 1), (key259, 1), (key396, 1), (key396, 1), (key441, 1), (key441, 1)]

theorem rawRowCheck8620 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form8 = rawRow8620 := by decide +kernel

def row8620 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

theorem rowCheck8620 : row8620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8620 := by decide +kernel

theorem rowEval8620 (x : Key → ℝ) : Integer.Sparse.eval row8620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8620, Integer.Sparse.eval_collectBalanced, rawRowCheck8620]

def rawRow8621 : Integer.Sparse Key := [(key318, -2), (key327, -2), (key318, -2), (key437, -2), (key449, -2), (key250, -2), (key449, -2), (key250, -2), (key437, -2), (key441, -2), (key259, -2), (key441, -2), (key318, 1), (key327, 1), (key304, 1), (key327, 1), (key304, 1), (key318, 1), (key408, 1), (key417, 1), (key238, 1), (key417, 1), (key238, 1), (key408, 1), (key387, 1), (key449, 1), (key250, 1), (key449, 1), (key250, 1), (key387, 1), (key396, 1), (key441, 1), (key259, 1), (key441, 1), (key259, 1), (key396, 1)]

theorem rawRowCheck8621 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form8 = rawRow8621 := by decide +kernel

def row8621 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

theorem rowCheck8621 : row8621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8621 := by decide +kernel

theorem rowEval8621 (x : Key → ℝ) : Integer.Sparse.eval row8621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8621, Integer.Sparse.eval_collectBalanced, rawRowCheck8621]

def rawRow8622 : Integer.Sparse Key := [(key327, -2), (key318, -2), (key318, -2), (key449, -2), (key437, -2), (key449, -2), (key250, -2), (key437, -2), (key250, -2), (key441, -2), (key441, -2), (key259, -2), (key327, 1), (key318, 1), (key327, 1), (key304, 1), (key318, 1), (key304, 1), (key417, 1), (key408, 1), (key417, 1), (key238, 1), (key408, 1), (key238, 1), (key449, 1), (key387, 1), (key449, 1), (key250, 1), (key387, 1), (key250, 1), (key441, 1), (key396, 1), (key441, 1), (key259, 1), (key396, 1), (key259, 1)]

theorem rawRowCheck8622 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form8 = rawRow8622 := by decide +kernel

def row8622 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

theorem rowCheck8622 : row8622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8622 := by decide +kernel

theorem rowEval8622 (x : Key → ℝ) : Integer.Sparse.eval row8622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8622, Integer.Sparse.eval_collectBalanced, rawRowCheck8622]

def rawRow8623 : Integer.Sparse Key := [(key437, -2), (key441, -2), (key449, -2), (key250, -2), (key259, -2), (key318, -2), (key441, -2), (key327, -2), (key449, -2), (key250, -2), (key318, -2), (key437, -2), (key387, 1), (key396, 1), (key408, 1), (key441, 1), (key417, 1), (key449, 1), (key250, 1), (key259, 1), (key318, 1), (key441, 1), (key327, 1), (key449, 1), (key238, 1), (key259, 1), (key304, 1), (key396, 1), (key327, 1), (key417, 1), (key238, 1), (key250, 1), (key304, 1), (key387, 1), (key318, 1), (key408, 1)]

theorem rawRowCheck8623 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form8 = rawRow8623 := by decide +kernel

def row8623 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

theorem rowCheck8623 : row8623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8623 := by decide +kernel

theorem rowEval8623 (x : Key → ℝ) : Integer.Sparse.eval row8623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8623, Integer.Sparse.eval_collectBalanced, rawRowCheck8623]

def rawRow8624 : Integer.Sparse Key := [(key441, -2), (key437, -2), (key449, -2), (key259, -2), (key250, -2), (key441, -2), (key318, -2), (key449, -2), (key327, -2), (key250, -2), (key437, -2), (key318, -2), (key396, 1), (key387, 1), (key441, 1), (key408, 1), (key449, 1), (key417, 1), (key259, 1), (key250, 1), (key441, 1), (key318, 1), (key449, 1), (key327, 1), (key259, 1), (key238, 1), (key396, 1), (key304, 1), (key417, 1), (key327, 1), (key250, 1), (key238, 1), (key387, 1), (key304, 1), (key408, 1), (key318, 1)]

theorem rawRowCheck8624 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form8 = rawRow8624 := by decide +kernel

def row8624 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

theorem rowCheck8624 : row8624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8624 := by decide +kernel

theorem rowEval8624 (x : Key → ℝ) : Integer.Sparse.eval row8624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8624, Integer.Sparse.eval_collectBalanced, rawRowCheck8624]

def rawRow8625 : Integer.Sparse Key := [(key437, -2), (key449, -2), (key441, -2), (key318, -2), (key327, -2), (key250, -2), (key449, -2), (key259, -2), (key441, -2), (key318, -2), (key250, -2), (key437, -2), (key408, 1), (key417, 1), (key387, 1), (key449, 1), (key396, 1), (key441, 1), (key318, 1), (key327, 1), (key250, 1), (key449, 1), (key259, 1), (key441, 1), (key304, 1), (key327, 1), (key238, 1), (key417, 1), (key259, 1), (key396, 1), (key304, 1), (key318, 1), (key238, 1), (key408, 1), (key250, 1), (key387, 1)]

theorem rawRowCheck8625 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form8 = rawRow8625 := by decide +kernel

def row8625 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

theorem rowCheck8625 : row8625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8625 := by decide +kernel

theorem rowEval8625 (x : Key → ℝ) : Integer.Sparse.eval row8625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8625, Integer.Sparse.eval_collectBalanced, rawRowCheck8625]

def rawRow8626 : Integer.Sparse Key := [(key449, -2), (key437, -2), (key441, -2), (key327, -2), (key318, -2), (key449, -2), (key250, -2), (key441, -2), (key259, -2), (key318, -2), (key437, -2), (key250, -2), (key417, 1), (key408, 1), (key449, 1), (key387, 1), (key441, 1), (key396, 1), (key327, 1), (key318, 1), (key449, 1), (key250, 1), (key441, 1), (key259, 1), (key327, 1), (key304, 1), (key417, 1), (key238, 1), (key396, 1), (key259, 1), (key318, 1), (key304, 1), (key408, 1), (key238, 1), (key387, 1), (key250, 1)]

theorem rawRowCheck8626 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form8 = rawRow8626 := by decide +kernel

def row8626 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

theorem rowCheck8626 : row8626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8626 := by decide +kernel

theorem rowEval8626 (x : Key → ℝ) : Integer.Sparse.eval row8626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8626, Integer.Sparse.eval_collectBalanced, rawRowCheck8626]

def rawRow8627 : Integer.Sparse Key := [(key441, -2), (key449, -2), (key437, -2), (key441, -2), (key449, -2), (key259, -2), (key327, -2), (key250, -2), (key318, -2), (key437, -2), (key250, -2), (key318, -2), (key441, 1), (key449, 1), (key396, 1), (key417, 1), (key387, 1), (key408, 1), (key441, 1), (key449, 1), (key259, 1), (key327, 1), (key250, 1), (key318, 1), (key396, 1), (key417, 1), (key259, 1), (key327, 1), (key238, 1), (key304, 1), (key387, 1), (key408, 1), (key250, 1), (key318, 1), (key238, 1), (key304, 1)]

theorem rawRowCheck8627 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form8 = rawRow8627 := by decide +kernel

def row8627 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

theorem rowCheck8627 : row8627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8627 := by decide +kernel

theorem rowEval8627 (x : Key → ℝ) : Integer.Sparse.eval row8627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8627, Integer.Sparse.eval_collectBalanced, rawRowCheck8627]

def rawRow8628 : Integer.Sparse Key := [(key449, -2), (key441, -2), (key437, -2), (key449, -2), (key441, -2), (key327, -2), (key259, -2), (key318, -2), (key250, -2), (key437, -2), (key318, -2), (key250, -2), (key449, 1), (key441, 1), (key417, 1), (key396, 1), (key408, 1), (key387, 1), (key449, 1), (key441, 1), (key327, 1), (key259, 1), (key318, 1), (key250, 1), (key417, 1), (key396, 1), (key327, 1), (key259, 1), (key304, 1), (key238, 1), (key408, 1), (key387, 1), (key318, 1), (key250, 1), (key304, 1), (key238, 1)]

theorem rawRowCheck8628 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form8 = rawRow8628 := by decide +kernel

def row8628 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

theorem rowCheck8628 : row8628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8628 := by decide +kernel

theorem rowEval8628 (x : Key → ℝ) : Integer.Sparse.eval row8628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8628, Integer.Sparse.eval_collectBalanced, rawRowCheck8628]

def rawRow8629 : Integer.Sparse Key := [(key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1350, -2), (key1350, -2), (key1350, -2), (key1471, -2), (key1471, -2), (key1471, -2), (key1680, -2), (key1680, -2), (key1680, -2), (key1680, -2), (key1680, -2), (key1680, -2)]

theorem rawRowCheck8629 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form9 = rawRow8629 := by decide +kernel

def row8629 : Integer.Sparse Key := [(key1309, 6), (key1350, -6), (key1417, 6), (key1471, -6), (key1615, 6), (key1680, -12), (key1917, 6)]

theorem rowCheck8629 : row8629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8629 := by decide +kernel

theorem rowEval8629 (x : Key → ℝ) : Integer.Sparse.eval row8629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8629, Integer.Sparse.eval_collectBalanced, rawRowCheck8629]

def rawRow8630 : Integer.Sparse Key := [(key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1471, -2), (key1680, -2), (key1680, -2), (key1350, -2), (key1680, -2), (key1680, -2), (key1350, -2), (key1350, -2), (key1471, -2), (key1471, -2), (key1680, -2), (key1680, -2)]

theorem rawRowCheck8630 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form9 = rawRow8630 := by decide +kernel

def row8630 : Integer.Sparse Key := [(key1309, 6), (key1350, -6), (key1417, 6), (key1471, -6), (key1615, 6), (key1680, -12), (key1917, 6)]

theorem rowCheck8630 : row8630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8630 := by decide +kernel

theorem rowEval8630 (x : Key → ℝ) : Integer.Sparse.eval row8630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8630, Integer.Sparse.eval_collectBalanced, rawRowCheck8630]

def rawRow8631 : Integer.Sparse Key := [(key1615, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1615, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1309, 1), (key1615, 1), (key1309, 1), (key1417, 1), (key1680, -2), (key1471, -2), (key1680, -2), (key1680, -2), (key1350, -2), (key1680, -2), (key1471, -2), (key1680, -2), (key1350, -2), (key1680, -2), (key1350, -2), (key1471, -2)]

theorem rawRowCheck8631 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form9 = rawRow8631 := by decide +kernel

def row8631 : Integer.Sparse Key := [(key1309, 6), (key1350, -6), (key1417, 6), (key1471, -6), (key1615, 6), (key1680, -12), (key1917, 6)]

theorem rowCheck8631 : row8631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8631 := by decide +kernel

theorem rowEval8631 (x : Key → ℝ) : Integer.Sparse.eval row8631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8631, Integer.Sparse.eval_collectBalanced, rawRowCheck8631]

def rawRow8632 : Integer.Sparse Key := [(key1917, 1), (key1615, 1), (key1917, 1), (key1417, 1), (key1615, 1), (key1417, 1), (key1917, 1), (key1615, 1), (key1917, 1), (key1309, 1), (key1615, 1), (key1309, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1309, 1), (key1615, 1), (key1417, 1), (key1615, 1), (key1309, 1), (key1417, 1), (key1309, 1), (key1680, -2), (key1680, -2), (key1471, -2), (key1680, -2), (key1680, -2), (key1350, -2), (key1680, -2), (key1471, -2), (key1680, -2), (key1350, -2), (key1471, -2), (key1350, -2)]

theorem rawRowCheck8632 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form9 = rawRow8632 := by decide +kernel

def row8632 : Integer.Sparse Key := [(key1309, 6), (key1350, -6), (key1417, 6), (key1471, -6), (key1615, 6), (key1680, -12), (key1917, 6)]

theorem rowCheck8632 : row8632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8632 := by decide +kernel

theorem rowEval8632 (x : Key → ℝ) : Integer.Sparse.eval row8632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8632, Integer.Sparse.eval_collectBalanced, rawRowCheck8632]

def rawRow8633 : Integer.Sparse Key := [(key1289, 1), (key1289, 1), (key1309, 1), (key1309, 1), (key1350, 1), (key1350, 1), (key1384, 1), (key1384, 1), (key1417, 1), (key1417, 1), (key1471, 1), (key1471, 1), (key1539, 1), (key1539, 1), (key1566, 1), (key1566, 1), (key1680, 1), (key1680, 1), (key1895, 1), (key1895, 1), (key1902, 1), (key1902, 1), (key1917, 1), (key1917, 1), (key1289, -2), (key1309, -2), (key1309, -2), (key1384, -2), (key1417, -2), (key1417, -2), (key1539, -2), (key1539, -2), (key1566, -2), (key1566, -2), (key1615, -2), (key1615, -2)]

theorem rawRowCheck8633 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form9 = rawRow8633 := by decide +kernel

def row8633 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

theorem rowCheck8633 : row8633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8633 := by decide +kernel

theorem rowEval8633 (x : Key → ℝ) : Integer.Sparse.eval row8633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8633, Integer.Sparse.eval_collectBalanced, rawRowCheck8633]

def rawRow8634 : Integer.Sparse Key := [(key1309, 1), (key1350, 1), (key1289, 1), (key1350, 1), (key1289, 1), (key1309, 1), (key1417, 1), (key1471, 1), (key1384, 1), (key1471, 1), (key1384, 1), (key1417, 1), (key1566, 1), (key1680, 1), (key1539, 1), (key1680, 1), (key1539, 1), (key1566, 1), (key1902, 1), (key1917, 1), (key1895, 1), (key1917, 1), (key1895, 1), (key1902, 1), (key1309, -2), (key1289, -2), (key1309, -2), (key1417, -2), (key1384, -2), (key1417, -2), (key1566, -2), (key1615, -2), (key1539, -2), (key1615, -2), (key1539, -2), (key1566, -2)]

theorem rawRowCheck8634 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form9 = rawRow8634 := by decide +kernel

def row8634 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

theorem rowCheck8634 : row8634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8634 := by decide +kernel

theorem rowEval8634 (x : Key → ℝ) : Integer.Sparse.eval row8634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8634, Integer.Sparse.eval_collectBalanced, rawRowCheck8634]

def rawRow8635 : Integer.Sparse Key := [(key1350, 1), (key1309, 1), (key1350, 1), (key1289, 1), (key1309, 1), (key1289, 1), (key1471, 1), (key1417, 1), (key1471, 1), (key1384, 1), (key1417, 1), (key1384, 1), (key1680, 1), (key1566, 1), (key1680, 1), (key1539, 1), (key1566, 1), (key1539, 1), (key1917, 1), (key1902, 1), (key1917, 1), (key1895, 1), (key1902, 1), (key1895, 1), (key1309, -2), (key1309, -2), (key1289, -2), (key1417, -2), (key1417, -2), (key1384, -2), (key1615, -2), (key1566, -2), (key1615, -2), (key1539, -2), (key1566, -2), (key1539, -2)]

theorem rawRowCheck8635 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form9 = rawRow8635 := by decide +kernel

def row8635 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

theorem rowCheck8635 : row8635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8635 := by decide +kernel

theorem rowEval8635 (x : Key → ℝ) : Integer.Sparse.eval row8635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8635, Integer.Sparse.eval_collectBalanced, rawRowCheck8635]

def rawRow8636 : Integer.Sparse Key := [(key1384, 1), (key1384, 1), (key1539, 1), (key1539, 1), (key1895, 1), (key1895, 1), (key1289, 1), (key1289, 1), (key1566, 1), (key1566, 1), (key1902, 1), (key1902, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1917, 1), (key1917, 1), (key1350, 1), (key1350, 1), (key1471, 1), (key1471, 1), (key1680, 1), (key1680, 1), (key1384, -2), (key1539, -2), (key1539, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1309, -2), (key1309, -2), (key1417, -2), (key1417, -2), (key1615, -2), (key1615, -2)]

theorem rawRowCheck8636 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form9 = rawRow8636 := by decide +kernel

def row8636 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

theorem rowCheck8636 : row8636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8636 := by decide +kernel

theorem rowEval8636 (x : Key → ℝ) : Integer.Sparse.eval row8636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8636, Integer.Sparse.eval_collectBalanced, rawRowCheck8636]

def rawRow8637 : Integer.Sparse Key := [(key1539, 1), (key1895, 1), (key1384, 1), (key1895, 1), (key1384, 1), (key1539, 1), (key1566, 1), (key1902, 1), (key1289, 1), (key1902, 1), (key1289, 1), (key1566, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1471, 1), (key1680, 1), (key1350, 1), (key1680, 1), (key1350, 1), (key1471, 1), (key1539, -2), (key1384, -2), (key1539, -2), (key1566, -2), (key1289, -2), (key1566, -2), (key1417, -2), (key1615, -2), (key1309, -2), (key1615, -2), (key1309, -2), (key1417, -2)]

theorem rawRowCheck8637 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form9 = rawRow8637 := by decide +kernel

def row8637 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

theorem rowCheck8637 : row8637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8637 := by decide +kernel

theorem rowEval8637 (x : Key → ℝ) : Integer.Sparse.eval row8637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8637, Integer.Sparse.eval_collectBalanced, rawRowCheck8637]

def rawRow8638 : Integer.Sparse Key := [(key1895, 1), (key1539, 1), (key1895, 1), (key1384, 1), (key1539, 1), (key1384, 1), (key1902, 1), (key1566, 1), (key1902, 1), (key1289, 1), (key1566, 1), (key1289, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1309, 1), (key1680, 1), (key1471, 1), (key1680, 1), (key1350, 1), (key1471, 1), (key1350, 1), (key1539, -2), (key1539, -2), (key1384, -2), (key1566, -2), (key1566, -2), (key1289, -2), (key1615, -2), (key1417, -2), (key1615, -2), (key1309, -2), (key1417, -2), (key1309, -2)]

theorem rawRowCheck8638 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form9 = rawRow8638 := by decide +kernel

def row8638 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

theorem rowCheck8638 : row8638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8638 := by decide +kernel

theorem rowEval8638 (x : Key → ℝ) : Integer.Sparse.eval row8638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8638, Integer.Sparse.eval_collectBalanced, rawRowCheck8638]

def rawRow8639 : Integer.Sparse Key := [(key1417, 1), (key1471, 1), (key1566, 1), (key1680, 1), (key1902, 1), (key1917, 1), (key1309, 1), (key1350, 1), (key1539, 1), (key1680, 1), (key1895, 1), (key1917, 1), (key1289, 1), (key1350, 1), (key1384, 1), (key1471, 1), (key1895, 1), (key1902, 1), (key1289, 1), (key1309, 1), (key1384, 1), (key1417, 1), (key1539, 1), (key1566, 1), (key1417, -2), (key1566, -2), (key1615, -2), (key1309, -2), (key1539, -2), (key1615, -2), (key1289, -2), (key1309, -2), (key1384, -2), (key1417, -2), (key1539, -2), (key1566, -2)]

theorem rawRowCheck8639 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form9 = rawRow8639 := by decide +kernel

def row8639 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

theorem rowCheck8639 : row8639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8639 := by decide +kernel

theorem rowEval8639 (x : Key → ℝ) : Integer.Sparse.eval row8639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8639, Integer.Sparse.eval_collectBalanced, rawRowCheck8639]

def rawRow8640 : Integer.Sparse Key := [(key1471, 1), (key1417, 1), (key1680, 1), (key1566, 1), (key1917, 1), (key1902, 1), (key1350, 1), (key1309, 1), (key1680, 1), (key1539, 1), (key1917, 1), (key1895, 1), (key1350, 1), (key1289, 1), (key1471, 1), (key1384, 1), (key1902, 1), (key1895, 1), (key1309, 1), (key1289, 1), (key1417, 1), (key1384, 1), (key1566, 1), (key1539, 1), (key1417, -2), (key1615, -2), (key1566, -2), (key1309, -2), (key1615, -2), (key1539, -2), (key1309, -2), (key1289, -2), (key1417, -2), (key1384, -2), (key1566, -2), (key1539, -2)]

theorem rawRowCheck8640 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form9 = rawRow8640 := by decide +kernel

def row8640 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

theorem rowCheck8640 : row8640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8640 := by decide +kernel

theorem rowEval8640 (x : Key → ℝ) : Integer.Sparse.eval row8640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8640, Integer.Sparse.eval_collectBalanced, rawRowCheck8640]

def rawRow8641 : Integer.Sparse Key := [(key1566, 1), (key1902, 1), (key1417, 1), (key1917, 1), (key1471, 1), (key1680, 1), (key1539, 1), (key1895, 1), (key1309, 1), (key1917, 1), (key1350, 1), (key1680, 1), (key1384, 1), (key1895, 1), (key1289, 1), (key1902, 1), (key1350, 1), (key1471, 1), (key1384, 1), (key1539, 1), (key1289, 1), (key1566, 1), (key1309, 1), (key1417, 1), (key1566, -2), (key1417, -2), (key1615, -2), (key1539, -2), (key1309, -2), (key1615, -2), (key1384, -2), (key1539, -2), (key1289, -2), (key1566, -2), (key1309, -2), (key1417, -2)]

theorem rawRowCheck8641 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form9 = rawRow8641 := by decide +kernel

def row8641 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

theorem rowCheck8641 : row8641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8641 := by decide +kernel

theorem rowEval8641 (x : Key → ℝ) : Integer.Sparse.eval row8641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8641, Integer.Sparse.eval_collectBalanced, rawRowCheck8641]

def rawRow8642 : Integer.Sparse Key := [(key1902, 1), (key1566, 1), (key1917, 1), (key1417, 1), (key1680, 1), (key1471, 1), (key1895, 1), (key1539, 1), (key1917, 1), (key1309, 1), (key1680, 1), (key1350, 1), (key1895, 1), (key1384, 1), (key1902, 1), (key1289, 1), (key1471, 1), (key1350, 1), (key1539, 1), (key1384, 1), (key1566, 1), (key1289, 1), (key1417, 1), (key1309, 1), (key1566, -2), (key1615, -2), (key1417, -2), (key1539, -2), (key1615, -2), (key1309, -2), (key1539, -2), (key1384, -2), (key1566, -2), (key1289, -2), (key1417, -2), (key1309, -2)]

theorem rawRowCheck8642 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form9 = rawRow8642 := by decide +kernel

def row8642 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

theorem rowCheck8642 : row8642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8642 := by decide +kernel

theorem rowEval8642 (x : Key → ℝ) : Integer.Sparse.eval row8642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8642, Integer.Sparse.eval_collectBalanced, rawRowCheck8642]

def rawRow8643 : Integer.Sparse Key := [(key1680, 1), (key1917, 1), (key1471, 1), (key1902, 1), (key1417, 1), (key1566, 1), (key1680, 1), (key1917, 1), (key1350, 1), (key1895, 1), (key1309, 1), (key1539, 1), (key1471, 1), (key1902, 1), (key1350, 1), (key1895, 1), (key1289, 1), (key1384, 1), (key1417, 1), (key1566, 1), (key1309, 1), (key1539, 1), (key1289, 1), (key1384, 1), (key1615, -2), (key1417, -2), (key1566, -2), (key1615, -2), (key1309, -2), (key1539, -2), (key1417, -2), (key1566, -2), (key1309, -2), (key1539, -2), (key1289, -2), (key1384, -2)]

theorem rawRowCheck8643 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form9 = rawRow8643 := by decide +kernel

def row8643 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

theorem rowCheck8643 : row8643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8643 := by decide +kernel

theorem rowEval8643 (x : Key → ℝ) : Integer.Sparse.eval row8643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8643, Integer.Sparse.eval_collectBalanced, rawRowCheck8643]

def rawRow8644 : Integer.Sparse Key := [(key1917, 1), (key1680, 1), (key1902, 1), (key1471, 1), (key1566, 1), (key1417, 1), (key1917, 1), (key1680, 1), (key1895, 1), (key1350, 1), (key1539, 1), (key1309, 1), (key1902, 1), (key1471, 1), (key1895, 1), (key1350, 1), (key1384, 1), (key1289, 1), (key1566, 1), (key1417, 1), (key1539, 1), (key1309, 1), (key1384, 1), (key1289, 1), (key1615, -2), (key1566, -2), (key1417, -2), (key1615, -2), (key1539, -2), (key1309, -2), (key1566, -2), (key1417, -2), (key1539, -2), (key1309, -2), (key1384, -2), (key1289, -2)]

theorem rawRowCheck8644 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form9 = rawRow8644 := by decide +kernel

def row8644 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

theorem rowCheck8644 : row8644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8644 := by decide +kernel

theorem rowEval8644 (x : Key → ℝ) : Integer.Sparse.eval row8644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8644, Integer.Sparse.eval_collectBalanced, rawRowCheck8644]

def rawRow8645 : Integer.Sparse Key := [(key234, -6), (key404, -6), (key404, -6), (key404, -6), (key246, 2), (key246, 2), (key246, 2), (key314, 2), (key314, 2), (key314, 2), (key433, 2), (key433, 2), (key433, 2), (key433, 2), (key433, 2), (key433, 2)]

theorem rawRowCheck8645 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow8645 := by decide +kernel

def row8645 : Integer.Sparse Key := [(key234, -6), (key246, 6), (key314, 6), (key404, -18), (key433, 12)]

theorem rowCheck8645 : row8645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8645 := by decide +kernel

theorem rowEval8645 (x : Key → ℝ) : Integer.Sparse.eval row8645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8645, Integer.Sparse.eval_collectBalanced, rawRowCheck8645]

def rawRow8646 : Integer.Sparse Key := [(key404, -6), (key234, -6), (key404, -6), (key404, -6), (key314, 2), (key433, 2), (key433, 2), (key246, 2), (key433, 2), (key433, 2), (key246, 2), (key246, 2), (key314, 2), (key314, 2), (key433, 2), (key433, 2)]

theorem rawRowCheck8646 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form10 = rawRow8646 := by decide +kernel

def row8646 : Integer.Sparse Key := [(key234, -6), (key246, 6), (key314, 6), (key404, -18), (key433, 12)]

theorem rowCheck8646 : row8646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8646 := by decide +kernel

theorem rowEval8646 (x : Key → ℝ) : Integer.Sparse.eval row8646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8646, Integer.Sparse.eval_collectBalanced, rawRowCheck8646]

def rawRow8647 : Integer.Sparse Key := [(key404, -6), (key404, -6), (key234, -6), (key404, -6), (key433, 2), (key314, 2), (key433, 2), (key433, 2), (key246, 2), (key433, 2), (key314, 2), (key433, 2), (key246, 2), (key433, 2), (key246, 2), (key314, 2)]

theorem rawRowCheck8647 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form10 = rawRow8647 := by decide +kernel

def row8647 : Integer.Sparse Key := [(key234, -6), (key246, 6), (key314, 6), (key404, -18), (key433, 12)]

theorem rowCheck8647 : row8647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8647 := by decide +kernel

theorem rowEval8647 (x : Key → ℝ) : Integer.Sparse.eval row8647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8647, Integer.Sparse.eval_collectBalanced, rawRowCheck8647]

def rawRow8648 : Integer.Sparse Key := [(key404, -6), (key404, -6), (key404, -6), (key234, -6), (key433, 2), (key433, 2), (key314, 2), (key433, 2), (key433, 2), (key246, 2), (key433, 2), (key314, 2), (key433, 2), (key246, 2), (key314, 2), (key246, 2)]

theorem rawRowCheck8648 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form10 = rawRow8648 := by decide +kernel

def row8648 : Integer.Sparse Key := [(key234, -6), (key246, 6), (key314, 6), (key404, -18), (key433, 12)]

theorem rowCheck8648 : row8648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8648 := by decide +kernel

theorem rowEval8648 (x : Key → ℝ) : Integer.Sparse.eval row8648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck8648, Integer.Sparse.eval_collectBalanced, rawRowCheck8648]

def rawRow8649 : Integer.Sparse Key := [(key246, -6), (key314, -6), (key433, -6), (key433, -6), (key234, 2), (key246, 2), (key246, 2), (key300, 2), (key314, 2), (key314, 2), (key383, 2), (key383, 2), (key404, 2), (key404, 2), (key433, 2), (key433, 2)]

theorem rawRowCheck8649 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form10 = rawRow8649 := by decide +kernel

def row8649 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

theorem rowCheck8649 : row8649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8649 := by decide +kernel

theorem rowEval8649 (x : Key → ℝ) : Integer.Sparse.eval row8649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8649, Integer.Sparse.eval_collectBalanced, rawRowCheck8649]

def rawRow8650 : Integer.Sparse Key := [(key246, -6), (key433, -6), (key314, -6), (key433, -6), (key246, 2), (key234, 2), (key246, 2), (key314, 2), (key300, 2), (key314, 2), (key404, 2), (key433, 2), (key383, 2), (key433, 2), (key383, 2), (key404, 2)]

theorem rawRowCheck8650 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form10 = rawRow8650 := by decide +kernel

def row8650 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

theorem rowCheck8650 : row8650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8650 := by decide +kernel

theorem rowEval8650 (x : Key → ℝ) : Integer.Sparse.eval row8650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8650, Integer.Sparse.eval_collectBalanced, rawRowCheck8650]

def rawRow8651 : Integer.Sparse Key := [(key246, -6), (key433, -6), (key433, -6), (key314, -6), (key246, 2), (key246, 2), (key234, 2), (key314, 2), (key314, 2), (key300, 2), (key433, 2), (key404, 2), (key433, 2), (key383, 2), (key404, 2), (key383, 2)]

theorem rawRowCheck8651 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form10 = rawRow8651 := by decide +kernel

def row8651 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

theorem rowCheck8651 : row8651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8651 := by decide +kernel

theorem rowEval8651 (x : Key → ℝ) : Integer.Sparse.eval row8651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck8651, Integer.Sparse.eval_collectBalanced, rawRowCheck8651]

def rawRow8652 : Integer.Sparse Key := [(key314, -6), (key246, -6), (key433, -6), (key433, -6), (key300, 2), (key314, 2), (key314, 2), (key234, 2), (key404, 2), (key404, 2), (key246, 2), (key246, 2), (key314, 2), (key314, 2), (key433, 2), (key433, 2)]

theorem rawRowCheck8652 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form10 = rawRow8652 := by decide +kernel

def row8652 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, 2), (key404, 4), (key433, -8)]

theorem rowCheck8652 : row8652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8652 := by decide +kernel

theorem rowEval8652 (x : Key → ℝ) : Integer.Sparse.eval row8652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8652, Integer.Sparse.eval_collectBalanced, rawRowCheck8652]

def rawRow8653 : Integer.Sparse Key := [(key314, -6), (key433, -6), (key246, -6), (key433, -6), (key314, 2), (key300, 2), (key314, 2), (key404, 2), (key234, 2), (key404, 2), (key314, 2), (key433, 2), (key246, 2), (key433, 2), (key246, 2), (key314, 2)]

theorem rawRowCheck8653 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form10 = rawRow8653 := by decide +kernel

def row8653 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, 2), (key404, 4), (key433, -8)]

theorem rowCheck8653 : row8653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8653 := by decide +kernel

theorem rowEval8653 (x : Key → ℝ) : Integer.Sparse.eval row8653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8653, Integer.Sparse.eval_collectBalanced, rawRowCheck8653]

def rawRow8654 : Integer.Sparse Key := [(key314, -6), (key433, -6), (key433, -6), (key246, -6), (key314, 2), (key314, 2), (key300, 2), (key404, 2), (key404, 2), (key234, 2), (key433, 2), (key314, 2), (key433, 2), (key246, 2), (key314, 2), (key246, 2)]

theorem rawRowCheck8654 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form10 = rawRow8654 := by decide +kernel

def row8654 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, 2), (key404, 4), (key433, -8)]

theorem rowCheck8654 : row8654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8654 := by decide +kernel

theorem rowEval8654 (x : Key → ℝ) : Integer.Sparse.eval row8654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck8654, Integer.Sparse.eval_collectBalanced, rawRowCheck8654]

def rawRow8655 : Integer.Sparse Key := [(key433, -6), (key246, -6), (key314, -6), (key433, -6), (key383, 2), (key404, 2), (key433, 2), (key246, 2), (key314, 2), (key433, 2), (key234, 2), (key246, 2), (key300, 2), (key314, 2), (key383, 2), (key404, 2)]

theorem rawRowCheck8655 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form10 = rawRow8655 := by decide +kernel

def row8655 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

theorem rowCheck8655 : row8655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8655 := by decide +kernel

theorem rowEval8655 (x : Key → ℝ) : Integer.Sparse.eval row8655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8655, Integer.Sparse.eval_collectBalanced, rawRowCheck8655]

def rawRow8656 : Integer.Sparse Key := [(key433, -6), (key246, -6), (key433, -6), (key314, -6), (key383, 2), (key433, 2), (key404, 2), (key246, 2), (key433, 2), (key314, 2), (key246, 2), (key234, 2), (key314, 2), (key300, 2), (key404, 2), (key383, 2)]

theorem rawRowCheck8656 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form10 = rawRow8656 := by decide +kernel

def row8656 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

theorem rowCheck8656 : row8656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8656 := by decide +kernel

theorem rowEval8656 (x : Key → ℝ) : Integer.Sparse.eval row8656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck8656, Integer.Sparse.eval_collectBalanced, rawRowCheck8656]

def rawRow8657 : Integer.Sparse Key := [(key433, -6), (key314, -6), (key246, -6), (key433, -6), (key404, 2), (key383, 2), (key433, 2), (key314, 2), (key246, 2), (key433, 2), (key300, 2), (key314, 2), (key234, 2), (key404, 2), (key246, 2), (key314, 2)]

theorem rawRowCheck8657 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form10 = rawRow8657 := by decide +kernel

def row8657 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key383, 2), (key404, 4), (key433, -8)]

theorem rowCheck8657 : row8657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8657 := by decide +kernel

theorem rowEval8657 (x : Key → ℝ) : Integer.Sparse.eval row8657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8657, Integer.Sparse.eval_collectBalanced, rawRowCheck8657]

def rawRow8658 : Integer.Sparse Key := [(key433, -6), (key314, -6), (key433, -6), (key246, -6), (key404, 2), (key433, 2), (key383, 2), (key314, 2), (key433, 2), (key246, 2), (key314, 2), (key300, 2), (key404, 2), (key234, 2), (key314, 2), (key246, 2)]

theorem rawRowCheck8658 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form10 = rawRow8658 := by decide +kernel

def row8658 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key383, 2), (key404, 4), (key433, -8)]

theorem rowCheck8658 : row8658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8658 := by decide +kernel

theorem rowEval8658 (x : Key → ℝ) : Integer.Sparse.eval row8658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck8658, Integer.Sparse.eval_collectBalanced, rawRowCheck8658]

def rawRow8659 : Integer.Sparse Key := [(key433, -6), (key433, -6), (key246, -6), (key314, -6), (key433, 2), (key383, 2), (key404, 2), (key433, 2), (key246, 2), (key314, 2), (key383, 2), (key404, 2), (key246, 2), (key314, 2), (key234, 2), (key300, 2)]

theorem rawRowCheck8659 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form10 = rawRow8659 := by decide +kernel

def row8659 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

theorem rowCheck8659 : row8659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8659 := by decide +kernel

theorem rowEval8659 (x : Key → ℝ) : Integer.Sparse.eval row8659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck8659, Integer.Sparse.eval_collectBalanced, rawRowCheck8659]

def rawRow8660 : Integer.Sparse Key := [(key433, -6), (key433, -6), (key314, -6), (key246, -6), (key433, 2), (key404, 2), (key383, 2), (key433, 2), (key314, 2), (key246, 2), (key404, 2), (key383, 2), (key314, 2), (key246, 2), (key300, 2), (key234, 2)]

theorem rawRowCheck8660 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form10 = rawRow8660 := by decide +kernel

def row8660 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

theorem rowCheck8660 : row8660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8660 := by decide +kernel

theorem rowEval8660 (x : Key → ℝ) : Integer.Sparse.eval row8660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck8660, Integer.Sparse.eval_collectBalanced, rawRowCheck8660]

def rawRow8661 : Integer.Sparse Key := [(key2456, 2), (key2456, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2531, 2), (key2456, 2), (key2459, 2), (key2456, 2), (key2531, 2), (key2459, 2), (key2531, 2), (key2517, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2520, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2561, -2)]

theorem rawRowCheck8661 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form0 = rawRow8661 := by decide +kernel

def row8661 : Integer.Sparse Key := [(key2456, 12), (key2459, 6), (key2517, -6), (key2520, -12), (key2531, 6), (key2561, -6)]

theorem rowCheck8661 : row8661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8661 := by decide +kernel

theorem rowEval8661 (x : Key → ℝ) : Integer.Sparse.eval row8661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8661, Integer.Sparse.eval_collectBalanced, rawRowCheck8661]

def rawRow8662 : Integer.Sparse Key := [(key2456, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2531, 2), (key2456, 2), (key2459, 2), (key2456, 2), (key2531, 2), (key2456, 2), (key2531, 2), (key2459, 2), (key2520, -2), (key2517, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2561, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2561, -2), (key2520, -2)]

theorem rawRowCheck8662 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form0 = rawRow8662 := by decide +kernel

def row8662 : Integer.Sparse Key := [(key2456, 12), (key2459, 6), (key2517, -6), (key2520, -12), (key2531, 6), (key2561, -6)]

theorem rowCheck8662 : row8662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8662 := by decide +kernel

theorem rowEval8662 (x : Key → ℝ) : Integer.Sparse.eval row8662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8662, Integer.Sparse.eval_collectBalanced, rawRowCheck8662]

def rawRow8663 : Integer.Sparse Key := [(key2459, 2), (key2456, 2), (key2456, 2), (key2531, 2), (key2456, 2), (key2456, 2), (key2531, 2), (key2531, 2), (key2459, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2520, -2), (key2520, -2), (key2517, -2), (key2561, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2520, -2)]

theorem rawRowCheck8663 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form0 = rawRow8663 := by decide +kernel

def row8663 : Integer.Sparse Key := [(key2456, 12), (key2459, 6), (key2517, -6), (key2520, -12), (key2531, 6), (key2561, -6)]

theorem rowCheck8663 : row8663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8663 := by decide +kernel

theorem rowEval8663 (x : Key → ℝ) : Integer.Sparse.eval row8663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8663, Integer.Sparse.eval_collectBalanced, rawRowCheck8663]

def rawRow8664 : Integer.Sparse Key := [(key2531, 2), (key2531, 2), (key2531, 2), (key2459, 2), (key2459, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2456, 2), (key2456, 2), (key2456, 2), (key2456, 2), (key2561, -2), (key2561, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2517, -2), (key2517, -2)]

theorem rawRowCheck8664 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form0 = rawRow8664 := by decide +kernel

def row8664 : Integer.Sparse Key := [(key2456, 12), (key2459, 6), (key2517, -6), (key2520, -12), (key2531, 6), (key2561, -6)]

theorem rowCheck8664 : row8664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8664 := by decide +kernel

theorem rowEval8664 (x : Key → ℝ) : Integer.Sparse.eval row8664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8664, Integer.Sparse.eval_collectBalanced, rawRowCheck8664]

def rawRow8665 : Integer.Sparse Key := [(key2364, 2), (key2364, 2), (key2364, 2), (key2459, 2), (key2459, 2), (key2459, 2), (key2520, 2), (key2520, 2), (key2520, 2), (key2520, 2), (key2520, 2), (key2520, 2), (key2361, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2517, -2)]

theorem rawRowCheck8665 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form0 = rawRow8665 := by decide +kernel

def row8665 : Integer.Sparse Key := [(key2361, -6), (key2364, 6), (key2456, -12), (key2459, 6), (key2517, -6), (key2520, 12)]

theorem rowCheck8665 : row8665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8665 := by decide +kernel

theorem rowEval8665 (x : Key → ℝ) : Integer.Sparse.eval row8665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8665, Integer.Sparse.eval_collectBalanced, rawRowCheck8665]

def rawRow8666 : Integer.Sparse Key := [(key2459, 2), (key2520, 2), (key2520, 2), (key2364, 2), (key2520, 2), (key2520, 2), (key2364, 2), (key2364, 2), (key2459, 2), (key2459, 2), (key2520, 2), (key2520, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, -2)]

theorem rawRowCheck8666 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form0 = rawRow8666 := by decide +kernel

def row8666 : Integer.Sparse Key := [(key2361, -6), (key2364, 6), (key2456, -12), (key2459, 6), (key2517, -6), (key2520, 12)]

theorem rowCheck8666 : row8666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8666 := by decide +kernel

theorem rowEval8666 (x : Key → ℝ) : Integer.Sparse.eval row8666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8666, Integer.Sparse.eval_collectBalanced, rawRowCheck8666]

def rawRow8667 : Integer.Sparse Key := [(key2520, 2), (key2459, 2), (key2520, 2), (key2520, 2), (key2364, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2364, 2), (key2520, 2), (key2364, 2), (key2459, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2361, -2), (key2456, -2)]

theorem rawRowCheck8667 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form0 = rawRow8667 := by decide +kernel

def row8667 : Integer.Sparse Key := [(key2361, -6), (key2364, 6), (key2456, -12), (key2459, 6), (key2517, -6), (key2520, 12)]

theorem rowCheck8667 : row8667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8667 := by decide +kernel

theorem rowEval8667 (x : Key → ℝ) : Integer.Sparse.eval row8667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8667, Integer.Sparse.eval_collectBalanced, rawRowCheck8667]

def rawRow8668 : Integer.Sparse Key := [(key2520, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2520, 2), (key2364, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2364, 2), (key2459, 2), (key2364, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2361, -2)]

theorem rawRowCheck8668 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form0 = rawRow8668 := by decide +kernel

def row8668 : Integer.Sparse Key := [(key2361, -6), (key2364, 6), (key2456, -12), (key2459, 6), (key2517, -6), (key2520, 12)]

theorem rowCheck8668 : row8668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8668 := by decide +kernel

theorem rowEval8668 (x : Key → ℝ) : Integer.Sparse.eval row8668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck8668, Integer.Sparse.eval_collectBalanced, rawRowCheck8668]

def rawRow8669 : Integer.Sparse Key := [(key969, -24), (key1083, 6), (key1083, 6), (key1083, 6), (key1177, 6)]

theorem rawRowCheck8669 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form1 = rawRow8669 := by decide +kernel

def row8669 : Integer.Sparse Key := [(key969, -24), (key1083, 18), (key1177, 6)]

theorem rowCheck8669 : row8669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8669 := by decide +kernel

theorem rowEval8669 (x : Key → ℝ) : Integer.Sparse.eval row8669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8669, Integer.Sparse.eval_collectBalanced, rawRowCheck8669]

def rawRow8670 : Integer.Sparse Key := [(key969, -24), (key1083, 6), (key1083, 6), (key1177, 6), (key1083, 6)]

theorem rawRowCheck8670 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form1 = rawRow8670 := by decide +kernel

def row8670 : Integer.Sparse Key := [(key969, -24), (key1083, 18), (key1177, 6)]

theorem rowCheck8670 : row8670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8670 := by decide +kernel

theorem rowEval8670 (x : Key → ℝ) : Integer.Sparse.eval row8670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8670, Integer.Sparse.eval_collectBalanced, rawRowCheck8670]

def rawRow8671 : Integer.Sparse Key := [(key969, -24), (key1083, 6), (key1177, 6), (key1083, 6), (key1083, 6)]

theorem rawRowCheck8671 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form1 = rawRow8671 := by decide +kernel

def row8671 : Integer.Sparse Key := [(key969, -24), (key1083, 18), (key1177, 6)]

theorem rowCheck8671 : row8671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8671 := by decide +kernel

theorem rowEval8671 (x : Key → ℝ) : Integer.Sparse.eval row8671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8671, Integer.Sparse.eval_collectBalanced, rawRowCheck8671]

def rawRow8672 : Integer.Sparse Key := [(key969, -24), (key1177, 6), (key1083, 6), (key1083, 6), (key1083, 6)]

theorem rawRowCheck8672 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form1 = rawRow8672 := by decide +kernel

def row8672 : Integer.Sparse Key := [(key969, -24), (key1083, 18), (key1177, 6)]

theorem rowCheck8672 : row8672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8672 := by decide +kernel

theorem rowEval8672 (x : Key → ℝ) : Integer.Sparse.eval row8672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8672, Integer.Sparse.eval_collectBalanced, rawRowCheck8672]

def rawRow8673 : Integer.Sparse Key := [(key1177, -24), (key969, 6), (key1083, 6), (key1083, 6), (key1083, 6)]

theorem rawRowCheck8673 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form1 = rawRow8673 := by decide +kernel

def row8673 : Integer.Sparse Key := [(key969, 6), (key1083, 18), (key1177, -24)]

theorem rowCheck8673 : row8673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8673 := by decide +kernel

theorem rowEval8673 (x : Key → ℝ) : Integer.Sparse.eval row8673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8673, Integer.Sparse.eval_collectBalanced, rawRowCheck8673]

def rawRow8674 : Integer.Sparse Key := [(key1177, -24), (key1083, 6), (key969, 6), (key1083, 6), (key1083, 6)]

theorem rawRowCheck8674 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form1 = rawRow8674 := by decide +kernel

def row8674 : Integer.Sparse Key := [(key969, 6), (key1083, 18), (key1177, -24)]

theorem rowCheck8674 : row8674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8674 := by decide +kernel

theorem rowEval8674 (x : Key → ℝ) : Integer.Sparse.eval row8674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8674, Integer.Sparse.eval_collectBalanced, rawRowCheck8674]

def rawRow8675 : Integer.Sparse Key := [(key1177, -24), (key1083, 6), (key1083, 6), (key969, 6), (key1083, 6)]

theorem rawRowCheck8675 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form1 = rawRow8675 := by decide +kernel

def row8675 : Integer.Sparse Key := [(key969, 6), (key1083, 18), (key1177, -24)]

theorem rowCheck8675 : row8675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8675 := by decide +kernel

theorem rowEval8675 (x : Key → ℝ) : Integer.Sparse.eval row8675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8675, Integer.Sparse.eval_collectBalanced, rawRowCheck8675]

def rawRow8676 : Integer.Sparse Key := [(key1177, -24), (key1083, 6), (key1083, 6), (key1083, 6), (key969, 6)]

theorem rawRowCheck8676 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form1 = rawRow8676 := by decide +kernel

def row8676 : Integer.Sparse Key := [(key969, 6), (key1083, 18), (key1177, -24)]

theorem rowCheck8676 : row8676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8676 := by decide +kernel

theorem rowEval8676 (x : Key → ℝ) : Integer.Sparse.eval row8676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck8676, Integer.Sparse.eval_collectBalanced, rawRowCheck8676]

def rawRow8677 : Integer.Sparse Key := [(key972, -6), (key977, -6), (key977, -6), (key977, -6), (key1086, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1181, 2)]

theorem rawRowCheck8677 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form2 = rawRow8677 := by decide +kernel

def row8677 : Integer.Sparse Key := [(key972, -6), (key977, -18), (key1086, 6), (key1091, 12), (key1181, 6)]

theorem rowCheck8677 : row8677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8677 := by decide +kernel

theorem rowEval8677 (x : Key → ℝ) : Integer.Sparse.eval row8677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8677, Integer.Sparse.eval_collectBalanced, rawRowCheck8677]

def rawRow8678 : Integer.Sparse Key := [(key977, -6), (key972, -6), (key977, -6), (key977, -6), (key1091, 2), (key1086, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1181, 2), (key1091, 2)]

theorem rawRowCheck8678 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form2 = rawRow8678 := by decide +kernel

def row8678 : Integer.Sparse Key := [(key972, -6), (key977, -18), (key1086, 6), (key1091, 12), (key1181, 6)]

theorem rowCheck8678 : row8678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8678 := by decide +kernel

theorem rowEval8678 (x : Key → ℝ) : Integer.Sparse.eval row8678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8678, Integer.Sparse.eval_collectBalanced, rawRowCheck8678]

def rawRow8679 : Integer.Sparse Key := [(key977, -6), (key977, -6), (key972, -6), (key977, -6), (key1091, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1091, 2)]

theorem rawRowCheck8679 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form2 = rawRow8679 := by decide +kernel

def row8679 : Integer.Sparse Key := [(key972, -6), (key977, -18), (key1086, 6), (key1091, 12), (key1181, 6)]

theorem rowCheck8679 : row8679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8679 := by decide +kernel

theorem rowEval8679 (x : Key → ℝ) : Integer.Sparse.eval row8679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8679, Integer.Sparse.eval_collectBalanced, rawRowCheck8679]

def rawRow8680 : Integer.Sparse Key := [(key977, -6), (key977, -6), (key977, -6), (key972, -6), (key1181, 2), (key1181, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1086, 2), (key1086, 2)]

theorem rawRowCheck8680 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form2 = rawRow8680 := by decide +kernel

def row8680 : Integer.Sparse Key := [(key972, -6), (key977, -18), (key1086, 6), (key1091, 12), (key1181, 6)]

theorem rowCheck8680 : row8680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8680 := by decide +kernel

theorem rowEval8680 (x : Key → ℝ) : Integer.Sparse.eval row8680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8680, Integer.Sparse.eval_collectBalanced, rawRowCheck8680]

def rawRow8681 : Integer.Sparse Key := [(key1181, -6), (key1181, -6), (key1181, -6), (key1218, -6), (key977, 2), (key977, 2), (key977, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key1162, 2), (key1162, 2)]

theorem rawRowCheck8681 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form2 = rawRow8681 := by decide +kernel

def row8681 : Integer.Sparse Key := [(key977, 6), (key1091, 12), (key1162, 6), (key1181, -18), (key1218, -6)]

theorem rowCheck8681 : row8681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8681 := by decide +kernel

theorem rowEval8681 (x : Key → ℝ) : Integer.Sparse.eval row8681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8681, Integer.Sparse.eval_collectBalanced, rawRowCheck8681]

def rawRow8682 : Integer.Sparse Key := [(key1181, -6), (key1181, -6), (key1218, -6), (key1181, -6), (key1091, 2), (key1091, 2), (key1162, 2), (key977, 2), (key977, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key1162, 2), (key977, 2), (key1091, 2), (key1091, 2)]

theorem rawRowCheck8682 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form2 = rawRow8682 := by decide +kernel

def row8682 : Integer.Sparse Key := [(key977, 6), (key1091, 12), (key1162, 6), (key1181, -18), (key1218, -6)]

theorem rowCheck8682 : row8682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8682 := by decide +kernel

theorem rowEval8682 (x : Key → ℝ) : Integer.Sparse.eval row8682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8682, Integer.Sparse.eval_collectBalanced, rawRowCheck8682]

def rawRow8683 : Integer.Sparse Key := [(key1181, -6), (key1218, -6), (key1181, -6), (key1181, -6), (key1091, 2), (key1162, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key977, 2), (key1162, 2), (key977, 2), (key1091, 2), (key1091, 2), (key977, 2), (key1091, 2)]

theorem rawRowCheck8683 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form2 = rawRow8683 := by decide +kernel

def row8683 : Integer.Sparse Key := [(key977, 6), (key1091, 12), (key1162, 6), (key1181, -18), (key1218, -6)]

theorem rowCheck8683 : row8683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8683 := by decide +kernel

theorem rowEval8683 (x : Key → ℝ) : Integer.Sparse.eval row8683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8683, Integer.Sparse.eval_collectBalanced, rawRowCheck8683]

def rawRow8684 : Integer.Sparse Key := [(key1218, -6), (key1181, -6), (key1181, -6), (key1181, -6), (key1162, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key1091, 2), (key1162, 2), (key977, 2), (key1091, 2), (key977, 2), (key1091, 2), (key1091, 2), (key977, 2)]

theorem rawRowCheck8684 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form2 = rawRow8684 := by decide +kernel

def row8684 : Integer.Sparse Key := [(key977, 6), (key1091, 12), (key1162, 6), (key1181, -18), (key1218, -6)]

theorem rowCheck8684 : row8684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8684 := by decide +kernel

theorem rowEval8684 (x : Key → ℝ) : Integer.Sparse.eval row8684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck8684, Integer.Sparse.eval_collectBalanced, rawRowCheck8684]

def rawRow8685 : Integer.Sparse Key := [(key2397, -6), (key2397, -6), (key2397, -6), (key2431, -6), (key2463, 2), (key2463, 2), (key2474, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2474, 2), (key2463, 2), (key2497, 2), (key2474, 2), (key2497, 2)]

theorem rawRowCheck8685 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form3 = rawRow8685 := by decide +kernel

def row8685 : Integer.Sparse Key := [(key2397, -18), (key2431, -6), (key2463, 12), (key2474, 6), (key2497, 6)]

theorem rowCheck8685 : row8685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8685 := by decide +kernel

theorem rowEval8685 (x : Key → ℝ) : Integer.Sparse.eval row8685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8685, Integer.Sparse.eval_collectBalanced, rawRowCheck8685]

def rawRow8686 : Integer.Sparse Key := [(key2397, -6), (key2397, -6), (key2431, -6), (key2397, -6), (key2463, 2), (key2474, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2474, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2497, 2), (key2474, 2)]

theorem rawRowCheck8686 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form3 = rawRow8686 := by decide +kernel

def row8686 : Integer.Sparse Key := [(key2397, -18), (key2431, -6), (key2463, 12), (key2474, 6), (key2497, 6)]

theorem rowCheck8686 : row8686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8686 := by decide +kernel

theorem rowEval8686 (x : Key → ℝ) : Integer.Sparse.eval row8686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8686, Integer.Sparse.eval_collectBalanced, rawRowCheck8686]

def rawRow8687 : Integer.Sparse Key := [(key2397, -6), (key2431, -6), (key2397, -6), (key2397, -6), (key2474, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2497, 2), (key2474, 2), (key2474, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck8687 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form3 = rawRow8687 := by decide +kernel

def row8687 : Integer.Sparse Key := [(key2397, -18), (key2431, -6), (key2463, 12), (key2474, 6), (key2497, 6)]

theorem rowCheck8687 : row8687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8687 := by decide +kernel

theorem rowEval8687 (x : Key → ℝ) : Integer.Sparse.eval row8687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8687, Integer.Sparse.eval_collectBalanced, rawRowCheck8687]

def rawRow8688 : Integer.Sparse Key := [(key2431, -6), (key2397, -6), (key2397, -6), (key2397, -6), (key2497, 2), (key2497, 2), (key2497, 2), (key2474, 2), (key2474, 2), (key2474, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck8688 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form3 = rawRow8688 := by decide +kernel

def row8688 : Integer.Sparse Key := [(key2397, -18), (key2431, -6), (key2463, 12), (key2474, 6), (key2497, 6)]

theorem rowCheck8688 : row8688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8688 := by decide +kernel

theorem rowEval8688 (x : Key → ℝ) : Integer.Sparse.eval row8688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8688, Integer.Sparse.eval_collectBalanced, rawRowCheck8688]

def rawRow8689 : Integer.Sparse Key := [(key2384, -6), (key2474, -6), (key2474, -6), (key2474, -6), (key2369, 2), (key2369, 2), (key2369, 2), (key2397, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck8689 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form3 = rawRow8689 := by decide +kernel

def row8689 : Integer.Sparse Key := [(key2369, 6), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, -18)]

theorem rowCheck8689 : row8689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8689 := by decide +kernel

theorem rowEval8689 (x : Key → ℝ) : Integer.Sparse.eval row8689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8689, Integer.Sparse.eval_collectBalanced, rawRowCheck8689]

def rawRow8690 : Integer.Sparse Key := [(key2474, -6), (key2384, -6), (key2474, -6), (key2474, -6), (key2397, 2), (key2463, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2463, 2), (key2369, 2), (key2369, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck8690 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form3 = rawRow8690 := by decide +kernel

def row8690 : Integer.Sparse Key := [(key2369, 6), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, -18)]

theorem rowCheck8690 : row8690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8690 := by decide +kernel

theorem rowEval8690 (x : Key → ℝ) : Integer.Sparse.eval row8690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8690, Integer.Sparse.eval_collectBalanced, rawRowCheck8690]

def rawRow8691 : Integer.Sparse Key := [(key2474, -6), (key2474, -6), (key2384, -6), (key2474, -6), (key2463, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2397, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2369, 2), (key2397, 2)]

theorem rawRowCheck8691 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form3 = rawRow8691 := by decide +kernel

def row8691 : Integer.Sparse Key := [(key2369, 6), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, -18)]

theorem rowCheck8691 : row8691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8691 := by decide +kernel

theorem rowEval8691 (x : Key → ℝ) : Integer.Sparse.eval row8691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8691, Integer.Sparse.eval_collectBalanced, rawRowCheck8691]

def rawRow8692 : Integer.Sparse Key := [(key2474, -6), (key2474, -6), (key2474, -6), (key2384, -6), (key2463, 2), (key2463, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2397, 2), (key2463, 2), (key2369, 2), (key2397, 2), (key2369, 2)]

theorem rawRowCheck8692 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form3 = rawRow8692 := by decide +kernel

def row8692 : Integer.Sparse Key := [(key2369, 6), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, -18)]

theorem rowCheck8692 : row8692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8692 := by decide +kernel

theorem rowEval8692 (x : Key → ℝ) : Integer.Sparse.eval row8692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck8692, Integer.Sparse.eval_collectBalanced, rawRowCheck8692]

def rawRow8693 : Integer.Sparse Key := [(key2354, -6), (key2358, -6), (key2358, -6), (key2358, -6), (key2449, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2529, 2)]

theorem rawRowCheck8693 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form4 = rawRow8693 := by decide +kernel

def row8693 : Integer.Sparse Key := [(key2354, -6), (key2358, -18), (key2449, 6), (key2453, 12), (key2529, 6)]

theorem rowCheck8693 : row8693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8693 := by decide +kernel

theorem rowEval8693 (x : Key → ℝ) : Integer.Sparse.eval row8693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8693, Integer.Sparse.eval_collectBalanced, rawRowCheck8693]

def rawRow8694 : Integer.Sparse Key := [(key2358, -6), (key2354, -6), (key2358, -6), (key2358, -6), (key2453, 2), (key2449, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2529, 2), (key2453, 2)]

theorem rawRowCheck8694 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form4 = rawRow8694 := by decide +kernel

def row8694 : Integer.Sparse Key := [(key2354, -6), (key2358, -18), (key2449, 6), (key2453, 12), (key2529, 6)]

theorem rowCheck8694 : row8694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8694 := by decide +kernel

theorem rowEval8694 (x : Key → ℝ) : Integer.Sparse.eval row8694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8694, Integer.Sparse.eval_collectBalanced, rawRowCheck8694]

def rawRow8695 : Integer.Sparse Key := [(key2358, -6), (key2358, -6), (key2354, -6), (key2358, -6), (key2453, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2453, 2)]

theorem rawRowCheck8695 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form4 = rawRow8695 := by decide +kernel

def row8695 : Integer.Sparse Key := [(key2354, -6), (key2358, -18), (key2449, 6), (key2453, 12), (key2529, 6)]

theorem rowCheck8695 : row8695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8695 := by decide +kernel

theorem rowEval8695 (x : Key → ℝ) : Integer.Sparse.eval row8695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8695, Integer.Sparse.eval_collectBalanced, rawRowCheck8695]

def rawRow8696 : Integer.Sparse Key := [(key2358, -6), (key2358, -6), (key2358, -6), (key2354, -6), (key2529, 2), (key2529, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2449, 2), (key2449, 2)]

theorem rawRowCheck8696 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form4 = rawRow8696 := by decide +kernel

def row8696 : Integer.Sparse Key := [(key2354, -6), (key2358, -18), (key2449, 6), (key2453, 12), (key2529, 6)]

theorem rowCheck8696 : row8696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8696 := by decide +kernel

theorem rowEval8696 (x : Key → ℝ) : Integer.Sparse.eval row8696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8696, Integer.Sparse.eval_collectBalanced, rawRowCheck8696]

def rawRow8697 : Integer.Sparse Key := [(key2529, -6), (key2529, -6), (key2529, -6), (key2559, -6), (key2358, 2), (key2358, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2514, 2), (key2514, 2)]

theorem rawRowCheck8697 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form4 = rawRow8697 := by decide +kernel

def row8697 : Integer.Sparse Key := [(key2358, 6), (key2453, 12), (key2514, 6), (key2529, -18), (key2559, -6)]

theorem rowCheck8697 : row8697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8697 := by decide +kernel

theorem rowEval8697 (x : Key → ℝ) : Integer.Sparse.eval row8697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8697, Integer.Sparse.eval_collectBalanced, rawRowCheck8697]

def rawRow8698 : Integer.Sparse Key := [(key2529, -6), (key2529, -6), (key2559, -6), (key2529, -6), (key2453, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2453, 2)]

theorem rawRowCheck8698 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form4 = rawRow8698 := by decide +kernel

def row8698 : Integer.Sparse Key := [(key2358, 6), (key2453, 12), (key2514, 6), (key2529, -18), (key2559, -6)]

theorem rowCheck8698 : row8698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8698 := by decide +kernel

theorem rowEval8698 (x : Key → ℝ) : Integer.Sparse.eval row8698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8698, Integer.Sparse.eval_collectBalanced, rawRowCheck8698]

def rawRow8699 : Integer.Sparse Key := [(key2529, -6), (key2559, -6), (key2529, -6), (key2529, -6), (key2453, 2), (key2514, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2358, 2), (key2453, 2)]

theorem rawRowCheck8699 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form4 = rawRow8699 := by decide +kernel

def row8699 : Integer.Sparse Key := [(key2358, 6), (key2453, 12), (key2514, 6), (key2529, -18), (key2559, -6)]

theorem rowCheck8699 : row8699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8699 := by decide +kernel

theorem rowEval8699 (x : Key → ℝ) : Integer.Sparse.eval row8699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8699, Integer.Sparse.eval_collectBalanced, rawRowCheck8699]

def rawRow8700 : Integer.Sparse Key := [(key2559, -6), (key2529, -6), (key2529, -6), (key2529, -6), (key2514, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2358, 2)]

theorem rawRowCheck8700 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form4 = rawRow8700 := by decide +kernel

def row8700 : Integer.Sparse Key := [(key2358, 6), (key2453, 12), (key2514, 6), (key2529, -18), (key2559, -6)]

theorem rowCheck8700 : row8700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8700 := by decide +kernel

theorem rowEval8700 (x : Key → ℝ) : Integer.Sparse.eval row8700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck8700, Integer.Sparse.eval_collectBalanced, rawRowCheck8700]

def rawRow8701 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2767, -2), (key2763, -2), (key2767, -2), (key2763, -2), (key2930, -2), (key2767, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2930, -2), (key2840, 1), (key2844, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2888, 1), (key2840, 1), (key2844, 1), (key2840, 1), (key2967, 1), (key2844, 1), (key2967, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2967, 1), (key2844, 1), (key2888, 1), (key2844, 1), (key2967, 1), (key2888, 1), (key2967, 1)]

theorem rawRowCheck8701 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form5 = rawRow8701 := by decide +kernel

def row8701 : Integer.Sparse Key := [(key2763, -6), (key2767, -12), (key2840, 6), (key2844, 6), (key2888, 6), (key2930, -6), (key2967, 6)]

theorem rowCheck8701 : row8701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8701 := by decide +kernel

theorem rowEval8701 (x : Key → ℝ) : Integer.Sparse.eval row8701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8701, Integer.Sparse.eval_collectBalanced, rawRowCheck8701]

def rawRow8702 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2767, -2), (key2767, -2), (key2763, -2), (key2930, -2), (key2763, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2930, -2), (key2767, -2), (key2844, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2844, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2967, 1), (key2844, 1), (key2967, 1), (key2888, 1)]

theorem rawRowCheck8702 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form5 = rawRow8702 := by decide +kernel

def row8702 : Integer.Sparse Key := [(key2763, -6), (key2767, -12), (key2840, 6), (key2844, 6), (key2888, 6), (key2930, -6), (key2967, 6)]

theorem rowCheck8702 : row8702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8702 := by decide +kernel

theorem rowEval8702 (x : Key → ℝ) : Integer.Sparse.eval row8702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8702, Integer.Sparse.eval_collectBalanced, rawRowCheck8702]

def rawRow8703 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2763, -2), (key2930, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2763, -2), (key2763, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1)]

theorem rawRowCheck8703 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form5 = rawRow8703 := by decide +kernel

def row8703 : Integer.Sparse Key := [(key2763, -6), (key2767, -12), (key2840, 6), (key2844, 6), (key2888, 6), (key2930, -6), (key2967, 6)]

theorem rowCheck8703 : row8703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8703 := by decide +kernel

theorem rowEval8703 (x : Key → ℝ) : Integer.Sparse.eval row8703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8703, Integer.Sparse.eval_collectBalanced, rawRowCheck8703]

end MUB6.Certificate.GramRows

end OAI
