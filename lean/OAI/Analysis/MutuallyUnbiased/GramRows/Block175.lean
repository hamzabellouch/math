import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
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

def rawRow19328 : Integer.Sparse Key := [(key1058, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1050, 6), (key1136, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1058, 6)]

theorem rawRowCheck19328 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form4 = rawRow19328 := by decide +kernel

def row19328 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

theorem rowCheck19328 : row19328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19328 := by decide +kernel

theorem rowEval19328 (x : Key → ℝ) : Integer.Sparse.eval row19328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19328, Integer.Sparse.eval_collectBalanced, rawRowCheck19328]

def rawRow19329 : Integer.Sparse Key := [(key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1138, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1136, 6), (key1050, 6), (key1050, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6)]

theorem rawRowCheck19329 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form4 = rawRow19329 := by decide +kernel

def row19329 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

theorem rowCheck19329 : row19329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19329 := by decide +kernel

theorem rowEval19329 (x : Key → ℝ) : Integer.Sparse.eval row19329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19329, Integer.Sparse.eval_collectBalanced, rawRowCheck19329]

def rawRow19330 : Integer.Sparse Key := [(key1136, 6), (key1138, 6), (key1138, 6), (key1138, 6), (key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1138, 6), (key1050, 6), (key1050, 6), (key1050, 6), (key1136, 6)]

theorem rawRowCheck19330 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form4 = rawRow19330 := by decide +kernel

def row19330 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

theorem rowCheck19330 : row19330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19330 := by decide +kernel

theorem rowEval19330 (x : Key → ℝ) : Integer.Sparse.eval row19330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19330, Integer.Sparse.eval_collectBalanced, rawRowCheck19330]

def rawRow19331 : Integer.Sparse Key := [(key1138, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1138, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1136, 6), (key1050, 6)]

theorem rawRowCheck19331 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form4 = rawRow19331 := by decide +kernel

def row19331 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

theorem rowCheck19331 : row19331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19331 := by decide +kernel

theorem rowEval19331 (x : Key → ℝ) : Integer.Sparse.eval row19331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19331, Integer.Sparse.eval_collectBalanced, rawRowCheck19331]

def rawRow19332 : Integer.Sparse Key := [(key1138, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1136, 6), (key1050, 6), (key1050, 6)]

theorem rawRowCheck19332 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form4 = rawRow19332 := by decide +kernel

def row19332 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

theorem rowCheck19332 : row19332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19332 := by decide +kernel

theorem rowEval19332 (x : Key → ℝ) : Integer.Sparse.eval row19332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19332, Integer.Sparse.eval_collectBalanced, rawRowCheck19332]

def rawRow19333 : Integer.Sparse Key := [(key1138, 6), (key1138, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1058, 6), (key1058, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1050, 6), (key1136, 6), (key1050, 6), (key1050, 6), (key1050, 6)]

theorem rawRowCheck19333 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form4 = rawRow19333 := by decide +kernel

def row19333 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

theorem rowCheck19333 : row19333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19333 := by decide +kernel

theorem rowEval19333 (x : Key → ℝ) : Integer.Sparse.eval row19333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19333, Integer.Sparse.eval_collectBalanced, rawRowCheck19333]

def rawRow19334 : Integer.Sparse Key := [(key2420, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2438, 4), (key2420, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2438, 4), (key2504, 4), (key2504, 4)]

theorem rawRowCheck19334 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form5 = rawRow19334 := by decide +kernel

def row19334 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

theorem rowCheck19334 : row19334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19334 := by decide +kernel

theorem rowEval19334 (x : Key → ℝ) : Integer.Sparse.eval row19334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19334, Integer.Sparse.eval_collectBalanced, rawRowCheck19334]

def rawRow19335 : Integer.Sparse Key := [(key2427, 4), (key2420, 4), (key2427, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2427, 4), (key2495, 4), (key2420, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2495, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2495, 4), (key2504, 4), (key2438, 4), (key2504, 4)]

theorem rawRowCheck19335 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form5 = rawRow19335 := by decide +kernel

def row19335 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

theorem rowCheck19335 : row19335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19335 := by decide +kernel

theorem rowEval19335 (x : Key → ℝ) : Integer.Sparse.eval row19335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19335, Integer.Sparse.eval_collectBalanced, rawRowCheck19335]

def rawRow19336 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2420, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2495, 4), (key2420, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2495, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2495, 4), (key2427, 4), (key2504, 4), (key2504, 4), (key2438, 4)]

theorem rawRowCheck19336 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form5 = rawRow19336 := by decide +kernel

def row19336 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

theorem rowCheck19336 : row19336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19336 := by decide +kernel

theorem rowEval19336 (x : Key → ℝ) : Integer.Sparse.eval row19336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19336, Integer.Sparse.eval_collectBalanced, rawRowCheck19336]

def rawRow19337 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2438, 4), (key2420, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2420, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2504, 4), (key2438, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2495, 4)]

theorem rawRowCheck19337 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form5 = rawRow19337 := by decide +kernel

def row19337 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

theorem rowCheck19337 : row19337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19337 := by decide +kernel

theorem rowEval19337 (x : Key → ℝ) : Integer.Sparse.eval row19337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19337, Integer.Sparse.eval_collectBalanced, rawRowCheck19337]

def rawRow19338 : Integer.Sparse Key := [(key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2427, 4), (key2495, 4), (key2504, 4), (key2495, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2420, 4), (key2495, 4), (key2427, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2438, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2504, 4), (key2438, 4), (key2427, 4), (key2495, 4), (key2427, 4)]

theorem rawRowCheck19338 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form5 = rawRow19338 := by decide +kernel

def row19338 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

theorem rowCheck19338 : row19338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19338 := by decide +kernel

theorem rowEval19338 (x : Key → ℝ) : Integer.Sparse.eval row19338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19338, Integer.Sparse.eval_collectBalanced, rawRowCheck19338]

def rawRow19339 : Integer.Sparse Key := [(key2438, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2504, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2420, 4), (key2504, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2438, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2427, 4), (key2427, 4)]

theorem rawRowCheck19339 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form5 = rawRow19339 := by decide +kernel

def row19339 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

theorem rowCheck19339 : row19339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19339 := by decide +kernel

theorem rowEval19339 (x : Key → ℝ) : Integer.Sparse.eval row19339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19339, Integer.Sparse.eval_collectBalanced, rawRowCheck19339]

def rawRow19340 : Integer.Sparse Key := [(key2495, 4), (key2495, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2504, 4), (key2438, 4), (key2504, 4), (key2420, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2427, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2495, 4)]

theorem rawRowCheck19340 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form5 = rawRow19340 := by decide +kernel

def row19340 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

theorem rowCheck19340 : row19340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19340 := by decide +kernel

theorem rowEval19340 (x : Key → ℝ) : Integer.Sparse.eval row19340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19340, Integer.Sparse.eval_collectBalanced, rawRowCheck19340]

def rawRow19341 : Integer.Sparse Key := [(key2495, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2504, 4), (key2438, 4), (key2427, 4), (key2420, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2420, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2427, 4)]

theorem rawRowCheck19341 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form5 = rawRow19341 := by decide +kernel

def row19341 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

theorem rowCheck19341 : row19341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19341 := by decide +kernel

theorem rowEval19341 (x : Key → ℝ) : Integer.Sparse.eval row19341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19341, Integer.Sparse.eval_collectBalanced, rawRowCheck19341]

def rawRow19342 : Integer.Sparse Key := [(key2504, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2495, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2504, 4), (key2438, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2420, 4), (key2495, 4), (key2427, 4), (key2427, 4)]

theorem rawRowCheck19342 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form5 = rawRow19342 := by decide +kernel

def row19342 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

theorem rowCheck19342 : row19342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19342 := by decide +kernel

theorem rowEval19342 (x : Key → ℝ) : Integer.Sparse.eval row19342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19342, Integer.Sparse.eval_collectBalanced, rawRowCheck19342]

def rawRow19343 : Integer.Sparse Key := [(key2504, 4), (key2504, 4), (key2504, 4), (key2495, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2504, 4), (key2438, 4), (key2438, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2420, 4), (key2420, 4)]

theorem rawRowCheck19343 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form5 = rawRow19343 := by decide +kernel

def row19343 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

theorem rowCheck19343 : row19343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19343 := by decide +kernel

theorem rowEval19343 (x : Key → ℝ) : Integer.Sparse.eval row19343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19343, Integer.Sparse.eval_collectBalanced, rawRowCheck19343]

def rawRow19344 : Integer.Sparse Key := [(key2413, 6), (key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2486, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2490, 6), (key2490, 6)]

theorem rawRowCheck19344 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form6 = rawRow19344 := by decide +kernel

def row19344 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

theorem rowCheck19344 : row19344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19344 := by decide +kernel

theorem rowEval19344 (x : Key → ℝ) : Integer.Sparse.eval row19344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19344, Integer.Sparse.eval_collectBalanced, rawRowCheck19344]

def rawRow19345 : Integer.Sparse Key := [(key2413, 6), (key2422, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2486, 6), (key2490, 6), (key2413, 6), (key2490, 6), (key2413, 6), (key2486, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2422, 6), (key2490, 6)]

theorem rawRowCheck19345 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form6 = rawRow19345 := by decide +kernel

def row19345 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

theorem rowCheck19345 : row19345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19345 := by decide +kernel

theorem rowEval19345 (x : Key → ℝ) : Integer.Sparse.eval row19345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19345, Integer.Sparse.eval_collectBalanced, rawRowCheck19345]

def rawRow19346 : Integer.Sparse Key := [(key2422, 6), (key2413, 6), (key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2413, 6), (key2486, 6), (key2413, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2490, 6), (key2490, 6), (key2422, 6)]

theorem rawRowCheck19346 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form6 = rawRow19346 := by decide +kernel

def row19346 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

theorem rowCheck19346 : row19346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19346 := by decide +kernel

theorem rowEval19346 (x : Key → ℝ) : Integer.Sparse.eval row19346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19346, Integer.Sparse.eval_collectBalanced, rawRowCheck19346]

def rawRow19347 : Integer.Sparse Key := [(key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2413, 6), (key2413, 6), (key2486, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2490, 6)]

theorem rawRowCheck19347 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form6 = rawRow19347 := by decide +kernel

def row19347 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

theorem rowCheck19347 : row19347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19347 := by decide +kernel

theorem rowEval19347 (x : Key → ℝ) : Integer.Sparse.eval row19347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19347, Integer.Sparse.eval_collectBalanced, rawRowCheck19347]

def rawRow19348 : Integer.Sparse Key := [(key2422, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2413, 6), (key2486, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2422, 6)]

theorem rawRowCheck19348 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form6 = rawRow19348 := by decide +kernel

def row19348 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

theorem rowCheck19348 : row19348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19348 := by decide +kernel

theorem rowEval19348 (x : Key → ℝ) : Integer.Sparse.eval row19348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19348, Integer.Sparse.eval_collectBalanced, rawRowCheck19348]

def rawRow19349 : Integer.Sparse Key := [(key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2490, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2486, 6), (key2413, 6), (key2413, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6)]

theorem rawRowCheck19349 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form6 = rawRow19349 := by decide +kernel

def row19349 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

theorem rowCheck19349 : row19349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19349 := by decide +kernel

theorem rowEval19349 (x : Key → ℝ) : Integer.Sparse.eval row19349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19349, Integer.Sparse.eval_collectBalanced, rawRowCheck19349]

def rawRow19350 : Integer.Sparse Key := [(key2486, 6), (key2490, 6), (key2490, 6), (key2490, 6), (key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2490, 6), (key2413, 6), (key2413, 6), (key2413, 6), (key2486, 6)]

theorem rawRowCheck19350 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form6 = rawRow19350 := by decide +kernel

def row19350 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

theorem rowCheck19350 : row19350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19350 := by decide +kernel

theorem rowEval19350 (x : Key → ℝ) : Integer.Sparse.eval row19350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19350, Integer.Sparse.eval_collectBalanced, rawRowCheck19350]

def rawRow19351 : Integer.Sparse Key := [(key2490, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2490, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2486, 6), (key2413, 6)]

theorem rawRowCheck19351 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form6 = rawRow19351 := by decide +kernel

def row19351 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

theorem rowCheck19351 : row19351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19351 := by decide +kernel

theorem rowEval19351 (x : Key → ℝ) : Integer.Sparse.eval row19351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19351, Integer.Sparse.eval_collectBalanced, rawRowCheck19351]

def rawRow19352 : Integer.Sparse Key := [(key2490, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2486, 6), (key2413, 6), (key2413, 6)]

theorem rawRowCheck19352 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form6 = rawRow19352 := by decide +kernel

def row19352 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

theorem rowCheck19352 : row19352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19352 := by decide +kernel

theorem rowEval19352 (x : Key → ℝ) : Integer.Sparse.eval row19352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19352, Integer.Sparse.eval_collectBalanced, rawRowCheck19352]

def rawRow19353 : Integer.Sparse Key := [(key2490, 6), (key2490, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2422, 6), (key2422, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2413, 6), (key2486, 6), (key2413, 6), (key2413, 6), (key2413, 6)]

theorem rawRowCheck19353 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form6 = rawRow19353 := by decide +kernel

def row19353 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

theorem rowCheck19353 : row19353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19353 := by decide +kernel

theorem rowEval19353 (x : Key → ℝ) : Integer.Sparse.eval row19353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19353, Integer.Sparse.eval_collectBalanced, rawRowCheck19353]

def rawRow19354 : Integer.Sparse Key := [(key2677, 6), (key2677, 6), (key2708, 6), (key2708, 6), (key2677, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3045, 6), (key3059, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3059, 6), (key3059, 6), (key3094, 6), (key3094, 6), (key3122, 6), (key3122, 6)]

theorem rawRowCheck19354 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form7 = rawRow19354 := by decide +kernel

def row19354 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key3045, 18), (key3059, 24), (key3094, 36), (key3122, 12)]

theorem rowCheck19354 : row19354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19354 := by decide +kernel

theorem rowEval19354 (x : Key → ℝ) : Integer.Sparse.eval row19354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19354, Integer.Sparse.eval_collectBalanced, rawRowCheck19354]

def rawRow19355 : Integer.Sparse Key := [(key2677, 6), (key2708, 6), (key2677, 6), (key2708, 6), (key2677, 6), (key3094, 6), (key3045, 6), (key3094, 6), (key3059, 6), (key3045, 6), (key3059, 6), (key3094, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3122, 6), (key3059, 6), (key3122, 6), (key3059, 6), (key3094, 6)]

theorem rawRowCheck19355 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form7 = rawRow19355 := by decide +kernel

def row19355 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key3045, 18), (key3059, 24), (key3094, 36), (key3122, 12)]

theorem rowCheck19355 : row19355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19355 := by decide +kernel

theorem rowEval19355 (x : Key → ℝ) : Integer.Sparse.eval row19355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19355, Integer.Sparse.eval_collectBalanced, rawRowCheck19355]

def rawRow19356 : Integer.Sparse Key := [(key2677, 6), (key2708, 6), (key2708, 6), (key2677, 6), (key2677, 6), (key3094, 6), (key3094, 6), (key3045, 6), (key3059, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3045, 6), (key3122, 6), (key3094, 6), (key3122, 6), (key3059, 6), (key3094, 6), (key3059, 6)]

theorem rawRowCheck19356 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form7 = rawRow19356 := by decide +kernel

def row19356 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key3045, 18), (key3059, 24), (key3094, 36), (key3122, 12)]

theorem rowCheck19356 : row19356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19356 := by decide +kernel

theorem rowEval19356 (x : Key → ℝ) : Integer.Sparse.eval row19356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19356, Integer.Sparse.eval_collectBalanced, rawRowCheck19356]

def rawRow19357 : Integer.Sparse Key := [(key2708, 6), (key2677, 6), (key2677, 6), (key2708, 6), (key2811, 6), (key2677, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3094, 6), (key3122, 6), (key3059, 6), (key3059, 6), (key3122, 6), (key3045, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3059, 6), (key3094, 6)]

theorem rawRowCheck19357 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form7 = rawRow19357 := by decide +kernel

def row19357 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key2811, 6), (key3045, 18), (key3059, 24), (key3094, 30), (key3122, 12)]

theorem rowCheck19357 : row19357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19357 := by decide +kernel

theorem rowEval19357 (x : Key → ℝ) : Integer.Sparse.eval row19357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19357, Integer.Sparse.eval_collectBalanced, rawRowCheck19357]

def rawRow19358 : Integer.Sparse Key := [(key2708, 6), (key2677, 6), (key2708, 6), (key2677, 6), (key2811, 6), (key2677, 6), (key3094, 6), (key3045, 6), (key3094, 6), (key3122, 6), (key3094, 6), (key3059, 6), (key3122, 6), (key3059, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3045, 6), (key3094, 6), (key3059, 6)]

theorem rawRowCheck19358 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form7 = rawRow19358 := by decide +kernel

def row19358 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key2811, 6), (key3045, 18), (key3059, 24), (key3094, 30), (key3122, 12)]

theorem rowCheck19358 : row19358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19358 := by decide +kernel

theorem rowEval19358 (x : Key → ℝ) : Integer.Sparse.eval row19358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19358, Integer.Sparse.eval_collectBalanced, rawRowCheck19358]

def rawRow19359 : Integer.Sparse Key := [(key2708, 6), (key2708, 6), (key2677, 6), (key2677, 6), (key2811, 6), (key2811, 6), (key2677, 6), (key3045, 6), (key3122, 6), (key3094, 6), (key3094, 6), (key3122, 6), (key3059, 6), (key3059, 6), (key3094, 6), (key3094, 6), (key3059, 6), (key3059, 6), (key3045, 6), (key3045, 6)]

theorem rawRowCheck19359 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form7 = rawRow19359 := by decide +kernel

def row19359 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key2811, 12), (key3045, 18), (key3059, 24), (key3094, 24), (key3122, 12)]

theorem rowCheck19359 : row19359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19359 := by decide +kernel

theorem rowEval19359 (x : Key → ℝ) : Integer.Sparse.eval row19359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19359, Integer.Sparse.eval_collectBalanced, rawRowCheck19359]

def rawRow19360 : Integer.Sparse Key := [(key2811, 6), (key2811, 6), (key2811, 6), (key2861, 6), (key2708, 6), (key2708, 6), (key2708, 6), (key2861, 6), (key2677, 6), (key2677, 6), (key2708, 6), (key2677, 6), (key3045, 6), (key3094, 6), (key3045, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3059, 6), (key3094, 6)]

theorem rawRowCheck19360 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form7 = rawRow19360 := by decide +kernel

def row19360 : Integer.Sparse Key := [(key2677, 18), (key2708, 24), (key2811, 18), (key2861, 12), (key3045, 18), (key3059, 12), (key3094, 18)]

theorem rowCheck19360 : row19360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19360 := by decide +kernel

theorem rowEval19360 (x : Key → ℝ) : Integer.Sparse.eval row19360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19360, Integer.Sparse.eval_collectBalanced, rawRowCheck19360]

def rawRow19361 : Integer.Sparse Key := [(key2811, 6), (key2811, 6), (key2861, 6), (key2811, 6), (key2708, 6), (key2708, 6), (key2861, 6), (key2708, 6), (key2677, 6), (key2708, 6), (key2677, 6), (key2677, 6), (key3094, 6), (key3045, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3045, 6), (key3094, 6), (key3059, 6)]

theorem rawRowCheck19361 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form7 = rawRow19361 := by decide +kernel

def row19361 : Integer.Sparse Key := [(key2677, 18), (key2708, 24), (key2811, 18), (key2861, 12), (key3045, 18), (key3059, 12), (key3094, 18)]

theorem rowCheck19361 : row19361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19361 := by decide +kernel

theorem rowEval19361 (x : Key → ℝ) : Integer.Sparse.eval row19361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19361, Integer.Sparse.eval_collectBalanced, rawRowCheck19361]

def rawRow19362 : Integer.Sparse Key := [(key2811, 6), (key2861, 6), (key2811, 6), (key2811, 6), (key2708, 6), (key2861, 6), (key2708, 6), (key2708, 6), (key2708, 6), (key2677, 6), (key2677, 6), (key2811, 6), (key2677, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3059, 6), (key3059, 6), (key3045, 6), (key3045, 6)]

theorem rawRowCheck19362 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form7 = rawRow19362 := by decide +kernel

def row19362 : Integer.Sparse Key := [(key2677, 18), (key2708, 24), (key2811, 24), (key2861, 12), (key3045, 18), (key3059, 12), (key3094, 12)]

theorem rowCheck19362 : row19362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19362 := by decide +kernel

theorem rowEval19362 (x : Key → ℝ) : Integer.Sparse.eval row19362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19362, Integer.Sparse.eval_collectBalanced, rawRowCheck19362]

def rawRow19363 : Integer.Sparse Key := [(key2861, 6), (key2811, 6), (key2811, 6), (key2811, 6), (key2861, 6), (key2708, 6), (key2708, 6), (key2708, 6), (key2811, 6), (key2811, 6), (key2811, 6), (key2708, 6), (key2708, 6), (key2708, 6), (key2677, 6), (key2677, 6), (key2677, 6), (key3045, 6), (key3045, 6), (key3045, 6)]

theorem rawRowCheck19363 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form7 = rawRow19363 := by decide +kernel

def row19363 : Integer.Sparse Key := [(key2677, 18), (key2708, 36), (key2811, 36), (key2861, 12), (key3045, 18)]

theorem rowCheck19363 : row19363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19363 := by decide +kernel

theorem rowEval19363 (x : Key → ℝ) : Integer.Sparse.eval row19363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19363, Integer.Sparse.eval_collectBalanced, rawRowCheck19363]

def rawRow19364 : Integer.Sparse Key := [(key1962, 24), (key1962, 24), (key1964, 24), (key1964, 24), (key1964, 24)]

theorem rawRowCheck19364 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form8 = rawRow19364 := by decide +kernel

def row19364 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

theorem rowCheck19364 : row19364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19364 := by decide +kernel

theorem rowEval19364 (x : Key → ℝ) : Integer.Sparse.eval row19364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19364, Integer.Sparse.eval_collectBalanced, rawRowCheck19364]

def rawRow19365 : Integer.Sparse Key := [(key1962, 24), (key1964, 24), (key1962, 24), (key1964, 24), (key1964, 24)]

theorem rawRowCheck19365 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form8 = rawRow19365 := by decide +kernel

def row19365 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

theorem rowCheck19365 : row19365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19365 := by decide +kernel

theorem rowEval19365 (x : Key → ℝ) : Integer.Sparse.eval row19365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19365, Integer.Sparse.eval_collectBalanced, rawRowCheck19365]

def rawRow19366 : Integer.Sparse Key := [(key1964, 24), (key1962, 24), (key1962, 24), (key1964, 24), (key1964, 24)]

theorem rawRowCheck19366 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form8 = rawRow19366 := by decide +kernel

def row19366 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

theorem rowCheck19366 : row19366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19366 := by decide +kernel

theorem rowEval19366 (x : Key → ℝ) : Integer.Sparse.eval row19366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19366, Integer.Sparse.eval_collectBalanced, rawRowCheck19366]

def rawRow19367 : Integer.Sparse Key := [(key1962, 24), (key1964, 24), (key1964, 24), (key1962, 24), (key1964, 24)]

theorem rawRowCheck19367 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form8 = rawRow19367 := by decide +kernel

def row19367 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

theorem rowCheck19367 : row19367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19367 := by decide +kernel

theorem rowEval19367 (x : Key → ℝ) : Integer.Sparse.eval row19367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19367, Integer.Sparse.eval_collectBalanced, rawRowCheck19367]

def rawRow19368 : Integer.Sparse Key := [(key1964, 24), (key1962, 24), (key1964, 24), (key1962, 24), (key1964, 24)]

theorem rawRowCheck19368 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form8 = rawRow19368 := by decide +kernel

def row19368 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

theorem rowCheck19368 : row19368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19368 := by decide +kernel

theorem rowEval19368 (x : Key → ℝ) : Integer.Sparse.eval row19368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19368, Integer.Sparse.eval_collectBalanced, rawRowCheck19368]

def rawRow19369 : Integer.Sparse Key := [(key1964, 24), (key1964, 24), (key1962, 24), (key1962, 24), (key1964, 24)]

theorem rawRowCheck19369 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form8 = rawRow19369 := by decide +kernel

def row19369 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

theorem rowCheck19369 : row19369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19369 := by decide +kernel

theorem rowEval19369 (x : Key → ℝ) : Integer.Sparse.eval row19369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19369, Integer.Sparse.eval_collectBalanced, rawRowCheck19369]

def rawRow19370 : Integer.Sparse Key := [(key1962, 24), (key1964, 24), (key1964, 24), (key1964, 24), (key1962, 24)]

theorem rawRowCheck19370 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form8 = rawRow19370 := by decide +kernel

def row19370 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

theorem rowCheck19370 : row19370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19370 := by decide +kernel

theorem rowEval19370 (x : Key → ℝ) : Integer.Sparse.eval row19370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19370, Integer.Sparse.eval_collectBalanced, rawRowCheck19370]

def rawRow19371 : Integer.Sparse Key := [(key1964, 24), (key1962, 24), (key1964, 24), (key1964, 24), (key1962, 24)]

theorem rawRowCheck19371 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form8 = rawRow19371 := by decide +kernel

def row19371 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

theorem rowCheck19371 : row19371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19371 := by decide +kernel

theorem rowEval19371 (x : Key → ℝ) : Integer.Sparse.eval row19371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19371, Integer.Sparse.eval_collectBalanced, rawRowCheck19371]

def rawRow19372 : Integer.Sparse Key := [(key1964, 24), (key1964, 24), (key1962, 24), (key1964, 24), (key1962, 24)]

theorem rawRowCheck19372 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form8 = rawRow19372 := by decide +kernel

def row19372 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

theorem rowCheck19372 : row19372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19372 := by decide +kernel

theorem rowEval19372 (x : Key → ℝ) : Integer.Sparse.eval row19372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19372, Integer.Sparse.eval_collectBalanced, rawRowCheck19372]

def rawRow19373 : Integer.Sparse Key := [(key1964, 24), (key1964, 24), (key1964, 24), (key1962, 24), (key1962, 24)]

theorem rawRowCheck19373 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form8 = rawRow19373 := by decide +kernel

def row19373 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

theorem rowCheck19373 : row19373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19373 := by decide +kernel

theorem rowEval19373 (x : Key → ℝ) : Integer.Sparse.eval row19373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19373, Integer.Sparse.eval_collectBalanced, rawRowCheck19373]

def rawRow19374 : Integer.Sparse Key := [(key3079, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3099, 12)]

theorem rawRowCheck19374 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form9 = rawRow19374 := by decide +kernel

def row19374 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

theorem rowCheck19374 : row19374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19374 := by decide +kernel

theorem rowEval19374 (x : Key → ℝ) : Integer.Sparse.eval row19374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19374, Integer.Sparse.eval_collectBalanced, rawRowCheck19374]

def rawRow19375 : Integer.Sparse Key := [(key3084, 12), (key3079, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3099, 12)]

theorem rawRowCheck19375 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form9 = rawRow19375 := by decide +kernel

def row19375 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

theorem rowCheck19375 : row19375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19375 := by decide +kernel

theorem rowEval19375 (x : Key → ℝ) : Integer.Sparse.eval row19375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19375, Integer.Sparse.eval_collectBalanced, rawRowCheck19375]

def rawRow19376 : Integer.Sparse Key := [(key3084, 12), (key3084, 12), (key3079, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3099, 12)]

theorem rawRowCheck19376 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form9 = rawRow19376 := by decide +kernel

def row19376 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

theorem rowCheck19376 : row19376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19376 := by decide +kernel

theorem rowEval19376 (x : Key → ℝ) : Integer.Sparse.eval row19376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck19376, Integer.Sparse.eval_collectBalanced, rawRowCheck19376]

def rawRow19377 : Integer.Sparse Key := [(key3084, 12), (key3084, 12), (key3099, 12), (key3079, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3099, 12), (key3084, 12)]

theorem rawRowCheck19377 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form9 = rawRow19377 := by decide +kernel

def row19377 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

theorem rowCheck19377 : row19377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19377 := by decide +kernel

theorem rowEval19377 (x : Key → ℝ) : Integer.Sparse.eval row19377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19377, Integer.Sparse.eval_collectBalanced, rawRowCheck19377]

def rawRow19378 : Integer.Sparse Key := [(key3084, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3079, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3099, 12), (key3084, 12)]

theorem rawRowCheck19378 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form9 = rawRow19378 := by decide +kernel

def row19378 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

theorem rowCheck19378 : row19378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19378 := by decide +kernel

theorem rowEval19378 (x : Key → ℝ) : Integer.Sparse.eval row19378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck19378, Integer.Sparse.eval_collectBalanced, rawRowCheck19378]

def rawRow19379 : Integer.Sparse Key := [(key3099, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3079, 12), (key3099, 12), (key3099, 12), (key3084, 12), (key3084, 12)]

theorem rawRowCheck19379 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form9 = rawRow19379 := by decide +kernel

def row19379 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

theorem rowCheck19379 : row19379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19379 := by decide +kernel

theorem rowEval19379 (x : Key → ℝ) : Integer.Sparse.eval row19379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck19379, Integer.Sparse.eval_collectBalanced, rawRowCheck19379]

def rawRow19380 : Integer.Sparse Key := [(key3084, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3099, 12), (key3099, 12), (key3079, 12), (key3084, 12), (key3084, 12), (key3084, 12)]

theorem rawRowCheck19380 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form9 = rawRow19380 := by decide +kernel

def row19380 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

theorem rowCheck19380 : row19380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19380 := by decide +kernel

theorem rowEval19380 (x : Key → ℝ) : Integer.Sparse.eval row19380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19380, Integer.Sparse.eval_collectBalanced, rawRowCheck19380]

def rawRow19381 : Integer.Sparse Key := [(key3084, 12), (key3099, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3079, 12), (key3084, 12), (key3084, 12)]

theorem rawRowCheck19381 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form9 = rawRow19381 := by decide +kernel

def row19381 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

theorem rowCheck19381 : row19381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19381 := by decide +kernel

theorem rowEval19381 (x : Key → ℝ) : Integer.Sparse.eval row19381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck19381, Integer.Sparse.eval_collectBalanced, rawRowCheck19381]

def rawRow19382 : Integer.Sparse Key := [(key3099, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3079, 12), (key3084, 12)]

theorem rawRowCheck19382 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form9 = rawRow19382 := by decide +kernel

def row19382 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

theorem rowCheck19382 : row19382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19382 := by decide +kernel

theorem rowEval19382 (x : Key → ℝ) : Integer.Sparse.eval row19382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck19382, Integer.Sparse.eval_collectBalanced, rawRowCheck19382]

def rawRow19383 : Integer.Sparse Key := [(key3099, 12), (key3099, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3079, 12)]

theorem rawRowCheck19383 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form9 = rawRow19383 := by decide +kernel

def row19383 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

theorem rowCheck19383 : row19383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19383 := by decide +kernel

theorem rowEval19383 (x : Key → ℝ) : Integer.Sparse.eval row19383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck19383, Integer.Sparse.eval_collectBalanced, rawRowCheck19383]

def rawRow19384 : Integer.Sparse Key := [(key1273, 6), (key1278, 6), (key1278, 6), (key1278, 6), (key1696, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1953, 6)]

theorem rawRowCheck19384 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form0 = rawRow19384 := by decide +kernel

def row19384 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19384 : row19384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19384 := by decide +kernel

theorem rowEval19384 (x : Key → ℝ) : Integer.Sparse.eval row19384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19384, Integer.Sparse.eval_collectBalanced, rawRowCheck19384]

def rawRow19385 : Integer.Sparse Key := [(key1278, 6), (key1273, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1696, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1933, 6)]

theorem rawRowCheck19385 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form0 = rawRow19385 := by decide +kernel

def row19385 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19385 : row19385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19385 := by decide +kernel

theorem rowEval19385 (x : Key → ℝ) : Integer.Sparse.eval row19385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19385, Integer.Sparse.eval_collectBalanced, rawRowCheck19385]

def rawRow19386 : Integer.Sparse Key := [(key1278, 6), (key1278, 6), (key1273, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1933, 6)]

theorem rawRowCheck19386 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form0 = rawRow19386 := by decide +kernel

def row19386 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19386 : row19386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19386 := by decide +kernel

theorem rowEval19386 (x : Key → ℝ) : Integer.Sparse.eval row19386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19386, Integer.Sparse.eval_collectBalanced, rawRowCheck19386]

def rawRow19387 : Integer.Sparse Key := [(key1278, 6), (key1278, 6), (key1278, 6), (key1273, 6), (key1751, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1696, 6), (key1696, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6)]

theorem rawRowCheck19387 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19387 := by decide +kernel

def row19387 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19387 : row19387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19387 := by decide +kernel

theorem rowEval19387 (x : Key → ℝ) : Integer.Sparse.eval row19387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19387, Integer.Sparse.eval_collectBalanced, rawRowCheck19387]

def rawRow19388 : Integer.Sparse Key := [(key1696, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1273, 6), (key1278, 6), (key1278, 6), (key1696, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1751, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6)]

theorem rawRowCheck19388 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form0 = rawRow19388 := by decide +kernel

def row19388 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19388 : row19388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19388 := by decide +kernel

theorem rowEval19388 (x : Key → ℝ) : Integer.Sparse.eval row19388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19388, Integer.Sparse.eval_collectBalanced, rawRowCheck19388]

def rawRow19389 : Integer.Sparse Key := [(key1701, 6), (key1696, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1273, 6), (key1278, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6)]

theorem rawRowCheck19389 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form0 = rawRow19389 := by decide +kernel

def row19389 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19389 : row19389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19389 := by decide +kernel

theorem rowEval19389 (x : Key → ℝ) : Integer.Sparse.eval row19389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19389, Integer.Sparse.eval_collectBalanced, rawRowCheck19389]

def rawRow19390 : Integer.Sparse Key := [(key1701, 6), (key1701, 6), (key1696, 6), (key1933, 6), (key1278, 6), (key1278, 6), (key1273, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1696, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6)]

theorem rawRowCheck19390 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form0 = rawRow19390 := by decide +kernel

def row19390 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19390 : row19390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19390 := by decide +kernel

theorem rowEval19390 (x : Key → ℝ) : Integer.Sparse.eval row19390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19390, Integer.Sparse.eval_collectBalanced, rawRowCheck19390]

def rawRow19391 : Integer.Sparse Key := [(key1696, 6), (key1701, 6), (key1933, 6), (key1701, 6), (key1696, 6), (key1701, 6), (key1933, 6), (key1273, 6), (key1278, 6), (key1696, 6), (key1751, 6), (key1933, 6), (key1953, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1751, 6)]

theorem rawRowCheck19391 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form0 = rawRow19391 := by decide +kernel

def row19391 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19391 : row19391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19391 := by decide +kernel

theorem rowEval19391 (x : Key → ℝ) : Integer.Sparse.eval row19391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19391, Integer.Sparse.eval_collectBalanced, rawRowCheck19391]

def rawRow19392 : Integer.Sparse Key := [(key1701, 6), (key1696, 6), (key1933, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1933, 6), (key1278, 6), (key1273, 6), (key1751, 6), (key1696, 6), (key1953, 6), (key1933, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1751, 6), (key1701, 6)]

theorem rawRowCheck19392 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form0 = rawRow19392 := by decide +kernel

def row19392 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19392 : row19392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19392 := by decide +kernel

theorem rowEval19392 (x : Key → ℝ) : Integer.Sparse.eval row19392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19392, Integer.Sparse.eval_collectBalanced, rawRowCheck19392]

def rawRow19393 : Integer.Sparse Key := [(key1696, 6), (key1933, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1933, 6), (key1701, 6), (key1696, 6), (key1933, 6), (key1273, 6), (key1953, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1751, 6)]

theorem rawRowCheck19393 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form0 = rawRow19393 := by decide +kernel

def row19393 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19393 : row19393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19393 := by decide +kernel

theorem rowEval19393 (x : Key → ℝ) : Integer.Sparse.eval row19393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19393, Integer.Sparse.eval_collectBalanced, rawRowCheck19393]

def rawRow19394 : Integer.Sparse Key := [(key1933, 6), (key1696, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1696, 6), (key1701, 6), (key1933, 6), (key1696, 6), (key1953, 6), (key1273, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1278, 6)]

theorem rawRowCheck19394 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form0 = rawRow19394 := by decide +kernel

def row19394 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19394 : row19394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19394 := by decide +kernel

theorem rowEval19394 (x : Key → ℝ) : Integer.Sparse.eval row19394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19394, Integer.Sparse.eval_collectBalanced, rawRowCheck19394]

def rawRow19395 : Integer.Sparse Key := [(key1701, 6), (key1933, 6), (key1696, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1696, 6), (key1751, 6), (key1953, 6), (key1278, 6), (key1933, 6), (key1273, 6), (key1696, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1278, 6), (key1701, 6)]

theorem rawRowCheck19395 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form0 = rawRow19395 := by decide +kernel

def row19395 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19395 : row19395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19395 := by decide +kernel

theorem rowEval19395 (x : Key → ℝ) : Integer.Sparse.eval row19395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19395, Integer.Sparse.eval_collectBalanced, rawRowCheck19395]

def rawRow19396 : Integer.Sparse Key := [(key1933, 6), (key1701, 6), (key1696, 6), (key1701, 6), (key1933, 6), (key1701, 6), (key1696, 6), (key1953, 6), (key1751, 6), (key1933, 6), (key1278, 6), (key1696, 6), (key1273, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1278, 6)]

theorem rawRowCheck19396 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form0 = rawRow19396 := by decide +kernel

def row19396 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19396 : row19396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19396 := by decide +kernel

theorem rowEval19396 (x : Key → ℝ) : Integer.Sparse.eval row19396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19396, Integer.Sparse.eval_collectBalanced, rawRowCheck19396]

def rawRow19397 : Integer.Sparse Key := [(key1701, 6), (key1701, 6), (key1933, 6), (key1696, 6), (key1751, 6), (key1751, 6), (key1953, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1933, 6), (key1273, 6), (key1696, 6), (key1696, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6)]

theorem rawRowCheck19397 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19397 := by decide +kernel

def row19397 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19397 : row19397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19397 := by decide +kernel

theorem rowEval19397 (x : Key → ℝ) : Integer.Sparse.eval row19397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19397, Integer.Sparse.eval_collectBalanced, rawRowCheck19397]

def rawRow19398 : Integer.Sparse Key := [(key1701, 6), (key1933, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1953, 6), (key1751, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1696, 6), (key1273, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6)]

theorem rawRowCheck19398 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19398 := by decide +kernel

def row19398 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19398 : row19398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19398 := by decide +kernel

theorem rowEval19398 (x : Key → ℝ) : Integer.Sparse.eval row19398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19398, Integer.Sparse.eval_collectBalanced, rawRowCheck19398]

def rawRow19399 : Integer.Sparse Key := [(key1933, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1953, 6), (key1751, 6), (key1751, 6), (key1933, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1278, 6), (key1696, 6), (key1696, 6), (key1273, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6)]

theorem rawRowCheck19399 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19399 := by decide +kernel

def row19399 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19399 : row19399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19399 := by decide +kernel

theorem rowEval19399 (x : Key → ℝ) : Integer.Sparse.eval row19399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19399, Integer.Sparse.eval_collectBalanced, rawRowCheck19399]

def rawRow19400 : Integer.Sparse Key := [(key1751, 6), (key1751, 6), (key1751, 6), (key1953, 6), (key1278, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1273, 6), (key1696, 6), (key1696, 6), (key1696, 6)]

theorem rawRowCheck19400 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19400 := by decide +kernel

def row19400 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19400 : row19400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19400 := by decide +kernel

theorem rowEval19400 (x : Key → ℝ) : Integer.Sparse.eval row19400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19400, Integer.Sparse.eval_collectBalanced, rawRowCheck19400]

def rawRow19401 : Integer.Sparse Key := [(key1751, 6), (key1751, 6), (key1953, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1273, 6), (key1696, 6), (key1696, 6)]

theorem rawRowCheck19401 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19401 := by decide +kernel

def row19401 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19401 : row19401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19401 := by decide +kernel

theorem rowEval19401 (x : Key → ℝ) : Integer.Sparse.eval row19401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19401, Integer.Sparse.eval_collectBalanced, rawRowCheck19401]

def rawRow19402 : Integer.Sparse Key := [(key1751, 6), (key1953, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1933, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1696, 6), (key1696, 6), (key1273, 6), (key1696, 6)]

theorem rawRowCheck19402 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19402 := by decide +kernel

def row19402 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19402 : row19402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19402 := by decide +kernel

theorem rowEval19402 (x : Key → ℝ) : Integer.Sparse.eval row19402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19402, Integer.Sparse.eval_collectBalanced, rawRowCheck19402]

def rawRow19403 : Integer.Sparse Key := [(key1953, 6), (key1751, 6), (key1751, 6), (key1751, 6), (key1933, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1696, 6), (key1696, 6), (key1696, 6), (key1273, 6)]

theorem rawRowCheck19403 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19403 := by decide +kernel

def row19403 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

theorem rowCheck19403 : row19403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19403 := by decide +kernel

theorem rowEval19403 (x : Key → ℝ) : Integer.Sparse.eval row19403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19403, Integer.Sparse.eval_collectBalanced, rawRowCheck19403]

def rawRow19404 : Integer.Sparse Key := [(key222, 24), (key494, 24), (key494, 24), (key494, 24), (key548, 24)]

theorem rawRowCheck19404 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form1 = rawRow19404 := by decide +kernel

def row19404 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19404 : row19404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19404 := by decide +kernel

theorem rowEval19404 (x : Key → ℝ) : Integer.Sparse.eval row19404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19404, Integer.Sparse.eval_collectBalanced, rawRowCheck19404]

def rawRow19405 : Integer.Sparse Key := [(key222, 24), (key494, 24), (key494, 24), (key548, 24), (key494, 24)]

theorem rawRowCheck19405 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form1 = rawRow19405 := by decide +kernel

def row19405 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19405 : row19405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19405 := by decide +kernel

theorem rowEval19405 (x : Key → ℝ) : Integer.Sparse.eval row19405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19405, Integer.Sparse.eval_collectBalanced, rawRowCheck19405]

def rawRow19406 : Integer.Sparse Key := [(key222, 24), (key494, 24), (key548, 24), (key494, 24), (key494, 24)]

theorem rawRowCheck19406 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form1 = rawRow19406 := by decide +kernel

def row19406 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19406 : row19406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19406 := by decide +kernel

theorem rowEval19406 (x : Key → ℝ) : Integer.Sparse.eval row19406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19406, Integer.Sparse.eval_collectBalanced, rawRowCheck19406]

def rawRow19407 : Integer.Sparse Key := [(key222, 24), (key548, 24), (key494, 24), (key494, 24), (key494, 24)]

theorem rawRowCheck19407 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form1 = rawRow19407 := by decide +kernel

def row19407 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19407 : row19407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19407 := by decide +kernel

theorem rowEval19407 (x : Key → ℝ) : Integer.Sparse.eval row19407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19407, Integer.Sparse.eval_collectBalanced, rawRowCheck19407]

def rawRow19408 : Integer.Sparse Key := [(key494, 24), (key222, 24), (key494, 24), (key494, 24), (key548, 24)]

theorem rawRowCheck19408 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form1 = rawRow19408 := by decide +kernel

def row19408 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19408 : row19408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19408 := by decide +kernel

theorem rowEval19408 (x : Key → ℝ) : Integer.Sparse.eval row19408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19408, Integer.Sparse.eval_collectBalanced, rawRowCheck19408]

def rawRow19409 : Integer.Sparse Key := [(key494, 24), (key222, 24), (key494, 24), (key548, 24), (key494, 24)]

theorem rawRowCheck19409 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form1 = rawRow19409 := by decide +kernel

def row19409 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19409 : row19409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19409 := by decide +kernel

theorem rowEval19409 (x : Key → ℝ) : Integer.Sparse.eval row19409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19409, Integer.Sparse.eval_collectBalanced, rawRowCheck19409]

def rawRow19410 : Integer.Sparse Key := [(key494, 24), (key222, 24), (key548, 24), (key494, 24), (key494, 24)]

theorem rawRowCheck19410 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form1 = rawRow19410 := by decide +kernel

def row19410 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19410 : row19410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19410 := by decide +kernel

theorem rowEval19410 (x : Key → ℝ) : Integer.Sparse.eval row19410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19410, Integer.Sparse.eval_collectBalanced, rawRowCheck19410]

def rawRow19411 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key222, 24), (key494, 24), (key548, 24)]

theorem rawRowCheck19411 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form1 = rawRow19411 := by decide +kernel

def row19411 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19411 : row19411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19411 := by decide +kernel

theorem rowEval19411 (x : Key → ℝ) : Integer.Sparse.eval row19411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19411, Integer.Sparse.eval_collectBalanced, rawRowCheck19411]

def rawRow19412 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key222, 24), (key548, 24), (key494, 24)]

theorem rawRowCheck19412 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form1 = rawRow19412 := by decide +kernel

def row19412 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19412 : row19412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19412 := by decide +kernel

theorem rowEval19412 (x : Key → ℝ) : Integer.Sparse.eval row19412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19412, Integer.Sparse.eval_collectBalanced, rawRowCheck19412]

def rawRow19413 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key494, 24), (key222, 24), (key548, 24)]

theorem rawRowCheck19413 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form1 = rawRow19413 := by decide +kernel

def row19413 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19413 : row19413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19413 := by decide +kernel

theorem rowEval19413 (x : Key → ℝ) : Integer.Sparse.eval row19413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19413, Integer.Sparse.eval_collectBalanced, rawRowCheck19413]

def rawRow19414 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key494, 24), (key548, 24), (key222, 24)]

theorem rawRowCheck19414 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form1 = rawRow19414 := by decide +kernel

def row19414 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19414 : row19414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19414 := by decide +kernel

theorem rowEval19414 (x : Key → ℝ) : Integer.Sparse.eval row19414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19414, Integer.Sparse.eval_collectBalanced, rawRowCheck19414]

def rawRow19415 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key548, 24), (key222, 24), (key494, 24)]

theorem rawRowCheck19415 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form1 = rawRow19415 := by decide +kernel

def row19415 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19415 : row19415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19415 := by decide +kernel

theorem rowEval19415 (x : Key → ℝ) : Integer.Sparse.eval row19415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19415, Integer.Sparse.eval_collectBalanced, rawRowCheck19415]

def rawRow19416 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key548, 24), (key494, 24), (key222, 24)]

theorem rawRowCheck19416 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form1 = rawRow19416 := by decide +kernel

def row19416 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19416 : row19416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19416 := by decide +kernel

theorem rowEval19416 (x : Key → ℝ) : Integer.Sparse.eval row19416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19416, Integer.Sparse.eval_collectBalanced, rawRowCheck19416]

def rawRow19417 : Integer.Sparse Key := [(key494, 24), (key548, 24), (key222, 24), (key494, 24), (key494, 24)]

theorem rawRowCheck19417 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form1 = rawRow19417 := by decide +kernel

def row19417 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19417 : row19417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19417 := by decide +kernel

theorem rowEval19417 (x : Key → ℝ) : Integer.Sparse.eval row19417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19417, Integer.Sparse.eval_collectBalanced, rawRowCheck19417]

def rawRow19418 : Integer.Sparse Key := [(key494, 24), (key548, 24), (key494, 24), (key222, 24), (key494, 24)]

theorem rawRowCheck19418 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form1 = rawRow19418 := by decide +kernel

def row19418 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19418 : row19418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19418 := by decide +kernel

theorem rowEval19418 (x : Key → ℝ) : Integer.Sparse.eval row19418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19418, Integer.Sparse.eval_collectBalanced, rawRowCheck19418]

def rawRow19419 : Integer.Sparse Key := [(key494, 24), (key548, 24), (key494, 24), (key494, 24), (key222, 24)]

theorem rawRowCheck19419 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form1 = rawRow19419 := by decide +kernel

def row19419 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19419 : row19419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19419 := by decide +kernel

theorem rowEval19419 (x : Key → ℝ) : Integer.Sparse.eval row19419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19419, Integer.Sparse.eval_collectBalanced, rawRowCheck19419]

def rawRow19420 : Integer.Sparse Key := [(key548, 24), (key222, 24), (key494, 24), (key494, 24), (key494, 24)]

theorem rawRowCheck19420 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form1 = rawRow19420 := by decide +kernel

def row19420 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19420 : row19420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19420 := by decide +kernel

theorem rowEval19420 (x : Key → ℝ) : Integer.Sparse.eval row19420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19420, Integer.Sparse.eval_collectBalanced, rawRowCheck19420]

def rawRow19421 : Integer.Sparse Key := [(key548, 24), (key494, 24), (key222, 24), (key494, 24), (key494, 24)]

theorem rawRowCheck19421 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form1 = rawRow19421 := by decide +kernel

def row19421 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19421 : row19421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19421 := by decide +kernel

theorem rowEval19421 (x : Key → ℝ) : Integer.Sparse.eval row19421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19421, Integer.Sparse.eval_collectBalanced, rawRowCheck19421]

def rawRow19422 : Integer.Sparse Key := [(key548, 24), (key494, 24), (key494, 24), (key222, 24), (key494, 24)]

theorem rawRowCheck19422 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form1 = rawRow19422 := by decide +kernel

def row19422 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19422 : row19422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19422 := by decide +kernel

theorem rowEval19422 (x : Key → ℝ) : Integer.Sparse.eval row19422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19422, Integer.Sparse.eval_collectBalanced, rawRowCheck19422]

def rawRow19423 : Integer.Sparse Key := [(key548, 24), (key494, 24), (key494, 24), (key494, 24), (key222, 24)]

theorem rawRowCheck19423 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form1 = rawRow19423 := by decide +kernel

def row19423 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

theorem rowCheck19423 : row19423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19423 := by decide +kernel

theorem rowEval19423 (x : Key → ℝ) : Integer.Sparse.eval row19423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19423, Integer.Sparse.eval_collectBalanced, rawRowCheck19423]

def rawRow19424 : Integer.Sparse Key := [(key1358, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1364, 2), (key1358, 2), (key1374, 2), (key1364, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1374, 2), (key1484, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1490, 2), (key1484, 2), (key1513, 2), (key1490, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1513, 2), (key1710, 2), (key1716, 2), (key1710, 2), (key1723, 2), (key1716, 2), (key1723, 2), (key1710, 2), (key1716, 2), (key1710, 2), (key1741, 2), (key1716, 2), (key1741, 2), (key1710, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1716, 2), (key1723, 2), (key1716, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1937, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1949, 2), (key1940, 2), (key1949, 2)]

theorem rawRowCheck19424 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form2 = rawRow19424 := by decide +kernel

def row19424 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19424 : row19424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19424 := by decide +kernel

theorem rowEval19424 (x : Key → ℝ) : Integer.Sparse.eval row19424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19424, Integer.Sparse.eval_collectBalanced, rawRowCheck19424]

def rawRow19425 : Integer.Sparse Key := [(key1364, 2), (key1358, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1374, 2), (key1358, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1374, 2), (key1364, 2), (key1490, 2), (key1484, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1513, 2), (key1484, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1513, 2), (key1490, 2), (key1716, 2), (key1710, 2), (key1723, 2), (key1710, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1716, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1741, 2), (key1716, 2), (key1741, 2), (key1723, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1949, 2), (key1940, 2)]

theorem rawRowCheck19425 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form2 = rawRow19425 := by decide +kernel

def row19425 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19425 : row19425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19425 := by decide +kernel

theorem rowEval19425 (x : Key → ℝ) : Integer.Sparse.eval row19425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19425, Integer.Sparse.eval_collectBalanced, rawRowCheck19425]

def rawRow19426 : Integer.Sparse Key := [(key1364, 2), (key1364, 2), (key1358, 2), (key1374, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1358, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1513, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1484, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1741, 2), (key1741, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1710, 2), (key1710, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1937, 2), (key1949, 2), (key1949, 2), (key1940, 2), (key1940, 2), (key1937, 2), (key1937, 2)]

theorem rawRowCheck19426 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form2 = rawRow19426 := by decide +kernel

def row19426 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19426 : row19426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19426 := by decide +kernel

theorem rowEval19426 (x : Key → ℝ) : Integer.Sparse.eval row19426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19426, Integer.Sparse.eval_collectBalanced, rawRowCheck19426]

def rawRow19427 : Integer.Sparse Key := [(key1374, 2), (key1374, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1358, 2), (key1358, 2), (key1513, 2), (key1513, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1484, 2), (key1484, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1949, 2), (key1949, 2), (key1949, 2), (key1940, 2), (key1940, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2)]

theorem rawRowCheck19427 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form2 = rawRow19427 := by decide +kernel

def row19427 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19427 : row19427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19427 := by decide +kernel

theorem rowEval19427 (x : Key → ℝ) : Integer.Sparse.eval row19427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19427, Integer.Sparse.eval_collectBalanced, rawRowCheck19427]

def rawRow19428 : Integer.Sparse Key := [(key1484, 2), (key1490, 2), (key1490, 2), (key1710, 2), (key1716, 2), (key1710, 2), (key1723, 2), (key1716, 2), (key1723, 2), (key1937, 2), (key1937, 2), (key1940, 2), (key1358, 2), (key1364, 2), (key1364, 2), (key1710, 2), (key1716, 2), (key1710, 2), (key1741, 2), (key1716, 2), (key1741, 2), (key1937, 2), (key1937, 2), (key1949, 2), (key1358, 2), (key1364, 2), (key1358, 2), (key1374, 2), (key1364, 2), (key1374, 2), (key1484, 2), (key1490, 2), (key1484, 2), (key1513, 2), (key1490, 2), (key1513, 2), (key1710, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1949, 2), (key1940, 2), (key1949, 2), (key1364, 2), (key1364, 2), (key1374, 2), (key1490, 2), (key1490, 2), (key1513, 2), (key1716, 2), (key1723, 2), (key1716, 2), (key1741, 2), (key1723, 2), (key1741, 2)]

theorem rawRowCheck19428 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form2 = rawRow19428 := by decide +kernel

def row19428 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19428 : row19428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19428 := by decide +kernel

theorem rowEval19428 (x : Key → ℝ) : Integer.Sparse.eval row19428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19428, Integer.Sparse.eval_collectBalanced, rawRowCheck19428]

def rawRow19429 : Integer.Sparse Key := [(key1490, 2), (key1484, 2), (key1490, 2), (key1716, 2), (key1710, 2), (key1723, 2), (key1710, 2), (key1723, 2), (key1716, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1364, 2), (key1358, 2), (key1364, 2), (key1716, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1716, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1364, 2), (key1358, 2), (key1374, 2), (key1358, 2), (key1374, 2), (key1364, 2), (key1490, 2), (key1484, 2), (key1513, 2), (key1484, 2), (key1513, 2), (key1490, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1940, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1949, 2), (key1940, 2), (key1364, 2), (key1374, 2), (key1364, 2), (key1490, 2), (key1513, 2), (key1490, 2), (key1723, 2), (key1716, 2), (key1741, 2), (key1716, 2), (key1741, 2), (key1723, 2)]

theorem rawRowCheck19429 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form2 = rawRow19429 := by decide +kernel

def row19429 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19429 : row19429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19429 := by decide +kernel

theorem rowEval19429 (x : Key → ℝ) : Integer.Sparse.eval row19429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19429, Integer.Sparse.eval_collectBalanced, rawRowCheck19429]

def rawRow19430 : Integer.Sparse Key := [(key1490, 2), (key1490, 2), (key1484, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1741, 2), (key1741, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1949, 2), (key1937, 2), (key1937, 2), (key1374, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1358, 2), (key1513, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1484, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1710, 2), (key1710, 2), (key1949, 2), (key1949, 2), (key1940, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1716, 2)]

theorem rawRowCheck19430 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form2 = rawRow19430 := by decide +kernel

def row19430 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19430 : row19430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19430 := by decide +kernel

theorem rowEval19430 (x : Key → ℝ) : Integer.Sparse.eval row19430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19430, Integer.Sparse.eval_collectBalanced, rawRowCheck19430]

def rawRow19431 : Integer.Sparse Key := [(key1710, 2), (key1716, 2), (key1937, 2), (key1484, 2), (key1490, 2), (key1710, 2), (key1723, 2), (key1937, 2), (key1940, 2), (key1490, 2), (key1716, 2), (key1723, 2), (key1710, 2), (key1716, 2), (key1937, 2), (key1358, 2), (key1364, 2), (key1710, 2), (key1741, 2), (key1937, 2), (key1949, 2), (key1364, 2), (key1716, 2), (key1741, 2), (key1484, 2), (key1490, 2), (key1710, 2), (key1723, 2), (key1937, 2), (key1940, 2), (key1358, 2), (key1364, 2), (key1710, 2), (key1741, 2), (key1937, 2), (key1949, 2), (key1358, 2), (key1374, 2), (key1484, 2), (key1513, 2), (key1940, 2), (key1949, 2), (key1364, 2), (key1374, 2), (key1490, 2), (key1513, 2), (key1723, 2), (key1741, 2), (key1490, 2), (key1716, 2), (key1723, 2), (key1364, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1374, 2), (key1490, 2), (key1513, 2), (key1723, 2), (key1741, 2)]

theorem rawRowCheck19431 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form2 = rawRow19431 := by decide +kernel

def row19431 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19431 : row19431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19431 := by decide +kernel

theorem rowEval19431 (x : Key → ℝ) : Integer.Sparse.eval row19431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19431, Integer.Sparse.eval_collectBalanced, rawRowCheck19431]

def rawRow19432 : Integer.Sparse Key := [(key1716, 2), (key1710, 2), (key1937, 2), (key1490, 2), (key1484, 2), (key1723, 2), (key1710, 2), (key1940, 2), (key1937, 2), (key1490, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1937, 2), (key1364, 2), (key1358, 2), (key1741, 2), (key1710, 2), (key1949, 2), (key1937, 2), (key1364, 2), (key1741, 2), (key1716, 2), (key1490, 2), (key1484, 2), (key1723, 2), (key1710, 2), (key1940, 2), (key1937, 2), (key1364, 2), (key1358, 2), (key1741, 2), (key1710, 2), (key1949, 2), (key1937, 2), (key1374, 2), (key1358, 2), (key1513, 2), (key1484, 2), (key1949, 2), (key1940, 2), (key1374, 2), (key1364, 2), (key1513, 2), (key1490, 2), (key1741, 2), (key1723, 2), (key1490, 2), (key1723, 2), (key1716, 2), (key1364, 2), (key1741, 2), (key1716, 2), (key1374, 2), (key1364, 2), (key1513, 2), (key1490, 2), (key1741, 2), (key1723, 2)]

theorem rawRowCheck19432 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form2 = rawRow19432 := by decide +kernel

def row19432 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19432 : row19432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19432 := by decide +kernel

theorem rowEval19432 (x : Key → ℝ) : Integer.Sparse.eval row19432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19432, Integer.Sparse.eval_collectBalanced, rawRowCheck19432]

def rawRow19433 : Integer.Sparse Key := [(key1710, 2), (key1937, 2), (key1716, 2), (key1710, 2), (key1937, 2), (key1484, 2), (key1940, 2), (key1490, 2), (key1723, 2), (key1716, 2), (key1490, 2), (key1723, 2), (key1710, 2), (key1937, 2), (key1716, 2), (key1710, 2), (key1937, 2), (key1358, 2), (key1949, 2), (key1364, 2), (key1741, 2), (key1716, 2), (key1364, 2), (key1741, 2), (key1710, 2), (key1937, 2), (key1484, 2), (key1940, 2), (key1490, 2), (key1723, 2), (key1710, 2), (key1937, 2), (key1358, 2), (key1949, 2), (key1364, 2), (key1741, 2), (key1484, 2), (key1940, 2), (key1358, 2), (key1949, 2), (key1374, 2), (key1513, 2), (key1490, 2), (key1723, 2), (key1364, 2), (key1741, 2), (key1374, 2), (key1513, 2), (key1716, 2), (key1490, 2), (key1723, 2), (key1716, 2), (key1364, 2), (key1741, 2), (key1490, 2), (key1723, 2), (key1364, 2), (key1741, 2), (key1374, 2), (key1513, 2)]

theorem rawRowCheck19433 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form2 = rawRow19433 := by decide +kernel

def row19433 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19433 : row19433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19433 := by decide +kernel

theorem rowEval19433 (x : Key → ℝ) : Integer.Sparse.eval row19433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19433, Integer.Sparse.eval_collectBalanced, rawRowCheck19433]

def rawRow19434 : Integer.Sparse Key := [(key1937, 2), (key1710, 2), (key1716, 2), (key1937, 2), (key1710, 2), (key1940, 2), (key1484, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1937, 2), (key1710, 2), (key1716, 2), (key1937, 2), (key1710, 2), (key1949, 2), (key1358, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1937, 2), (key1710, 2), (key1940, 2), (key1484, 2), (key1723, 2), (key1490, 2), (key1937, 2), (key1710, 2), (key1949, 2), (key1358, 2), (key1741, 2), (key1364, 2), (key1940, 2), (key1484, 2), (key1949, 2), (key1358, 2), (key1513, 2), (key1374, 2), (key1723, 2), (key1490, 2), (key1741, 2), (key1364, 2), (key1513, 2), (key1374, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1723, 2), (key1490, 2), (key1741, 2), (key1364, 2), (key1513, 2), (key1374, 2)]

theorem rawRowCheck19434 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form2 = rawRow19434 := by decide +kernel

def row19434 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19434 : row19434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19434 := by decide +kernel

theorem rowEval19434 (x : Key → ℝ) : Integer.Sparse.eval row19434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19434, Integer.Sparse.eval_collectBalanced, rawRowCheck19434]

def rawRow19435 : Integer.Sparse Key := [(key1716, 2), (key1937, 2), (key1710, 2), (key1723, 2), (key1940, 2), (key1490, 2), (key1937, 2), (key1484, 2), (key1710, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1710, 2), (key1741, 2), (key1949, 2), (key1364, 2), (key1937, 2), (key1358, 2), (key1710, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1723, 2), (key1940, 2), (key1490, 2), (key1937, 2), (key1484, 2), (key1710, 2), (key1741, 2), (key1949, 2), (key1364, 2), (key1937, 2), (key1358, 2), (key1710, 2), (key1513, 2), (key1949, 2), (key1374, 2), (key1940, 2), (key1358, 2), (key1484, 2), (key1513, 2), (key1741, 2), (key1374, 2), (key1723, 2), (key1364, 2), (key1490, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1513, 2), (key1741, 2), (key1374, 2), (key1723, 2), (key1364, 2), (key1490, 2)]

theorem rawRowCheck19435 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form2 = rawRow19435 := by decide +kernel

def row19435 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19435 : row19435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19435 := by decide +kernel

theorem rowEval19435 (x : Key → ℝ) : Integer.Sparse.eval row19435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19435, Integer.Sparse.eval_collectBalanced, rawRowCheck19435]

def rawRow19436 : Integer.Sparse Key := [(key1937, 2), (key1716, 2), (key1710, 2), (key1940, 2), (key1723, 2), (key1937, 2), (key1490, 2), (key1710, 2), (key1484, 2), (key1723, 2), (key1716, 2), (key1490, 2), (key1937, 2), (key1716, 2), (key1710, 2), (key1949, 2), (key1741, 2), (key1937, 2), (key1364, 2), (key1710, 2), (key1358, 2), (key1741, 2), (key1716, 2), (key1364, 2), (key1940, 2), (key1723, 2), (key1937, 2), (key1490, 2), (key1710, 2), (key1484, 2), (key1949, 2), (key1741, 2), (key1937, 2), (key1364, 2), (key1710, 2), (key1358, 2), (key1949, 2), (key1513, 2), (key1940, 2), (key1374, 2), (key1484, 2), (key1358, 2), (key1741, 2), (key1513, 2), (key1723, 2), (key1374, 2), (key1490, 2), (key1364, 2), (key1723, 2), (key1716, 2), (key1490, 2), (key1741, 2), (key1716, 2), (key1364, 2), (key1741, 2), (key1513, 2), (key1723, 2), (key1374, 2), (key1490, 2), (key1364, 2)]

theorem rawRowCheck19436 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form2 = rawRow19436 := by decide +kernel

def row19436 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19436 : row19436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19436 := by decide +kernel

theorem rowEval19436 (x : Key → ℝ) : Integer.Sparse.eval row19436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19436, Integer.Sparse.eval_collectBalanced, rawRowCheck19436]

def rawRow19437 : Integer.Sparse Key := [(key1723, 2), (key1723, 2), (key1940, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1937, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1937, 2), (key1358, 2), (key1710, 2), (key1710, 2), (key1513, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1949, 2), (key1374, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1940, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1937, 2), (key1937, 2), (key1358, 2), (key1358, 2), (key1484, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2)]

theorem rawRowCheck19437 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form2 = rawRow19437 := by decide +kernel

def row19437 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19437 : row19437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19437 := by decide +kernel

theorem rowEval19437 (x : Key → ℝ) : Integer.Sparse.eval row19437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19437, Integer.Sparse.eval_collectBalanced, rawRowCheck19437]

def rawRow19438 : Integer.Sparse Key := [(key1723, 2), (key1940, 2), (key1723, 2), (key1716, 2), (key1937, 2), (key1490, 2), (key1937, 2), (key1490, 2), (key1716, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1741, 2), (key1949, 2), (key1741, 2), (key1716, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1716, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1741, 2), (key1949, 2), (key1513, 2), (key1949, 2), (key1513, 2), (key1741, 2), (key1723, 2), (key1940, 2), (key1374, 2), (key1940, 2), (key1374, 2), (key1723, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1484, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1358, 2), (key1484, 2), (key1741, 2), (key1513, 2), (key1741, 2), (key1723, 2), (key1374, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1490, 2)]

theorem rawRowCheck19438 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form2 = rawRow19438 := by decide +kernel

def row19438 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19438 : row19438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19438 := by decide +kernel

theorem rowEval19438 (x : Key → ℝ) : Integer.Sparse.eval row19438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19438, Integer.Sparse.eval_collectBalanced, rawRowCheck19438]

def rawRow19439 : Integer.Sparse Key := [(key1940, 2), (key1723, 2), (key1723, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1710, 2), (key1710, 2), (key1484, 2), (key1949, 2), (key1741, 2), (key1741, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1710, 2), (key1710, 2), (key1358, 2), (key1949, 2), (key1741, 2), (key1949, 2), (key1513, 2), (key1741, 2), (key1513, 2), (key1940, 2), (key1723, 2), (key1940, 2), (key1374, 2), (key1723, 2), (key1374, 2), (key1937, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1358, 2), (key1484, 2), (key1358, 2), (key1741, 2), (key1741, 2), (key1513, 2), (key1723, 2), (key1723, 2), (key1374, 2), (key1716, 2), (key1490, 2), (key1716, 2), (key1364, 2), (key1490, 2), (key1364, 2)]

theorem rawRowCheck19439 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form2 = rawRow19439 := by decide +kernel

def row19439 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19439 : row19439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19439 := by decide +kernel

theorem rowEval19439 (x : Key → ℝ) : Integer.Sparse.eval row19439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19439, Integer.Sparse.eval_collectBalanced, rawRowCheck19439]

def rawRow19440 : Integer.Sparse Key := [(key1513, 2), (key1513, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1949, 2), (key1949, 2), (key1374, 2), (key1374, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1940, 2), (key1940, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1358, 2), (key1358, 2), (key1358, 2), (key1484, 2), (key1484, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2)]

theorem rawRowCheck19440 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form2 = rawRow19440 := by decide +kernel

def row19440 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19440 : row19440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19440 := by decide +kernel

theorem rowEval19440 (x : Key → ℝ) : Integer.Sparse.eval row19440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19440, Integer.Sparse.eval_collectBalanced, rawRowCheck19440]

def rawRow19441 : Integer.Sparse Key := [(key1741, 2), (key1741, 2), (key1949, 2), (key1513, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1949, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1374, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1940, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1937, 2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1937, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1937, 2), (key1937, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1710, 2), (key1358, 2), (key1358, 2), (key1484, 2), (key1484, 2), (key1710, 2), (key1710, 2)]

theorem rawRowCheck19441 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form2 = rawRow19441 := by decide +kernel

def row19441 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19441 : row19441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19441 := by decide +kernel

theorem rowEval19441 (x : Key → ℝ) : Integer.Sparse.eval row19441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19441, Integer.Sparse.eval_collectBalanced, rawRowCheck19441]

def rawRow19442 : Integer.Sparse Key := [(key1741, 2), (key1949, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1513, 2), (key1949, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1513, 2), (key1741, 2), (key1723, 2), (key1940, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1374, 2), (key1940, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1374, 2), (key1723, 2), (key1716, 2), (key1937, 2), (key1490, 2), (key1937, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1716, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1490, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1358, 2), (key1484, 2)]

theorem rawRowCheck19442 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form2 = rawRow19442 := by decide +kernel

def row19442 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19442 : row19442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19442 := by decide +kernel

theorem rowEval19442 (x : Key → ℝ) : Integer.Sparse.eval row19442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19442, Integer.Sparse.eval_collectBalanced, rawRowCheck19442]

def rawRow19443 : Integer.Sparse Key := [(key1949, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1741, 2), (key1949, 2), (key1513, 2), (key1741, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1513, 2), (key1940, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1723, 2), (key1940, 2), (key1374, 2), (key1723, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1374, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1937, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1716, 2), (key1490, 2), (key1716, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1710, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1358, 2), (key1484, 2), (key1358, 2)]

theorem rawRowCheck19443 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form2 = rawRow19443 := by decide +kernel

def row19443 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

theorem rowCheck19443 : row19443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19443 := by decide +kernel

theorem rowEval19443 (x : Key → ℝ) : Integer.Sparse.eval row19443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19443, Integer.Sparse.eval_collectBalanced, rawRowCheck19443]

def rawRow19444 : Integer.Sparse Key := [(key1275, 24), (key1698, 24), (key1698, 24), (key1698, 24), (key1750, 24)]

theorem rawRowCheck19444 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form3 = rawRow19444 := by decide +kernel

def row19444 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19444 : row19444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19444 := by decide +kernel

theorem rowEval19444 (x : Key → ℝ) : Integer.Sparse.eval row19444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19444, Integer.Sparse.eval_collectBalanced, rawRowCheck19444]

def rawRow19445 : Integer.Sparse Key := [(key1275, 24), (key1698, 24), (key1698, 24), (key1750, 24), (key1698, 24)]

theorem rawRowCheck19445 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form3 = rawRow19445 := by decide +kernel

def row19445 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19445 : row19445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19445 := by decide +kernel

theorem rowEval19445 (x : Key → ℝ) : Integer.Sparse.eval row19445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19445, Integer.Sparse.eval_collectBalanced, rawRowCheck19445]

def rawRow19446 : Integer.Sparse Key := [(key1275, 24), (key1698, 24), (key1750, 24), (key1698, 24), (key1698, 24)]

theorem rawRowCheck19446 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form3 = rawRow19446 := by decide +kernel

def row19446 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19446 : row19446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19446 := by decide +kernel

theorem rowEval19446 (x : Key → ℝ) : Integer.Sparse.eval row19446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19446, Integer.Sparse.eval_collectBalanced, rawRowCheck19446]

def rawRow19447 : Integer.Sparse Key := [(key1275, 24), (key1750, 24), (key1698, 24), (key1698, 24), (key1698, 24)]

theorem rawRowCheck19447 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19447 := by decide +kernel

def row19447 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19447 : row19447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19447 := by decide +kernel

theorem rowEval19447 (x : Key → ℝ) : Integer.Sparse.eval row19447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19447, Integer.Sparse.eval_collectBalanced, rawRowCheck19447]

def rawRow19448 : Integer.Sparse Key := [(key1698, 24), (key1275, 24), (key1698, 24), (key1698, 24), (key1750, 24)]

theorem rawRowCheck19448 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form3 = rawRow19448 := by decide +kernel

def row19448 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19448 : row19448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19448 := by decide +kernel

theorem rowEval19448 (x : Key → ℝ) : Integer.Sparse.eval row19448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19448, Integer.Sparse.eval_collectBalanced, rawRowCheck19448]

def rawRow19449 : Integer.Sparse Key := [(key1698, 24), (key1275, 24), (key1698, 24), (key1750, 24), (key1698, 24)]

theorem rawRowCheck19449 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form3 = rawRow19449 := by decide +kernel

def row19449 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19449 : row19449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19449 := by decide +kernel

theorem rowEval19449 (x : Key → ℝ) : Integer.Sparse.eval row19449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19449, Integer.Sparse.eval_collectBalanced, rawRowCheck19449]

def rawRow19450 : Integer.Sparse Key := [(key1698, 24), (key1275, 24), (key1750, 24), (key1698, 24), (key1698, 24)]

theorem rawRowCheck19450 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form3 = rawRow19450 := by decide +kernel

def row19450 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19450 : row19450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19450 := by decide +kernel

theorem rowEval19450 (x : Key → ℝ) : Integer.Sparse.eval row19450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19450, Integer.Sparse.eval_collectBalanced, rawRowCheck19450]

def rawRow19451 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1275, 24), (key1698, 24), (key1750, 24)]

theorem rawRowCheck19451 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form3 = rawRow19451 := by decide +kernel

def row19451 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19451 : row19451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19451 := by decide +kernel

theorem rowEval19451 (x : Key → ℝ) : Integer.Sparse.eval row19451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19451, Integer.Sparse.eval_collectBalanced, rawRowCheck19451]

def rawRow19452 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1275, 24), (key1750, 24), (key1698, 24)]

theorem rawRowCheck19452 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form3 = rawRow19452 := by decide +kernel

def row19452 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19452 : row19452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19452 := by decide +kernel

theorem rowEval19452 (x : Key → ℝ) : Integer.Sparse.eval row19452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19452, Integer.Sparse.eval_collectBalanced, rawRowCheck19452]

def rawRow19453 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1698, 24), (key1275, 24), (key1750, 24)]

theorem rawRowCheck19453 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form3 = rawRow19453 := by decide +kernel

def row19453 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19453 : row19453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19453 := by decide +kernel

theorem rowEval19453 (x : Key → ℝ) : Integer.Sparse.eval row19453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19453, Integer.Sparse.eval_collectBalanced, rawRowCheck19453]

def rawRow19454 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1698, 24), (key1750, 24), (key1275, 24)]

theorem rawRowCheck19454 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form3 = rawRow19454 := by decide +kernel

def row19454 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19454 : row19454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19454 := by decide +kernel

theorem rowEval19454 (x : Key → ℝ) : Integer.Sparse.eval row19454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19454, Integer.Sparse.eval_collectBalanced, rawRowCheck19454]

def rawRow19455 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1750, 24), (key1275, 24), (key1698, 24)]

theorem rawRowCheck19455 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form3 = rawRow19455 := by decide +kernel

def row19455 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19455 : row19455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19455 := by decide +kernel

theorem rowEval19455 (x : Key → ℝ) : Integer.Sparse.eval row19455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19455, Integer.Sparse.eval_collectBalanced, rawRowCheck19455]

end MUB6.Certificate.GramRows

end OAI
