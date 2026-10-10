import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19584 : Integer.Sparse Key := [(key288, 6), (key289, 6), (key289, 6), (key289, 6), (key513, 6), (key515, 6), (key515, 6), (key513, 6), (key515, 6), (key513, 6), (key547, 6), (key515, 6), (key547, 6), (key515, 6), (key515, 6), (key547, 6), (key670, 6), (key670, 6), (key670, 6), (key680, 6)]

theorem rawRowCheck19584 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form10 = rawRow19584 := by decide +kernel

def row19584 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

theorem rowCheck19584 : row19584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19584 := by decide +kernel

theorem rowEval19584 (x : Key → ℝ) : Integer.Sparse.eval row19584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19584, Integer.Sparse.eval_collectBalanced, rawRowCheck19584]

def rawRow19585 : Integer.Sparse Key := [(key289, 6), (key288, 6), (key289, 6), (key289, 6), (key515, 6), (key513, 6), (key515, 6), (key515, 6), (key513, 6), (key547, 6), (key513, 6), (key547, 6), (key515, 6), (key515, 6), (key547, 6), (key515, 6), (key670, 6), (key670, 6), (key680, 6), (key670, 6)]

theorem rawRowCheck19585 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form10 = rawRow19585 := by decide +kernel

def row19585 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

theorem rowCheck19585 : row19585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19585 := by decide +kernel

theorem rowEval19585 (x : Key → ℝ) : Integer.Sparse.eval row19585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19585, Integer.Sparse.eval_collectBalanced, rawRowCheck19585]

def rawRow19586 : Integer.Sparse Key := [(key289, 6), (key289, 6), (key288, 6), (key289, 6), (key515, 6), (key515, 6), (key513, 6), (key547, 6), (key547, 6), (key515, 6), (key515, 6), (key513, 6), (key513, 6), (key547, 6), (key515, 6), (key515, 6), (key670, 6), (key680, 6), (key670, 6), (key670, 6)]

theorem rawRowCheck19586 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form10 = rawRow19586 := by decide +kernel

def row19586 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

theorem rowCheck19586 : row19586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19586 := by decide +kernel

theorem rowEval19586 (x : Key → ℝ) : Integer.Sparse.eval row19586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19586, Integer.Sparse.eval_collectBalanced, rawRowCheck19586]

def rawRow19587 : Integer.Sparse Key := [(key289, 6), (key289, 6), (key289, 6), (key288, 6), (key547, 6), (key547, 6), (key547, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key513, 6), (key513, 6), (key513, 6), (key680, 6), (key670, 6), (key670, 6), (key670, 6)]

theorem rawRowCheck19587 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form10 = rawRow19587 := by decide +kernel

def row19587 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

theorem rowCheck19587 : row19587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19587 := by decide +kernel

theorem rowEval19587 (x : Key → ℝ) : Integer.Sparse.eval row19587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19587, Integer.Sparse.eval_collectBalanced, rawRowCheck19587]

def rawRow19588 : Integer.Sparse Key := [(key513, 6), (key515, 6), (key515, 6), (key547, 6), (key288, 6), (key289, 6), (key289, 6), (key513, 6), (key515, 6), (key513, 6), (key547, 6), (key515, 6), (key547, 6), (key670, 6), (key670, 6), (key680, 6), (key289, 6), (key515, 6), (key515, 6), (key547, 6)]

theorem rawRowCheck19588 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form10 = rawRow19588 := by decide +kernel

def row19588 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 24), (key670, 12), (key680, 6)]

theorem rowCheck19588 : row19588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19588 := by decide +kernel

theorem rowEval19588 (x : Key → ℝ) : Integer.Sparse.eval row19588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19588, Integer.Sparse.eval_collectBalanced, rawRowCheck19588]

def rawRow19589 : Integer.Sparse Key := [(key515, 6), (key513, 6), (key515, 6), (key547, 6), (key289, 6), (key288, 6), (key289, 6), (key515, 6), (key513, 6), (key547, 6), (key513, 6), (key547, 6), (key515, 6), (key670, 6), (key680, 6), (key670, 6), (key289, 6), (key515, 6), (key547, 6), (key515, 6)]

theorem rawRowCheck19589 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form10 = rawRow19589 := by decide +kernel

def row19589 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 24), (key670, 12), (key680, 6)]

theorem rowCheck19589 : row19589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19589 := by decide +kernel

theorem rowEval19589 (x : Key → ℝ) : Integer.Sparse.eval row19589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19589, Integer.Sparse.eval_collectBalanced, rawRowCheck19589]

def rawRow19590 : Integer.Sparse Key := [(key515, 6), (key515, 6), (key513, 6), (key547, 6), (key289, 6), (key289, 6), (key288, 6), (key547, 6), (key547, 6), (key515, 6), (key515, 6), (key513, 6), (key513, 6), (key680, 6), (key670, 6), (key670, 6), (key289, 6), (key547, 6), (key515, 6), (key515, 6)]

theorem rawRowCheck19590 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form10 = rawRow19590 := by decide +kernel

def row19590 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 24), (key670, 12), (key680, 6)]

theorem rowCheck19590 : row19590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19590 := by decide +kernel

theorem rowEval19590 (x : Key → ℝ) : Integer.Sparse.eval row19590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19590, Integer.Sparse.eval_collectBalanced, rawRowCheck19590]

def rawRow19591 : Integer.Sparse Key := [(key513, 6), (key515, 6), (key547, 6), (key515, 6), (key513, 6), (key515, 6), (key547, 6), (key288, 6), (key289, 6), (key513, 6), (key547, 6), (key670, 6), (key680, 6), (key289, 6), (key515, 6), (key547, 6), (key515, 6), (key289, 6), (key515, 6), (key547, 6)]

theorem rawRowCheck19591 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form10 = rawRow19591 := by decide +kernel

def row19591 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 30), (key670, 6), (key680, 6)]

theorem rowCheck19591 : row19591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19591 := by decide +kernel

theorem rowEval19591 (x : Key → ℝ) : Integer.Sparse.eval row19591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19591, Integer.Sparse.eval_collectBalanced, rawRowCheck19591]

def rawRow19592 : Integer.Sparse Key := [(key515, 6), (key513, 6), (key547, 6), (key515, 6), (key515, 6), (key513, 6), (key547, 6), (key289, 6), (key288, 6), (key547, 6), (key513, 6), (key680, 6), (key670, 6), (key289, 6), (key547, 6), (key515, 6), (key515, 6), (key289, 6), (key547, 6), (key515, 6)]

theorem rawRowCheck19592 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form10 = rawRow19592 := by decide +kernel

def row19592 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 30), (key670, 6), (key680, 6)]

theorem rowCheck19592 : row19592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19592 := by decide +kernel

theorem rowEval19592 (x : Key → ℝ) : Integer.Sparse.eval row19592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19592, Integer.Sparse.eval_collectBalanced, rawRowCheck19592]

def rawRow19593 : Integer.Sparse Key := [(key513, 6), (key547, 6), (key515, 6), (key515, 6), (key513, 6), (key547, 6), (key515, 6), (key513, 6), (key547, 6), (key288, 6), (key680, 6), (key289, 6), (key547, 6), (key515, 6), (key289, 6), (key547, 6), (key515, 6), (key515, 6), (key289, 6), (key547, 6)]

theorem rawRowCheck19593 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form10 = rawRow19593 := by decide +kernel

def row19593 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 36), (key680, 6)]

theorem rowCheck19593 : row19593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19593 := by decide +kernel

theorem rowEval19593 (x : Key → ℝ) : Integer.Sparse.eval row19593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19593, Integer.Sparse.eval_collectBalanced, rawRowCheck19593]

def rawRow19594 : Integer.Sparse Key := [(key547, 6), (key513, 6), (key515, 6), (key515, 6), (key547, 6), (key513, 6), (key515, 6), (key547, 6), (key513, 6), (key680, 6), (key288, 6), (key547, 6), (key289, 6), (key515, 6), (key547, 6), (key289, 6), (key515, 6), (key515, 6), (key547, 6), (key289, 6)]

theorem rawRowCheck19594 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form10 = rawRow19594 := by decide +kernel

def row19594 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 36), (key680, 6)]

theorem rowCheck19594 : row19594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19594 := by decide +kernel

theorem rowEval19594 (x : Key → ℝ) : Integer.Sparse.eval row19594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19594, Integer.Sparse.eval_collectBalanced, rawRowCheck19594]

def rawRow19595 : Integer.Sparse Key := [(key515, 6), (key547, 6), (key513, 6), (key515, 6), (key515, 6), (key547, 6), (key513, 6), (key670, 6), (key680, 6), (key289, 6), (key547, 6), (key288, 6), (key513, 6), (key547, 6), (key289, 6), (key515, 6), (key515, 6), (key547, 6), (key289, 6), (key515, 6)]

theorem rawRowCheck19595 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form10 = rawRow19595 := by decide +kernel

def row19595 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 30), (key670, 6), (key680, 6)]

theorem rowCheck19595 : row19595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19595 := by decide +kernel

theorem rowEval19595 (x : Key → ℝ) : Integer.Sparse.eval row19595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19595, Integer.Sparse.eval_collectBalanced, rawRowCheck19595]

def rawRow19596 : Integer.Sparse Key := [(key547, 6), (key515, 6), (key513, 6), (key515, 6), (key547, 6), (key515, 6), (key513, 6), (key680, 6), (key670, 6), (key547, 6), (key289, 6), (key513, 6), (key288, 6), (key547, 6), (key515, 6), (key289, 6), (key515, 6), (key547, 6), (key515, 6), (key289, 6)]

theorem rawRowCheck19596 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form10 = rawRow19596 := by decide +kernel

def row19596 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 30), (key670, 6), (key680, 6)]

theorem rowCheck19596 : row19596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19596 := by decide +kernel

theorem rowEval19596 (x : Key → ℝ) : Integer.Sparse.eval row19596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19596, Integer.Sparse.eval_collectBalanced, rawRowCheck19596]

def rawRow19597 : Integer.Sparse Key := [(key515, 6), (key515, 6), (key547, 6), (key513, 6), (key670, 6), (key670, 6), (key680, 6), (key289, 6), (key289, 6), (key515, 6), (key515, 6), (key547, 6), (key547, 6), (key288, 6), (key513, 6), (key513, 6), (key547, 6), (key289, 6), (key515, 6), (key515, 6)]

theorem rawRowCheck19597 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form10 = rawRow19597 := by decide +kernel

def row19597 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 24), (key670, 12), (key680, 6)]

theorem rowCheck19597 : row19597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19597 := by decide +kernel

theorem rowEval19597 (x : Key → ℝ) : Integer.Sparse.eval row19597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19597, Integer.Sparse.eval_collectBalanced, rawRowCheck19597]

def rawRow19598 : Integer.Sparse Key := [(key515, 6), (key547, 6), (key515, 6), (key513, 6), (key670, 6), (key680, 6), (key670, 6), (key515, 6), (key547, 6), (key289, 6), (key547, 6), (key289, 6), (key515, 6), (key513, 6), (key288, 6), (key513, 6), (key547, 6), (key515, 6), (key289, 6), (key515, 6)]

theorem rawRowCheck19598 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form10 = rawRow19598 := by decide +kernel

def row19598 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 24), (key670, 12), (key680, 6)]

theorem rowCheck19598 : row19598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19598 := by decide +kernel

theorem rowEval19598 (x : Key → ℝ) : Integer.Sparse.eval row19598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19598, Integer.Sparse.eval_collectBalanced, rawRowCheck19598]

def rawRow19599 : Integer.Sparse Key := [(key547, 6), (key515, 6), (key515, 6), (key513, 6), (key680, 6), (key670, 6), (key670, 6), (key547, 6), (key515, 6), (key547, 6), (key289, 6), (key515, 6), (key289, 6), (key513, 6), (key513, 6), (key288, 6), (key547, 6), (key515, 6), (key515, 6), (key289, 6)]

theorem rawRowCheck19599 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form10 = rawRow19599 := by decide +kernel

def row19599 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 24), (key670, 12), (key680, 6)]

theorem rowCheck19599 : row19599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19599 := by decide +kernel

theorem rowEval19599 (x : Key → ℝ) : Integer.Sparse.eval row19599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19599, Integer.Sparse.eval_collectBalanced, rawRowCheck19599]

def rawRow19600 : Integer.Sparse Key := [(key670, 6), (key670, 6), (key670, 6), (key680, 6), (key289, 6), (key289, 6), (key289, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key547, 6), (key547, 6), (key547, 6), (key288, 6), (key513, 6), (key513, 6), (key513, 6)]

theorem rawRowCheck19600 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form10 = rawRow19600 := by decide +kernel

def row19600 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

theorem rowCheck19600 : row19600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19600 := by decide +kernel

theorem rowEval19600 (x : Key → ℝ) : Integer.Sparse.eval row19600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19600, Integer.Sparse.eval_collectBalanced, rawRowCheck19600]

def rawRow19601 : Integer.Sparse Key := [(key670, 6), (key670, 6), (key680, 6), (key670, 6), (key515, 6), (key515, 6), (key547, 6), (key289, 6), (key289, 6), (key515, 6), (key515, 6), (key547, 6), (key547, 6), (key289, 6), (key515, 6), (key515, 6), (key513, 6), (key288, 6), (key513, 6), (key513, 6)]

theorem rawRowCheck19601 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form10 = rawRow19601 := by decide +kernel

def row19601 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

theorem rowCheck19601 : row19601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19601 := by decide +kernel

theorem rowEval19601 (x : Key → ℝ) : Integer.Sparse.eval row19601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19601, Integer.Sparse.eval_collectBalanced, rawRowCheck19601]

def rawRow19602 : Integer.Sparse Key := [(key670, 6), (key680, 6), (key670, 6), (key670, 6), (key515, 6), (key547, 6), (key515, 6), (key515, 6), (key547, 6), (key289, 6), (key547, 6), (key289, 6), (key515, 6), (key515, 6), (key289, 6), (key515, 6), (key513, 6), (key513, 6), (key288, 6), (key513, 6)]

theorem rawRowCheck19602 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form10 = rawRow19602 := by decide +kernel

def row19602 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

theorem rowCheck19602 : row19602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19602 := by decide +kernel

theorem rowEval19602 (x : Key → ℝ) : Integer.Sparse.eval row19602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19602, Integer.Sparse.eval_collectBalanced, rawRowCheck19602]

def rawRow19603 : Integer.Sparse Key := [(key680, 6), (key670, 6), (key670, 6), (key670, 6), (key547, 6), (key515, 6), (key515, 6), (key547, 6), (key515, 6), (key547, 6), (key289, 6), (key515, 6), (key289, 6), (key515, 6), (key515, 6), (key289, 6), (key513, 6), (key513, 6), (key513, 6), (key288, 6)]

theorem rawRowCheck19603 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form10 = rawRow19603 := by decide +kernel

def row19603 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

theorem rowCheck19603 : row19603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19603 := by decide +kernel

theorem rowEval19603 (x : Key → ℝ) : Integer.Sparse.eval row19603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19603, Integer.Sparse.eval_collectBalanced, rawRowCheck19603]

def rawRow19604 : Integer.Sparse Key := [(key1251, 6), (key1259, 6), (key1259, 6), (key1271, 6), (key1526, 6), (key1534, 6), (key1534, 6), (key1604, 6), (key1612, 6), (key1604, 6), (key1640, 6), (key1612, 6), (key1640, 6), (key1679, 6), (key1679, 6), (key1693, 6), (key1894, 6), (key1916, 6), (key1916, 6), (key1930, 6)]

theorem rawRowCheck19604 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form0 = rawRow19604 := by decide +kernel

def row19604 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19604 : row19604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19604 := by decide +kernel

theorem rowEval19604 (x : Key → ℝ) : Integer.Sparse.eval row19604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19604, Integer.Sparse.eval_collectBalanced, rawRowCheck19604]

def rawRow19605 : Integer.Sparse Key := [(key1259, 6), (key1251, 6), (key1259, 6), (key1271, 6), (key1534, 6), (key1526, 6), (key1534, 6), (key1612, 6), (key1604, 6), (key1640, 6), (key1604, 6), (key1640, 6), (key1612, 6), (key1679, 6), (key1693, 6), (key1679, 6), (key1894, 6), (key1916, 6), (key1930, 6), (key1916, 6)]

theorem rawRowCheck19605 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form0 = rawRow19605 := by decide +kernel

def row19605 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19605 : row19605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19605 := by decide +kernel

theorem rowEval19605 (x : Key → ℝ) : Integer.Sparse.eval row19605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19605, Integer.Sparse.eval_collectBalanced, rawRowCheck19605]

def rawRow19606 : Integer.Sparse Key := [(key1259, 6), (key1259, 6), (key1251, 6), (key1271, 6), (key1534, 6), (key1534, 6), (key1526, 6), (key1640, 6), (key1640, 6), (key1612, 6), (key1612, 6), (key1604, 6), (key1604, 6), (key1693, 6), (key1679, 6), (key1679, 6), (key1894, 6), (key1930, 6), (key1916, 6), (key1916, 6)]

theorem rawRowCheck19606 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form0 = rawRow19606 := by decide +kernel

def row19606 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19606 : row19606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19606 := by decide +kernel

theorem rowEval19606 (x : Key → ℝ) : Integer.Sparse.eval row19606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19606, Integer.Sparse.eval_collectBalanced, rawRowCheck19606]

def rawRow19607 : Integer.Sparse Key := [(key1251, 6), (key1259, 6), (key1271, 6), (key1259, 6), (key1604, 6), (key1612, 6), (key1679, 6), (key1526, 6), (key1534, 6), (key1604, 6), (key1640, 6), (key1679, 6), (key1693, 6), (key1534, 6), (key1612, 6), (key1640, 6), (key1916, 6), (key1894, 6), (key1916, 6), (key1930, 6)]

theorem rawRowCheck19607 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form0 = rawRow19607 := by decide +kernel

def row19607 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19607 : row19607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19607 := by decide +kernel

theorem rowEval19607 (x : Key → ℝ) : Integer.Sparse.eval row19607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19607, Integer.Sparse.eval_collectBalanced, rawRowCheck19607]

def rawRow19608 : Integer.Sparse Key := [(key1259, 6), (key1251, 6), (key1271, 6), (key1259, 6), (key1612, 6), (key1604, 6), (key1679, 6), (key1534, 6), (key1526, 6), (key1640, 6), (key1604, 6), (key1693, 6), (key1679, 6), (key1534, 6), (key1640, 6), (key1612, 6), (key1916, 6), (key1894, 6), (key1930, 6), (key1916, 6)]

theorem rawRowCheck19608 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form0 = rawRow19608 := by decide +kernel

def row19608 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19608 : row19608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19608 := by decide +kernel

theorem rowEval19608 (x : Key → ℝ) : Integer.Sparse.eval row19608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19608, Integer.Sparse.eval_collectBalanced, rawRowCheck19608]

def rawRow19609 : Integer.Sparse Key := [(key1251, 6), (key1271, 6), (key1259, 6), (key1259, 6), (key1604, 6), (key1679, 6), (key1612, 6), (key1604, 6), (key1679, 6), (key1526, 6), (key1693, 6), (key1534, 6), (key1640, 6), (key1612, 6), (key1534, 6), (key1640, 6), (key1916, 6), (key1916, 6), (key1894, 6), (key1930, 6)]

theorem rawRowCheck19609 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form0 = rawRow19609 := by decide +kernel

def row19609 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19609 : row19609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19609 := by decide +kernel

theorem rowEval19609 (x : Key → ℝ) : Integer.Sparse.eval row19609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19609, Integer.Sparse.eval_collectBalanced, rawRowCheck19609]

def rawRow19610 : Integer.Sparse Key := [(key1271, 6), (key1251, 6), (key1259, 6), (key1259, 6), (key1679, 6), (key1604, 6), (key1612, 6), (key1679, 6), (key1604, 6), (key1693, 6), (key1526, 6), (key1640, 6), (key1534, 6), (key1612, 6), (key1640, 6), (key1534, 6), (key1916, 6), (key1916, 6), (key1930, 6), (key1894, 6)]

theorem rawRowCheck19610 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form0 = rawRow19610 := by decide +kernel

def row19610 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19610 : row19610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19610 := by decide +kernel

theorem rowEval19610 (x : Key → ℝ) : Integer.Sparse.eval row19610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19610, Integer.Sparse.eval_collectBalanced, rawRowCheck19610]

def rawRow19611 : Integer.Sparse Key := [(key1259, 6), (key1271, 6), (key1251, 6), (key1259, 6), (key1612, 6), (key1679, 6), (key1604, 6), (key1640, 6), (key1693, 6), (key1534, 6), (key1679, 6), (key1526, 6), (key1604, 6), (key1640, 6), (key1534, 6), (key1612, 6), (key1916, 6), (key1930, 6), (key1894, 6), (key1916, 6)]

theorem rawRowCheck19611 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form0 = rawRow19611 := by decide +kernel

def row19611 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19611 : row19611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19611 := by decide +kernel

theorem rowEval19611 (x : Key → ℝ) : Integer.Sparse.eval row19611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19611, Integer.Sparse.eval_collectBalanced, rawRowCheck19611]

def rawRow19612 : Integer.Sparse Key := [(key1271, 6), (key1259, 6), (key1251, 6), (key1259, 6), (key1679, 6), (key1612, 6), (key1604, 6), (key1693, 6), (key1640, 6), (key1679, 6), (key1534, 6), (key1604, 6), (key1526, 6), (key1640, 6), (key1612, 6), (key1534, 6), (key1916, 6), (key1930, 6), (key1916, 6), (key1894, 6)]

theorem rawRowCheck19612 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form0 = rawRow19612 := by decide +kernel

def row19612 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19612 : row19612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19612 := by decide +kernel

theorem rowEval19612 (x : Key → ℝ) : Integer.Sparse.eval row19612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19612, Integer.Sparse.eval_collectBalanced, rawRowCheck19612]

def rawRow19613 : Integer.Sparse Key := [(key1259, 6), (key1259, 6), (key1271, 6), (key1251, 6), (key1640, 6), (key1640, 6), (key1693, 6), (key1534, 6), (key1534, 6), (key1612, 6), (key1612, 6), (key1679, 6), (key1679, 6), (key1526, 6), (key1604, 6), (key1604, 6), (key1930, 6), (key1894, 6), (key1916, 6), (key1916, 6)]

theorem rawRowCheck19613 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form0 = rawRow19613 := by decide +kernel

def row19613 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19613 : row19613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19613 := by decide +kernel

theorem rowEval19613 (x : Key → ℝ) : Integer.Sparse.eval row19613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19613, Integer.Sparse.eval_collectBalanced, rawRowCheck19613]

def rawRow19614 : Integer.Sparse Key := [(key1259, 6), (key1271, 6), (key1259, 6), (key1251, 6), (key1640, 6), (key1693, 6), (key1640, 6), (key1612, 6), (key1679, 6), (key1534, 6), (key1679, 6), (key1534, 6), (key1612, 6), (key1604, 6), (key1526, 6), (key1604, 6), (key1930, 6), (key1916, 6), (key1894, 6), (key1916, 6)]

theorem rawRowCheck19614 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form0 = rawRow19614 := by decide +kernel

def row19614 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19614 : row19614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19614 := by decide +kernel

theorem rowEval19614 (x : Key → ℝ) : Integer.Sparse.eval row19614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19614, Integer.Sparse.eval_collectBalanced, rawRowCheck19614]

def rawRow19615 : Integer.Sparse Key := [(key1271, 6), (key1259, 6), (key1259, 6), (key1251, 6), (key1693, 6), (key1640, 6), (key1640, 6), (key1679, 6), (key1612, 6), (key1679, 6), (key1534, 6), (key1612, 6), (key1534, 6), (key1604, 6), (key1604, 6), (key1526, 6), (key1930, 6), (key1916, 6), (key1916, 6), (key1894, 6)]

theorem rawRowCheck19615 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form0 = rawRow19615 := by decide +kernel

def row19615 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19615 : row19615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19615 := by decide +kernel

theorem rowEval19615 (x : Key → ℝ) : Integer.Sparse.eval row19615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19615, Integer.Sparse.eval_collectBalanced, rawRowCheck19615]

def rawRow19616 : Integer.Sparse Key := [(key1526, 6), (key1534, 6), (key1534, 6), (key1894, 6), (key1251, 6), (key1259, 6), (key1259, 6), (key1604, 6), (key1612, 6), (key1604, 6), (key1640, 6), (key1612, 6), (key1640, 6), (key1916, 6), (key1916, 6), (key1930, 6), (key1271, 6), (key1679, 6), (key1679, 6), (key1693, 6)]

theorem rawRowCheck19616 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form0 = rawRow19616 := by decide +kernel

def row19616 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19616 : row19616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19616 := by decide +kernel

theorem rowEval19616 (x : Key → ℝ) : Integer.Sparse.eval row19616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19616, Integer.Sparse.eval_collectBalanced, rawRowCheck19616]

def rawRow19617 : Integer.Sparse Key := [(key1534, 6), (key1526, 6), (key1534, 6), (key1894, 6), (key1259, 6), (key1251, 6), (key1259, 6), (key1612, 6), (key1604, 6), (key1640, 6), (key1604, 6), (key1640, 6), (key1612, 6), (key1916, 6), (key1930, 6), (key1916, 6), (key1271, 6), (key1679, 6), (key1693, 6), (key1679, 6)]

theorem rawRowCheck19617 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form0 = rawRow19617 := by decide +kernel

def row19617 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19617 : row19617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19617 := by decide +kernel

theorem rowEval19617 (x : Key → ℝ) : Integer.Sparse.eval row19617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19617, Integer.Sparse.eval_collectBalanced, rawRowCheck19617]

def rawRow19618 : Integer.Sparse Key := [(key1534, 6), (key1534, 6), (key1526, 6), (key1894, 6), (key1259, 6), (key1259, 6), (key1251, 6), (key1640, 6), (key1640, 6), (key1612, 6), (key1612, 6), (key1604, 6), (key1604, 6), (key1930, 6), (key1916, 6), (key1916, 6), (key1271, 6), (key1693, 6), (key1679, 6), (key1679, 6)]

theorem rawRowCheck19618 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form0 = rawRow19618 := by decide +kernel

def row19618 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19618 : row19618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19618 := by decide +kernel

theorem rowEval19618 (x : Key → ℝ) : Integer.Sparse.eval row19618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19618, Integer.Sparse.eval_collectBalanced, rawRowCheck19618]

def rawRow19619 : Integer.Sparse Key := [(key1526, 6), (key1534, 6), (key1894, 6), (key1534, 6), (key1604, 6), (key1612, 6), (key1916, 6), (key1251, 6), (key1259, 6), (key1604, 6), (key1640, 6), (key1916, 6), (key1930, 6), (key1259, 6), (key1612, 6), (key1640, 6), (key1679, 6), (key1271, 6), (key1679, 6), (key1693, 6)]

theorem rawRowCheck19619 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form0 = rawRow19619 := by decide +kernel

def row19619 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19619 : row19619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19619 := by decide +kernel

theorem rowEval19619 (x : Key → ℝ) : Integer.Sparse.eval row19619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19619, Integer.Sparse.eval_collectBalanced, rawRowCheck19619]

def rawRow19620 : Integer.Sparse Key := [(key1534, 6), (key1526, 6), (key1894, 6), (key1534, 6), (key1612, 6), (key1604, 6), (key1916, 6), (key1259, 6), (key1251, 6), (key1640, 6), (key1604, 6), (key1930, 6), (key1916, 6), (key1259, 6), (key1640, 6), (key1612, 6), (key1679, 6), (key1271, 6), (key1693, 6), (key1679, 6)]

theorem rawRowCheck19620 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form0 = rawRow19620 := by decide +kernel

def row19620 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19620 : row19620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19620 := by decide +kernel

theorem rowEval19620 (x : Key → ℝ) : Integer.Sparse.eval row19620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19620, Integer.Sparse.eval_collectBalanced, rawRowCheck19620]

def rawRow19621 : Integer.Sparse Key := [(key1526, 6), (key1894, 6), (key1534, 6), (key1534, 6), (key1604, 6), (key1916, 6), (key1612, 6), (key1604, 6), (key1916, 6), (key1251, 6), (key1930, 6), (key1259, 6), (key1640, 6), (key1612, 6), (key1259, 6), (key1640, 6), (key1679, 6), (key1679, 6), (key1271, 6), (key1693, 6)]

theorem rawRowCheck19621 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form0 = rawRow19621 := by decide +kernel

def row19621 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19621 : row19621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19621 := by decide +kernel

theorem rowEval19621 (x : Key → ℝ) : Integer.Sparse.eval row19621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19621, Integer.Sparse.eval_collectBalanced, rawRowCheck19621]

def rawRow19622 : Integer.Sparse Key := [(key1894, 6), (key1526, 6), (key1534, 6), (key1534, 6), (key1916, 6), (key1604, 6), (key1612, 6), (key1916, 6), (key1604, 6), (key1930, 6), (key1251, 6), (key1640, 6), (key1259, 6), (key1612, 6), (key1640, 6), (key1259, 6), (key1679, 6), (key1679, 6), (key1693, 6), (key1271, 6)]

theorem rawRowCheck19622 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form0 = rawRow19622 := by decide +kernel

def row19622 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19622 : row19622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19622 := by decide +kernel

theorem rowEval19622 (x : Key → ℝ) : Integer.Sparse.eval row19622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19622, Integer.Sparse.eval_collectBalanced, rawRowCheck19622]

def rawRow19623 : Integer.Sparse Key := [(key1534, 6), (key1894, 6), (key1526, 6), (key1534, 6), (key1612, 6), (key1916, 6), (key1604, 6), (key1640, 6), (key1930, 6), (key1259, 6), (key1916, 6), (key1251, 6), (key1604, 6), (key1640, 6), (key1259, 6), (key1612, 6), (key1679, 6), (key1693, 6), (key1271, 6), (key1679, 6)]

theorem rawRowCheck19623 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form0 = rawRow19623 := by decide +kernel

def row19623 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19623 : row19623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19623 := by decide +kernel

theorem rowEval19623 (x : Key → ℝ) : Integer.Sparse.eval row19623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19623, Integer.Sparse.eval_collectBalanced, rawRowCheck19623]

def rawRow19624 : Integer.Sparse Key := [(key1894, 6), (key1534, 6), (key1526, 6), (key1534, 6), (key1916, 6), (key1612, 6), (key1604, 6), (key1930, 6), (key1640, 6), (key1916, 6), (key1259, 6), (key1604, 6), (key1251, 6), (key1640, 6), (key1612, 6), (key1259, 6), (key1679, 6), (key1693, 6), (key1679, 6), (key1271, 6)]

theorem rawRowCheck19624 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form0 = rawRow19624 := by decide +kernel

def row19624 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19624 : row19624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19624 := by decide +kernel

theorem rowEval19624 (x : Key → ℝ) : Integer.Sparse.eval row19624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19624, Integer.Sparse.eval_collectBalanced, rawRowCheck19624]

def rawRow19625 : Integer.Sparse Key := [(key1534, 6), (key1534, 6), (key1894, 6), (key1526, 6), (key1640, 6), (key1640, 6), (key1930, 6), (key1259, 6), (key1259, 6), (key1612, 6), (key1612, 6), (key1916, 6), (key1916, 6), (key1251, 6), (key1604, 6), (key1604, 6), (key1693, 6), (key1271, 6), (key1679, 6), (key1679, 6)]

theorem rawRowCheck19625 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19625 := by decide +kernel

def row19625 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19625 : row19625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19625 := by decide +kernel

theorem rowEval19625 (x : Key → ℝ) : Integer.Sparse.eval row19625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19625, Integer.Sparse.eval_collectBalanced, rawRowCheck19625]

def rawRow19626 : Integer.Sparse Key := [(key1534, 6), (key1894, 6), (key1534, 6), (key1526, 6), (key1640, 6), (key1930, 6), (key1640, 6), (key1612, 6), (key1916, 6), (key1259, 6), (key1916, 6), (key1259, 6), (key1612, 6), (key1604, 6), (key1251, 6), (key1604, 6), (key1693, 6), (key1679, 6), (key1271, 6), (key1679, 6)]

theorem rawRowCheck19626 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19626 := by decide +kernel

def row19626 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19626 : row19626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19626 := by decide +kernel

theorem rowEval19626 (x : Key → ℝ) : Integer.Sparse.eval row19626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19626, Integer.Sparse.eval_collectBalanced, rawRowCheck19626]

def rawRow19627 : Integer.Sparse Key := [(key1894, 6), (key1534, 6), (key1534, 6), (key1526, 6), (key1930, 6), (key1640, 6), (key1640, 6), (key1916, 6), (key1612, 6), (key1916, 6), (key1259, 6), (key1612, 6), (key1259, 6), (key1604, 6), (key1604, 6), (key1251, 6), (key1693, 6), (key1679, 6), (key1679, 6), (key1271, 6)]

theorem rawRowCheck19627 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19627 := by decide +kernel

def row19627 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19627 : row19627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19627 := by decide +kernel

theorem rowEval19627 (x : Key → ℝ) : Integer.Sparse.eval row19627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19627, Integer.Sparse.eval_collectBalanced, rawRowCheck19627]

def rawRow19628 : Integer.Sparse Key := [(key1604, 6), (key1612, 6), (key1679, 6), (key1916, 6), (key1251, 6), (key1259, 6), (key1271, 6), (key1526, 6), (key1534, 6), (key1604, 6), (key1640, 6), (key1679, 6), (key1693, 6), (key1894, 6), (key1916, 6), (key1930, 6), (key1259, 6), (key1534, 6), (key1612, 6), (key1640, 6)]

theorem rawRowCheck19628 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form0 = rawRow19628 := by decide +kernel

def row19628 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19628 : row19628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19628 := by decide +kernel

theorem rowEval19628 (x : Key → ℝ) : Integer.Sparse.eval row19628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19628, Integer.Sparse.eval_collectBalanced, rawRowCheck19628]

def rawRow19629 : Integer.Sparse Key := [(key1612, 6), (key1604, 6), (key1679, 6), (key1916, 6), (key1259, 6), (key1251, 6), (key1271, 6), (key1534, 6), (key1526, 6), (key1640, 6), (key1604, 6), (key1693, 6), (key1679, 6), (key1894, 6), (key1930, 6), (key1916, 6), (key1259, 6), (key1534, 6), (key1640, 6), (key1612, 6)]

theorem rawRowCheck19629 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form0 = rawRow19629 := by decide +kernel

def row19629 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19629 : row19629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19629 := by decide +kernel

theorem rowEval19629 (x : Key → ℝ) : Integer.Sparse.eval row19629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19629, Integer.Sparse.eval_collectBalanced, rawRowCheck19629]

def rawRow19630 : Integer.Sparse Key := [(key1604, 6), (key1679, 6), (key1612, 6), (key1916, 6), (key1251, 6), (key1271, 6), (key1259, 6), (key1604, 6), (key1679, 6), (key1526, 6), (key1693, 6), (key1534, 6), (key1640, 6), (key1916, 6), (key1894, 6), (key1930, 6), (key1259, 6), (key1612, 6), (key1534, 6), (key1640, 6)]

theorem rawRowCheck19630 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form0 = rawRow19630 := by decide +kernel

def row19630 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19630 : row19630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19630 := by decide +kernel

theorem rowEval19630 (x : Key → ℝ) : Integer.Sparse.eval row19630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19630, Integer.Sparse.eval_collectBalanced, rawRowCheck19630]

def rawRow19631 : Integer.Sparse Key := [(key1679, 6), (key1604, 6), (key1612, 6), (key1916, 6), (key1271, 6), (key1251, 6), (key1259, 6), (key1679, 6), (key1604, 6), (key1693, 6), (key1526, 6), (key1640, 6), (key1534, 6), (key1916, 6), (key1930, 6), (key1894, 6), (key1259, 6), (key1612, 6), (key1640, 6), (key1534, 6)]

theorem rawRowCheck19631 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form0 = rawRow19631 := by decide +kernel

def row19631 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19631 : row19631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19631 := by decide +kernel

theorem rowEval19631 (x : Key → ℝ) : Integer.Sparse.eval row19631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19631, Integer.Sparse.eval_collectBalanced, rawRowCheck19631]

def rawRow19632 : Integer.Sparse Key := [(key1612, 6), (key1679, 6), (key1604, 6), (key1916, 6), (key1259, 6), (key1271, 6), (key1251, 6), (key1640, 6), (key1693, 6), (key1534, 6), (key1679, 6), (key1526, 6), (key1604, 6), (key1930, 6), (key1894, 6), (key1916, 6), (key1259, 6), (key1640, 6), (key1534, 6), (key1612, 6)]

theorem rawRowCheck19632 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form0 = rawRow19632 := by decide +kernel

def row19632 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19632 : row19632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19632 := by decide +kernel

theorem rowEval19632 (x : Key → ℝ) : Integer.Sparse.eval row19632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19632, Integer.Sparse.eval_collectBalanced, rawRowCheck19632]

def rawRow19633 : Integer.Sparse Key := [(key1679, 6), (key1612, 6), (key1604, 6), (key1916, 6), (key1271, 6), (key1259, 6), (key1251, 6), (key1693, 6), (key1640, 6), (key1679, 6), (key1534, 6), (key1604, 6), (key1526, 6), (key1930, 6), (key1916, 6), (key1894, 6), (key1259, 6), (key1640, 6), (key1612, 6), (key1534, 6)]

theorem rawRowCheck19633 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form0 = rawRow19633 := by decide +kernel

def row19633 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19633 : row19633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19633 := by decide +kernel

theorem rowEval19633 (x : Key → ℝ) : Integer.Sparse.eval row19633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19633, Integer.Sparse.eval_collectBalanced, rawRowCheck19633]

def rawRow19634 : Integer.Sparse Key := [(key1604, 6), (key1612, 6), (key1916, 6), (key1679, 6), (key1526, 6), (key1534, 6), (key1894, 6), (key1251, 6), (key1259, 6), (key1604, 6), (key1640, 6), (key1916, 6), (key1930, 6), (key1271, 6), (key1679, 6), (key1693, 6), (key1534, 6), (key1259, 6), (key1612, 6), (key1640, 6)]

theorem rawRowCheck19634 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form0 = rawRow19634 := by decide +kernel

def row19634 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19634 : row19634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19634 := by decide +kernel

theorem rowEval19634 (x : Key → ℝ) : Integer.Sparse.eval row19634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19634, Integer.Sparse.eval_collectBalanced, rawRowCheck19634]

def rawRow19635 : Integer.Sparse Key := [(key1612, 6), (key1604, 6), (key1916, 6), (key1679, 6), (key1534, 6), (key1526, 6), (key1894, 6), (key1259, 6), (key1251, 6), (key1640, 6), (key1604, 6), (key1930, 6), (key1916, 6), (key1271, 6), (key1693, 6), (key1679, 6), (key1534, 6), (key1259, 6), (key1640, 6), (key1612, 6)]

theorem rawRowCheck19635 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form0 = rawRow19635 := by decide +kernel

def row19635 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19635 : row19635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19635 := by decide +kernel

theorem rowEval19635 (x : Key → ℝ) : Integer.Sparse.eval row19635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19635, Integer.Sparse.eval_collectBalanced, rawRowCheck19635]

def rawRow19636 : Integer.Sparse Key := [(key1604, 6), (key1916, 6), (key1612, 6), (key1679, 6), (key1526, 6), (key1894, 6), (key1534, 6), (key1604, 6), (key1916, 6), (key1251, 6), (key1930, 6), (key1259, 6), (key1640, 6), (key1679, 6), (key1271, 6), (key1693, 6), (key1534, 6), (key1612, 6), (key1259, 6), (key1640, 6)]

theorem rawRowCheck19636 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form0 = rawRow19636 := by decide +kernel

def row19636 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19636 : row19636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19636 := by decide +kernel

theorem rowEval19636 (x : Key → ℝ) : Integer.Sparse.eval row19636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19636, Integer.Sparse.eval_collectBalanced, rawRowCheck19636]

def rawRow19637 : Integer.Sparse Key := [(key1916, 6), (key1604, 6), (key1612, 6), (key1679, 6), (key1894, 6), (key1526, 6), (key1534, 6), (key1916, 6), (key1604, 6), (key1930, 6), (key1251, 6), (key1640, 6), (key1259, 6), (key1679, 6), (key1693, 6), (key1271, 6), (key1534, 6), (key1612, 6), (key1640, 6), (key1259, 6)]

theorem rawRowCheck19637 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form0 = rawRow19637 := by decide +kernel

def row19637 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19637 : row19637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19637 := by decide +kernel

theorem rowEval19637 (x : Key → ℝ) : Integer.Sparse.eval row19637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19637, Integer.Sparse.eval_collectBalanced, rawRowCheck19637]

def rawRow19638 : Integer.Sparse Key := [(key1612, 6), (key1916, 6), (key1604, 6), (key1679, 6), (key1534, 6), (key1894, 6), (key1526, 6), (key1640, 6), (key1930, 6), (key1259, 6), (key1916, 6), (key1251, 6), (key1604, 6), (key1693, 6), (key1271, 6), (key1679, 6), (key1534, 6), (key1640, 6), (key1259, 6), (key1612, 6)]

theorem rawRowCheck19638 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form0 = rawRow19638 := by decide +kernel

def row19638 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19638 : row19638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19638 := by decide +kernel

theorem rowEval19638 (x : Key → ℝ) : Integer.Sparse.eval row19638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19638, Integer.Sparse.eval_collectBalanced, rawRowCheck19638]

def rawRow19639 : Integer.Sparse Key := [(key1916, 6), (key1612, 6), (key1604, 6), (key1679, 6), (key1894, 6), (key1534, 6), (key1526, 6), (key1930, 6), (key1640, 6), (key1916, 6), (key1259, 6), (key1604, 6), (key1251, 6), (key1693, 6), (key1679, 6), (key1271, 6), (key1534, 6), (key1640, 6), (key1612, 6), (key1259, 6)]

theorem rawRowCheck19639 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form0 = rawRow19639 := by decide +kernel

def row19639 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19639 : row19639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19639 := by decide +kernel

theorem rowEval19639 (x : Key → ℝ) : Integer.Sparse.eval row19639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19639, Integer.Sparse.eval_collectBalanced, rawRowCheck19639]

def rawRow19640 : Integer.Sparse Key := [(key1604, 6), (key1679, 6), (key1916, 6), (key1612, 6), (key1604, 6), (key1679, 6), (key1916, 6), (key1251, 6), (key1271, 6), (key1526, 6), (key1693, 6), (key1894, 6), (key1930, 6), (key1259, 6), (key1534, 6), (key1640, 6), (key1612, 6), (key1259, 6), (key1534, 6), (key1640, 6)]

theorem rawRowCheck19640 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form0 = rawRow19640 := by decide +kernel

def row19640 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19640 : row19640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19640 := by decide +kernel

theorem rowEval19640 (x : Key → ℝ) : Integer.Sparse.eval row19640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19640, Integer.Sparse.eval_collectBalanced, rawRowCheck19640]

def rawRow19641 : Integer.Sparse Key := [(key1679, 6), (key1604, 6), (key1916, 6), (key1612, 6), (key1679, 6), (key1604, 6), (key1916, 6), (key1271, 6), (key1251, 6), (key1693, 6), (key1526, 6), (key1930, 6), (key1894, 6), (key1259, 6), (key1640, 6), (key1534, 6), (key1612, 6), (key1259, 6), (key1640, 6), (key1534, 6)]

theorem rawRowCheck19641 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form0 = rawRow19641 := by decide +kernel

def row19641 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19641 : row19641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19641 := by decide +kernel

theorem rowEval19641 (x : Key → ℝ) : Integer.Sparse.eval row19641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19641, Integer.Sparse.eval_collectBalanced, rawRowCheck19641]

def rawRow19642 : Integer.Sparse Key := [(key1604, 6), (key1916, 6), (key1679, 6), (key1612, 6), (key1604, 6), (key1916, 6), (key1679, 6), (key1526, 6), (key1894, 6), (key1251, 6), (key1930, 6), (key1271, 6), (key1693, 6), (key1534, 6), (key1259, 6), (key1640, 6), (key1612, 6), (key1534, 6), (key1259, 6), (key1640, 6)]

theorem rawRowCheck19642 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form0 = rawRow19642 := by decide +kernel

def row19642 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19642 : row19642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19642 := by decide +kernel

theorem rowEval19642 (x : Key → ℝ) : Integer.Sparse.eval row19642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19642, Integer.Sparse.eval_collectBalanced, rawRowCheck19642]

def rawRow19643 : Integer.Sparse Key := [(key1916, 6), (key1604, 6), (key1679, 6), (key1612, 6), (key1916, 6), (key1604, 6), (key1679, 6), (key1894, 6), (key1526, 6), (key1930, 6), (key1251, 6), (key1693, 6), (key1271, 6), (key1534, 6), (key1640, 6), (key1259, 6), (key1612, 6), (key1534, 6), (key1640, 6), (key1259, 6)]

theorem rawRowCheck19643 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form0 = rawRow19643 := by decide +kernel

def row19643 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19643 : row19643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19643 := by decide +kernel

theorem rowEval19643 (x : Key → ℝ) : Integer.Sparse.eval row19643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19643, Integer.Sparse.eval_collectBalanced, rawRowCheck19643]

def rawRow19644 : Integer.Sparse Key := [(key1679, 6), (key1916, 6), (key1604, 6), (key1612, 6), (key1679, 6), (key1916, 6), (key1604, 6), (key1693, 6), (key1930, 6), (key1271, 6), (key1894, 6), (key1251, 6), (key1526, 6), (key1640, 6), (key1259, 6), (key1534, 6), (key1612, 6), (key1640, 6), (key1259, 6), (key1534, 6)]

theorem rawRowCheck19644 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form0 = rawRow19644 := by decide +kernel

def row19644 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19644 : row19644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19644 := by decide +kernel

theorem rowEval19644 (x : Key → ℝ) : Integer.Sparse.eval row19644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19644, Integer.Sparse.eval_collectBalanced, rawRowCheck19644]

def rawRow19645 : Integer.Sparse Key := [(key1916, 6), (key1679, 6), (key1604, 6), (key1612, 6), (key1916, 6), (key1679, 6), (key1604, 6), (key1930, 6), (key1693, 6), (key1894, 6), (key1271, 6), (key1526, 6), (key1251, 6), (key1640, 6), (key1534, 6), (key1259, 6), (key1612, 6), (key1640, 6), (key1534, 6), (key1259, 6)]

theorem rawRowCheck19645 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form0 = rawRow19645 := by decide +kernel

def row19645 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19645 : row19645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19645 := by decide +kernel

theorem rowEval19645 (x : Key → ℝ) : Integer.Sparse.eval row19645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19645, Integer.Sparse.eval_collectBalanced, rawRowCheck19645]

def rawRow19646 : Integer.Sparse Key := [(key1612, 6), (key1679, 6), (key1916, 6), (key1604, 6), (key1640, 6), (key1693, 6), (key1930, 6), (key1259, 6), (key1271, 6), (key1534, 6), (key1679, 6), (key1894, 6), (key1916, 6), (key1251, 6), (key1526, 6), (key1604, 6), (key1640, 6), (key1259, 6), (key1534, 6), (key1612, 6)]

theorem rawRowCheck19646 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form0 = rawRow19646 := by decide +kernel

def row19646 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19646 : row19646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19646 := by decide +kernel

theorem rowEval19646 (x : Key → ℝ) : Integer.Sparse.eval row19646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19646, Integer.Sparse.eval_collectBalanced, rawRowCheck19646]

def rawRow19647 : Integer.Sparse Key := [(key1679, 6), (key1612, 6), (key1916, 6), (key1604, 6), (key1693, 6), (key1640, 6), (key1930, 6), (key1271, 6), (key1259, 6), (key1679, 6), (key1534, 6), (key1916, 6), (key1894, 6), (key1251, 6), (key1604, 6), (key1526, 6), (key1640, 6), (key1259, 6), (key1612, 6), (key1534, 6)]

theorem rawRowCheck19647 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form0 = rawRow19647 := by decide +kernel

def row19647 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19647 : row19647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19647 := by decide +kernel

theorem rowEval19647 (x : Key → ℝ) : Integer.Sparse.eval row19647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19647, Integer.Sparse.eval_collectBalanced, rawRowCheck19647]

def rawRow19648 : Integer.Sparse Key := [(key1612, 6), (key1916, 6), (key1679, 6), (key1604, 6), (key1640, 6), (key1930, 6), (key1693, 6), (key1534, 6), (key1894, 6), (key1259, 6), (key1916, 6), (key1271, 6), (key1679, 6), (key1526, 6), (key1251, 6), (key1604, 6), (key1640, 6), (key1534, 6), (key1259, 6), (key1612, 6)]

theorem rawRowCheck19648 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form0 = rawRow19648 := by decide +kernel

def row19648 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19648 : row19648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19648 := by decide +kernel

theorem rowEval19648 (x : Key → ℝ) : Integer.Sparse.eval row19648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19648, Integer.Sparse.eval_collectBalanced, rawRowCheck19648]

def rawRow19649 : Integer.Sparse Key := [(key1916, 6), (key1612, 6), (key1679, 6), (key1604, 6), (key1930, 6), (key1640, 6), (key1693, 6), (key1894, 6), (key1534, 6), (key1916, 6), (key1259, 6), (key1679, 6), (key1271, 6), (key1526, 6), (key1604, 6), (key1251, 6), (key1640, 6), (key1534, 6), (key1612, 6), (key1259, 6)]

theorem rawRowCheck19649 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form0 = rawRow19649 := by decide +kernel

def row19649 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19649 : row19649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19649 := by decide +kernel

theorem rowEval19649 (x : Key → ℝ) : Integer.Sparse.eval row19649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19649, Integer.Sparse.eval_collectBalanced, rawRowCheck19649]

def rawRow19650 : Integer.Sparse Key := [(key1679, 6), (key1916, 6), (key1612, 6), (key1604, 6), (key1693, 6), (key1930, 6), (key1640, 6), (key1679, 6), (key1916, 6), (key1271, 6), (key1894, 6), (key1259, 6), (key1534, 6), (key1604, 6), (key1251, 6), (key1526, 6), (key1640, 6), (key1612, 6), (key1259, 6), (key1534, 6)]

theorem rawRowCheck19650 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form0 = rawRow19650 := by decide +kernel

def row19650 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19650 : row19650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19650 := by decide +kernel

theorem rowEval19650 (x : Key → ℝ) : Integer.Sparse.eval row19650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19650, Integer.Sparse.eval_collectBalanced, rawRowCheck19650]

def rawRow19651 : Integer.Sparse Key := [(key1916, 6), (key1679, 6), (key1612, 6), (key1604, 6), (key1930, 6), (key1693, 6), (key1640, 6), (key1916, 6), (key1679, 6), (key1894, 6), (key1271, 6), (key1534, 6), (key1259, 6), (key1604, 6), (key1526, 6), (key1251, 6), (key1640, 6), (key1612, 6), (key1534, 6), (key1259, 6)]

theorem rawRowCheck19651 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form0 = rawRow19651 := by decide +kernel

def row19651 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19651 : row19651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19651 := by decide +kernel

theorem rowEval19651 (x : Key → ℝ) : Integer.Sparse.eval row19651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19651, Integer.Sparse.eval_collectBalanced, rawRowCheck19651]

def rawRow19652 : Integer.Sparse Key := [(key1640, 6), (key1640, 6), (key1693, 6), (key1930, 6), (key1259, 6), (key1259, 6), (key1271, 6), (key1534, 6), (key1534, 6), (key1612, 6), (key1612, 6), (key1679, 6), (key1679, 6), (key1894, 6), (key1916, 6), (key1916, 6), (key1251, 6), (key1526, 6), (key1604, 6), (key1604, 6)]

theorem rawRowCheck19652 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form0 = rawRow19652 := by decide +kernel

def row19652 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19652 : row19652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19652 := by decide +kernel

theorem rowEval19652 (x : Key → ℝ) : Integer.Sparse.eval row19652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19652, Integer.Sparse.eval_collectBalanced, rawRowCheck19652]

def rawRow19653 : Integer.Sparse Key := [(key1640, 6), (key1693, 6), (key1640, 6), (key1930, 6), (key1259, 6), (key1271, 6), (key1259, 6), (key1612, 6), (key1679, 6), (key1534, 6), (key1679, 6), (key1534, 6), (key1612, 6), (key1916, 6), (key1894, 6), (key1916, 6), (key1251, 6), (key1604, 6), (key1526, 6), (key1604, 6)]

theorem rawRowCheck19653 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form0 = rawRow19653 := by decide +kernel

def row19653 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19653 : row19653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19653 := by decide +kernel

theorem rowEval19653 (x : Key → ℝ) : Integer.Sparse.eval row19653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19653, Integer.Sparse.eval_collectBalanced, rawRowCheck19653]

def rawRow19654 : Integer.Sparse Key := [(key1693, 6), (key1640, 6), (key1640, 6), (key1930, 6), (key1271, 6), (key1259, 6), (key1259, 6), (key1679, 6), (key1612, 6), (key1679, 6), (key1534, 6), (key1612, 6), (key1534, 6), (key1916, 6), (key1916, 6), (key1894, 6), (key1251, 6), (key1604, 6), (key1604, 6), (key1526, 6)]

theorem rawRowCheck19654 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form0 = rawRow19654 := by decide +kernel

def row19654 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19654 : row19654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19654 := by decide +kernel

theorem rowEval19654 (x : Key → ℝ) : Integer.Sparse.eval row19654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19654, Integer.Sparse.eval_collectBalanced, rawRowCheck19654]

def rawRow19655 : Integer.Sparse Key := [(key1640, 6), (key1640, 6), (key1930, 6), (key1693, 6), (key1534, 6), (key1534, 6), (key1894, 6), (key1259, 6), (key1259, 6), (key1612, 6), (key1612, 6), (key1916, 6), (key1916, 6), (key1271, 6), (key1679, 6), (key1679, 6), (key1526, 6), (key1251, 6), (key1604, 6), (key1604, 6)]

theorem rawRowCheck19655 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19655 := by decide +kernel

def row19655 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19655 : row19655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19655 := by decide +kernel

theorem rowEval19655 (x : Key → ℝ) : Integer.Sparse.eval row19655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19655, Integer.Sparse.eval_collectBalanced, rawRowCheck19655]

def rawRow19656 : Integer.Sparse Key := [(key1640, 6), (key1930, 6), (key1640, 6), (key1693, 6), (key1534, 6), (key1894, 6), (key1534, 6), (key1612, 6), (key1916, 6), (key1259, 6), (key1916, 6), (key1259, 6), (key1612, 6), (key1679, 6), (key1271, 6), (key1679, 6), (key1526, 6), (key1604, 6), (key1251, 6), (key1604, 6)]

theorem rawRowCheck19656 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19656 := by decide +kernel

def row19656 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19656 : row19656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19656 := by decide +kernel

theorem rowEval19656 (x : Key → ℝ) : Integer.Sparse.eval row19656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19656, Integer.Sparse.eval_collectBalanced, rawRowCheck19656]

def rawRow19657 : Integer.Sparse Key := [(key1930, 6), (key1640, 6), (key1640, 6), (key1693, 6), (key1894, 6), (key1534, 6), (key1534, 6), (key1916, 6), (key1612, 6), (key1916, 6), (key1259, 6), (key1612, 6), (key1259, 6), (key1679, 6), (key1679, 6), (key1271, 6), (key1526, 6), (key1604, 6), (key1604, 6), (key1251, 6)]

theorem rawRowCheck19657 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19657 := by decide +kernel

def row19657 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19657 : row19657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19657 := by decide +kernel

theorem rowEval19657 (x : Key → ℝ) : Integer.Sparse.eval row19657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19657, Integer.Sparse.eval_collectBalanced, rawRowCheck19657]

def rawRow19658 : Integer.Sparse Key := [(key1640, 6), (key1693, 6), (key1930, 6), (key1640, 6), (key1612, 6), (key1679, 6), (key1916, 6), (key1259, 6), (key1271, 6), (key1534, 6), (key1679, 6), (key1894, 6), (key1916, 6), (key1259, 6), (key1534, 6), (key1612, 6), (key1604, 6), (key1251, 6), (key1526, 6), (key1604, 6)]

theorem rawRowCheck19658 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form0 = rawRow19658 := by decide +kernel

def row19658 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19658 : row19658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19658 := by decide +kernel

theorem rowEval19658 (x : Key → ℝ) : Integer.Sparse.eval row19658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19658, Integer.Sparse.eval_collectBalanced, rawRowCheck19658]

def rawRow19659 : Integer.Sparse Key := [(key1693, 6), (key1640, 6), (key1930, 6), (key1640, 6), (key1679, 6), (key1612, 6), (key1916, 6), (key1271, 6), (key1259, 6), (key1679, 6), (key1534, 6), (key1916, 6), (key1894, 6), (key1259, 6), (key1612, 6), (key1534, 6), (key1604, 6), (key1251, 6), (key1604, 6), (key1526, 6)]

theorem rawRowCheck19659 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form0 = rawRow19659 := by decide +kernel

def row19659 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19659 : row19659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19659 := by decide +kernel

theorem rowEval19659 (x : Key → ℝ) : Integer.Sparse.eval row19659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19659, Integer.Sparse.eval_collectBalanced, rawRowCheck19659]

def rawRow19660 : Integer.Sparse Key := [(key1640, 6), (key1930, 6), (key1693, 6), (key1640, 6), (key1612, 6), (key1916, 6), (key1679, 6), (key1534, 6), (key1894, 6), (key1259, 6), (key1916, 6), (key1271, 6), (key1679, 6), (key1534, 6), (key1259, 6), (key1612, 6), (key1604, 6), (key1526, 6), (key1251, 6), (key1604, 6)]

theorem rawRowCheck19660 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form0 = rawRow19660 := by decide +kernel

def row19660 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19660 : row19660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19660 := by decide +kernel

theorem rowEval19660 (x : Key → ℝ) : Integer.Sparse.eval row19660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19660, Integer.Sparse.eval_collectBalanced, rawRowCheck19660]

def rawRow19661 : Integer.Sparse Key := [(key1930, 6), (key1640, 6), (key1693, 6), (key1640, 6), (key1916, 6), (key1612, 6), (key1679, 6), (key1894, 6), (key1534, 6), (key1916, 6), (key1259, 6), (key1679, 6), (key1271, 6), (key1534, 6), (key1612, 6), (key1259, 6), (key1604, 6), (key1526, 6), (key1604, 6), (key1251, 6)]

theorem rawRowCheck19661 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form0 = rawRow19661 := by decide +kernel

def row19661 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19661 : row19661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19661 := by decide +kernel

theorem rowEval19661 (x : Key → ℝ) : Integer.Sparse.eval row19661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19661, Integer.Sparse.eval_collectBalanced, rawRowCheck19661]

def rawRow19662 : Integer.Sparse Key := [(key1693, 6), (key1930, 6), (key1640, 6), (key1640, 6), (key1679, 6), (key1916, 6), (key1612, 6), (key1679, 6), (key1916, 6), (key1271, 6), (key1894, 6), (key1259, 6), (key1534, 6), (key1612, 6), (key1259, 6), (key1534, 6), (key1604, 6), (key1604, 6), (key1251, 6), (key1526, 6)]

theorem rawRowCheck19662 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form0 = rawRow19662 := by decide +kernel

def row19662 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19662 : row19662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19662 := by decide +kernel

theorem rowEval19662 (x : Key → ℝ) : Integer.Sparse.eval row19662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19662, Integer.Sparse.eval_collectBalanced, rawRowCheck19662]

def rawRow19663 : Integer.Sparse Key := [(key1930, 6), (key1693, 6), (key1640, 6), (key1640, 6), (key1916, 6), (key1679, 6), (key1612, 6), (key1916, 6), (key1679, 6), (key1894, 6), (key1271, 6), (key1534, 6), (key1259, 6), (key1612, 6), (key1534, 6), (key1259, 6), (key1604, 6), (key1604, 6), (key1526, 6), (key1251, 6)]

theorem rawRowCheck19663 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form0 = rawRow19663 := by decide +kernel

def row19663 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

theorem rowCheck19663 : row19663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19663 := by decide +kernel

theorem rowEval19663 (x : Key → ℝ) : Integer.Sparse.eval row19663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19663, Integer.Sparse.eval_collectBalanced, rawRowCheck19663]

def rawRow19664 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 24), (key428, 24), (key456, 24)]

theorem rawRowCheck19664 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form1 = rawRow19664 := by decide +kernel

def row19664 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19664 : row19664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19664 := by decide +kernel

theorem rowEval19664 (x : Key → ℝ) : Integer.Sparse.eval row19664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19664, Integer.Sparse.eval_collectBalanced, rawRowCheck19664]

def rawRow19665 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 24), (key456, 24), (key428, 24)]

theorem rawRowCheck19665 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form1 = rawRow19665 := by decide +kernel

def row19665 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19665 : row19665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19665 := by decide +kernel

theorem rowEval19665 (x : Key → ℝ) : Integer.Sparse.eval row19665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19665, Integer.Sparse.eval_collectBalanced, rawRowCheck19665]

def rawRow19666 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key456, 24), (key428, 24), (key428, 24)]

theorem rawRowCheck19666 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form1 = rawRow19666 := by decide +kernel

def row19666 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19666 : row19666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19666 := by decide +kernel

theorem rowEval19666 (x : Key → ℝ) : Integer.Sparse.eval row19666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19666, Integer.Sparse.eval_collectBalanced, rawRowCheck19666]

def rawRow19667 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key377, 24), (key428, 24), (key456, 24)]

theorem rawRowCheck19667 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form1 = rawRow19667 := by decide +kernel

def row19667 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19667 : row19667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19667 := by decide +kernel

theorem rowEval19667 (x : Key → ℝ) : Integer.Sparse.eval row19667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19667, Integer.Sparse.eval_collectBalanced, rawRowCheck19667]

def rawRow19668 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key377, 24), (key456, 24), (key428, 24)]

theorem rawRowCheck19668 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form1 = rawRow19668 := by decide +kernel

def row19668 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19668 : row19668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19668 := by decide +kernel

theorem rowEval19668 (x : Key → ℝ) : Integer.Sparse.eval row19668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19668, Integer.Sparse.eval_collectBalanced, rawRowCheck19668]

def rawRow19669 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key428, 24), (key377, 24), (key456, 24)]

theorem rawRowCheck19669 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form1 = rawRow19669 := by decide +kernel

def row19669 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19669 : row19669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19669 := by decide +kernel

theorem rowEval19669 (x : Key → ℝ) : Integer.Sparse.eval row19669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19669, Integer.Sparse.eval_collectBalanced, rawRowCheck19669]

def rawRow19670 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key428, 24), (key456, 24), (key377, 24)]

theorem rawRowCheck19670 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form1 = rawRow19670 := by decide +kernel

def row19670 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19670 : row19670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19670 := by decide +kernel

theorem rowEval19670 (x : Key → ℝ) : Integer.Sparse.eval row19670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19670, Integer.Sparse.eval_collectBalanced, rawRowCheck19670]

def rawRow19671 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key456, 24), (key377, 24), (key428, 24)]

theorem rawRowCheck19671 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form1 = rawRow19671 := by decide +kernel

def row19671 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19671 : row19671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19671 := by decide +kernel

theorem rowEval19671 (x : Key → ℝ) : Integer.Sparse.eval row19671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19671, Integer.Sparse.eval_collectBalanced, rawRowCheck19671]

def rawRow19672 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key456, 24), (key428, 24), (key377, 24)]

theorem rawRowCheck19672 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form1 = rawRow19672 := by decide +kernel

def row19672 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19672 : row19672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19672 := by decide +kernel

theorem rowEval19672 (x : Key → ℝ) : Integer.Sparse.eval row19672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19672, Integer.Sparse.eval_collectBalanced, rawRowCheck19672]

def rawRow19673 : Integer.Sparse Key := [(key208, 24), (key456, 24), (key377, 24), (key428, 24), (key428, 24)]

theorem rawRowCheck19673 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form1 = rawRow19673 := by decide +kernel

def row19673 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19673 : row19673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19673 := by decide +kernel

theorem rowEval19673 (x : Key → ℝ) : Integer.Sparse.eval row19673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19673, Integer.Sparse.eval_collectBalanced, rawRowCheck19673]

def rawRow19674 : Integer.Sparse Key := [(key208, 24), (key456, 24), (key428, 24), (key377, 24), (key428, 24)]

theorem rawRowCheck19674 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form1 = rawRow19674 := by decide +kernel

def row19674 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19674 : row19674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19674 := by decide +kernel

theorem rowEval19674 (x : Key → ℝ) : Integer.Sparse.eval row19674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19674, Integer.Sparse.eval_collectBalanced, rawRowCheck19674]

def rawRow19675 : Integer.Sparse Key := [(key208, 24), (key456, 24), (key428, 24), (key428, 24), (key377, 24)]

theorem rawRowCheck19675 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form1 = rawRow19675 := by decide +kernel

def row19675 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19675 : row19675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19675 := by decide +kernel

theorem rowEval19675 (x : Key → ℝ) : Integer.Sparse.eval row19675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19675, Integer.Sparse.eval_collectBalanced, rawRowCheck19675]

def rawRow19676 : Integer.Sparse Key := [(key377, 24), (key208, 24), (key428, 24), (key428, 24), (key456, 24)]

theorem rawRowCheck19676 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form1 = rawRow19676 := by decide +kernel

def row19676 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19676 : row19676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19676 := by decide +kernel

theorem rowEval19676 (x : Key → ℝ) : Integer.Sparse.eval row19676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19676, Integer.Sparse.eval_collectBalanced, rawRowCheck19676]

def rawRow19677 : Integer.Sparse Key := [(key377, 24), (key208, 24), (key428, 24), (key456, 24), (key428, 24)]

theorem rawRowCheck19677 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form1 = rawRow19677 := by decide +kernel

def row19677 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19677 : row19677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19677 := by decide +kernel

theorem rowEval19677 (x : Key → ℝ) : Integer.Sparse.eval row19677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19677, Integer.Sparse.eval_collectBalanced, rawRowCheck19677]

def rawRow19678 : Integer.Sparse Key := [(key377, 24), (key208, 24), (key456, 24), (key428, 24), (key428, 24)]

theorem rawRowCheck19678 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form1 = rawRow19678 := by decide +kernel

def row19678 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19678 : row19678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19678 := by decide +kernel

theorem rowEval19678 (x : Key → ℝ) : Integer.Sparse.eval row19678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19678, Integer.Sparse.eval_collectBalanced, rawRowCheck19678]

def rawRow19679 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key208, 24), (key428, 24), (key456, 24)]

theorem rawRowCheck19679 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form1 = rawRow19679 := by decide +kernel

def row19679 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19679 : row19679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19679 := by decide +kernel

theorem rowEval19679 (x : Key → ℝ) : Integer.Sparse.eval row19679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19679, Integer.Sparse.eval_collectBalanced, rawRowCheck19679]

def rawRow19680 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key208, 24), (key456, 24), (key428, 24)]

theorem rawRowCheck19680 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form1 = rawRow19680 := by decide +kernel

def row19680 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19680 : row19680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19680 := by decide +kernel

theorem rowEval19680 (x : Key → ℝ) : Integer.Sparse.eval row19680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19680, Integer.Sparse.eval_collectBalanced, rawRowCheck19680]

def rawRow19681 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key428, 24), (key208, 24), (key456, 24)]

theorem rawRowCheck19681 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form1 = rawRow19681 := by decide +kernel

def row19681 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19681 : row19681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19681 := by decide +kernel

theorem rowEval19681 (x : Key → ℝ) : Integer.Sparse.eval row19681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19681, Integer.Sparse.eval_collectBalanced, rawRowCheck19681]

def rawRow19682 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key428, 24), (key456, 24), (key208, 24)]

theorem rawRowCheck19682 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form1 = rawRow19682 := by decide +kernel

def row19682 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19682 : row19682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19682 := by decide +kernel

theorem rowEval19682 (x : Key → ℝ) : Integer.Sparse.eval row19682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19682, Integer.Sparse.eval_collectBalanced, rawRowCheck19682]

def rawRow19683 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key456, 24), (key208, 24), (key428, 24)]

theorem rawRowCheck19683 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form1 = rawRow19683 := by decide +kernel

def row19683 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19683 : row19683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19683 := by decide +kernel

theorem rowEval19683 (x : Key → ℝ) : Integer.Sparse.eval row19683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19683, Integer.Sparse.eval_collectBalanced, rawRowCheck19683]

def rawRow19684 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key456, 24), (key428, 24), (key208, 24)]

theorem rawRowCheck19684 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form1 = rawRow19684 := by decide +kernel

def row19684 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19684 : row19684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19684 := by decide +kernel

theorem rowEval19684 (x : Key → ℝ) : Integer.Sparse.eval row19684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19684, Integer.Sparse.eval_collectBalanced, rawRowCheck19684]

def rawRow19685 : Integer.Sparse Key := [(key377, 24), (key456, 24), (key208, 24), (key428, 24), (key428, 24)]

theorem rawRowCheck19685 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form1 = rawRow19685 := by decide +kernel

def row19685 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19685 : row19685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19685 := by decide +kernel

theorem rowEval19685 (x : Key → ℝ) : Integer.Sparse.eval row19685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19685, Integer.Sparse.eval_collectBalanced, rawRowCheck19685]

def rawRow19686 : Integer.Sparse Key := [(key377, 24), (key456, 24), (key428, 24), (key208, 24), (key428, 24)]

theorem rawRowCheck19686 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form1 = rawRow19686 := by decide +kernel

def row19686 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19686 : row19686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19686 := by decide +kernel

theorem rowEval19686 (x : Key → ℝ) : Integer.Sparse.eval row19686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19686, Integer.Sparse.eval_collectBalanced, rawRowCheck19686]

def rawRow19687 : Integer.Sparse Key := [(key377, 24), (key456, 24), (key428, 24), (key428, 24), (key208, 24)]

theorem rawRowCheck19687 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form1 = rawRow19687 := by decide +kernel

def row19687 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19687 : row19687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19687 := by decide +kernel

theorem rowEval19687 (x : Key → ℝ) : Integer.Sparse.eval row19687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19687, Integer.Sparse.eval_collectBalanced, rawRowCheck19687]

def rawRow19688 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key377, 24), (key428, 24), (key456, 24)]

theorem rawRowCheck19688 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form1 = rawRow19688 := by decide +kernel

def row19688 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19688 : row19688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19688 := by decide +kernel

theorem rowEval19688 (x : Key → ℝ) : Integer.Sparse.eval row19688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19688, Integer.Sparse.eval_collectBalanced, rawRowCheck19688]

def rawRow19689 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key377, 24), (key456, 24), (key428, 24)]

theorem rawRowCheck19689 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form1 = rawRow19689 := by decide +kernel

def row19689 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19689 : row19689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19689 := by decide +kernel

theorem rowEval19689 (x : Key → ℝ) : Integer.Sparse.eval row19689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19689, Integer.Sparse.eval_collectBalanced, rawRowCheck19689]

def rawRow19690 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key428, 24), (key377, 24), (key456, 24)]

theorem rawRowCheck19690 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form1 = rawRow19690 := by decide +kernel

def row19690 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19690 : row19690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19690 := by decide +kernel

theorem rowEval19690 (x : Key → ℝ) : Integer.Sparse.eval row19690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19690, Integer.Sparse.eval_collectBalanced, rawRowCheck19690]

def rawRow19691 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key428, 24), (key456, 24), (key377, 24)]

theorem rawRowCheck19691 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form1 = rawRow19691 := by decide +kernel

def row19691 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19691 : row19691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19691 := by decide +kernel

theorem rowEval19691 (x : Key → ℝ) : Integer.Sparse.eval row19691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19691, Integer.Sparse.eval_collectBalanced, rawRowCheck19691]

def rawRow19692 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key456, 24), (key377, 24), (key428, 24)]

theorem rawRowCheck19692 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form1 = rawRow19692 := by decide +kernel

def row19692 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19692 : row19692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19692 := by decide +kernel

theorem rowEval19692 (x : Key → ℝ) : Integer.Sparse.eval row19692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19692, Integer.Sparse.eval_collectBalanced, rawRowCheck19692]

def rawRow19693 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key456, 24), (key428, 24), (key377, 24)]

theorem rawRowCheck19693 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form1 = rawRow19693 := by decide +kernel

def row19693 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19693 : row19693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19693 := by decide +kernel

theorem rowEval19693 (x : Key → ℝ) : Integer.Sparse.eval row19693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19693, Integer.Sparse.eval_collectBalanced, rawRowCheck19693]

def rawRow19694 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key208, 24), (key428, 24), (key456, 24)]

theorem rawRowCheck19694 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form1 = rawRow19694 := by decide +kernel

def row19694 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19694 : row19694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19694 := by decide +kernel

theorem rowEval19694 (x : Key → ℝ) : Integer.Sparse.eval row19694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19694, Integer.Sparse.eval_collectBalanced, rawRowCheck19694]

def rawRow19695 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key208, 24), (key456, 24), (key428, 24)]

theorem rawRowCheck19695 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form1 = rawRow19695 := by decide +kernel

def row19695 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19695 : row19695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19695 := by decide +kernel

theorem rowEval19695 (x : Key → ℝ) : Integer.Sparse.eval row19695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19695, Integer.Sparse.eval_collectBalanced, rawRowCheck19695]

def rawRow19696 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key428, 24), (key208, 24), (key456, 24)]

theorem rawRowCheck19696 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form1 = rawRow19696 := by decide +kernel

def row19696 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19696 : row19696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19696 := by decide +kernel

theorem rowEval19696 (x : Key → ℝ) : Integer.Sparse.eval row19696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19696, Integer.Sparse.eval_collectBalanced, rawRowCheck19696]

def rawRow19697 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key428, 24), (key456, 24), (key208, 24)]

theorem rawRowCheck19697 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form1 = rawRow19697 := by decide +kernel

def row19697 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19697 : row19697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19697 := by decide +kernel

theorem rowEval19697 (x : Key → ℝ) : Integer.Sparse.eval row19697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19697, Integer.Sparse.eval_collectBalanced, rawRowCheck19697]

def rawRow19698 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key456, 24), (key208, 24), (key428, 24)]

theorem rawRowCheck19698 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form1 = rawRow19698 := by decide +kernel

def row19698 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19698 : row19698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19698 := by decide +kernel

theorem rowEval19698 (x : Key → ℝ) : Integer.Sparse.eval row19698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19698, Integer.Sparse.eval_collectBalanced, rawRowCheck19698]

def rawRow19699 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key456, 24), (key428, 24), (key208, 24)]

theorem rawRowCheck19699 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form1 = rawRow19699 := by decide +kernel

def row19699 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19699 : row19699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19699 := by decide +kernel

theorem rowEval19699 (x : Key → ℝ) : Integer.Sparse.eval row19699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19699, Integer.Sparse.eval_collectBalanced, rawRowCheck19699]

def rawRow19700 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key208, 24), (key377, 24), (key456, 24)]

theorem rawRowCheck19700 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form1 = rawRow19700 := by decide +kernel

def row19700 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19700 : row19700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19700 := by decide +kernel

theorem rowEval19700 (x : Key → ℝ) : Integer.Sparse.eval row19700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19700, Integer.Sparse.eval_collectBalanced, rawRowCheck19700]

def rawRow19701 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key208, 24), (key456, 24), (key377, 24)]

theorem rawRowCheck19701 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form1 = rawRow19701 := by decide +kernel

def row19701 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19701 : row19701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19701 := by decide +kernel

theorem rowEval19701 (x : Key → ℝ) : Integer.Sparse.eval row19701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19701, Integer.Sparse.eval_collectBalanced, rawRowCheck19701]

def rawRow19702 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key377, 24), (key208, 24), (key456, 24)]

theorem rawRowCheck19702 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form1 = rawRow19702 := by decide +kernel

def row19702 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19702 : row19702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19702 := by decide +kernel

theorem rowEval19702 (x : Key → ℝ) : Integer.Sparse.eval row19702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19702, Integer.Sparse.eval_collectBalanced, rawRowCheck19702]

def rawRow19703 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key377, 24), (key456, 24), (key208, 24)]

theorem rawRowCheck19703 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form1 = rawRow19703 := by decide +kernel

def row19703 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19703 : row19703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19703 := by decide +kernel

theorem rowEval19703 (x : Key → ℝ) : Integer.Sparse.eval row19703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19703, Integer.Sparse.eval_collectBalanced, rawRowCheck19703]

def rawRow19704 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key456, 24), (key208, 24), (key377, 24)]

theorem rawRowCheck19704 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form1 = rawRow19704 := by decide +kernel

def row19704 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19704 : row19704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19704 := by decide +kernel

theorem rowEval19704 (x : Key → ℝ) : Integer.Sparse.eval row19704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19704, Integer.Sparse.eval_collectBalanced, rawRowCheck19704]

def rawRow19705 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key456, 24), (key377, 24), (key208, 24)]

theorem rawRowCheck19705 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form1 = rawRow19705 := by decide +kernel

def row19705 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19705 : row19705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19705 := by decide +kernel

theorem rowEval19705 (x : Key → ℝ) : Integer.Sparse.eval row19705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19705, Integer.Sparse.eval_collectBalanced, rawRowCheck19705]

def rawRow19706 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key208, 24), (key377, 24), (key428, 24)]

theorem rawRowCheck19706 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form1 = rawRow19706 := by decide +kernel

def row19706 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19706 : row19706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19706 := by decide +kernel

theorem rowEval19706 (x : Key → ℝ) : Integer.Sparse.eval row19706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19706, Integer.Sparse.eval_collectBalanced, rawRowCheck19706]

def rawRow19707 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key208, 24), (key428, 24), (key377, 24)]

theorem rawRowCheck19707 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form1 = rawRow19707 := by decide +kernel

def row19707 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19707 : row19707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19707 := by decide +kernel

theorem rowEval19707 (x : Key → ℝ) : Integer.Sparse.eval row19707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19707, Integer.Sparse.eval_collectBalanced, rawRowCheck19707]

def rawRow19708 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key377, 24), (key208, 24), (key428, 24)]

theorem rawRowCheck19708 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form1 = rawRow19708 := by decide +kernel

def row19708 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19708 : row19708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19708 := by decide +kernel

theorem rowEval19708 (x : Key → ℝ) : Integer.Sparse.eval row19708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19708, Integer.Sparse.eval_collectBalanced, rawRowCheck19708]

def rawRow19709 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key377, 24), (key428, 24), (key208, 24)]

theorem rawRowCheck19709 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form1 = rawRow19709 := by decide +kernel

def row19709 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19709 : row19709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19709 := by decide +kernel

theorem rowEval19709 (x : Key → ℝ) : Integer.Sparse.eval row19709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19709, Integer.Sparse.eval_collectBalanced, rawRowCheck19709]

def rawRow19710 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key428, 24), (key208, 24), (key377, 24)]

theorem rawRowCheck19710 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form1 = rawRow19710 := by decide +kernel

def row19710 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19710 : row19710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19710 := by decide +kernel

theorem rowEval19710 (x : Key → ℝ) : Integer.Sparse.eval row19710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19710, Integer.Sparse.eval_collectBalanced, rawRowCheck19710]

def rawRow19711 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key428, 24), (key377, 24), (key208, 24)]

theorem rawRowCheck19711 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form1 = rawRow19711 := by decide +kernel

def row19711 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

theorem rowCheck19711 : row19711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19711 := by decide +kernel

theorem rowEval19711 (x : Key → ℝ) : Integer.Sparse.eval row19711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19711, Integer.Sparse.eval_collectBalanced, rawRowCheck19711]

end MUB6.Certificate.GramRows

end OAI
