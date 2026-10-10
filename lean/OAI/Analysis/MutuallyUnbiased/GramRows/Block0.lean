import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow0 : Integer.Sparse Key := [(key236, -1), (key239, -1), (key239, 2), (key248, 1), (key251, 1), (key251, -1), (key260, -1), (key267, -2), (key267, 1), (key271, 1), (key302, 1), (key305, 1), (key305, -2), (key316, -1), (key319, -1), (key319, 1), (key328, 1), (key335, 2), (key335, -1), (key340, -1), (key385, -1), (key388, -1), (key388, 1), (key397, 1), (key406, 1), (key409, 1), (key409, -1), (key418, -1), (key467, -1), (key469, -1), (key467, 1), (key475, 1), (key568, 2), (key568, -1), (key572, -1), (key578, -2), (key578, 1), (key583, 1), (key593, 1), (key595, 1), (key593, -1), (key601, -1)]

theorem rawRowCheck0 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form0 = rawRow0 := by decide +kernel

def row0 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck0 : row0 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow0 := by decide +kernel

theorem rowEval0 (x : Key → ℝ) : Integer.Sparse.eval row0 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck0, Integer.Sparse.eval_collectBalanced, rawRowCheck0]

def rawRow1 : Integer.Sparse Key := [(key239, -1), (key236, -1), (key239, 2), (key251, 1), (key248, 1), (key260, -1), (key251, -1), (key267, -2), (key271, 1), (key267, 1), (key305, 1), (key302, 1), (key305, -2), (key319, -1), (key316, -1), (key328, 1), (key319, 1), (key335, 2), (key340, -1), (key335, -1), (key388, -1), (key385, -1), (key397, 1), (key388, 1), (key409, 1), (key406, 1), (key418, -1), (key409, -1), (key469, -1), (key467, -1), (key475, 1), (key467, 1), (key568, 2), (key572, -1), (key568, -1), (key578, -2), (key583, 1), (key578, 1), (key595, 1), (key593, 1), (key601, -1), (key593, -1)]

theorem rawRowCheck1 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form0 = rawRow1 := by decide +kernel

def row1 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck1 : row1 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1 := by decide +kernel

theorem rowEval1 (x : Key → ℝ) : Integer.Sparse.eval row1 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck1, Integer.Sparse.eval_collectBalanced, rawRowCheck1]

def rawRow2 : Integer.Sparse Key := [(key239, -1), (key239, -1), (key236, 2), (key260, 1), (key260, 1), (key248, -1), (key248, -1), (key271, -2), (key267, 1), (key267, 1), (key305, 1), (key305, 1), (key302, -2), (key328, -1), (key328, -1), (key316, 1), (key316, 1), (key340, 2), (key335, -1), (key335, -1), (key397, -1), (key397, -1), (key385, 1), (key385, 1), (key418, 1), (key418, 1), (key406, -1), (key406, -1), (key475, -1), (key475, -1), (key469, 1), (key469, 1), (key572, 2), (key568, -1), (key568, -1), (key583, -2), (key578, 1), (key578, 1), (key601, 1), (key601, 1), (key595, -1), (key595, -1)]

theorem rawRowCheck2 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form0 = rawRow2 := by decide +kernel

def row2 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key260, 2), (key267, 2), (key271, -2), (key302, -2), (key305, 2), (key316, 2), (key328, -2), (key335, -2), (key340, 2), (key385, 2), (key397, -2), (key406, -2), (key418, 2), (key469, 2), (key475, -2), (key568, -2), (key572, 2), (key578, 2), (key583, -2), (key595, -2), (key601, 2)]

theorem rowCheck2 : row2 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2 := by decide +kernel

theorem rowEval2 (x : Key → ℝ) : Integer.Sparse.eval row2 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck2, Integer.Sparse.eval_collectBalanced, rawRowCheck2]

def rawRow3 : Integer.Sparse Key := [(key248, -1), (key251, -1), (key260, 2), (key236, 1), (key239, 1), (key267, -1), (key271, -1), (key239, -2), (key251, 1), (key260, 1), (key316, 1), (key319, 1), (key335, -2), (key302, -1), (key305, -1), (key335, 1), (key340, 1), (key305, 2), (key319, -1), (key328, -1), (key406, -1), (key409, -1), (key467, 1), (key469, 1), (key385, 1), (key388, 1), (key467, -1), (key475, -1), (key388, -1), (key397, -1), (key409, 1), (key418, 1), (key578, 2), (key593, -1), (key595, -1), (key568, -2), (key593, 1), (key601, 1), (key568, 1), (key572, 1), (key578, -1), (key583, -1)]

theorem rawRowCheck3 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form0 = rawRow3 := by decide +kernel

def row3 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, -1), (key340, 1), (key385, 1), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

theorem rowCheck3 : row3 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3 := by decide +kernel

theorem rowEval3 (x : Key → ℝ) : Integer.Sparse.eval row3 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck3, Integer.Sparse.eval_collectBalanced, rawRowCheck3]

def rawRow4 : Integer.Sparse Key := [(key251, -1), (key248, -1), (key260, 2), (key239, 1), (key236, 1), (key271, -1), (key267, -1), (key239, -2), (key260, 1), (key251, 1), (key319, 1), (key316, 1), (key335, -2), (key305, -1), (key302, -1), (key340, 1), (key335, 1), (key305, 2), (key328, -1), (key319, -1), (key409, -1), (key406, -1), (key469, 1), (key467, 1), (key388, 1), (key385, 1), (key475, -1), (key467, -1), (key397, -1), (key388, -1), (key418, 1), (key409, 1), (key578, 2), (key595, -1), (key593, -1), (key568, -2), (key601, 1), (key593, 1), (key572, 1), (key568, 1), (key583, -1), (key578, -1)]

theorem rawRowCheck4 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form0 = rawRow4 := by decide +kernel

def row4 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, -1), (key340, 1), (key385, 1), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

theorem rowCheck4 : row4 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4 := by decide +kernel

theorem rowEval4 (x : Key → ℝ) : Integer.Sparse.eval row4 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck4, Integer.Sparse.eval_collectBalanced, rawRowCheck4]

def rawRow5 : Integer.Sparse Key := [(key251, -1), (key260, -1), (key248, 2), (key267, 1), (key271, 1), (key236, -1), (key248, -1), (key260, -2), (key239, 1), (key251, 1), (key319, 1), (key335, 1), (key316, -2), (key328, -1), (key340, -1), (key302, 1), (key316, 1), (key328, 2), (key305, -1), (key319, -1), (key442, -1), (key469, -1), (key406, 1), (key435, 1), (key450, 1), (key475, 1), (key385, -1), (key435, -1), (key418, -1), (key450, -1), (key397, 1), (key442, 1), (key595, 2), (key578, -1), (key593, -1), (key601, -2), (key568, 1), (key593, 1), (key583, 1), (key601, 1), (key572, -1), (key595, -1)]

theorem rawRowCheck5 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form0 = rawRow5 := by decide +kernel

def row5 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck5 : row5 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5 := by decide +kernel

theorem rowEval5 (x : Key → ℝ) : Integer.Sparse.eval row5 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck5, Integer.Sparse.eval_collectBalanced, rawRowCheck5]

def rawRow6 : Integer.Sparse Key := [(key260, -1), (key251, -1), (key248, 2), (key271, 1), (key267, 1), (key248, -1), (key236, -1), (key260, -2), (key251, 1), (key239, 1), (key335, 1), (key319, 1), (key316, -2), (key340, -1), (key328, -1), (key316, 1), (key302, 1), (key328, 2), (key319, -1), (key305, -1), (key469, -1), (key442, -1), (key435, 1), (key406, 1), (key475, 1), (key450, 1), (key435, -1), (key385, -1), (key450, -1), (key418, -1), (key442, 1), (key397, 1), (key595, 2), (key593, -1), (key578, -1), (key601, -2), (key593, 1), (key568, 1), (key601, 1), (key583, 1), (key595, -1), (key572, -1)]

theorem rawRowCheck6 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form0 = rawRow6 := by decide +kernel

def row6 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck6 : row6 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6 := by decide +kernel

theorem rowEval6 (x : Key → ℝ) : Integer.Sparse.eval row6 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck6, Integer.Sparse.eval_collectBalanced, rawRowCheck6]

def rawRow7 : Integer.Sparse Key := [(key267, -1), (key267, -1), (key271, 2), (key239, 1), (key239, 1), (key260, -1), (key260, -1), (key236, -2), (key248, 1), (key248, 1), (key328, 1), (key328, 1), (key340, -2), (key305, -1), (key305, -1), (key335, 1), (key335, 1), (key302, 2), (key316, -1), (key316, -1), (key418, -1), (key418, -1), (key475, 1), (key475, 1), (key397, 1), (key397, 1), (key469, -1), (key469, -1), (key385, -1), (key385, -1), (key406, 1), (key406, 1), (key583, 2), (key601, -1), (key601, -1), (key572, -2), (key595, 1), (key595, 1), (key568, 1), (key568, 1), (key578, -1), (key578, -1)]

theorem rawRowCheck7 : GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form0 = rawRow7 := by decide +kernel

def row7 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key260, -2), (key267, -2), (key271, 2), (key302, 2), (key305, -2), (key316, -2), (key328, 2), (key335, 2), (key340, -2), (key385, -2), (key397, 2), (key406, 2), (key418, -2), (key469, -2), (key475, 2), (key568, 2), (key572, -2), (key578, -2), (key583, 2), (key595, 2), (key601, -2)]

theorem rowCheck7 : row7 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7 := by decide +kernel

theorem rowEval7 (x : Key → ℝ) : Integer.Sparse.eval row7 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck7, Integer.Sparse.eval_collectBalanced, rawRowCheck7]

def rawRow8 : Integer.Sparse Key := [(key267, -1), (key271, -1), (key267, 2), (key251, 1), (key260, 1), (key239, -1), (key251, -1), (key248, -2), (key236, 1), (key248, 1), (key328, 1), (key340, 1), (key328, -2), (key319, -1), (key335, -1), (key305, 1), (key319, 1), (key316, 2), (key302, -1), (key316, -1), (key450, -1), (key475, -1), (key418, 1), (key450, 1), (key442, 1), (key469, 1), (key397, -1), (key442, -1), (key406, -1), (key435, -1), (key385, 1), (key435, 1), (key601, 2), (key583, -1), (key601, -1), (key595, -2), (key572, 1), (key595, 1), (key578, 1), (key593, 1), (key568, -1), (key593, -1)]

theorem rawRowCheck8 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form0 = rawRow8 := by decide +kernel

def row8 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, -1), (key340, 1), (key385, 1), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

theorem rowCheck8 : row8 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8 := by decide +kernel

theorem rowEval8 (x : Key → ℝ) : Integer.Sparse.eval row8 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck8, Integer.Sparse.eval_collectBalanced, rawRowCheck8]

def rawRow9 : Integer.Sparse Key := [(key271, -1), (key267, -1), (key267, 2), (key260, 1), (key251, 1), (key251, -1), (key239, -1), (key248, -2), (key248, 1), (key236, 1), (key340, 1), (key328, 1), (key328, -2), (key335, -1), (key319, -1), (key319, 1), (key305, 1), (key316, 2), (key316, -1), (key302, -1), (key475, -1), (key450, -1), (key450, 1), (key418, 1), (key469, 1), (key442, 1), (key442, -1), (key397, -1), (key435, -1), (key406, -1), (key435, 1), (key385, 1), (key601, 2), (key601, -1), (key583, -1), (key595, -2), (key595, 1), (key572, 1), (key593, 1), (key578, 1), (key593, -1), (key568, -1)]

theorem rawRowCheck9 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form0 = rawRow9 := by decide +kernel

def row9 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, -1), (key340, 1), (key385, 1), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

theorem rowCheck9 : row9 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9 := by decide +kernel

theorem rowEval9 (x : Key → ℝ) : Integer.Sparse.eval row9 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck9, Integer.Sparse.eval_collectBalanced, rawRowCheck9]

def rawRow10 : Integer.Sparse Key := [(key302, -1), (key305, -1), (key305, 2), (key316, 1), (key319, 1), (key319, -1), (key335, -1), (key328, -2), (key328, 1), (key340, 1), (key236, 1), (key239, 1), (key239, -2), (key406, -1), (key409, -1), (key409, 1), (key418, 1), (key578, 2), (key578, -1), (key583, -1), (key248, -1), (key251, -1), (key251, 1), (key260, 1), (key316, 1), (key319, 1), (key319, -1), (key328, -1), (key593, -1), (key595, -1), (key593, 1), (key601, 1), (key267, 2), (key267, -1), (key271, -1), (key335, -2), (key335, 1), (key340, 1), (key467, 1), (key469, 1), (key467, -1), (key475, -1)]

theorem rawRowCheck10 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form0 = rawRow10 := by decide +kernel

def row10 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 2), (key328, -2), (key335, -2), (key340, 2), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

theorem rowCheck10 : row10 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10 := by decide +kernel

theorem rowEval10 (x : Key → ℝ) : Integer.Sparse.eval row10 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck10, Integer.Sparse.eval_collectBalanced, rawRowCheck10]

def rawRow11 : Integer.Sparse Key := [(key305, -1), (key302, -1), (key305, 2), (key319, 1), (key316, 1), (key335, -1), (key319, -1), (key328, -2), (key340, 1), (key328, 1), (key239, 1), (key236, 1), (key239, -2), (key409, -1), (key406, -1), (key418, 1), (key409, 1), (key578, 2), (key583, -1), (key578, -1), (key251, -1), (key248, -1), (key260, 1), (key251, 1), (key319, 1), (key316, 1), (key328, -1), (key319, -1), (key595, -1), (key593, -1), (key601, 1), (key593, 1), (key267, 2), (key271, -1), (key267, -1), (key335, -2), (key340, 1), (key335, 1), (key469, 1), (key467, 1), (key475, -1), (key467, -1)]

theorem rawRowCheck11 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form0 = rawRow11 := by decide +kernel

def row11 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 2), (key328, -2), (key335, -2), (key340, 2), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

theorem rowCheck11 : row11 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11 := by decide +kernel

theorem rowEval11 (x : Key → ℝ) : Integer.Sparse.eval row11 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck11, Integer.Sparse.eval_collectBalanced, rawRowCheck11]

def rawRow12 : Integer.Sparse Key := [(key305, -1), (key305, -1), (key302, 2), (key335, 1), (key335, 1), (key316, -1), (key316, -1), (key340, -2), (key328, 1), (key328, 1), (key239, 1), (key239, 1), (key236, -2), (key418, -1), (key418, -1), (key406, 1), (key406, 1), (key583, 2), (key578, -1), (key578, -1), (key260, -1), (key260, -1), (key248, 1), (key248, 1), (key328, 1), (key328, 1), (key316, -1), (key316, -1), (key601, -1), (key601, -1), (key595, 1), (key595, 1), (key271, 2), (key267, -1), (key267, -1), (key340, -2), (key335, 1), (key335, 1), (key475, 1), (key475, 1), (key469, -1), (key469, -1)]

theorem rawRowCheck12 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form0 = rawRow12 := by decide +kernel

def row12 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key260, -2), (key267, -2), (key271, 2), (key302, 2), (key305, -2), (key316, -4), (key328, 4), (key335, 4), (key340, -4), (key406, 2), (key418, -2), (key469, -2), (key475, 2), (key578, -2), (key583, 2), (key595, 2), (key601, -2)]

theorem rowCheck12 : row12 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12 := by decide +kernel

theorem rowEval12 (x : Key → ℝ) : Integer.Sparse.eval row12 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck12, Integer.Sparse.eval_collectBalanced, rawRowCheck12]

def rawRow13 : Integer.Sparse Key := [(key316, -1), (key319, -1), (key328, 2), (key302, 1), (key305, 1), (key328, -1), (key340, -1), (key305, -2), (key319, 1), (key335, 1), (key406, 1), (key409, 1), (key418, -2), (key236, -1), (key239, -1), (key578, 1), (key583, 1), (key239, 2), (key409, -1), (key418, -1), (key316, -1), (key319, -1), (key593, 1), (key595, 1), (key248, 1), (key251, 1), (key593, -1), (key601, -1), (key251, -1), (key260, -1), (key319, 1), (key328, 1), (key335, 2), (key467, -1), (key469, -1), (key267, -2), (key467, 1), (key475, 1), (key267, 1), (key271, 1), (key335, -1), (key340, -1)]

theorem rawRowCheck13 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form0 = rawRow13 := by decide +kernel

def row13 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -2), (key328, 2), (key335, 2), (key340, -2), (key406, 1), (key418, -3), (key469, -1), (key475, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck13 : row13 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13 := by decide +kernel

theorem rowEval13 (x : Key → ℝ) : Integer.Sparse.eval row13 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck13, Integer.Sparse.eval_collectBalanced, rawRowCheck13]

def rawRow14 : Integer.Sparse Key := [(key319, -1), (key316, -1), (key328, 2), (key305, 1), (key302, 1), (key340, -1), (key328, -1), (key305, -2), (key335, 1), (key319, 1), (key409, 1), (key406, 1), (key418, -2), (key239, -1), (key236, -1), (key583, 1), (key578, 1), (key239, 2), (key418, -1), (key409, -1), (key319, -1), (key316, -1), (key595, 1), (key593, 1), (key251, 1), (key248, 1), (key601, -1), (key593, -1), (key260, -1), (key251, -1), (key328, 1), (key319, 1), (key335, 2), (key469, -1), (key467, -1), (key267, -2), (key475, 1), (key467, 1), (key271, 1), (key267, 1), (key340, -1), (key335, -1)]

theorem rawRowCheck14 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form0 = rawRow14 := by decide +kernel

def row14 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -2), (key328, 2), (key335, 2), (key340, -2), (key406, 1), (key418, -3), (key469, -1), (key475, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck14 : row14 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14 := by decide +kernel

theorem rowEval14 (x : Key → ℝ) : Integer.Sparse.eval row14 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck14, Integer.Sparse.eval_collectBalanced, rawRowCheck14]

def rawRow15 : Integer.Sparse Key := [(key319, -1), (key328, -1), (key316, 2), (key335, 1), (key340, 1), (key302, -1), (key316, -1), (key335, -2), (key305, 1), (key319, 1), (key409, 1), (key418, 1), (key406, -2), (key578, -1), (key583, -1), (key236, 1), (key406, 1), (key418, 2), (key239, -1), (key409, -1), (key442, -1), (key595, -1), (key316, 1), (key435, 1), (key450, 1), (key601, 1), (key248, -1), (key435, -1), (key328, -1), (key450, -1), (key260, 1), (key442, 1), (key469, 2), (key335, -1), (key467, -1), (key475, -2), (key267, 1), (key467, 1), (key340, 1), (key475, 1), (key271, -1), (key469, -1)]

theorem rawRowCheck15 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form0 = rawRow15 := by decide +kernel

def row15 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 2), (key328, -2), (key335, -2), (key340, 2), (key406, -1), (key418, 3), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key595, -1), (key601, 1)]

theorem rowCheck15 : row15 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15 := by decide +kernel

theorem rowEval15 (x : Key → ℝ) : Integer.Sparse.eval row15 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck15, Integer.Sparse.eval_collectBalanced, rawRowCheck15]

def rawRow16 : Integer.Sparse Key := [(key328, -1), (key319, -1), (key316, 2), (key340, 1), (key335, 1), (key316, -1), (key302, -1), (key335, -2), (key319, 1), (key305, 1), (key418, 1), (key409, 1), (key406, -2), (key583, -1), (key578, -1), (key406, 1), (key236, 1), (key418, 2), (key409, -1), (key239, -1), (key595, -1), (key442, -1), (key435, 1), (key316, 1), (key601, 1), (key450, 1), (key435, -1), (key248, -1), (key450, -1), (key328, -1), (key442, 1), (key260, 1), (key469, 2), (key467, -1), (key335, -1), (key475, -2), (key467, 1), (key267, 1), (key475, 1), (key340, 1), (key469, -1), (key271, -1)]

theorem rawRowCheck16 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form0 = rawRow16 := by decide +kernel

def row16 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 2), (key328, -2), (key335, -2), (key340, 2), (key406, -1), (key418, 3), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key595, -1), (key601, 1)]

theorem rowCheck16 : row16 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16 := by decide +kernel

theorem rowEval16 (x : Key → ℝ) : Integer.Sparse.eval row16 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck16, Integer.Sparse.eval_collectBalanced, rawRowCheck16]

def rawRow17 : Integer.Sparse Key := [(key335, -1), (key335, -1), (key340, 2), (key305, 1), (key305, 1), (key328, -1), (key328, -1), (key302, -2), (key316, 1), (key316, 1), (key578, 1), (key578, 1), (key583, -2), (key239, -1), (key239, -1), (key418, 1), (key418, 1), (key236, 2), (key406, -1), (key406, -1), (key328, -1), (key328, -1), (key601, 1), (key601, 1), (key260, 1), (key260, 1), (key595, -1), (key595, -1), (key248, -1), (key248, -1), (key316, 1), (key316, 1), (key340, 2), (key475, -1), (key475, -1), (key271, -2), (key469, 1), (key469, 1), (key267, 1), (key267, 1), (key335, -1), (key335, -1)]

theorem rawRowCheck17 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form0 = rawRow17 := by decide +kernel

def row17 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key260, 2), (key267, 2), (key271, -2), (key302, -2), (key305, 2), (key316, 4), (key328, -4), (key335, -4), (key340, 4), (key406, -2), (key418, 2), (key469, 2), (key475, -2), (key578, 2), (key583, -2), (key595, -2), (key601, 2)]

theorem rowCheck17 : row17 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17 := by decide +kernel

theorem rowEval17 (x : Key → ℝ) : Integer.Sparse.eval row17 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck17, Integer.Sparse.eval_collectBalanced, rawRowCheck17]

def rawRow18 : Integer.Sparse Key := [(key335, -1), (key340, -1), (key335, 2), (key319, 1), (key328, 1), (key305, -1), (key319, -1), (key316, -2), (key302, 1), (key316, 1), (key578, 1), (key583, 1), (key578, -2), (key409, -1), (key418, -1), (key239, 1), (key409, 1), (key406, 2), (key236, -1), (key406, -1), (key450, -1), (key601, -1), (key328, 1), (key450, 1), (key442, 1), (key595, 1), (key260, -1), (key442, -1), (key316, -1), (key435, -1), (key248, 1), (key435, 1), (key475, 2), (key340, -1), (key475, -1), (key469, -2), (key271, 1), (key469, 1), (key335, 1), (key467, 1), (key267, -1), (key467, -1)]

theorem rawRowCheck18 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form0 = rawRow18 := by decide +kernel

def row18 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -2), (key328, 2), (key335, 2), (key340, -2), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck18 : row18 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18 := by decide +kernel

theorem rowEval18 (x : Key → ℝ) : Integer.Sparse.eval row18 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck18, Integer.Sparse.eval_collectBalanced, rawRowCheck18]

def rawRow19 : Integer.Sparse Key := [(key340, -1), (key335, -1), (key335, 2), (key328, 1), (key319, 1), (key319, -1), (key305, -1), (key316, -2), (key316, 1), (key302, 1), (key583, 1), (key578, 1), (key578, -2), (key418, -1), (key409, -1), (key409, 1), (key239, 1), (key406, 2), (key406, -1), (key236, -1), (key601, -1), (key450, -1), (key450, 1), (key328, 1), (key595, 1), (key442, 1), (key442, -1), (key260, -1), (key435, -1), (key316, -1), (key435, 1), (key248, 1), (key475, 2), (key475, -1), (key340, -1), (key469, -2), (key469, 1), (key271, 1), (key467, 1), (key335, 1), (key467, -1), (key267, -1)]

theorem rawRowCheck19 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form0 = rawRow19 := by decide +kernel

def row19 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -2), (key328, 2), (key335, 2), (key340, -2), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck19 : row19 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19 := by decide +kernel

theorem rowEval19 (x : Key → ℝ) : Integer.Sparse.eval row19 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck19, Integer.Sparse.eval_collectBalanced, rawRowCheck19]

def rawRow20 : Integer.Sparse Key := [(key385, -1), (key388, -1), (key397, 2), (key406, 1), (key409, 1), (key442, -1), (key469, -1), (key418, -2), (key450, 1), (key475, 1), (key248, 1), (key251, 1), (key260, -2), (key316, -1), (key319, -1), (key442, 1), (key595, 1), (key328, 2), (key450, -1), (key601, -1), (key236, -1), (key239, -1), (key267, 1), (key271, 1), (key302, 1), (key305, 1), (key335, -1), (key340, -1), (key568, -1), (key572, -1), (key578, 1), (key583, 1), (key239, 2), (key251, -1), (key260, -1), (key305, -2), (key319, 1), (key328, 1), (key388, 1), (key397, 1), (key409, -1), (key418, -1)]

theorem rawRowCheck20 : GramPolynomial.normalizedRow 0 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form0 = rawRow20 := by decide +kernel

def row20 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 3), (key335, -1), (key340, -1), (key385, -1), (key397, 3), (key406, 1), (key418, -3), (key469, -1), (key475, 1), (key568, -1), (key572, -1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck20 : row20 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20 := by decide +kernel

theorem rowEval20 (x : Key → ℝ) : Integer.Sparse.eval row20 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck20, Integer.Sparse.eval_collectBalanced, rawRowCheck20]

def rawRow21 : Integer.Sparse Key := [(key388, -1), (key385, -1), (key397, 2), (key409, 1), (key406, 1), (key469, -1), (key442, -1), (key418, -2), (key475, 1), (key450, 1), (key251, 1), (key248, 1), (key260, -2), (key319, -1), (key316, -1), (key595, 1), (key442, 1), (key328, 2), (key601, -1), (key450, -1), (key239, -1), (key236, -1), (key271, 1), (key267, 1), (key305, 1), (key302, 1), (key340, -1), (key335, -1), (key572, -1), (key568, -1), (key583, 1), (key578, 1), (key239, 2), (key260, -1), (key251, -1), (key305, -2), (key328, 1), (key319, 1), (key397, 1), (key388, 1), (key418, -1), (key409, -1)]

theorem rawRowCheck21 : GramPolynomial.normalizedRow 0 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form0 = rawRow21 := by decide +kernel

def row21 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 3), (key335, -1), (key340, -1), (key385, -1), (key397, 3), (key406, 1), (key418, -3), (key469, -1), (key475, 1), (key568, -1), (key572, -1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck21 : row21 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow21 := by decide +kernel

theorem rowEval21 (x : Key → ℝ) : Integer.Sparse.eval row21 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck21, Integer.Sparse.eval_collectBalanced, rawRowCheck21]

def rawRow22 : Integer.Sparse Key := [(key388, -1), (key397, -1), (key385, 2), (key467, 1), (key469, 1), (key406, -1), (key435, -1), (key475, -2), (key418, 1), (key450, 1), (key251, 1), (key260, 1), (key248, -2), (key593, -1), (key595, -1), (key316, 1), (key435, 1), (key601, 2), (key328, -1), (key450, -1), (key267, -1), (key271, -1), (key236, 1), (key248, 1), (key328, 1), (key340, 1), (key302, -1), (key316, -1), (key583, -1), (key601, -1), (key572, 1), (key595, 1), (key260, 2), (key239, -1), (key251, -1), (key328, -2), (key305, 1), (key319, 1), (key418, 1), (key450, 1), (key397, -1), (key442, -1)]

theorem rawRowCheck22 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form0 = rawRow22 := by decide +kernel

def row22 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key302, -1), (key305, 1), (key319, 1), (key328, -2), (key340, 1), (key385, 2), (key388, -1), (key397, -2), (key406, -1), (key418, 2), (key442, -1), (key450, 1), (key467, 1), (key469, 1), (key475, -2), (key572, 1), (key583, -1), (key593, -1), (key601, 1)]

theorem rowCheck22 : row22 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow22 := by decide +kernel

theorem rowEval22 (x : Key → ℝ) : Integer.Sparse.eval row22 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck22, Integer.Sparse.eval_collectBalanced, rawRowCheck22]

def rawRow23 : Integer.Sparse Key := [(key397, -1), (key388, -1), (key385, 2), (key469, 1), (key467, 1), (key435, -1), (key406, -1), (key475, -2), (key450, 1), (key418, 1), (key260, 1), (key251, 1), (key248, -2), (key595, -1), (key593, -1), (key435, 1), (key316, 1), (key601, 2), (key450, -1), (key328, -1), (key271, -1), (key267, -1), (key248, 1), (key236, 1), (key340, 1), (key328, 1), (key316, -1), (key302, -1), (key601, -1), (key583, -1), (key595, 1), (key572, 1), (key260, 2), (key251, -1), (key239, -1), (key328, -2), (key319, 1), (key305, 1), (key450, 1), (key418, 1), (key442, -1), (key397, -1)]

theorem rawRowCheck23 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form0 = rawRow23 := by decide +kernel

def row23 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key302, -1), (key305, 1), (key319, 1), (key328, -2), (key340, 1), (key385, 2), (key388, -1), (key397, -2), (key406, -1), (key418, 2), (key442, -1), (key450, 1), (key467, 1), (key469, 1), (key475, -2), (key572, 1), (key583, -1), (key593, -1), (key601, 1)]

theorem rowCheck23 : row23 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow23 := by decide +kernel

theorem rowEval23 (x : Key → ℝ) : Integer.Sparse.eval row23 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck23, Integer.Sparse.eval_collectBalanced, rawRowCheck23]

def rawRow24 : Integer.Sparse Key := [(key406, -1), (key409, -1), (key418, 2), (key385, 1), (key388, 1), (key450, -1), (key475, -1), (key397, -2), (key442, 1), (key469, 1), (key316, 1), (key319, 1), (key328, -2), (key248, -1), (key251, -1), (key450, 1), (key601, 1), (key260, 2), (key442, -1), (key595, -1), (key302, -1), (key305, -1), (key328, 1), (key340, 1), (key236, 1), (key239, 1), (key578, -1), (key583, -1), (key267, -1), (key271, -1), (key335, 1), (key340, 1), (key305, 2), (key388, -1), (key397, -1), (key239, -2), (key409, 1), (key418, 1), (key251, 1), (key260, 1), (key319, -1), (key328, -1)]

theorem rawRowCheck24 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form0 = rawRow24 := by decide +kernel

def row24 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key328, -2), (key335, 1), (key340, 2), (key385, 1), (key397, -3), (key406, -1), (key418, 3), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key595, -1), (key601, 1)]

theorem rowCheck24 : row24 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow24 := by decide +kernel

theorem rowEval24 (x : Key → ℝ) : Integer.Sparse.eval row24 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck24, Integer.Sparse.eval_collectBalanced, rawRowCheck24]

def rawRow25 : Integer.Sparse Key := [(key409, -1), (key406, -1), (key418, 2), (key388, 1), (key385, 1), (key475, -1), (key450, -1), (key397, -2), (key469, 1), (key442, 1), (key319, 1), (key316, 1), (key328, -2), (key251, -1), (key248, -1), (key601, 1), (key450, 1), (key260, 2), (key595, -1), (key442, -1), (key305, -1), (key302, -1), (key340, 1), (key328, 1), (key239, 1), (key236, 1), (key583, -1), (key578, -1), (key271, -1), (key267, -1), (key340, 1), (key335, 1), (key305, 2), (key397, -1), (key388, -1), (key239, -2), (key418, 1), (key409, 1), (key260, 1), (key251, 1), (key328, -1), (key319, -1)]

theorem rawRowCheck25 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form0 = rawRow25 := by decide +kernel

def row25 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key328, -2), (key335, 1), (key340, 2), (key385, 1), (key397, -3), (key406, -1), (key418, 3), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key595, -1), (key601, 1)]

theorem rowCheck25 : row25 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow25 := by decide +kernel

theorem rowEval25 (x : Key → ℝ) : Integer.Sparse.eval row25 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck25, Integer.Sparse.eval_collectBalanced, rawRowCheck25]

def rawRow26 : Integer.Sparse Key := [(key409, -1), (key418, -1), (key406, 2), (key467, 1), (key475, 1), (key385, -1), (key435, -1), (key469, -2), (key397, 1), (key442, 1), (key319, 1), (key328, 1), (key316, -2), (key593, -1), (key601, -1), (key248, 1), (key435, 1), (key595, 2), (key260, -1), (key442, -1), (key335, -1), (key340, -1), (key302, 1), (key316, 1), (key578, 1), (key583, 1), (key236, -1), (key406, -1), (key340, -1), (key475, -1), (key271, 1), (key469, 1), (key397, 2), (key305, -1), (key388, -1), (key418, -2), (key239, 1), (key409, 1), (key328, 1), (key450, 1), (key260, -1), (key442, -1)]

theorem rawRowCheck26 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form0 = rawRow26 := by decide +kernel

def row26 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -2), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, 2), (key335, -1), (key340, -2), (key385, -1), (key388, -1), (key397, 3), (key406, 1), (key418, -3), (key442, -1), (key450, 1), (key467, 1), (key469, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

theorem rowCheck26 : row26 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow26 := by decide +kernel

theorem rowEval26 (x : Key → ℝ) : Integer.Sparse.eval row26 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck26, Integer.Sparse.eval_collectBalanced, rawRowCheck26]

def rawRow27 : Integer.Sparse Key := [(key418, -1), (key409, -1), (key406, 2), (key475, 1), (key467, 1), (key435, -1), (key385, -1), (key469, -2), (key442, 1), (key397, 1), (key328, 1), (key319, 1), (key316, -2), (key601, -1), (key593, -1), (key435, 1), (key248, 1), (key595, 2), (key442, -1), (key260, -1), (key340, -1), (key335, -1), (key316, 1), (key302, 1), (key583, 1), (key578, 1), (key406, -1), (key236, -1), (key475, -1), (key340, -1), (key469, 1), (key271, 1), (key397, 2), (key388, -1), (key305, -1), (key418, -2), (key409, 1), (key239, 1), (key450, 1), (key328, 1), (key442, -1), (key260, -1)]

theorem rawRowCheck27 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form0 = rawRow27 := by decide +kernel

def row27 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -2), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, 2), (key335, -1), (key340, -2), (key385, -1), (key388, -1), (key397, 3), (key406, 1), (key418, -3), (key442, -1), (key450, 1), (key467, 1), (key469, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

theorem rowCheck27 : row27 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow27 := by decide +kernel

theorem rowEval27 (x : Key → ℝ) : Integer.Sparse.eval row27 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck27, Integer.Sparse.eval_collectBalanced, rawRowCheck27]

def rawRow28 : Integer.Sparse Key := [(key467, -1), (key469, -1), (key475, 2), (key388, 1), (key397, 1), (key418, -1), (key450, -1), (key385, -2), (key406, 1), (key435, 1), (key593, 1), (key595, 1), (key601, -2), (key251, -1), (key260, -1), (key328, 1), (key450, 1), (key248, 2), (key316, -1), (key435, -1), (key568, -1), (key572, -1), (key583, 1), (key601, 1), (key267, 1), (key271, 1), (key340, -1), (key475, -1), (key236, -1), (key248, -1), (key302, 1), (key316, 1), (key328, 2), (key418, -1), (key450, -1), (key260, -2), (key397, 1), (key442, 1), (key239, 1), (key251, 1), (key305, -1), (key319, -1)]

theorem rawRowCheck28 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form0 = rawRow28 := by decide +kernel

def row28 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, 1), (key305, -1), (key319, -1), (key328, 3), (key340, -1), (key385, -2), (key388, 1), (key397, 2), (key406, 1), (key418, -2), (key442, 1), (key450, -1), (key467, -1), (key469, -1), (key475, 1), (key568, -1), (key572, -1), (key583, 1), (key593, 1), (key595, 1), (key601, -1)]

theorem rowCheck28 : row28 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow28 := by decide +kernel

theorem rowEval28 (x : Key → ℝ) : Integer.Sparse.eval row28 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck28, Integer.Sparse.eval_collectBalanced, rawRowCheck28]

def rawRow29 : Integer.Sparse Key := [(key469, -1), (key467, -1), (key475, 2), (key397, 1), (key388, 1), (key450, -1), (key418, -1), (key385, -2), (key435, 1), (key406, 1), (key595, 1), (key593, 1), (key601, -2), (key260, -1), (key251, -1), (key450, 1), (key328, 1), (key248, 2), (key435, -1), (key316, -1), (key572, -1), (key568, -1), (key601, 1), (key583, 1), (key271, 1), (key267, 1), (key475, -1), (key340, -1), (key248, -1), (key236, -1), (key316, 1), (key302, 1), (key328, 2), (key450, -1), (key418, -1), (key260, -2), (key442, 1), (key397, 1), (key251, 1), (key239, 1), (key319, -1), (key305, -1)]

theorem rawRowCheck29 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form0 = rawRow29 := by decide +kernel

def row29 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, 1), (key305, -1), (key319, -1), (key328, 3), (key340, -1), (key385, -2), (key388, 1), (key397, 2), (key406, 1), (key418, -2), (key442, 1), (key450, -1), (key467, -1), (key469, -1), (key475, 1), (key568, -1), (key572, -1), (key583, 1), (key593, 1), (key595, 1), (key601, -1)]

theorem rowCheck29 : row29 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow29 := by decide +kernel

theorem rowEval29 (x : Key → ℝ) : Integer.Sparse.eval row29 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck29, Integer.Sparse.eval_collectBalanced, rawRowCheck29]

def rawRow30 : Integer.Sparse Key := [(key467, -1), (key475, -1), (key469, 2), (key409, 1), (key418, 1), (key397, -1), (key442, -1), (key406, -2), (key385, 1), (key435, 1), (key593, 1), (key601, 1), (key595, -2), (key319, -1), (key328, -1), (key260, 1), (key442, 1), (key316, 2), (key248, -1), (key435, -1), (key578, -1), (key583, -1), (key572, 1), (key595, 1), (key335, 1), (key340, 1), (key271, -1), (key469, -1), (key302, -1), (key316, -1), (key236, 1), (key406, 1), (key418, 2), (key328, -1), (key450, -1), (key397, -2), (key260, 1), (key442, 1), (key305, 1), (key388, 1), (key239, -1), (key409, -1)]

theorem rawRowCheck30 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form0 = rawRow30 := by decide +kernel

def row30 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 2), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key319, -1), (key328, -2), (key335, 1), (key340, 1), (key385, 1), (key388, 1), (key397, -3), (key406, -1), (key418, 3), (key442, 1), (key450, -1), (key467, -1), (key469, 1), (key475, -1), (key572, 1), (key578, -1), (key583, -1), (key593, 1), (key595, -1), (key601, 1)]

theorem rowCheck30 : row30 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow30 := by decide +kernel

theorem rowEval30 (x : Key → ℝ) : Integer.Sparse.eval row30 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck30, Integer.Sparse.eval_collectBalanced, rawRowCheck30]

def rawRow31 : Integer.Sparse Key := [(key475, -1), (key467, -1), (key469, 2), (key418, 1), (key409, 1), (key442, -1), (key397, -1), (key406, -2), (key435, 1), (key385, 1), (key601, 1), (key593, 1), (key595, -2), (key328, -1), (key319, -1), (key442, 1), (key260, 1), (key316, 2), (key435, -1), (key248, -1), (key583, -1), (key578, -1), (key595, 1), (key572, 1), (key340, 1), (key335, 1), (key469, -1), (key271, -1), (key316, -1), (key302, -1), (key406, 1), (key236, 1), (key418, 2), (key450, -1), (key328, -1), (key397, -2), (key442, 1), (key260, 1), (key388, 1), (key305, 1), (key409, -1), (key239, -1)]

theorem rawRowCheck31 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form0 = rawRow31 := by decide +kernel

def row31 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 2), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key319, -1), (key328, -2), (key335, 1), (key340, 1), (key385, 1), (key388, 1), (key397, -3), (key406, -1), (key418, 3), (key442, 1), (key450, -1), (key467, -1), (key469, 1), (key475, -1), (key572, 1), (key578, -1), (key583, -1), (key593, 1), (key595, -1), (key601, 1)]

theorem rowCheck31 : row31 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow31 := by decide +kernel

theorem rowEval31 (x : Key → ℝ) : Integer.Sparse.eval row31 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck31, Integer.Sparse.eval_collectBalanced, rawRowCheck31]

def rawRow32 : Integer.Sparse Key := [(key568, -1), (key568, -1), (key572, 2), (key578, 1), (key578, 1), (key595, -1), (key595, -1), (key583, -2), (key601, 1), (key601, 1), (key267, 1), (key267, 1), (key271, -2), (key335, -1), (key335, -1), (key469, 1), (key469, 1), (key340, 2), (key475, -1), (key475, -1), (key239, -1), (key239, -1), (key260, 1), (key260, 1), (key305, 1), (key305, 1), (key397, -1), (key397, -1), (key328, -1), (key328, -1), (key418, 1), (key418, 1), (key236, 2), (key248, -1), (key248, -1), (key302, -2), (key316, 1), (key316, 1), (key385, 1), (key385, 1), (key406, -1), (key406, -1)]

theorem rawRowCheck32 : GramPolynomial.normalizedRow 0 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form0 = rawRow32 := by decide +kernel

def row32 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key260, 2), (key267, 2), (key271, -2), (key302, -2), (key305, 2), (key316, 2), (key328, -2), (key335, -2), (key340, 2), (key385, 2), (key397, -2), (key406, -2), (key418, 2), (key469, 2), (key475, -2), (key568, -2), (key572, 2), (key578, 2), (key583, -2), (key595, -2), (key601, 2)]

theorem rowCheck32 : row32 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow32 := by decide +kernel

theorem rowEval32 (x : Key → ℝ) : Integer.Sparse.eval row32 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck32, Integer.Sparse.eval_collectBalanced, rawRowCheck32]

def rawRow33 : Integer.Sparse Key := [(key568, -1), (key572, -1), (key568, 2), (key593, 1), (key595, 1), (key578, -1), (key593, -1), (key601, -2), (key583, 1), (key601, 1), (key267, 1), (key271, 1), (key267, -2), (key467, -1), (key469, -1), (key335, 1), (key467, 1), (key475, 2), (key340, -1), (key475, -1), (key251, -1), (key260, -1), (key239, 1), (key251, 1), (key388, 1), (key397, 1), (key305, -1), (key388, -1), (key418, -1), (key450, -1), (key328, 1), (key450, 1), (key248, 2), (key236, -1), (key248, -1), (key316, -2), (key302, 1), (key316, 1), (key406, 1), (key435, 1), (key385, -1), (key435, -1)]

theorem rawRowCheck33 : GramPolynomial.normalizedRow 0 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form0 = rawRow33 := by decide +kernel

def row33 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck33 : row33 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow33 := by decide +kernel

theorem rowEval33 (x : Key → ℝ) : Integer.Sparse.eval row33 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck33, Integer.Sparse.eval_collectBalanced, rawRowCheck33]

def rawRow34 : Integer.Sparse Key := [(key572, -1), (key568, -1), (key568, 2), (key595, 1), (key593, 1), (key593, -1), (key578, -1), (key601, -2), (key601, 1), (key583, 1), (key271, 1), (key267, 1), (key267, -2), (key469, -1), (key467, -1), (key467, 1), (key335, 1), (key475, 2), (key475, -1), (key340, -1), (key260, -1), (key251, -1), (key251, 1), (key239, 1), (key397, 1), (key388, 1), (key388, -1), (key305, -1), (key450, -1), (key418, -1), (key450, 1), (key328, 1), (key248, 2), (key248, -1), (key236, -1), (key316, -2), (key316, 1), (key302, 1), (key435, 1), (key406, 1), (key435, -1), (key385, -1)]

theorem rawRowCheck34 : GramPolynomial.normalizedRow 0 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form0 = rawRow34 := by decide +kernel

def row34 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck34 : row34 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow34 := by decide +kernel

theorem rowEval34 (x : Key → ℝ) : Integer.Sparse.eval row34 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck34, Integer.Sparse.eval_collectBalanced, rawRowCheck34]

def rawRow35 : Integer.Sparse Key := [(key578, -1), (key578, -1), (key583, 2), (key568, 1), (key568, 1), (key601, -1), (key601, -1), (key572, -2), (key595, 1), (key595, 1), (key335, 1), (key335, 1), (key340, -2), (key267, -1), (key267, -1), (key475, 1), (key475, 1), (key271, 2), (key469, -1), (key469, -1), (key305, -1), (key305, -1), (key328, 1), (key328, 1), (key239, 1), (key239, 1), (key418, -1), (key418, -1), (key260, -1), (key260, -1), (key397, 1), (key397, 1), (key302, 2), (key316, -1), (key316, -1), (key236, -2), (key406, 1), (key406, 1), (key248, 1), (key248, 1), (key316, -1), (key316, -1)]

theorem rawRowCheck35 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form0 = rawRow35 := by decide +kernel

def row35 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key260, -2), (key267, -2), (key271, 2), (key302, 2), (key305, -2), (key316, -4), (key328, 2), (key335, 2), (key340, -2), (key397, 2), (key406, 2), (key418, -2), (key469, -2), (key475, 2), (key568, 2), (key572, -2), (key578, -2), (key583, 2), (key595, 2), (key601, -2)]

theorem rowCheck35 : row35 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow35 := by decide +kernel

theorem rowEval35 (x : Key → ℝ) : Integer.Sparse.eval row35 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck35, Integer.Sparse.eval_collectBalanced, rawRowCheck35]

def rawRow36 : Integer.Sparse Key := [(key578, -1), (key583, -1), (key578, 2), (key593, 1), (key601, 1), (key568, -1), (key593, -1), (key595, -2), (key572, 1), (key595, 1), (key335, 1), (key340, 1), (key335, -2), (key467, -1), (key475, -1), (key267, 1), (key467, 1), (key469, 2), (key271, -1), (key469, -1), (key319, -1), (key328, -1), (key305, 1), (key319, 1), (key409, 1), (key418, 1), (key239, -1), (key409, -1), (key397, -1), (key442, -1), (key260, 1), (key442, 1), (key316, 2), (key302, -1), (key316, -1), (key406, -2), (key236, 1), (key406, 1), (key316, 1), (key435, 1), (key248, -1), (key435, -1)]

theorem rawRowCheck36 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form0 = rawRow36 := by decide +kernel

def row36 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 2), (key328, -1), (key335, -1), (key340, 1), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

theorem rowCheck36 : row36 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow36 := by decide +kernel

theorem rowEval36 (x : Key → ℝ) : Integer.Sparse.eval row36 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck36, Integer.Sparse.eval_collectBalanced, rawRowCheck36]

def rawRow37 : Integer.Sparse Key := [(key583, -1), (key578, -1), (key578, 2), (key601, 1), (key593, 1), (key593, -1), (key568, -1), (key595, -2), (key595, 1), (key572, 1), (key340, 1), (key335, 1), (key335, -2), (key475, -1), (key467, -1), (key467, 1), (key267, 1), (key469, 2), (key469, -1), (key271, -1), (key328, -1), (key319, -1), (key319, 1), (key305, 1), (key418, 1), (key409, 1), (key409, -1), (key239, -1), (key442, -1), (key397, -1), (key442, 1), (key260, 1), (key316, 2), (key316, -1), (key302, -1), (key406, -2), (key406, 1), (key236, 1), (key435, 1), (key316, 1), (key435, -1), (key248, -1)]

theorem rawRowCheck37 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form0 = rawRow37 := by decide +kernel

def row37 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 2), (key328, -1), (key335, -1), (key340, 1), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

theorem rowCheck37 : row37 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow37 := by decide +kernel

theorem rowEval37 (x : Key → ℝ) : Integer.Sparse.eval row37 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck37, Integer.Sparse.eval_collectBalanced, rawRowCheck37]

def rawRow38 : Integer.Sparse Key := [(key593, -1), (key595, -1), (key601, 2), (key568, 1), (key572, 1), (key583, -1), (key601, -1), (key568, -2), (key578, 1), (key593, 1), (key467, 1), (key469, 1), (key475, -2), (key267, -1), (key271, -1), (key340, 1), (key475, 1), (key267, 2), (key335, -1), (key467, -1), (key388, -1), (key397, -1), (key418, 1), (key450, 1), (key251, 1), (key260, 1), (key328, -1), (key450, -1), (key239, -1), (key251, -1), (key305, 1), (key388, 1), (key385, 2), (key406, -1), (key435, -1), (key248, -2), (key316, 1), (key435, 1), (key236, 1), (key248, 1), (key302, -1), (key316, -1)]

theorem rawRowCheck38 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form0 = rawRow38 := by decide +kernel

def row38 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key328, -1), (key335, -1), (key340, 1), (key385, 2), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

theorem rowCheck38 : row38 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow38 := by decide +kernel

theorem rowEval38 (x : Key → ℝ) : Integer.Sparse.eval row38 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck38, Integer.Sparse.eval_collectBalanced, rawRowCheck38]

def rawRow39 : Integer.Sparse Key := [(key595, -1), (key593, -1), (key601, 2), (key572, 1), (key568, 1), (key601, -1), (key583, -1), (key568, -2), (key593, 1), (key578, 1), (key469, 1), (key467, 1), (key475, -2), (key271, -1), (key267, -1), (key475, 1), (key340, 1), (key267, 2), (key467, -1), (key335, -1), (key397, -1), (key388, -1), (key450, 1), (key418, 1), (key260, 1), (key251, 1), (key450, -1), (key328, -1), (key251, -1), (key239, -1), (key388, 1), (key305, 1), (key385, 2), (key435, -1), (key406, -1), (key248, -2), (key435, 1), (key316, 1), (key248, 1), (key236, 1), (key316, -1), (key302, -1)]

theorem rawRowCheck39 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form0 = rawRow39 := by decide +kernel

def row39 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key328, -1), (key335, -1), (key340, 1), (key385, 2), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

theorem rowCheck39 : row39 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow39 := by decide +kernel

theorem rowEval39 (x : Key → ℝ) : Integer.Sparse.eval row39 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck39, Integer.Sparse.eval_collectBalanced, rawRowCheck39]

def rawRow40 : Integer.Sparse Key := [(key593, -1), (key601, -1), (key595, 2), (key578, 1), (key583, 1), (key572, -1), (key595, -1), (key578, -2), (key568, 1), (key593, 1), (key467, 1), (key475, 1), (key469, -2), (key335, -1), (key340, -1), (key271, 1), (key469, 1), (key335, 2), (key267, -1), (key467, -1), (key409, -1), (key418, -1), (key397, 1), (key442, 1), (key319, 1), (key328, 1), (key260, -1), (key442, -1), (key305, -1), (key319, -1), (key239, 1), (key409, 1), (key406, 2), (key385, -1), (key435, -1), (key316, -2), (key248, 1), (key435, 1), (key302, 1), (key316, 1), (key236, -1), (key406, -1)]

theorem rawRowCheck40 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form0 = rawRow40 := by decide +kernel

def row40 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck40 : row40 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow40 := by decide +kernel

theorem rowEval40 (x : Key → ℝ) : Integer.Sparse.eval row40 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck40, Integer.Sparse.eval_collectBalanced, rawRowCheck40]

def rawRow41 : Integer.Sparse Key := [(key601, -1), (key593, -1), (key595, 2), (key583, 1), (key578, 1), (key595, -1), (key572, -1), (key578, -2), (key593, 1), (key568, 1), (key475, 1), (key467, 1), (key469, -2), (key340, -1), (key335, -1), (key469, 1), (key271, 1), (key335, 2), (key467, -1), (key267, -1), (key418, -1), (key409, -1), (key442, 1), (key397, 1), (key328, 1), (key319, 1), (key442, -1), (key260, -1), (key319, -1), (key305, -1), (key409, 1), (key239, 1), (key406, 2), (key435, -1), (key385, -1), (key316, -2), (key435, 1), (key248, 1), (key316, 1), (key302, 1), (key406, -1), (key236, -1)]

theorem rawRowCheck41 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form0 = rawRow41 := by decide +kernel

def row41 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck41 : row41 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow41 := by decide +kernel

theorem rowEval41 (x : Key → ℝ) : Integer.Sparse.eval row41 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck41, Integer.Sparse.eval_collectBalanced, rawRowCheck41]

def rawRow42 : Integer.Sparse Key := [(key1296, -1), (key1296, -1), (key1302, 2), (key1316, 1), (key1316, 1), (key1339, -1), (key1339, -1), (key1329, -2), (key1345, 1), (key1345, 1), (key1391, 1), (key1391, 1), (key1397, -2), (key1546, -1), (key1546, -1), (key1774, 1), (key1774, 1), (key1559, 2), (key1780, -1), (key1780, -1), (key1424, -1), (key1424, -1), (key1457, 1), (key1457, 1), (key1573, 1), (key1573, 1), (key1790, -1), (key1790, -1), (key1659, -1), (key1659, -1), (key1817, 1), (key1817, 1), (key1447, 2), (key1466, -1), (key1466, -1), (key1596, -2), (key1798, 1), (key1798, 1), (key1667, 1), (key1667, 1), (key1825, -1), (key1825, -1)]

theorem rawRowCheck42 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form0 = rawRow42 := by decide +kernel

def row42 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1546, -2), (key1559, 2), (key1573, 2), (key1596, -2), (key1659, -2), (key1667, 2), (key1774, 2), (key1780, -2), (key1790, -2), (key1798, 2), (key1817, 2), (key1825, -2)]

theorem rowCheck42 : row42 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow42 := by decide +kernel

theorem rowEval42 (x : Key → ℝ) : Integer.Sparse.eval row42 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck42, Integer.Sparse.eval_collectBalanced, rawRowCheck42]

def rawRow43 : Integer.Sparse Key := [(key1296, -1), (key1302, -1), (key1296, 2), (key1337, 1), (key1339, 1), (key1316, -1), (key1337, -1), (key1345, -2), (key1329, 1), (key1345, 1), (key1391, 1), (key1397, 1), (key1391, -2), (key1772, -1), (key1774, -1), (key1546, 1), (key1772, 1), (key1780, 2), (key1559, -1), (key1780, -1), (key1455, -1), (key1457, -1), (key1424, 1), (key1455, 1), (key1788, 1), (key1790, 1), (key1573, -1), (key1788, -1), (key1817, -1), (key1841, -1), (key1659, 1), (key1841, 1), (key1466, 2), (key1447, -1), (key1466, -1), (key1798, -2), (key1596, 1), (key1798, 1), (key1825, 1), (key1844, 1), (key1667, -1), (key1844, -1)]

theorem rawRowCheck43 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form0 = rawRow43 := by decide +kernel

def row43 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck43 : row43 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow43 := by decide +kernel

theorem rowEval43 (x : Key → ℝ) : Integer.Sparse.eval row43 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck43, Integer.Sparse.eval_collectBalanced, rawRowCheck43]

def rawRow44 : Integer.Sparse Key := [(key1302, -1), (key1296, -1), (key1296, 2), (key1339, 1), (key1337, 1), (key1337, -1), (key1316, -1), (key1345, -2), (key1345, 1), (key1329, 1), (key1397, 1), (key1391, 1), (key1391, -2), (key1774, -1), (key1772, -1), (key1772, 1), (key1546, 1), (key1780, 2), (key1780, -1), (key1559, -1), (key1457, -1), (key1455, -1), (key1455, 1), (key1424, 1), (key1790, 1), (key1788, 1), (key1788, -1), (key1573, -1), (key1841, -1), (key1817, -1), (key1841, 1), (key1659, 1), (key1466, 2), (key1466, -1), (key1447, -1), (key1798, -2), (key1798, 1), (key1596, 1), (key1844, 1), (key1825, 1), (key1844, -1), (key1667, -1)]

theorem rawRowCheck44 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form0 = rawRow44 := by decide +kernel

def row44 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck44 : row44 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow44 := by decide +kernel

theorem rowEval44 (x : Key → ℝ) : Integer.Sparse.eval row44 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck44, Integer.Sparse.eval_collectBalanced, rawRowCheck44]

def rawRow45 : Integer.Sparse Key := [(key1316, -1), (key1316, -1), (key1329, 2), (key1296, 1), (key1296, 1), (key1345, -1), (key1345, -1), (key1302, -2), (key1339, 1), (key1339, 1), (key1546, 1), (key1546, 1), (key1559, -2), (key1391, -1), (key1391, -1), (key1780, 1), (key1780, 1), (key1397, 2), (key1774, -1), (key1774, -1), (key1573, -1), (key1573, -1), (key1659, 1), (key1659, 1), (key1424, 1), (key1424, 1), (key1817, -1), (key1817, -1), (key1457, -1), (key1457, -1), (key1790, 1), (key1790, 1), (key1596, 2), (key1667, -1), (key1667, -1), (key1447, -2), (key1825, 1), (key1825, 1), (key1466, 1), (key1466, 1), (key1798, -1), (key1798, -1)]

theorem rawRowCheck45 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form0 = rawRow45 := by decide +kernel

def row45 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1546, 2), (key1559, -2), (key1573, -2), (key1596, 2), (key1659, 2), (key1667, -2), (key1774, -2), (key1780, 2), (key1790, 2), (key1798, -2), (key1817, -2), (key1825, 2)]

theorem rowCheck45 : row45 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow45 := by decide +kernel

theorem rowEval45 (x : Key → ℝ) : Integer.Sparse.eval row45 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck45, Integer.Sparse.eval_collectBalanced, rawRowCheck45]

def rawRow46 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1316, 2), (key1337, 1), (key1345, 1), (key1296, -1), (key1337, -1), (key1339, -2), (key1302, 1), (key1339, 1), (key1546, 1), (key1559, 1), (key1546, -2), (key1772, -1), (key1780, -1), (key1391, 1), (key1772, 1), (key1774, 2), (key1397, -1), (key1774, -1), (key1655, -1), (key1659, -1), (key1573, 1), (key1655, 1), (key1813, 1), (key1817, 1), (key1424, -1), (key1813, -1), (key1790, -1), (key1839, -1), (key1457, 1), (key1839, 1), (key1667, 2), (key1596, -1), (key1667, -1), (key1825, -2), (key1447, 1), (key1825, 1), (key1798, 1), (key1844, 1), (key1466, -1), (key1844, -1)]

theorem rawRowCheck46 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form0 = rawRow46 := by decide +kernel

def row46 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck46 : row46 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow46 := by decide +kernel

theorem rowEval46 (x : Key → ℝ) : Integer.Sparse.eval row46 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck46, Integer.Sparse.eval_collectBalanced, rawRowCheck46]

def rawRow47 : Integer.Sparse Key := [(key1329, -1), (key1316, -1), (key1316, 2), (key1345, 1), (key1337, 1), (key1337, -1), (key1296, -1), (key1339, -2), (key1339, 1), (key1302, 1), (key1559, 1), (key1546, 1), (key1546, -2), (key1780, -1), (key1772, -1), (key1772, 1), (key1391, 1), (key1774, 2), (key1774, -1), (key1397, -1), (key1659, -1), (key1655, -1), (key1655, 1), (key1573, 1), (key1817, 1), (key1813, 1), (key1813, -1), (key1424, -1), (key1839, -1), (key1790, -1), (key1839, 1), (key1457, 1), (key1667, 2), (key1667, -1), (key1596, -1), (key1825, -2), (key1825, 1), (key1447, 1), (key1844, 1), (key1798, 1), (key1844, -1), (key1466, -1)]

theorem rawRowCheck47 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form0 = rawRow47 := by decide +kernel

def row47 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck47 : row47 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow47 := by decide +kernel

theorem rowEval47 (x : Key → ℝ) : Integer.Sparse.eval row47 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck47, Integer.Sparse.eval_collectBalanced, rawRowCheck47]

def rawRow48 : Integer.Sparse Key := [(key1337, -1), (key1339, -1), (key1345, 2), (key1296, 1), (key1302, 1), (key1329, -1), (key1345, -1), (key1296, -2), (key1316, 1), (key1337, 1), (key1772, 1), (key1774, 1), (key1780, -2), (key1391, -1), (key1397, -1), (key1559, 1), (key1780, 1), (key1391, 2), (key1546, -1), (key1772, -1), (key1788, -1), (key1790, -1), (key1817, 1), (key1841, 1), (key1455, 1), (key1457, 1), (key1659, -1), (key1841, -1), (key1424, -1), (key1455, -1), (key1573, 1), (key1788, 1), (key1798, 2), (key1825, -1), (key1844, -1), (key1466, -2), (key1667, 1), (key1844, 1), (key1447, 1), (key1466, 1), (key1596, -1), (key1798, -1)]

theorem rawRowCheck48 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form0 = rawRow48 := by decide +kernel

def row48 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck48 : row48 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow48 := by decide +kernel

theorem rowEval48 (x : Key → ℝ) : Integer.Sparse.eval row48 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck48, Integer.Sparse.eval_collectBalanced, rawRowCheck48]

def rawRow49 : Integer.Sparse Key := [(key1339, -1), (key1337, -1), (key1345, 2), (key1302, 1), (key1296, 1), (key1345, -1), (key1329, -1), (key1296, -2), (key1337, 1), (key1316, 1), (key1774, 1), (key1772, 1), (key1780, -2), (key1397, -1), (key1391, -1), (key1780, 1), (key1559, 1), (key1391, 2), (key1772, -1), (key1546, -1), (key1790, -1), (key1788, -1), (key1841, 1), (key1817, 1), (key1457, 1), (key1455, 1), (key1841, -1), (key1659, -1), (key1455, -1), (key1424, -1), (key1788, 1), (key1573, 1), (key1798, 2), (key1844, -1), (key1825, -1), (key1466, -2), (key1844, 1), (key1667, 1), (key1466, 1), (key1447, 1), (key1798, -1), (key1596, -1)]

theorem rawRowCheck49 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form0 = rawRow49 := by decide +kernel

def row49 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck49 : row49 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow49 := by decide +kernel

theorem rowEval49 (x : Key → ℝ) : Integer.Sparse.eval row49 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck49, Integer.Sparse.eval_collectBalanced, rawRowCheck49]

def rawRow50 : Integer.Sparse Key := [(key1337, -1), (key1345, -1), (key1339, 2), (key1316, 1), (key1329, 1), (key1302, -1), (key1339, -1), (key1316, -2), (key1296, 1), (key1337, 1), (key1772, 1), (key1780, 1), (key1774, -2), (key1546, -1), (key1559, -1), (key1397, 1), (key1774, 1), (key1546, 2), (key1391, -1), (key1772, -1), (key1813, -1), (key1817, -1), (key1790, 1), (key1839, 1), (key1655, 1), (key1659, 1), (key1457, -1), (key1839, -1), (key1573, -1), (key1655, -1), (key1424, 1), (key1813, 1), (key1825, 2), (key1798, -1), (key1844, -1), (key1667, -2), (key1466, 1), (key1844, 1), (key1596, 1), (key1667, 1), (key1447, -1), (key1825, -1)]

theorem rawRowCheck50 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form0 = rawRow50 := by decide +kernel

def row50 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck50 : row50 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow50 := by decide +kernel

theorem rowEval50 (x : Key → ℝ) : Integer.Sparse.eval row50 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck50, Integer.Sparse.eval_collectBalanced, rawRowCheck50]

def rawRow51 : Integer.Sparse Key := [(key1345, -1), (key1337, -1), (key1339, 2), (key1329, 1), (key1316, 1), (key1339, -1), (key1302, -1), (key1316, -2), (key1337, 1), (key1296, 1), (key1780, 1), (key1772, 1), (key1774, -2), (key1559, -1), (key1546, -1), (key1774, 1), (key1397, 1), (key1546, 2), (key1772, -1), (key1391, -1), (key1817, -1), (key1813, -1), (key1839, 1), (key1790, 1), (key1659, 1), (key1655, 1), (key1839, -1), (key1457, -1), (key1655, -1), (key1573, -1), (key1813, 1), (key1424, 1), (key1825, 2), (key1844, -1), (key1798, -1), (key1667, -2), (key1844, 1), (key1466, 1), (key1667, 1), (key1596, 1), (key1825, -1), (key1447, -1)]

theorem rawRowCheck51 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form0 = rawRow51 := by decide +kernel

def row51 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck51 : row51 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow51 := by decide +kernel

theorem rowEval51 (x : Key → ℝ) : Integer.Sparse.eval row51 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck51, Integer.Sparse.eval_collectBalanced, rawRowCheck51]

def rawRow52 : Integer.Sparse Key := [(key1391, -1), (key1391, -1), (key1397, 2), (key1424, 1), (key1424, 1), (key1457, -1), (key1457, -1), (key1447, -2), (key1466, 1), (key1466, 1), (key1296, 1), (key1296, 1), (key1302, -2), (key1573, -1), (key1573, -1), (key1790, 1), (key1790, 1), (key1596, 2), (key1798, -1), (key1798, -1), (key1316, -1), (key1316, -1), (key1339, 1), (key1339, 1), (key1546, 1), (key1546, 1), (key1774, -1), (key1774, -1), (key1667, -1), (key1667, -1), (key1825, 1), (key1825, 1), (key1329, 2), (key1345, -1), (key1345, -1), (key1559, -2), (key1780, 1), (key1780, 1), (key1659, 1), (key1659, 1), (key1817, -1), (key1817, -1)]

theorem rawRowCheck52 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form0 = rawRow52 := by decide +kernel

def row52 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1546, 2), (key1559, -2), (key1573, -2), (key1596, 2), (key1659, 2), (key1667, -2), (key1774, -2), (key1780, 2), (key1790, 2), (key1798, -2), (key1817, -2), (key1825, 2)]

theorem rowCheck52 : row52 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow52 := by decide +kernel

theorem rowEval52 (x : Key → ℝ) : Integer.Sparse.eval row52 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck52, Integer.Sparse.eval_collectBalanced, rawRowCheck52]

def rawRow53 : Integer.Sparse Key := [(key1391, -1), (key1397, -1), (key1391, 2), (key1455, 1), (key1457, 1), (key1424, -1), (key1455, -1), (key1466, -2), (key1447, 1), (key1466, 1), (key1296, 1), (key1302, 1), (key1296, -2), (key1788, -1), (key1790, -1), (key1573, 1), (key1788, 1), (key1798, 2), (key1596, -1), (key1798, -1), (key1337, -1), (key1339, -1), (key1316, 1), (key1337, 1), (key1772, 1), (key1774, 1), (key1546, -1), (key1772, -1), (key1825, -1), (key1844, -1), (key1667, 1), (key1844, 1), (key1345, 2), (key1329, -1), (key1345, -1), (key1780, -2), (key1559, 1), (key1780, 1), (key1817, 1), (key1841, 1), (key1659, -1), (key1841, -1)]

theorem rawRowCheck53 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form0 = rawRow53 := by decide +kernel

def row53 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck53 : row53 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow53 := by decide +kernel

theorem rowEval53 (x : Key → ℝ) : Integer.Sparse.eval row53 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck53, Integer.Sparse.eval_collectBalanced, rawRowCheck53]

def rawRow54 : Integer.Sparse Key := [(key1397, -1), (key1391, -1), (key1391, 2), (key1457, 1), (key1455, 1), (key1455, -1), (key1424, -1), (key1466, -2), (key1466, 1), (key1447, 1), (key1302, 1), (key1296, 1), (key1296, -2), (key1790, -1), (key1788, -1), (key1788, 1), (key1573, 1), (key1798, 2), (key1798, -1), (key1596, -1), (key1339, -1), (key1337, -1), (key1337, 1), (key1316, 1), (key1774, 1), (key1772, 1), (key1772, -1), (key1546, -1), (key1844, -1), (key1825, -1), (key1844, 1), (key1667, 1), (key1345, 2), (key1345, -1), (key1329, -1), (key1780, -2), (key1780, 1), (key1559, 1), (key1841, 1), (key1817, 1), (key1841, -1), (key1659, -1)]

theorem rawRowCheck54 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form0 = rawRow54 := by decide +kernel

def row54 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck54 : row54 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow54 := by decide +kernel

theorem rowEval54 (x : Key → ℝ) : Integer.Sparse.eval row54 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck54, Integer.Sparse.eval_collectBalanced, rawRowCheck54]

def rawRow55 : Integer.Sparse Key := [(key1424, -1), (key1424, -1), (key1447, 2), (key1391, 1), (key1391, 1), (key1466, -1), (key1466, -1), (key1397, -2), (key1457, 1), (key1457, 1), (key1573, 1), (key1573, 1), (key1596, -2), (key1296, -1), (key1296, -1), (key1798, 1), (key1798, 1), (key1302, 2), (key1790, -1), (key1790, -1), (key1546, -1), (key1546, -1), (key1667, 1), (key1667, 1), (key1316, 1), (key1316, 1), (key1825, -1), (key1825, -1), (key1339, -1), (key1339, -1), (key1774, 1), (key1774, 1), (key1559, 2), (key1659, -1), (key1659, -1), (key1329, -2), (key1817, 1), (key1817, 1), (key1345, 1), (key1345, 1), (key1780, -1), (key1780, -1)]

theorem rawRowCheck55 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form0 = rawRow55 := by decide +kernel

def row55 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1546, -2), (key1559, 2), (key1573, 2), (key1596, -2), (key1659, -2), (key1667, 2), (key1774, 2), (key1780, -2), (key1790, -2), (key1798, 2), (key1817, 2), (key1825, -2)]

theorem rowCheck55 : row55 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow55 := by decide +kernel

theorem rowEval55 (x : Key → ℝ) : Integer.Sparse.eval row55 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck55, Integer.Sparse.eval_collectBalanced, rawRowCheck55]

def rawRow56 : Integer.Sparse Key := [(key1424, -1), (key1447, -1), (key1424, 2), (key1455, 1), (key1466, 1), (key1391, -1), (key1455, -1), (key1457, -2), (key1397, 1), (key1457, 1), (key1573, 1), (key1596, 1), (key1573, -2), (key1788, -1), (key1798, -1), (key1296, 1), (key1788, 1), (key1790, 2), (key1302, -1), (key1790, -1), (key1655, -1), (key1667, -1), (key1546, 1), (key1655, 1), (key1813, 1), (key1825, 1), (key1316, -1), (key1813, -1), (key1774, -1), (key1839, -1), (key1339, 1), (key1839, 1), (key1659, 2), (key1559, -1), (key1659, -1), (key1817, -2), (key1329, 1), (key1817, 1), (key1780, 1), (key1841, 1), (key1345, -1), (key1841, -1)]

theorem rawRowCheck56 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form0 = rawRow56 := by decide +kernel

def row56 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck56 : row56 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow56 := by decide +kernel

theorem rowEval56 (x : Key → ℝ) : Integer.Sparse.eval row56 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck56, Integer.Sparse.eval_collectBalanced, rawRowCheck56]

def rawRow57 : Integer.Sparse Key := [(key1447, -1), (key1424, -1), (key1424, 2), (key1466, 1), (key1455, 1), (key1455, -1), (key1391, -1), (key1457, -2), (key1457, 1), (key1397, 1), (key1596, 1), (key1573, 1), (key1573, -2), (key1798, -1), (key1788, -1), (key1788, 1), (key1296, 1), (key1790, 2), (key1790, -1), (key1302, -1), (key1667, -1), (key1655, -1), (key1655, 1), (key1546, 1), (key1825, 1), (key1813, 1), (key1813, -1), (key1316, -1), (key1839, -1), (key1774, -1), (key1839, 1), (key1339, 1), (key1659, 2), (key1659, -1), (key1559, -1), (key1817, -2), (key1817, 1), (key1329, 1), (key1841, 1), (key1780, 1), (key1841, -1), (key1345, -1)]

theorem rawRowCheck57 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form0 = rawRow57 := by decide +kernel

def row57 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck57 : row57 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow57 := by decide +kernel

theorem rowEval57 (x : Key → ℝ) : Integer.Sparse.eval row57 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck57, Integer.Sparse.eval_collectBalanced, rawRowCheck57]

def rawRow58 : Integer.Sparse Key := [(key1455, -1), (key1457, -1), (key1466, 2), (key1391, 1), (key1397, 1), (key1447, -1), (key1466, -1), (key1391, -2), (key1424, 1), (key1455, 1), (key1788, 1), (key1790, 1), (key1798, -2), (key1296, -1), (key1302, -1), (key1596, 1), (key1798, 1), (key1296, 2), (key1573, -1), (key1788, -1), (key1772, -1), (key1774, -1), (key1825, 1), (key1844, 1), (key1337, 1), (key1339, 1), (key1667, -1), (key1844, -1), (key1316, -1), (key1337, -1), (key1546, 1), (key1772, 1), (key1780, 2), (key1817, -1), (key1841, -1), (key1345, -2), (key1659, 1), (key1841, 1), (key1329, 1), (key1345, 1), (key1559, -1), (key1780, -1)]

theorem rawRowCheck58 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form0 = rawRow58 := by decide +kernel

def row58 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck58 : row58 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow58 := by decide +kernel

theorem rowEval58 (x : Key → ℝ) : Integer.Sparse.eval row58 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck58, Integer.Sparse.eval_collectBalanced, rawRowCheck58]

def rawRow59 : Integer.Sparse Key := [(key1457, -1), (key1455, -1), (key1466, 2), (key1397, 1), (key1391, 1), (key1466, -1), (key1447, -1), (key1391, -2), (key1455, 1), (key1424, 1), (key1790, 1), (key1788, 1), (key1798, -2), (key1302, -1), (key1296, -1), (key1798, 1), (key1596, 1), (key1296, 2), (key1788, -1), (key1573, -1), (key1774, -1), (key1772, -1), (key1844, 1), (key1825, 1), (key1339, 1), (key1337, 1), (key1844, -1), (key1667, -1), (key1337, -1), (key1316, -1), (key1772, 1), (key1546, 1), (key1780, 2), (key1841, -1), (key1817, -1), (key1345, -2), (key1841, 1), (key1659, 1), (key1345, 1), (key1329, 1), (key1780, -1), (key1559, -1)]

theorem rawRowCheck59 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form0 = rawRow59 := by decide +kernel

def row59 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck59 : row59 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow59 := by decide +kernel

theorem rowEval59 (x : Key → ℝ) : Integer.Sparse.eval row59 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck59, Integer.Sparse.eval_collectBalanced, rawRowCheck59]

def rawRow60 : Integer.Sparse Key := [(key1455, -1), (key1466, -1), (key1457, 2), (key1424, 1), (key1447, 1), (key1397, -1), (key1457, -1), (key1424, -2), (key1391, 1), (key1455, 1), (key1788, 1), (key1798, 1), (key1790, -2), (key1573, -1), (key1596, -1), (key1302, 1), (key1790, 1), (key1573, 2), (key1296, -1), (key1788, -1), (key1813, -1), (key1825, -1), (key1774, 1), (key1839, 1), (key1655, 1), (key1667, 1), (key1339, -1), (key1839, -1), (key1546, -1), (key1655, -1), (key1316, 1), (key1813, 1), (key1817, 2), (key1780, -1), (key1841, -1), (key1659, -2), (key1345, 1), (key1841, 1), (key1559, 1), (key1659, 1), (key1329, -1), (key1817, -1)]

theorem rawRowCheck60 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form0 = rawRow60 := by decide +kernel

def row60 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck60 : row60 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow60 := by decide +kernel

theorem rowEval60 (x : Key → ℝ) : Integer.Sparse.eval row60 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck60, Integer.Sparse.eval_collectBalanced, rawRowCheck60]

def rawRow61 : Integer.Sparse Key := [(key1466, -1), (key1455, -1), (key1457, 2), (key1447, 1), (key1424, 1), (key1457, -1), (key1397, -1), (key1424, -2), (key1455, 1), (key1391, 1), (key1798, 1), (key1788, 1), (key1790, -2), (key1596, -1), (key1573, -1), (key1790, 1), (key1302, 1), (key1573, 2), (key1788, -1), (key1296, -1), (key1825, -1), (key1813, -1), (key1839, 1), (key1774, 1), (key1667, 1), (key1655, 1), (key1839, -1), (key1339, -1), (key1655, -1), (key1546, -1), (key1813, 1), (key1316, 1), (key1817, 2), (key1841, -1), (key1780, -1), (key1659, -2), (key1841, 1), (key1345, 1), (key1659, 1), (key1559, 1), (key1817, -1), (key1329, -1)]

theorem rawRowCheck61 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form0 = rawRow61 := by decide +kernel

def row61 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck61 : row61 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow61 := by decide +kernel

theorem rowEval61 (x : Key → ℝ) : Integer.Sparse.eval row61 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck61, Integer.Sparse.eval_collectBalanced, rawRowCheck61]

def rawRow62 : Integer.Sparse Key := [(key1546, -1), (key1546, -1), (key1559, 2), (key1573, 1), (key1573, 1), (key1659, -1), (key1659, -1), (key1596, -2), (key1667, 1), (key1667, 1), (key1316, 1), (key1316, 1), (key1329, -2), (key1424, -1), (key1424, -1), (key1817, 1), (key1817, 1), (key1447, 2), (key1825, -1), (key1825, -1), (key1296, -1), (key1296, -1), (key1345, 1), (key1345, 1), (key1391, 1), (key1391, 1), (key1780, -1), (key1780, -1), (key1466, -1), (key1466, -1), (key1798, 1), (key1798, 1), (key1302, 2), (key1339, -1), (key1339, -1), (key1397, -2), (key1774, 1), (key1774, 1), (key1457, 1), (key1457, 1), (key1790, -1), (key1790, -1)]

theorem rawRowCheck62 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form0 = rawRow62 := by decide +kernel

def row62 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1546, -2), (key1559, 2), (key1573, 2), (key1596, -2), (key1659, -2), (key1667, 2), (key1774, 2), (key1780, -2), (key1790, -2), (key1798, 2), (key1817, 2), (key1825, -2)]

theorem rowCheck62 : row62 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow62 := by decide +kernel

theorem rowEval62 (x : Key → ℝ) : Integer.Sparse.eval row62 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck62, Integer.Sparse.eval_collectBalanced, rawRowCheck62]

def rawRow63 : Integer.Sparse Key := [(key1546, -1), (key1559, -1), (key1546, 2), (key1655, 1), (key1659, 1), (key1573, -1), (key1655, -1), (key1667, -2), (key1596, 1), (key1667, 1), (key1316, 1), (key1329, 1), (key1316, -2), (key1813, -1), (key1817, -1), (key1424, 1), (key1813, 1), (key1825, 2), (key1447, -1), (key1825, -1), (key1337, -1), (key1345, -1), (key1296, 1), (key1337, 1), (key1772, 1), (key1780, 1), (key1391, -1), (key1772, -1), (key1798, -1), (key1844, -1), (key1466, 1), (key1844, 1), (key1339, 2), (key1302, -1), (key1339, -1), (key1774, -2), (key1397, 1), (key1774, 1), (key1790, 1), (key1839, 1), (key1457, -1), (key1839, -1)]

theorem rawRowCheck63 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form0 = rawRow63 := by decide +kernel

def row63 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck63 : row63 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow63 := by decide +kernel

theorem rowEval63 (x : Key → ℝ) : Integer.Sparse.eval row63 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck63, Integer.Sparse.eval_collectBalanced, rawRowCheck63]

def rawRow64 : Integer.Sparse Key := [(key1559, -1), (key1546, -1), (key1546, 2), (key1659, 1), (key1655, 1), (key1655, -1), (key1573, -1), (key1667, -2), (key1667, 1), (key1596, 1), (key1329, 1), (key1316, 1), (key1316, -2), (key1817, -1), (key1813, -1), (key1813, 1), (key1424, 1), (key1825, 2), (key1825, -1), (key1447, -1), (key1345, -1), (key1337, -1), (key1337, 1), (key1296, 1), (key1780, 1), (key1772, 1), (key1772, -1), (key1391, -1), (key1844, -1), (key1798, -1), (key1844, 1), (key1466, 1), (key1339, 2), (key1339, -1), (key1302, -1), (key1774, -2), (key1774, 1), (key1397, 1), (key1839, 1), (key1790, 1), (key1839, -1), (key1457, -1)]

theorem rawRowCheck64 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form0 = rawRow64 := by decide +kernel

def row64 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck64 : row64 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow64 := by decide +kernel

theorem rowEval64 (x : Key → ℝ) : Integer.Sparse.eval row64 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck64, Integer.Sparse.eval_collectBalanced, rawRowCheck64]

def rawRow65 : Integer.Sparse Key := [(key1573, -1), (key1573, -1), (key1596, 2), (key1546, 1), (key1546, 1), (key1667, -1), (key1667, -1), (key1559, -2), (key1659, 1), (key1659, 1), (key1424, 1), (key1424, 1), (key1447, -2), (key1316, -1), (key1316, -1), (key1825, 1), (key1825, 1), (key1329, 2), (key1817, -1), (key1817, -1), (key1391, -1), (key1391, -1), (key1466, 1), (key1466, 1), (key1296, 1), (key1296, 1), (key1798, -1), (key1798, -1), (key1345, -1), (key1345, -1), (key1780, 1), (key1780, 1), (key1397, 2), (key1457, -1), (key1457, -1), (key1302, -2), (key1790, 1), (key1790, 1), (key1339, 1), (key1339, 1), (key1774, -1), (key1774, -1)]

theorem rawRowCheck65 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form0 = rawRow65 := by decide +kernel

def row65 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1546, 2), (key1559, -2), (key1573, -2), (key1596, 2), (key1659, 2), (key1667, -2), (key1774, -2), (key1780, 2), (key1790, 2), (key1798, -2), (key1817, -2), (key1825, 2)]

theorem rowCheck65 : row65 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow65 := by decide +kernel

theorem rowEval65 (x : Key → ℝ) : Integer.Sparse.eval row65 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck65, Integer.Sparse.eval_collectBalanced, rawRowCheck65]

def rawRow66 : Integer.Sparse Key := [(key1573, -1), (key1596, -1), (key1573, 2), (key1655, 1), (key1667, 1), (key1546, -1), (key1655, -1), (key1659, -2), (key1559, 1), (key1659, 1), (key1424, 1), (key1447, 1), (key1424, -2), (key1813, -1), (key1825, -1), (key1316, 1), (key1813, 1), (key1817, 2), (key1329, -1), (key1817, -1), (key1455, -1), (key1466, -1), (key1391, 1), (key1455, 1), (key1788, 1), (key1798, 1), (key1296, -1), (key1788, -1), (key1780, -1), (key1841, -1), (key1345, 1), (key1841, 1), (key1457, 2), (key1397, -1), (key1457, -1), (key1790, -2), (key1302, 1), (key1790, 1), (key1774, 1), (key1839, 1), (key1339, -1), (key1839, -1)]

theorem rawRowCheck66 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form0 = rawRow66 := by decide +kernel

def row66 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck66 : row66 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow66 := by decide +kernel

theorem rowEval66 (x : Key → ℝ) : Integer.Sparse.eval row66 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck66, Integer.Sparse.eval_collectBalanced, rawRowCheck66]

def rawRow67 : Integer.Sparse Key := [(key1596, -1), (key1573, -1), (key1573, 2), (key1667, 1), (key1655, 1), (key1655, -1), (key1546, -1), (key1659, -2), (key1659, 1), (key1559, 1), (key1447, 1), (key1424, 1), (key1424, -2), (key1825, -1), (key1813, -1), (key1813, 1), (key1316, 1), (key1817, 2), (key1817, -1), (key1329, -1), (key1466, -1), (key1455, -1), (key1455, 1), (key1391, 1), (key1798, 1), (key1788, 1), (key1788, -1), (key1296, -1), (key1841, -1), (key1780, -1), (key1841, 1), (key1345, 1), (key1457, 2), (key1457, -1), (key1397, -1), (key1790, -2), (key1790, 1), (key1302, 1), (key1839, 1), (key1774, 1), (key1839, -1), (key1339, -1)]

theorem rawRowCheck67 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form0 = rawRow67 := by decide +kernel

def row67 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck67 : row67 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow67 := by decide +kernel

theorem rowEval67 (x : Key → ℝ) : Integer.Sparse.eval row67 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck67, Integer.Sparse.eval_collectBalanced, rawRowCheck67]

def rawRow68 : Integer.Sparse Key := [(key1655, -1), (key1659, -1), (key1667, 2), (key1546, 1), (key1559, 1), (key1596, -1), (key1667, -1), (key1546, -2), (key1573, 1), (key1655, 1), (key1813, 1), (key1817, 1), (key1825, -2), (key1316, -1), (key1329, -1), (key1447, 1), (key1825, 1), (key1316, 2), (key1424, -1), (key1813, -1), (key1772, -1), (key1780, -1), (key1798, 1), (key1844, 1), (key1337, 1), (key1345, 1), (key1466, -1), (key1844, -1), (key1296, -1), (key1337, -1), (key1391, 1), (key1772, 1), (key1774, 2), (key1790, -1), (key1839, -1), (key1339, -2), (key1457, 1), (key1839, 1), (key1302, 1), (key1339, 1), (key1397, -1), (key1774, -1)]

theorem rawRowCheck68 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form0 = rawRow68 := by decide +kernel

def row68 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck68 : row68 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow68 := by decide +kernel

theorem rowEval68 (x : Key → ℝ) : Integer.Sparse.eval row68 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck68, Integer.Sparse.eval_collectBalanced, rawRowCheck68]

def rawRow69 : Integer.Sparse Key := [(key1659, -1), (key1655, -1), (key1667, 2), (key1559, 1), (key1546, 1), (key1667, -1), (key1596, -1), (key1546, -2), (key1655, 1), (key1573, 1), (key1817, 1), (key1813, 1), (key1825, -2), (key1329, -1), (key1316, -1), (key1825, 1), (key1447, 1), (key1316, 2), (key1813, -1), (key1424, -1), (key1780, -1), (key1772, -1), (key1844, 1), (key1798, 1), (key1345, 1), (key1337, 1), (key1844, -1), (key1466, -1), (key1337, -1), (key1296, -1), (key1772, 1), (key1391, 1), (key1774, 2), (key1839, -1), (key1790, -1), (key1339, -2), (key1839, 1), (key1457, 1), (key1339, 1), (key1302, 1), (key1774, -1), (key1397, -1)]

theorem rawRowCheck69 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form0 = rawRow69 := by decide +kernel

def row69 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck69 : row69 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow69 := by decide +kernel

theorem rowEval69 (x : Key → ℝ) : Integer.Sparse.eval row69 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck69, Integer.Sparse.eval_collectBalanced, rawRowCheck69]

def rawRow70 : Integer.Sparse Key := [(key1655, -1), (key1667, -1), (key1659, 2), (key1573, 1), (key1596, 1), (key1559, -1), (key1659, -1), (key1573, -2), (key1546, 1), (key1655, 1), (key1813, 1), (key1825, 1), (key1817, -2), (key1424, -1), (key1447, -1), (key1329, 1), (key1817, 1), (key1424, 2), (key1316, -1), (key1813, -1), (key1788, -1), (key1798, -1), (key1780, 1), (key1841, 1), (key1455, 1), (key1466, 1), (key1345, -1), (key1841, -1), (key1391, -1), (key1455, -1), (key1296, 1), (key1788, 1), (key1790, 2), (key1774, -1), (key1839, -1), (key1457, -2), (key1339, 1), (key1839, 1), (key1397, 1), (key1457, 1), (key1302, -1), (key1790, -1)]

theorem rawRowCheck70 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form0 = rawRow70 := by decide +kernel

def row70 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck70 : row70 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow70 := by decide +kernel

theorem rowEval70 (x : Key → ℝ) : Integer.Sparse.eval row70 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck70, Integer.Sparse.eval_collectBalanced, rawRowCheck70]

def rawRow71 : Integer.Sparse Key := [(key1667, -1), (key1655, -1), (key1659, 2), (key1596, 1), (key1573, 1), (key1659, -1), (key1559, -1), (key1573, -2), (key1655, 1), (key1546, 1), (key1825, 1), (key1813, 1), (key1817, -2), (key1447, -1), (key1424, -1), (key1817, 1), (key1329, 1), (key1424, 2), (key1813, -1), (key1316, -1), (key1798, -1), (key1788, -1), (key1841, 1), (key1780, 1), (key1466, 1), (key1455, 1), (key1841, -1), (key1345, -1), (key1455, -1), (key1391, -1), (key1788, 1), (key1296, 1), (key1790, 2), (key1839, -1), (key1774, -1), (key1457, -2), (key1839, 1), (key1339, 1), (key1457, 1), (key1397, 1), (key1790, -1), (key1302, -1)]

theorem rawRowCheck71 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form0 = rawRow71 := by decide +kernel

def row71 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck71 : row71 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow71 := by decide +kernel

theorem rowEval71 (x : Key → ℝ) : Integer.Sparse.eval row71 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck71, Integer.Sparse.eval_collectBalanced, rawRowCheck71]

def rawRow72 : Integer.Sparse Key := [(key1772, -1), (key1774, -1), (key1780, 2), (key1788, 1), (key1790, 1), (key1817, -1), (key1841, -1), (key1798, -2), (key1825, 1), (key1844, 1), (key1337, 1), (key1339, 1), (key1345, -2), (key1455, -1), (key1457, -1), (key1659, 1), (key1841, 1), (key1466, 2), (key1667, -1), (key1844, -1), (key1296, -1), (key1302, -1), (key1329, 1), (key1345, 1), (key1391, 1), (key1397, 1), (key1559, -1), (key1780, -1), (key1447, -1), (key1466, -1), (key1596, 1), (key1798, 1), (key1296, 2), (key1316, -1), (key1337, -1), (key1391, -2), (key1546, 1), (key1772, 1), (key1424, 1), (key1455, 1), (key1573, -1), (key1788, -1)]

theorem rawRowCheck72 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form0 = rawRow72 := by decide +kernel

def row72 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck72 : row72 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow72 := by decide +kernel

theorem rowEval72 (x : Key → ℝ) : Integer.Sparse.eval row72 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck72, Integer.Sparse.eval_collectBalanced, rawRowCheck72]

def rawRow73 : Integer.Sparse Key := [(key1774, -1), (key1772, -1), (key1780, 2), (key1790, 1), (key1788, 1), (key1841, -1), (key1817, -1), (key1798, -2), (key1844, 1), (key1825, 1), (key1339, 1), (key1337, 1), (key1345, -2), (key1457, -1), (key1455, -1), (key1841, 1), (key1659, 1), (key1466, 2), (key1844, -1), (key1667, -1), (key1302, -1), (key1296, -1), (key1345, 1), (key1329, 1), (key1397, 1), (key1391, 1), (key1780, -1), (key1559, -1), (key1466, -1), (key1447, -1), (key1798, 1), (key1596, 1), (key1296, 2), (key1337, -1), (key1316, -1), (key1391, -2), (key1772, 1), (key1546, 1), (key1455, 1), (key1424, 1), (key1788, -1), (key1573, -1)]

theorem rawRowCheck73 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form0 = rawRow73 := by decide +kernel

def row73 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck73 : row73 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow73 := by decide +kernel

theorem rowEval73 (x : Key → ℝ) : Integer.Sparse.eval row73 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck73, Integer.Sparse.eval_collectBalanced, rawRowCheck73]

def rawRow74 : Integer.Sparse Key := [(key1772, -1), (key1780, -1), (key1774, 2), (key1813, 1), (key1817, 1), (key1790, -1), (key1839, -1), (key1825, -2), (key1798, 1), (key1844, 1), (key1337, 1), (key1345, 1), (key1339, -2), (key1655, -1), (key1659, -1), (key1457, 1), (key1839, 1), (key1667, 2), (key1466, -1), (key1844, -1), (key1316, -1), (key1329, -1), (key1302, 1), (key1339, 1), (key1546, 1), (key1559, 1), (key1397, -1), (key1774, -1), (key1596, -1), (key1667, -1), (key1447, 1), (key1825, 1), (key1316, 2), (key1296, -1), (key1337, -1), (key1546, -2), (key1391, 1), (key1772, 1), (key1573, 1), (key1655, 1), (key1424, -1), (key1813, -1)]

theorem rawRowCheck74 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form0 = rawRow74 := by decide +kernel

def row74 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck74 : row74 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow74 := by decide +kernel

theorem rowEval74 (x : Key → ℝ) : Integer.Sparse.eval row74 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck74, Integer.Sparse.eval_collectBalanced, rawRowCheck74]

def rawRow75 : Integer.Sparse Key := [(key1780, -1), (key1772, -1), (key1774, 2), (key1817, 1), (key1813, 1), (key1839, -1), (key1790, -1), (key1825, -2), (key1844, 1), (key1798, 1), (key1345, 1), (key1337, 1), (key1339, -2), (key1659, -1), (key1655, -1), (key1839, 1), (key1457, 1), (key1667, 2), (key1844, -1), (key1466, -1), (key1329, -1), (key1316, -1), (key1339, 1), (key1302, 1), (key1559, 1), (key1546, 1), (key1774, -1), (key1397, -1), (key1667, -1), (key1596, -1), (key1825, 1), (key1447, 1), (key1316, 2), (key1337, -1), (key1296, -1), (key1546, -2), (key1772, 1), (key1391, 1), (key1655, 1), (key1573, 1), (key1813, -1), (key1424, -1)]

theorem rawRowCheck75 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form0 = rawRow75 := by decide +kernel

def row75 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck75 : row75 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow75 := by decide +kernel

theorem rowEval75 (x : Key → ℝ) : Integer.Sparse.eval row75 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck75, Integer.Sparse.eval_collectBalanced, rawRowCheck75]

def rawRow76 : Integer.Sparse Key := [(key1788, -1), (key1790, -1), (key1798, 2), (key1772, 1), (key1774, 1), (key1825, -1), (key1844, -1), (key1780, -2), (key1817, 1), (key1841, 1), (key1455, 1), (key1457, 1), (key1466, -2), (key1337, -1), (key1339, -1), (key1667, 1), (key1844, 1), (key1345, 2), (key1659, -1), (key1841, -1), (key1391, -1), (key1397, -1), (key1447, 1), (key1466, 1), (key1296, 1), (key1302, 1), (key1596, -1), (key1798, -1), (key1329, -1), (key1345, -1), (key1559, 1), (key1780, 1), (key1391, 2), (key1424, -1), (key1455, -1), (key1296, -2), (key1573, 1), (key1788, 1), (key1316, 1), (key1337, 1), (key1546, -1), (key1772, -1)]

theorem rawRowCheck76 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form0 = rawRow76 := by decide +kernel

def row76 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck76 : row76 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow76 := by decide +kernel

theorem rowEval76 (x : Key → ℝ) : Integer.Sparse.eval row76 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck76, Integer.Sparse.eval_collectBalanced, rawRowCheck76]

def rawRow77 : Integer.Sparse Key := [(key1790, -1), (key1788, -1), (key1798, 2), (key1774, 1), (key1772, 1), (key1844, -1), (key1825, -1), (key1780, -2), (key1841, 1), (key1817, 1), (key1457, 1), (key1455, 1), (key1466, -2), (key1339, -1), (key1337, -1), (key1844, 1), (key1667, 1), (key1345, 2), (key1841, -1), (key1659, -1), (key1397, -1), (key1391, -1), (key1466, 1), (key1447, 1), (key1302, 1), (key1296, 1), (key1798, -1), (key1596, -1), (key1345, -1), (key1329, -1), (key1780, 1), (key1559, 1), (key1391, 2), (key1455, -1), (key1424, -1), (key1296, -2), (key1788, 1), (key1573, 1), (key1337, 1), (key1316, 1), (key1772, -1), (key1546, -1)]

theorem rawRowCheck77 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form0 = rawRow77 := by decide +kernel

def row77 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck77 : row77 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow77 := by decide +kernel

theorem rowEval77 (x : Key → ℝ) : Integer.Sparse.eval row77 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck77, Integer.Sparse.eval_collectBalanced, rawRowCheck77]

def rawRow78 : Integer.Sparse Key := [(key1788, -1), (key1798, -1), (key1790, 2), (key1813, 1), (key1825, 1), (key1774, -1), (key1839, -1), (key1817, -2), (key1780, 1), (key1841, 1), (key1455, 1), (key1466, 1), (key1457, -2), (key1655, -1), (key1667, -1), (key1339, 1), (key1839, 1), (key1659, 2), (key1345, -1), (key1841, -1), (key1424, -1), (key1447, -1), (key1397, 1), (key1457, 1), (key1573, 1), (key1596, 1), (key1302, -1), (key1790, -1), (key1559, -1), (key1659, -1), (key1329, 1), (key1817, 1), (key1424, 2), (key1391, -1), (key1455, -1), (key1573, -2), (key1296, 1), (key1788, 1), (key1546, 1), (key1655, 1), (key1316, -1), (key1813, -1)]

theorem rawRowCheck78 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form0 = rawRow78 := by decide +kernel

def row78 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck78 : row78 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow78 := by decide +kernel

theorem rowEval78 (x : Key → ℝ) : Integer.Sparse.eval row78 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck78, Integer.Sparse.eval_collectBalanced, rawRowCheck78]

def rawRow79 : Integer.Sparse Key := [(key1798, -1), (key1788, -1), (key1790, 2), (key1825, 1), (key1813, 1), (key1839, -1), (key1774, -1), (key1817, -2), (key1841, 1), (key1780, 1), (key1466, 1), (key1455, 1), (key1457, -2), (key1667, -1), (key1655, -1), (key1839, 1), (key1339, 1), (key1659, 2), (key1841, -1), (key1345, -1), (key1447, -1), (key1424, -1), (key1457, 1), (key1397, 1), (key1596, 1), (key1573, 1), (key1790, -1), (key1302, -1), (key1659, -1), (key1559, -1), (key1817, 1), (key1329, 1), (key1424, 2), (key1455, -1), (key1391, -1), (key1573, -2), (key1788, 1), (key1296, 1), (key1655, 1), (key1546, 1), (key1813, -1), (key1316, -1)]

theorem rawRowCheck79 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form0 = rawRow79 := by decide +kernel

def row79 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck79 : row79 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow79 := by decide +kernel

theorem rowEval79 (x : Key → ℝ) : Integer.Sparse.eval row79 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck79, Integer.Sparse.eval_collectBalanced, rawRowCheck79]

def rawRow80 : Integer.Sparse Key := [(key1813, -1), (key1817, -1), (key1825, 2), (key1772, 1), (key1780, 1), (key1798, -1), (key1844, -1), (key1774, -2), (key1790, 1), (key1839, 1), (key1655, 1), (key1659, 1), (key1667, -2), (key1337, -1), (key1345, -1), (key1466, 1), (key1844, 1), (key1339, 2), (key1457, -1), (key1839, -1), (key1546, -1), (key1559, -1), (key1596, 1), (key1667, 1), (key1316, 1), (key1329, 1), (key1447, -1), (key1825, -1), (key1302, -1), (key1339, -1), (key1397, 1), (key1774, 1), (key1546, 2), (key1573, -1), (key1655, -1), (key1316, -2), (key1424, 1), (key1813, 1), (key1296, 1), (key1337, 1), (key1391, -1), (key1772, -1)]

theorem rawRowCheck80 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form0 = rawRow80 := by decide +kernel

def row80 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck80 : row80 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow80 := by decide +kernel

theorem rowEval80 (x : Key → ℝ) : Integer.Sparse.eval row80 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck80, Integer.Sparse.eval_collectBalanced, rawRowCheck80]

def rawRow81 : Integer.Sparse Key := [(key1817, -1), (key1813, -1), (key1825, 2), (key1780, 1), (key1772, 1), (key1844, -1), (key1798, -1), (key1774, -2), (key1839, 1), (key1790, 1), (key1659, 1), (key1655, 1), (key1667, -2), (key1345, -1), (key1337, -1), (key1844, 1), (key1466, 1), (key1339, 2), (key1839, -1), (key1457, -1), (key1559, -1), (key1546, -1), (key1667, 1), (key1596, 1), (key1329, 1), (key1316, 1), (key1825, -1), (key1447, -1), (key1339, -1), (key1302, -1), (key1774, 1), (key1397, 1), (key1546, 2), (key1655, -1), (key1573, -1), (key1316, -2), (key1813, 1), (key1424, 1), (key1337, 1), (key1296, 1), (key1772, -1), (key1391, -1)]

theorem rawRowCheck81 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form0 = rawRow81 := by decide +kernel

def row81 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

theorem rowCheck81 : row81 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow81 := by decide +kernel

theorem rowEval81 (x : Key → ℝ) : Integer.Sparse.eval row81 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck81, Integer.Sparse.eval_collectBalanced, rawRowCheck81]

def rawRow82 : Integer.Sparse Key := [(key1813, -1), (key1825, -1), (key1817, 2), (key1788, 1), (key1798, 1), (key1780, -1), (key1841, -1), (key1790, -2), (key1774, 1), (key1839, 1), (key1655, 1), (key1667, 1), (key1659, -2), (key1455, -1), (key1466, -1), (key1345, 1), (key1841, 1), (key1457, 2), (key1339, -1), (key1839, -1), (key1573, -1), (key1596, -1), (key1559, 1), (key1659, 1), (key1424, 1), (key1447, 1), (key1329, -1), (key1817, -1), (key1397, -1), (key1457, -1), (key1302, 1), (key1790, 1), (key1573, 2), (key1546, -1), (key1655, -1), (key1424, -2), (key1316, 1), (key1813, 1), (key1391, 1), (key1455, 1), (key1296, -1), (key1788, -1)]

theorem rawRowCheck82 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form0 = rawRow82 := by decide +kernel

def row82 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck82 : row82 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow82 := by decide +kernel

theorem rowEval82 (x : Key → ℝ) : Integer.Sparse.eval row82 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck82, Integer.Sparse.eval_collectBalanced, rawRowCheck82]

def rawRow83 : Integer.Sparse Key := [(key1825, -1), (key1813, -1), (key1817, 2), (key1798, 1), (key1788, 1), (key1841, -1), (key1780, -1), (key1790, -2), (key1839, 1), (key1774, 1), (key1667, 1), (key1655, 1), (key1659, -2), (key1466, -1), (key1455, -1), (key1841, 1), (key1345, 1), (key1457, 2), (key1839, -1), (key1339, -1), (key1596, -1), (key1573, -1), (key1659, 1), (key1559, 1), (key1447, 1), (key1424, 1), (key1817, -1), (key1329, -1), (key1457, -1), (key1397, -1), (key1790, 1), (key1302, 1), (key1573, 2), (key1655, -1), (key1546, -1), (key1424, -2), (key1813, 1), (key1316, 1), (key1455, 1), (key1391, 1), (key1788, -1), (key1296, -1)]

theorem rawRowCheck83 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form0 = rawRow83 := by decide +kernel

def row83 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

theorem rowCheck83 : row83 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow83 := by decide +kernel

theorem rowEval83 (x : Key → ℝ) : Integer.Sparse.eval row83 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck83, Integer.Sparse.eval_collectBalanced, rawRowCheck83]

def rawRow84 : Integer.Sparse Key := [(key2617, -2), (key2620, 1), (key2620, 1), (key2633, 2), (key2643, -1), (key2643, -1), (key2650, -1), (key2650, -1), (key2655, 1), (key2655, 1), (key2672, 2), (key2675, -1), (key2675, -1), (key2707, -2), (key2730, 1), (key2730, 1), (key2739, 1), (key2739, 1), (key2749, -1), (key2749, -1), (key2787, -2), (key2797, 1), (key2797, 1), (key2810, 2), (key2833, -1), (key2833, -1), (key2899, -1), (key2899, -1), (key2906, 1), (key2906, 1), (key2940, 1), (key2940, 1), (key2945, -1), (key2945, -1), (key2952, -1), (key2952, -1), (key2962, 1), (key2962, 1), (key2978, 1), (key2978, 1), (key2985, -1), (key2985, -1)]

theorem rawRowCheck84 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form1 = rawRow84 := by decide +kernel

def row84 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, -2), (key2787, -2), (key2797, 2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, 2), (key2940, 2), (key2945, -2), (key2952, -2), (key2962, 2), (key2978, 2), (key2985, -2)]

theorem rowCheck84 : row84 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow84 := by decide +kernel

theorem rowEval84 (x : Key → ℝ) : Integer.Sparse.eval row84 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck84, Integer.Sparse.eval_collectBalanced, rawRowCheck84]

def rawRow85 : Integer.Sparse Key := [(key2620, -2), (key2617, 1), (key2620, 1), (key2643, 2), (key2633, -1), (key2643, -1), (key2655, -1), (key2656, -1), (key2650, 1), (key2656, 1), (key2675, 2), (key2672, -1), (key2675, -1), (key2730, -2), (key2707, 1), (key2730, 1), (key2749, 1), (key2751, 1), (key2739, -1), (key2751, -1), (key2797, -2), (key2787, 1), (key2797, 1), (key2833, 2), (key2810, -1), (key2833, -1), (key2906, -1), (key2915, -1), (key2899, 1), (key2915, 1), (key2945, 1), (key2946, 1), (key2940, -1), (key2946, -1), (key2962, -1), (key2964, -1), (key2952, 1), (key2964, 1), (key2985, 1), (key2994, 1), (key2978, -1), (key2994, -1)]

theorem rawRowCheck85 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form1 = rawRow85 := by decide +kernel

def row85 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, 1), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck85 : row85 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow85 := by decide +kernel

theorem rowEval85 (x : Key → ℝ) : Integer.Sparse.eval row85 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck85, Integer.Sparse.eval_collectBalanced, rawRowCheck85]

def rawRow86 : Integer.Sparse Key := [(key2620, -2), (key2620, 1), (key2617, 1), (key2643, 2), (key2643, -1), (key2633, -1), (key2656, -1), (key2655, -1), (key2656, 1), (key2650, 1), (key2675, 2), (key2675, -1), (key2672, -1), (key2730, -2), (key2730, 1), (key2707, 1), (key2751, 1), (key2749, 1), (key2751, -1), (key2739, -1), (key2797, -2), (key2797, 1), (key2787, 1), (key2833, 2), (key2833, -1), (key2810, -1), (key2915, -1), (key2906, -1), (key2915, 1), (key2899, 1), (key2946, 1), (key2945, 1), (key2946, -1), (key2940, -1), (key2964, -1), (key2962, -1), (key2964, 1), (key2952, 1), (key2994, 1), (key2985, 1), (key2994, -1), (key2978, -1)]

theorem rawRowCheck86 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form1 = rawRow86 := by decide +kernel

def row86 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, 1), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck86 : row86 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow86 := by decide +kernel

theorem rowEval86 (x : Key → ℝ) : Integer.Sparse.eval row86 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck86, Integer.Sparse.eval_collectBalanced, rawRowCheck86]

def rawRow87 : Integer.Sparse Key := [(key2633, -2), (key2643, 1), (key2643, 1), (key2617, 2), (key2655, -1), (key2655, -1), (key2620, -1), (key2620, -1), (key2643, 1), (key2643, 1), (key2707, 2), (key2739, -1), (key2739, -1), (key2672, -2), (key2749, 1), (key2749, 1), (key2675, 1), (key2675, 1), (key2730, -1), (key2730, -1), (key2810, -2), (key2899, 1), (key2899, 1), (key2787, 2), (key2906, -1), (key2906, -1), (key2797, -1), (key2797, -1), (key2833, 1), (key2833, 1), (key2952, 1), (key2952, 1), (key2978, -1), (key2978, -1), (key2940, -1), (key2940, -1), (key2985, 1), (key2985, 1), (key2945, 1), (key2945, 1), (key2962, -1), (key2962, -1)]

theorem rawRowCheck87 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form1 = rawRow87 := by decide +kernel

def row87 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, -2), (key2675, 2), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, 2), (key2787, 2), (key2797, -2), (key2810, -2), (key2833, 2), (key2899, 2), (key2906, -2), (key2940, -2), (key2945, 2), (key2952, 2), (key2962, -2), (key2978, -2), (key2985, 2)]

theorem rowCheck87 : row87 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow87 := by decide +kernel

theorem rowEval87 (x : Key → ℝ) : Integer.Sparse.eval row87 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck87, Integer.Sparse.eval_collectBalanced, rawRowCheck87]

def rawRow88 : Integer.Sparse Key := [(key2643, -2), (key2633, 1), (key2643, 1), (key2655, 2), (key2617, -1), (key2655, -1), (key2643, -1), (key2656, -1), (key2620, 1), (key2656, 1), (key2739, 2), (key2707, -1), (key2739, -1), (key2749, -2), (key2672, 1), (key2749, 1), (key2730, 1), (key2751, 1), (key2675, -1), (key2751, -1), (key2899, -2), (key2810, 1), (key2899, 1), (key2906, 2), (key2787, -1), (key2906, -1), (key2833, -1), (key2915, -1), (key2797, 1), (key2915, 1), (key2978, 1), (key2999, 1), (key2952, -1), (key2999, -1), (key2985, -1), (key3001, -1), (key2940, 1), (key3001, 1), (key2962, 1), (key3004, 1), (key2945, -1), (key3004, -1)]

theorem rawRowCheck88 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form1 = rawRow88 := by decide +kernel

def row88 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck88 : row88 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow88 := by decide +kernel

theorem rowEval88 (x : Key → ℝ) : Integer.Sparse.eval row88 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck88, Integer.Sparse.eval_collectBalanced, rawRowCheck88]

def rawRow89 : Integer.Sparse Key := [(key2643, -2), (key2643, 1), (key2633, 1), (key2655, 2), (key2655, -1), (key2617, -1), (key2656, -1), (key2643, -1), (key2656, 1), (key2620, 1), (key2739, 2), (key2739, -1), (key2707, -1), (key2749, -2), (key2749, 1), (key2672, 1), (key2751, 1), (key2730, 1), (key2751, -1), (key2675, -1), (key2899, -2), (key2899, 1), (key2810, 1), (key2906, 2), (key2906, -1), (key2787, -1), (key2915, -1), (key2833, -1), (key2915, 1), (key2797, 1), (key2999, 1), (key2978, 1), (key2999, -1), (key2952, -1), (key3001, -1), (key2985, -1), (key3001, 1), (key2940, 1), (key3004, 1), (key2962, 1), (key3004, -1), (key2945, -1)]

theorem rawRowCheck89 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form1 = rawRow89 := by decide +kernel

def row89 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck89 : row89 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow89 := by decide +kernel

theorem rowEval89 (x : Key → ℝ) : Integer.Sparse.eval row89 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck89, Integer.Sparse.eval_collectBalanced, rawRowCheck89]

def rawRow90 : Integer.Sparse Key := [(key2650, -2), (key2655, 1), (key2656, 1), (key2620, 2), (key2643, -1), (key2656, -1), (key2617, -1), (key2620, -1), (key2633, 1), (key2643, 1), (key2730, 2), (key2749, -1), (key2751, -1), (key2675, -2), (key2739, 1), (key2751, 1), (key2672, 1), (key2675, 1), (key2707, -1), (key2730, -1), (key2833, -2), (key2906, 1), (key2915, 1), (key2797, 2), (key2899, -1), (key2915, -1), (key2787, -1), (key2797, -1), (key2810, 1), (key2833, 1), (key2962, 1), (key2964, 1), (key2985, -1), (key2994, -1), (key2945, -1), (key2946, -1), (key2978, 1), (key2994, 1), (key2940, 1), (key2946, 1), (key2952, -1), (key2964, -1)]

theorem rawRowCheck90 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form1 = rawRow90 := by decide +kernel

def row90 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck90 : row90 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow90 := by decide +kernel

theorem rowEval90 (x : Key → ℝ) : Integer.Sparse.eval row90 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck90, Integer.Sparse.eval_collectBalanced, rawRowCheck90]

def rawRow91 : Integer.Sparse Key := [(key2650, -2), (key2656, 1), (key2655, 1), (key2620, 2), (key2656, -1), (key2643, -1), (key2620, -1), (key2617, -1), (key2643, 1), (key2633, 1), (key2730, 2), (key2751, -1), (key2749, -1), (key2675, -2), (key2751, 1), (key2739, 1), (key2675, 1), (key2672, 1), (key2730, -1), (key2707, -1), (key2833, -2), (key2915, 1), (key2906, 1), (key2797, 2), (key2915, -1), (key2899, -1), (key2797, -1), (key2787, -1), (key2833, 1), (key2810, 1), (key2964, 1), (key2962, 1), (key2994, -1), (key2985, -1), (key2946, -1), (key2945, -1), (key2994, 1), (key2978, 1), (key2946, 1), (key2940, 1), (key2964, -1), (key2952, -1)]

theorem rawRowCheck91 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form1 = rawRow91 := by decide +kernel

def row91 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck91 : row91 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow91 := by decide +kernel

theorem rowEval91 (x : Key → ℝ) : Integer.Sparse.eval row91 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck91, Integer.Sparse.eval_collectBalanced, rawRowCheck91]

def rawRow92 : Integer.Sparse Key := [(key2655, -2), (key2650, 1), (key2656, 1), (key2643, 2), (key2620, -1), (key2656, -1), (key2633, -1), (key2643, -1), (key2617, 1), (key2655, 1), (key2749, 2), (key2730, -1), (key2751, -1), (key2739, -2), (key2675, 1), (key2751, 1), (key2707, 1), (key2739, 1), (key2672, -1), (key2749, -1), (key2906, -2), (key2833, 1), (key2915, 1), (key2899, 2), (key2797, -1), (key2915, -1), (key2810, -1), (key2899, -1), (key2787, 1), (key2906, 1), (key2985, 1), (key3001, 1), (key2962, -1), (key3004, -1), (key2978, -1), (key2999, -1), (key2945, 1), (key3004, 1), (key2952, 1), (key2999, 1), (key2940, -1), (key3001, -1)]

theorem rawRowCheck92 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form1 = rawRow92 := by decide +kernel

def row92 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, 1), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck92 : row92 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow92 := by decide +kernel

theorem rowEval92 (x : Key → ℝ) : Integer.Sparse.eval row92 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck92, Integer.Sparse.eval_collectBalanced, rawRowCheck92]

def rawRow93 : Integer.Sparse Key := [(key2655, -2), (key2656, 1), (key2650, 1), (key2643, 2), (key2656, -1), (key2620, -1), (key2643, -1), (key2633, -1), (key2655, 1), (key2617, 1), (key2749, 2), (key2751, -1), (key2730, -1), (key2739, -2), (key2751, 1), (key2675, 1), (key2739, 1), (key2707, 1), (key2749, -1), (key2672, -1), (key2906, -2), (key2915, 1), (key2833, 1), (key2899, 2), (key2915, -1), (key2797, -1), (key2899, -1), (key2810, -1), (key2906, 1), (key2787, 1), (key3001, 1), (key2985, 1), (key3004, -1), (key2962, -1), (key2999, -1), (key2978, -1), (key3004, 1), (key2945, 1), (key2999, 1), (key2952, 1), (key3001, -1), (key2940, -1)]

theorem rawRowCheck93 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form1 = rawRow93 := by decide +kernel

def row93 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, 1), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck93 : row93 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow93 := by decide +kernel

theorem rowEval93 (x : Key → ℝ) : Integer.Sparse.eval row93 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck93, Integer.Sparse.eval_collectBalanced, rawRowCheck93]

def rawRow94 : Integer.Sparse Key := [(key2672, -2), (key2675, 1), (key2675, 1), (key2707, 2), (key2739, -1), (key2739, -1), (key2730, -1), (key2730, -1), (key2749, 1), (key2749, 1), (key2617, 2), (key2620, -1), (key2620, -1), (key2810, -2), (key2833, 1), (key2833, 1), (key2952, 1), (key2952, 1), (key2962, -1), (key2962, -1), (key2633, -2), (key2643, 1), (key2643, 1), (key2707, 2), (key2730, -1), (key2730, -1), (key2978, -1), (key2978, -1), (key2985, 1), (key2985, 1), (key2650, 1), (key2650, 1), (key2655, -1), (key2655, -1), (key2739, -1), (key2739, -1), (key2749, 1), (key2749, 1), (key2899, 1), (key2899, 1), (key2906, -1), (key2906, -1)]

theorem rawRowCheck94 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form1 = rawRow94 := by decide +kernel

def row94 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 2), (key2650, 2), (key2655, -2), (key2672, -2), (key2675, 2), (key2707, 4), (key2730, -4), (key2739, -4), (key2749, 4), (key2810, -2), (key2833, 2), (key2899, 2), (key2906, -2), (key2952, 2), (key2962, -2), (key2978, -2), (key2985, 2)]

theorem rowCheck94 : row94 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow94 := by decide +kernel

theorem rowEval94 (x : Key → ℝ) : Integer.Sparse.eval row94 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck94, Integer.Sparse.eval_collectBalanced, rawRowCheck94]

def rawRow95 : Integer.Sparse Key := [(key2675, -2), (key2672, 1), (key2675, 1), (key2739, 2), (key2707, -1), (key2739, -1), (key2749, -1), (key2751, -1), (key2730, 1), (key2751, 1), (key2620, 2), (key2617, -1), (key2620, -1), (key2833, -2), (key2810, 1), (key2833, 1), (key2962, 1), (key2964, 1), (key2952, -1), (key2964, -1), (key2643, -2), (key2633, 1), (key2643, 1), (key2730, 2), (key2707, -1), (key2730, -1), (key2985, -1), (key2994, -1), (key2978, 1), (key2994, 1), (key2655, 1), (key2656, 1), (key2650, -1), (key2656, -1), (key2749, -1), (key2751, -1), (key2739, 1), (key2751, 1), (key2906, 1), (key2915, 1), (key2899, -1), (key2915, -1)]

theorem rawRowCheck95 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form1 = rawRow95 := by decide +kernel

def row95 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, -2), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck95 : row95 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow95 := by decide +kernel

theorem rowEval95 (x : Key → ℝ) : Integer.Sparse.eval row95 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck95, Integer.Sparse.eval_collectBalanced, rawRowCheck95]

def rawRow96 : Integer.Sparse Key := [(key2675, -2), (key2675, 1), (key2672, 1), (key2739, 2), (key2739, -1), (key2707, -1), (key2751, -1), (key2749, -1), (key2751, 1), (key2730, 1), (key2620, 2), (key2620, -1), (key2617, -1), (key2833, -2), (key2833, 1), (key2810, 1), (key2964, 1), (key2962, 1), (key2964, -1), (key2952, -1), (key2643, -2), (key2643, 1), (key2633, 1), (key2730, 2), (key2730, -1), (key2707, -1), (key2994, -1), (key2985, -1), (key2994, 1), (key2978, 1), (key2656, 1), (key2655, 1), (key2656, -1), (key2650, -1), (key2751, -1), (key2749, -1), (key2751, 1), (key2739, 1), (key2915, 1), (key2906, 1), (key2915, -1), (key2899, -1)]

theorem rawRowCheck96 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form1 = rawRow96 := by decide +kernel

def row96 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, -2), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck96 : row96 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow96 := by decide +kernel

theorem rowEval96 (x : Key → ℝ) : Integer.Sparse.eval row96 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck96, Integer.Sparse.eval_collectBalanced, rawRowCheck96]

def rawRow97 : Integer.Sparse Key := [(key2707, -2), (key2730, 1), (key2730, 1), (key2672, 2), (key2749, -1), (key2749, -1), (key2675, -1), (key2675, -1), (key2739, 1), (key2739, 1), (key2810, 2), (key2833, -1), (key2833, -1), (key2617, -2), (key2962, 1), (key2962, 1), (key2620, 1), (key2620, 1), (key2833, -1), (key2833, -1), (key2707, -2), (key2978, 1), (key2978, 1), (key2633, 2), (key2985, -1), (key2985, -1), (key2643, -1), (key2643, -1), (key2730, 1), (key2730, 1), (key2739, 1), (key2739, 1), (key2899, -1), (key2899, -1), (key2650, -1), (key2650, -1), (key2906, 1), (key2906, 1), (key2655, 1), (key2655, 1), (key2749, -1), (key2749, -1)]

theorem rawRowCheck97 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form1 = rawRow97 := by decide +kernel

def row97 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2672, 2), (key2675, -2), (key2707, -4), (key2730, 4), (key2739, 4), (key2749, -4), (key2810, 2), (key2833, -4), (key2899, -2), (key2906, 2), (key2962, 2), (key2978, 2), (key2985, -2)]

theorem rowCheck97 : row97 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow97 := by decide +kernel

theorem rowEval97 (x : Key → ℝ) : Integer.Sparse.eval row97 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck97, Integer.Sparse.eval_collectBalanced, rawRowCheck97]

def rawRow98 : Integer.Sparse Key := [(key2730, -2), (key2707, 1), (key2730, 1), (key2749, 2), (key2672, -1), (key2749, -1), (key2739, -1), (key2751, -1), (key2675, 1), (key2751, 1), (key2833, 2), (key2810, -1), (key2833, -1), (key2962, -2), (key2617, 1), (key2962, 1), (key2833, 1), (key2964, 1), (key2620, -1), (key2964, -1), (key2978, -2), (key2707, 1), (key2978, 1), (key2985, 2), (key2633, -1), (key2985, -1), (key2730, -1), (key2994, -1), (key2643, 1), (key2994, 1), (key2899, 1), (key2999, 1), (key2739, -1), (key2999, -1), (key2906, -1), (key3001, -1), (key2650, 1), (key3001, 1), (key2749, 1), (key3004, 1), (key2655, -1), (key3004, -1)]

theorem rawRowCheck98 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form1 = rawRow98 := by decide +kernel

def row98 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, 2), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck98 : row98 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow98 := by decide +kernel

theorem rowEval98 (x : Key → ℝ) : Integer.Sparse.eval row98 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck98, Integer.Sparse.eval_collectBalanced, rawRowCheck98]

def rawRow99 : Integer.Sparse Key := [(key2730, -2), (key2730, 1), (key2707, 1), (key2749, 2), (key2749, -1), (key2672, -1), (key2751, -1), (key2739, -1), (key2751, 1), (key2675, 1), (key2833, 2), (key2833, -1), (key2810, -1), (key2962, -2), (key2962, 1), (key2617, 1), (key2964, 1), (key2833, 1), (key2964, -1), (key2620, -1), (key2978, -2), (key2978, 1), (key2707, 1), (key2985, 2), (key2985, -1), (key2633, -1), (key2994, -1), (key2730, -1), (key2994, 1), (key2643, 1), (key2999, 1), (key2899, 1), (key2999, -1), (key2739, -1), (key3001, -1), (key2906, -1), (key3001, 1), (key2650, 1), (key3004, 1), (key2749, 1), (key3004, -1), (key2655, -1)]

theorem rawRowCheck99 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form1 = rawRow99 := by decide +kernel

def row99 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, 2), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck99 : row99 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow99 := by decide +kernel

theorem rowEval99 (x : Key → ℝ) : Integer.Sparse.eval row99 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck99, Integer.Sparse.eval_collectBalanced, rawRowCheck99]

def rawRow100 : Integer.Sparse Key := [(key2739, -2), (key2749, 1), (key2751, 1), (key2675, 2), (key2730, -1), (key2751, -1), (key2672, -1), (key2675, -1), (key2707, 1), (key2739, 1), (key2952, 2), (key2962, -1), (key2964, -1), (key2620, -2), (key2833, 1), (key2964, 1), (key2617, 1), (key2620, 1), (key2810, -1), (key2833, -1), (key2730, -2), (key2985, 1), (key2994, 1), (key2643, 2), (key2978, -1), (key2994, -1), (key2633, -1), (key2643, -1), (key2707, 1), (key2730, 1), (key2749, 1), (key2751, 1), (key2906, -1), (key2915, -1), (key2655, -1), (key2656, -1), (key2899, 1), (key2915, 1), (key2650, 1), (key2656, 1), (key2739, -1), (key2751, -1)]

theorem rawRowCheck100 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form1 = rawRow100 := by decide +kernel

def row100 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, 2), (key2810, -1), (key2899, 1), (key2906, -1), (key2952, 2), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck100 : row100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow100 := by decide +kernel

theorem rowEval100 (x : Key → ℝ) : Integer.Sparse.eval row100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck100, Integer.Sparse.eval_collectBalanced, rawRowCheck100]

def rawRow101 : Integer.Sparse Key := [(key2739, -2), (key2751, 1), (key2749, 1), (key2675, 2), (key2751, -1), (key2730, -1), (key2675, -1), (key2672, -1), (key2739, 1), (key2707, 1), (key2952, 2), (key2964, -1), (key2962, -1), (key2620, -2), (key2964, 1), (key2833, 1), (key2620, 1), (key2617, 1), (key2833, -1), (key2810, -1), (key2730, -2), (key2994, 1), (key2985, 1), (key2643, 2), (key2994, -1), (key2978, -1), (key2643, -1), (key2633, -1), (key2730, 1), (key2707, 1), (key2751, 1), (key2749, 1), (key2915, -1), (key2906, -1), (key2656, -1), (key2655, -1), (key2915, 1), (key2899, 1), (key2656, 1), (key2650, 1), (key2751, -1), (key2739, -1)]

theorem rawRowCheck101 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form1 = rawRow101 := by decide +kernel

def row101 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, 2), (key2810, -1), (key2899, 1), (key2906, -1), (key2952, 2), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck101 : row101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow101 := by decide +kernel

theorem rowEval101 (x : Key → ℝ) : Integer.Sparse.eval row101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck101, Integer.Sparse.eval_collectBalanced, rawRowCheck101]

def rawRow102 : Integer.Sparse Key := [(key2749, -2), (key2739, 1), (key2751, 1), (key2730, 2), (key2675, -1), (key2751, -1), (key2707, -1), (key2730, -1), (key2672, 1), (key2749, 1), (key2962, 2), (key2952, -1), (key2964, -1), (key2833, -2), (key2620, 1), (key2964, 1), (key2810, 1), (key2833, 1), (key2617, -1), (key2962, -1), (key2985, -2), (key2730, 1), (key2994, 1), (key2978, 2), (key2643, -1), (key2994, -1), (key2707, -1), (key2978, -1), (key2633, 1), (key2985, 1), (key2906, 1), (key3001, 1), (key2749, -1), (key3004, -1), (key2899, -1), (key2999, -1), (key2655, 1), (key3004, 1), (key2739, 1), (key2999, 1), (key2650, -1), (key3001, -1)]

theorem rawRowCheck102 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form1 = rawRow102 := by decide +kernel

def row102 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, -2), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck102 : row102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow102 := by decide +kernel

theorem rowEval102 (x : Key → ℝ) : Integer.Sparse.eval row102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck102, Integer.Sparse.eval_collectBalanced, rawRowCheck102]

def rawRow103 : Integer.Sparse Key := [(key2749, -2), (key2751, 1), (key2739, 1), (key2730, 2), (key2751, -1), (key2675, -1), (key2730, -1), (key2707, -1), (key2749, 1), (key2672, 1), (key2962, 2), (key2964, -1), (key2952, -1), (key2833, -2), (key2964, 1), (key2620, 1), (key2833, 1), (key2810, 1), (key2962, -1), (key2617, -1), (key2985, -2), (key2994, 1), (key2730, 1), (key2978, 2), (key2994, -1), (key2643, -1), (key2978, -1), (key2707, -1), (key2985, 1), (key2633, 1), (key3001, 1), (key2906, 1), (key3004, -1), (key2749, -1), (key2999, -1), (key2899, -1), (key3004, 1), (key2655, 1), (key2999, 1), (key2739, 1), (key3001, -1), (key2650, -1)]

theorem rawRowCheck103 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form1 = rawRow103 := by decide +kernel

def row103 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, -2), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck103 : row103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow103 := by decide +kernel

theorem rowEval103 (x : Key → ℝ) : Integer.Sparse.eval row103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck103, Integer.Sparse.eval_collectBalanced, rawRowCheck103]

def rawRow104 : Integer.Sparse Key := [(key2787, -2), (key2797, 1), (key2797, 1), (key2810, 2), (key2899, -1), (key2899, -1), (key2833, -1), (key2833, -1), (key2906, 1), (key2906, 1), (key2633, 2), (key2643, -1), (key2643, -1), (key2707, -2), (key2978, 1), (key2978, 1), (key2730, 1), (key2730, 1), (key2985, -1), (key2985, -1), (key2617, -2), (key2655, 1), (key2655, 1), (key2672, 2), (key2749, -1), (key2749, -1), (key2945, -1), (key2945, -1), (key2962, 1), (key2962, 1), (key2620, 1), (key2620, 1), (key2643, -1), (key2643, -1), (key2675, -1), (key2675, -1), (key2730, 1), (key2730, 1), (key2797, 1), (key2797, 1), (key2833, -1), (key2833, -1)]

theorem rawRowCheck104 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form1 = rawRow104 := by decide +kernel

def row104 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -4), (key2655, 2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 4), (key2749, -2), (key2787, -2), (key2797, 4), (key2810, 2), (key2833, -4), (key2899, -2), (key2906, 2), (key2945, -2), (key2962, 2), (key2978, 2), (key2985, -2)]

theorem rowCheck104 : row104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow104 := by decide +kernel

theorem rowEval104 (x : Key → ℝ) : Integer.Sparse.eval row104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck104, Integer.Sparse.eval_collectBalanced, rawRowCheck104]

def rawRow105 : Integer.Sparse Key := [(key2797, -2), (key2787, 1), (key2797, 1), (key2899, 2), (key2810, -1), (key2899, -1), (key2906, -1), (key2915, -1), (key2833, 1), (key2915, 1), (key2643, 2), (key2633, -1), (key2643, -1), (key2978, -2), (key2707, 1), (key2978, 1), (key2985, 1), (key2994, 1), (key2730, -1), (key2994, -1), (key2655, -2), (key2617, 1), (key2655, 1), (key2749, 2), (key2672, -1), (key2749, -1), (key2962, -1), (key3004, -1), (key2945, 1), (key3004, 1), (key2643, 1), (key2656, 1), (key2620, -1), (key2656, -1), (key2730, -1), (key2751, -1), (key2675, 1), (key2751, 1), (key2833, 1), (key2915, 1), (key2797, -1), (key2915, -1)]

theorem rawRowCheck105 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form1 = rawRow105 := by decide +kernel

def row105 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 2), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -2), (key2749, 1), (key2787, 1), (key2797, -2), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2945, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck105 : row105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow105 := by decide +kernel

theorem rowEval105 (x : Key → ℝ) : Integer.Sparse.eval row105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck105, Integer.Sparse.eval_collectBalanced, rawRowCheck105]

def rawRow106 : Integer.Sparse Key := [(key2797, -2), (key2797, 1), (key2787, 1), (key2899, 2), (key2899, -1), (key2810, -1), (key2915, -1), (key2906, -1), (key2915, 1), (key2833, 1), (key2643, 2), (key2643, -1), (key2633, -1), (key2978, -2), (key2978, 1), (key2707, 1), (key2994, 1), (key2985, 1), (key2994, -1), (key2730, -1), (key2655, -2), (key2655, 1), (key2617, 1), (key2749, 2), (key2749, -1), (key2672, -1), (key3004, -1), (key2962, -1), (key3004, 1), (key2945, 1), (key2656, 1), (key2643, 1), (key2656, -1), (key2620, -1), (key2751, -1), (key2730, -1), (key2751, 1), (key2675, 1), (key2915, 1), (key2833, 1), (key2915, -1), (key2797, -1)]

theorem rawRowCheck106 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form1 = rawRow106 := by decide +kernel

def row106 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 2), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -2), (key2749, 1), (key2787, 1), (key2797, -2), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2945, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck106 : row106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow106 := by decide +kernel

theorem rowEval106 (x : Key → ℝ) : Integer.Sparse.eval row106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck106, Integer.Sparse.eval_collectBalanced, rawRowCheck106]

def rawRow107 : Integer.Sparse Key := [(key2810, -2), (key2833, 1), (key2833, 1), (key2787, 2), (key2906, -1), (key2906, -1), (key2797, -1), (key2797, -1), (key2899, 1), (key2899, 1), (key2707, 2), (key2730, -1), (key2730, -1), (key2633, -2), (key2985, 1), (key2985, 1), (key2643, 1), (key2643, 1), (key2978, -1), (key2978, -1), (key2672, -2), (key2749, 1), (key2749, 1), (key2617, 2), (key2962, -1), (key2962, -1), (key2655, -1), (key2655, -1), (key2749, 1), (key2749, 1), (key2675, 1), (key2675, 1), (key2797, -1), (key2797, -1), (key2620, -1), (key2620, -1), (key2833, 1), (key2833, 1), (key2643, 1), (key2643, 1), (key2730, -1), (key2730, -1)]

theorem rawRowCheck107 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form1 = rawRow107 := by decide +kernel

def row107 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, -2), (key2675, 2), (key2707, 2), (key2730, -4), (key2749, 4), (key2787, 2), (key2797, -4), (key2810, -2), (key2833, 4), (key2899, 2), (key2906, -2), (key2962, -2), (key2978, -2), (key2985, 2)]

theorem rowCheck107 : row107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow107 := by decide +kernel

theorem rowEval107 (x : Key → ℝ) : Integer.Sparse.eval row107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck107, Integer.Sparse.eval_collectBalanced, rawRowCheck107]

def rawRow108 : Integer.Sparse Key := [(key2833, -2), (key2810, 1), (key2833, 1), (key2906, 2), (key2787, -1), (key2906, -1), (key2899, -1), (key2915, -1), (key2797, 1), (key2915, 1), (key2730, 2), (key2707, -1), (key2730, -1), (key2985, -2), (key2633, 1), (key2985, 1), (key2978, 1), (key2994, 1), (key2643, -1), (key2994, -1), (key2749, -2), (key2672, 1), (key2749, 1), (key2962, 2), (key2617, -1), (key2962, -1), (key2749, -1), (key3004, -1), (key2655, 1), (key3004, 1), (key2797, 1), (key2946, 1), (key2675, -1), (key2946, -1), (key2833, -1), (key2964, -1), (key2620, 1), (key2964, 1), (key2730, 1), (key2994, 1), (key2643, -1), (key2994, -1)]

theorem rawRowCheck108 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form1 = rawRow108 := by decide +kernel

def row108 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 2), (key2749, -2), (key2787, -1), (key2797, 2), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck108 : row108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow108 := by decide +kernel

theorem rowEval108 (x : Key → ℝ) : Integer.Sparse.eval row108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck108, Integer.Sparse.eval_collectBalanced, rawRowCheck108]

def rawRow109 : Integer.Sparse Key := [(key2833, -2), (key2833, 1), (key2810, 1), (key2906, 2), (key2906, -1), (key2787, -1), (key2915, -1), (key2899, -1), (key2915, 1), (key2797, 1), (key2730, 2), (key2730, -1), (key2707, -1), (key2985, -2), (key2985, 1), (key2633, 1), (key2994, 1), (key2978, 1), (key2994, -1), (key2643, -1), (key2749, -2), (key2749, 1), (key2672, 1), (key2962, 2), (key2962, -1), (key2617, -1), (key3004, -1), (key2749, -1), (key3004, 1), (key2655, 1), (key2946, 1), (key2797, 1), (key2946, -1), (key2675, -1), (key2964, -1), (key2833, -1), (key2964, 1), (key2620, 1), (key2994, 1), (key2730, 1), (key2994, -1), (key2643, -1)]

theorem rawRowCheck109 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form1 = rawRow109 := by decide +kernel

def row109 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 2), (key2749, -2), (key2787, -1), (key2797, 2), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck109 : row109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow109 := by decide +kernel

theorem rowEval109 (x : Key → ℝ) : Integer.Sparse.eval row109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck109, Integer.Sparse.eval_collectBalanced, rawRowCheck109]

def rawRow110 : Integer.Sparse Key := [(key2899, -2), (key2906, 1), (key2915, 1), (key2797, 2), (key2833, -1), (key2915, -1), (key2787, -1), (key2797, -1), (key2810, 1), (key2899, 1), (key2978, 2), (key2985, -1), (key2994, -1), (key2643, -2), (key2730, 1), (key2994, 1), (key2633, 1), (key2643, 1), (key2707, -1), (key2978, -1), (key2945, -2), (key2962, 1), (key3004, 1), (key2655, 2), (key2749, -1), (key3004, -1), (key2617, -1), (key2655, -1), (key2672, 1), (key2749, 1), (key2730, 1), (key2751, 1), (key2833, -1), (key2915, -1), (key2643, -1), (key2656, -1), (key2797, 1), (key2915, 1), (key2620, 1), (key2656, 1), (key2675, -1), (key2751, -1)]

theorem rawRowCheck110 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form1 = rawRow110 := by decide +kernel

def row110 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 2), (key2787, -1), (key2797, 2), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2945, -2), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck110 : row110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow110 := by decide +kernel

theorem rowEval110 (x : Key → ℝ) : Integer.Sparse.eval row110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck110, Integer.Sparse.eval_collectBalanced, rawRowCheck110]

def rawRow111 : Integer.Sparse Key := [(key2899, -2), (key2915, 1), (key2906, 1), (key2797, 2), (key2915, -1), (key2833, -1), (key2797, -1), (key2787, -1), (key2899, 1), (key2810, 1), (key2978, 2), (key2994, -1), (key2985, -1), (key2643, -2), (key2994, 1), (key2730, 1), (key2643, 1), (key2633, 1), (key2978, -1), (key2707, -1), (key2945, -2), (key3004, 1), (key2962, 1), (key2655, 2), (key3004, -1), (key2749, -1), (key2655, -1), (key2617, -1), (key2749, 1), (key2672, 1), (key2751, 1), (key2730, 1), (key2915, -1), (key2833, -1), (key2656, -1), (key2643, -1), (key2915, 1), (key2797, 1), (key2656, 1), (key2620, 1), (key2751, -1), (key2675, -1)]

theorem rawRowCheck111 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form1 = rawRow111 := by decide +kernel

def row111 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 2), (key2787, -1), (key2797, 2), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2945, -2), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck111 : row111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow111 := by decide +kernel

theorem rowEval111 (x : Key → ℝ) : Integer.Sparse.eval row111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck111, Integer.Sparse.eval_collectBalanced, rawRowCheck111]

def rawRow112 : Integer.Sparse Key := [(key2906, -2), (key2899, 1), (key2915, 1), (key2833, 2), (key2797, -1), (key2915, -1), (key2810, -1), (key2833, -1), (key2787, 1), (key2906, 1), (key2985, 2), (key2978, -1), (key2994, -1), (key2730, -2), (key2643, 1), (key2994, 1), (key2707, 1), (key2730, 1), (key2633, -1), (key2985, -1), (key2962, -2), (key2945, 1), (key3004, 1), (key2749, 2), (key2655, -1), (key3004, -1), (key2672, -1), (key2749, -1), (key2617, 1), (key2962, 1), (key2833, 1), (key2964, 1), (key2730, -1), (key2994, -1), (key2797, -1), (key2946, -1), (key2643, 1), (key2994, 1), (key2675, 1), (key2946, 1), (key2620, -1), (key2964, -1)]

theorem rawRowCheck112 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form1 = rawRow112 := by decide +kernel

def row112 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 2), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -2), (key2749, 1), (key2787, 1), (key2797, -2), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2945, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck112 : row112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow112 := by decide +kernel

theorem rowEval112 (x : Key → ℝ) : Integer.Sparse.eval row112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck112, Integer.Sparse.eval_collectBalanced, rawRowCheck112]

def rawRow113 : Integer.Sparse Key := [(key2906, -2), (key2915, 1), (key2899, 1), (key2833, 2), (key2915, -1), (key2797, -1), (key2833, -1), (key2810, -1), (key2906, 1), (key2787, 1), (key2985, 2), (key2994, -1), (key2978, -1), (key2730, -2), (key2994, 1), (key2643, 1), (key2730, 1), (key2707, 1), (key2985, -1), (key2633, -1), (key2962, -2), (key3004, 1), (key2945, 1), (key2749, 2), (key3004, -1), (key2655, -1), (key2749, -1), (key2672, -1), (key2962, 1), (key2617, 1), (key2964, 1), (key2833, 1), (key2994, -1), (key2730, -1), (key2946, -1), (key2797, -1), (key2994, 1), (key2643, 1), (key2946, 1), (key2675, 1), (key2964, -1), (key2620, -1)]

theorem rawRowCheck113 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form1 = rawRow113 := by decide +kernel

def row113 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 2), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -2), (key2749, 1), (key2787, 1), (key2797, -2), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2945, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck113 : row113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow113 := by decide +kernel

theorem rowEval113 (x : Key → ℝ) : Integer.Sparse.eval row113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck113, Integer.Sparse.eval_collectBalanced, rawRowCheck113]

def rawRow114 : Integer.Sparse Key := [(key2940, -2), (key2945, 1), (key2946, 1), (key2952, 2), (key2978, -1), (key2999, -1), (key2962, -1), (key2964, -1), (key2985, 1), (key3001, 1), (key2650, 2), (key2655, -1), (key2656, -1), (key2739, -2), (key2899, 1), (key2999, 1), (key2749, 1), (key2751, 1), (key2906, -1), (key3001, -1), (key2620, -2), (key2643, 1), (key2656, 1), (key2675, 2), (key2797, -1), (key2946, -1), (key2730, -1), (key2751, -1), (key2833, 1), (key2964, 1), (key2617, 1), (key2620, 1), (key2633, -1), (key2643, -1), (key2672, -1), (key2675, -1), (key2707, 1), (key2730, 1), (key2787, 1), (key2797, 1), (key2810, -1), (key2833, -1)]

theorem rawRowCheck114 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form1 = rawRow114 := by decide +kernel

def row114 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2650, 2), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2739, -2), (key2749, 1), (key2787, 1), (key2810, -1), (key2899, 1), (key2906, -1), (key2940, -2), (key2945, 1), (key2952, 2), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck114 : row114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow114 := by decide +kernel

theorem rowEval114 (x : Key → ℝ) : Integer.Sparse.eval row114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck114, Integer.Sparse.eval_collectBalanced, rawRowCheck114]

def rawRow115 : Integer.Sparse Key := [(key2940, -2), (key2946, 1), (key2945, 1), (key2952, 2), (key2999, -1), (key2978, -1), (key2964, -1), (key2962, -1), (key3001, 1), (key2985, 1), (key2650, 2), (key2656, -1), (key2655, -1), (key2739, -2), (key2999, 1), (key2899, 1), (key2751, 1), (key2749, 1), (key3001, -1), (key2906, -1), (key2620, -2), (key2656, 1), (key2643, 1), (key2675, 2), (key2946, -1), (key2797, -1), (key2751, -1), (key2730, -1), (key2964, 1), (key2833, 1), (key2620, 1), (key2617, 1), (key2643, -1), (key2633, -1), (key2675, -1), (key2672, -1), (key2730, 1), (key2707, 1), (key2797, 1), (key2787, 1), (key2833, -1), (key2810, -1)]

theorem rawRowCheck115 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form1 = rawRow115 := by decide +kernel

def row115 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2650, 2), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2739, -2), (key2749, 1), (key2787, 1), (key2810, -1), (key2899, 1), (key2906, -1), (key2940, -2), (key2945, 1), (key2952, 2), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck115 : row115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow115 := by decide +kernel

theorem rowEval115 (x : Key → ℝ) : Integer.Sparse.eval row115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck115, Integer.Sparse.eval_collectBalanced, rawRowCheck115]

def rawRow116 : Integer.Sparse Key := [(key2945, -2), (key2940, 1), (key2946, 1), (key2978, 2), (key2952, -1), (key2999, -1), (key2985, -1), (key2994, -1), (key2962, 1), (key3004, 1), (key2655, 2), (key2650, -1), (key2656, -1), (key2899, -2), (key2739, 1), (key2999, 1), (key2906, 1), (key2915, 1), (key2749, -1), (key3004, -1), (key2643, -2), (key2620, 1), (key2656, 1), (key2797, 2), (key2675, -1), (key2946, -1), (key2833, -1), (key2915, -1), (key2730, 1), (key2994, 1), (key2633, 1), (key2643, 1), (key2617, -1), (key2655, -1), (key2707, -1), (key2739, -1), (key2672, 1), (key2749, 1), (key2810, 1), (key2899, 1), (key2787, -1), (key2906, -1)]

theorem rawRowCheck116 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form1 = rawRow116 := by decide +kernel

def row116 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2787, -1), (key2797, 2), (key2810, 1), (key2833, -1), (key2899, -1), (key2940, 1), (key2945, -2), (key2952, -1), (key2962, 1), (key2978, 2), (key2985, -1)]

theorem rowCheck116 : row116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow116 := by decide +kernel

theorem rowEval116 (x : Key → ℝ) : Integer.Sparse.eval row116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck116, Integer.Sparse.eval_collectBalanced, rawRowCheck116]

def rawRow117 : Integer.Sparse Key := [(key2945, -2), (key2946, 1), (key2940, 1), (key2978, 2), (key2999, -1), (key2952, -1), (key2994, -1), (key2985, -1), (key3004, 1), (key2962, 1), (key2655, 2), (key2656, -1), (key2650, -1), (key2899, -2), (key2999, 1), (key2739, 1), (key2915, 1), (key2906, 1), (key3004, -1), (key2749, -1), (key2643, -2), (key2656, 1), (key2620, 1), (key2797, 2), (key2946, -1), (key2675, -1), (key2915, -1), (key2833, -1), (key2994, 1), (key2730, 1), (key2643, 1), (key2633, 1), (key2655, -1), (key2617, -1), (key2739, -1), (key2707, -1), (key2749, 1), (key2672, 1), (key2899, 1), (key2810, 1), (key2906, -1), (key2787, -1)]

theorem rawRowCheck117 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form1 = rawRow117 := by decide +kernel

def row117 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2787, -1), (key2797, 2), (key2810, 1), (key2833, -1), (key2899, -1), (key2940, 1), (key2945, -2), (key2952, -1), (key2962, 1), (key2978, 2), (key2985, -1)]

theorem rowCheck117 : row117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow117 := by decide +kernel

theorem rowEval117 (x : Key → ℝ) : Integer.Sparse.eval row117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck117, Integer.Sparse.eval_collectBalanced, rawRowCheck117]

def rawRow118 : Integer.Sparse Key := [(key2952, -2), (key2962, 1), (key2964, 1), (key2940, 2), (key2985, -1), (key3001, -1), (key2945, -1), (key2946, -1), (key2978, 1), (key2999, 1), (key2739, 2), (key2749, -1), (key2751, -1), (key2650, -2), (key2906, 1), (key3001, 1), (key2655, 1), (key2656, 1), (key2899, -1), (key2999, -1), (key2675, -2), (key2730, 1), (key2751, 1), (key2620, 2), (key2833, -1), (key2964, -1), (key2643, -1), (key2656, -1), (key2797, 1), (key2946, 1), (key2672, 1), (key2675, 1), (key2707, -1), (key2739, -1), (key2617, -1), (key2620, -1), (key2810, 1), (key2833, 1), (key2633, 1), (key2643, 1), (key2707, -1), (key2730, -1)]

theorem rawRowCheck118 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form1 = rawRow118 := by decide +kernel

def row118 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -2), (key2739, 1), (key2749, -1), (key2797, 1), (key2810, 1), (key2899, -1), (key2906, 1), (key2940, 2), (key2945, -1), (key2952, -2), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck118 : row118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow118 := by decide +kernel

theorem rowEval118 (x : Key → ℝ) : Integer.Sparse.eval row118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck118, Integer.Sparse.eval_collectBalanced, rawRowCheck118]

def rawRow119 : Integer.Sparse Key := [(key2952, -2), (key2964, 1), (key2962, 1), (key2940, 2), (key3001, -1), (key2985, -1), (key2946, -1), (key2945, -1), (key2999, 1), (key2978, 1), (key2739, 2), (key2751, -1), (key2749, -1), (key2650, -2), (key3001, 1), (key2906, 1), (key2656, 1), (key2655, 1), (key2999, -1), (key2899, -1), (key2675, -2), (key2751, 1), (key2730, 1), (key2620, 2), (key2964, -1), (key2833, -1), (key2656, -1), (key2643, -1), (key2946, 1), (key2797, 1), (key2675, 1), (key2672, 1), (key2739, -1), (key2707, -1), (key2620, -1), (key2617, -1), (key2833, 1), (key2810, 1), (key2643, 1), (key2633, 1), (key2730, -1), (key2707, -1)]

theorem rawRowCheck119 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form1 = rawRow119 := by decide +kernel

def row119 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -2), (key2739, 1), (key2749, -1), (key2797, 1), (key2810, 1), (key2899, -1), (key2906, 1), (key2940, 2), (key2945, -1), (key2952, -2), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck119 : row119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow119 := by decide +kernel

theorem rowEval119 (x : Key → ℝ) : Integer.Sparse.eval row119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck119, Integer.Sparse.eval_collectBalanced, rawRowCheck119]

def rawRow120 : Integer.Sparse Key := [(key2962, -2), (key2952, 1), (key2964, 1), (key2985, 2), (key2940, -1), (key3001, -1), (key2978, -1), (key2994, -1), (key2945, 1), (key3004, 1), (key2749, 2), (key2739, -1), (key2751, -1), (key2906, -2), (key2650, 1), (key3001, 1), (key2899, 1), (key2915, 1), (key2655, -1), (key3004, -1), (key2730, -2), (key2675, 1), (key2751, 1), (key2833, 2), (key2620, -1), (key2964, -1), (key2797, -1), (key2915, -1), (key2643, 1), (key2994, 1), (key2707, 1), (key2730, 1), (key2672, -1), (key2749, -1), (key2810, -1), (key2833, -1), (key2617, 1), (key2962, 1), (key2707, 1), (key2978, 1), (key2633, -1), (key2985, -1)]

theorem rawRowCheck120 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form1 = rawRow120 := by decide +kernel

def row120 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 2), (key2730, -1), (key2739, -1), (key2749, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2940, -1), (key2945, 1), (key2952, 1), (key2962, -1), (key2985, 1)]

theorem rowCheck120 : row120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow120 := by decide +kernel

theorem rowEval120 (x : Key → ℝ) : Integer.Sparse.eval row120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck120, Integer.Sparse.eval_collectBalanced, rawRowCheck120]

def rawRow121 : Integer.Sparse Key := [(key2962, -2), (key2964, 1), (key2952, 1), (key2985, 2), (key3001, -1), (key2940, -1), (key2994, -1), (key2978, -1), (key3004, 1), (key2945, 1), (key2749, 2), (key2751, -1), (key2739, -1), (key2906, -2), (key3001, 1), (key2650, 1), (key2915, 1), (key2899, 1), (key3004, -1), (key2655, -1), (key2730, -2), (key2751, 1), (key2675, 1), (key2833, 2), (key2964, -1), (key2620, -1), (key2915, -1), (key2797, -1), (key2994, 1), (key2643, 1), (key2730, 1), (key2707, 1), (key2749, -1), (key2672, -1), (key2833, -1), (key2810, -1), (key2962, 1), (key2617, 1), (key2978, 1), (key2707, 1), (key2985, -1), (key2633, -1)]

theorem rawRowCheck121 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form1 = rawRow121 := by decide +kernel

def row121 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 2), (key2730, -1), (key2739, -1), (key2749, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2940, -1), (key2945, 1), (key2952, 1), (key2962, -1), (key2985, 1)]

theorem rowCheck121 : row121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow121 := by decide +kernel

theorem rowEval121 (x : Key → ℝ) : Integer.Sparse.eval row121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck121, Integer.Sparse.eval_collectBalanced, rawRowCheck121]

def rawRow122 : Integer.Sparse Key := [(key2978, -2), (key2985, 1), (key2994, 1), (key2945, 2), (key2962, -1), (key3004, -1), (key2940, -1), (key2946, -1), (key2952, 1), (key2999, 1), (key2899, 2), (key2906, -1), (key2915, -1), (key2655, -2), (key2749, 1), (key3004, 1), (key2650, 1), (key2656, 1), (key2739, -1), (key2999, -1), (key2797, -2), (key2833, 1), (key2915, 1), (key2643, 2), (key2730, -1), (key2994, -1), (key2620, -1), (key2656, -1), (key2675, 1), (key2946, 1), (key2787, 1), (key2797, 1), (key2810, -1), (key2899, -1), (key2633, -1), (key2643, -1), (key2707, 1), (key2978, 1), (key2617, 1), (key2655, 1), (key2672, -1), (key2749, -1)]

theorem rawRowCheck122 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form1 = rawRow122 := by decide +kernel

def row122 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 2), (key2952, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck122 : row122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow122 := by decide +kernel

theorem rowEval122 (x : Key → ℝ) : Integer.Sparse.eval row122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck122, Integer.Sparse.eval_collectBalanced, rawRowCheck122]

def rawRow123 : Integer.Sparse Key := [(key2978, -2), (key2994, 1), (key2985, 1), (key2945, 2), (key3004, -1), (key2962, -1), (key2946, -1), (key2940, -1), (key2999, 1), (key2952, 1), (key2899, 2), (key2915, -1), (key2906, -1), (key2655, -2), (key3004, 1), (key2749, 1), (key2656, 1), (key2650, 1), (key2999, -1), (key2739, -1), (key2797, -2), (key2915, 1), (key2833, 1), (key2643, 2), (key2994, -1), (key2730, -1), (key2656, -1), (key2620, -1), (key2946, 1), (key2675, 1), (key2797, 1), (key2787, 1), (key2899, -1), (key2810, -1), (key2643, -1), (key2633, -1), (key2978, 1), (key2707, 1), (key2655, 1), (key2617, 1), (key2749, -1), (key2672, -1)]

theorem rawRowCheck123 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form1 = rawRow123 := by decide +kernel

def row123 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 2), (key2952, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

theorem rowCheck123 : row123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow123 := by decide +kernel

theorem rowEval123 (x : Key → ℝ) : Integer.Sparse.eval row123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck123, Integer.Sparse.eval_collectBalanced, rawRowCheck123]

def rawRow124 : Integer.Sparse Key := [(key2985, -2), (key2978, 1), (key2994, 1), (key2962, 2), (key2945, -1), (key3004, -1), (key2952, -1), (key2964, -1), (key2940, 1), (key3001, 1), (key2906, 2), (key2899, -1), (key2915, -1), (key2749, -2), (key2655, 1), (key3004, 1), (key2739, 1), (key2751, 1), (key2650, -1), (key3001, -1), (key2833, -2), (key2797, 1), (key2915, 1), (key2730, 2), (key2643, -1), (key2994, -1), (key2675, -1), (key2751, -1), (key2620, 1), (key2964, 1), (key2810, 1), (key2833, 1), (key2787, -1), (key2906, -1), (key2707, -1), (key2730, -1), (key2633, 1), (key2985, 1), (key2672, 1), (key2749, 1), (key2617, -1), (key2962, -1)]

theorem rawRowCheck124 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form1 = rawRow124 := by decide +kernel

def row124 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck124 : row124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow124 := by decide +kernel

theorem rowEval124 (x : Key → ℝ) : Integer.Sparse.eval row124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck124, Integer.Sparse.eval_collectBalanced, rawRowCheck124]

def rawRow125 : Integer.Sparse Key := [(key2985, -2), (key2994, 1), (key2978, 1), (key2962, 2), (key3004, -1), (key2945, -1), (key2964, -1), (key2952, -1), (key3001, 1), (key2940, 1), (key2906, 2), (key2915, -1), (key2899, -1), (key2749, -2), (key3004, 1), (key2655, 1), (key2751, 1), (key2739, 1), (key3001, -1), (key2650, -1), (key2833, -2), (key2915, 1), (key2797, 1), (key2730, 2), (key2994, -1), (key2643, -1), (key2751, -1), (key2675, -1), (key2964, 1), (key2620, 1), (key2833, 1), (key2810, 1), (key2906, -1), (key2787, -1), (key2730, -1), (key2707, -1), (key2985, 1), (key2633, 1), (key2749, 1), (key2672, 1), (key2962, -1), (key2617, -1)]

theorem rawRowCheck125 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form1 = rawRow125 := by decide +kernel

def row125 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

theorem rowCheck125 : row125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow125 := by decide +kernel

theorem rowEval125 (x : Key → ℝ) : Integer.Sparse.eval row125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck125, Integer.Sparse.eval_collectBalanced, rawRowCheck125]

def rawRow126 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1298, 2), (key1312, 1), (key1318, 1), (key1318, -1), (key1351, -1), (key1326, -2), (key1326, 1), (key1354, 1), (key1387, 1), (key1393, 1), (key1393, -2), (key1542, -1), (key1548, -1), (key1548, 1), (key1896, 1), (key1556, 2), (key1556, -1), (key1899, -1), (key1420, -1), (key1426, -1), (key1426, 1), (key1472, 1), (key1569, 1), (key1575, 1), (key1575, -1), (key1903, -1), (key1624, -1), (key1683, -1), (key1624, 1), (key1920, 1), (key1444, 2), (key1444, -1), (key1480, -1), (key1593, -2), (key1593, 1), (key1911, 1), (key1633, 1), (key1689, 1), (key1633, -1), (key1926, -1)]

theorem rawRowCheck126 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block0.form0 = rawRow126 := by decide +kernel

def row126 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck126 : row126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow126 := by decide +kernel

theorem rowEval126 (x : Key → ℝ) : Integer.Sparse.eval row126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block0.form0) x := by
  rw [rowCheck126, Integer.Sparse.eval_collectBalanced, rawRowCheck126]

def rawRow127 : Integer.Sparse Key := [(key1298, -1), (key1292, -1), (key1298, 2), (key1318, 1), (key1312, 1), (key1351, -1), (key1318, -1), (key1326, -2), (key1354, 1), (key1326, 1), (key1393, 1), (key1387, 1), (key1393, -2), (key1548, -1), (key1542, -1), (key1896, 1), (key1548, 1), (key1556, 2), (key1899, -1), (key1556, -1), (key1426, -1), (key1420, -1), (key1472, 1), (key1426, 1), (key1575, 1), (key1569, 1), (key1903, -1), (key1575, -1), (key1683, -1), (key1624, -1), (key1920, 1), (key1624, 1), (key1444, 2), (key1480, -1), (key1444, -1), (key1593, -2), (key1911, 1), (key1593, 1), (key1689, 1), (key1633, 1), (key1926, -1), (key1633, -1)]

theorem rawRowCheck127 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block0.form0 = rawRow127 := by decide +kernel

def row127 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck127 : row127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow127 := by decide +kernel

theorem rowEval127 (x : Key → ℝ) : Integer.Sparse.eval row127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck127, Integer.Sparse.eval_collectBalanced, rawRowCheck127]

end MUB6.Certificate.GramRows

end OAI
