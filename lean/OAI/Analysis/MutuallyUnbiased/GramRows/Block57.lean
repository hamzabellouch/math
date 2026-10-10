import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4224 : Integer.Sparse Key := [(key251, -1), (key248, -1), (key593, -1), (key435, -1), (key601, -1), (key450, -1), (key260, 2), (key595, 2), (key442, 2), (key239, 1), (key236, 1), (key418, 1), (key406, 1), (key583, 1), (key578, 1), (key271, -1), (key267, -1), (key340, -1), (key335, -1), (key475, -1), (key469, -1), (key239, -2), (key418, -2), (key409, -2), (key260, 1), (key251, 1), (key328, 1), (key319, 1), (key450, 1), (key442, 1)]

theorem rawRowCheck4224 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form17 = rawRow4224 := by decide +kernel

def row4224 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key418, -1), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

theorem rowCheck4224 : row4224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4224 := by decide +kernel

theorem rowEval4224 (x : Key → ℝ) : Integer.Sparse.eval row4224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4224, Integer.Sparse.eval_collectBalanced, rawRowCheck4224]

def rawRow4225 : Integer.Sparse Key := [(key435, -1), (key450, -1), (key248, -1), (key601, -1), (key251, -1), (key593, -1), (key442, 2), (key260, 2), (key595, 2), (key406, 1), (key418, 1), (key236, 1), (key583, 1), (key239, 1), (key418, 1), (key335, -1), (key469, -1), (key267, -1), (key475, -1), (key271, -1), (key340, -1), (key409, -2), (key239, -2), (key418, -2), (key319, 1), (key442, 1), (key251, 1), (key450, 1), (key260, 1), (key328, 1)]

theorem rawRowCheck4225 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form17 = rawRow4225 := by decide +kernel

def row4225 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

theorem rowCheck4225 : row4225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4225 := by decide +kernel

theorem rowEval4225 (x : Key → ℝ) : Integer.Sparse.eval row4225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4225, Integer.Sparse.eval_collectBalanced, rawRowCheck4225]

def rawRow4226 : Integer.Sparse Key := [(key450, -1), (key435, -1), (key601, -1), (key248, -1), (key593, -1), (key251, -1), (key442, 2), (key595, 2), (key260, 2), (key418, 1), (key406, 1), (key583, 1), (key236, 1), (key418, 1), (key239, 1), (key469, -1), (key335, -1), (key475, -1), (key267, -1), (key340, -1), (key271, -1), (key409, -2), (key418, -2), (key239, -2), (key442, 1), (key319, 1), (key450, 1), (key251, 1), (key328, 1), (key260, 1)]

theorem rawRowCheck4226 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form17 = rawRow4226 := by decide +kernel

def row4226 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

theorem rowCheck4226 : row4226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4226 := by decide +kernel

theorem rowEval4226 (x : Key → ℝ) : Integer.Sparse.eval row4226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4226, Integer.Sparse.eval_collectBalanced, rawRowCheck4226]

def rawRow4227 : Integer.Sparse Key := [(key593, -1), (key601, -1), (key251, -1), (key450, -1), (key248, -1), (key435, -1), (key595, 2), (key260, 2), (key442, 2), (key578, 1), (key583, 1), (key239, 1), (key418, 1), (key236, 1), (key406, 1), (key340, -1), (key475, -1), (key271, -1), (key469, -1), (key267, -1), (key335, -1), (key418, -2), (key239, -2), (key409, -2), (key328, 1), (key450, 1), (key260, 1), (key442, 1), (key251, 1), (key319, 1)]

theorem rawRowCheck4227 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form17 = rawRow4227 := by decide +kernel

def row4227 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key418, -1), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

theorem rowCheck4227 : row4227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4227 := by decide +kernel

theorem rowEval4227 (x : Key → ℝ) : Integer.Sparse.eval row4227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4227, Integer.Sparse.eval_collectBalanced, rawRowCheck4227]

def rawRow4228 : Integer.Sparse Key := [(key601, -1), (key593, -1), (key450, -1), (key251, -1), (key435, -1), (key248, -1), (key595, 2), (key442, 2), (key260, 2), (key583, 1), (key578, 1), (key418, 1), (key239, 1), (key406, 1), (key236, 1), (key475, -1), (key340, -1), (key469, -1), (key271, -1), (key335, -1), (key267, -1), (key418, -2), (key409, -2), (key239, -2), (key450, 1), (key328, 1), (key442, 1), (key260, 1), (key319, 1), (key251, 1)]

theorem rawRowCheck4228 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form17 = rawRow4228 := by decide +kernel

def row4228 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key418, -1), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

theorem rowCheck4228 : row4228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4228 := by decide +kernel

theorem rowEval4228 (x : Key → ℝ) : Integer.Sparse.eval row4228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4228, Integer.Sparse.eval_collectBalanced, rawRowCheck4228]

def rawRow4229 : Integer.Sparse Key := [(key251, -1), (key260, -1), (key319, -1), (key442, -1), (key328, -1), (key450, -1), (key248, 2), (key316, 2), (key435, 2), (key267, 1), (key271, 1), (key335, 1), (key469, 1), (key340, 1), (key475, 1), (key236, -1), (key248, -1), (key302, -1), (key316, -1), (key385, -1), (key406, -1), (key260, -2), (key397, -2), (key442, -2), (key239, 1), (key251, 1), (key305, 1), (key319, 1), (key388, 1), (key409, 1)]

theorem rawRowCheck4229 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form17 = rawRow4229 := by decide +kernel

def row4229 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, 1), (key340, 1), (key385, -1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

theorem rowCheck4229 : row4229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4229 := by decide +kernel

theorem rowEval4229 (x : Key → ℝ) : Integer.Sparse.eval row4229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4229, Integer.Sparse.eval_collectBalanced, rawRowCheck4229]

def rawRow4230 : Integer.Sparse Key := [(key260, -1), (key251, -1), (key442, -1), (key319, -1), (key450, -1), (key328, -1), (key248, 2), (key435, 2), (key316, 2), (key271, 1), (key267, 1), (key469, 1), (key335, 1), (key475, 1), (key340, 1), (key248, -1), (key236, -1), (key316, -1), (key302, -1), (key406, -1), (key385, -1), (key260, -2), (key442, -2), (key397, -2), (key251, 1), (key239, 1), (key319, 1), (key305, 1), (key409, 1), (key388, 1)]

theorem rawRowCheck4230 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form17 = rawRow4230 := by decide +kernel

def row4230 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, 1), (key340, 1), (key385, -1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

theorem rowCheck4230 : row4230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4230 := by decide +kernel

theorem rowEval4230 (x : Key → ℝ) : Integer.Sparse.eval row4230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4230, Integer.Sparse.eval_collectBalanced, rawRowCheck4230]

def rawRow4231 : Integer.Sparse Key := [(key319, -1), (key328, -1), (key251, -1), (key450, -1), (key260, -1), (key442, -1), (key316, 2), (key248, 2), (key435, 2), (key335, 1), (key340, 1), (key267, 1), (key475, 1), (key271, 1), (key469, 1), (key302, -1), (key316, -1), (key236, -1), (key406, -1), (key248, -1), (key316, -1), (key397, -2), (key260, -2), (key442, -2), (key305, 1), (key388, 1), (key239, 1), (key409, 1), (key251, 1), (key319, 1)]

theorem rawRowCheck4231 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form17 = rawRow4231 := by decide +kernel

def row4231 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key328, -1), (key335, 1), (key340, 1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

theorem rowCheck4231 : row4231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4231 := by decide +kernel

theorem rowEval4231 (x : Key → ℝ) : Integer.Sparse.eval row4231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4231, Integer.Sparse.eval_collectBalanced, rawRowCheck4231]

def rawRow4232 : Integer.Sparse Key := [(key328, -1), (key319, -1), (key450, -1), (key251, -1), (key442, -1), (key260, -1), (key316, 2), (key435, 2), (key248, 2), (key340, 1), (key335, 1), (key475, 1), (key267, 1), (key469, 1), (key271, 1), (key316, -1), (key302, -1), (key406, -1), (key236, -1), (key316, -1), (key248, -1), (key397, -2), (key442, -2), (key260, -2), (key388, 1), (key305, 1), (key409, 1), (key239, 1), (key319, 1), (key251, 1)]

theorem rawRowCheck4232 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form17 = rawRow4232 := by decide +kernel

def row4232 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key328, -1), (key335, 1), (key340, 1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

theorem rowCheck4232 : row4232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4232 := by decide +kernel

theorem rowEval4232 (x : Key → ℝ) : Integer.Sparse.eval row4232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4232, Integer.Sparse.eval_collectBalanced, rawRowCheck4232]

def rawRow4233 : Integer.Sparse Key := [(key442, -1), (key450, -1), (key260, -1), (key328, -1), (key251, -1), (key319, -1), (key435, 2), (key248, 2), (key316, 2), (key469, 1), (key475, 1), (key271, 1), (key340, 1), (key267, 1), (key335, 1), (key385, -1), (key406, -1), (key248, -1), (key316, -1), (key236, -1), (key302, -1), (key442, -2), (key260, -2), (key397, -2), (key319, 1), (key409, 1), (key251, 1), (key388, 1), (key239, 1), (key305, 1)]

theorem rawRowCheck4233 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form17 = rawRow4233 := by decide +kernel

def row4233 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, 1), (key340, 1), (key385, -1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

theorem rowCheck4233 : row4233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4233 := by decide +kernel

theorem rowEval4233 (x : Key → ℝ) : Integer.Sparse.eval row4233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4233, Integer.Sparse.eval_collectBalanced, rawRowCheck4233]

def rawRow4234 : Integer.Sparse Key := [(key450, -1), (key442, -1), (key328, -1), (key260, -1), (key319, -1), (key251, -1), (key435, 2), (key316, 2), (key248, 2), (key475, 1), (key469, 1), (key340, 1), (key271, 1), (key335, 1), (key267, 1), (key406, -1), (key385, -1), (key316, -1), (key248, -1), (key302, -1), (key236, -1), (key442, -2), (key397, -2), (key260, -2), (key409, 1), (key319, 1), (key388, 1), (key251, 1), (key305, 1), (key239, 1)]

theorem rawRowCheck4234 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form17 = rawRow4234 := by decide +kernel

def row4234 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, 1), (key340, 1), (key385, -1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

theorem rowCheck4234 : row4234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4234 := by decide +kernel

theorem rowEval4234 (x : Key → ℝ) : Integer.Sparse.eval row4234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4234, Integer.Sparse.eval_collectBalanced, rawRowCheck4234]

def rawRow4235 : Integer.Sparse Key := [(key267, -1), (key267, -1), (key467, -1), (key467, -1), (key475, -1), (key475, -1), (key271, 2), (key469, 2), (key469, 2), (key239, 1), (key239, 1), (key409, 1), (key409, 1), (key418, 1), (key418, 1), (key260, -1), (key260, -1), (key397, -1), (key397, -1), (key442, -1), (key442, -1), (key236, -2), (key406, -2), (key406, -2), (key248, 1), (key248, 1), (key316, 1), (key316, 1), (key435, 1), (key435, 1)]

theorem rawRowCheck4235 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form17 = rawRow4235 := by decide +kernel

def row4235 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key260, -2), (key267, -2), (key271, 2), (key316, 2), (key397, -2), (key406, -4), (key409, 2), (key418, 2), (key435, 2), (key442, -2), (key467, -2), (key469, 4), (key475, -2)]

theorem rowCheck4235 : row4235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4235 := by decide +kernel

theorem rowEval4235 (x : Key → ℝ) : Integer.Sparse.eval row4235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4235, Integer.Sparse.eval_collectBalanced, rawRowCheck4235]

def rawRow4236 : Integer.Sparse Key := [(key467, -1), (key475, -1), (key267, -1), (key475, -1), (key267, -1), (key467, -1), (key469, 2), (key271, 2), (key469, 2), (key409, 1), (key418, 1), (key239, 1), (key418, 1), (key239, 1), (key409, 1), (key397, -1), (key442, -1), (key260, -1), (key442, -1), (key260, -1), (key397, -1), (key406, -2), (key236, -2), (key406, -2), (key316, 1), (key435, 1), (key248, 1), (key435, 1), (key248, 1), (key316, 1)]

theorem rawRowCheck4236 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form17 = rawRow4236 := by decide +kernel

def row4236 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key260, -2), (key267, -2), (key271, 2), (key316, 2), (key397, -2), (key406, -4), (key409, 2), (key418, 2), (key435, 2), (key442, -2), (key467, -2), (key469, 4), (key475, -2)]

theorem rowCheck4236 : row4236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4236 := by decide +kernel

theorem rowEval4236 (x : Key → ℝ) : Integer.Sparse.eval row4236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4236, Integer.Sparse.eval_collectBalanced, rawRowCheck4236]

def rawRow4237 : Integer.Sparse Key := [(key475, -1), (key467, -1), (key475, -1), (key267, -1), (key467, -1), (key267, -1), (key469, 2), (key469, 2), (key271, 2), (key418, 1), (key409, 1), (key418, 1), (key239, 1), (key409, 1), (key239, 1), (key442, -1), (key397, -1), (key442, -1), (key260, -1), (key397, -1), (key260, -1), (key406, -2), (key406, -2), (key236, -2), (key435, 1), (key316, 1), (key435, 1), (key248, 1), (key316, 1), (key248, 1)]

theorem rawRowCheck4237 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form17 = rawRow4237 := by decide +kernel

def row4237 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key260, -2), (key267, -2), (key271, 2), (key316, 2), (key397, -2), (key406, -4), (key409, 2), (key418, 2), (key435, 2), (key442, -2), (key467, -2), (key469, 4), (key475, -2)]

theorem rowCheck4237 : row4237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4237 := by decide +kernel

theorem rowEval4237 (x : Key → ℝ) : Integer.Sparse.eval row4237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4237, Integer.Sparse.eval_collectBalanced, rawRowCheck4237]

def rawRow4238 : Integer.Sparse Key := [(key267, -1), (key271, -1), (key335, -1), (key469, -1), (key340, -1), (key475, -1), (key267, 2), (key335, 2), (key467, 2), (key251, 1), (key260, 1), (key319, 1), (key442, 1), (key328, 1), (key450, 1), (key239, -1), (key251, -1), (key305, -1), (key388, -1), (key319, -1), (key409, -1), (key248, -2), (key316, -2), (key435, -2), (key236, 1), (key248, 1), (key302, 1), (key316, 1), (key385, 1), (key406, 1)]

theorem rawRowCheck4238 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form17 = rawRow4238 := by decide +kernel

def row4238 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, 1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

theorem rowCheck4238 : row4238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4238 := by decide +kernel

theorem rowEval4238 (x : Key → ℝ) : Integer.Sparse.eval row4238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4238, Integer.Sparse.eval_collectBalanced, rawRowCheck4238]

def rawRow4239 : Integer.Sparse Key := [(key271, -1), (key267, -1), (key469, -1), (key335, -1), (key475, -1), (key340, -1), (key267, 2), (key467, 2), (key335, 2), (key260, 1), (key251, 1), (key442, 1), (key319, 1), (key450, 1), (key328, 1), (key251, -1), (key239, -1), (key388, -1), (key305, -1), (key409, -1), (key319, -1), (key248, -2), (key435, -2), (key316, -2), (key248, 1), (key236, 1), (key316, 1), (key302, 1), (key406, 1), (key385, 1)]

theorem rawRowCheck4239 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form17 = rawRow4239 := by decide +kernel

def row4239 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, 1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

theorem rowCheck4239 : row4239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4239 := by decide +kernel

theorem rowEval4239 (x : Key → ℝ) : Integer.Sparse.eval row4239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4239, Integer.Sparse.eval_collectBalanced, rawRowCheck4239]

def rawRow4240 : Integer.Sparse Key := [(key335, -1), (key340, -1), (key267, -1), (key475, -1), (key271, -1), (key469, -1), (key335, 2), (key267, 2), (key467, 2), (key319, 1), (key328, 1), (key251, 1), (key450, 1), (key260, 1), (key442, 1), (key305, -1), (key319, -1), (key239, -1), (key409, -1), (key251, -1), (key388, -1), (key316, -2), (key248, -2), (key435, -2), (key302, 1), (key316, 1), (key236, 1), (key406, 1), (key248, 1), (key316, 1)]

theorem rawRowCheck4240 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form17 = rawRow4240 := by decide +kernel

def row4240 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key328, 1), (key335, 1), (key340, -1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

theorem rowCheck4240 : row4240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4240 := by decide +kernel

theorem rowEval4240 (x : Key → ℝ) : Integer.Sparse.eval row4240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4240, Integer.Sparse.eval_collectBalanced, rawRowCheck4240]

def rawRow4241 : Integer.Sparse Key := [(key340, -1), (key335, -1), (key475, -1), (key267, -1), (key469, -1), (key271, -1), (key335, 2), (key467, 2), (key267, 2), (key328, 1), (key319, 1), (key450, 1), (key251, 1), (key442, 1), (key260, 1), (key319, -1), (key305, -1), (key409, -1), (key239, -1), (key388, -1), (key251, -1), (key316, -2), (key435, -2), (key248, -2), (key316, 1), (key302, 1), (key406, 1), (key236, 1), (key316, 1), (key248, 1)]

theorem rawRowCheck4241 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form17 = rawRow4241 := by decide +kernel

def row4241 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key328, 1), (key335, 1), (key340, -1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

theorem rowCheck4241 : row4241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4241 := by decide +kernel

theorem rowEval4241 (x : Key → ℝ) : Integer.Sparse.eval row4241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4241, Integer.Sparse.eval_collectBalanced, rawRowCheck4241]

def rawRow4242 : Integer.Sparse Key := [(key469, -1), (key475, -1), (key271, -1), (key340, -1), (key267, -1), (key335, -1), (key467, 2), (key267, 2), (key335, 2), (key442, 1), (key450, 1), (key260, 1), (key328, 1), (key251, 1), (key319, 1), (key388, -1), (key409, -1), (key251, -1), (key319, -1), (key239, -1), (key305, -1), (key435, -2), (key248, -2), (key316, -2), (key385, 1), (key406, 1), (key248, 1), (key316, 1), (key236, 1), (key302, 1)]

theorem rawRowCheck4242 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form17 = rawRow4242 := by decide +kernel

def row4242 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, 1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

theorem rowCheck4242 : row4242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4242 := by decide +kernel

theorem rowEval4242 (x : Key → ℝ) : Integer.Sparse.eval row4242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4242, Integer.Sparse.eval_collectBalanced, rawRowCheck4242]

def rawRow4243 : Integer.Sparse Key := [(key475, -1), (key469, -1), (key340, -1), (key271, -1), (key335, -1), (key267, -1), (key467, 2), (key335, 2), (key267, 2), (key450, 1), (key442, 1), (key328, 1), (key260, 1), (key319, 1), (key251, 1), (key409, -1), (key388, -1), (key319, -1), (key251, -1), (key305, -1), (key239, -1), (key435, -2), (key316, -2), (key248, -2), (key406, 1), (key385, 1), (key316, 1), (key248, 1), (key302, 1), (key236, 1)]

theorem rawRowCheck4243 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form17 = rawRow4243 := by decide +kernel

def row4243 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, 1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

theorem rowCheck4243 : row4243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4243 := by decide +kernel

theorem rowEval4243 (x : Key → ℝ) : Integer.Sparse.eval row4243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4243, Integer.Sparse.eval_collectBalanced, rawRowCheck4243]

def rawRow4244 : Integer.Sparse Key := [(key2642, -2), (key2729, -2), (key2883, -2), (key2632, 1), (key2640, 1), (key2706, 1), (key2860, 1), (key2726, 1), (key2870, 1), (key2654, 2), (key2748, 2), (key2913, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2794, -1), (key2726, -1), (key2829, -1), (key2649, -1), (key2654, -1), (key2738, -1), (key2898, -1), (key2748, -1), (key2905, -1), (key2619, 1), (key2642, 1), (key2674, 1), (key2796, 1), (key2729, 1), (key2832, 1)]

theorem rawRowCheck4244 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form0 = rawRow4244 := by decide +kernel

def row4244 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

theorem rowCheck4244 : row4244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4244 := by decide +kernel

theorem rowEval4244 (x : Key → ℝ) : Integer.Sparse.eval row4244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4244, Integer.Sparse.eval_collectBalanced, rawRowCheck4244]

def rawRow4245 : Integer.Sparse Key := [(key2642, -2), (key2883, -2), (key2729, -2), (key2640, 1), (key2632, 1), (key2860, 1), (key2706, 1), (key2870, 1), (key2726, 1), (key2654, 2), (key2913, 2), (key2748, 2), (key2640, -1), (key2616, -1), (key2794, -1), (key2671, -1), (key2829, -1), (key2726, -1), (key2654, -1), (key2649, -1), (key2898, -1), (key2738, -1), (key2905, -1), (key2748, -1), (key2642, 1), (key2619, 1), (key2796, 1), (key2674, 1), (key2832, 1), (key2729, 1)]

theorem rawRowCheck4245 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form0 = rawRow4245 := by decide +kernel

def row4245 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

theorem rowCheck4245 : row4245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4245 := by decide +kernel

theorem rowEval4245 (x : Key → ℝ) : Integer.Sparse.eval row4245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck4245, Integer.Sparse.eval_collectBalanced, rawRowCheck4245]

def rawRow4246 : Integer.Sparse Key := [(key2729, -2), (key2642, -2), (key2883, -2), (key2706, 1), (key2726, 1), (key2632, 1), (key2870, 1), (key2640, 1), (key2860, 1), (key2748, 2), (key2654, 2), (key2913, 2), (key2671, -1), (key2726, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2738, -1), (key2748, -1), (key2649, -1), (key2905, -1), (key2654, -1), (key2898, -1), (key2674, 1), (key2729, 1), (key2619, 1), (key2832, 1), (key2642, 1), (key2796, 1)]

theorem rawRowCheck4246 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form0 = rawRow4246 := by decide +kernel

def row4246 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

theorem rowCheck4246 : row4246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4246 := by decide +kernel

theorem rowEval4246 (x : Key → ℝ) : Integer.Sparse.eval row4246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4246, Integer.Sparse.eval_collectBalanced, rawRowCheck4246]

def rawRow4247 : Integer.Sparse Key := [(key2729, -2), (key2883, -2), (key2642, -2), (key2726, 1), (key2706, 1), (key2870, 1), (key2632, 1), (key2860, 1), (key2640, 1), (key2748, 2), (key2913, 2), (key2654, 2), (key2726, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2794, -1), (key2640, -1), (key2748, -1), (key2738, -1), (key2905, -1), (key2649, -1), (key2898, -1), (key2654, -1), (key2729, 1), (key2674, 1), (key2832, 1), (key2619, 1), (key2796, 1), (key2642, 1)]

theorem rawRowCheck4247 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form0 = rawRow4247 := by decide +kernel

def row4247 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

theorem rowCheck4247 : row4247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4247 := by decide +kernel

theorem rowEval4247 (x : Key → ℝ) : Integer.Sparse.eval row4247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck4247, Integer.Sparse.eval_collectBalanced, rawRowCheck4247]

def rawRow4248 : Integer.Sparse Key := [(key2883, -2), (key2642, -2), (key2729, -2), (key2860, 1), (key2870, 1), (key2640, 1), (key2726, 1), (key2632, 1), (key2706, 1), (key2913, 2), (key2654, 2), (key2748, 2), (key2794, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2616, -1), (key2671, -1), (key2898, -1), (key2905, -1), (key2654, -1), (key2748, -1), (key2649, -1), (key2738, -1), (key2796, 1), (key2832, 1), (key2642, 1), (key2729, 1), (key2619, 1), (key2674, 1)]

theorem rawRowCheck4248 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form0 = rawRow4248 := by decide +kernel

def row4248 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

theorem rowCheck4248 : row4248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4248 := by decide +kernel

theorem rowEval4248 (x : Key → ℝ) : Integer.Sparse.eval row4248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck4248, Integer.Sparse.eval_collectBalanced, rawRowCheck4248]

def rawRow4249 : Integer.Sparse Key := [(key2883, -2), (key2729, -2), (key2642, -2), (key2870, 1), (key2860, 1), (key2726, 1), (key2640, 1), (key2706, 1), (key2632, 1), (key2913, 2), (key2748, 2), (key2654, 2), (key2829, -1), (key2794, -1), (key2726, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2905, -1), (key2898, -1), (key2748, -1), (key2654, -1), (key2738, -1), (key2649, -1), (key2832, 1), (key2796, 1), (key2729, 1), (key2642, 1), (key2674, 1), (key2619, 1)]

theorem rawRowCheck4249 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form0 = rawRow4249 := by decide +kernel

def row4249 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

theorem rowCheck4249 : row4249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4249 := by decide +kernel

theorem rowEval4249 (x : Key → ℝ) : Integer.Sparse.eval row4249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck4249, Integer.Sparse.eval_collectBalanced, rawRowCheck4249]

def rawRow4250 : Integer.Sparse Key := [(key2654, -2), (key2748, -2), (key2913, -2), (key2649, 1), (key2654, 1), (key2738, 1), (key2898, 1), (key2748, 1), (key2905, 1), (key2642, 2), (key2729, 2), (key2883, 2), (key2619, -1), (key2642, -1), (key2674, -1), (key2796, -1), (key2729, -1), (key2832, -1), (key2632, -1), (key2640, -1), (key2706, -1), (key2860, -1), (key2726, -1), (key2870, -1), (key2616, 1), (key2640, 1), (key2671, 1), (key2794, 1), (key2726, 1), (key2829, 1)]

theorem rawRowCheck4250 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form0 = rawRow4250 := by decide +kernel

def row4250 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

theorem rowCheck4250 : row4250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4250 := by decide +kernel

theorem rowEval4250 (x : Key → ℝ) : Integer.Sparse.eval row4250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4250, Integer.Sparse.eval_collectBalanced, rawRowCheck4250]

def rawRow4251 : Integer.Sparse Key := [(key2654, -2), (key2913, -2), (key2748, -2), (key2654, 1), (key2649, 1), (key2898, 1), (key2738, 1), (key2905, 1), (key2748, 1), (key2642, 2), (key2883, 2), (key2729, 2), (key2642, -1), (key2619, -1), (key2796, -1), (key2674, -1), (key2832, -1), (key2729, -1), (key2640, -1), (key2632, -1), (key2860, -1), (key2706, -1), (key2870, -1), (key2726, -1), (key2640, 1), (key2616, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2726, 1)]

theorem rawRowCheck4251 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form0 = rawRow4251 := by decide +kernel

def row4251 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

theorem rowCheck4251 : row4251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4251 := by decide +kernel

theorem rowEval4251 (x : Key → ℝ) : Integer.Sparse.eval row4251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck4251, Integer.Sparse.eval_collectBalanced, rawRowCheck4251]

def rawRow4252 : Integer.Sparse Key := [(key2748, -2), (key2654, -2), (key2913, -2), (key2738, 1), (key2748, 1), (key2649, 1), (key2905, 1), (key2654, 1), (key2898, 1), (key2729, 2), (key2642, 2), (key2883, 2), (key2674, -1), (key2729, -1), (key2619, -1), (key2832, -1), (key2642, -1), (key2796, -1), (key2706, -1), (key2726, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2671, 1), (key2726, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2794, 1)]

theorem rawRowCheck4252 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form0 = rawRow4252 := by decide +kernel

def row4252 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

theorem rowCheck4252 : row4252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4252 := by decide +kernel

theorem rowEval4252 (x : Key → ℝ) : Integer.Sparse.eval row4252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4252, Integer.Sparse.eval_collectBalanced, rawRowCheck4252]

def rawRow4253 : Integer.Sparse Key := [(key2748, -2), (key2913, -2), (key2654, -2), (key2748, 1), (key2738, 1), (key2905, 1), (key2649, 1), (key2898, 1), (key2654, 1), (key2729, 2), (key2883, 2), (key2642, 2), (key2729, -1), (key2674, -1), (key2832, -1), (key2619, -1), (key2796, -1), (key2642, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2860, -1), (key2640, -1), (key2726, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2794, 1), (key2640, 1)]

theorem rawRowCheck4253 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form0 = rawRow4253 := by decide +kernel

def row4253 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

theorem rowCheck4253 : row4253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4253 := by decide +kernel

theorem rowEval4253 (x : Key → ℝ) : Integer.Sparse.eval row4253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck4253, Integer.Sparse.eval_collectBalanced, rawRowCheck4253]

def rawRow4254 : Integer.Sparse Key := [(key2913, -2), (key2654, -2), (key2748, -2), (key2898, 1), (key2905, 1), (key2654, 1), (key2748, 1), (key2649, 1), (key2738, 1), (key2883, 2), (key2642, 2), (key2729, 2), (key2796, -1), (key2832, -1), (key2642, -1), (key2729, -1), (key2619, -1), (key2674, -1), (key2860, -1), (key2870, -1), (key2640, -1), (key2726, -1), (key2632, -1), (key2706, -1), (key2794, 1), (key2829, 1), (key2640, 1), (key2726, 1), (key2616, 1), (key2671, 1)]

theorem rawRowCheck4254 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form0 = rawRow4254 := by decide +kernel

def row4254 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

theorem rowCheck4254 : row4254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4254 := by decide +kernel

theorem rowEval4254 (x : Key → ℝ) : Integer.Sparse.eval row4254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck4254, Integer.Sparse.eval_collectBalanced, rawRowCheck4254]

def rawRow4255 : Integer.Sparse Key := [(key2913, -2), (key2748, -2), (key2654, -2), (key2905, 1), (key2898, 1), (key2748, 1), (key2654, 1), (key2738, 1), (key2649, 1), (key2883, 2), (key2729, 2), (key2642, 2), (key2832, -1), (key2796, -1), (key2729, -1), (key2642, -1), (key2674, -1), (key2619, -1), (key2870, -1), (key2860, -1), (key2726, -1), (key2640, -1), (key2706, -1), (key2632, -1), (key2829, 1), (key2794, 1), (key2726, 1), (key2640, 1), (key2671, 1), (key2616, 1)]

theorem rawRowCheck4255 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form0 = rawRow4255 := by decide +kernel

def row4255 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

theorem rowCheck4255 : row4255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4255 := by decide +kernel

theorem rowEval4255 (x : Key → ℝ) : Integer.Sparse.eval row4255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck4255, Integer.Sparse.eval_collectBalanced, rawRowCheck4255]

def rawRow4256 : Integer.Sparse Key := [(key1652, -6), (key1538, 2), (key1565, 2), (key1614, 2), (key1810, 6), (key1308, -2), (key1416, -2), (key1614, -2), (key1769, -2), (key1785, -2), (key1810, -2), (key1334, 2), (key1452, 2), (key1652, 2)]

theorem rawRowCheck4256 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form1 = rawRow4256 := by decide +kernel

def row4256 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

theorem rowCheck4256 : row4256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4256 := by decide +kernel

theorem rowEval4256 (x : Key → ℝ) : Integer.Sparse.eval row4256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4256, Integer.Sparse.eval_collectBalanced, rawRowCheck4256]

def rawRow4257 : Integer.Sparse Key := [(key1652, -6), (key1538, 2), (key1614, 2), (key1565, 2), (key1810, 6), (key1308, -2), (key1614, -2), (key1416, -2), (key1769, -2), (key1810, -2), (key1785, -2), (key1334, 2), (key1652, 2), (key1452, 2)]

theorem rawRowCheck4257 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form1 = rawRow4257 := by decide +kernel

def row4257 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

theorem rowCheck4257 : row4257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4257 := by decide +kernel

theorem rowEval4257 (x : Key → ℝ) : Integer.Sparse.eval row4257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4257, Integer.Sparse.eval_collectBalanced, rawRowCheck4257]

def rawRow4258 : Integer.Sparse Key := [(key1652, -6), (key1565, 2), (key1538, 2), (key1614, 2), (key1810, 6), (key1416, -2), (key1308, -2), (key1614, -2), (key1785, -2), (key1769, -2), (key1810, -2), (key1452, 2), (key1334, 2), (key1652, 2)]

theorem rawRowCheck4258 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form1 = rawRow4258 := by decide +kernel

def row4258 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

theorem rowCheck4258 : row4258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4258 := by decide +kernel

theorem rowEval4258 (x : Key → ℝ) : Integer.Sparse.eval row4258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4258, Integer.Sparse.eval_collectBalanced, rawRowCheck4258]

def rawRow4259 : Integer.Sparse Key := [(key1652, -6), (key1565, 2), (key1614, 2), (key1538, 2), (key1810, 6), (key1416, -2), (key1614, -2), (key1308, -2), (key1785, -2), (key1810, -2), (key1769, -2), (key1452, 2), (key1652, 2), (key1334, 2)]

theorem rawRowCheck4259 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form1 = rawRow4259 := by decide +kernel

def row4259 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

theorem rowCheck4259 : row4259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4259 := by decide +kernel

theorem rowEval4259 (x : Key → ℝ) : Integer.Sparse.eval row4259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4259, Integer.Sparse.eval_collectBalanced, rawRowCheck4259]

def rawRow4260 : Integer.Sparse Key := [(key1652, -6), (key1614, 2), (key1538, 2), (key1565, 2), (key1810, 6), (key1614, -2), (key1308, -2), (key1416, -2), (key1810, -2), (key1769, -2), (key1785, -2), (key1652, 2), (key1334, 2), (key1452, 2)]

theorem rawRowCheck4260 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form1 = rawRow4260 := by decide +kernel

def row4260 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

theorem rowCheck4260 : row4260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4260 := by decide +kernel

theorem rowEval4260 (x : Key → ℝ) : Integer.Sparse.eval row4260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4260, Integer.Sparse.eval_collectBalanced, rawRowCheck4260]

def rawRow4261 : Integer.Sparse Key := [(key1652, -6), (key1614, 2), (key1565, 2), (key1538, 2), (key1810, 6), (key1614, -2), (key1416, -2), (key1308, -2), (key1810, -2), (key1785, -2), (key1769, -2), (key1652, 2), (key1452, 2), (key1334, 2)]

theorem rawRowCheck4261 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form1 = rawRow4261 := by decide +kernel

def row4261 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

theorem rowCheck4261 : row4261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4261 := by decide +kernel

theorem rowEval4261 (x : Key → ℝ) : Integer.Sparse.eval row4261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4261, Integer.Sparse.eval_collectBalanced, rawRowCheck4261]

def rawRow4262 : Integer.Sparse Key := [(key1810, -6), (key1769, 2), (key1785, 2), (key1810, 2), (key1652, 6), (key1334, -2), (key1452, -2), (key1652, -2), (key1538, -2), (key1565, -2), (key1614, -2), (key1308, 2), (key1416, 2), (key1614, 2)]

theorem rawRowCheck4262 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form1 = rawRow4262 := by decide +kernel

def row4262 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck4262 : row4262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4262 := by decide +kernel

theorem rowEval4262 (x : Key → ℝ) : Integer.Sparse.eval row4262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4262, Integer.Sparse.eval_collectBalanced, rawRowCheck4262]

def rawRow4263 : Integer.Sparse Key := [(key1810, -6), (key1769, 2), (key1810, 2), (key1785, 2), (key1652, 6), (key1334, -2), (key1652, -2), (key1452, -2), (key1538, -2), (key1614, -2), (key1565, -2), (key1308, 2), (key1614, 2), (key1416, 2)]

theorem rawRowCheck4263 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form1 = rawRow4263 := by decide +kernel

def row4263 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck4263 : row4263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4263 := by decide +kernel

theorem rowEval4263 (x : Key → ℝ) : Integer.Sparse.eval row4263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4263, Integer.Sparse.eval_collectBalanced, rawRowCheck4263]

def rawRow4264 : Integer.Sparse Key := [(key1810, -6), (key1785, 2), (key1769, 2), (key1810, 2), (key1652, 6), (key1452, -2), (key1334, -2), (key1652, -2), (key1565, -2), (key1538, -2), (key1614, -2), (key1416, 2), (key1308, 2), (key1614, 2)]

theorem rawRowCheck4264 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form1 = rawRow4264 := by decide +kernel

def row4264 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck4264 : row4264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4264 := by decide +kernel

theorem rowEval4264 (x : Key → ℝ) : Integer.Sparse.eval row4264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4264, Integer.Sparse.eval_collectBalanced, rawRowCheck4264]

def rawRow4265 : Integer.Sparse Key := [(key1810, -6), (key1785, 2), (key1810, 2), (key1769, 2), (key1652, 6), (key1452, -2), (key1652, -2), (key1334, -2), (key1565, -2), (key1614, -2), (key1538, -2), (key1416, 2), (key1614, 2), (key1308, 2)]

theorem rawRowCheck4265 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form1 = rawRow4265 := by decide +kernel

def row4265 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck4265 : row4265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4265 := by decide +kernel

theorem rowEval4265 (x : Key → ℝ) : Integer.Sparse.eval row4265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4265, Integer.Sparse.eval_collectBalanced, rawRowCheck4265]

def rawRow4266 : Integer.Sparse Key := [(key1810, -6), (key1810, 2), (key1769, 2), (key1785, 2), (key1652, 6), (key1652, -2), (key1334, -2), (key1452, -2), (key1614, -2), (key1538, -2), (key1565, -2), (key1614, 2), (key1308, 2), (key1416, 2)]

theorem rawRowCheck4266 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form1 = rawRow4266 := by decide +kernel

def row4266 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck4266 : row4266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4266 := by decide +kernel

theorem rowEval4266 (x : Key → ℝ) : Integer.Sparse.eval row4266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4266, Integer.Sparse.eval_collectBalanced, rawRowCheck4266]

def rawRow4267 : Integer.Sparse Key := [(key1810, -6), (key1810, 2), (key1785, 2), (key1769, 2), (key1652, 6), (key1652, -2), (key1452, -2), (key1334, -2), (key1614, -2), (key1565, -2), (key1538, -2), (key1614, 2), (key1416, 2), (key1308, 2)]

theorem rawRowCheck4267 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form1 = rawRow4267 := by decide +kernel

def row4267 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck4267 : row4267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4267 := by decide +kernel

theorem rowEval4267 (x : Key → ℝ) : Integer.Sparse.eval row4267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4267, Integer.Sparse.eval_collectBalanced, rawRowCheck4267]

def rawRow4268 : Integer.Sparse Key := [(key2894, -2), (key2896, -2), (key2903, -2), (key2783, 1), (key2791, 1), (key2806, 1), (key2857, 1), (key2826, 1), (key2867, 1), (key2973, 2), (key2975, 2), (key2982, 2), (key2629, -1), (key2637, -1), (key2703, -1), (key2857, -1), (key2723, -1), (key2867, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2975, -1), (key2959, -1), (key2982, -1), (key2647, 1), (key2652, 1), (key2736, 1), (key2896, 1), (key2746, 1), (key2903, 1)]

theorem rawRowCheck4268 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form2 = rawRow4268 := by decide +kernel

def row4268 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

theorem rowCheck4268 : row4268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4268 := by decide +kernel

theorem rowEval4268 (x : Key → ℝ) : Integer.Sparse.eval row4268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4268, Integer.Sparse.eval_collectBalanced, rawRowCheck4268]

def rawRow4269 : Integer.Sparse Key := [(key2896, -2), (key2894, -2), (key2903, -2), (key2791, 1), (key2783, 1), (key2857, 1), (key2806, 1), (key2867, 1), (key2826, 1), (key2975, 2), (key2973, 2), (key2982, 2), (key2637, -1), (key2629, -1), (key2857, -1), (key2703, -1), (key2867, -1), (key2723, -1), (key2942, -1), (key2937, -1), (key2975, -1), (key2949, -1), (key2982, -1), (key2959, -1), (key2652, 1), (key2647, 1), (key2896, 1), (key2736, 1), (key2903, 1), (key2746, 1)]

theorem rawRowCheck4269 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form2 = rawRow4269 := by decide +kernel

def row4269 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

theorem rowCheck4269 : row4269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4269 := by decide +kernel

theorem rowEval4269 (x : Key → ℝ) : Integer.Sparse.eval row4269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck4269, Integer.Sparse.eval_collectBalanced, rawRowCheck4269]

def rawRow4270 : Integer.Sparse Key := [(key2894, -2), (key2903, -2), (key2896, -2), (key2806, 1), (key2826, 1), (key2783, 1), (key2867, 1), (key2791, 1), (key2857, 1), (key2973, 2), (key2982, 2), (key2975, 2), (key2703, -1), (key2723, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2949, -1), (key2959, -1), (key2937, -1), (key2982, -1), (key2942, -1), (key2975, -1), (key2736, 1), (key2746, 1), (key2647, 1), (key2903, 1), (key2652, 1), (key2896, 1)]

theorem rawRowCheck4270 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form2 = rawRow4270 := by decide +kernel

def row4270 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

theorem rowCheck4270 : row4270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4270 := by decide +kernel

theorem rowEval4270 (x : Key → ℝ) : Integer.Sparse.eval row4270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4270, Integer.Sparse.eval_collectBalanced, rawRowCheck4270]

def rawRow4271 : Integer.Sparse Key := [(key2903, -2), (key2894, -2), (key2896, -2), (key2826, 1), (key2806, 1), (key2867, 1), (key2783, 1), (key2857, 1), (key2791, 1), (key2982, 2), (key2973, 2), (key2975, 2), (key2723, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2857, -1), (key2637, -1), (key2959, -1), (key2949, -1), (key2982, -1), (key2937, -1), (key2975, -1), (key2942, -1), (key2746, 1), (key2736, 1), (key2903, 1), (key2647, 1), (key2896, 1), (key2652, 1)]

theorem rawRowCheck4271 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form2 = rawRow4271 := by decide +kernel

def row4271 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

theorem rowCheck4271 : row4271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4271 := by decide +kernel

theorem rowEval4271 (x : Key → ℝ) : Integer.Sparse.eval row4271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck4271, Integer.Sparse.eval_collectBalanced, rawRowCheck4271]

def rawRow4272 : Integer.Sparse Key := [(key2896, -2), (key2903, -2), (key2894, -2), (key2857, 1), (key2867, 1), (key2791, 1), (key2826, 1), (key2783, 1), (key2806, 1), (key2975, 2), (key2982, 2), (key2973, 2), (key2857, -1), (key2867, -1), (key2637, -1), (key2723, -1), (key2629, -1), (key2703, -1), (key2975, -1), (key2982, -1), (key2942, -1), (key2959, -1), (key2937, -1), (key2949, -1), (key2896, 1), (key2903, 1), (key2652, 1), (key2746, 1), (key2647, 1), (key2736, 1)]

theorem rawRowCheck4272 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form2 = rawRow4272 := by decide +kernel

def row4272 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

theorem rowCheck4272 : row4272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4272 := by decide +kernel

theorem rowEval4272 (x : Key → ℝ) : Integer.Sparse.eval row4272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck4272, Integer.Sparse.eval_collectBalanced, rawRowCheck4272]

def rawRow4273 : Integer.Sparse Key := [(key2903, -2), (key2896, -2), (key2894, -2), (key2867, 1), (key2857, 1), (key2826, 1), (key2791, 1), (key2806, 1), (key2783, 1), (key2982, 2), (key2975, 2), (key2973, 2), (key2867, -1), (key2857, -1), (key2723, -1), (key2637, -1), (key2703, -1), (key2629, -1), (key2982, -1), (key2975, -1), (key2959, -1), (key2942, -1), (key2949, -1), (key2937, -1), (key2903, 1), (key2896, 1), (key2746, 1), (key2652, 1), (key2736, 1), (key2647, 1)]

theorem rawRowCheck4273 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form2 = rawRow4273 := by decide +kernel

def row4273 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

theorem rowCheck4273 : row4273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4273 := by decide +kernel

theorem rowEval4273 (x : Key → ℝ) : Integer.Sparse.eval row4273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck4273, Integer.Sparse.eval_collectBalanced, rawRowCheck4273]

def rawRow4274 : Integer.Sparse Key := [(key2973, -2), (key2975, -2), (key2982, -2), (key2937, 1), (key2942, 1), (key2949, 1), (key2975, 1), (key2959, 1), (key2982, 1), (key2894, 2), (key2896, 2), (key2903, 2), (key2647, -1), (key2652, -1), (key2736, -1), (key2896, -1), (key2746, -1), (key2903, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2857, -1), (key2826, -1), (key2867, -1), (key2629, 1), (key2637, 1), (key2703, 1), (key2857, 1), (key2723, 1), (key2867, 1)]

theorem rawRowCheck4274 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form2 = rawRow4274 := by decide +kernel

def row4274 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck4274 : row4274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4274 := by decide +kernel

theorem rowEval4274 (x : Key → ℝ) : Integer.Sparse.eval row4274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4274, Integer.Sparse.eval_collectBalanced, rawRowCheck4274]

def rawRow4275 : Integer.Sparse Key := [(key2975, -2), (key2973, -2), (key2982, -2), (key2942, 1), (key2937, 1), (key2975, 1), (key2949, 1), (key2982, 1), (key2959, 1), (key2896, 2), (key2894, 2), (key2903, 2), (key2652, -1), (key2647, -1), (key2896, -1), (key2736, -1), (key2903, -1), (key2746, -1), (key2791, -1), (key2783, -1), (key2857, -1), (key2806, -1), (key2867, -1), (key2826, -1), (key2637, 1), (key2629, 1), (key2857, 1), (key2703, 1), (key2867, 1), (key2723, 1)]

theorem rawRowCheck4275 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form2 = rawRow4275 := by decide +kernel

def row4275 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck4275 : row4275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4275 := by decide +kernel

theorem rowEval4275 (x : Key → ℝ) : Integer.Sparse.eval row4275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck4275, Integer.Sparse.eval_collectBalanced, rawRowCheck4275]

def rawRow4276 : Integer.Sparse Key := [(key2973, -2), (key2982, -2), (key2975, -2), (key2949, 1), (key2959, 1), (key2937, 1), (key2982, 1), (key2942, 1), (key2975, 1), (key2894, 2), (key2903, 2), (key2896, 2), (key2736, -1), (key2746, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2806, -1), (key2826, -1), (key2783, -1), (key2867, -1), (key2791, -1), (key2857, -1), (key2703, 1), (key2723, 1), (key2629, 1), (key2867, 1), (key2637, 1), (key2857, 1)]

theorem rawRowCheck4276 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form2 = rawRow4276 := by decide +kernel

def row4276 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck4276 : row4276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4276 := by decide +kernel

theorem rowEval4276 (x : Key → ℝ) : Integer.Sparse.eval row4276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4276, Integer.Sparse.eval_collectBalanced, rawRowCheck4276]

def rawRow4277 : Integer.Sparse Key := [(key2982, -2), (key2973, -2), (key2975, -2), (key2959, 1), (key2949, 1), (key2982, 1), (key2937, 1), (key2975, 1), (key2942, 1), (key2903, 2), (key2894, 2), (key2896, 2), (key2746, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2896, -1), (key2652, -1), (key2826, -1), (key2806, -1), (key2867, -1), (key2783, -1), (key2857, -1), (key2791, -1), (key2723, 1), (key2703, 1), (key2867, 1), (key2629, 1), (key2857, 1), (key2637, 1)]

theorem rawRowCheck4277 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form2 = rawRow4277 := by decide +kernel

def row4277 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck4277 : row4277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4277 := by decide +kernel

theorem rowEval4277 (x : Key → ℝ) : Integer.Sparse.eval row4277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck4277, Integer.Sparse.eval_collectBalanced, rawRowCheck4277]

def rawRow4278 : Integer.Sparse Key := [(key2975, -2), (key2982, -2), (key2973, -2), (key2975, 1), (key2982, 1), (key2942, 1), (key2959, 1), (key2937, 1), (key2949, 1), (key2896, 2), (key2903, 2), (key2894, 2), (key2896, -1), (key2903, -1), (key2652, -1), (key2746, -1), (key2647, -1), (key2736, -1), (key2857, -1), (key2867, -1), (key2791, -1), (key2826, -1), (key2783, -1), (key2806, -1), (key2857, 1), (key2867, 1), (key2637, 1), (key2723, 1), (key2629, 1), (key2703, 1)]

theorem rawRowCheck4278 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form2 = rawRow4278 := by decide +kernel

def row4278 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck4278 : row4278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4278 := by decide +kernel

theorem rowEval4278 (x : Key → ℝ) : Integer.Sparse.eval row4278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck4278, Integer.Sparse.eval_collectBalanced, rawRowCheck4278]

def rawRow4279 : Integer.Sparse Key := [(key2982, -2), (key2975, -2), (key2973, -2), (key2982, 1), (key2975, 1), (key2959, 1), (key2942, 1), (key2949, 1), (key2937, 1), (key2903, 2), (key2896, 2), (key2894, 2), (key2903, -1), (key2896, -1), (key2746, -1), (key2652, -1), (key2736, -1), (key2647, -1), (key2867, -1), (key2857, -1), (key2826, -1), (key2791, -1), (key2806, -1), (key2783, -1), (key2867, 1), (key2857, 1), (key2723, 1), (key2637, 1), (key2703, 1), (key2629, 1)]

theorem rawRowCheck4279 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form2 = rawRow4279 := by decide +kernel

def row4279 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck4279 : row4279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4279 := by decide +kernel

theorem rowEval4279 (x : Key → ℝ) : Integer.Sparse.eval row4279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck4279, Integer.Sparse.eval_collectBalanced, rawRowCheck4279]

def rawRow4280 : Integer.Sparse Key := [(key1112, -2), (key1121, -2), (key1148, -2), (key1107, 6), (key1191, 2), (key1197, 2), (key1210, 2), (key994, -2), (key1029, -2), (key1107, -2), (key1191, -6), (key999, 2), (key1034, 2), (key1112, 2)]

theorem rawRowCheck4280 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form3 = rawRow4280 := by decide +kernel

def row4280 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

theorem rowCheck4280 : row4280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4280 := by decide +kernel

theorem rowEval4280 (x : Key → ℝ) : Integer.Sparse.eval row4280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4280, Integer.Sparse.eval_collectBalanced, rawRowCheck4280]

def rawRow4281 : Integer.Sparse Key := [(key1121, -2), (key1112, -2), (key1148, -2), (key1107, 6), (key1197, 2), (key1191, 2), (key1210, 2), (key994, -2), (key1107, -2), (key1029, -2), (key1191, -6), (key999, 2), (key1112, 2), (key1034, 2)]

theorem rawRowCheck4281 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form3 = rawRow4281 := by decide +kernel

def row4281 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

theorem rowCheck4281 : row4281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4281 := by decide +kernel

theorem rowEval4281 (x : Key → ℝ) : Integer.Sparse.eval row4281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4281, Integer.Sparse.eval_collectBalanced, rawRowCheck4281]

def rawRow4282 : Integer.Sparse Key := [(key1112, -2), (key1148, -2), (key1121, -2), (key1107, 6), (key1191, 2), (key1210, 2), (key1197, 2), (key1029, -2), (key994, -2), (key1107, -2), (key1191, -6), (key1034, 2), (key999, 2), (key1112, 2)]

theorem rawRowCheck4282 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form3 = rawRow4282 := by decide +kernel

def row4282 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

theorem rowCheck4282 : row4282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4282 := by decide +kernel

theorem rowEval4282 (x : Key → ℝ) : Integer.Sparse.eval row4282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4282, Integer.Sparse.eval_collectBalanced, rawRowCheck4282]

def rawRow4283 : Integer.Sparse Key := [(key1148, -2), (key1112, -2), (key1121, -2), (key1107, 6), (key1210, 2), (key1191, 2), (key1197, 2), (key1029, -2), (key1107, -2), (key994, -2), (key1191, -6), (key1034, 2), (key1112, 2), (key999, 2)]

theorem rawRowCheck4283 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form3 = rawRow4283 := by decide +kernel

def row4283 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

theorem rowCheck4283 : row4283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4283 := by decide +kernel

theorem rowEval4283 (x : Key → ℝ) : Integer.Sparse.eval row4283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4283, Integer.Sparse.eval_collectBalanced, rawRowCheck4283]

def rawRow4284 : Integer.Sparse Key := [(key1121, -2), (key1148, -2), (key1112, -2), (key1107, 6), (key1197, 2), (key1210, 2), (key1191, 2), (key1107, -2), (key994, -2), (key1029, -2), (key1191, -6), (key1112, 2), (key999, 2), (key1034, 2)]

theorem rawRowCheck4284 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form3 = rawRow4284 := by decide +kernel

def row4284 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

theorem rowCheck4284 : row4284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4284 := by decide +kernel

theorem rowEval4284 (x : Key → ℝ) : Integer.Sparse.eval row4284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4284, Integer.Sparse.eval_collectBalanced, rawRowCheck4284]

def rawRow4285 : Integer.Sparse Key := [(key1148, -2), (key1121, -2), (key1112, -2), (key1107, 6), (key1210, 2), (key1197, 2), (key1191, 2), (key1107, -2), (key1029, -2), (key994, -2), (key1191, -6), (key1112, 2), (key1034, 2), (key999, 2)]

theorem rawRowCheck4285 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form3 = rawRow4285 := by decide +kernel

def row4285 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

theorem rowCheck4285 : row4285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4285 := by decide +kernel

theorem rowEval4285 (x : Key → ℝ) : Integer.Sparse.eval row4285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4285, Integer.Sparse.eval_collectBalanced, rawRowCheck4285]

def rawRow4286 : Integer.Sparse Key := [(key1191, -2), (key1197, -2), (key1210, -2), (key1191, 6), (key1112, 2), (key1121, 2), (key1148, 2), (key999, -2), (key1034, -2), (key1112, -2), (key1107, -6), (key994, 2), (key1029, 2), (key1107, 2)]

theorem rawRowCheck4286 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form3 = rawRow4286 := by decide +kernel

def row4286 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck4286 : row4286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4286 := by decide +kernel

theorem rowEval4286 (x : Key → ℝ) : Integer.Sparse.eval row4286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4286, Integer.Sparse.eval_collectBalanced, rawRowCheck4286]

def rawRow4287 : Integer.Sparse Key := [(key1197, -2), (key1191, -2), (key1210, -2), (key1191, 6), (key1121, 2), (key1112, 2), (key1148, 2), (key999, -2), (key1112, -2), (key1034, -2), (key1107, -6), (key994, 2), (key1107, 2), (key1029, 2)]

theorem rawRowCheck4287 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form3 = rawRow4287 := by decide +kernel

def row4287 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck4287 : row4287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4287 := by decide +kernel

theorem rowEval4287 (x : Key → ℝ) : Integer.Sparse.eval row4287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4287, Integer.Sparse.eval_collectBalanced, rawRowCheck4287]

def rawRow4288 : Integer.Sparse Key := [(key1191, -2), (key1210, -2), (key1197, -2), (key1191, 6), (key1112, 2), (key1148, 2), (key1121, 2), (key1034, -2), (key999, -2), (key1112, -2), (key1107, -6), (key1029, 2), (key994, 2), (key1107, 2)]

theorem rawRowCheck4288 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form3 = rawRow4288 := by decide +kernel

def row4288 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck4288 : row4288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4288 := by decide +kernel

theorem rowEval4288 (x : Key → ℝ) : Integer.Sparse.eval row4288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4288, Integer.Sparse.eval_collectBalanced, rawRowCheck4288]

def rawRow4289 : Integer.Sparse Key := [(key1210, -2), (key1191, -2), (key1197, -2), (key1191, 6), (key1148, 2), (key1112, 2), (key1121, 2), (key1034, -2), (key1112, -2), (key999, -2), (key1107, -6), (key1029, 2), (key1107, 2), (key994, 2)]

theorem rawRowCheck4289 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form3 = rawRow4289 := by decide +kernel

def row4289 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck4289 : row4289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4289 := by decide +kernel

theorem rowEval4289 (x : Key → ℝ) : Integer.Sparse.eval row4289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4289, Integer.Sparse.eval_collectBalanced, rawRowCheck4289]

def rawRow4290 : Integer.Sparse Key := [(key1197, -2), (key1210, -2), (key1191, -2), (key1191, 6), (key1121, 2), (key1148, 2), (key1112, 2), (key1112, -2), (key999, -2), (key1034, -2), (key1107, -6), (key1107, 2), (key994, 2), (key1029, 2)]

theorem rawRowCheck4290 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form3 = rawRow4290 := by decide +kernel

def row4290 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck4290 : row4290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4290 := by decide +kernel

theorem rowEval4290 (x : Key → ℝ) : Integer.Sparse.eval row4290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4290, Integer.Sparse.eval_collectBalanced, rawRowCheck4290]

def rawRow4291 : Integer.Sparse Key := [(key1210, -2), (key1197, -2), (key1191, -2), (key1191, 6), (key1148, 2), (key1121, 2), (key1112, 2), (key1112, -2), (key1034, -2), (key999, -2), (key1107, -6), (key1107, 2), (key1029, 2), (key994, 2)]

theorem rawRowCheck4291 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form3 = rawRow4291 := by decide +kernel

def row4291 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

theorem rowCheck4291 : row4291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4291 := by decide +kernel

theorem rowEval4291 (x : Key → ℝ) : Integer.Sparse.eval row4291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4291, Integer.Sparse.eval_collectBalanced, rawRowCheck4291]

def rawRow4292 : Integer.Sparse Key := [(key2854, -6), (key2697, 2), (key2800, 2), (key2850, 2), (key2864, 6), (key2623, -2), (key2777, -2), (key2850, -2), (key2720, -2), (key2823, -2), (key2864, -2), (key2634, 2), (key2788, 2), (key2854, 2)]

theorem rawRowCheck4292 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form4 = rawRow4292 := by decide +kernel

def row4292 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

theorem rowCheck4292 : row4292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4292 := by decide +kernel

theorem rowEval4292 (x : Key → ℝ) : Integer.Sparse.eval row4292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4292, Integer.Sparse.eval_collectBalanced, rawRowCheck4292]

def rawRow4293 : Integer.Sparse Key := [(key2854, -6), (key2697, 2), (key2850, 2), (key2800, 2), (key2864, 6), (key2623, -2), (key2850, -2), (key2777, -2), (key2720, -2), (key2864, -2), (key2823, -2), (key2634, 2), (key2854, 2), (key2788, 2)]

theorem rawRowCheck4293 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form4 = rawRow4293 := by decide +kernel

def row4293 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

theorem rowCheck4293 : row4293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4293 := by decide +kernel

theorem rowEval4293 (x : Key → ℝ) : Integer.Sparse.eval row4293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4293, Integer.Sparse.eval_collectBalanced, rawRowCheck4293]

def rawRow4294 : Integer.Sparse Key := [(key2854, -6), (key2800, 2), (key2697, 2), (key2850, 2), (key2864, 6), (key2777, -2), (key2623, -2), (key2850, -2), (key2823, -2), (key2720, -2), (key2864, -2), (key2788, 2), (key2634, 2), (key2854, 2)]

theorem rawRowCheck4294 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form4 = rawRow4294 := by decide +kernel

def row4294 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

theorem rowCheck4294 : row4294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4294 := by decide +kernel

theorem rowEval4294 (x : Key → ℝ) : Integer.Sparse.eval row4294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4294, Integer.Sparse.eval_collectBalanced, rawRowCheck4294]

def rawRow4295 : Integer.Sparse Key := [(key2854, -6), (key2800, 2), (key2850, 2), (key2697, 2), (key2864, 6), (key2777, -2), (key2850, -2), (key2623, -2), (key2823, -2), (key2864, -2), (key2720, -2), (key2788, 2), (key2854, 2), (key2634, 2)]

theorem rawRowCheck4295 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form4 = rawRow4295 := by decide +kernel

def row4295 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

theorem rowCheck4295 : row4295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4295 := by decide +kernel

theorem rowEval4295 (x : Key → ℝ) : Integer.Sparse.eval row4295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4295, Integer.Sparse.eval_collectBalanced, rawRowCheck4295]

def rawRow4296 : Integer.Sparse Key := [(key2854, -6), (key2850, 2), (key2697, 2), (key2800, 2), (key2864, 6), (key2850, -2), (key2623, -2), (key2777, -2), (key2864, -2), (key2720, -2), (key2823, -2), (key2854, 2), (key2634, 2), (key2788, 2)]

theorem rawRowCheck4296 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form4 = rawRow4296 := by decide +kernel

def row4296 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

theorem rowCheck4296 : row4296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4296 := by decide +kernel

theorem rowEval4296 (x : Key → ℝ) : Integer.Sparse.eval row4296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4296, Integer.Sparse.eval_collectBalanced, rawRowCheck4296]

def rawRow4297 : Integer.Sparse Key := [(key2854, -6), (key2850, 2), (key2800, 2), (key2697, 2), (key2864, 6), (key2850, -2), (key2777, -2), (key2623, -2), (key2864, -2), (key2823, -2), (key2720, -2), (key2854, 2), (key2788, 2), (key2634, 2)]

theorem rawRowCheck4297 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form4 = rawRow4297 := by decide +kernel

def row4297 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

theorem rowCheck4297 : row4297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4297 := by decide +kernel

theorem rowEval4297 (x : Key → ℝ) : Integer.Sparse.eval row4297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4297, Integer.Sparse.eval_collectBalanced, rawRowCheck4297]

def rawRow4298 : Integer.Sparse Key := [(key2864, -6), (key2720, 2), (key2823, 2), (key2864, 2), (key2854, 6), (key2634, -2), (key2788, -2), (key2854, -2), (key2697, -2), (key2800, -2), (key2850, -2), (key2623, 2), (key2777, 2), (key2850, 2)]

theorem rawRowCheck4298 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form4 = rawRow4298 := by decide +kernel

def row4298 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

theorem rowCheck4298 : row4298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4298 := by decide +kernel

theorem rowEval4298 (x : Key → ℝ) : Integer.Sparse.eval row4298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4298, Integer.Sparse.eval_collectBalanced, rawRowCheck4298]

def rawRow4299 : Integer.Sparse Key := [(key2864, -6), (key2720, 2), (key2864, 2), (key2823, 2), (key2854, 6), (key2634, -2), (key2854, -2), (key2788, -2), (key2697, -2), (key2850, -2), (key2800, -2), (key2623, 2), (key2850, 2), (key2777, 2)]

theorem rawRowCheck4299 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form4 = rawRow4299 := by decide +kernel

def row4299 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

theorem rowCheck4299 : row4299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4299 := by decide +kernel

theorem rowEval4299 (x : Key → ℝ) : Integer.Sparse.eval row4299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4299, Integer.Sparse.eval_collectBalanced, rawRowCheck4299]

def rawRow4300 : Integer.Sparse Key := [(key2864, -6), (key2823, 2), (key2720, 2), (key2864, 2), (key2854, 6), (key2788, -2), (key2634, -2), (key2854, -2), (key2800, -2), (key2697, -2), (key2850, -2), (key2777, 2), (key2623, 2), (key2850, 2)]

theorem rawRowCheck4300 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form4 = rawRow4300 := by decide +kernel

def row4300 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

theorem rowCheck4300 : row4300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4300 := by decide +kernel

theorem rowEval4300 (x : Key → ℝ) : Integer.Sparse.eval row4300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4300, Integer.Sparse.eval_collectBalanced, rawRowCheck4300]

def rawRow4301 : Integer.Sparse Key := [(key2864, -6), (key2823, 2), (key2864, 2), (key2720, 2), (key2854, 6), (key2788, -2), (key2854, -2), (key2634, -2), (key2800, -2), (key2850, -2), (key2697, -2), (key2777, 2), (key2850, 2), (key2623, 2)]

theorem rawRowCheck4301 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form4 = rawRow4301 := by decide +kernel

def row4301 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

theorem rowCheck4301 : row4301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4301 := by decide +kernel

theorem rowEval4301 (x : Key → ℝ) : Integer.Sparse.eval row4301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4301, Integer.Sparse.eval_collectBalanced, rawRowCheck4301]

def rawRow4302 : Integer.Sparse Key := [(key2864, -6), (key2864, 2), (key2720, 2), (key2823, 2), (key2854, 6), (key2854, -2), (key2634, -2), (key2788, -2), (key2850, -2), (key2697, -2), (key2800, -2), (key2850, 2), (key2623, 2), (key2777, 2)]

theorem rawRowCheck4302 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form4 = rawRow4302 := by decide +kernel

def row4302 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

theorem rowCheck4302 : row4302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4302 := by decide +kernel

theorem rowEval4302 (x : Key → ℝ) : Integer.Sparse.eval row4302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4302, Integer.Sparse.eval_collectBalanced, rawRowCheck4302]

def rawRow4303 : Integer.Sparse Key := [(key2864, -6), (key2864, 2), (key2823, 2), (key2720, 2), (key2854, 6), (key2854, -2), (key2788, -2), (key2634, -2), (key2850, -2), (key2800, -2), (key2697, -2), (key2850, 2), (key2777, 2), (key2623, 2)]

theorem rawRowCheck4303 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form4 = rawRow4303 := by decide +kernel

def row4303 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

theorem rowCheck4303 : row4303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4303 := by decide +kernel

theorem rowEval4303 (x : Key → ℝ) : Integer.Sparse.eval row4303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4303, Integer.Sparse.eval_collectBalanced, rawRowCheck4303]

def rawRow4304 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1425, -1), (key1623, -1), (key1443, -1), (key1632, -1), (key1312, 2), (key1420, 2), (key1618, 2), (key1338, 1), (key1344, 1), (key1456, 1), (key1658, 1), (key1465, 1), (key1666, 1), (key1292, -1), (key1312, -1), (key1387, -1), (key1542, -1), (key1420, -1), (key1569, -1), (key1338, -2), (key1456, -2), (key1656, -2), (key1297, 1), (key1317, 1), (key1392, 1), (key1547, 1), (key1425, 1), (key1574, 1)]

theorem rawRowCheck4304 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form5 = rawRow4304 := by decide +kernel

def row4304 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

theorem rowCheck4304 : row4304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4304 := by decide +kernel

theorem rowEval4304 (x : Key → ℝ) : Integer.Sparse.eval row4304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4304, Integer.Sparse.eval_collectBalanced, rawRowCheck4304]

def rawRow4305 : Integer.Sparse Key := [(key1325, -1), (key1317, -1), (key1623, -1), (key1425, -1), (key1632, -1), (key1443, -1), (key1312, 2), (key1618, 2), (key1420, 2), (key1344, 1), (key1338, 1), (key1658, 1), (key1456, 1), (key1666, 1), (key1465, 1), (key1312, -1), (key1292, -1), (key1542, -1), (key1387, -1), (key1569, -1), (key1420, -1), (key1338, -2), (key1656, -2), (key1456, -2), (key1317, 1), (key1297, 1), (key1547, 1), (key1392, 1), (key1574, 1), (key1425, 1)]

theorem rawRowCheck4305 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form5 = rawRow4305 := by decide +kernel

def row4305 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

theorem rowCheck4305 : row4305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4305 := by decide +kernel

theorem rowEval4305 (x : Key → ℝ) : Integer.Sparse.eval row4305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4305, Integer.Sparse.eval_collectBalanced, rawRowCheck4305]

def rawRow4306 : Integer.Sparse Key := [(key1425, -1), (key1443, -1), (key1317, -1), (key1632, -1), (key1325, -1), (key1623, -1), (key1420, 2), (key1312, 2), (key1618, 2), (key1456, 1), (key1465, 1), (key1338, 1), (key1666, 1), (key1344, 1), (key1658, 1), (key1387, -1), (key1420, -1), (key1292, -1), (key1569, -1), (key1312, -1), (key1542, -1), (key1456, -2), (key1338, -2), (key1656, -2), (key1392, 1), (key1425, 1), (key1297, 1), (key1574, 1), (key1317, 1), (key1547, 1)]

theorem rawRowCheck4306 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form5 = rawRow4306 := by decide +kernel

def row4306 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

theorem rowCheck4306 : row4306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4306 := by decide +kernel

theorem rowEval4306 (x : Key → ℝ) : Integer.Sparse.eval row4306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4306, Integer.Sparse.eval_collectBalanced, rawRowCheck4306]

def rawRow4307 : Integer.Sparse Key := [(key1443, -1), (key1425, -1), (key1632, -1), (key1317, -1), (key1623, -1), (key1325, -1), (key1420, 2), (key1618, 2), (key1312, 2), (key1465, 1), (key1456, 1), (key1666, 1), (key1338, 1), (key1658, 1), (key1344, 1), (key1420, -1), (key1387, -1), (key1569, -1), (key1292, -1), (key1542, -1), (key1312, -1), (key1456, -2), (key1656, -2), (key1338, -2), (key1425, 1), (key1392, 1), (key1574, 1), (key1297, 1), (key1547, 1), (key1317, 1)]

theorem rawRowCheck4307 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form5 = rawRow4307 := by decide +kernel

def row4307 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

theorem rowCheck4307 : row4307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4307 := by decide +kernel

theorem rowEval4307 (x : Key → ℝ) : Integer.Sparse.eval row4307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck4307, Integer.Sparse.eval_collectBalanced, rawRowCheck4307]

def rawRow4308 : Integer.Sparse Key := [(key1623, -1), (key1632, -1), (key1325, -1), (key1443, -1), (key1317, -1), (key1425, -1), (key1618, 2), (key1312, 2), (key1420, 2), (key1658, 1), (key1666, 1), (key1344, 1), (key1465, 1), (key1338, 1), (key1456, 1), (key1542, -1), (key1569, -1), (key1312, -1), (key1420, -1), (key1292, -1), (key1387, -1), (key1656, -2), (key1338, -2), (key1456, -2), (key1547, 1), (key1574, 1), (key1317, 1), (key1425, 1), (key1297, 1), (key1392, 1)]

theorem rawRowCheck4308 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form5 = rawRow4308 := by decide +kernel

def row4308 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

theorem rowCheck4308 : row4308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4308 := by decide +kernel

theorem rowEval4308 (x : Key → ℝ) : Integer.Sparse.eval row4308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4308, Integer.Sparse.eval_collectBalanced, rawRowCheck4308]

def rawRow4309 : Integer.Sparse Key := [(key1632, -1), (key1623, -1), (key1443, -1), (key1325, -1), (key1425, -1), (key1317, -1), (key1618, 2), (key1420, 2), (key1312, 2), (key1666, 1), (key1658, 1), (key1465, 1), (key1344, 1), (key1456, 1), (key1338, 1), (key1569, -1), (key1542, -1), (key1420, -1), (key1312, -1), (key1387, -1), (key1292, -1), (key1656, -2), (key1456, -2), (key1338, -2), (key1574, 1), (key1547, 1), (key1425, 1), (key1317, 1), (key1392, 1), (key1297, 1)]

theorem rawRowCheck4309 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form5 = rawRow4309 := by decide +kernel

def row4309 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

theorem rowCheck4309 : row4309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4309 := by decide +kernel

theorem rowEval4309 (x : Key → ℝ) : Integer.Sparse.eval row4309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck4309, Integer.Sparse.eval_collectBalanced, rawRowCheck4309]

def rawRow4310 : Integer.Sparse Key := [(key1338, -1), (key1344, -1), (key1456, -1), (key1658, -1), (key1465, -1), (key1666, -1), (key1338, 2), (key1456, 2), (key1656, 2), (key1317, 1), (key1325, 1), (key1425, 1), (key1623, 1), (key1443, 1), (key1632, 1), (key1297, -1), (key1317, -1), (key1392, -1), (key1547, -1), (key1425, -1), (key1574, -1), (key1312, -2), (key1420, -2), (key1618, -2), (key1292, 1), (key1312, 1), (key1387, 1), (key1542, 1), (key1420, 1), (key1569, 1)]

theorem rawRowCheck4310 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form5 = rawRow4310 := by decide +kernel

def row4310 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

theorem rowCheck4310 : row4310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4310 := by decide +kernel

theorem rowEval4310 (x : Key → ℝ) : Integer.Sparse.eval row4310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4310, Integer.Sparse.eval_collectBalanced, rawRowCheck4310]

def rawRow4311 : Integer.Sparse Key := [(key1344, -1), (key1338, -1), (key1658, -1), (key1456, -1), (key1666, -1), (key1465, -1), (key1338, 2), (key1656, 2), (key1456, 2), (key1325, 1), (key1317, 1), (key1623, 1), (key1425, 1), (key1632, 1), (key1443, 1), (key1317, -1), (key1297, -1), (key1547, -1), (key1392, -1), (key1574, -1), (key1425, -1), (key1312, -2), (key1618, -2), (key1420, -2), (key1312, 1), (key1292, 1), (key1542, 1), (key1387, 1), (key1569, 1), (key1420, 1)]

theorem rawRowCheck4311 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form5 = rawRow4311 := by decide +kernel

def row4311 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

theorem rowCheck4311 : row4311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4311 := by decide +kernel

theorem rowEval4311 (x : Key → ℝ) : Integer.Sparse.eval row4311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4311, Integer.Sparse.eval_collectBalanced, rawRowCheck4311]

def rawRow4312 : Integer.Sparse Key := [(key1456, -1), (key1465, -1), (key1338, -1), (key1666, -1), (key1344, -1), (key1658, -1), (key1456, 2), (key1338, 2), (key1656, 2), (key1425, 1), (key1443, 1), (key1317, 1), (key1632, 1), (key1325, 1), (key1623, 1), (key1392, -1), (key1425, -1), (key1297, -1), (key1574, -1), (key1317, -1), (key1547, -1), (key1420, -2), (key1312, -2), (key1618, -2), (key1387, 1), (key1420, 1), (key1292, 1), (key1569, 1), (key1312, 1), (key1542, 1)]

theorem rawRowCheck4312 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form5 = rawRow4312 := by decide +kernel

def row4312 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

theorem rowCheck4312 : row4312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4312 := by decide +kernel

theorem rowEval4312 (x : Key → ℝ) : Integer.Sparse.eval row4312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4312, Integer.Sparse.eval_collectBalanced, rawRowCheck4312]

def rawRow4313 : Integer.Sparse Key := [(key1465, -1), (key1456, -1), (key1666, -1), (key1338, -1), (key1658, -1), (key1344, -1), (key1456, 2), (key1656, 2), (key1338, 2), (key1443, 1), (key1425, 1), (key1632, 1), (key1317, 1), (key1623, 1), (key1325, 1), (key1425, -1), (key1392, -1), (key1574, -1), (key1297, -1), (key1547, -1), (key1317, -1), (key1420, -2), (key1618, -2), (key1312, -2), (key1420, 1), (key1387, 1), (key1569, 1), (key1292, 1), (key1542, 1), (key1312, 1)]

theorem rawRowCheck4313 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form5 = rawRow4313 := by decide +kernel

def row4313 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

theorem rowCheck4313 : row4313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4313 := by decide +kernel

theorem rowEval4313 (x : Key → ℝ) : Integer.Sparse.eval row4313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck4313, Integer.Sparse.eval_collectBalanced, rawRowCheck4313]

def rawRow4314 : Integer.Sparse Key := [(key1658, -1), (key1666, -1), (key1344, -1), (key1465, -1), (key1338, -1), (key1456, -1), (key1656, 2), (key1338, 2), (key1456, 2), (key1623, 1), (key1632, 1), (key1325, 1), (key1443, 1), (key1317, 1), (key1425, 1), (key1547, -1), (key1574, -1), (key1317, -1), (key1425, -1), (key1297, -1), (key1392, -1), (key1618, -2), (key1312, -2), (key1420, -2), (key1542, 1), (key1569, 1), (key1312, 1), (key1420, 1), (key1292, 1), (key1387, 1)]

theorem rawRowCheck4314 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form5 = rawRow4314 := by decide +kernel

def row4314 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

theorem rowCheck4314 : row4314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4314 := by decide +kernel

theorem rowEval4314 (x : Key → ℝ) : Integer.Sparse.eval row4314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4314, Integer.Sparse.eval_collectBalanced, rawRowCheck4314]

def rawRow4315 : Integer.Sparse Key := [(key1666, -1), (key1658, -1), (key1465, -1), (key1344, -1), (key1456, -1), (key1338, -1), (key1656, 2), (key1456, 2), (key1338, 2), (key1632, 1), (key1623, 1), (key1443, 1), (key1325, 1), (key1425, 1), (key1317, 1), (key1574, -1), (key1547, -1), (key1425, -1), (key1317, -1), (key1392, -1), (key1297, -1), (key1618, -2), (key1420, -2), (key1312, -2), (key1569, 1), (key1542, 1), (key1420, 1), (key1312, 1), (key1387, 1), (key1292, 1)]

theorem rawRowCheck4315 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form5 = rawRow4315 := by decide +kernel

def row4315 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

theorem rowCheck4315 : row4315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4315 := by decide +kernel

theorem rowEval4315 (x : Key → ℝ) : Integer.Sparse.eval row4315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck4315, Integer.Sparse.eval_collectBalanced, rawRowCheck4315]

def rawRow4316 : Integer.Sparse Key := [(key3052, -2), (key3067, -2), (key3104, -2), (key3048, 2), (key3062, 2), (key3097, 2), (key3056, 2), (key3073, 2), (key3111, 2), (key3048, -6), (key3056, -2), (key3071, -2), (key3108, -2), (key3052, 6)]

theorem rawRowCheck4316 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form6 = rawRow4316 := by decide +kernel

def row4316 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

theorem rowCheck4316 : row4316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4316 := by decide +kernel

theorem rowEval4316 (x : Key → ℝ) : Integer.Sparse.eval row4316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4316, Integer.Sparse.eval_collectBalanced, rawRowCheck4316]

def rawRow4317 : Integer.Sparse Key := [(key3067, -2), (key3052, -2), (key3104, -2), (key3062, 2), (key3048, 2), (key3097, 2), (key3073, 2), (key3056, 2), (key3111, 2), (key3048, -6), (key3071, -2), (key3056, -2), (key3108, -2), (key3052, 6)]

theorem rawRowCheck4317 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form6 = rawRow4317 := by decide +kernel

def row4317 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

theorem rowCheck4317 : row4317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4317 := by decide +kernel

theorem rowEval4317 (x : Key → ℝ) : Integer.Sparse.eval row4317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4317, Integer.Sparse.eval_collectBalanced, rawRowCheck4317]

def rawRow4318 : Integer.Sparse Key := [(key3052, -2), (key3104, -2), (key3067, -2), (key3048, 2), (key3097, 2), (key3062, 2), (key3056, 2), (key3111, 2), (key3073, 2), (key3048, -6), (key3056, -2), (key3108, -2), (key3071, -2), (key3052, 6)]

theorem rawRowCheck4318 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form6 = rawRow4318 := by decide +kernel

def row4318 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

theorem rowCheck4318 : row4318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4318 := by decide +kernel

theorem rowEval4318 (x : Key → ℝ) : Integer.Sparse.eval row4318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4318, Integer.Sparse.eval_collectBalanced, rawRowCheck4318]

def rawRow4319 : Integer.Sparse Key := [(key3104, -2), (key3052, -2), (key3067, -2), (key3097, 2), (key3048, 2), (key3062, 2), (key3111, 2), (key3056, 2), (key3073, 2), (key3048, -6), (key3108, -2), (key3056, -2), (key3071, -2), (key3052, 6)]

theorem rawRowCheck4319 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form6 = rawRow4319 := by decide +kernel

def row4319 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

theorem rowCheck4319 : row4319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4319 := by decide +kernel

theorem rowEval4319 (x : Key → ℝ) : Integer.Sparse.eval row4319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4319, Integer.Sparse.eval_collectBalanced, rawRowCheck4319]

def rawRow4320 : Integer.Sparse Key := [(key3067, -2), (key3104, -2), (key3052, -2), (key3062, 2), (key3097, 2), (key3048, 2), (key3073, 2), (key3111, 2), (key3056, 2), (key3048, -6), (key3071, -2), (key3108, -2), (key3056, -2), (key3052, 6)]

theorem rawRowCheck4320 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form6 = rawRow4320 := by decide +kernel

def row4320 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

theorem rowCheck4320 : row4320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4320 := by decide +kernel

theorem rowEval4320 (x : Key → ℝ) : Integer.Sparse.eval row4320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4320, Integer.Sparse.eval_collectBalanced, rawRowCheck4320]

def rawRow4321 : Integer.Sparse Key := [(key3104, -2), (key3067, -2), (key3052, -2), (key3097, 2), (key3062, 2), (key3048, 2), (key3111, 2), (key3073, 2), (key3056, 2), (key3048, -6), (key3108, -2), (key3071, -2), (key3056, -2), (key3052, 6)]

theorem rawRowCheck4321 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form6 = rawRow4321 := by decide +kernel

def row4321 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

theorem rowCheck4321 : row4321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4321 := by decide +kernel

theorem rowEval4321 (x : Key → ℝ) : Integer.Sparse.eval row4321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4321, Integer.Sparse.eval_collectBalanced, rawRowCheck4321]

def rawRow4322 : Integer.Sparse Key := [(key3056, -2), (key3073, -2), (key3111, -2), (key3056, 2), (key3071, 2), (key3108, 2), (key3052, 2), (key3067, 2), (key3104, 2), (key3052, -6), (key3048, -2), (key3062, -2), (key3097, -2), (key3048, 6)]

theorem rawRowCheck4322 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form6 = rawRow4322 := by decide +kernel

def row4322 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

theorem rowCheck4322 : row4322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4322 := by decide +kernel

theorem rowEval4322 (x : Key → ℝ) : Integer.Sparse.eval row4322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4322, Integer.Sparse.eval_collectBalanced, rawRowCheck4322]

def rawRow4323 : Integer.Sparse Key := [(key3073, -2), (key3056, -2), (key3111, -2), (key3071, 2), (key3056, 2), (key3108, 2), (key3067, 2), (key3052, 2), (key3104, 2), (key3052, -6), (key3062, -2), (key3048, -2), (key3097, -2), (key3048, 6)]

theorem rawRowCheck4323 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form6 = rawRow4323 := by decide +kernel

def row4323 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

theorem rowCheck4323 : row4323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4323 := by decide +kernel

theorem rowEval4323 (x : Key → ℝ) : Integer.Sparse.eval row4323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4323, Integer.Sparse.eval_collectBalanced, rawRowCheck4323]

def rawRow4324 : Integer.Sparse Key := [(key3056, -2), (key3111, -2), (key3073, -2), (key3056, 2), (key3108, 2), (key3071, 2), (key3052, 2), (key3104, 2), (key3067, 2), (key3052, -6), (key3048, -2), (key3097, -2), (key3062, -2), (key3048, 6)]

theorem rawRowCheck4324 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form6 = rawRow4324 := by decide +kernel

def row4324 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

theorem rowCheck4324 : row4324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4324 := by decide +kernel

theorem rowEval4324 (x : Key → ℝ) : Integer.Sparse.eval row4324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4324, Integer.Sparse.eval_collectBalanced, rawRowCheck4324]

def rawRow4325 : Integer.Sparse Key := [(key3111, -2), (key3056, -2), (key3073, -2), (key3108, 2), (key3056, 2), (key3071, 2), (key3104, 2), (key3052, 2), (key3067, 2), (key3052, -6), (key3097, -2), (key3048, -2), (key3062, -2), (key3048, 6)]

theorem rawRowCheck4325 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form6 = rawRow4325 := by decide +kernel

def row4325 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

theorem rowCheck4325 : row4325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4325 := by decide +kernel

theorem rowEval4325 (x : Key → ℝ) : Integer.Sparse.eval row4325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4325, Integer.Sparse.eval_collectBalanced, rawRowCheck4325]

def rawRow4326 : Integer.Sparse Key := [(key3073, -2), (key3111, -2), (key3056, -2), (key3071, 2), (key3108, 2), (key3056, 2), (key3067, 2), (key3104, 2), (key3052, 2), (key3052, -6), (key3062, -2), (key3097, -2), (key3048, -2), (key3048, 6)]

theorem rawRowCheck4326 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form6 = rawRow4326 := by decide +kernel

def row4326 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

theorem rowCheck4326 : row4326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4326 := by decide +kernel

theorem rowEval4326 (x : Key → ℝ) : Integer.Sparse.eval row4326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4326, Integer.Sparse.eval_collectBalanced, rawRowCheck4326]

def rawRow4327 : Integer.Sparse Key := [(key3111, -2), (key3073, -2), (key3056, -2), (key3108, 2), (key3071, 2), (key3056, 2), (key3104, 2), (key3067, 2), (key3052, 2), (key3052, -6), (key3097, -2), (key3062, -2), (key3048, -2), (key3048, 6)]

theorem rawRowCheck4327 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form6 = rawRow4327 := by decide +kernel

def row4327 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

theorem rowCheck4327 : row4327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4327 := by decide +kernel

theorem rowEval4327 (x : Key → ℝ) : Integer.Sparse.eval row4327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4327, Integer.Sparse.eval_collectBalanced, rawRowCheck4327]

def rawRow4328 : Integer.Sparse Key := [(key1656, -2), (key1658, -2), (key1666, -2), (key1547, 1), (key1555, 1), (key1574, 1), (key1623, 1), (key1592, 1), (key1632, 1), (key1814, 2), (key1816, 2), (key1824, 2), (key1317, -1), (key1325, -1), (key1425, -1), (key1623, -1), (key1443, -1), (key1632, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1816, -1), (key1797, -1), (key1824, -1), (key1338, 1), (key1344, 1), (key1456, 1), (key1658, 1), (key1465, 1), (key1666, 1)]

theorem rawRowCheck4328 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form7 = rawRow4328 := by decide +kernel

def row4328 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

theorem rowCheck4328 : row4328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4328 := by decide +kernel

theorem rowEval4328 (x : Key → ℝ) : Integer.Sparse.eval row4328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4328, Integer.Sparse.eval_collectBalanced, rawRowCheck4328]

def rawRow4329 : Integer.Sparse Key := [(key1658, -2), (key1656, -2), (key1666, -2), (key1555, 1), (key1547, 1), (key1623, 1), (key1574, 1), (key1632, 1), (key1592, 1), (key1816, 2), (key1814, 2), (key1824, 2), (key1325, -1), (key1317, -1), (key1623, -1), (key1425, -1), (key1632, -1), (key1443, -1), (key1779, -1), (key1773, -1), (key1816, -1), (key1789, -1), (key1824, -1), (key1797, -1), (key1344, 1), (key1338, 1), (key1658, 1), (key1456, 1), (key1666, 1), (key1465, 1)]

theorem rawRowCheck4329 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form7 = rawRow4329 := by decide +kernel

def row4329 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

theorem rowCheck4329 : row4329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4329 := by decide +kernel

theorem rowEval4329 (x : Key → ℝ) : Integer.Sparse.eval row4329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4329, Integer.Sparse.eval_collectBalanced, rawRowCheck4329]

def rawRow4330 : Integer.Sparse Key := [(key1656, -2), (key1666, -2), (key1658, -2), (key1574, 1), (key1592, 1), (key1547, 1), (key1632, 1), (key1555, 1), (key1623, 1), (key1814, 2), (key1824, 2), (key1816, 2), (key1425, -1), (key1443, -1), (key1317, -1), (key1632, -1), (key1325, -1), (key1623, -1), (key1789, -1), (key1797, -1), (key1773, -1), (key1824, -1), (key1779, -1), (key1816, -1), (key1456, 1), (key1465, 1), (key1338, 1), (key1666, 1), (key1344, 1), (key1658, 1)]

theorem rawRowCheck4330 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form7 = rawRow4330 := by decide +kernel

def row4330 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

theorem rowCheck4330 : row4330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4330 := by decide +kernel

theorem rowEval4330 (x : Key → ℝ) : Integer.Sparse.eval row4330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4330, Integer.Sparse.eval_collectBalanced, rawRowCheck4330]

def rawRow4331 : Integer.Sparse Key := [(key1666, -2), (key1656, -2), (key1658, -2), (key1592, 1), (key1574, 1), (key1632, 1), (key1547, 1), (key1623, 1), (key1555, 1), (key1824, 2), (key1814, 2), (key1816, 2), (key1443, -1), (key1425, -1), (key1632, -1), (key1317, -1), (key1623, -1), (key1325, -1), (key1797, -1), (key1789, -1), (key1824, -1), (key1773, -1), (key1816, -1), (key1779, -1), (key1465, 1), (key1456, 1), (key1666, 1), (key1338, 1), (key1658, 1), (key1344, 1)]

theorem rawRowCheck4331 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form7 = rawRow4331 := by decide +kernel

def row4331 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

theorem rowCheck4331 : row4331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4331 := by decide +kernel

theorem rowEval4331 (x : Key → ℝ) : Integer.Sparse.eval row4331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4331, Integer.Sparse.eval_collectBalanced, rawRowCheck4331]

def rawRow4332 : Integer.Sparse Key := [(key1658, -2), (key1666, -2), (key1656, -2), (key1623, 1), (key1632, 1), (key1555, 1), (key1592, 1), (key1547, 1), (key1574, 1), (key1816, 2), (key1824, 2), (key1814, 2), (key1623, -1), (key1632, -1), (key1325, -1), (key1443, -1), (key1317, -1), (key1425, -1), (key1816, -1), (key1824, -1), (key1779, -1), (key1797, -1), (key1773, -1), (key1789, -1), (key1658, 1), (key1666, 1), (key1344, 1), (key1465, 1), (key1338, 1), (key1456, 1)]

theorem rawRowCheck4332 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form7 = rawRow4332 := by decide +kernel

def row4332 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

theorem rowCheck4332 : row4332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4332 := by decide +kernel

theorem rowEval4332 (x : Key → ℝ) : Integer.Sparse.eval row4332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4332, Integer.Sparse.eval_collectBalanced, rawRowCheck4332]

def rawRow4333 : Integer.Sparse Key := [(key1666, -2), (key1658, -2), (key1656, -2), (key1632, 1), (key1623, 1), (key1592, 1), (key1555, 1), (key1574, 1), (key1547, 1), (key1824, 2), (key1816, 2), (key1814, 2), (key1632, -1), (key1623, -1), (key1443, -1), (key1325, -1), (key1425, -1), (key1317, -1), (key1824, -1), (key1816, -1), (key1797, -1), (key1779, -1), (key1789, -1), (key1773, -1), (key1666, 1), (key1658, 1), (key1465, 1), (key1344, 1), (key1456, 1), (key1338, 1)]

theorem rawRowCheck4333 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form7 = rawRow4333 := by decide +kernel

def row4333 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

theorem rowCheck4333 : row4333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4333 := by decide +kernel

theorem rowEval4333 (x : Key → ℝ) : Integer.Sparse.eval row4333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4333, Integer.Sparse.eval_collectBalanced, rawRowCheck4333]

def rawRow4334 : Integer.Sparse Key := [(key1814, -2), (key1816, -2), (key1824, -2), (key1773, 1), (key1779, 1), (key1789, 1), (key1816, 1), (key1797, 1), (key1824, 1), (key1656, 2), (key1658, 2), (key1666, 2), (key1338, -1), (key1344, -1), (key1456, -1), (key1658, -1), (key1465, -1), (key1666, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1623, -1), (key1592, -1), (key1632, -1), (key1317, 1), (key1325, 1), (key1425, 1), (key1623, 1), (key1443, 1), (key1632, 1)]

theorem rawRowCheck4334 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form7 = rawRow4334 := by decide +kernel

def row4334 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck4334 : row4334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4334 := by decide +kernel

theorem rowEval4334 (x : Key → ℝ) : Integer.Sparse.eval row4334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4334, Integer.Sparse.eval_collectBalanced, rawRowCheck4334]

def rawRow4335 : Integer.Sparse Key := [(key1816, -2), (key1814, -2), (key1824, -2), (key1779, 1), (key1773, 1), (key1816, 1), (key1789, 1), (key1824, 1), (key1797, 1), (key1658, 2), (key1656, 2), (key1666, 2), (key1344, -1), (key1338, -1), (key1658, -1), (key1456, -1), (key1666, -1), (key1465, -1), (key1555, -1), (key1547, -1), (key1623, -1), (key1574, -1), (key1632, -1), (key1592, -1), (key1325, 1), (key1317, 1), (key1623, 1), (key1425, 1), (key1632, 1), (key1443, 1)]

theorem rawRowCheck4335 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form7 = rawRow4335 := by decide +kernel

def row4335 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck4335 : row4335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4335 := by decide +kernel

theorem rowEval4335 (x : Key → ℝ) : Integer.Sparse.eval row4335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4335, Integer.Sparse.eval_collectBalanced, rawRowCheck4335]

def rawRow4336 : Integer.Sparse Key := [(key1814, -2), (key1824, -2), (key1816, -2), (key1789, 1), (key1797, 1), (key1773, 1), (key1824, 1), (key1779, 1), (key1816, 1), (key1656, 2), (key1666, 2), (key1658, 2), (key1456, -1), (key1465, -1), (key1338, -1), (key1666, -1), (key1344, -1), (key1658, -1), (key1574, -1), (key1592, -1), (key1547, -1), (key1632, -1), (key1555, -1), (key1623, -1), (key1425, 1), (key1443, 1), (key1317, 1), (key1632, 1), (key1325, 1), (key1623, 1)]

theorem rawRowCheck4336 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form7 = rawRow4336 := by decide +kernel

def row4336 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck4336 : row4336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4336 := by decide +kernel

theorem rowEval4336 (x : Key → ℝ) : Integer.Sparse.eval row4336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4336, Integer.Sparse.eval_collectBalanced, rawRowCheck4336]

def rawRow4337 : Integer.Sparse Key := [(key1824, -2), (key1814, -2), (key1816, -2), (key1797, 1), (key1789, 1), (key1824, 1), (key1773, 1), (key1816, 1), (key1779, 1), (key1666, 2), (key1656, 2), (key1658, 2), (key1465, -1), (key1456, -1), (key1666, -1), (key1338, -1), (key1658, -1), (key1344, -1), (key1592, -1), (key1574, -1), (key1632, -1), (key1547, -1), (key1623, -1), (key1555, -1), (key1443, 1), (key1425, 1), (key1632, 1), (key1317, 1), (key1623, 1), (key1325, 1)]

theorem rawRowCheck4337 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form7 = rawRow4337 := by decide +kernel

def row4337 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck4337 : row4337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4337 := by decide +kernel

theorem rowEval4337 (x : Key → ℝ) : Integer.Sparse.eval row4337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4337, Integer.Sparse.eval_collectBalanced, rawRowCheck4337]

def rawRow4338 : Integer.Sparse Key := [(key1816, -2), (key1824, -2), (key1814, -2), (key1816, 1), (key1824, 1), (key1779, 1), (key1797, 1), (key1773, 1), (key1789, 1), (key1658, 2), (key1666, 2), (key1656, 2), (key1658, -1), (key1666, -1), (key1344, -1), (key1465, -1), (key1338, -1), (key1456, -1), (key1623, -1), (key1632, -1), (key1555, -1), (key1592, -1), (key1547, -1), (key1574, -1), (key1623, 1), (key1632, 1), (key1325, 1), (key1443, 1), (key1317, 1), (key1425, 1)]

theorem rawRowCheck4338 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form7 = rawRow4338 := by decide +kernel

def row4338 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck4338 : row4338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4338 := by decide +kernel

theorem rowEval4338 (x : Key → ℝ) : Integer.Sparse.eval row4338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4338, Integer.Sparse.eval_collectBalanced, rawRowCheck4338]

def rawRow4339 : Integer.Sparse Key := [(key1824, -2), (key1816, -2), (key1814, -2), (key1824, 1), (key1816, 1), (key1797, 1), (key1779, 1), (key1789, 1), (key1773, 1), (key1666, 2), (key1658, 2), (key1656, 2), (key1666, -1), (key1658, -1), (key1465, -1), (key1344, -1), (key1456, -1), (key1338, -1), (key1632, -1), (key1623, -1), (key1592, -1), (key1555, -1), (key1574, -1), (key1547, -1), (key1632, 1), (key1623, 1), (key1443, 1), (key1325, 1), (key1425, 1), (key1317, 1)]

theorem rawRowCheck4339 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form7 = rawRow4339 := by decide +kernel

def row4339 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

theorem rowCheck4339 : row4339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4339 := by decide +kernel

theorem rowEval4339 (x : Key → ℝ) : Integer.Sparse.eval row4339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4339, Integer.Sparse.eval_collectBalanced, rawRowCheck4339]

def rawRow4340 : Integer.Sparse Key := [(key1110, -2), (key1120, -2), (key1147, -2), (key1106, 6), (key1189, 2), (key1196, 2), (key1209, 2), (key993, -2), (key1028, -2), (key1106, -2), (key1189, -6), (key997, 2), (key1032, 2), (key1110, 2)]

theorem rawRowCheck4340 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form8 = rawRow4340 := by decide +kernel

def row4340 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

theorem rowCheck4340 : row4340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4340 := by decide +kernel

theorem rowEval4340 (x : Key → ℝ) : Integer.Sparse.eval row4340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4340, Integer.Sparse.eval_collectBalanced, rawRowCheck4340]

def rawRow4341 : Integer.Sparse Key := [(key1120, -2), (key1110, -2), (key1147, -2), (key1106, 6), (key1196, 2), (key1189, 2), (key1209, 2), (key993, -2), (key1106, -2), (key1028, -2), (key1189, -6), (key997, 2), (key1110, 2), (key1032, 2)]

theorem rawRowCheck4341 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form8 = rawRow4341 := by decide +kernel

def row4341 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

theorem rowCheck4341 : row4341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4341 := by decide +kernel

theorem rowEval4341 (x : Key → ℝ) : Integer.Sparse.eval row4341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4341, Integer.Sparse.eval_collectBalanced, rawRowCheck4341]

def rawRow4342 : Integer.Sparse Key := [(key1110, -2), (key1147, -2), (key1120, -2), (key1106, 6), (key1189, 2), (key1209, 2), (key1196, 2), (key1028, -2), (key993, -2), (key1106, -2), (key1189, -6), (key1032, 2), (key997, 2), (key1110, 2)]

theorem rawRowCheck4342 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form8 = rawRow4342 := by decide +kernel

def row4342 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

theorem rowCheck4342 : row4342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4342 := by decide +kernel

theorem rowEval4342 (x : Key → ℝ) : Integer.Sparse.eval row4342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4342, Integer.Sparse.eval_collectBalanced, rawRowCheck4342]

def rawRow4343 : Integer.Sparse Key := [(key1147, -2), (key1110, -2), (key1120, -2), (key1106, 6), (key1209, 2), (key1189, 2), (key1196, 2), (key1028, -2), (key1106, -2), (key993, -2), (key1189, -6), (key1032, 2), (key1110, 2), (key997, 2)]

theorem rawRowCheck4343 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form8 = rawRow4343 := by decide +kernel

def row4343 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

theorem rowCheck4343 : row4343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4343 := by decide +kernel

theorem rowEval4343 (x : Key → ℝ) : Integer.Sparse.eval row4343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4343, Integer.Sparse.eval_collectBalanced, rawRowCheck4343]

def rawRow4344 : Integer.Sparse Key := [(key1120, -2), (key1147, -2), (key1110, -2), (key1106, 6), (key1196, 2), (key1209, 2), (key1189, 2), (key1106, -2), (key993, -2), (key1028, -2), (key1189, -6), (key1110, 2), (key997, 2), (key1032, 2)]

theorem rawRowCheck4344 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form8 = rawRow4344 := by decide +kernel

def row4344 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

theorem rowCheck4344 : row4344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4344 := by decide +kernel

theorem rowEval4344 (x : Key → ℝ) : Integer.Sparse.eval row4344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4344, Integer.Sparse.eval_collectBalanced, rawRowCheck4344]

def rawRow4345 : Integer.Sparse Key := [(key1147, -2), (key1120, -2), (key1110, -2), (key1106, 6), (key1209, 2), (key1196, 2), (key1189, 2), (key1106, -2), (key1028, -2), (key993, -2), (key1189, -6), (key1110, 2), (key1032, 2), (key997, 2)]

theorem rawRowCheck4345 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form8 = rawRow4345 := by decide +kernel

def row4345 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

theorem rowCheck4345 : row4345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4345 := by decide +kernel

theorem rowEval4345 (x : Key → ℝ) : Integer.Sparse.eval row4345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4345, Integer.Sparse.eval_collectBalanced, rawRowCheck4345]

def rawRow4346 : Integer.Sparse Key := [(key1189, -2), (key1196, -2), (key1209, -2), (key1189, 6), (key1110, 2), (key1120, 2), (key1147, 2), (key997, -2), (key1032, -2), (key1110, -2), (key1106, -6), (key993, 2), (key1028, 2), (key1106, 2)]

theorem rawRowCheck4346 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form8 = rawRow4346 := by decide +kernel

def row4346 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck4346 : row4346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4346 := by decide +kernel

theorem rowEval4346 (x : Key → ℝ) : Integer.Sparse.eval row4346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4346, Integer.Sparse.eval_collectBalanced, rawRowCheck4346]

def rawRow4347 : Integer.Sparse Key := [(key1196, -2), (key1189, -2), (key1209, -2), (key1189, 6), (key1120, 2), (key1110, 2), (key1147, 2), (key997, -2), (key1110, -2), (key1032, -2), (key1106, -6), (key993, 2), (key1106, 2), (key1028, 2)]

theorem rawRowCheck4347 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form8 = rawRow4347 := by decide +kernel

def row4347 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck4347 : row4347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4347 := by decide +kernel

theorem rowEval4347 (x : Key → ℝ) : Integer.Sparse.eval row4347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4347, Integer.Sparse.eval_collectBalanced, rawRowCheck4347]

def rawRow4348 : Integer.Sparse Key := [(key1189, -2), (key1209, -2), (key1196, -2), (key1189, 6), (key1110, 2), (key1147, 2), (key1120, 2), (key1032, -2), (key997, -2), (key1110, -2), (key1106, -6), (key1028, 2), (key993, 2), (key1106, 2)]

theorem rawRowCheck4348 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form8 = rawRow4348 := by decide +kernel

def row4348 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck4348 : row4348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4348 := by decide +kernel

theorem rowEval4348 (x : Key → ℝ) : Integer.Sparse.eval row4348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4348, Integer.Sparse.eval_collectBalanced, rawRowCheck4348]

def rawRow4349 : Integer.Sparse Key := [(key1209, -2), (key1189, -2), (key1196, -2), (key1189, 6), (key1147, 2), (key1110, 2), (key1120, 2), (key1032, -2), (key1110, -2), (key997, -2), (key1106, -6), (key1028, 2), (key1106, 2), (key993, 2)]

theorem rawRowCheck4349 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form8 = rawRow4349 := by decide +kernel

def row4349 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck4349 : row4349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4349 := by decide +kernel

theorem rowEval4349 (x : Key → ℝ) : Integer.Sparse.eval row4349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4349, Integer.Sparse.eval_collectBalanced, rawRowCheck4349]

def rawRow4350 : Integer.Sparse Key := [(key1196, -2), (key1209, -2), (key1189, -2), (key1189, 6), (key1120, 2), (key1147, 2), (key1110, 2), (key1110, -2), (key997, -2), (key1032, -2), (key1106, -6), (key1106, 2), (key993, 2), (key1028, 2)]

theorem rawRowCheck4350 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form8 = rawRow4350 := by decide +kernel

def row4350 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck4350 : row4350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4350 := by decide +kernel

theorem rowEval4350 (x : Key → ℝ) : Integer.Sparse.eval row4350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4350, Integer.Sparse.eval_collectBalanced, rawRowCheck4350]

def rawRow4351 : Integer.Sparse Key := [(key1209, -2), (key1196, -2), (key1189, -2), (key1189, 6), (key1147, 2), (key1120, 2), (key1110, 2), (key1110, -2), (key1032, -2), (key997, -2), (key1106, -6), (key1106, 2), (key1028, 2), (key993, 2)]

theorem rawRowCheck4351 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form8 = rawRow4351 := by decide +kernel

def row4351 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

theorem rowCheck4351 : row4351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4351 := by decide +kernel

theorem rowEval4351 (x : Key → ℝ) : Integer.Sparse.eval row4351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4351, Integer.Sparse.eval_collectBalanced, rawRowCheck4351]

end MUB6.Certificate.GramRows

end OAI
