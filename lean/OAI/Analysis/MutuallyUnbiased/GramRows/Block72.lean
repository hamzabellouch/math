import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
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

def rawRow6144 : Integer.Sparse Key := [(key260, -1), (key248, -1), (key251, 2), (key260, -1), (key248, -1), (key271, 2), (key236, 2), (key260, -1), (key239, -1), (key251, 2), (key260, -1), (key239, -1), (key335, 1), (key316, 1), (key319, -2), (key335, 1), (key316, 1), (key340, -2), (key302, -2), (key328, 1), (key305, 1), (key319, -2), (key328, 1), (key305, 1), (key469, -1), (key406, -1), (key442, 1), (key409, 1), (key475, 1), (key385, 1), (key450, -1), (key388, -1), (key469, -1), (key406, -1), (key475, 1), (key385, 1), (key442, 1), (key409, 1), (key450, -1), (key388, -1)]

theorem rawRowCheck6144 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form6 = rawRow6144 := by decide +kernel

def row6144 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key251, 4), (key260, -4), (key271, 2), (key302, -2), (key305, 2), (key316, 2), (key319, -4), (key328, 2), (key335, 2), (key340, -2), (key385, 2), (key388, -2), (key406, -2), (key409, 2), (key442, 2), (key450, -2), (key469, -2), (key475, 2)]

theorem rowCheck6144 : row6144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6144 := by decide +kernel

theorem rowEval6144 (x : Key → ℝ) : Integer.Sparse.eval row6144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6144, Integer.Sparse.eval_collectBalanced, rawRowCheck6144]

def rawRow6145 : Integer.Sparse Key := [(key251, -1), (key260, -1), (key248, 2), (key267, -1), (key271, -1), (key239, 2), (key260, 2), (key236, -1), (key248, -1), (key260, 2), (key239, -1), (key251, -1), (key319, 1), (key335, 1), (key316, -2), (key328, 1), (key340, 1), (key305, -2), (key335, -2), (key302, 1), (key316, 1), (key328, -2), (key305, 1), (key319, 1), (key409, -1), (key467, -1), (key406, 1), (key435, 1), (key388, 1), (key467, 1), (key385, -1), (key435, -1), (key418, -1), (key475, -1), (key397, 1), (key469, 1), (key418, 1), (key450, 1), (key397, -1), (key442, -1)]

theorem rawRowCheck6145 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form6 = rawRow6145 := by decide +kernel

def row6145 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 3), (key267, -1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

theorem rowCheck6145 : row6145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6145 := by decide +kernel

theorem rowEval6145 (x : Key → ℝ) : Integer.Sparse.eval row6145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6145, Integer.Sparse.eval_collectBalanced, rawRowCheck6145]

def rawRow6146 : Integer.Sparse Key := [(key260, -1), (key251, -1), (key248, 2), (key271, -1), (key267, -1), (key260, 2), (key239, 2), (key248, -1), (key236, -1), (key260, 2), (key251, -1), (key239, -1), (key335, 1), (key319, 1), (key316, -2), (key340, 1), (key328, 1), (key335, -2), (key305, -2), (key316, 1), (key302, 1), (key328, -2), (key319, 1), (key305, 1), (key467, -1), (key409, -1), (key435, 1), (key406, 1), (key467, 1), (key388, 1), (key435, -1), (key385, -1), (key475, -1), (key418, -1), (key469, 1), (key397, 1), (key450, 1), (key418, 1), (key442, -1), (key397, -1)]

theorem rawRowCheck6146 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form6 = rawRow6146 := by decide +kernel

def row6146 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 3), (key267, -1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

theorem rowCheck6146 : row6146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6146 := by decide +kernel

theorem rowEval6146 (x : Key → ℝ) : Integer.Sparse.eval row6146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6146, Integer.Sparse.eval_collectBalanced, rawRowCheck6146]

def rawRow6147 : Integer.Sparse Key := [(key267, -1), (key267, -1), (key271, 2), (key239, -1), (key239, -1), (key251, 2), (key251, 2), (key260, -1), (key260, -1), (key236, 2), (key248, -1), (key248, -1), (key328, 1), (key328, 1), (key340, -2), (key305, 1), (key305, 1), (key319, -2), (key319, -2), (key335, 1), (key335, 1), (key302, -2), (key316, 1), (key316, 1), (key450, -1), (key450, -1), (key475, 1), (key475, 1), (key442, 1), (key442, 1), (key469, -1), (key469, -1), (key388, -1), (key388, -1), (key409, 1), (key409, 1), (key385, 1), (key385, 1), (key406, -1), (key406, -1)]

theorem rawRowCheck6147 : GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form6 = rawRow6147 := by decide +kernel

def row6147 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key251, 4), (key260, -2), (key267, -2), (key271, 2), (key302, -2), (key305, 2), (key316, 2), (key319, -4), (key328, 2), (key335, 2), (key340, -2), (key385, 2), (key388, -2), (key406, -2), (key409, 2), (key442, 2), (key450, -2), (key469, -2), (key475, 2)]

theorem rowCheck6147 : row6147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6147 := by decide +kernel

theorem rowEval6147 (x : Key → ℝ) : Integer.Sparse.eval row6147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6147, Integer.Sparse.eval_collectBalanced, rawRowCheck6147]

def rawRow6148 : Integer.Sparse Key := [(key267, -1), (key271, -1), (key267, 2), (key251, -1), (key260, -1), (key239, 2), (key260, 2), (key239, -1), (key251, -1), (key248, 2), (key236, -1), (key248, -1), (key328, 1), (key340, 1), (key328, -2), (key319, 1), (key335, 1), (key305, -2), (key335, -2), (key305, 1), (key319, 1), (key316, -2), (key302, 1), (key316, 1), (key418, -1), (key475, -1), (key418, 1), (key450, 1), (key397, 1), (key469, 1), (key397, -1), (key442, -1), (key409, -1), (key467, -1), (key388, 1), (key467, 1), (key406, 1), (key435, 1), (key385, -1), (key435, -1)]

theorem rawRowCheck6148 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form6 = rawRow6148 := by decide +kernel

def row6148 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

theorem rowCheck6148 : row6148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6148 := by decide +kernel

theorem rowEval6148 (x : Key → ℝ) : Integer.Sparse.eval row6148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6148, Integer.Sparse.eval_collectBalanced, rawRowCheck6148]

def rawRow6149 : Integer.Sparse Key := [(key271, -1), (key267, -1), (key267, 2), (key260, -1), (key251, -1), (key260, 2), (key239, 2), (key251, -1), (key239, -1), (key248, 2), (key248, -1), (key236, -1), (key340, 1), (key328, 1), (key328, -2), (key335, 1), (key319, 1), (key335, -2), (key305, -2), (key319, 1), (key305, 1), (key316, -2), (key316, 1), (key302, 1), (key475, -1), (key418, -1), (key450, 1), (key418, 1), (key469, 1), (key397, 1), (key442, -1), (key397, -1), (key467, -1), (key409, -1), (key467, 1), (key388, 1), (key435, 1), (key406, 1), (key435, -1), (key385, -1)]

theorem rawRowCheck6149 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form6 = rawRow6149 := by decide +kernel

def row6149 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

theorem rowCheck6149 : row6149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6149 := by decide +kernel

theorem rowEval6149 (x : Key → ℝ) : Integer.Sparse.eval row6149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6149, Integer.Sparse.eval_collectBalanced, rawRowCheck6149]

def rawRow6150 : Integer.Sparse Key := [(key302, -1), (key305, -1), (key305, 2), (key316, -1), (key319, -1), (key316, 2), (key335, 2), (key319, -1), (key335, -1), (key328, 2), (key328, -1), (key340, -1), (key236, 1), (key239, 1), (key239, -2), (key406, 1), (key409, 1), (key406, -2), (key418, -2), (key409, 1), (key418, 1), (key578, -2), (key578, 1), (key583, 1), (key248, -1), (key260, -1), (key251, 1), (key260, 1), (key316, 1), (key328, 1), (key319, -1), (key328, -1), (key435, -1), (key442, -1), (key435, 1), (key450, 1), (key593, 1), (key595, 1), (key593, -1), (key601, -1)]

theorem rawRowCheck6150 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form6 = rawRow6150 := by decide +kernel

def row6150 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -1), (key442, -1), (key450, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck6150 : row6150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6150 := by decide +kernel

theorem rowEval6150 (x : Key → ℝ) : Integer.Sparse.eval row6150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6150, Integer.Sparse.eval_collectBalanced, rawRowCheck6150]

def rawRow6151 : Integer.Sparse Key := [(key305, -1), (key302, -1), (key305, 2), (key319, -1), (key316, -1), (key335, 2), (key316, 2), (key335, -1), (key319, -1), (key328, 2), (key340, -1), (key328, -1), (key239, 1), (key236, 1), (key239, -2), (key409, 1), (key406, 1), (key418, -2), (key406, -2), (key418, 1), (key409, 1), (key578, -2), (key583, 1), (key578, 1), (key260, -1), (key248, -1), (key260, 1), (key251, 1), (key328, 1), (key316, 1), (key328, -1), (key319, -1), (key442, -1), (key435, -1), (key450, 1), (key435, 1), (key595, 1), (key593, 1), (key601, -1), (key593, -1)]

theorem rawRowCheck6151 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form6 = rawRow6151 := by decide +kernel

def row6151 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -1), (key442, -1), (key450, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck6151 : row6151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6151 := by decide +kernel

theorem rowEval6151 (x : Key → ℝ) : Integer.Sparse.eval row6151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6151, Integer.Sparse.eval_collectBalanced, rawRowCheck6151]

def rawRow6152 : Integer.Sparse Key := [(key305, -1), (key305, -1), (key302, 2), (key335, -1), (key335, -1), (key319, 2), (key319, 2), (key316, -1), (key316, -1), (key340, 2), (key328, -1), (key328, -1), (key239, 1), (key239, 1), (key236, -2), (key418, 1), (key418, 1), (key409, -2), (key409, -2), (key406, 1), (key406, 1), (key583, -2), (key578, 1), (key578, 1), (key251, -1), (key251, -1), (key248, 1), (key248, 1), (key319, 1), (key319, 1), (key316, -1), (key316, -1), (key450, -1), (key450, -1), (key442, 1), (key442, 1), (key601, 1), (key601, 1), (key595, -1), (key595, -1)]

theorem rawRowCheck6152 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form6 = rawRow6152 := by decide +kernel

def row6152 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key251, -2), (key302, 2), (key305, -2), (key316, -4), (key319, 6), (key328, -2), (key335, -2), (key340, 2), (key406, 2), (key409, -4), (key418, 2), (key442, 2), (key450, -2), (key578, 2), (key583, -2), (key595, -2), (key601, 2)]

theorem rowCheck6152 : row6152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6152 := by decide +kernel

theorem rowEval6152 (x : Key → ℝ) : Integer.Sparse.eval row6152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6152, Integer.Sparse.eval_collectBalanced, rawRowCheck6152]

def rawRow6153 : Integer.Sparse Key := [(key316, -1), (key319, -1), (key328, 2), (key302, -1), (key305, -1), (key316, 2), (key335, 2), (key328, -1), (key340, -1), (key305, 2), (key319, -1), (key335, -1), (key406, 1), (key409, 1), (key418, -2), (key236, 1), (key239, 1), (key406, -2), (key418, -2), (key578, 1), (key583, 1), (key239, -2), (key409, 1), (key418, 1), (key435, -1), (key442, -1), (key593, 1), (key595, 1), (key435, 1), (key450, 1), (key593, -1), (key601, -1), (key248, -1), (key260, -1), (key316, 1), (key328, 1), (key251, 1), (key260, 1), (key319, -1), (key328, -1)]

theorem rawRowCheck6153 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form6 = rawRow6153 := by decide +kernel

def row6153 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -3), (key442, -1), (key450, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck6153 : row6153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6153 := by decide +kernel

theorem rowEval6153 (x : Key → ℝ) : Integer.Sparse.eval row6153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6153, Integer.Sparse.eval_collectBalanced, rawRowCheck6153]

def rawRow6154 : Integer.Sparse Key := [(key319, -1), (key316, -1), (key328, 2), (key305, -1), (key302, -1), (key335, 2), (key316, 2), (key340, -1), (key328, -1), (key305, 2), (key335, -1), (key319, -1), (key409, 1), (key406, 1), (key418, -2), (key239, 1), (key236, 1), (key418, -2), (key406, -2), (key583, 1), (key578, 1), (key239, -2), (key418, 1), (key409, 1), (key442, -1), (key435, -1), (key595, 1), (key593, 1), (key450, 1), (key435, 1), (key601, -1), (key593, -1), (key260, -1), (key248, -1), (key328, 1), (key316, 1), (key260, 1), (key251, 1), (key328, -1), (key319, -1)]

theorem rawRowCheck6154 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form6 = rawRow6154 := by decide +kernel

def row6154 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -3), (key442, -1), (key450, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck6154 : row6154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6154 := by decide +kernel

theorem rowEval6154 (x : Key → ℝ) : Integer.Sparse.eval row6154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6154, Integer.Sparse.eval_collectBalanced, rawRowCheck6154]

def rawRow6155 : Integer.Sparse Key := [(key316, -1), (key328, -1), (key319, 2), (key316, -1), (key328, -1), (key302, 2), (key340, 2), (key305, -1), (key335, -1), (key319, 2), (key305, -1), (key335, -1), (key406, 1), (key418, 1), (key409, -2), (key406, 1), (key418, 1), (key236, -2), (key583, -2), (key239, 1), (key418, 1), (key409, -2), (key239, 1), (key418, 1), (key316, -1), (key595, -1), (key319, 1), (key442, 1), (key248, 1), (key601, 1), (key251, -1), (key450, -1), (key316, -1), (key595, -1), (key248, 1), (key601, 1), (key319, 1), (key442, 1), (key251, -1), (key450, -1)]

theorem rawRowCheck6155 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form6 = rawRow6155 := by decide +kernel

def row6155 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key251, -2), (key302, 2), (key305, -2), (key316, -4), (key319, 6), (key328, -2), (key335, -2), (key340, 2), (key406, 2), (key409, -4), (key418, 4), (key442, 2), (key450, -2), (key583, -2), (key595, -2), (key601, 2)]

theorem rowCheck6155 : row6155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6155 := by decide +kernel

theorem rowEval6155 (x : Key → ℝ) : Integer.Sparse.eval row6155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6155, Integer.Sparse.eval_collectBalanced, rawRowCheck6155]

def rawRow6156 : Integer.Sparse Key := [(key328, -1), (key316, -1), (key319, 2), (key328, -1), (key316, -1), (key340, 2), (key302, 2), (key335, -1), (key305, -1), (key319, 2), (key335, -1), (key305, -1), (key418, 1), (key406, 1), (key409, -2), (key418, 1), (key406, 1), (key583, -2), (key236, -2), (key418, 1), (key239, 1), (key409, -2), (key418, 1), (key239, 1), (key595, -1), (key316, -1), (key442, 1), (key319, 1), (key601, 1), (key248, 1), (key450, -1), (key251, -1), (key595, -1), (key316, -1), (key601, 1), (key248, 1), (key442, 1), (key319, 1), (key450, -1), (key251, -1)]

theorem rawRowCheck6156 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form6 = rawRow6156 := by decide +kernel

def row6156 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key251, -2), (key302, 2), (key305, -2), (key316, -4), (key319, 6), (key328, -2), (key335, -2), (key340, 2), (key406, 2), (key409, -4), (key418, 4), (key442, 2), (key450, -2), (key583, -2), (key595, -2), (key601, 2)]

theorem rowCheck6156 : row6156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6156 := by decide +kernel

theorem rowEval6156 (x : Key → ℝ) : Integer.Sparse.eval row6156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6156, Integer.Sparse.eval_collectBalanced, rawRowCheck6156]

def rawRow6157 : Integer.Sparse Key := [(key319, -1), (key328, -1), (key316, 2), (key335, -1), (key340, -1), (key305, 2), (key328, 2), (key302, -1), (key316, -1), (key335, 2), (key305, -1), (key319, -1), (key409, 1), (key418, 1), (key406, -2), (key578, 1), (key583, 1), (key239, -2), (key418, -2), (key236, 1), (key406, 1), (key418, -2), (key239, 1), (key409, 1), (key319, -1), (key593, -1), (key316, 1), (key435, 1), (key251, 1), (key593, 1), (key248, -1), (key435, -1), (key328, -1), (key601, -1), (key260, 1), (key595, 1), (key328, 1), (key450, 1), (key260, -1), (key442, -1)]

theorem rawRowCheck6157 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form6 = rawRow6157 := by decide +kernel

def row6157 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -3), (key442, -1), (key450, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck6157 : row6157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6157 := by decide +kernel

theorem rowEval6157 (x : Key → ℝ) : Integer.Sparse.eval row6157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6157, Integer.Sparse.eval_collectBalanced, rawRowCheck6157]

def rawRow6158 : Integer.Sparse Key := [(key328, -1), (key319, -1), (key316, 2), (key340, -1), (key335, -1), (key328, 2), (key305, 2), (key316, -1), (key302, -1), (key335, 2), (key319, -1), (key305, -1), (key418, 1), (key409, 1), (key406, -2), (key583, 1), (key578, 1), (key418, -2), (key239, -2), (key406, 1), (key236, 1), (key418, -2), (key409, 1), (key239, 1), (key593, -1), (key319, -1), (key435, 1), (key316, 1), (key593, 1), (key251, 1), (key435, -1), (key248, -1), (key601, -1), (key328, -1), (key595, 1), (key260, 1), (key450, 1), (key328, 1), (key442, -1), (key260, -1)]

theorem rawRowCheck6158 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form6 = rawRow6158 := by decide +kernel

def row6158 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -3), (key442, -1), (key450, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck6158 : row6158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6158 := by decide +kernel

theorem rowEval6158 (x : Key → ℝ) : Integer.Sparse.eval row6158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6158, Integer.Sparse.eval_collectBalanced, rawRowCheck6158]

def rawRow6159 : Integer.Sparse Key := [(key335, -1), (key335, -1), (key340, 2), (key305, -1), (key305, -1), (key319, 2), (key319, 2), (key328, -1), (key328, -1), (key302, 2), (key316, -1), (key316, -1), (key578, 1), (key578, 1), (key583, -2), (key239, 1), (key239, 1), (key409, -2), (key409, -2), (key418, 1), (key418, 1), (key236, -2), (key406, 1), (key406, 1), (key450, -1), (key450, -1), (key601, 1), (key601, 1), (key442, 1), (key442, 1), (key595, -1), (key595, -1), (key251, -1), (key251, -1), (key319, 1), (key319, 1), (key248, 1), (key248, 1), (key316, -1), (key316, -1)]

theorem rawRowCheck6159 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form6 = rawRow6159 := by decide +kernel

def row6159 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key251, -2), (key302, 2), (key305, -2), (key316, -4), (key319, 6), (key328, -2), (key335, -2), (key340, 2), (key406, 2), (key409, -4), (key418, 2), (key442, 2), (key450, -2), (key578, 2), (key583, -2), (key595, -2), (key601, 2)]

theorem rowCheck6159 : row6159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6159 := by decide +kernel

theorem rowEval6159 (x : Key → ℝ) : Integer.Sparse.eval row6159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6159, Integer.Sparse.eval_collectBalanced, rawRowCheck6159]

def rawRow6160 : Integer.Sparse Key := [(key335, -1), (key340, -1), (key335, 2), (key319, -1), (key328, -1), (key305, 2), (key328, 2), (key305, -1), (key319, -1), (key316, 2), (key302, -1), (key316, -1), (key578, 1), (key583, 1), (key578, -2), (key409, 1), (key418, 1), (key239, -2), (key418, -2), (key239, 1), (key409, 1), (key406, -2), (key236, 1), (key406, 1), (key328, -1), (key601, -1), (key328, 1), (key450, 1), (key260, 1), (key595, 1), (key260, -1), (key442, -1), (key319, -1), (key593, -1), (key251, 1), (key593, 1), (key316, 1), (key435, 1), (key248, -1), (key435, -1)]

theorem rawRowCheck6160 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form6 = rawRow6160 := by decide +kernel

def row6160 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -1), (key442, -1), (key450, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck6160 : row6160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6160 := by decide +kernel

theorem rowEval6160 (x : Key → ℝ) : Integer.Sparse.eval row6160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6160, Integer.Sparse.eval_collectBalanced, rawRowCheck6160]

def rawRow6161 : Integer.Sparse Key := [(key340, -1), (key335, -1), (key335, 2), (key328, -1), (key319, -1), (key328, 2), (key305, 2), (key319, -1), (key305, -1), (key316, 2), (key316, -1), (key302, -1), (key583, 1), (key578, 1), (key578, -2), (key418, 1), (key409, 1), (key418, -2), (key239, -2), (key409, 1), (key239, 1), (key406, -2), (key406, 1), (key236, 1), (key601, -1), (key328, -1), (key450, 1), (key328, 1), (key595, 1), (key260, 1), (key442, -1), (key260, -1), (key593, -1), (key319, -1), (key593, 1), (key251, 1), (key435, 1), (key316, 1), (key435, -1), (key248, -1)]

theorem rawRowCheck6161 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form6 = rawRow6161 := by decide +kernel

def row6161 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -1), (key442, -1), (key450, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

theorem rowCheck6161 : row6161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6161 := by decide +kernel

theorem rowEval6161 (x : Key → ℝ) : Integer.Sparse.eval row6161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6161, Integer.Sparse.eval_collectBalanced, rawRowCheck6161]

def rawRow6162 : Integer.Sparse Key := [(key385, -1), (key397, -1), (key388, 2), (key435, -1), (key442, -1), (key406, 2), (key469, 2), (key409, -1), (key467, -1), (key450, 2), (key418, -1), (key475, -1), (key248, 1), (key260, 1), (key251, -2), (key435, 1), (key442, 1), (key316, -2), (key595, -2), (key319, 1), (key593, 1), (key450, -2), (key328, 1), (key601, 1), (key236, -1), (key271, -1), (key239, 1), (key260, 1), (key302, 1), (key340, 1), (key305, -1), (key328, -1), (key406, -1), (key469, -1), (key385, 1), (key475, 1), (key578, 1), (key595, 1), (key568, -1), (key601, -1)]

theorem rawRowCheck6162 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form6 = rawRow6162 := by decide +kernel

def row6162 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -2), (key319, 1), (key340, 1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key418, -1), (key467, -1), (key469, 1), (key568, -1), (key578, 1), (key593, 1), (key595, -1)]

theorem rowCheck6162 : row6162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6162 := by decide +kernel

theorem rowEval6162 (x : Key → ℝ) : Integer.Sparse.eval row6162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6162, Integer.Sparse.eval_collectBalanced, rawRowCheck6162]

def rawRow6163 : Integer.Sparse Key := [(key397, -1), (key385, -1), (key388, 2), (key442, -1), (key435, -1), (key469, 2), (key406, 2), (key467, -1), (key409, -1), (key450, 2), (key475, -1), (key418, -1), (key260, 1), (key248, 1), (key251, -2), (key442, 1), (key435, 1), (key595, -2), (key316, -2), (key593, 1), (key319, 1), (key450, -2), (key601, 1), (key328, 1), (key271, -1), (key236, -1), (key260, 1), (key239, 1), (key340, 1), (key302, 1), (key328, -1), (key305, -1), (key469, -1), (key406, -1), (key475, 1), (key385, 1), (key595, 1), (key578, 1), (key601, -1), (key568, -1)]

theorem rawRowCheck6163 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form6 = rawRow6163 := by decide +kernel

def row6163 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -2), (key319, 1), (key340, 1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key418, -1), (key467, -1), (key469, 1), (key568, -1), (key578, 1), (key593, 1), (key595, -1)]

theorem rowCheck6163 : row6163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6163 := by decide +kernel

theorem rowEval6163 (x : Key → ℝ) : Integer.Sparse.eval row6163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6163, Integer.Sparse.eval_collectBalanced, rawRowCheck6163]

def rawRow6164 : Integer.Sparse Key := [(key388, -1), (key397, -1), (key385, 2), (key467, -1), (key469, -1), (key409, 2), (key442, 2), (key406, -1), (key435, -1), (key475, 2), (key418, -1), (key450, -1), (key251, 1), (key260, 1), (key248, -2), (key593, 1), (key595, 1), (key319, -2), (key442, -2), (key316, 1), (key435, 1), (key601, -2), (key328, 1), (key450, 1), (key239, -1), (key260, -1), (key236, 1), (key248, 1), (key305, 1), (key335, 1), (key302, -1), (key316, -1), (key418, -1), (key475, -1), (key397, 1), (key469, 1), (key583, 1), (key601, 1), (key572, -1), (key595, -1)]

theorem rawRowCheck6164 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form6 = rawRow6164 := by decide +kernel

def row6164 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 1), (key385, 2), (key388, -1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key572, -1), (key583, 1), (key593, 1), (key601, -1)]

theorem rowCheck6164 : row6164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6164 := by decide +kernel

theorem rowEval6164 (x : Key → ℝ) : Integer.Sparse.eval row6164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6164, Integer.Sparse.eval_collectBalanced, rawRowCheck6164]

def rawRow6165 : Integer.Sparse Key := [(key397, -1), (key388, -1), (key385, 2), (key469, -1), (key467, -1), (key442, 2), (key409, 2), (key435, -1), (key406, -1), (key475, 2), (key450, -1), (key418, -1), (key260, 1), (key251, 1), (key248, -2), (key595, 1), (key593, 1), (key442, -2), (key319, -2), (key435, 1), (key316, 1), (key601, -2), (key450, 1), (key328, 1), (key260, -1), (key239, -1), (key248, 1), (key236, 1), (key335, 1), (key305, 1), (key316, -1), (key302, -1), (key475, -1), (key418, -1), (key469, 1), (key397, 1), (key601, 1), (key583, 1), (key595, -1), (key572, -1)]

theorem rawRowCheck6165 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form6 = rawRow6165 := by decide +kernel

def row6165 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 1), (key385, 2), (key388, -1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key572, -1), (key583, 1), (key593, 1), (key601, -1)]

theorem rowCheck6165 : row6165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6165 := by decide +kernel

theorem rowEval6165 (x : Key → ℝ) : Integer.Sparse.eval row6165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6165, Integer.Sparse.eval_collectBalanced, rawRowCheck6165]

def rawRow6166 : Integer.Sparse Key := [(key406, -1), (key418, -1), (key409, 2), (key435, -1), (key450, -1), (key385, 2), (key475, 2), (key388, -1), (key467, -1), (key442, 2), (key397, -1), (key469, -1), (key316, 1), (key328, 1), (key319, -2), (key435, 1), (key450, 1), (key248, -2), (key601, -2), (key251, 1), (key593, 1), (key442, -2), (key260, 1), (key595, 1), (key302, -1), (key340, -1), (key305, 1), (key335, 1), (key236, 1), (key583, 1), (key239, -1), (key418, -1), (key316, -1), (key595, -1), (key248, 1), (key601, 1), (key335, 1), (key469, 1), (key267, -1), (key475, -1)]

theorem rawRowCheck6166 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form6 = rawRow6166 := by decide +kernel

def row6166 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key260, 1), (key267, -1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 2), (key340, -1), (key385, 2), (key388, -1), (key397, -1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key583, 1), (key593, 1), (key601, -1)]

theorem rowCheck6166 : row6166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6166 := by decide +kernel

theorem rowEval6166 (x : Key → ℝ) : Integer.Sparse.eval row6166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6166, Integer.Sparse.eval_collectBalanced, rawRowCheck6166]

def rawRow6167 : Integer.Sparse Key := [(key418, -1), (key406, -1), (key409, 2), (key450, -1), (key435, -1), (key475, 2), (key385, 2), (key467, -1), (key388, -1), (key442, 2), (key469, -1), (key397, -1), (key328, 1), (key316, 1), (key319, -2), (key450, 1), (key435, 1), (key601, -2), (key248, -2), (key593, 1), (key251, 1), (key442, -2), (key595, 1), (key260, 1), (key340, -1), (key302, -1), (key335, 1), (key305, 1), (key583, 1), (key236, 1), (key418, -1), (key239, -1), (key595, -1), (key316, -1), (key601, 1), (key248, 1), (key469, 1), (key335, 1), (key475, -1), (key267, -1)]

theorem rawRowCheck6167 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form6 = rawRow6167 := by decide +kernel

def row6167 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key260, 1), (key267, -1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 2), (key340, -1), (key385, 2), (key388, -1), (key397, -1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key583, 1), (key593, 1), (key601, -1)]

theorem rowCheck6167 : row6167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6167 := by decide +kernel

theorem rowEval6167 (x : Key → ℝ) : Integer.Sparse.eval row6167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6167, Integer.Sparse.eval_collectBalanced, rawRowCheck6167]

def rawRow6168 : Integer.Sparse Key := [(key409, -1), (key418, -1), (key406, 2), (key467, -1), (key475, -1), (key388, 2), (key450, 2), (key385, -1), (key435, -1), (key469, 2), (key397, -1), (key442, -1), (key319, 1), (key328, 1), (key316, -2), (key593, 1), (key601, 1), (key251, -2), (key450, -2), (key248, 1), (key435, 1), (key595, -2), (key260, 1), (key442, 1), (key305, -1), (key328, -1), (key302, 1), (key316, 1), (key239, 1), (key418, 1), (key236, -1), (key406, -1), (key328, -1), (key601, -1), (key260, 1), (key595, 1), (key340, 1), (key475, 1), (key271, -1), (key469, -1)]

theorem rawRowCheck6168 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form6 = rawRow6168 := by decide +kernel

def row6168 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, -1), (key340, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key593, 1), (key595, -1)]

theorem rowCheck6168 : row6168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6168 := by decide +kernel

theorem rowEval6168 (x : Key → ℝ) : Integer.Sparse.eval row6168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6168, Integer.Sparse.eval_collectBalanced, rawRowCheck6168]

def rawRow6169 : Integer.Sparse Key := [(key418, -1), (key409, -1), (key406, 2), (key475, -1), (key467, -1), (key450, 2), (key388, 2), (key435, -1), (key385, -1), (key469, 2), (key442, -1), (key397, -1), (key328, 1), (key319, 1), (key316, -2), (key601, 1), (key593, 1), (key450, -2), (key251, -2), (key435, 1), (key248, 1), (key595, -2), (key442, 1), (key260, 1), (key328, -1), (key305, -1), (key316, 1), (key302, 1), (key418, 1), (key239, 1), (key406, -1), (key236, -1), (key601, -1), (key328, -1), (key595, 1), (key260, 1), (key475, 1), (key340, 1), (key469, -1), (key271, -1)]

theorem rawRowCheck6169 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form6 = rawRow6169 := by decide +kernel

def row6169 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, -1), (key340, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key593, 1), (key595, -1)]

theorem rowCheck6169 : row6169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6169 := by decide +kernel

theorem rowEval6169 (x : Key → ℝ) : Integer.Sparse.eval row6169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6169, Integer.Sparse.eval_collectBalanced, rawRowCheck6169]

def rawRow6170 : Integer.Sparse Key := [(key435, -1), (key442, -1), (key450, 2), (key385, -1), (key397, -1), (key406, 2), (key469, 2), (key418, -1), (key475, -1), (key388, 2), (key409, -1), (key467, -1), (key435, 1), (key442, 1), (key450, -2), (key248, 1), (key260, 1), (key316, -2), (key595, -2), (key328, 1), (key601, 1), (key251, -2), (key319, 1), (key593, 1), (key406, -1), (key469, -1), (key418, 1), (key475, 1), (key316, 1), (key595, 1), (key328, -1), (key601, -1), (key236, -1), (key271, -1), (key302, 1), (key340, 1), (key239, 1), (key260, 1), (key305, -1), (key328, -1)]

theorem rawRowCheck6170 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form6 = rawRow6170 := by decide +kernel

def row6170 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, -1), (key340, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key593, 1), (key595, -1)]

theorem rowCheck6170 : row6170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6170 := by decide +kernel

theorem rowEval6170 (x : Key → ℝ) : Integer.Sparse.eval row6170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6170, Integer.Sparse.eval_collectBalanced, rawRowCheck6170]

def rawRow6171 : Integer.Sparse Key := [(key442, -1), (key435, -1), (key450, 2), (key397, -1), (key385, -1), (key469, 2), (key406, 2), (key475, -1), (key418, -1), (key388, 2), (key467, -1), (key409, -1), (key442, 1), (key435, 1), (key450, -2), (key260, 1), (key248, 1), (key595, -2), (key316, -2), (key601, 1), (key328, 1), (key251, -2), (key593, 1), (key319, 1), (key469, -1), (key406, -1), (key475, 1), (key418, 1), (key595, 1), (key316, 1), (key601, -1), (key328, -1), (key271, -1), (key236, -1), (key340, 1), (key302, 1), (key260, 1), (key239, 1), (key328, -1), (key305, -1)]

theorem rawRowCheck6171 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form6 = rawRow6171 := by decide +kernel

def row6171 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, -1), (key340, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key593, 1), (key595, -1)]

theorem rowCheck6171 : row6171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6171 := by decide +kernel

theorem rowEval6171 (x : Key → ℝ) : Integer.Sparse.eval row6171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6171, Integer.Sparse.eval_collectBalanced, rawRowCheck6171]

def rawRow6172 : Integer.Sparse Key := [(key435, -1), (key450, -1), (key442, 2), (key406, -1), (key418, -1), (key385, 2), (key475, 2), (key397, -1), (key469, -1), (key409, 2), (key388, -1), (key467, -1), (key435, 1), (key450, 1), (key442, -2), (key316, 1), (key328, 1), (key248, -2), (key601, -2), (key260, 1), (key595, 1), (key319, -2), (key251, 1), (key593, 1), (key385, -1), (key475, -1), (key397, 1), (key469, 1), (key248, 1), (key601, 1), (key260, -1), (key595, -1), (key302, -1), (key340, -1), (key236, 1), (key583, 1), (key305, 1), (key397, 1), (key239, -1), (key418, -1)]

theorem rawRowCheck6172 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form6 = rawRow6172 := by decide +kernel

def row6172 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 1), (key319, -2), (key328, 1), (key340, -1), (key385, 1), (key388, -1), (key397, 1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key583, 1), (key593, 1), (key601, -1)]

theorem rowCheck6172 : row6172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6172 := by decide +kernel

theorem rowEval6172 (x : Key → ℝ) : Integer.Sparse.eval row6172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6172, Integer.Sparse.eval_collectBalanced, rawRowCheck6172]

def rawRow6173 : Integer.Sparse Key := [(key450, -1), (key435, -1), (key442, 2), (key418, -1), (key406, -1), (key475, 2), (key385, 2), (key469, -1), (key397, -1), (key409, 2), (key467, -1), (key388, -1), (key450, 1), (key435, 1), (key442, -2), (key328, 1), (key316, 1), (key601, -2), (key248, -2), (key595, 1), (key260, 1), (key319, -2), (key593, 1), (key251, 1), (key475, -1), (key385, -1), (key469, 1), (key397, 1), (key601, 1), (key248, 1), (key595, -1), (key260, -1), (key340, -1), (key302, -1), (key583, 1), (key236, 1), (key397, 1), (key305, 1), (key418, -1), (key239, -1)]

theorem rawRowCheck6173 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form6 = rawRow6173 := by decide +kernel

def row6173 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 1), (key319, -2), (key328, 1), (key340, -1), (key385, 1), (key388, -1), (key397, 1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key583, 1), (key593, 1), (key601, -1)]

theorem rowCheck6173 : row6173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6173 := by decide +kernel

theorem rowEval6173 (x : Key → ℝ) : Integer.Sparse.eval row6173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6173, Integer.Sparse.eval_collectBalanced, rawRowCheck6173]

def rawRow6174 : Integer.Sparse Key := [(key467, -1), (key469, -1), (key475, 2), (key388, -1), (key397, -1), (key409, 2), (key442, 2), (key418, -1), (key450, -1), (key385, 2), (key406, -1), (key435, -1), (key593, 1), (key595, 1), (key601, -2), (key251, 1), (key260, 1), (key319, -2), (key442, -2), (key328, 1), (key450, 1), (key248, -2), (key316, 1), (key435, 1), (key578, -1), (key595, -1), (key583, 1), (key601, 1), (key335, 1), (key469, 1), (key340, -1), (key475, -1), (key239, -1), (key260, -1), (key305, 1), (key397, 1), (key236, 1), (key248, 1), (key302, -1), (key316, -1)]

theorem rawRowCheck6174 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form6 = rawRow6174 := by decide +kernel

def row6174 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 1), (key340, -1), (key385, 2), (key388, -1), (key406, -1), (key409, 2), (key418, -1), (key467, -1), (key475, 1), (key578, -1), (key583, 1), (key593, 1), (key601, -1)]

theorem rowCheck6174 : row6174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6174 := by decide +kernel

theorem rowEval6174 (x : Key → ℝ) : Integer.Sparse.eval row6174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6174, Integer.Sparse.eval_collectBalanced, rawRowCheck6174]

def rawRow6175 : Integer.Sparse Key := [(key469, -1), (key467, -1), (key475, 2), (key397, -1), (key388, -1), (key442, 2), (key409, 2), (key450, -1), (key418, -1), (key385, 2), (key435, -1), (key406, -1), (key595, 1), (key593, 1), (key601, -2), (key260, 1), (key251, 1), (key442, -2), (key319, -2), (key450, 1), (key328, 1), (key248, -2), (key435, 1), (key316, 1), (key595, -1), (key578, -1), (key601, 1), (key583, 1), (key469, 1), (key335, 1), (key475, -1), (key340, -1), (key260, -1), (key239, -1), (key397, 1), (key305, 1), (key248, 1), (key236, 1), (key316, -1), (key302, -1)]

theorem rawRowCheck6175 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form6 = rawRow6175 := by decide +kernel

def row6175 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 1), (key340, -1), (key385, 2), (key388, -1), (key406, -1), (key409, 2), (key418, -1), (key467, -1), (key475, 1), (key578, -1), (key583, 1), (key593, 1), (key601, -1)]

theorem rowCheck6175 : row6175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6175 := by decide +kernel

theorem rowEval6175 (x : Key → ℝ) : Integer.Sparse.eval row6175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6175, Integer.Sparse.eval_collectBalanced, rawRowCheck6175]

def rawRow6176 : Integer.Sparse Key := [(key467, -1), (key475, -1), (key469, 2), (key409, -1), (key418, -1), (key388, 2), (key450, 2), (key397, -1), (key442, -1), (key406, 2), (key385, -1), (key435, -1), (key593, 1), (key601, 1), (key595, -2), (key319, 1), (key328, 1), (key251, -2), (key450, -2), (key260, 1), (key442, 1), (key316, -2), (key248, 1), (key435, 1), (key568, -1), (key601, -1), (key572, 1), (key595, 1), (key267, 1), (key475, 1), (key271, -1), (key469, -1), (key305, -1), (key328, -1), (key239, 1), (key418, 1), (key302, 1), (key316, 1), (key236, -1), (key406, -1)]

theorem rawRowCheck6176 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form6 = rawRow6176 := by decide +kernel

def row6176 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key568, -1), (key572, 1), (key593, 1), (key595, -1)]

theorem rowCheck6176 : row6176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6176 := by decide +kernel

theorem rowEval6176 (x : Key → ℝ) : Integer.Sparse.eval row6176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6176, Integer.Sparse.eval_collectBalanced, rawRowCheck6176]

def rawRow6177 : Integer.Sparse Key := [(key475, -1), (key467, -1), (key469, 2), (key418, -1), (key409, -1), (key450, 2), (key388, 2), (key442, -1), (key397, -1), (key406, 2), (key435, -1), (key385, -1), (key601, 1), (key593, 1), (key595, -2), (key328, 1), (key319, 1), (key450, -2), (key251, -2), (key442, 1), (key260, 1), (key316, -2), (key435, 1), (key248, 1), (key601, -1), (key568, -1), (key595, 1), (key572, 1), (key475, 1), (key267, 1), (key469, -1), (key271, -1), (key328, -1), (key305, -1), (key418, 1), (key239, 1), (key316, 1), (key302, 1), (key406, -1), (key236, -1)]

theorem rawRowCheck6177 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form6 = rawRow6177 := by decide +kernel

def row6177 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key568, -1), (key572, 1), (key593, 1), (key595, -1)]

theorem rowCheck6177 : row6177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6177 := by decide +kernel

theorem rowEval6177 (x : Key → ℝ) : Integer.Sparse.eval row6177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6177, Integer.Sparse.eval_collectBalanced, rawRowCheck6177]

def rawRow6178 : Integer.Sparse Key := [(key2778, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2851, 2), (key2918, 2), (key2858, -1), (key2919, -1), (key2827, 2), (key2868, -1), (key2922, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2698, 1), (key2704, 1), (key2851, -2), (key3021, -2), (key2858, 1), (key3022, 1), (key2724, -2), (key2868, 1), (key3025, 1), (key2624, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2698, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, -1), (key2792, -1), (key2801, 1), (key2827, 1), (key3007, 1), (key3009, 1), (key3011, -1), (key3016, -1)]

theorem rawRowCheck6178 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form0 = rawRow6178 := by decide +kernel

def row6178 : Integer.Sparse Key := [(key2630, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2698, 2), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -2), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 3), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, 1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6178 : row6178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6178 := by decide +kernel

theorem rowEval6178 (x : Key → ℝ) : Integer.Sparse.eval row6178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6178, Integer.Sparse.eval_collectBalanced, rawRowCheck6178]

def rawRow6179 : Integer.Sparse Key := [(key2784, -1), (key2778, -1), (key2792, 2), (key2807, -1), (key2801, -1), (key2918, 2), (key2851, 2), (key2919, -1), (key2858, -1), (key2827, 2), (key2922, -1), (key2868, -1), (key2630, 1), (key2624, 1), (key2638, -2), (key2704, 1), (key2698, 1), (key3021, -2), (key2851, -2), (key3022, 1), (key2858, 1), (key2724, -2), (key3025, 1), (key2868, 1), (key2638, -1), (key2624, -1), (key2659, 1), (key2657, 1), (key2724, 1), (key2698, 1), (key2757, -1), (key2752, -1), (key2792, -1), (key2778, -1), (key2827, 1), (key2801, 1), (key3009, 1), (key3007, 1), (key3016, -1), (key3011, -1)]

theorem rawRowCheck6179 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form0 = rawRow6179 := by decide +kernel

def row6179 : Integer.Sparse Key := [(key2630, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2698, 2), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -2), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 3), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, 1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6179 : row6179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6179 := by decide +kernel

theorem rowEval6179 (x : Key → ℝ) : Integer.Sparse.eval row6179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6179, Integer.Sparse.eval_collectBalanced, rawRowCheck6179]

def rawRow6180 : Integer.Sparse Key := [(key2801, -1), (key2807, -1), (key2827, 2), (key2778, -1), (key2784, -1), (key2851, 2), (key2918, 2), (key2868, -1), (key2922, -1), (key2792, 2), (key2858, -1), (key2919, -1), (key2698, 1), (key2704, 1), (key2724, -2), (key2624, 1), (key2630, 1), (key2851, -2), (key3021, -2), (key2868, 1), (key3025, 1), (key2638, -2), (key2858, 1), (key3022, 1), (key2698, -1), (key2752, -1), (key2724, 1), (key2757, 1), (key2801, 1), (key2827, 1), (key3011, -1), (key3016, -1), (key2624, -1), (key2638, -1), (key2698, 1), (key2724, 1), (key2657, 1), (key2659, 1), (key2752, -1), (key2757, -1)]

theorem rawRowCheck6180 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form0 = rawRow6180 := by decide +kernel

def row6180 : Integer.Sparse Key := [(key2630, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2698, 1), (key2704, 1), (key2752, -2), (key2778, -1), (key2784, -1), (key2792, 2), (key2807, -1), (key2827, 3), (key2918, 2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6180 : row6180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6180 := by decide +kernel

theorem rowEval6180 (x : Key → ℝ) : Integer.Sparse.eval row6180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6180, Integer.Sparse.eval_collectBalanced, rawRowCheck6180]

def rawRow6181 : Integer.Sparse Key := [(key2807, -1), (key2801, -1), (key2827, 2), (key2784, -1), (key2778, -1), (key2918, 2), (key2851, 2), (key2922, -1), (key2868, -1), (key2792, 2), (key2919, -1), (key2858, -1), (key2704, 1), (key2698, 1), (key2724, -2), (key2630, 1), (key2624, 1), (key3021, -2), (key2851, -2), (key3025, 1), (key2868, 1), (key2638, -2), (key3022, 1), (key2858, 1), (key2752, -1), (key2698, -1), (key2757, 1), (key2724, 1), (key2827, 1), (key2801, 1), (key3016, -1), (key3011, -1), (key2638, -1), (key2624, -1), (key2724, 1), (key2698, 1), (key2659, 1), (key2657, 1), (key2757, -1), (key2752, -1)]

theorem rawRowCheck6181 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form0 = rawRow6181 := by decide +kernel

def row6181 : Integer.Sparse Key := [(key2630, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2698, 1), (key2704, 1), (key2752, -2), (key2778, -1), (key2784, -1), (key2792, 2), (key2807, -1), (key2827, 3), (key2918, 2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6181 : row6181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6181 := by decide +kernel

theorem rowEval6181 (x : Key → ℝ) : Integer.Sparse.eval row6181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6181, Integer.Sparse.eval_collectBalanced, rawRowCheck6181]

def rawRow6182 : Integer.Sparse Key := [(key2858, -1), (key2868, -1), (key2851, 2), (key2919, -1), (key2922, -1), (key2792, 2), (key2827, 2), (key2778, -1), (key2801, -1), (key2918, 2), (key2784, -1), (key2807, -1), (key2858, 1), (key2868, 1), (key2851, -2), (key3022, 1), (key3025, 1), (key2638, -2), (key2724, -2), (key2624, 1), (key2698, 1), (key3021, -2), (key2630, 1), (key2704, 1), (key2792, -1), (key2827, -1), (key2778, 1), (key2801, 1), (key2638, 1), (key2724, 1), (key2624, -1), (key2698, -1), (key3009, -1), (key3016, -1), (key2659, 1), (key2757, 1), (key2724, 1), (key2827, 1), (key2638, -1), (key2792, -1)]

theorem rawRowCheck6182 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form0 = rawRow6182 := by decide +kernel

def row6182 : Integer.Sparse Key := [(key2630, 1), (key2638, -2), (key2659, 1), (key2704, 1), (key2757, 1), (key2784, -1), (key2807, -1), (key2827, 2), (key2918, 2), (key2919, -1), (key2922, -1), (key3009, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6182 : row6182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6182 := by decide +kernel

theorem rowEval6182 (x : Key → ℝ) : Integer.Sparse.eval row6182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6182, Integer.Sparse.eval_collectBalanced, rawRowCheck6182]

def rawRow6183 : Integer.Sparse Key := [(key2868, -1), (key2858, -1), (key2851, 2), (key2922, -1), (key2919, -1), (key2827, 2), (key2792, 2), (key2801, -1), (key2778, -1), (key2918, 2), (key2807, -1), (key2784, -1), (key2868, 1), (key2858, 1), (key2851, -2), (key3025, 1), (key3022, 1), (key2724, -2), (key2638, -2), (key2698, 1), (key2624, 1), (key3021, -2), (key2704, 1), (key2630, 1), (key2827, -1), (key2792, -1), (key2801, 1), (key2778, 1), (key2724, 1), (key2638, 1), (key2698, -1), (key2624, -1), (key3016, -1), (key3009, -1), (key2757, 1), (key2659, 1), (key2827, 1), (key2724, 1), (key2792, -1), (key2638, -1)]

theorem rawRowCheck6183 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form0 = rawRow6183 := by decide +kernel

def row6183 : Integer.Sparse Key := [(key2630, 1), (key2638, -2), (key2659, 1), (key2704, 1), (key2757, 1), (key2784, -1), (key2807, -1), (key2827, 2), (key2918, 2), (key2919, -1), (key2922, -1), (key3009, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6183 : row6183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6183 := by decide +kernel

theorem rowEval6183 (x : Key → ℝ) : Integer.Sparse.eval row6183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6183, Integer.Sparse.eval_collectBalanced, rawRowCheck6183]

def rawRow6184 : Integer.Sparse Key := [(key2919, -1), (key2922, -1), (key2918, 2), (key2858, -1), (key2868, -1), (key2792, 2), (key2827, 2), (key2784, -1), (key2807, -1), (key2851, 2), (key2778, -1), (key2801, -1), (key3022, 1), (key3025, 1), (key3021, -2), (key2858, 1), (key2868, 1), (key2638, -2), (key2724, -2), (key2630, 1), (key2704, 1), (key2851, -2), (key2624, 1), (key2698, 1), (key3009, -1), (key3016, -1), (key3007, 1), (key3011, 1), (key2659, 1), (key2757, 1), (key2657, -1), (key2752, -1), (key2792, -1), (key2827, -1), (key2638, 1), (key2724, 1), (key2778, 1), (key2801, 1), (key2624, -1), (key2698, -1)]

theorem rawRowCheck6184 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form0 = rawRow6184 := by decide +kernel

def row6184 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6184 : row6184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6184 := by decide +kernel

theorem rowEval6184 (x : Key → ℝ) : Integer.Sparse.eval row6184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6184, Integer.Sparse.eval_collectBalanced, rawRowCheck6184]

def rawRow6185 : Integer.Sparse Key := [(key2922, -1), (key2919, -1), (key2918, 2), (key2868, -1), (key2858, -1), (key2827, 2), (key2792, 2), (key2807, -1), (key2784, -1), (key2851, 2), (key2801, -1), (key2778, -1), (key3025, 1), (key3022, 1), (key3021, -2), (key2868, 1), (key2858, 1), (key2724, -2), (key2638, -2), (key2704, 1), (key2630, 1), (key2851, -2), (key2698, 1), (key2624, 1), (key3016, -1), (key3009, -1), (key3011, 1), (key3007, 1), (key2757, 1), (key2659, 1), (key2752, -1), (key2657, -1), (key2827, -1), (key2792, -1), (key2724, 1), (key2638, 1), (key2801, 1), (key2778, 1), (key2698, -1), (key2624, -1)]

theorem rawRowCheck6185 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form0 = rawRow6185 := by decide +kernel

def row6185 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6185 : row6185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6185 := by decide +kernel

theorem rowEval6185 (x : Key → ℝ) : Integer.Sparse.eval row6185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6185, Integer.Sparse.eval_collectBalanced, rawRowCheck6185]

def rawRow6186 : Integer.Sparse Key := [(key3007, -1), (key3007, -1), (key3009, 2), (key3011, -1), (key3011, -1), (key3021, 2), (key3021, 2), (key3022, -1), (key3022, -1), (key3016, 2), (key3025, -1), (key3025, -1), (key2657, 1), (key2657, 1), (key2659, -2), (key2752, 1), (key2752, 1), (key2918, -2), (key2918, -2), (key2919, 1), (key2919, 1), (key2757, -2), (key2922, 1), (key2922, 1), (key2630, -1), (key2630, -1), (key2638, 1), (key2638, 1), (key2784, 1), (key2784, 1), (key2792, -1), (key2792, -1), (key2704, -1), (key2704, -1), (key2807, 1), (key2807, 1), (key2724, 1), (key2724, 1), (key2827, -1), (key2827, -1)]

theorem rawRowCheck6186 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form0 = rawRow6186 := by decide +kernel

def row6186 : Integer.Sparse Key := [(key2630, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2704, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, -2), (key2807, 2), (key2827, -2), (key2918, -4), (key2919, 2), (key2922, 2), (key3007, -2), (key3009, 2), (key3011, -2), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

theorem rowCheck6186 : row6186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6186 := by decide +kernel

theorem rowEval6186 (x : Key → ℝ) : Integer.Sparse.eval row6186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6186, Integer.Sparse.eval_collectBalanced, rawRowCheck6186]

def rawRow6187 : Integer.Sparse Key := [(key3007, -1), (key3009, -1), (key3007, 2), (key3021, -1), (key3022, -1), (key3011, 2), (key3022, 2), (key3011, -1), (key3021, -1), (key3025, 2), (key3016, -1), (key3025, -1), (key2657, 1), (key2659, 1), (key2657, -2), (key2918, 1), (key2919, 1), (key2752, -2), (key2919, -2), (key2752, 1), (key2918, 1), (key2922, -2), (key2757, 1), (key2922, 1), (key2614, -1), (key2638, -1), (key2614, 1), (key2630, 1), (key2669, 1), (key2792, 1), (key2669, -1), (key2784, -1), (key2807, -1), (key2858, -1), (key2704, 1), (key2858, 1), (key2827, 1), (key2868, 1), (key2724, -1), (key2868, -1)]

theorem rawRowCheck6187 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form0 = rawRow6187 := by decide +kernel

def row6187 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6187 : row6187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6187 := by decide +kernel

theorem rowEval6187 (x : Key → ℝ) : Integer.Sparse.eval row6187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6187, Integer.Sparse.eval_collectBalanced, rawRowCheck6187]

def rawRow6188 : Integer.Sparse Key := [(key3009, -1), (key3007, -1), (key3007, 2), (key3022, -1), (key3021, -1), (key3022, 2), (key3011, 2), (key3021, -1), (key3011, -1), (key3025, 2), (key3025, -1), (key3016, -1), (key2659, 1), (key2657, 1), (key2657, -2), (key2919, 1), (key2918, 1), (key2919, -2), (key2752, -2), (key2918, 1), (key2752, 1), (key2922, -2), (key2922, 1), (key2757, 1), (key2638, -1), (key2614, -1), (key2630, 1), (key2614, 1), (key2792, 1), (key2669, 1), (key2784, -1), (key2669, -1), (key2858, -1), (key2807, -1), (key2858, 1), (key2704, 1), (key2868, 1), (key2827, 1), (key2868, -1), (key2724, -1)]

theorem rawRowCheck6188 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form0 = rawRow6188 := by decide +kernel

def row6188 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6188 : row6188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6188 := by decide +kernel

theorem rowEval6188 (x : Key → ℝ) : Integer.Sparse.eval row6188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6188, Integer.Sparse.eval_collectBalanced, rawRowCheck6188]

def rawRow6189 : Integer.Sparse Key := [(key3011, -1), (key3011, -1), (key3016, 2), (key3007, -1), (key3007, -1), (key3021, 2), (key3021, 2), (key3025, -1), (key3025, -1), (key3009, 2), (key3022, -1), (key3022, -1), (key2752, 1), (key2752, 1), (key2757, -2), (key2657, 1), (key2657, 1), (key2918, -2), (key2918, -2), (key2922, 1), (key2922, 1), (key2659, -2), (key2919, 1), (key2919, 1), (key2704, -1), (key2704, -1), (key2724, 1), (key2724, 1), (key2807, 1), (key2807, 1), (key2827, -1), (key2827, -1), (key2630, -1), (key2630, -1), (key2784, 1), (key2784, 1), (key2638, 1), (key2638, 1), (key2792, -1), (key2792, -1)]

theorem rawRowCheck6189 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form0 = rawRow6189 := by decide +kernel

def row6189 : Integer.Sparse Key := [(key2630, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2704, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, -2), (key2807, 2), (key2827, -2), (key2918, -4), (key2919, 2), (key2922, 2), (key3007, -2), (key3009, 2), (key3011, -2), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

theorem rowCheck6189 : row6189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6189 := by decide +kernel

theorem rowEval6189 (x : Key → ℝ) : Integer.Sparse.eval row6189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6189, Integer.Sparse.eval_collectBalanced, rawRowCheck6189]

def rawRow6190 : Integer.Sparse Key := [(key3011, -1), (key3016, -1), (key3011, 2), (key3021, -1), (key3025, -1), (key3007, 2), (key3025, 2), (key3007, -1), (key3021, -1), (key3022, 2), (key3009, -1), (key3022, -1), (key2752, 1), (key2757, 1), (key2752, -2), (key2918, 1), (key2922, 1), (key2657, -2), (key2922, -2), (key2657, 1), (key2918, 1), (key2919, -2), (key2659, 1), (key2919, 1), (key2669, -1), (key2724, -1), (key2669, 1), (key2704, 1), (key2614, 1), (key2827, 1), (key2614, -1), (key2807, -1), (key2784, -1), (key2868, -1), (key2630, 1), (key2868, 1), (key2792, 1), (key2858, 1), (key2638, -1), (key2858, -1)]

theorem rawRowCheck6190 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form0 = rawRow6190 := by decide +kernel

def row6190 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6190 : row6190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6190 := by decide +kernel

theorem rowEval6190 (x : Key → ℝ) : Integer.Sparse.eval row6190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6190, Integer.Sparse.eval_collectBalanced, rawRowCheck6190]

def rawRow6191 : Integer.Sparse Key := [(key3016, -1), (key3011, -1), (key3011, 2), (key3025, -1), (key3021, -1), (key3025, 2), (key3007, 2), (key3021, -1), (key3007, -1), (key3022, 2), (key3022, -1), (key3009, -1), (key2757, 1), (key2752, 1), (key2752, -2), (key2922, 1), (key2918, 1), (key2922, -2), (key2657, -2), (key2918, 1), (key2657, 1), (key2919, -2), (key2919, 1), (key2659, 1), (key2724, -1), (key2669, -1), (key2704, 1), (key2669, 1), (key2827, 1), (key2614, 1), (key2807, -1), (key2614, -1), (key2868, -1), (key2784, -1), (key2868, 1), (key2630, 1), (key2858, 1), (key2792, 1), (key2858, -1), (key2638, -1)]

theorem rawRowCheck6191 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form0 = rawRow6191 := by decide +kernel

def row6191 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6191 : row6191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6191 := by decide +kernel

theorem rowEval6191 (x : Key → ℝ) : Integer.Sparse.eval row6191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6191, Integer.Sparse.eval_collectBalanced, rawRowCheck6191]

def rawRow6192 : Integer.Sparse Key := [(key3021, -1), (key3022, -1), (key3025, 2), (key3007, -1), (key3009, -1), (key3011, 2), (key3022, 2), (key3016, -1), (key3025, -1), (key3007, 2), (key3011, -1), (key3021, -1), (key2918, 1), (key2919, 1), (key2922, -2), (key2657, 1), (key2659, 1), (key2752, -2), (key2919, -2), (key2757, 1), (key2922, 1), (key2657, -2), (key2752, 1), (key2918, 1), (key2807, -1), (key2858, -1), (key2827, 1), (key2868, 1), (key2704, 1), (key2858, 1), (key2724, -1), (key2868, -1), (key2614, -1), (key2638, -1), (key2669, 1), (key2792, 1), (key2614, 1), (key2630, 1), (key2669, -1), (key2784, -1)]

theorem rawRowCheck6192 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form0 = rawRow6192 := by decide +kernel

def row6192 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6192 : row6192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6192 := by decide +kernel

theorem rowEval6192 (x : Key → ℝ) : Integer.Sparse.eval row6192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6192, Integer.Sparse.eval_collectBalanced, rawRowCheck6192]

def rawRow6193 : Integer.Sparse Key := [(key3022, -1), (key3021, -1), (key3025, 2), (key3009, -1), (key3007, -1), (key3022, 2), (key3011, 2), (key3025, -1), (key3016, -1), (key3007, 2), (key3021, -1), (key3011, -1), (key2919, 1), (key2918, 1), (key2922, -2), (key2659, 1), (key2657, 1), (key2919, -2), (key2752, -2), (key2922, 1), (key2757, 1), (key2657, -2), (key2918, 1), (key2752, 1), (key2858, -1), (key2807, -1), (key2868, 1), (key2827, 1), (key2858, 1), (key2704, 1), (key2868, -1), (key2724, -1), (key2638, -1), (key2614, -1), (key2792, 1), (key2669, 1), (key2630, 1), (key2614, 1), (key2784, -1), (key2669, -1)]

theorem rawRowCheck6193 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form0 = rawRow6193 := by decide +kernel

def row6193 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6193 : row6193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6193 := by decide +kernel

theorem rowEval6193 (x : Key → ℝ) : Integer.Sparse.eval row6193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6193, Integer.Sparse.eval_collectBalanced, rawRowCheck6193]

def rawRow6194 : Integer.Sparse Key := [(key3021, -1), (key3025, -1), (key3022, 2), (key3011, -1), (key3016, -1), (key3007, 2), (key3025, 2), (key3009, -1), (key3022, -1), (key3011, 2), (key3007, -1), (key3021, -1), (key2918, 1), (key2922, 1), (key2919, -2), (key2752, 1), (key2757, 1), (key2657, -2), (key2922, -2), (key2659, 1), (key2919, 1), (key2752, -2), (key2657, 1), (key2918, 1), (key2784, -1), (key2868, -1), (key2792, 1), (key2858, 1), (key2630, 1), (key2868, 1), (key2638, -1), (key2858, -1), (key2669, -1), (key2724, -1), (key2614, 1), (key2827, 1), (key2669, 1), (key2704, 1), (key2614, -1), (key2807, -1)]

theorem rawRowCheck6194 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form0 = rawRow6194 := by decide +kernel

def row6194 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6194 : row6194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6194 := by decide +kernel

theorem rowEval6194 (x : Key → ℝ) : Integer.Sparse.eval row6194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6194, Integer.Sparse.eval_collectBalanced, rawRowCheck6194]

def rawRow6195 : Integer.Sparse Key := [(key3025, -1), (key3021, -1), (key3022, 2), (key3016, -1), (key3011, -1), (key3025, 2), (key3007, 2), (key3022, -1), (key3009, -1), (key3011, 2), (key3021, -1), (key3007, -1), (key2922, 1), (key2918, 1), (key2919, -2), (key2757, 1), (key2752, 1), (key2922, -2), (key2657, -2), (key2919, 1), (key2659, 1), (key2752, -2), (key2918, 1), (key2657, 1), (key2868, -1), (key2784, -1), (key2858, 1), (key2792, 1), (key2868, 1), (key2630, 1), (key2858, -1), (key2638, -1), (key2724, -1), (key2669, -1), (key2827, 1), (key2614, 1), (key2704, 1), (key2669, 1), (key2807, -1), (key2614, -1)]

theorem rawRowCheck6195 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form0 = rawRow6195 := by decide +kernel

def row6195 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

theorem rowCheck6195 : row6195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6195 := by decide +kernel

theorem rowEval6195 (x : Key → ℝ) : Integer.Sparse.eval row6195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6195, Integer.Sparse.eval_collectBalanced, rawRowCheck6195]

def rawRow6196 : Integer.Sparse Key := [(key3022, -1), (key3025, -1), (key3021, 2), (key3022, -1), (key3025, -1), (key3009, 2), (key3016, 2), (key3007, -1), (key3011, -1), (key3021, 2), (key3007, -1), (key3011, -1), (key2919, 1), (key2922, 1), (key2918, -2), (key2919, 1), (key2922, 1), (key2659, -2), (key2757, -2), (key2657, 1), (key2752, 1), (key2918, -2), (key2657, 1), (key2752, 1), (key2792, -1), (key2827, -1), (key2784, 1), (key2807, 1), (key2638, 1), (key2724, 1), (key2630, -1), (key2704, -1), (key2792, -1), (key2827, -1), (key2638, 1), (key2724, 1), (key2784, 1), (key2807, 1), (key2630, -1), (key2704, -1)]

theorem rawRowCheck6196 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form0 = rawRow6196 := by decide +kernel

def row6196 : Integer.Sparse Key := [(key2630, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2704, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, -2), (key2807, 2), (key2827, -2), (key2918, -4), (key2919, 2), (key2922, 2), (key3007, -2), (key3009, 2), (key3011, -2), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

theorem rowCheck6196 : row6196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6196 := by decide +kernel

theorem rowEval6196 (x : Key → ℝ) : Integer.Sparse.eval row6196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6196, Integer.Sparse.eval_collectBalanced, rawRowCheck6196]

def rawRow6197 : Integer.Sparse Key := [(key3025, -1), (key3022, -1), (key3021, 2), (key3025, -1), (key3022, -1), (key3016, 2), (key3009, 2), (key3011, -1), (key3007, -1), (key3021, 2), (key3011, -1), (key3007, -1), (key2922, 1), (key2919, 1), (key2918, -2), (key2922, 1), (key2919, 1), (key2757, -2), (key2659, -2), (key2752, 1), (key2657, 1), (key2918, -2), (key2752, 1), (key2657, 1), (key2827, -1), (key2792, -1), (key2807, 1), (key2784, 1), (key2724, 1), (key2638, 1), (key2704, -1), (key2630, -1), (key2827, -1), (key2792, -1), (key2724, 1), (key2638, 1), (key2807, 1), (key2784, 1), (key2704, -1), (key2630, -1)]

theorem rawRowCheck6197 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form0 = rawRow6197 := by decide +kernel

def row6197 : Integer.Sparse Key := [(key2630, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2704, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, -2), (key2807, 2), (key2827, -2), (key2918, -4), (key2919, 2), (key2922, 2), (key3007, -2), (key3009, 2), (key3011, -2), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

theorem rowCheck6197 : row6197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6197 := by decide +kernel

theorem rowEval6197 (x : Key → ℝ) : Integer.Sparse.eval row6197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6197, Integer.Sparse.eval_collectBalanced, rawRowCheck6197]

def rawRow6198 : Integer.Sparse Key := [(key1386, -1), (key1394, -1), (key1394, 2), (key1419, -1), (key1427, -1), (key1419, 2), (key1473, 2), (key1427, -1), (key1473, -1), (key1445, 2), (key1445, -1), (key1481, -1), (key1291, 1), (key1299, 1), (key1299, -2), (key1568, 1), (key1576, 1), (key1568, -2), (key1904, -2), (key1576, 1), (key1904, 1), (key1594, -2), (key1594, 1), (key1912, 1), (key1311, -1), (key1352, -1), (key1319, 1), (key1352, 1), (key1541, 1), (key1897, 1), (key1549, -1), (key1897, -1), (key1617, -1), (key1682, -1), (key1617, 1), (key1919, 1), (key1634, 1), (key1690, 1), (key1634, -1), (key1927, -1)]

theorem rawRowCheck6198 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form1 = rawRow6198 := by decide +kernel

def row6198 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6198 : row6198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6198 := by decide +kernel

theorem rowEval6198 (x : Key → ℝ) : Integer.Sparse.eval row6198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6198, Integer.Sparse.eval_collectBalanced, rawRowCheck6198]

def rawRow6199 : Integer.Sparse Key := [(key1394, -1), (key1386, -1), (key1394, 2), (key1427, -1), (key1419, -1), (key1473, 2), (key1419, 2), (key1473, -1), (key1427, -1), (key1445, 2), (key1481, -1), (key1445, -1), (key1299, 1), (key1291, 1), (key1299, -2), (key1576, 1), (key1568, 1), (key1904, -2), (key1568, -2), (key1904, 1), (key1576, 1), (key1594, -2), (key1912, 1), (key1594, 1), (key1352, -1), (key1311, -1), (key1352, 1), (key1319, 1), (key1897, 1), (key1541, 1), (key1897, -1), (key1549, -1), (key1682, -1), (key1617, -1), (key1919, 1), (key1617, 1), (key1690, 1), (key1634, 1), (key1927, -1), (key1634, -1)]

theorem rawRowCheck6199 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form1 = rawRow6199 := by decide +kernel

def row6199 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6199 : row6199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6199 := by decide +kernel

theorem rowEval6199 (x : Key → ℝ) : Integer.Sparse.eval row6199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6199, Integer.Sparse.eval_collectBalanced, rawRowCheck6199]

def rawRow6200 : Integer.Sparse Key := [(key1394, -1), (key1394, -1), (key1386, 2), (key1473, -1), (key1473, -1), (key1427, 2), (key1427, 2), (key1419, -1), (key1419, -1), (key1481, 2), (key1445, -1), (key1445, -1), (key1299, 1), (key1299, 1), (key1291, -2), (key1904, 1), (key1904, 1), (key1576, -2), (key1576, -2), (key1568, 1), (key1568, 1), (key1912, -2), (key1594, 1), (key1594, 1), (key1319, -1), (key1319, -1), (key1311, 1), (key1311, 1), (key1549, 1), (key1549, 1), (key1541, -1), (key1541, -1), (key1919, -1), (key1919, -1), (key1682, 1), (key1682, 1), (key1927, 1), (key1927, 1), (key1690, -1), (key1690, -1)]

theorem rawRowCheck6200 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form1 = rawRow6200 := by decide +kernel

def row6200 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 4), (key1445, -2), (key1473, -2), (key1481, 2), (key1541, -2), (key1549, 2), (key1568, 2), (key1576, -4), (key1594, 2), (key1682, 2), (key1690, -2), (key1904, 2), (key1912, -2), (key1919, -2), (key1927, 2)]

theorem rowCheck6200 : row6200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6200 := by decide +kernel

theorem rowEval6200 (x : Key → ℝ) : Integer.Sparse.eval row6200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6200, Integer.Sparse.eval_collectBalanced, rawRowCheck6200]

def rawRow6201 : Integer.Sparse Key := [(key1419, -1), (key1427, -1), (key1445, 2), (key1386, -1), (key1394, -1), (key1419, 2), (key1473, 2), (key1445, -1), (key1481, -1), (key1394, 2), (key1427, -1), (key1473, -1), (key1568, 1), (key1576, 1), (key1594, -2), (key1291, 1), (key1299, 1), (key1568, -2), (key1904, -2), (key1594, 1), (key1912, 1), (key1299, -2), (key1576, 1), (key1904, 1), (key1617, -1), (key1682, -1), (key1634, 1), (key1690, 1), (key1617, 1), (key1919, 1), (key1634, -1), (key1927, -1), (key1311, -1), (key1352, -1), (key1541, 1), (key1897, 1), (key1319, 1), (key1352, 1), (key1549, -1), (key1897, -1)]

theorem rawRowCheck6201 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form1 = rawRow6201 := by decide +kernel

def row6201 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6201 : row6201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6201 := by decide +kernel

theorem rowEval6201 (x : Key → ℝ) : Integer.Sparse.eval row6201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6201, Integer.Sparse.eval_collectBalanced, rawRowCheck6201]

def rawRow6202 : Integer.Sparse Key := [(key1427, -1), (key1419, -1), (key1445, 2), (key1394, -1), (key1386, -1), (key1473, 2), (key1419, 2), (key1481, -1), (key1445, -1), (key1394, 2), (key1473, -1), (key1427, -1), (key1576, 1), (key1568, 1), (key1594, -2), (key1299, 1), (key1291, 1), (key1904, -2), (key1568, -2), (key1912, 1), (key1594, 1), (key1299, -2), (key1904, 1), (key1576, 1), (key1682, -1), (key1617, -1), (key1690, 1), (key1634, 1), (key1919, 1), (key1617, 1), (key1927, -1), (key1634, -1), (key1352, -1), (key1311, -1), (key1897, 1), (key1541, 1), (key1352, 1), (key1319, 1), (key1897, -1), (key1549, -1)]

theorem rawRowCheck6202 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form1 = rawRow6202 := by decide +kernel

def row6202 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6202 : row6202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6202 := by decide +kernel

theorem rowEval6202 (x : Key → ℝ) : Integer.Sparse.eval row6202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6202, Integer.Sparse.eval_collectBalanced, rawRowCheck6202]

def rawRow6203 : Integer.Sparse Key := [(key1419, -1), (key1445, -1), (key1427, 2), (key1419, -1), (key1445, -1), (key1386, 2), (key1481, 2), (key1394, -1), (key1473, -1), (key1427, 2), (key1394, -1), (key1473, -1), (key1568, 1), (key1594, 1), (key1576, -2), (key1568, 1), (key1594, 1), (key1291, -2), (key1912, -2), (key1299, 1), (key1904, 1), (key1576, -2), (key1299, 1), (key1904, 1), (key1541, -1), (key1690, -1), (key1549, 1), (key1682, 1), (key1311, 1), (key1927, 1), (key1319, -1), (key1919, -1), (key1541, -1), (key1690, -1), (key1311, 1), (key1927, 1), (key1549, 1), (key1682, 1), (key1319, -1), (key1919, -1)]

theorem rawRowCheck6203 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form1 = rawRow6203 := by decide +kernel

def row6203 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 4), (key1445, -2), (key1473, -2), (key1481, 2), (key1541, -2), (key1549, 2), (key1568, 2), (key1576, -4), (key1594, 2), (key1682, 2), (key1690, -2), (key1904, 2), (key1912, -2), (key1919, -2), (key1927, 2)]

theorem rowCheck6203 : row6203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6203 := by decide +kernel

theorem rowEval6203 (x : Key → ℝ) : Integer.Sparse.eval row6203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6203, Integer.Sparse.eval_collectBalanced, rawRowCheck6203]

def rawRow6204 : Integer.Sparse Key := [(key1445, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1419, -1), (key1481, 2), (key1386, 2), (key1473, -1), (key1394, -1), (key1427, 2), (key1473, -1), (key1394, -1), (key1594, 1), (key1568, 1), (key1576, -2), (key1594, 1), (key1568, 1), (key1912, -2), (key1291, -2), (key1904, 1), (key1299, 1), (key1576, -2), (key1904, 1), (key1299, 1), (key1690, -1), (key1541, -1), (key1682, 1), (key1549, 1), (key1927, 1), (key1311, 1), (key1919, -1), (key1319, -1), (key1690, -1), (key1541, -1), (key1927, 1), (key1311, 1), (key1682, 1), (key1549, 1), (key1919, -1), (key1319, -1)]

theorem rawRowCheck6204 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form1 = rawRow6204 := by decide +kernel

def row6204 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 4), (key1445, -2), (key1473, -2), (key1481, 2), (key1541, -2), (key1549, 2), (key1568, 2), (key1576, -4), (key1594, 2), (key1682, 2), (key1690, -2), (key1904, 2), (key1912, -2), (key1919, -2), (key1927, 2)]

theorem rowCheck6204 : row6204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6204 := by decide +kernel

theorem rowEval6204 (x : Key → ℝ) : Integer.Sparse.eval row6204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6204, Integer.Sparse.eval_collectBalanced, rawRowCheck6204]

def rawRow6205 : Integer.Sparse Key := [(key1427, -1), (key1445, -1), (key1419, 2), (key1473, -1), (key1481, -1), (key1394, 2), (key1445, 2), (key1386, -1), (key1419, -1), (key1473, 2), (key1394, -1), (key1427, -1), (key1576, 1), (key1594, 1), (key1568, -2), (key1904, 1), (key1912, 1), (key1299, -2), (key1594, -2), (key1291, 1), (key1568, 1), (key1904, -2), (key1299, 1), (key1576, 1), (key1549, -1), (key1634, -1), (key1541, 1), (key1617, 1), (key1319, 1), (key1634, 1), (key1311, -1), (key1617, -1), (key1897, -1), (key1927, -1), (key1352, 1), (key1690, 1), (key1897, 1), (key1919, 1), (key1352, -1), (key1682, -1)]

theorem rawRowCheck6205 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form1 = rawRow6205 := by decide +kernel

def row6205 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6205 : row6205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6205 := by decide +kernel

theorem rowEval6205 (x : Key → ℝ) : Integer.Sparse.eval row6205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6205, Integer.Sparse.eval_collectBalanced, rawRowCheck6205]

def rawRow6206 : Integer.Sparse Key := [(key1445, -1), (key1427, -1), (key1419, 2), (key1481, -1), (key1473, -1), (key1445, 2), (key1394, 2), (key1419, -1), (key1386, -1), (key1473, 2), (key1427, -1), (key1394, -1), (key1594, 1), (key1576, 1), (key1568, -2), (key1912, 1), (key1904, 1), (key1594, -2), (key1299, -2), (key1568, 1), (key1291, 1), (key1904, -2), (key1576, 1), (key1299, 1), (key1634, -1), (key1549, -1), (key1617, 1), (key1541, 1), (key1634, 1), (key1319, 1), (key1617, -1), (key1311, -1), (key1927, -1), (key1897, -1), (key1690, 1), (key1352, 1), (key1919, 1), (key1897, 1), (key1682, -1), (key1352, -1)]

theorem rawRowCheck6206 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form1 = rawRow6206 := by decide +kernel

def row6206 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6206 : row6206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6206 := by decide +kernel

theorem rowEval6206 (x : Key → ℝ) : Integer.Sparse.eval row6206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6206, Integer.Sparse.eval_collectBalanced, rawRowCheck6206]

def rawRow6207 : Integer.Sparse Key := [(key1473, -1), (key1473, -1), (key1481, 2), (key1394, -1), (key1394, -1), (key1427, 2), (key1427, 2), (key1445, -1), (key1445, -1), (key1386, 2), (key1419, -1), (key1419, -1), (key1904, 1), (key1904, 1), (key1912, -2), (key1299, 1), (key1299, 1), (key1576, -2), (key1576, -2), (key1594, 1), (key1594, 1), (key1291, -2), (key1568, 1), (key1568, 1), (key1919, -1), (key1919, -1), (key1927, 1), (key1927, 1), (key1682, 1), (key1682, 1), (key1690, -1), (key1690, -1), (key1319, -1), (key1319, -1), (key1549, 1), (key1549, 1), (key1311, 1), (key1311, 1), (key1541, -1), (key1541, -1)]

theorem rawRowCheck6207 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form1 = rawRow6207 := by decide +kernel

def row6207 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 4), (key1445, -2), (key1473, -2), (key1481, 2), (key1541, -2), (key1549, 2), (key1568, 2), (key1576, -4), (key1594, 2), (key1682, 2), (key1690, -2), (key1904, 2), (key1912, -2), (key1919, -2), (key1927, 2)]

theorem rowCheck6207 : row6207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6207 := by decide +kernel

theorem rowEval6207 (x : Key → ℝ) : Integer.Sparse.eval row6207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6207, Integer.Sparse.eval_collectBalanced, rawRowCheck6207]

def rawRow6208 : Integer.Sparse Key := [(key1473, -1), (key1481, -1), (key1473, 2), (key1427, -1), (key1445, -1), (key1394, 2), (key1445, 2), (key1394, -1), (key1427, -1), (key1419, 2), (key1386, -1), (key1419, -1), (key1904, 1), (key1912, 1), (key1904, -2), (key1576, 1), (key1594, 1), (key1299, -2), (key1594, -2), (key1299, 1), (key1576, 1), (key1568, -2), (key1291, 1), (key1568, 1), (key1897, -1), (key1927, -1), (key1897, 1), (key1919, 1), (key1352, 1), (key1690, 1), (key1352, -1), (key1682, -1), (key1549, -1), (key1634, -1), (key1319, 1), (key1634, 1), (key1541, 1), (key1617, 1), (key1311, -1), (key1617, -1)]

theorem rawRowCheck6208 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form1 = rawRow6208 := by decide +kernel

def row6208 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6208 : row6208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6208 := by decide +kernel

theorem rowEval6208 (x : Key → ℝ) : Integer.Sparse.eval row6208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6208, Integer.Sparse.eval_collectBalanced, rawRowCheck6208]

def rawRow6209 : Integer.Sparse Key := [(key1481, -1), (key1473, -1), (key1473, 2), (key1445, -1), (key1427, -1), (key1445, 2), (key1394, 2), (key1427, -1), (key1394, -1), (key1419, 2), (key1419, -1), (key1386, -1), (key1912, 1), (key1904, 1), (key1904, -2), (key1594, 1), (key1576, 1), (key1594, -2), (key1299, -2), (key1576, 1), (key1299, 1), (key1568, -2), (key1568, 1), (key1291, 1), (key1927, -1), (key1897, -1), (key1919, 1), (key1897, 1), (key1690, 1), (key1352, 1), (key1682, -1), (key1352, -1), (key1634, -1), (key1549, -1), (key1634, 1), (key1319, 1), (key1617, 1), (key1541, 1), (key1617, -1), (key1311, -1)]

theorem rawRowCheck6209 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form1 = rawRow6209 := by decide +kernel

def row6209 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6209 : row6209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6209 := by decide +kernel

theorem rowEval6209 (x : Key → ℝ) : Integer.Sparse.eval row6209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6209, Integer.Sparse.eval_collectBalanced, rawRowCheck6209]

def rawRow6210 : Integer.Sparse Key := [(key1541, -1), (key1549, -1), (key1557, 2), (key1568, -1), (key1576, -1), (key1617, 2), (key1682, 2), (key1625, -1), (key1684, -1), (key1594, 2), (key1634, -1), (key1690, -1), (key1311, 1), (key1319, 1), (key1327, -2), (key1419, 1), (key1427, 1), (key1617, -2), (key1919, -2), (key1625, 1), (key1921, 1), (key1445, -2), (key1634, 1), (key1927, 1), (key1311, -1), (key1352, -1), (key1327, 1), (key1355, 1), (key1541, 1), (key1897, 1), (key1557, -1), (key1900, -1), (key1419, -1), (key1473, -1), (key1568, 1), (key1904, 1), (key1445, 1), (key1481, 1), (key1594, -1), (key1912, -1)]

theorem rawRowCheck6210 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form1 = rawRow6210 := by decide +kernel

def row6210 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6210 : row6210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6210 := by decide +kernel

theorem rowEval6210 (x : Key → ℝ) : Integer.Sparse.eval row6210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6210, Integer.Sparse.eval_collectBalanced, rawRowCheck6210]

def rawRow6211 : Integer.Sparse Key := [(key1549, -1), (key1541, -1), (key1557, 2), (key1576, -1), (key1568, -1), (key1682, 2), (key1617, 2), (key1684, -1), (key1625, -1), (key1594, 2), (key1690, -1), (key1634, -1), (key1319, 1), (key1311, 1), (key1327, -2), (key1427, 1), (key1419, 1), (key1919, -2), (key1617, -2), (key1921, 1), (key1625, 1), (key1445, -2), (key1927, 1), (key1634, 1), (key1352, -1), (key1311, -1), (key1355, 1), (key1327, 1), (key1897, 1), (key1541, 1), (key1900, -1), (key1557, -1), (key1473, -1), (key1419, -1), (key1904, 1), (key1568, 1), (key1481, 1), (key1445, 1), (key1912, -1), (key1594, -1)]

theorem rawRowCheck6211 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form1 = rawRow6211 := by decide +kernel

def row6211 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6211 : row6211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6211 := by decide +kernel

theorem rowEval6211 (x : Key → ℝ) : Integer.Sparse.eval row6211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6211, Integer.Sparse.eval_collectBalanced, rawRowCheck6211]

def rawRow6212 : Integer.Sparse Key := [(key1549, -1), (key1557, -1), (key1541, 2), (key1682, -1), (key1684, -1), (key1576, 2), (key1625, 2), (key1568, -1), (key1617, -1), (key1690, 2), (key1594, -1), (key1634, -1), (key1319, 1), (key1327, 1), (key1311, -2), (key1919, 1), (key1921, 1), (key1427, -2), (key1625, -2), (key1419, 1), (key1617, 1), (key1927, -2), (key1445, 1), (key1634, 1), (key1299, -1), (key1327, -1), (key1291, 1), (key1311, 1), (key1394, 1), (key1557, 1), (key1386, -1), (key1541, -1), (key1904, -1), (key1921, -1), (key1473, 1), (key1684, 1), (key1912, 1), (key1927, 1), (key1481, -1), (key1690, -1)]

theorem rawRowCheck6212 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form1 = rawRow6212 := by decide +kernel

def row6212 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6212 : row6212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6212 := by decide +kernel

theorem rowEval6212 (x : Key → ℝ) : Integer.Sparse.eval row6212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6212, Integer.Sparse.eval_collectBalanced, rawRowCheck6212]

def rawRow6213 : Integer.Sparse Key := [(key1557, -1), (key1549, -1), (key1541, 2), (key1684, -1), (key1682, -1), (key1625, 2), (key1576, 2), (key1617, -1), (key1568, -1), (key1690, 2), (key1634, -1), (key1594, -1), (key1327, 1), (key1319, 1), (key1311, -2), (key1921, 1), (key1919, 1), (key1625, -2), (key1427, -2), (key1617, 1), (key1419, 1), (key1927, -2), (key1634, 1), (key1445, 1), (key1327, -1), (key1299, -1), (key1311, 1), (key1291, 1), (key1557, 1), (key1394, 1), (key1541, -1), (key1386, -1), (key1921, -1), (key1904, -1), (key1684, 1), (key1473, 1), (key1927, 1), (key1912, 1), (key1690, -1), (key1481, -1)]

theorem rawRowCheck6213 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form1 = rawRow6213 := by decide +kernel

def row6213 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6213 : row6213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6213 := by decide +kernel

theorem rowEval6213 (x : Key → ℝ) : Integer.Sparse.eval row6213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6213, Integer.Sparse.eval_collectBalanced, rawRowCheck6213]

def rawRow6214 : Integer.Sparse Key := [(key1568, -1), (key1576, -1), (key1594, 2), (key1541, -1), (key1549, -1), (key1617, 2), (key1682, 2), (key1634, -1), (key1690, -1), (key1557, 2), (key1625, -1), (key1684, -1), (key1419, 1), (key1427, 1), (key1445, -2), (key1311, 1), (key1319, 1), (key1617, -2), (key1919, -2), (key1634, 1), (key1927, 1), (key1327, -2), (key1625, 1), (key1921, 1), (key1419, -1), (key1473, -1), (key1445, 1), (key1481, 1), (key1568, 1), (key1904, 1), (key1594, -1), (key1912, -1), (key1311, -1), (key1352, -1), (key1541, 1), (key1897, 1), (key1327, 1), (key1355, 1), (key1557, -1), (key1900, -1)]

theorem rawRowCheck6214 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form1 = rawRow6214 := by decide +kernel

def row6214 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6214 : row6214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6214 := by decide +kernel

theorem rowEval6214 (x : Key → ℝ) : Integer.Sparse.eval row6214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6214, Integer.Sparse.eval_collectBalanced, rawRowCheck6214]

def rawRow6215 : Integer.Sparse Key := [(key1576, -1), (key1568, -1), (key1594, 2), (key1549, -1), (key1541, -1), (key1682, 2), (key1617, 2), (key1690, -1), (key1634, -1), (key1557, 2), (key1684, -1), (key1625, -1), (key1427, 1), (key1419, 1), (key1445, -2), (key1319, 1), (key1311, 1), (key1919, -2), (key1617, -2), (key1927, 1), (key1634, 1), (key1327, -2), (key1921, 1), (key1625, 1), (key1473, -1), (key1419, -1), (key1481, 1), (key1445, 1), (key1904, 1), (key1568, 1), (key1912, -1), (key1594, -1), (key1352, -1), (key1311, -1), (key1897, 1), (key1541, 1), (key1355, 1), (key1327, 1), (key1900, -1), (key1557, -1)]

theorem rawRowCheck6215 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form1 = rawRow6215 := by decide +kernel

def row6215 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6215 : row6215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6215 := by decide +kernel

theorem rowEval6215 (x : Key → ℝ) : Integer.Sparse.eval row6215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6215, Integer.Sparse.eval_collectBalanced, rawRowCheck6215]

def rawRow6216 : Integer.Sparse Key := [(key1568, -1), (key1594, -1), (key1576, 2), (key1617, -1), (key1634, -1), (key1541, 2), (key1690, 2), (key1549, -1), (key1682, -1), (key1625, 2), (key1557, -1), (key1684, -1), (key1419, 1), (key1445, 1), (key1427, -2), (key1617, 1), (key1634, 1), (key1311, -2), (key1927, -2), (key1319, 1), (key1919, 1), (key1625, -2), (key1327, 1), (key1921, 1), (key1386, -1), (key1481, -1), (key1394, 1), (key1473, 1), (key1291, 1), (key1912, 1), (key1299, -1), (key1904, -1), (key1541, -1), (key1690, -1), (key1311, 1), (key1927, 1), (key1557, 1), (key1684, 1), (key1327, -1), (key1921, -1)]

theorem rawRowCheck6216 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form1 = rawRow6216 := by decide +kernel

def row6216 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6216 : row6216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6216 := by decide +kernel

theorem rowEval6216 (x : Key → ℝ) : Integer.Sparse.eval row6216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6216, Integer.Sparse.eval_collectBalanced, rawRowCheck6216]

def rawRow6217 : Integer.Sparse Key := [(key1594, -1), (key1568, -1), (key1576, 2), (key1634, -1), (key1617, -1), (key1690, 2), (key1541, 2), (key1682, -1), (key1549, -1), (key1625, 2), (key1684, -1), (key1557, -1), (key1445, 1), (key1419, 1), (key1427, -2), (key1634, 1), (key1617, 1), (key1927, -2), (key1311, -2), (key1919, 1), (key1319, 1), (key1625, -2), (key1921, 1), (key1327, 1), (key1481, -1), (key1386, -1), (key1473, 1), (key1394, 1), (key1912, 1), (key1291, 1), (key1904, -1), (key1299, -1), (key1690, -1), (key1541, -1), (key1927, 1), (key1311, 1), (key1684, 1), (key1557, 1), (key1921, -1), (key1327, -1)]

theorem rawRowCheck6217 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form1 = rawRow6217 := by decide +kernel

def row6217 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6217 : row6217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6217 := by decide +kernel

theorem rowEval6217 (x : Key → ℝ) : Integer.Sparse.eval row6217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6217, Integer.Sparse.eval_collectBalanced, rawRowCheck6217]

def rawRow6218 : Integer.Sparse Key := [(key1617, -1), (key1634, -1), (key1625, 2), (key1568, -1), (key1594, -1), (key1541, 2), (key1690, 2), (key1557, -1), (key1684, -1), (key1576, 2), (key1549, -1), (key1682, -1), (key1617, 1), (key1634, 1), (key1625, -2), (key1419, 1), (key1445, 1), (key1311, -2), (key1927, -2), (key1327, 1), (key1921, 1), (key1427, -2), (key1319, 1), (key1919, 1), (key1541, -1), (key1690, -1), (key1557, 1), (key1684, 1), (key1311, 1), (key1927, 1), (key1327, -1), (key1921, -1), (key1386, -1), (key1481, -1), (key1291, 1), (key1912, 1), (key1394, 1), (key1473, 1), (key1299, -1), (key1904, -1)]

theorem rawRowCheck6218 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form1 = rawRow6218 := by decide +kernel

def row6218 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6218 : row6218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6218 := by decide +kernel

theorem rowEval6218 (x : Key → ℝ) : Integer.Sparse.eval row6218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6218, Integer.Sparse.eval_collectBalanced, rawRowCheck6218]

def rawRow6219 : Integer.Sparse Key := [(key1634, -1), (key1617, -1), (key1625, 2), (key1594, -1), (key1568, -1), (key1690, 2), (key1541, 2), (key1684, -1), (key1557, -1), (key1576, 2), (key1682, -1), (key1549, -1), (key1634, 1), (key1617, 1), (key1625, -2), (key1445, 1), (key1419, 1), (key1927, -2), (key1311, -2), (key1921, 1), (key1327, 1), (key1427, -2), (key1919, 1), (key1319, 1), (key1690, -1), (key1541, -1), (key1684, 1), (key1557, 1), (key1927, 1), (key1311, 1), (key1921, -1), (key1327, -1), (key1481, -1), (key1386, -1), (key1912, 1), (key1291, 1), (key1473, 1), (key1394, 1), (key1904, -1), (key1299, -1)]

theorem rawRowCheck6219 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form1 = rawRow6219 := by decide +kernel

def row6219 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6219 : row6219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6219 := by decide +kernel

theorem rowEval6219 (x : Key → ℝ) : Integer.Sparse.eval row6219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6219, Integer.Sparse.eval_collectBalanced, rawRowCheck6219]

def rawRow6220 : Integer.Sparse Key := [(key1625, -1), (key1634, -1), (key1617, 2), (key1684, -1), (key1690, -1), (key1557, 2), (key1594, 2), (key1541, -1), (key1568, -1), (key1682, 2), (key1549, -1), (key1576, -1), (key1625, 1), (key1634, 1), (key1617, -2), (key1921, 1), (key1927, 1), (key1327, -2), (key1445, -2), (key1311, 1), (key1419, 1), (key1919, -2), (key1319, 1), (key1427, 1), (key1557, -1), (key1594, -1), (key1541, 1), (key1568, 1), (key1327, 1), (key1445, 1), (key1311, -1), (key1419, -1), (key1900, -1), (key1912, -1), (key1355, 1), (key1481, 1), (key1897, 1), (key1904, 1), (key1352, -1), (key1473, -1)]

theorem rawRowCheck6220 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form1 = rawRow6220 := by decide +kernel

def row6220 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6220 : row6220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6220 := by decide +kernel

theorem rowEval6220 (x : Key → ℝ) : Integer.Sparse.eval row6220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6220, Integer.Sparse.eval_collectBalanced, rawRowCheck6220]

def rawRow6221 : Integer.Sparse Key := [(key1634, -1), (key1625, -1), (key1617, 2), (key1690, -1), (key1684, -1), (key1594, 2), (key1557, 2), (key1568, -1), (key1541, -1), (key1682, 2), (key1576, -1), (key1549, -1), (key1634, 1), (key1625, 1), (key1617, -2), (key1927, 1), (key1921, 1), (key1445, -2), (key1327, -2), (key1419, 1), (key1311, 1), (key1919, -2), (key1427, 1), (key1319, 1), (key1594, -1), (key1557, -1), (key1568, 1), (key1541, 1), (key1445, 1), (key1327, 1), (key1419, -1), (key1311, -1), (key1912, -1), (key1900, -1), (key1481, 1), (key1355, 1), (key1904, 1), (key1897, 1), (key1473, -1), (key1352, -1)]

theorem rawRowCheck6221 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form1 = rawRow6221 := by decide +kernel

def row6221 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6221 : row6221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6221 := by decide +kernel

theorem rowEval6221 (x : Key → ℝ) : Integer.Sparse.eval row6221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6221, Integer.Sparse.eval_collectBalanced, rawRowCheck6221]

def rawRow6222 : Integer.Sparse Key := [(key1682, -1), (key1684, -1), (key1690, 2), (key1549, -1), (key1557, -1), (key1576, 2), (key1625, 2), (key1594, -1), (key1634, -1), (key1541, 2), (key1568, -1), (key1617, -1), (key1919, 1), (key1921, 1), (key1927, -2), (key1319, 1), (key1327, 1), (key1427, -2), (key1625, -2), (key1445, 1), (key1634, 1), (key1311, -2), (key1419, 1), (key1617, 1), (key1904, -1), (key1921, -1), (key1912, 1), (key1927, 1), (key1473, 1), (key1684, 1), (key1481, -1), (key1690, -1), (key1299, -1), (key1327, -1), (key1394, 1), (key1557, 1), (key1291, 1), (key1311, 1), (key1386, -1), (key1541, -1)]

theorem rawRowCheck6222 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form1 = rawRow6222 := by decide +kernel

def row6222 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6222 : row6222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6222 := by decide +kernel

theorem rowEval6222 (x : Key → ℝ) : Integer.Sparse.eval row6222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6222, Integer.Sparse.eval_collectBalanced, rawRowCheck6222]

def rawRow6223 : Integer.Sparse Key := [(key1684, -1), (key1682, -1), (key1690, 2), (key1557, -1), (key1549, -1), (key1625, 2), (key1576, 2), (key1634, -1), (key1594, -1), (key1541, 2), (key1617, -1), (key1568, -1), (key1921, 1), (key1919, 1), (key1927, -2), (key1327, 1), (key1319, 1), (key1625, -2), (key1427, -2), (key1634, 1), (key1445, 1), (key1311, -2), (key1617, 1), (key1419, 1), (key1921, -1), (key1904, -1), (key1927, 1), (key1912, 1), (key1684, 1), (key1473, 1), (key1690, -1), (key1481, -1), (key1327, -1), (key1299, -1), (key1557, 1), (key1394, 1), (key1311, 1), (key1291, 1), (key1541, -1), (key1386, -1)]

theorem rawRowCheck6223 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form1 = rawRow6223 := by decide +kernel

def row6223 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

theorem rowCheck6223 : row6223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6223 := by decide +kernel

theorem rowEval6223 (x : Key → ℝ) : Integer.Sparse.eval row6223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6223, Integer.Sparse.eval_collectBalanced, rawRowCheck6223]

def rawRow6224 : Integer.Sparse Key := [(key1684, -1), (key1690, -1), (key1682, 2), (key1625, -1), (key1634, -1), (key1557, 2), (key1594, 2), (key1549, -1), (key1576, -1), (key1617, 2), (key1541, -1), (key1568, -1), (key1921, 1), (key1927, 1), (key1919, -2), (key1625, 1), (key1634, 1), (key1327, -2), (key1445, -2), (key1319, 1), (key1427, 1), (key1617, -2), (key1311, 1), (key1419, 1), (key1900, -1), (key1912, -1), (key1897, 1), (key1904, 1), (key1355, 1), (key1481, 1), (key1352, -1), (key1473, -1), (key1557, -1), (key1594, -1), (key1327, 1), (key1445, 1), (key1541, 1), (key1568, 1), (key1311, -1), (key1419, -1)]

theorem rawRowCheck6224 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form1 = rawRow6224 := by decide +kernel

def row6224 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6224 : row6224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6224 := by decide +kernel

theorem rowEval6224 (x : Key → ℝ) : Integer.Sparse.eval row6224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6224, Integer.Sparse.eval_collectBalanced, rawRowCheck6224]

def rawRow6225 : Integer.Sparse Key := [(key1690, -1), (key1684, -1), (key1682, 2), (key1634, -1), (key1625, -1), (key1594, 2), (key1557, 2), (key1576, -1), (key1549, -1), (key1617, 2), (key1568, -1), (key1541, -1), (key1927, 1), (key1921, 1), (key1919, -2), (key1634, 1), (key1625, 1), (key1445, -2), (key1327, -2), (key1427, 1), (key1319, 1), (key1617, -2), (key1419, 1), (key1311, 1), (key1912, -1), (key1900, -1), (key1904, 1), (key1897, 1), (key1481, 1), (key1355, 1), (key1473, -1), (key1352, -1), (key1594, -1), (key1557, -1), (key1445, 1), (key1327, 1), (key1568, 1), (key1541, 1), (key1419, -1), (key1311, -1)]

theorem rawRowCheck6225 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form1 = rawRow6225 := by decide +kernel

def row6225 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6225 : row6225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6225 := by decide +kernel

theorem rowEval6225 (x : Key → ℝ) : Integer.Sparse.eval row6225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6225, Integer.Sparse.eval_collectBalanced, rawRowCheck6225]

def rawRow6226 : Integer.Sparse Key := [(key1897, -1), (key1897, -1), (key1900, 2), (key1904, -1), (key1904, -1), (key1919, 2), (key1919, 2), (key1921, -1), (key1921, -1), (key1912, 2), (key1927, -1), (key1927, -1), (key1352, 1), (key1352, 1), (key1355, -2), (key1473, 1), (key1473, 1), (key1682, -2), (key1682, -2), (key1684, 1), (key1684, 1), (key1481, -2), (key1690, 1), (key1690, 1), (key1319, -1), (key1319, -1), (key1327, 1), (key1327, 1), (key1549, 1), (key1549, 1), (key1557, -1), (key1557, -1), (key1427, -1), (key1427, -1), (key1576, 1), (key1576, 1), (key1445, 1), (key1445, 1), (key1594, -1), (key1594, -1)]

theorem rawRowCheck6226 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form1 = rawRow6226 := by decide +kernel

def row6226 : Integer.Sparse Key := [(key1319, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1427, -2), (key1445, 2), (key1473, 2), (key1481, -2), (key1549, 2), (key1557, -2), (key1576, 2), (key1594, -2), (key1682, -4), (key1684, 2), (key1690, 2), (key1897, -2), (key1900, 2), (key1904, -2), (key1912, 2), (key1919, 4), (key1921, -2), (key1927, -2)]

theorem rowCheck6226 : row6226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6226 := by decide +kernel

theorem rowEval6226 (x : Key → ℝ) : Integer.Sparse.eval row6226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6226, Integer.Sparse.eval_collectBalanced, rawRowCheck6226]

def rawRow6227 : Integer.Sparse Key := [(key1897, -1), (key1900, -1), (key1897, 2), (key1919, -1), (key1921, -1), (key1904, 2), (key1921, 2), (key1904, -1), (key1919, -1), (key1927, 2), (key1912, -1), (key1927, -1), (key1352, 1), (key1355, 1), (key1352, -2), (key1682, 1), (key1684, 1), (key1473, -2), (key1684, -2), (key1473, 1), (key1682, 1), (key1690, -2), (key1481, 1), (key1690, 1), (key1299, -1), (key1327, -1), (key1299, 1), (key1319, 1), (key1394, 1), (key1557, 1), (key1394, -1), (key1549, -1), (key1576, -1), (key1625, -1), (key1427, 1), (key1625, 1), (key1594, 1), (key1634, 1), (key1445, -1), (key1634, -1)]

theorem rawRowCheck6227 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form1 = rawRow6227 := by decide +kernel

def row6227 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6227 : row6227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6227 := by decide +kernel

theorem rowEval6227 (x : Key → ℝ) : Integer.Sparse.eval row6227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6227, Integer.Sparse.eval_collectBalanced, rawRowCheck6227]

def rawRow6228 : Integer.Sparse Key := [(key1900, -1), (key1897, -1), (key1897, 2), (key1921, -1), (key1919, -1), (key1921, 2), (key1904, 2), (key1919, -1), (key1904, -1), (key1927, 2), (key1927, -1), (key1912, -1), (key1355, 1), (key1352, 1), (key1352, -2), (key1684, 1), (key1682, 1), (key1684, -2), (key1473, -2), (key1682, 1), (key1473, 1), (key1690, -2), (key1690, 1), (key1481, 1), (key1327, -1), (key1299, -1), (key1319, 1), (key1299, 1), (key1557, 1), (key1394, 1), (key1549, -1), (key1394, -1), (key1625, -1), (key1576, -1), (key1625, 1), (key1427, 1), (key1634, 1), (key1594, 1), (key1634, -1), (key1445, -1)]

theorem rawRowCheck6228 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form1 = rawRow6228 := by decide +kernel

def row6228 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6228 : row6228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6228 := by decide +kernel

theorem rowEval6228 (x : Key → ℝ) : Integer.Sparse.eval row6228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6228, Integer.Sparse.eval_collectBalanced, rawRowCheck6228]

def rawRow6229 : Integer.Sparse Key := [(key1904, -1), (key1904, -1), (key1912, 2), (key1897, -1), (key1897, -1), (key1919, 2), (key1919, 2), (key1927, -1), (key1927, -1), (key1900, 2), (key1921, -1), (key1921, -1), (key1473, 1), (key1473, 1), (key1481, -2), (key1352, 1), (key1352, 1), (key1682, -2), (key1682, -2), (key1690, 1), (key1690, 1), (key1355, -2), (key1684, 1), (key1684, 1), (key1427, -1), (key1427, -1), (key1445, 1), (key1445, 1), (key1576, 1), (key1576, 1), (key1594, -1), (key1594, -1), (key1319, -1), (key1319, -1), (key1549, 1), (key1549, 1), (key1327, 1), (key1327, 1), (key1557, -1), (key1557, -1)]

theorem rawRowCheck6229 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form1 = rawRow6229 := by decide +kernel

def row6229 : Integer.Sparse Key := [(key1319, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1427, -2), (key1445, 2), (key1473, 2), (key1481, -2), (key1549, 2), (key1557, -2), (key1576, 2), (key1594, -2), (key1682, -4), (key1684, 2), (key1690, 2), (key1897, -2), (key1900, 2), (key1904, -2), (key1912, 2), (key1919, 4), (key1921, -2), (key1927, -2)]

theorem rowCheck6229 : row6229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6229 := by decide +kernel

theorem rowEval6229 (x : Key → ℝ) : Integer.Sparse.eval row6229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6229, Integer.Sparse.eval_collectBalanced, rawRowCheck6229]

def rawRow6230 : Integer.Sparse Key := [(key1904, -1), (key1912, -1), (key1904, 2), (key1919, -1), (key1927, -1), (key1897, 2), (key1927, 2), (key1897, -1), (key1919, -1), (key1921, 2), (key1900, -1), (key1921, -1), (key1473, 1), (key1481, 1), (key1473, -2), (key1682, 1), (key1690, 1), (key1352, -2), (key1690, -2), (key1352, 1), (key1682, 1), (key1684, -2), (key1355, 1), (key1684, 1), (key1394, -1), (key1445, -1), (key1394, 1), (key1427, 1), (key1299, 1), (key1594, 1), (key1299, -1), (key1576, -1), (key1549, -1), (key1634, -1), (key1319, 1), (key1634, 1), (key1557, 1), (key1625, 1), (key1327, -1), (key1625, -1)]

theorem rawRowCheck6230 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form1 = rawRow6230 := by decide +kernel

def row6230 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6230 : row6230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6230 := by decide +kernel

theorem rowEval6230 (x : Key → ℝ) : Integer.Sparse.eval row6230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6230, Integer.Sparse.eval_collectBalanced, rawRowCheck6230]

def rawRow6231 : Integer.Sparse Key := [(key1912, -1), (key1904, -1), (key1904, 2), (key1927, -1), (key1919, -1), (key1927, 2), (key1897, 2), (key1919, -1), (key1897, -1), (key1921, 2), (key1921, -1), (key1900, -1), (key1481, 1), (key1473, 1), (key1473, -2), (key1690, 1), (key1682, 1), (key1690, -2), (key1352, -2), (key1682, 1), (key1352, 1), (key1684, -2), (key1684, 1), (key1355, 1), (key1445, -1), (key1394, -1), (key1427, 1), (key1394, 1), (key1594, 1), (key1299, 1), (key1576, -1), (key1299, -1), (key1634, -1), (key1549, -1), (key1634, 1), (key1319, 1), (key1625, 1), (key1557, 1), (key1625, -1), (key1327, -1)]

theorem rawRowCheck6231 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form1 = rawRow6231 := by decide +kernel

def row6231 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6231 : row6231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6231 := by decide +kernel

theorem rowEval6231 (x : Key → ℝ) : Integer.Sparse.eval row6231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6231, Integer.Sparse.eval_collectBalanced, rawRowCheck6231]

def rawRow6232 : Integer.Sparse Key := [(key1919, -1), (key1921, -1), (key1927, 2), (key1897, -1), (key1900, -1), (key1904, 2), (key1921, 2), (key1912, -1), (key1927, -1), (key1897, 2), (key1904, -1), (key1919, -1), (key1682, 1), (key1684, 1), (key1690, -2), (key1352, 1), (key1355, 1), (key1473, -2), (key1684, -2), (key1481, 1), (key1690, 1), (key1352, -2), (key1473, 1), (key1682, 1), (key1576, -1), (key1625, -1), (key1594, 1), (key1634, 1), (key1427, 1), (key1625, 1), (key1445, -1), (key1634, -1), (key1299, -1), (key1327, -1), (key1394, 1), (key1557, 1), (key1299, 1), (key1319, 1), (key1394, -1), (key1549, -1)]

theorem rawRowCheck6232 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form1 = rawRow6232 := by decide +kernel

def row6232 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6232 : row6232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6232 := by decide +kernel

theorem rowEval6232 (x : Key → ℝ) : Integer.Sparse.eval row6232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6232, Integer.Sparse.eval_collectBalanced, rawRowCheck6232]

def rawRow6233 : Integer.Sparse Key := [(key1921, -1), (key1919, -1), (key1927, 2), (key1900, -1), (key1897, -1), (key1921, 2), (key1904, 2), (key1927, -1), (key1912, -1), (key1897, 2), (key1919, -1), (key1904, -1), (key1684, 1), (key1682, 1), (key1690, -2), (key1355, 1), (key1352, 1), (key1684, -2), (key1473, -2), (key1690, 1), (key1481, 1), (key1352, -2), (key1682, 1), (key1473, 1), (key1625, -1), (key1576, -1), (key1634, 1), (key1594, 1), (key1625, 1), (key1427, 1), (key1634, -1), (key1445, -1), (key1327, -1), (key1299, -1), (key1557, 1), (key1394, 1), (key1319, 1), (key1299, 1), (key1549, -1), (key1394, -1)]

theorem rawRowCheck6233 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form1 = rawRow6233 := by decide +kernel

def row6233 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6233 : row6233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6233 := by decide +kernel

theorem rowEval6233 (x : Key → ℝ) : Integer.Sparse.eval row6233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6233, Integer.Sparse.eval_collectBalanced, rawRowCheck6233]

def rawRow6234 : Integer.Sparse Key := [(key1919, -1), (key1927, -1), (key1921, 2), (key1904, -1), (key1912, -1), (key1897, 2), (key1927, 2), (key1900, -1), (key1921, -1), (key1904, 2), (key1897, -1), (key1919, -1), (key1682, 1), (key1690, 1), (key1684, -2), (key1473, 1), (key1481, 1), (key1352, -2), (key1690, -2), (key1355, 1), (key1684, 1), (key1473, -2), (key1352, 1), (key1682, 1), (key1549, -1), (key1634, -1), (key1557, 1), (key1625, 1), (key1319, 1), (key1634, 1), (key1327, -1), (key1625, -1), (key1394, -1), (key1445, -1), (key1299, 1), (key1594, 1), (key1394, 1), (key1427, 1), (key1299, -1), (key1576, -1)]

theorem rawRowCheck6234 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form1 = rawRow6234 := by decide +kernel

def row6234 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6234 : row6234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6234 := by decide +kernel

theorem rowEval6234 (x : Key → ℝ) : Integer.Sparse.eval row6234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6234, Integer.Sparse.eval_collectBalanced, rawRowCheck6234]

def rawRow6235 : Integer.Sparse Key := [(key1927, -1), (key1919, -1), (key1921, 2), (key1912, -1), (key1904, -1), (key1927, 2), (key1897, 2), (key1921, -1), (key1900, -1), (key1904, 2), (key1919, -1), (key1897, -1), (key1690, 1), (key1682, 1), (key1684, -2), (key1481, 1), (key1473, 1), (key1690, -2), (key1352, -2), (key1684, 1), (key1355, 1), (key1473, -2), (key1682, 1), (key1352, 1), (key1634, -1), (key1549, -1), (key1625, 1), (key1557, 1), (key1634, 1), (key1319, 1), (key1625, -1), (key1327, -1), (key1445, -1), (key1394, -1), (key1594, 1), (key1299, 1), (key1427, 1), (key1394, 1), (key1576, -1), (key1299, -1)]

theorem rawRowCheck6235 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form1 = rawRow6235 := by decide +kernel

def row6235 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

theorem rowCheck6235 : row6235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6235 := by decide +kernel

theorem rowEval6235 (x : Key → ℝ) : Integer.Sparse.eval row6235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6235, Integer.Sparse.eval_collectBalanced, rawRowCheck6235]

def rawRow6236 : Integer.Sparse Key := [(key1921, -1), (key1927, -1), (key1919, 2), (key1921, -1), (key1927, -1), (key1900, 2), (key1912, 2), (key1897, -1), (key1904, -1), (key1919, 2), (key1897, -1), (key1904, -1), (key1684, 1), (key1690, 1), (key1682, -2), (key1684, 1), (key1690, 1), (key1355, -2), (key1481, -2), (key1352, 1), (key1473, 1), (key1682, -2), (key1352, 1), (key1473, 1), (key1557, -1), (key1594, -1), (key1549, 1), (key1576, 1), (key1327, 1), (key1445, 1), (key1319, -1), (key1427, -1), (key1557, -1), (key1594, -1), (key1327, 1), (key1445, 1), (key1549, 1), (key1576, 1), (key1319, -1), (key1427, -1)]

theorem rawRowCheck6236 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form1 = rawRow6236 := by decide +kernel

def row6236 : Integer.Sparse Key := [(key1319, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1427, -2), (key1445, 2), (key1473, 2), (key1481, -2), (key1549, 2), (key1557, -2), (key1576, 2), (key1594, -2), (key1682, -4), (key1684, 2), (key1690, 2), (key1897, -2), (key1900, 2), (key1904, -2), (key1912, 2), (key1919, 4), (key1921, -2), (key1927, -2)]

theorem rowCheck6236 : row6236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6236 := by decide +kernel

theorem rowEval6236 (x : Key → ℝ) : Integer.Sparse.eval row6236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6236, Integer.Sparse.eval_collectBalanced, rawRowCheck6236]

def rawRow6237 : Integer.Sparse Key := [(key1927, -1), (key1921, -1), (key1919, 2), (key1927, -1), (key1921, -1), (key1912, 2), (key1900, 2), (key1904, -1), (key1897, -1), (key1919, 2), (key1904, -1), (key1897, -1), (key1690, 1), (key1684, 1), (key1682, -2), (key1690, 1), (key1684, 1), (key1481, -2), (key1355, -2), (key1473, 1), (key1352, 1), (key1682, -2), (key1473, 1), (key1352, 1), (key1594, -1), (key1557, -1), (key1576, 1), (key1549, 1), (key1445, 1), (key1327, 1), (key1427, -1), (key1319, -1), (key1594, -1), (key1557, -1), (key1445, 1), (key1327, 1), (key1576, 1), (key1549, 1), (key1427, -1), (key1319, -1)]

theorem rawRowCheck6237 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form1 = rawRow6237 := by decide +kernel

def row6237 : Integer.Sparse Key := [(key1319, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1427, -2), (key1445, 2), (key1473, 2), (key1481, -2), (key1549, 2), (key1557, -2), (key1576, 2), (key1594, -2), (key1682, -4), (key1684, 2), (key1690, 2), (key1897, -2), (key1900, 2), (key1904, -2), (key1912, 2), (key1919, 4), (key1921, -2), (key1927, -2)]

theorem rowCheck6237 : row6237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6237 := by decide +kernel

theorem rowEval6237 (x : Key → ℝ) : Integer.Sparse.eval row6237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6237, Integer.Sparse.eval_collectBalanced, rawRowCheck6237]

def rawRow6238 : Integer.Sparse Key := [(key2664, -1), (key2668, -1), (key2668, 2), (key2779, -1), (key2783, -1), (key2779, 2), (key2791, 2), (key2783, -1), (key2791, -1), (key2937, 2), (key2937, -1), (key2942, -1), (key2609, 1), (key2613, 1), (key2613, -2), (key2802, 1), (key2806, 1), (key2802, -2), (key2826, -2), (key2806, 1), (key2826, 1), (key2949, -2), (key2949, 1), (key2959, 1), (key2625, -1), (key2637, -1), (key2629, 1), (key2637, 1), (key2699, 1), (key2723, 1), (key2703, -1), (key2723, -1), (key2852, -1), (key2857, -1), (key2852, 1), (key2867, 1), (key2973, 1), (key2975, 1), (key2973, -1), (key2982, -1)]

theorem rawRowCheck6238 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form2 = rawRow6238 := by decide +kernel

def row6238 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6238 : row6238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6238 := by decide +kernel

theorem rowEval6238 (x : Key → ℝ) : Integer.Sparse.eval row6238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6238, Integer.Sparse.eval_collectBalanced, rawRowCheck6238]

def rawRow6239 : Integer.Sparse Key := [(key2668, -1), (key2664, -1), (key2668, 2), (key2783, -1), (key2779, -1), (key2791, 2), (key2779, 2), (key2791, -1), (key2783, -1), (key2937, 2), (key2942, -1), (key2937, -1), (key2613, 1), (key2609, 1), (key2613, -2), (key2806, 1), (key2802, 1), (key2826, -2), (key2802, -2), (key2826, 1), (key2806, 1), (key2949, -2), (key2959, 1), (key2949, 1), (key2637, -1), (key2625, -1), (key2637, 1), (key2629, 1), (key2723, 1), (key2699, 1), (key2723, -1), (key2703, -1), (key2857, -1), (key2852, -1), (key2867, 1), (key2852, 1), (key2975, 1), (key2973, 1), (key2982, -1), (key2973, -1)]

theorem rawRowCheck6239 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form2 = rawRow6239 := by decide +kernel

def row6239 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6239 : row6239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6239 := by decide +kernel

theorem rowEval6239 (x : Key → ℝ) : Integer.Sparse.eval row6239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6239, Integer.Sparse.eval_collectBalanced, rawRowCheck6239]

def rawRow6240 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2664, 2), (key2791, -1), (key2791, -1), (key2783, 2), (key2783, 2), (key2779, -1), (key2779, -1), (key2942, 2), (key2937, -1), (key2937, -1), (key2613, 1), (key2613, 1), (key2609, -2), (key2826, 1), (key2826, 1), (key2806, -2), (key2806, -2), (key2802, 1), (key2802, 1), (key2959, -2), (key2949, 1), (key2949, 1), (key2629, -1), (key2629, -1), (key2625, 1), (key2625, 1), (key2703, 1), (key2703, 1), (key2699, -1), (key2699, -1), (key2867, -1), (key2867, -1), (key2857, 1), (key2857, 1), (key2982, 1), (key2982, 1), (key2975, -1), (key2975, -1)]

theorem rawRowCheck6240 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form2 = rawRow6240 := by decide +kernel

def row6240 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 2), (key2806, -4), (key2826, 2), (key2857, 2), (key2867, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

theorem rowCheck6240 : row6240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6240 := by decide +kernel

theorem rowEval6240 (x : Key → ℝ) : Integer.Sparse.eval row6240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6240, Integer.Sparse.eval_collectBalanced, rawRowCheck6240]

def rawRow6241 : Integer.Sparse Key := [(key2779, -1), (key2783, -1), (key2937, 2), (key2664, -1), (key2668, -1), (key2779, 2), (key2791, 2), (key2937, -1), (key2942, -1), (key2668, 2), (key2783, -1), (key2791, -1), (key2802, 1), (key2806, 1), (key2949, -2), (key2609, 1), (key2613, 1), (key2802, -2), (key2826, -2), (key2949, 1), (key2959, 1), (key2613, -2), (key2806, 1), (key2826, 1), (key2852, -1), (key2857, -1), (key2973, 1), (key2975, 1), (key2852, 1), (key2867, 1), (key2973, -1), (key2982, -1), (key2625, -1), (key2637, -1), (key2699, 1), (key2723, 1), (key2629, 1), (key2637, 1), (key2703, -1), (key2723, -1)]

theorem rawRowCheck6241 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form2 = rawRow6241 := by decide +kernel

def row6241 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6241 : row6241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6241 := by decide +kernel

theorem rowEval6241 (x : Key → ℝ) : Integer.Sparse.eval row6241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6241, Integer.Sparse.eval_collectBalanced, rawRowCheck6241]

def rawRow6242 : Integer.Sparse Key := [(key2783, -1), (key2779, -1), (key2937, 2), (key2668, -1), (key2664, -1), (key2791, 2), (key2779, 2), (key2942, -1), (key2937, -1), (key2668, 2), (key2791, -1), (key2783, -1), (key2806, 1), (key2802, 1), (key2949, -2), (key2613, 1), (key2609, 1), (key2826, -2), (key2802, -2), (key2959, 1), (key2949, 1), (key2613, -2), (key2826, 1), (key2806, 1), (key2857, -1), (key2852, -1), (key2975, 1), (key2973, 1), (key2867, 1), (key2852, 1), (key2982, -1), (key2973, -1), (key2637, -1), (key2625, -1), (key2723, 1), (key2699, 1), (key2637, 1), (key2629, 1), (key2723, -1), (key2703, -1)]

theorem rawRowCheck6242 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form2 = rawRow6242 := by decide +kernel

def row6242 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6242 : row6242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6242 := by decide +kernel

theorem rowEval6242 (x : Key → ℝ) : Integer.Sparse.eval row6242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6242, Integer.Sparse.eval_collectBalanced, rawRowCheck6242]

def rawRow6243 : Integer.Sparse Key := [(key2779, -1), (key2937, -1), (key2783, 2), (key2779, -1), (key2937, -1), (key2664, 2), (key2942, 2), (key2668, -1), (key2791, -1), (key2783, 2), (key2668, -1), (key2791, -1), (key2802, 1), (key2949, 1), (key2806, -2), (key2802, 1), (key2949, 1), (key2609, -2), (key2959, -2), (key2613, 1), (key2826, 1), (key2806, -2), (key2613, 1), (key2826, 1), (key2699, -1), (key2975, -1), (key2703, 1), (key2857, 1), (key2625, 1), (key2982, 1), (key2629, -1), (key2867, -1), (key2699, -1), (key2975, -1), (key2625, 1), (key2982, 1), (key2703, 1), (key2857, 1), (key2629, -1), (key2867, -1)]

theorem rawRowCheck6243 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form2 = rawRow6243 := by decide +kernel

def row6243 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 2), (key2806, -4), (key2826, 2), (key2857, 2), (key2867, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

theorem rowCheck6243 : row6243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6243 := by decide +kernel

theorem rowEval6243 (x : Key → ℝ) : Integer.Sparse.eval row6243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6243, Integer.Sparse.eval_collectBalanced, rawRowCheck6243]

def rawRow6244 : Integer.Sparse Key := [(key2937, -1), (key2779, -1), (key2783, 2), (key2937, -1), (key2779, -1), (key2942, 2), (key2664, 2), (key2791, -1), (key2668, -1), (key2783, 2), (key2791, -1), (key2668, -1), (key2949, 1), (key2802, 1), (key2806, -2), (key2949, 1), (key2802, 1), (key2959, -2), (key2609, -2), (key2826, 1), (key2613, 1), (key2806, -2), (key2826, 1), (key2613, 1), (key2975, -1), (key2699, -1), (key2857, 1), (key2703, 1), (key2982, 1), (key2625, 1), (key2867, -1), (key2629, -1), (key2975, -1), (key2699, -1), (key2982, 1), (key2625, 1), (key2857, 1), (key2703, 1), (key2867, -1), (key2629, -1)]

theorem rawRowCheck6244 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form2 = rawRow6244 := by decide +kernel

def row6244 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 2), (key2806, -4), (key2826, 2), (key2857, 2), (key2867, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

theorem rowCheck6244 : row6244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6244 := by decide +kernel

theorem rowEval6244 (x : Key → ℝ) : Integer.Sparse.eval row6244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6244, Integer.Sparse.eval_collectBalanced, rawRowCheck6244]

def rawRow6245 : Integer.Sparse Key := [(key2783, -1), (key2937, -1), (key2779, 2), (key2791, -1), (key2942, -1), (key2668, 2), (key2937, 2), (key2664, -1), (key2779, -1), (key2791, 2), (key2668, -1), (key2783, -1), (key2806, 1), (key2949, 1), (key2802, -2), (key2826, 1), (key2959, 1), (key2613, -2), (key2949, -2), (key2609, 1), (key2802, 1), (key2826, -2), (key2613, 1), (key2806, 1), (key2703, -1), (key2973, -1), (key2699, 1), (key2852, 1), (key2629, 1), (key2973, 1), (key2625, -1), (key2852, -1), (key2723, -1), (key2982, -1), (key2637, 1), (key2975, 1), (key2723, 1), (key2867, 1), (key2637, -1), (key2857, -1)]

theorem rawRowCheck6245 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form2 = rawRow6245 := by decide +kernel

def row6245 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6245 : row6245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6245 := by decide +kernel

theorem rowEval6245 (x : Key → ℝ) : Integer.Sparse.eval row6245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6245, Integer.Sparse.eval_collectBalanced, rawRowCheck6245]

def rawRow6246 : Integer.Sparse Key := [(key2937, -1), (key2783, -1), (key2779, 2), (key2942, -1), (key2791, -1), (key2937, 2), (key2668, 2), (key2779, -1), (key2664, -1), (key2791, 2), (key2783, -1), (key2668, -1), (key2949, 1), (key2806, 1), (key2802, -2), (key2959, 1), (key2826, 1), (key2949, -2), (key2613, -2), (key2802, 1), (key2609, 1), (key2826, -2), (key2806, 1), (key2613, 1), (key2973, -1), (key2703, -1), (key2852, 1), (key2699, 1), (key2973, 1), (key2629, 1), (key2852, -1), (key2625, -1), (key2982, -1), (key2723, -1), (key2975, 1), (key2637, 1), (key2867, 1), (key2723, 1), (key2857, -1), (key2637, -1)]

theorem rawRowCheck6246 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form2 = rawRow6246 := by decide +kernel

def row6246 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6246 : row6246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6246 := by decide +kernel

theorem rowEval6246 (x : Key → ℝ) : Integer.Sparse.eval row6246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6246, Integer.Sparse.eval_collectBalanced, rawRowCheck6246]

def rawRow6247 : Integer.Sparse Key := [(key2791, -1), (key2791, -1), (key2942, 2), (key2668, -1), (key2668, -1), (key2783, 2), (key2783, 2), (key2937, -1), (key2937, -1), (key2664, 2), (key2779, -1), (key2779, -1), (key2826, 1), (key2826, 1), (key2959, -2), (key2613, 1), (key2613, 1), (key2806, -2), (key2806, -2), (key2949, 1), (key2949, 1), (key2609, -2), (key2802, 1), (key2802, 1), (key2867, -1), (key2867, -1), (key2982, 1), (key2982, 1), (key2857, 1), (key2857, 1), (key2975, -1), (key2975, -1), (key2629, -1), (key2629, -1), (key2703, 1), (key2703, 1), (key2625, 1), (key2625, 1), (key2699, -1), (key2699, -1)]

theorem rawRowCheck6247 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form2 = rawRow6247 := by decide +kernel

def row6247 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 2), (key2806, -4), (key2826, 2), (key2857, 2), (key2867, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

theorem rowCheck6247 : row6247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6247 := by decide +kernel

theorem rowEval6247 (x : Key → ℝ) : Integer.Sparse.eval row6247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6247, Integer.Sparse.eval_collectBalanced, rawRowCheck6247]

def rawRow6248 : Integer.Sparse Key := [(key2791, -1), (key2942, -1), (key2791, 2), (key2783, -1), (key2937, -1), (key2668, 2), (key2937, 2), (key2668, -1), (key2783, -1), (key2779, 2), (key2664, -1), (key2779, -1), (key2826, 1), (key2959, 1), (key2826, -2), (key2806, 1), (key2949, 1), (key2613, -2), (key2949, -2), (key2613, 1), (key2806, 1), (key2802, -2), (key2609, 1), (key2802, 1), (key2723, -1), (key2982, -1), (key2723, 1), (key2867, 1), (key2637, 1), (key2975, 1), (key2637, -1), (key2857, -1), (key2703, -1), (key2973, -1), (key2629, 1), (key2973, 1), (key2699, 1), (key2852, 1), (key2625, -1), (key2852, -1)]

theorem rawRowCheck6248 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form2 = rawRow6248 := by decide +kernel

def row6248 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6248 : row6248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6248 := by decide +kernel

theorem rowEval6248 (x : Key → ℝ) : Integer.Sparse.eval row6248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6248, Integer.Sparse.eval_collectBalanced, rawRowCheck6248]

def rawRow6249 : Integer.Sparse Key := [(key2942, -1), (key2791, -1), (key2791, 2), (key2937, -1), (key2783, -1), (key2937, 2), (key2668, 2), (key2783, -1), (key2668, -1), (key2779, 2), (key2779, -1), (key2664, -1), (key2959, 1), (key2826, 1), (key2826, -2), (key2949, 1), (key2806, 1), (key2949, -2), (key2613, -2), (key2806, 1), (key2613, 1), (key2802, -2), (key2802, 1), (key2609, 1), (key2982, -1), (key2723, -1), (key2867, 1), (key2723, 1), (key2975, 1), (key2637, 1), (key2857, -1), (key2637, -1), (key2973, -1), (key2703, -1), (key2973, 1), (key2629, 1), (key2852, 1), (key2699, 1), (key2852, -1), (key2625, -1)]

theorem rawRowCheck6249 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form2 = rawRow6249 := by decide +kernel

def row6249 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6249 : row6249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6249 := by decide +kernel

theorem rowEval6249 (x : Key → ℝ) : Integer.Sparse.eval row6249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6249, Integer.Sparse.eval_collectBalanced, rawRowCheck6249]

def rawRow6250 : Integer.Sparse Key := [(key2699, -1), (key2703, -1), (key2736, 2), (key2802, -1), (key2806, -1), (key2852, 2), (key2857, 2), (key2894, -1), (key2896, -1), (key2949, 2), (key2973, -1), (key2975, -1), (key2625, 1), (key2629, 1), (key2647, -2), (key2779, 1), (key2783, 1), (key2852, -2), (key2867, -2), (key2894, 1), (key2903, 1), (key2937, -2), (key2973, 1), (key2982, 1), (key2625, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2699, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, -1), (key2791, -1), (key2802, 1), (key2826, 1), (key2937, 1), (key2942, 1), (key2949, -1), (key2959, -1)]

theorem rawRowCheck6250 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form2 = rawRow6250 := by decide +kernel

def row6250 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6250 : row6250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6250 := by decide +kernel

theorem rowEval6250 (x : Key → ℝ) : Integer.Sparse.eval row6250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6250, Integer.Sparse.eval_collectBalanced, rawRowCheck6250]

def rawRow6251 : Integer.Sparse Key := [(key2703, -1), (key2699, -1), (key2736, 2), (key2806, -1), (key2802, -1), (key2857, 2), (key2852, 2), (key2896, -1), (key2894, -1), (key2949, 2), (key2975, -1), (key2973, -1), (key2629, 1), (key2625, 1), (key2647, -2), (key2783, 1), (key2779, 1), (key2867, -2), (key2852, -2), (key2903, 1), (key2894, 1), (key2937, -2), (key2982, 1), (key2973, 1), (key2637, -1), (key2625, -1), (key2652, 1), (key2647, 1), (key2723, 1), (key2699, 1), (key2746, -1), (key2736, -1), (key2791, -1), (key2779, -1), (key2826, 1), (key2802, 1), (key2942, 1), (key2937, 1), (key2959, -1), (key2949, -1)]

theorem rawRowCheck6251 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form2 = rawRow6251 := by decide +kernel

def row6251 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6251 : row6251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6251 := by decide +kernel

theorem rowEval6251 (x : Key → ℝ) : Integer.Sparse.eval row6251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6251, Integer.Sparse.eval_collectBalanced, rawRowCheck6251]

def rawRow6252 : Integer.Sparse Key := [(key2703, -1), (key2736, -1), (key2699, 2), (key2857, -1), (key2896, -1), (key2806, 2), (key2894, 2), (key2802, -1), (key2852, -1), (key2975, 2), (key2949, -1), (key2973, -1), (key2629, 1), (key2647, 1), (key2625, -2), (key2867, 1), (key2903, 1), (key2783, -2), (key2894, -2), (key2779, 1), (key2852, 1), (key2982, -2), (key2937, 1), (key2973, 1), (key2613, -1), (key2647, -1), (key2609, 1), (key2625, 1), (key2668, 1), (key2736, 1), (key2664, -1), (key2699, -1), (key2826, -1), (key2903, -1), (key2791, 1), (key2896, 1), (key2959, 1), (key2982, 1), (key2942, -1), (key2975, -1)]

theorem rawRowCheck6252 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form2 = rawRow6252 := by decide +kernel

def row6252 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6252 : row6252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6252 := by decide +kernel

theorem rowEval6252 (x : Key → ℝ) : Integer.Sparse.eval row6252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6252, Integer.Sparse.eval_collectBalanced, rawRowCheck6252]

def rawRow6253 : Integer.Sparse Key := [(key2736, -1), (key2703, -1), (key2699, 2), (key2896, -1), (key2857, -1), (key2894, 2), (key2806, 2), (key2852, -1), (key2802, -1), (key2975, 2), (key2973, -1), (key2949, -1), (key2647, 1), (key2629, 1), (key2625, -2), (key2903, 1), (key2867, 1), (key2894, -2), (key2783, -2), (key2852, 1), (key2779, 1), (key2982, -2), (key2973, 1), (key2937, 1), (key2647, -1), (key2613, -1), (key2625, 1), (key2609, 1), (key2736, 1), (key2668, 1), (key2699, -1), (key2664, -1), (key2903, -1), (key2826, -1), (key2896, 1), (key2791, 1), (key2982, 1), (key2959, 1), (key2975, -1), (key2942, -1)]

theorem rawRowCheck6253 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form2 = rawRow6253 := by decide +kernel

def row6253 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6253 : row6253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6253 := by decide +kernel

theorem rowEval6253 (x : Key → ℝ) : Integer.Sparse.eval row6253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6253, Integer.Sparse.eval_collectBalanced, rawRowCheck6253]

def rawRow6254 : Integer.Sparse Key := [(key2802, -1), (key2806, -1), (key2949, 2), (key2699, -1), (key2703, -1), (key2852, 2), (key2857, 2), (key2973, -1), (key2975, -1), (key2736, 2), (key2894, -1), (key2896, -1), (key2779, 1), (key2783, 1), (key2937, -2), (key2625, 1), (key2629, 1), (key2852, -2), (key2867, -2), (key2973, 1), (key2982, 1), (key2647, -2), (key2894, 1), (key2903, 1), (key2779, -1), (key2791, -1), (key2937, 1), (key2942, 1), (key2802, 1), (key2826, 1), (key2949, -1), (key2959, -1), (key2625, -1), (key2637, -1), (key2699, 1), (key2723, 1), (key2647, 1), (key2652, 1), (key2736, -1), (key2746, -1)]

theorem rawRowCheck6254 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form2 = rawRow6254 := by decide +kernel

def row6254 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6254 : row6254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6254 := by decide +kernel

theorem rowEval6254 (x : Key → ℝ) : Integer.Sparse.eval row6254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6254, Integer.Sparse.eval_collectBalanced, rawRowCheck6254]

def rawRow6255 : Integer.Sparse Key := [(key2806, -1), (key2802, -1), (key2949, 2), (key2703, -1), (key2699, -1), (key2857, 2), (key2852, 2), (key2975, -1), (key2973, -1), (key2736, 2), (key2896, -1), (key2894, -1), (key2783, 1), (key2779, 1), (key2937, -2), (key2629, 1), (key2625, 1), (key2867, -2), (key2852, -2), (key2982, 1), (key2973, 1), (key2647, -2), (key2903, 1), (key2894, 1), (key2791, -1), (key2779, -1), (key2942, 1), (key2937, 1), (key2826, 1), (key2802, 1), (key2959, -1), (key2949, -1), (key2637, -1), (key2625, -1), (key2723, 1), (key2699, 1), (key2652, 1), (key2647, 1), (key2746, -1), (key2736, -1)]

theorem rawRowCheck6255 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form2 = rawRow6255 := by decide +kernel

def row6255 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6255 : row6255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6255 := by decide +kernel

theorem rowEval6255 (x : Key → ℝ) : Integer.Sparse.eval row6255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6255, Integer.Sparse.eval_collectBalanced, rawRowCheck6255]

def rawRow6256 : Integer.Sparse Key := [(key2802, -1), (key2949, -1), (key2806, 2), (key2852, -1), (key2973, -1), (key2699, 2), (key2975, 2), (key2703, -1), (key2857, -1), (key2894, 2), (key2736, -1), (key2896, -1), (key2779, 1), (key2937, 1), (key2783, -2), (key2852, 1), (key2973, 1), (key2625, -2), (key2982, -2), (key2629, 1), (key2867, 1), (key2894, -2), (key2647, 1), (key2903, 1), (key2664, -1), (key2942, -1), (key2668, 1), (key2791, 1), (key2609, 1), (key2959, 1), (key2613, -1), (key2826, -1), (key2699, -1), (key2975, -1), (key2625, 1), (key2982, 1), (key2736, 1), (key2896, 1), (key2647, -1), (key2903, -1)]

theorem rawRowCheck6256 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form2 = rawRow6256 := by decide +kernel

def row6256 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6256 : row6256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6256 := by decide +kernel

theorem rowEval6256 (x : Key → ℝ) : Integer.Sparse.eval row6256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6256, Integer.Sparse.eval_collectBalanced, rawRowCheck6256]

def rawRow6257 : Integer.Sparse Key := [(key2949, -1), (key2802, -1), (key2806, 2), (key2973, -1), (key2852, -1), (key2975, 2), (key2699, 2), (key2857, -1), (key2703, -1), (key2894, 2), (key2896, -1), (key2736, -1), (key2937, 1), (key2779, 1), (key2783, -2), (key2973, 1), (key2852, 1), (key2982, -2), (key2625, -2), (key2867, 1), (key2629, 1), (key2894, -2), (key2903, 1), (key2647, 1), (key2942, -1), (key2664, -1), (key2791, 1), (key2668, 1), (key2959, 1), (key2609, 1), (key2826, -1), (key2613, -1), (key2975, -1), (key2699, -1), (key2982, 1), (key2625, 1), (key2896, 1), (key2736, 1), (key2903, -1), (key2647, -1)]

theorem rawRowCheck6257 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form2 = rawRow6257 := by decide +kernel

def row6257 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6257 : row6257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6257 := by decide +kernel

theorem rowEval6257 (x : Key → ℝ) : Integer.Sparse.eval row6257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6257, Integer.Sparse.eval_collectBalanced, rawRowCheck6257]

def rawRow6258 : Integer.Sparse Key := [(key2852, -1), (key2973, -1), (key2894, 2), (key2802, -1), (key2949, -1), (key2699, 2), (key2975, 2), (key2736, -1), (key2896, -1), (key2806, 2), (key2703, -1), (key2857, -1), (key2852, 1), (key2973, 1), (key2894, -2), (key2779, 1), (key2937, 1), (key2625, -2), (key2982, -2), (key2647, 1), (key2903, 1), (key2783, -2), (key2629, 1), (key2867, 1), (key2699, -1), (key2975, -1), (key2736, 1), (key2896, 1), (key2625, 1), (key2982, 1), (key2647, -1), (key2903, -1), (key2664, -1), (key2942, -1), (key2609, 1), (key2959, 1), (key2668, 1), (key2791, 1), (key2613, -1), (key2826, -1)]

theorem rawRowCheck6258 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form2 = rawRow6258 := by decide +kernel

def row6258 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6258 : row6258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6258 := by decide +kernel

theorem rowEval6258 (x : Key → ℝ) : Integer.Sparse.eval row6258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6258, Integer.Sparse.eval_collectBalanced, rawRowCheck6258]

def rawRow6259 : Integer.Sparse Key := [(key2973, -1), (key2852, -1), (key2894, 2), (key2949, -1), (key2802, -1), (key2975, 2), (key2699, 2), (key2896, -1), (key2736, -1), (key2806, 2), (key2857, -1), (key2703, -1), (key2973, 1), (key2852, 1), (key2894, -2), (key2937, 1), (key2779, 1), (key2982, -2), (key2625, -2), (key2903, 1), (key2647, 1), (key2783, -2), (key2867, 1), (key2629, 1), (key2975, -1), (key2699, -1), (key2896, 1), (key2736, 1), (key2982, 1), (key2625, 1), (key2903, -1), (key2647, -1), (key2942, -1), (key2664, -1), (key2959, 1), (key2609, 1), (key2791, 1), (key2668, 1), (key2826, -1), (key2613, -1)]

theorem rawRowCheck6259 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form2 = rawRow6259 := by decide +kernel

def row6259 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6259 : row6259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6259 := by decide +kernel

theorem rowEval6259 (x : Key → ℝ) : Integer.Sparse.eval row6259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6259, Integer.Sparse.eval_collectBalanced, rawRowCheck6259]

def rawRow6260 : Integer.Sparse Key := [(key2894, -1), (key2973, -1), (key2852, 2), (key2896, -1), (key2975, -1), (key2736, 2), (key2949, 2), (key2699, -1), (key2802, -1), (key2857, 2), (key2703, -1), (key2806, -1), (key2894, 1), (key2973, 1), (key2852, -2), (key2903, 1), (key2982, 1), (key2647, -2), (key2937, -2), (key2625, 1), (key2779, 1), (key2867, -2), (key2629, 1), (key2783, 1), (key2736, -1), (key2949, -1), (key2699, 1), (key2802, 1), (key2647, 1), (key2937, 1), (key2625, -1), (key2779, -1), (key2746, -1), (key2959, -1), (key2652, 1), (key2942, 1), (key2723, 1), (key2826, 1), (key2637, -1), (key2791, -1)]

theorem rawRowCheck6260 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form2 = rawRow6260 := by decide +kernel

def row6260 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6260 : row6260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6260 := by decide +kernel

theorem rowEval6260 (x : Key → ℝ) : Integer.Sparse.eval row6260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6260, Integer.Sparse.eval_collectBalanced, rawRowCheck6260]

def rawRow6261 : Integer.Sparse Key := [(key2973, -1), (key2894, -1), (key2852, 2), (key2975, -1), (key2896, -1), (key2949, 2), (key2736, 2), (key2802, -1), (key2699, -1), (key2857, 2), (key2806, -1), (key2703, -1), (key2973, 1), (key2894, 1), (key2852, -2), (key2982, 1), (key2903, 1), (key2937, -2), (key2647, -2), (key2779, 1), (key2625, 1), (key2867, -2), (key2783, 1), (key2629, 1), (key2949, -1), (key2736, -1), (key2802, 1), (key2699, 1), (key2937, 1), (key2647, 1), (key2779, -1), (key2625, -1), (key2959, -1), (key2746, -1), (key2942, 1), (key2652, 1), (key2826, 1), (key2723, 1), (key2791, -1), (key2637, -1)]

theorem rawRowCheck6261 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form2 = rawRow6261 := by decide +kernel

def row6261 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6261 : row6261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6261 := by decide +kernel

theorem rowEval6261 (x : Key → ℝ) : Integer.Sparse.eval row6261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6261, Integer.Sparse.eval_collectBalanced, rawRowCheck6261]

def rawRow6262 : Integer.Sparse Key := [(key2857, -1), (key2896, -1), (key2975, 2), (key2703, -1), (key2736, -1), (key2806, 2), (key2894, 2), (key2949, -1), (key2973, -1), (key2699, 2), (key2802, -1), (key2852, -1), (key2867, 1), (key2903, 1), (key2982, -2), (key2629, 1), (key2647, 1), (key2783, -2), (key2894, -2), (key2937, 1), (key2973, 1), (key2625, -2), (key2779, 1), (key2852, 1), (key2826, -1), (key2903, -1), (key2959, 1), (key2982, 1), (key2791, 1), (key2896, 1), (key2942, -1), (key2975, -1), (key2613, -1), (key2647, -1), (key2668, 1), (key2736, 1), (key2609, 1), (key2625, 1), (key2664, -1), (key2699, -1)]

theorem rawRowCheck6262 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form2 = rawRow6262 := by decide +kernel

def row6262 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6262 : row6262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6262 := by decide +kernel

theorem rowEval6262 (x : Key → ℝ) : Integer.Sparse.eval row6262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6262, Integer.Sparse.eval_collectBalanced, rawRowCheck6262]

def rawRow6263 : Integer.Sparse Key := [(key2896, -1), (key2857, -1), (key2975, 2), (key2736, -1), (key2703, -1), (key2894, 2), (key2806, 2), (key2973, -1), (key2949, -1), (key2699, 2), (key2852, -1), (key2802, -1), (key2903, 1), (key2867, 1), (key2982, -2), (key2647, 1), (key2629, 1), (key2894, -2), (key2783, -2), (key2973, 1), (key2937, 1), (key2625, -2), (key2852, 1), (key2779, 1), (key2903, -1), (key2826, -1), (key2982, 1), (key2959, 1), (key2896, 1), (key2791, 1), (key2975, -1), (key2942, -1), (key2647, -1), (key2613, -1), (key2736, 1), (key2668, 1), (key2625, 1), (key2609, 1), (key2699, -1), (key2664, -1)]

theorem rawRowCheck6263 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form2 = rawRow6263 := by decide +kernel

def row6263 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck6263 : row6263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6263 := by decide +kernel

theorem rowEval6263 (x : Key → ℝ) : Integer.Sparse.eval row6263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6263, Integer.Sparse.eval_collectBalanced, rawRowCheck6263]

def rawRow6264 : Integer.Sparse Key := [(key2896, -1), (key2975, -1), (key2857, 2), (key2894, -1), (key2973, -1), (key2736, 2), (key2949, 2), (key2703, -1), (key2806, -1), (key2852, 2), (key2699, -1), (key2802, -1), (key2903, 1), (key2982, 1), (key2867, -2), (key2894, 1), (key2973, 1), (key2647, -2), (key2937, -2), (key2629, 1), (key2783, 1), (key2852, -2), (key2625, 1), (key2779, 1), (key2746, -1), (key2959, -1), (key2723, 1), (key2826, 1), (key2652, 1), (key2942, 1), (key2637, -1), (key2791, -1), (key2736, -1), (key2949, -1), (key2647, 1), (key2937, 1), (key2699, 1), (key2802, 1), (key2625, -1), (key2779, -1)]

theorem rawRowCheck6264 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form2 = rawRow6264 := by decide +kernel

def row6264 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6264 : row6264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6264 := by decide +kernel

theorem rowEval6264 (x : Key → ℝ) : Integer.Sparse.eval row6264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6264, Integer.Sparse.eval_collectBalanced, rawRowCheck6264]

def rawRow6265 : Integer.Sparse Key := [(key2975, -1), (key2896, -1), (key2857, 2), (key2973, -1), (key2894, -1), (key2949, 2), (key2736, 2), (key2806, -1), (key2703, -1), (key2852, 2), (key2802, -1), (key2699, -1), (key2982, 1), (key2903, 1), (key2867, -2), (key2973, 1), (key2894, 1), (key2937, -2), (key2647, -2), (key2783, 1), (key2629, 1), (key2852, -2), (key2779, 1), (key2625, 1), (key2959, -1), (key2746, -1), (key2826, 1), (key2723, 1), (key2942, 1), (key2652, 1), (key2791, -1), (key2637, -1), (key2949, -1), (key2736, -1), (key2937, 1), (key2647, 1), (key2802, 1), (key2699, 1), (key2779, -1), (key2625, -1)]

theorem rawRowCheck6265 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form2 = rawRow6265 := by decide +kernel

def row6265 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6265 : row6265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6265 := by decide +kernel

theorem rowEval6265 (x : Key → ℝ) : Integer.Sparse.eval row6265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6265, Integer.Sparse.eval_collectBalanced, rawRowCheck6265]

def rawRow6266 : Integer.Sparse Key := [(key2723, -1), (key2723, -1), (key2746, 2), (key2826, -1), (key2826, -1), (key2867, 2), (key2867, 2), (key2903, -1), (key2903, -1), (key2959, 2), (key2982, -1), (key2982, -1), (key2637, 1), (key2637, 1), (key2652, -2), (key2791, 1), (key2791, 1), (key2857, -2), (key2857, -2), (key2896, 1), (key2896, 1), (key2942, -2), (key2975, 1), (key2975, 1), (key2629, -1), (key2629, -1), (key2647, 1), (key2647, 1), (key2703, 1), (key2703, 1), (key2736, -1), (key2736, -1), (key2783, -1), (key2783, -1), (key2806, 1), (key2806, 1), (key2937, 1), (key2937, 1), (key2949, -1), (key2949, -1)]

theorem rawRowCheck6266 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form2 = rawRow6266 := by decide +kernel

def row6266 : Integer.Sparse Key := [(key2629, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2703, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2783, -2), (key2791, 2), (key2806, 2), (key2826, -2), (key2857, -4), (key2867, 4), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

theorem rowCheck6266 : row6266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6266 := by decide +kernel

theorem rowEval6266 (x : Key → ℝ) : Integer.Sparse.eval row6266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6266, Integer.Sparse.eval_collectBalanced, rawRowCheck6266]

def rawRow6267 : Integer.Sparse Key := [(key2723, -1), (key2746, -1), (key2723, 2), (key2867, -1), (key2903, -1), (key2826, 2), (key2903, 2), (key2826, -1), (key2867, -1), (key2982, 2), (key2959, -1), (key2982, -1), (key2637, 1), (key2652, 1), (key2637, -2), (key2857, 1), (key2896, 1), (key2791, -2), (key2896, -2), (key2791, 1), (key2857, 1), (key2975, -2), (key2942, 1), (key2975, 1), (key2613, -1), (key2647, -1), (key2613, 1), (key2629, 1), (key2668, 1), (key2736, 1), (key2668, -1), (key2703, -1), (key2806, -1), (key2894, -1), (key2783, 1), (key2894, 1), (key2949, 1), (key2973, 1), (key2937, -1), (key2973, -1)]

theorem rawRowCheck6267 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form2 = rawRow6267 := by decide +kernel

def row6267 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6267 : row6267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6267 := by decide +kernel

theorem rowEval6267 (x : Key → ℝ) : Integer.Sparse.eval row6267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6267, Integer.Sparse.eval_collectBalanced, rawRowCheck6267]

def rawRow6268 : Integer.Sparse Key := [(key2746, -1), (key2723, -1), (key2723, 2), (key2903, -1), (key2867, -1), (key2903, 2), (key2826, 2), (key2867, -1), (key2826, -1), (key2982, 2), (key2982, -1), (key2959, -1), (key2652, 1), (key2637, 1), (key2637, -2), (key2896, 1), (key2857, 1), (key2896, -2), (key2791, -2), (key2857, 1), (key2791, 1), (key2975, -2), (key2975, 1), (key2942, 1), (key2647, -1), (key2613, -1), (key2629, 1), (key2613, 1), (key2736, 1), (key2668, 1), (key2703, -1), (key2668, -1), (key2894, -1), (key2806, -1), (key2894, 1), (key2783, 1), (key2973, 1), (key2949, 1), (key2973, -1), (key2937, -1)]

theorem rawRowCheck6268 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form2 = rawRow6268 := by decide +kernel

def row6268 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6268 : row6268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6268 := by decide +kernel

theorem rowEval6268 (x : Key → ℝ) : Integer.Sparse.eval row6268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6268, Integer.Sparse.eval_collectBalanced, rawRowCheck6268]

def rawRow6269 : Integer.Sparse Key := [(key2826, -1), (key2826, -1), (key2959, 2), (key2723, -1), (key2723, -1), (key2867, 2), (key2867, 2), (key2982, -1), (key2982, -1), (key2746, 2), (key2903, -1), (key2903, -1), (key2791, 1), (key2791, 1), (key2942, -2), (key2637, 1), (key2637, 1), (key2857, -2), (key2857, -2), (key2975, 1), (key2975, 1), (key2652, -2), (key2896, 1), (key2896, 1), (key2783, -1), (key2783, -1), (key2937, 1), (key2937, 1), (key2806, 1), (key2806, 1), (key2949, -1), (key2949, -1), (key2629, -1), (key2629, -1), (key2703, 1), (key2703, 1), (key2647, 1), (key2647, 1), (key2736, -1), (key2736, -1)]

theorem rawRowCheck6269 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form2 = rawRow6269 := by decide +kernel

def row6269 : Integer.Sparse Key := [(key2629, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2703, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2783, -2), (key2791, 2), (key2806, 2), (key2826, -2), (key2857, -4), (key2867, 4), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

theorem rowCheck6269 : row6269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6269 := by decide +kernel

theorem rowEval6269 (x : Key → ℝ) : Integer.Sparse.eval row6269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6269, Integer.Sparse.eval_collectBalanced, rawRowCheck6269]

def rawRow6270 : Integer.Sparse Key := [(key2826, -1), (key2959, -1), (key2826, 2), (key2867, -1), (key2982, -1), (key2723, 2), (key2982, 2), (key2723, -1), (key2867, -1), (key2903, 2), (key2746, -1), (key2903, -1), (key2791, 1), (key2942, 1), (key2791, -2), (key2857, 1), (key2975, 1), (key2637, -2), (key2975, -2), (key2637, 1), (key2857, 1), (key2896, -2), (key2652, 1), (key2896, 1), (key2668, -1), (key2937, -1), (key2668, 1), (key2783, 1), (key2613, 1), (key2949, 1), (key2613, -1), (key2806, -1), (key2703, -1), (key2973, -1), (key2629, 1), (key2973, 1), (key2736, 1), (key2894, 1), (key2647, -1), (key2894, -1)]

theorem rawRowCheck6270 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form2 = rawRow6270 := by decide +kernel

def row6270 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6270 : row6270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6270 := by decide +kernel

theorem rowEval6270 (x : Key → ℝ) : Integer.Sparse.eval row6270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6270, Integer.Sparse.eval_collectBalanced, rawRowCheck6270]

def rawRow6271 : Integer.Sparse Key := [(key2959, -1), (key2826, -1), (key2826, 2), (key2982, -1), (key2867, -1), (key2982, 2), (key2723, 2), (key2867, -1), (key2723, -1), (key2903, 2), (key2903, -1), (key2746, -1), (key2942, 1), (key2791, 1), (key2791, -2), (key2975, 1), (key2857, 1), (key2975, -2), (key2637, -2), (key2857, 1), (key2637, 1), (key2896, -2), (key2896, 1), (key2652, 1), (key2937, -1), (key2668, -1), (key2783, 1), (key2668, 1), (key2949, 1), (key2613, 1), (key2806, -1), (key2613, -1), (key2973, -1), (key2703, -1), (key2973, 1), (key2629, 1), (key2894, 1), (key2736, 1), (key2894, -1), (key2647, -1)]

theorem rawRowCheck6271 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form2 = rawRow6271 := by decide +kernel

def row6271 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6271 : row6271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6271 := by decide +kernel

theorem rowEval6271 (x : Key → ℝ) : Integer.Sparse.eval row6271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6271, Integer.Sparse.eval_collectBalanced, rawRowCheck6271]

end MUB6.Certificate.GramRows

end OAI
