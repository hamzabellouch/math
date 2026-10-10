import Mathlib
import OAI.Probability.SKRatio.Matrices.LiftMatrix

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKRatioGaussian.RealComplex
open scoped Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realPart (M : Matrix ι ι ℂ) : Matrix ι ι ℝ := M.map Complex.re

lemma norm_realPart_le (M : Matrix ι ι ℂ) : ‖realPart M‖ ≤ ‖M‖ := by
  rw [Matrix.frobenius_norm_def,Matrix.frobenius_norm_def]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro k _
  simp only [realPart,Matrix.map_apply,Real.rpow_two]
  exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (M i k)) 2

omit [Fintype ι] [DecidableEq ι] in
lemma realPart_sub (M N : Matrix ι ι ℂ) : realPart (M-N) = realPart M-realPart N := by
  ext i k; simp [realPart]
omit [Fintype ι] [DecidableEq ι] in
lemma realPart_liftMatrix (M : Matrix ι ι ℝ) : realPart (liftMatrix M) = M := by
  ext i k; simp [realPart,liftMatrix]

lemma realPart_lipschitz : LipschitzWith 1 (realPart (ι := ι)) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul,realPart_sub] using norm_realPart_le (M-N)

omit [DecidableEq ι] in
lemma reVec_norm_le (x : EuclideanSpace ℂ ι) : ‖reVec x‖ ≤ ‖x‖ := by
  have h := vec_norm_split x
  nlinarith [sq_nonneg ‖imVec x‖,norm_nonneg (reVec x),norm_nonneg x]

lemma realPart_operator (M : Matrix ι ι ℂ) (x : EuclideanSpace ℝ ι) :
    rlin (realPart M) x = reVec (clin M (liftVec x)) := by
  ext i
  change (∑ k, (M i k).re*x k) = (∑ k, M i k*(x k : ℂ)).re
  simp

lemma operator_realPart_le (M : Matrix ι ι ℂ) : opNorm (realPart M) ≤ ‖clin M‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [realPart_operator]
  exact (reVec_norm_le _).trans ((clin M).le_opNorm (liftVec x) |>.trans_eq (by rw [norm_liftVec]))

lemma liftMatrix_inverse {M : Matrix ι ι ℝ} (hM : IsUnit M) :
    liftMatrix M⁻¹ = (liftMatrix M)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← liftMatrix_mul,Matrix.mul_nonsing_inv M (M.isUnit_iff_isUnit_det.mp hM),liftMatrix_one]

end SKRatioGaussian.RealComplex

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
