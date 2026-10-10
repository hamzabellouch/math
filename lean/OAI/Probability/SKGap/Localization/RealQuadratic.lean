import Mathlib
import OAI.Probability.SKGap.Localization.Quadratic
import OAI.Probability.SKGap.Matrix.LiftMatrix

namespace OAI

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
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap.RealComplex
open SKGap.ComplexSpectral
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realQuadratic (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, ∑ k, x i * M i k * x k

omit [DecidableEq ι] in
lemma quadratic_lift_split (M : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    quadratic (liftMatrix M) x = realQuadratic M (reVec x)+realQuadratic M (imVec x) := by
  change (∑ i, star (x i)*∑ k, (M i k:ℂ)*x k).re = _
  simp only [Finset.mul_sum,Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,realQuadratic,reVec,imVec,PiLp.toLp_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq ι] in
lemma lowerRayleigh_lift_ge [Nonempty ι] {M : Matrix ι ι ℝ} {c : ℝ}
    (hc : ∀ x : EuclideanSpace ℝ ι, c*‖x‖^2 ≤ realQuadratic M x) :
    c ≤ lowerRayleigh (liftMatrix M) := by
  apply lowerRayleigh_ge
  intro x hx
  have hn : ‖x‖ = 1 := by simpa only [unitSphere,Metric.mem_sphere,dist_zero_right] using hx
  have h := add_le_add (hc (reVec x)) (hc (imVec x))
  rw [← mul_add,← vec_norm_split,hn,one_pow,mul_one,← quadratic_lift_split] at h
  exact h

lemma quadratic_eq_inner (M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    quadratic M x = (inner ℂ x (clin M x)).re := by
  rw [PiLp.inner_apply]
  change (∑ i, star (x i)*(∑ k, M i k*x k)).re =
    (∑ i, (∑ k, M i k*x k)*star (x i)).re
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma lowerRayleigh_ge_neg_norm [Nonempty ι] (M : Matrix ι ι ℂ) :
    -‖clin M‖ ≤ lowerRayleigh M := by
  apply lowerRayleigh_ge
  intro x hx
  have hn : ‖x‖ = 1 := by simpa only [unitSphere,Metric.mem_sphere,dist_zero_right] using hx
  rw [quadratic_eq_inner]
  have hh := (norm_inner_le_norm (𝕜 := ℂ) x (clin M x)).trans
    (mul_le_mul_of_nonneg_left ((clin M).le_opNorm x) (norm_nonneg x))
  rw [hn,mul_one,one_mul] at hh
  exact (neg_le_neg ((Complex.abs_re_le_norm _).trans hh)).trans (neg_abs_le _)

lemma lowerRayleigh_neg_lift_ge [Nonempty ι] (M : Matrix ι ι ℝ) :
    -opNorm M ≤ lowerRayleigh (-liftMatrix M) := by
  have h := lowerRayleigh_ge_neg_norm (-liftMatrix M)
  have he : clin (-liftMatrix M) = -clin (liftMatrix M) := by
    ext x i
    change (∑ k, -(liftMatrix M i k)*x k) = -(∑ k, liftMatrix M i k*x k)
    simp only [neg_mul,Finset.sum_neg_distrib]
  rw [he,norm_neg,operator_norm_lift] at h
  exact h

end SKGap.RealComplex

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
end
end
end

end OAI
