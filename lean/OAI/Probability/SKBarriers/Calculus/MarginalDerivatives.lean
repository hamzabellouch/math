import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.Basic
import OAI.Probability.SKBarriers.Gaussian.GaussianDomination
import OAI.Probability.SKBarriers.Scalar.RawDerivatives

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section MarginalDerivatives
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def leftRestrict : ((E × ℝ) →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip (ContinuousLinearMap.inl ℝ E ℝ)

theorem leftRestrict_apply_bound (A : (E × ℝ) →L[ℝ] F) : ‖leftRestrict A‖ ≤ ‖A‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℝ E ℝ) (norm_nonneg A)).trans_eq (mul_one _))

theorem leftRestrict_norm : ‖leftRestrict (E := E) (F := F)‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun A => (leftRestrict_apply_bound A).trans_eq (one_mul _).symm)

theorem leftRestrict_hasFDerivAt (f : E × ℝ → F) (hd : Differentiable ℝ f) (x : E) (y : ℝ) :
    HasFDerivAt (fun z => f (z,y)) (leftRestrict (fderiv ℝ f (x,y))) x := by
  exact (hd (x,y)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))

theorem fderiv_gaussian_integral (f : E × ℝ → F) (hf : ContDiff ℝ 1 f)
    (hg : HasExpGrowth f) (hg₁ : HasExpGrowth (fderiv ℝ f)) (x : E) :
    fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) x =
      ∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianReal 0 1 := by
  exact (hasFDerivAt_gaussian_integral f _ hf.continuous
    (leftRestrict.continuous.comp ((hf.fderiv_right (m := 0) (by norm_num)).continuous))
    hg (hg₁.clm leftRestrict)
    (leftRestrict_hasFDerivAt f (hf.differentiable (by norm_num))) x).fderiv

theorem norm_fderiv_gaussian_integral_le (f : E × ℝ → F) (hf : ContDiff ℝ 1 f)
    (hg : HasExpGrowth f) (hg₁ : HasExpGrowth (fderiv ℝ f)) (x : E) :
    ‖fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) x‖ ≤
      ∫ y, ‖fderiv ℝ f (x,y)‖ ∂gaussianReal 0 1 := by
  rw [fderiv_gaussian_integral f hf hg hg₁ x]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono
  · exact ((hg₁.clm leftRestrict).integrable_gaussian_section
      (leftRestrict.continuous.comp ((hf.fderiv_right (m := 0) (by norm_num)).continuous)) x).norm
  · exact (hg₁.integrable_gaussian_section ((hf.fderiv_right (m := 0) (by norm_num)).continuous) x).norm
  · exact fun y => leftRestrict_apply_bound _

end MarginalDerivatives
end SK.Analytic

end
end
end
end
end
end

end OAI
