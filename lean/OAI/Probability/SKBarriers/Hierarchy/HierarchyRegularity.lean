import Mathlib
import OAI.Probability.SKBarriers.Calculus.MarginalSecondDerivative
import OAI.Probability.SKBarriers.Gaussian.LogDerivatives

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
section ClosedHierarchy
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BoundedDerivs.log_gaussian_integral_exp {f : E × ℝ → ℝ} (h : BoundedDerivs f) :
    BoundedDerivs (fun x => Real.log (∫ y, Real.exp (f (x,y)) ∂gaussianReal 0 1)) := by
  obtain ⟨hf,C,D,hC,hD,hb,hbb⟩ := h
  have hd := hf.differentiable (by norm_num)
  have hg : HasExpGrowth (fun x => Real.exp (f x)) := by
    simpa only [one_mul] using exp_mul_growth_of_fderiv_bound f hd C hC hb 1
  have hg₁ := fderiv_exp_growth f hd hg hC hb
  have hg₂ := fderiv_fderiv_exp_growth f hf hg hC hD hb hbb
  have hp : ∀ x, 0 < ∫ y, Real.exp (f (x,y)) ∂gaussianReal 0 1 := by
    intro x
    apply integral_exp_pos
    exact hg.integrable_gaussian_section hf.exp.continuous x
  apply log_boundedDerivs_of_relative_bounds _
    (BoundedDerivs.exp_smooth_integral ⟨hf,C,D,hC,hD,hb,hbb⟩) hp hC
    (show 0 ≤ D+C*C by positivity)
  · intro x
    apply (norm_fderiv_gaussian_integral_le _ (hf.exp.of_le (by norm_num)) hg hg₁ x).trans
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (ae_of_all _ (fun y =>
      ContinuousLinearMap.opNorm_nonneg (fderiv ℝ (fun z => Real.exp (f z)) (x,y))))
    · exact (hg.integrable_gaussian_section hf.exp.continuous x).const_mul C
    · apply ae_of_all
      intro y
      dsimp only
      rw [fderiv_exp (hd (x,y)), norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_left (hb (x,y)) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  · intro x
    apply (norm_fderiv_fderiv_gaussian_integral_le _ hf.exp hg hg₁ hg₂ x).trans
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (ae_of_all _ (fun y =>
      ContinuousLinearMap.opNorm_nonneg (fderiv ℝ (fderiv ℝ (fun z => Real.exp (f z))) (x,y))))
    · exact (hg.integrable_gaussian_section hf.exp.continuous x).const_mul (D+C*C)
    · exact ae_of_all _ (fun y => norm_fderiv_fderiv_exp_le f hf hC hD hb hbb (x,y))

theorem BoundedDerivs.positiveGaussianLogStep {f : E × ℝ → ℝ} (h : BoundedDerivs f) (m : ℝ) :
    BoundedDerivs (positiveGaussianLogStep m f) := by
  have hh := ((h.const_mul m).log_gaussian_integral_exp).const_mul m⁻¹
  change BoundedDerivs (fun x => Real.log
    (∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1) / m)
  simpa only [div_eq_mul_inv, mul_comm] using hh

end ClosedHierarchy
end SK.Analytic

end
end
end
end
end
end

end OAI
