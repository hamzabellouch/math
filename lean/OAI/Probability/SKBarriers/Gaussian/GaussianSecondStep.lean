import Mathlib
import OAI.Probability.SKBarriers.Gaussian.LogDerivatives
import OAI.Probability.SKBarriers.Gaussian.GaussianStepCalculus

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
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
section SecondStep
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_fderiv_const_mul (f : E → ℝ) (hf : ContDiff ℝ 2 f) (c : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (fun z => c*f z)) x = c • fderiv ℝ (fderiv ℝ f) x := by
  have he : fderiv ℝ (fun z => c*f z) = fun z => c • fderiv ℝ f z := by
    funext z
    exact ((hf.differentiable (by norm_num) z).hasFDerivAt.const_mul c).fderiv
  rw [he]
  exact (((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt.const_smul c).fderiv

theorem BoundedDerivs.exp_growths {f : E → ℝ} (hf : BoundedDerivs f) (m : ℝ) :
    HasExpGrowth (fun x => Real.exp (m*f x)) ∧
    HasExpGrowth (fderiv ℝ (fun x => Real.exp (m*f x))) ∧
    HasExpGrowth (fderiv ℝ (fderiv ℝ (fun x => Real.exp (m*f x)))) := by
  obtain ⟨hfd,C,D,hC,hD,hb,hbb⟩ := hf.const_mul m
  have hg : HasExpGrowth (fun x => Real.exp (m*f x)) := by
    simpa only [one_mul] using exp_mul_growth_of_fderiv_bound (fun x => m*f x)
      (hfd.differentiable (by norm_num)) C hC hb 1
  exact ⟨hg,fderiv_exp_growth _ (hfd.differentiable (by norm_num)) hg hC hb,
    fderiv_fderiv_exp_growth _ hfd hg hC hD hb hbb⟩

theorem fderiv_fderiv_gaussianStep_nonzero {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    {m : ℝ} (hm : m ≠ 0) (x : E) :
    fderiv ℝ (fderiv ℝ (gaussianStep m f)) x =
      m⁻¹ • (((∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1)⁻¹) •
        (∫ y, secondLeftRestrict (fderiv ℝ (fderiv ℝ (fun z => Real.exp (m*f z))) (x,y))
          ∂gaussianReal 0 1) +
      (-((∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1)^2)⁻¹ •
        (∫ y, leftRestrict (fderiv ℝ (fun z => Real.exp (m*f z)) (x,y)) ∂gaussianReal 0 1)).smulRight
        (∫ y, leftRestrict (fderiv ℝ (fun z => Real.exp (m*f z)) (x,y)) ∂gaussianReal 0 1)) := by
  let Z : E → ℝ := fun x => ∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1
  have hZ := (hf.const_mul m).exp_smooth_integral
  have hp (z : E) : Z z ≠ 0 := (integral_exp_pos (hf.exp_integrable m z)).ne'
  have he : gaussianStep m f = fun z => m⁻¹*Real.log (Z z) := by
    funext z
    simp only [gaussianStep,ite_eq_right hm,positiveGaussianLogStep,Z,div_eq_mul_inv,mul_comm]
  have hL : ContDiff ℝ 2 (fun z => Real.log (Z z)) := hZ.log hp
  obtain ⟨hg,hg₁,hg₂⟩ := hf.exp_growths m
  rw [he,fderiv_fderiv_const_mul _ hL,fderiv_fderiv_log _ hZ hp]
  rw [fderiv_gaussian_integral _ ((contDiff_const.mul hf.1).exp.of_le (by norm_num)) hg hg₁]
  rw [fderiv_fderiv_gaussian_integral _ (contDiff_const.mul hf.1).exp hg hg₁ hg₂]

theorem fderiv_fderiv_gaussianStep_zero {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (x : E) :
    fderiv ℝ (fderiv ℝ (gaussianStep 0 f)) x =
      ∫ y, secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y)) ∂gaussianReal 0 1 := by
  have he : gaussianStep 0 f = fun x => ∫ y, f (x,y) ∂gaussianReal 0 1 := by
    funext z
    simp only [gaussianStep,ite_true]
  rw [he]
  obtain ⟨hfd,C,D,hC,hD,hb,hbb⟩ := hf
  exact fderiv_fderiv_gaussian_integral f hfd
    (growth_of_fderiv_bound f (hfd.differentiable (by norm_num)) hC hb)
    (HasExpGrowth.of_bounded hC hb) (HasExpGrowth.of_bounded hD hbb) x

theorem integrable_exp_smul_of_bounded {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (m : ℝ) (x : E)
    (g : ℝ → F) (hg : Continuous g) {C : ℝ} (hb : ∀ y, ‖g y‖ ≤ C) :
    Integrable (fun y => Real.exp (m*f (x,y)) • g y) (gaussianReal 0 1) := by
  apply ((hf.exp_integrable m x).const_mul C).mono'
    ((Real.continuous_exp.comp (continuous_const.mul
      (hf.1.continuous.comp (continuous_const.prodMk continuous_id)))).smul hg).aestronglyMeasurable
  filter_upwards [] with y
  change ‖Real.exp (m*f (x,y)) • g y‖ ≤ C * Real.exp (m*f (x,y))
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (hb y) (Real.exp_pos _).le).trans_eq (mul_comm _ _)

end SecondStep
end SK.Analytic

end
end
end
end
end
end
end

end OAI
