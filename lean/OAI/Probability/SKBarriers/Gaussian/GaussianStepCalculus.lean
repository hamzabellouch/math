import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianZeroMass

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
section StepCalculus
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def gaussianStepLaw (m : ℝ) (f : E × ℝ → ℝ) (x : E) : Measure ℝ :=
  (gaussianReal 0 1).tilted (fun y => m*f (x,y))

theorem BoundedDerivs.exp_integrable {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x : E) : Integrable (fun y => Real.exp (m*f (x,y))) (gaussianReal 0 1) := by
  obtain ⟨hf,C,D,hC,hD,hb,hbb⟩ := hf
  exact (exp_mul_growth_of_fderiv_bound f (hf.differentiable (by norm_num)) C hC hb m).integrable_gaussian_section (Real.continuous_exp.comp (continuous_const.mul hf.continuous)) x

theorem gaussianStepLaw_probability {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x : E) : IsProbabilityMeasure (gaussianStepLaw m f x) :=
  isProbabilityMeasure_tilted (hf.exp_integrable m x)

theorem gaussianTransition_density {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x : E) (y : ℝ) :
    Real.exp (m*(f (x,y)-gaussianStep m f x)) =
      Real.exp (m*f (x,y)) / (∫ z, Real.exp (m*f (x,z)) ∂gaussianReal 0 1) := by
  by_cases hm : m = 0
  · subst m
    simp
  · have hpos := integral_exp_pos (hf.exp_integrable m x)
    rw [gaussianStep,ite_eq_right hm,positiveGaussianLogStep]
    have he : m*(f (x,y)-Real.log (∫ z, Real.exp (m*f (x,z)) ∂gaussianReal 0 1)/m) =
        m*f (x,y)-Real.log (∫ z, Real.exp (m*f (x,z)) ∂gaussianReal 0 1) := by
      rw [mul_sub, mul_div_cancel₀ _ hm]
    rw [he,Real.exp_sub,Real.exp_log hpos]

theorem gaussianTransition_integral_one {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x : E) :
    (∫ y, Real.exp (m*(f (x,y)-gaussianStep m f x)) ∂gaussianReal 0 1) = 1 := by
  simp_rw [gaussianTransition_density hf]
  rw [integral_div,div_self (integral_exp_pos (hf.exp_integrable m x)).ne']

theorem gaussianStepLaw_integral {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (m : ℝ) (x : E) (g : ℝ → F) :
    (∫ y, g y ∂gaussianStepLaw m f x) =
      ∫ y, Real.exp (m*(f (x,y)-gaussianStep m f x)) • g y ∂gaussianReal 0 1 := by
  rw [gaussianStepLaw,integral_tilted]
  simp_rw [gaussianTransition_density hf]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianStepLaw_zero (f : E × ℝ → ℝ) (x : E) :
    gaussianStepLaw 0 f x = gaussianReal 0 1 := by
  simp [gaussianStepLaw]

theorem BoundedDerivs.gaussianStep {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (m : ℝ) :
    BoundedDerivs (gaussianStep m f) := by
  unfold SK.Analytic.gaussianStep
  split
  · exact hf.gaussian_integral
  · exact hf.positiveGaussianLogStep m

theorem fderiv_gaussianStep {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x : E) :
    fderiv ℝ (gaussianStep m f) x =
      ∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianStepLaw m f x := by
  classical
  obtain ⟨hfd,C,D,hC,hD,hb,hbb⟩ := hf
  have hd := hfd.differentiable (by norm_num)
  have hg := exp_mul_growth_of_fderiv_bound f hd C hC hb m
  have hmf : BoundedDerivs (fun z => m*f z) :=
    BoundedDerivs.const_mul ⟨hfd,C,D,hC,hD,hb,hbb⟩ m
  have hmfb : ∀ z, ‖fderiv ℝ (fun z => m*f z) z‖ ≤ |m| * C := by
    intro z
    rw [((hd z).hasFDerivAt.const_mul m).fderiv, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb z) (abs_nonneg m)
  have hg₁ := fderiv_exp_growth _ (hmf.1.differentiable (by norm_num)) hg
    (mul_nonneg (abs_nonneg m) hC) hmfb
  by_cases hm : m = 0
  · subst m
    rw [gaussianStepLaw_zero]
    have he : SK.Analytic.gaussianStep 0 f = (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
      funext x
      simp only [SK.Analytic.gaussianStep,ite_true]
    rw [he]
    exact fderiv_gaussian_integral f (hfd.of_le (by norm_num))
      (growth_of_fderiv_bound f hd hC hb)
      (HasExpGrowth.of_bounded hC hb) x
  · let Z : E → ℝ := fun x => ∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1
    have hZ := hmf.exp_smooth_integral
    have hp : Z x ≠ 0 := (integral_exp_pos
      (BoundedDerivs.exp_integrable ⟨hfd,C,D,hC,hD,hb,hbb⟩ m x)).ne'
    have he : gaussianStep m f = fun x => Real.log (Z x)/m := by
      funext x
      simp only [gaussianStep,ite_eq_right hm,positiveGaussianLogStep,Z]
    rw [he]
    have hder := ((hZ.differentiable (by norm_num) x).hasFDerivAt.log hp).mul_const m⁻¹
    simp only [div_eq_mul_inv] at ⊢
    rw [hder.fderiv]
    have hi := fderiv_gaussian_integral (fun z => Real.exp (m*f z))
      ((contDiff_const.mul hfd).exp.of_le (by norm_num)) hg hg₁ x
    change (m⁻¹ • ((Z x)⁻¹ • fderiv ℝ Z x)) = _
    rw [hi,← integral_smul,← integral_smul,gaussianStepLaw,integral_tilted]
    apply integral_congr_ae
    filter_upwards [] with y
    have hdexp := ((hd (x,y)).hasFDerivAt.const_mul m).exp.fderiv
    rw [hdexp]
    ext v
    simp only [smul_apply,smul_eq_mul,leftRestrict,
      ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply]
    dsimp only [Z] at hp ⊢
    field_simp [hm,hp]

end StepCalculus
end SK.Analytic

end
end
end
end
end
end

end OAI
