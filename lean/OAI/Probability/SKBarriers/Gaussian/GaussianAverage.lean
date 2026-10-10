import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianCovarianceStep

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
section GaussianAverage
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def gaussianAverage (m : ℝ) (f : E × ℝ → ℝ) (g : E × ℝ → F) (x : E) : F :=
  ∫ y, g (x,y) ∂gaussianStepLaw m f x

theorem gaussianAverage_continuous {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) {g : E × ℝ → F} (hg : Continuous g) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z, ‖g z‖ ≤ C) : Continuous (gaussianAverage m f g) := by
  have he := (hf.exp_growths m).1
  have hce : Continuous (fun z => Real.exp (m*f z)) :=
    Real.continuous_exp.comp (continuous_const.mul hf.1.continuous)
  have hweightedGrowth : HasExpGrowth (fun point => Real.exp (m*f point) • g point) :=
    he.congr_bound hC (fun point => by
      rw [norm_smul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hb point) (norm_nonneg _))
  have hn := hweightedGrowth.continuous_gaussian_integral (hce.smul hg)
  have hd := he.continuous_gaussian_integral hce
  have hp (x : E) : (∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1) ≠ 0 :=
    (integral_exp_pos (hf.exp_integrable m x)).ne'
  have ha : gaussianAverage m f g = fun x =>
      (∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1)⁻¹ •
        ∫ y, Real.exp (m*f (x,y)) • g (x,y) ∂gaussianReal 0 1 := by
    funext x
    exact gaussianStepLaw_integral_inv_smul m f x _
  rw [ha]
  exact (hd.inv₀ hp).smul hn

omit [NormedSpace ℝ F] in
theorem integrable_gaussianStep_of_bounded {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x : E) {g : ℝ → F} (hg : Continuous g) {C : ℝ}
    (hb : ∀ y, ‖g y‖ ≤ C) : Integrable g (gaussianStepLaw m f x) := by
  let := gaussianStepLaw_probability hf m x
  exact Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ hb)

theorem gaussianAverage_norm_le {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) {g : E × ℝ → F} {C : ℝ}
    (hb : ∀ z, ‖g z‖ ≤ C) (x : E) : ‖gaussianAverage m f g x‖ ≤ C := by
  let := gaussianStepLaw_probability hf m x
  simpa only [gaussianAverage,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := gaussianStepLaw m f x)
      (ae_of_all _ (fun y => hb (x,y)))

def prefixGradient (f : E × ℝ → ℝ) (u : E) (z : E × ℝ) : ℝ :=
  fderiv ℝ f z (u,0)

def prefixHessian (f : E × ℝ → ℝ) (u v : E) (z : E × ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ f) z (u,0) (v,0)

theorem prefixGradient_data {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (u : E) :
    Continuous (prefixGradient f u) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖prefixGradient f u z‖ ≤ C := by
  obtain ⟨hc,C,D,hC,hD,hb,hbb⟩ := hf
  refine ⟨(hc.continuous_fderiv (by norm_num)).clm_apply continuous_const,
    C*‖(u,(0:ℝ))‖,mul_nonneg hC (norm_nonneg _),fun z => ?_⟩
  exact ((fderiv ℝ f z).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _))

theorem prefixHessian_data {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (u v : E) :
    Continuous (prefixHessian f u v) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖prefixHessian f u v z‖ ≤ C := by
  obtain ⟨hc,C,D,hC,hD,hb,hbb⟩ := hf
  refine ⟨((hc.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
    continuous_const |>.clm_apply continuous_const,
    D*‖(u,(0:ℝ))‖*‖(v,(0:ℝ))‖,by positivity,fun z => ?_⟩
  exact ((fderiv ℝ (fderiv ℝ f) z (u,0)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ f) z).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbb z) (norm_nonneg _))) (norm_nonneg _))

theorem fderiv_gaussianStep_apply {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x u : E) :
    fderiv ℝ (gaussianStep m f) x u = gaussianAverage m f (prefixGradient f u) x := by
  rw [fderiv_gaussianStep hf]
  have hc : Continuous (fun y : ℝ => leftRestrict (fderiv ℝ f (x,y))) := leftRestrict.continuous.comp
    (hf.1.continuous_fderiv (by norm_num) |>.comp (continuous_const.prodMk continuous_id))
  obtain ⟨hcd,C,D,hC,hD,hb,hbb⟩ := hf
  have hi := integrable_gaussianStep_of_bounded (show BoundedDerivs f from
    ⟨hcd,C,D,hC,hD,hb,hbb⟩) m x hc
    (fun y => (leftRestrict_apply_bound (fderiv ℝ f (x,y))).trans (hb (x,y)))
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

theorem fderiv_fderiv_gaussianStep_apply {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x u v : E) :
    fderiv ℝ (fderiv ℝ (gaussianStep m f)) x u v =
      gaussianAverage m f (prefixHessian f u v) x + m*(
        gaussianAverage m f (fun z => prefixGradient f u z*prefixGradient f v z) x -
        gaussianAverage m f (prefixGradient f u) x*gaussianAverage m f (prefixGradient f v) x) := by
  let X : ℝ → E →L[ℝ] ℝ := fun y => leftRestrict (fderiv ℝ f (x,y))
  let Y : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun y => secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y))
  obtain ⟨hc,C,D,hC,hD,hb,hbb⟩ := hf
  have hf : BoundedDerivs f := ⟨hc,C,D,hC,hD,hb,hbb⟩
  have hX : Continuous X := leftRestrict.continuous.comp
    (hc.continuous_fderiv (by norm_num) |>.comp (continuous_const.prodMk continuous_id))
  have hY : Continuous Y := secondLeftRestrict.continuous.comp
    ((hc.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num) |>.comp
      (continuous_const.prodMk continuous_id))
  have bX (y : ℝ) : ‖X y‖ ≤ C := (leftRestrict_apply_bound _).trans (hb _)
  have bY (y : ℝ) : ‖Y y‖ ≤ D := (secondLeftRestrict_apply_bound _).trans (hbb _)
  have hXX : Continuous (fun y => (X y).smulRight (X y)) :=
    ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp hX).clm_apply hX
  have bXX (y : ℝ) : ‖(X y).smulRight (X y)‖ ≤ C*C := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (bX y) (bX y) (norm_nonneg _) hC
  have iX := integrable_gaussianStep_of_bounded hf m x hX bX
  have iY := integrable_gaussianStep_of_bounded (F := E →L[ℝ] E →L[ℝ] ℝ) hf m x hY bY
  have iXX := integrable_gaussianStep_of_bounded (F := E →L[ℝ] E →L[ℝ] ℝ) hf m x hXX bXX
  rw [fderiv_fderiv_gaussianStep hf]
  change (∫ y, Y y ∂gaussianStepLaw m f x) u v +
    m*((∫ y, (X y).smulRight (X y) ∂gaussianStepLaw m f x) u v -
      (∫ y, X y ∂gaussianStepLaw m f x) u*(∫ y, X y ∂gaussianStepLaw m f x) v) = _
  rw [ContinuousLinearMap.integral_apply iY,
    ContinuousLinearMap.integral_apply (iY.apply_continuousLinearMap u),
    ContinuousLinearMap.integral_apply iXX,
    ContinuousLinearMap.integral_apply (iXX.apply_continuousLinearMap u),
    ContinuousLinearMap.integral_apply iX,ContinuousLinearMap.integral_apply iX]
  rfl

theorem gaussianStep_curvature_domination {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    {A : E × ℝ → ℝ} (hc : Continuous A) {C : ℝ} (hb : ∀ z, ‖A z‖ ≤ C)
    (m : ℝ) (u x : E)
    (hH : ∀ y, m*(A (x,y)-(prefixGradient f u (x,y))^2) ≤ prefixHessian f u u (x,y)) :
    m*(gaussianAverage m f A x-(fderiv ℝ (gaussianStep m f) x u)^2) ≤
      fderiv ℝ (fderiv ℝ (gaussianStep m f)) x u u := by
  let := gaussianStepLaw_probability hf m x
  obtain ⟨hcG,B,hB,hbG⟩ := prefixGradient_data hf u
  obtain ⟨hcH,D,hD,hbH⟩ := prefixHessian_data hf u u
  have iA := integrable_gaussianStep_of_bounded hf m x
    (hc.comp (continuous_const.prodMk continuous_id)) (fun y => hb (x,y))
  have iH := integrable_gaussianStep_of_bounded hf m x
    (hcH.comp (continuous_const.prodMk continuous_id)) (fun y => hbH (x,y))
  have iGG := integrable_gaussianStep_of_bounded hf m x
    (g := fun y => prefixGradient f u (x,y)*prefixGradient f u (x,y))
    ((hcG.mul hcG).comp (continuous_const.prodMk continuous_id)) (C := B*B) (fun y => by
      rw [norm_mul]; exact mul_le_mul (hbG _) (hbG _) (norm_nonneg _) hB)
  have H := integral_mono ((iA.sub (by simpa only [pow_two] using iGG)).const_mul m) iH hH
  rw [integral_const_mul] at H
  simp only [Pi.sub_apply,Function.comp_apply,id_eq] at H
  have iA' : Integrable (fun y => A (x,y)) (gaussianStepLaw m f x) := iA
  rw [integral_sub iA' (by simpa only [pow_two] using iGG)] at H
  rw [fderiv_fderiv_gaussianStep_apply hf, fderiv_gaussianStep_apply hf]
  simp only [pow_two,gaussianAverage] at H ⊢
  nlinarith

theorem gaussianStep_variance_nonneg {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    {A : E × ℝ → ℝ} (hc : Continuous A) {C : ℝ} (hb : ∀ z, ‖A z‖ ≤ C)
    (m : ℝ) (u x : E)
    (hA : ∀ y, 0 ≤ A (x,y)-(prefixGradient f u (x,y))^2) :
    0 ≤ gaussianAverage m f A x-(fderiv ℝ (gaussianStep m f) x u)^2 := by
  let μ := gaussianStepLaw m f x
  let := gaussianStepLaw_probability hf m x
  obtain ⟨hcG,B,hB,hbG⟩ := prefixGradient_data hf u
  have hcm : Continuous (fun y : ℝ => prefixGradient f u (x,y)) :=
    hcG.comp (continuous_const.prodMk continuous_id)
  have hmem : MemLp (fun y => prefixGradient f u (x,y)) 2 μ :=
    MemLp.of_bound hcm.aestronglyMeasurable B (ae_of_all _ (fun y => hbG (x,y)))
  have iA := integrable_gaussianStep_of_bounded hf m x
    (hc.comp (continuous_const.prodMk continuous_id)) (fun y => hb (x,y))
  have iG := hmem.integrable_sq
  have Hi := integral_mono iG iA (fun y => sub_nonneg.mp (hA y))
  simp only [Function.comp_apply,id_eq] at Hi
  have Hv := variance_nonneg (fun y => prefixGradient f u (x,y)) μ
  rw [variance_eq_sub hmem] at Hv
  rw [fderiv_gaussianStep_apply hf]
  change 0 ≤ (∫ y, A (x,y) ∂μ)-(∫ y, prefixGradient f u (x,y) ∂μ)^2
  change 0 ≤ (∫ y, (prefixGradient f u (x,y))^2 ∂μ)-_ at Hv
  linarith

end GaussianAverage
end SK.Analytic

end
end
end
end
end
end
end

end OAI
