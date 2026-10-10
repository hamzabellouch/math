import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianSecondStep

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
section CovarianceStep
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianStepLaw_integral_inv_smul {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℝ) (f : E × ℝ → ℝ) (x : E) (g : ℝ → F) :
    (∫ y, g y ∂gaussianStepLaw m f x) =
      (∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1)⁻¹ •
        ∫ y, Real.exp (m*f (x,y)) • g y ∂gaussianReal 0 1 := by
  rw [gaussianStepLaw,integral_tilted,← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [smul_smul,div_eq_mul_inv,mul_comm]

local instance : SMulZeroClass ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (@Module.toDistribMulAction ℝ (E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance inferInstance).toDistribSMul.toSMulZeroClass
local instance : ContinuousENorm (E →L[ℝ] E →L[ℝ] ℝ) :=
  @SeminormedAddGroup.toContinuousENorm (E →L[ℝ] E →L[ℝ] ℝ) inferInstance

local instance : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  @NormedSpace.toIsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) _ _ _

theorem fderiv_fderiv_gaussianStep {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (gaussianStep m f)) x =
      (∫ y, secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y)) ∂gaussianStepLaw m f x) +
      m • ((∫ y, (leftRestrict (fderiv ℝ f (x,y))).smulRight
          (leftRestrict (fderiv ℝ f (x,y))) ∂gaussianStepLaw m f x) -
        (∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianStepLaw m f x).smulRight
          (∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianStepLaw m f x)) := by
  by_cases hm : m = 0
  · subst m
    rw [gaussianStepLaw_zero]
    convert! fderiv_fderiv_gaussianStep_zero hf x using 1
    ext u v
    simp
  obtain ⟨hfd,C,D,hC,hD,hb,hbb⟩ := hf
  have hf : BoundedDerivs f := ⟨hfd,C,D,hC,hD,hb,hbb⟩
  let X : ℝ → E →L[ℝ] ℝ := fun y => leftRestrict (fderiv ℝ f (x,y))
  let Y : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun y =>
    secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y))
  have hX : Continuous X := leftRestrict.continuous.comp
    ((hfd.fderiv_right (m := 1) (by norm_num)).continuous.comp
      (continuous_const.prodMk continuous_id))
  have hY : Continuous Y := secondLeftRestrict.continuous.comp
    ((hfd.fderiv_right (m := 1) (by norm_num) |>.fderiv_right (m := 0) (by norm_num)).continuous.comp
      (continuous_const.prodMk continuous_id))
  have bX (y : ℝ) : ‖X y‖ ≤ C := (leftRestrict_apply_bound _).trans (hb _)
  have bY (y : ℝ) : ‖Y y‖ ≤ D := (secondLeftRestrict_apply_bound _).trans (hbb _)
  have hXX : Continuous (fun y => (X y).smulRight (X y)) :=
    ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp hX).clm_apply hX
  have bXX (y : ℝ) : ‖(X y).smulRight (X y)‖ ≤ C*C := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (bX y) (bX y) (norm_nonneg _) hC
  have iX := integrable_exp_smul_of_bounded hf m x X hX bX
  have iY := integrable_exp_smul_of_bounded hf m x Y hY bY
  have iXX := integrable_exp_smul_of_bounded hf m x (fun y => (X y).smulRight (X y)) hXX bXX
  let A := ∫ y, Real.exp (m*f (x,y)) • X y ∂gaussianReal 0 1
  let B := ∫ y, Real.exp (m*f (x,y)) • Y y ∂gaussianReal 0 1
  let C₂ := ∫ y, Real.exp (m*f (x,y)) • (X y).smulRight (X y) ∂gaussianReal 0 1
  have he₁ (y : ℝ) : leftRestrict
      (fderiv ℝ (fun z => Real.exp (m*f z)) (x,y)) =
      m • (Real.exp (m*f (x,y)) • X y) := by
    rw [((hfd.differentiable (by norm_num) (x,y)).hasFDerivAt.const_mul m).exp.fderiv]
    ext u
    simp only [X,leftRestrict,ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply,smul_apply,smul_eq_mul]
    ring
  have he₂ (y : ℝ) : secondLeftRestrict
      (fderiv ℝ (fderiv ℝ (fun z => Real.exp (m*f z))) (x,y)) =
      m • (Real.exp (m*f (x,y)) • Y y) +
      m^2 • (Real.exp (m*f (x,y)) • (X y).smulRight (X y)) := by
    rw [fderiv_fderiv_exp _ (contDiff_const.mul hfd),fderiv_fderiv_const_mul f hfd,
      ((hfd.differentiable (by norm_num) (x,y)).hasFDerivAt.const_mul m).fderiv]
    ext u v
    simp only [X,Y,secondLeftRestrict,leftRestrict,ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply,add_apply,
      ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
    ring
  rw [fderiv_fderiv_gaussianStep_nonzero hf hm]
  simp_rw [he₁,he₂]
  erw [integral_add (iY.smul m) (iXX.smul (m^2))]
  simp only [Pi.smul_apply]
  erw [iY.integral_smul m, iXX.integral_smul (m^2), iX.integral_smul m]
  simp_rw [gaussianStepLaw_integral_inv_smul]
  change m⁻¹ • ((_ : ℝ) • (m • B + m^2 • C₂) +
    ((_ : ℝ) • (m • A)).smulRight (m • A)) =
    (_ : ℝ) • B + m • ((_ : ℝ) • C₂ - ((_ : ℝ) • A).smulRight ((_ : ℝ) • A))
  ext u v
  simp only [add_apply,sub_apply,
    ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
  have hp := (integral_exp_pos (hf.exp_integrable m x)).ne'
  field_simp [hm,hp]
  ring

end CovarianceStep
end SK.Analytic

end
end
end
end
end
end
end

end OAI
