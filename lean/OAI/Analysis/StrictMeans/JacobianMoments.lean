import OAI.Analysis.StrictMeans.ReciprocalMoments

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

open Set Filter Complex
open scoped Topology

noncomputable section

namespace StrictInverseFirstPower

theorem real_det_eq (L : ℂ →ₗ[ℝ] ℂ) :
    LinearMap.det L = (L 1).re * (L I).im - (L I).re * (L 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]

def criticalMap (k : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  F z - I * (z.im : ℂ) * deriv F z / (k : ℂ)

def normalizedJacobian (k : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  (fderiv ℝ (criticalMap k F) z).det / ‖deriv F z‖ ^ 2

theorem criticalMap_fderiv {k : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (hF' : DifferentiableAt ℂ (deriv F) z) :
    fderiv ℝ (criticalMap k F) z =
      (ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ -
        (I / (k : ℂ)) •
          ((z.im : ℂ) • (ContinuousLinearMap.toSpanSingleton ℂ (deriv (deriv F) z)).restrictScalars ℝ +
            deriv F z • (Complex.ofRealCLM.comp Complex.imCLM)) := by
  have h1 := hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have h2 := hF'.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hi := (Complex.ofRealCLM.comp Complex.imCLM).hasFDerivAt (x := z)
  have hh := h1.sub ((hi.mul h2).const_mul (I / (k : ℂ)))
  convert hh.fderiv using 1
  · congr 1
    funext w
    simp only [criticalMap, Pi.mul_apply, Pi.sub_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      Complex.ofRealCLM_apply, Complex.imCLM_apply]
    ring
  · ext w
    simp [smul_eq_mul]

def logarithmicDerivative (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  -I * (z.im : ℂ) * (deriv (deriv F) z / deriv F z)

def jacobianExpression (k : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  (k * (k - 1) + (2 * k - 1) * (logarithmicDerivative F z).re +
    ‖logarithmicDerivative F z‖ ^ 2) / k ^ 2

theorem determinant_columns_factor (a q : ℂ) (k : ℝ) :
    (a * ((k : ℂ) + q)).re * (I * a * ((k : ℂ) - 1 + q)).im -
    (I * a * ((k : ℂ) - 1 + q)).re * (a * ((k : ℂ) + q)).im =
      ‖a‖ ^ 2 * (k * (k - 1) + (2 * k - 1) * q.re + ‖q‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, add_re, add_im,
    sub_re, sub_im, mul_re, mul_im, I_re, I_im, one_re, one_im, ofReal_re, ofReal_im]
  ring

theorem criticalMap_fderiv_one {k : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hk : k ≠ 0) (hF : DifferentiableAt ℂ F z) (hF' : DifferentiableAt ℂ (deriv F) z)
    (hne : deriv F z ≠ 0) :
    fderiv ℝ (criticalMap k F) z 1 =
      (deriv F z / (k : ℂ)) * ((k : ℂ) + logarithmicDerivative F z) := by
  have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  rw [criticalMap_fderiv hF hF']
  simp [smul_eq_mul, logarithmicDerivative]
  field_simp [hk', hne]
  ring

theorem criticalMap_fderiv_I {k : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hk : k ≠ 0) (hF : DifferentiableAt ℂ F z) (hF' : DifferentiableAt ℂ (deriv F) z)
    (hne : deriv F z ≠ 0) :
    fderiv ℝ (criticalMap k F) z I =
      I * (deriv F z / (k : ℂ)) * ((k : ℂ) - 1 + logarithmicDerivative F z) := by
  have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  rw [criticalMap_fderiv hF hF']
  simp [smul_eq_mul, logarithmicDerivative]
  field_simp [hk', hne]
  ring

theorem normalizedJacobian_eq {k : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hk : k ≠ 0) (hF : DifferentiableAt ℂ F z) (hF' : DifferentiableAt ℂ (deriv F) z)
    (hne : deriv F z ≠ 0) :
    normalizedJacobian k F z = jacobianExpression k F z := by
  unfold normalizedJacobian
  change LinearMap.det (fderiv ℝ (criticalMap k F) z : ℂ →ₗ[ℝ] ℂ) / ‖deriv F z‖ ^ 2 = _
  rw [real_det_eq]
  change ( (fderiv ℝ (criticalMap k F) z 1).re * (fderiv ℝ (criticalMap k F) z I).im -
    (fderiv ℝ (criticalMap k F) z I).re * (fderiv ℝ (criticalMap k F) z 1).im) /
    ‖deriv F z‖ ^ 2 = _
  rw [criticalMap_fderiv_one hk hF hF' hne, criticalMap_fderiv_I hk hF hF' hne,
    determinant_columns_factor]
  unfold jacobianExpression
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  field_simp

end StrictInverseFirstPower

end

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

lemma reciprocalFunction_deriv_I (f : DiskFamily) :
    deriv (reciprocalFunction f) I = -deriv (deriv (halfPlaneFunction f)) I := by
  have h := (((halfPlaneFunction_differentiableOn f).deriv isOpen_halfPlane).differentiableAt
    (isOpen_halfPlane.mem_nhds (show (I : ℂ).im > 0 by simp))).hasDerivAt
  have hn : deriv (halfPlaneFunction f) I ≠ 0 := by simp
  change deriv (fun z => (deriv (halfPlaneFunction f) z)⁻¹) I = _
  simpa using! (h.inv hn).deriv

lemma logarithmicDerivative_I_eq (f : DiskFamily) :
    logarithmicDerivative (halfPlaneFunction f) I = deriv (reciprocalFunction f) I * I := by
  rw [reciprocalFunction_deriv_I]
  simp [logarithmicDerivative, mul_comm]

lemma continuous_logarithmicDerivative_I :
    Continuous (fun f : DiskFamily => logarithmicDerivative (halfPlaneFunction f) I) := by
  simp_rw [logarithmicDerivative_I_eq]
  exact (continuous_reciprocalFunction_deriv.comp
    (continuous_id.prodMk (continuous_const (y := (⟨I, by simp⟩ : HalfPlaneSet))))).mul_const I

lemma logarithmicDerivative_integrable_I (μ : Measure DiskFamily) [IsFiniteMeasure μ] :
    Integrable (fun f : DiskFamily => logarithmicDerivative (halfPlaneFunction f) I) μ :=
  continuous_logarithmicDerivative_I.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma logarithmicDerivative_real_moment (μ : Measure DiskFamily) [IsFiniteMeasure μ] (β : ℝ)
    (hlaw : ReciprocalMeanLaw μ β) :
    (∫ f, (logarithmicDerivative (halfPlaneFunction f) I).re ∂μ) = -β := by
  simpa [logarithmicDerivative_I_eq] using
    normPathFirst_integral_zero μ β hlaw I (by simp)

lemma logarithmicDerivative_norm_sq_moment (μ : Measure DiskFamily) [IsFiniteMeasure μ] (β : ℝ)
    (hlaw : ReciprocalMeanLaw μ β) :
    (∫ f, ‖logarithmicDerivative (halfPlaneFunction f) I‖ ^ 2 ∂μ) = β * (β + 1) := by
  simpa [logarithmicDerivative_I_eq, norm_mul] using
    reciprocal_deriv_norm_sq_moment μ β hlaw

lemma halfPlaneFunction_normalizedJacobian_I (f : DiskFamily) {k : ℝ} (hk : k ≠ 0) :
    normalizedJacobian k (halfPlaneFunction f) I = jacobianExpression k (halfPlaneFunction f) I :=
  normalizedJacobian_eq hk ((halfPlaneFunction_differentiableOn f).differentiableAt
    (isOpen_halfPlane.mem_nhds (by simp)))
    (((halfPlaneFunction_differentiableOn f).deriv isOpen_halfPlane).differentiableAt
    (isOpen_halfPlane.mem_nhds (by simp))) (by simp)

lemma expected_normalizedJacobian (μ : ProbabilityMeasure DiskFamily) (β k : ℝ)
    (hk : k ≠ 0) (hlaw : ReciprocalMeanLaw (μ : Measure DiskFamily) β) :
    k ^ 2 * (∫ f, normalizedJacobian k (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) =
      k * (k - 1) - (2 * k - 1) * β + β * (β + 1) := by
  have hq := continuous_logarithmicDerivative_I
  have h₁ : Integrable (fun f : DiskFamily => (2 * k - 1) *
      (logarithmicDerivative (halfPlaneFunction f) I).re) (μ : Measure DiskFamily) :=
    ((Complex.continuous_re.comp hq).const_mul _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h₂ : Integrable (fun f : DiskFamily => ‖logarithmicDerivative (halfPlaneFunction f) I‖ ^ 2) (μ : Measure DiskFamily) :=
    (hq.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h₀₁ : Integrable (fun f : DiskFamily => k * (k - 1) +
      (2 * k - 1) * (logarithmicDerivative (halfPlaneFunction f) I).re) (μ : Measure DiskFamily) :=
    (integrable_const _).add h₁
  have hadd := integral_add h₀₁ h₂
  have hadd₁ := integral_add (integrable_const (k * (k - 1))) h₁
  simp_rw [halfPlaneFunction_normalizedJacobian_I _ hk, jacobianExpression]
  rw [integral_div, hadd, hadd₁, integral_const_mul (2 * k - 1),
    logarithmicDerivative_real_moment _ β hlaw, logarithmicDerivative_norm_sq_moment _ β hlaw]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  field_simp
  ring

theorem expected_normalizedJacobian_at_source_k (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 1 / 4 ≤ β) (hlaw : ReciprocalMeanLaw (μ : Measure DiskFamily) β) :
    ((β + 2) / 3) ^ 2 *
      (∫ f, normalizedJacobian ((β + 2) / 3) (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) =
      ((4 * β - 1) * (β + 2)) / 9 := by
  rw [expected_normalizedJacobian μ β ((β + 2) / 3) (by linarith) hlaw]
  ring

end
end StrictInverseFirstPower

end

end OAI
