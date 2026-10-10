import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJets
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! Pointwise convolution and differentiation for integrable kernels and bounded spatial jets. -/

noncomputable section
namespace ForcedComputation.BoundedKernel

open MeasureTheory Set Filter
open scoped Topology ContDiff

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def convolve (μ : Measure E) (w : E → ℝ) (f : E → F) (x : E) : F :=
  ∫ y, w y • f (x - y) ∂μ

omit [NormedSpace ℝ E] [CompleteSpace F] in
theorem integrand_integrable (μ : Measure E) (w : E → ℝ) (f : E → F)
    (hw : Integrable w μ) (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (x : E) : Integrable (fun y => w y • f (x - y)) μ := by
  apply (hw.norm.mul_const C).mono'
  · exact hw.aestronglyMeasurable.smul
      ((hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · exact ae_of_all _ fun y => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC (x - y)) (norm_nonneg _)

omit [NormedSpace ℝ E] [CompleteSpace F] in
theorem norm_convolve_le (μ : Measure E) (w : E → ℝ) (f : E → F)
    (hw : Integrable w μ) (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (x : E) : ‖convolve E F μ w f x‖ ≤ C * ∫ y, |w y| ∂μ := by
  have hi := integrand_integrable E F μ w f hw hf C hC x
  calc
    _ ≤ ∫ y, ‖w y • f (x - y)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖w y‖ * C ∂μ := by
      apply integral_mono hi.norm (hw.norm.mul_const C)
      intro y
      change ‖w y • f (x - y)‖ ≤ ‖w y‖ * C
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC (x - y)) (norm_nonneg _)
    _ = C * ∫ y, |w y| ∂μ := by
      rw [integral_mul_const]
      simp only [Real.norm_eq_abs]
      ring

omit [CompleteSpace F] in
/-- Dominated differentiation transfers a spatial derivative to the bounded input function. -/
theorem hasFDerivAt_convolve (μ : Measure E) (w : E → ℝ) (f : E → F)
    (hw : Integrable w μ) (hf : ContDiff ℝ 1 f)
    (C D : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ D)
    (x : E) :
    HasFDerivAt (convolve E F μ w f)
      (∫ y, w y • fderiv ℝ f (x - y) ∂μ) x := by
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ) (s := univ) (F' := fun z y => w y • fderiv ℝ f (z - y))
    (bound := fun y => ‖w y‖ * D) univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun z =>
      (integrand_integrable E F μ w f hw hf.continuous C hC z).aestronglyMeasurable
  · exact integrand_integrable E F μ w f hw hf.continuous C hC x
  · exact (integrand_integrable E (E →L[ℝ] F) μ w (fderiv ℝ f) hw hdc D hD x).aestronglyMeasurable
  · exact ae_of_all _ fun y z _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hD (z - y)) (norm_nonneg _)
  · exact hw.norm.mul_const D
  · exact ae_of_all _ fun y z _ => by
      have h := (((hf.differentiable (by norm_num)) (z - y)).hasFDerivAt.comp z
        ((hasFDerivAt_id z).sub_const y)).const_smul (w y)
      change HasFDerivAt (fun v => w y • f (v - y)) _ z at h
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq, Pi.smul_apply] using h

omit [CompleteSpace F] in
theorem fderiv_convolve (μ : Measure E) (w : E → ℝ) (f : E → F)
    (hw : Integrable w μ) (hf : ContDiff ℝ 1 f)
    (C D : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ D)
    (x : E) :
    fderiv ℝ (convolve E F μ w f) x =
      ∫ y, w y • fderiv ℝ f (x - y) ∂μ :=
  (hasFDerivAt_convolve E F μ w f hw hf C D hC hD x).fderiv

end ForcedComputation.BoundedKernel

end

end OAI
