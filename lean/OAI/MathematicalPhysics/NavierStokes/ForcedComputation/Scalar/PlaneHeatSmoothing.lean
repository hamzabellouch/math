import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatKernelBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedKernelConvolution
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! Gaussian convolution differentiates bounded continuous data by differentiating the kernel. -/

noncomputable section
namespace ForcedComputation.PlaneHeat

open MeasureTheory Set Filter ShearFlows
open scoped Topology ContDiff

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The symmetric form of heat convolution, convenient for differentiating the kernel. -/
def heatConvolution (t : ℝ) (f : Plane → F) (x : Plane) : F :=
  ∫ y, kernel t (x - y) • f y

theorem heatConvolution_eq (t : ℝ) (f : Plane → F) (x : Plane) :
    heatConvolution F t f x = BoundedKernel.convolve Plane F volume (kernel t) f x := by
  unfold heatConvolution BoundedKernel.convolve
  rw [← integral_sub_left_eq_self _ volume x]
  simp only [sub_sub_self]

private theorem integrand_integrable {t : ℝ} (ht : 0 < t) (f : Plane → F)
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (x : Plane) :
    Integrable (fun y => kernel t (x - y) • f y) := by
  have hi := BoundedKernel.integrand_integrable Plane F volume (kernel t) f
    (kernel_integrable ht) hf C hC x
  convert! hi.comp_sub_left x using 1
  simp only [sub_sub_self]

private theorem derivativeIntegrand_continuous (t : ℝ) (f : Plane → F)
    (hf : Continuous f) (x : Plane) :
    Continuous (fun y => (fderiv ℝ (kernel t) (x - y)).smulRight (f y)) := by
  have hk : Continuous (fderiv ℝ (kernel t)) :=
    (kernel_smooth t).continuous_fderiv (by simp)
  exact ((ContinuousLinearMap.smulRightL ℝ Plane F).continuous.comp
    (hk.comp (continuous_const.sub continuous_id))).clm_apply hf

private theorem derivativeIntegrand_integrable {t : ℝ} (ht : 0 < t)
    (f : Plane → F) (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (x : Plane) :
    Integrable (fun y => (fderiv ℝ (kernel t) (x - y)).smulRight (f y)) := by
  apply ((derivativeEnvelope_integrable ht (‖x‖ + 1)).mul_const C).mono'
    (derivativeIntegrand_continuous F t f hf x).aestronglyMeasurable
  exact ae_of_all _ fun y => by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    apply mul_le_mul
    · exact kernel_fderiv_shift_le ht (by positivity) x y fun j =>
        (norm_le_pi_norm x j).trans (by linarith)
    · exact hC y
    · exact norm_nonneg _
    · have h := kernel_fderiv_shift_le ht (by positivity : 0 ≤ ‖x‖ + 1) x y
        (fun j => (norm_le_pi_norm x j).trans (by linarith))
      exact (norm_nonneg _).trans h

/-- Differentiating under the integral is valid for bounded continuous data, without a
spatial derivative assumption on that data. -/
theorem hasFDerivAt_heatConvolution {t : ℝ} (ht : 0 < t) (f : Plane → F)
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (x : Plane) :
    HasFDerivAt (heatConvolution F t f)
      (∫ y, (fderiv ℝ (kernel t) (x - y)).smulRight (f y)) x := by
  let R := ‖x‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcoord (z : Plane) (hz : z ∈ Metric.ball x 1) (j : Fin 2) : |z j| ≤ R := by
    have hz' : ‖z - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    calc
      |z j| ≤ ‖z‖ := norm_le_pi_norm z j
      _ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ R := by dsimp [R]; linarith
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (s := Metric.ball x 1)
    (F' := fun z y => (fderiv ℝ (kernel t) (z - y)).smulRight (f y))
    (bound := fun y => derivativeEnvelope t R y * C)
    (Metric.ball_mem_nhds x zero_lt_one) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun z => (integrand_integrable F ht f hf C hC z).aestronglyMeasurable
  · exact integrand_integrable F ht f hf C hC x
  · exact (derivativeIntegrand_integrable F ht f hf C hC x).aestronglyMeasurable
  · exact ae_of_all _ fun y z hz => by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      have hk := kernel_fderiv_shift_le ht hR z y (hcoord z hz)
      exact mul_le_mul hk (hC y) (norm_nonneg _) ((norm_nonneg _).trans hk)
  · exact (derivativeEnvelope_integrable ht R).mul_const C
  · exact ae_of_all _ fun y z _ => by
      have h := (((kernel_smooth t).differentiable (by simp) (z - y)).hasFDerivAt.comp z
        ((hasFDerivAt_id z).sub_const y)).smul_const (f y)
      change HasFDerivAt (fun v => kernel t (v - y) • f y) _ z at h
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using h

/-- Each directional derivative is convolution against the corresponding integrable
Gaussian derivative. -/
theorem fderiv_heatConvolution_basis {t : ℝ} (ht : 0 < t) (f : Plane → F)
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (x : Plane) (j : Fin 2) :
    fderiv ℝ (heatConvolution F t f) x (Pi.single j 1) =
      BoundedKernel.convolve Plane F volume (kernelDerivative t j) f x := by
  rw [(hasFDerivAt_heatConvolution F ht f hf C hC x).fderiv,
    ContinuousLinearMap.integral_apply (derivativeIntegrand_integrable F ht f hf C hC x)]
  simp_rw [ContinuousLinearMap.smulRight_apply, kernel_fderiv_basis ht]
  unfold BoundedKernel.convolve
  rw [← integral_sub_left_eq_self _ volume x]
  simp only [sub_sub_self]

theorem norm_fderiv_heatConvolution_basis_le {t : ℝ} (ht : 0 < t) (f : Plane → F)
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (x : Plane) (j : Fin 2) :
    ‖fderiv ℝ (heatConvolution F t f) x (Pi.single j 1)‖ ≤ C * (2 / Real.sqrt t) := by
  rw [fderiv_heatConvolution_basis F ht f hf C hC]
  apply (BoundedKernel.norm_convolve_le Plane F volume (kernelDerivative t j) f
    (kernelDerivative_integrable ht j) hf C hC x).trans
  exact mul_le_mul_of_nonneg_left (kernelDerivative_abs_integral_le ht j)
    ((norm_nonneg (f 0)).trans (hC 0))

end ForcedComputation.PlaneHeat

end

end OAI
