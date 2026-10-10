import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetDifferentiation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildSource

namespace OAI

/-! Directional derivatives commute with the actual Gaussian Volterra operators. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild

open MeasureTheory Set ShearFlows
open scoped Topology Interval ContDiff

/-- Differentiate a continuous jet path pointwise. -/
def directionalPath (k : ℕ) (v : Plane) (T : ℝ) :
    WeaklySingular.Path (Jet (k+1)) T →L[ℝ] WeaklySingular.Path (Jet k) T :=
  (WeaklySingular.pathEquiv (Jet k) T).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k v).compLeftContinuous ℝ
      (Icc (0 : ℝ) T)).comp
      (WeaklySingular.pathEquiv (Jet (k+1)) T).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem directionalPath_apply (k : ℕ) (v : Plane) (T : ℝ)
    (u : WeaklySingular.Path (Jet (k+1)) T) (t : Icc (0 : ℝ) T) :
    directionalPath k v T u t = BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k v (u t) := rfl

theorem extendPath_directional {T : ℝ} (hT : 0 ≤ T) (k : ℕ) (v : Plane)
    (u : WeaklySingular.Path (Jet (k+1)) T) (s : ℝ) :
    WeaklySingular.extendPath (Jet k) hT (directionalPath k v T u) s =
      BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k v
        (WeaklySingular.extendPath (Jet (k+1)) hT u s) := rfl

theorem rawHeatKernel_directional {ν : ℝ} (hν : 0 < ν) (k : ℕ) (v : Plane)
    (r : ℝ) (J : Jet (k+1)) :
    BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k v (rawHeatKernel hν (k+1) r J) =
      rawHeatKernel hν k r (BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k v J) := by
  by_cases hr : 0 < r
  · rw [rawHeatKernel_pos hν (k+1) hr, rawHeatKernel_pos hν k hr]
    exact BoundedSpatialJets.directionalDerivativeCLM_convolution Plane ℝ k v volume
      (PlaneHeat.kernel (ν*r)) (PlaneHeat.kernel_integrable (mul_pos hν hr)) J
  · simp only [rawHeatKernel_nonpos hν (k+1) (not_lt.mp hr),
      rawHeatKernel_nonpos hν k (not_lt.mp hr), zero_apply, map_zero]

theorem gradientKernel_directional {ν : ℝ} (hν : 0 < ν) (k : ℕ) (v : Plane)
    (j : Fin 2) (r : ℝ) (J : Jet (k+1)) :
    BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k v (gradientKernel hν (k+1) j r J) =
      gradientKernel hν k j r (BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k v J) := by
  by_cases hr : 0 < r
  · rw [gradientKernel_pos hν (k+1) j hr, gradientKernel_pos hν k j hr]
    exact BoundedSpatialJets.directionalDerivativeCLM_convolution Plane ℝ k v volume
      (PlaneHeat.kernelDerivative (ν*r) j)
      (PlaneHeat.kernelDerivative_integrable (mul_pos hν hr) j) J
  · simp only [gradientKernel_nonpos hν (k+1) j (not_lt.mp hr),
      gradientKernel_nonpos hν k j (not_lt.mp hr), zero_apply, map_zero]

theorem rawKernels_directional {ν : ℝ} (hν : 0 < ν) (k : ℕ) (v : Plane)
    (i : Fin 3) (r : ℝ) (J : Jet (k+1)) :
    BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k v (rawKernels hν (k+1) i r J) =
      rawKernels hν k i r (BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k v J) :=
  Fin.cases (rawHeatKernel_directional hν k v r J)
    (fun j => gradientKernel_directional hν k v j r J) i

/-- Spatial differentiation passes through the actual singular time integral. -/
theorem rawKernelIntegral_directional {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (v : Plane) (u : WeaklySingular.Path (Jet (k+1)) T)
    (i : Fin 3) (t : Icc (0 : ℝ) T) :
    BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k v
      (∫ s in 0..t.val, rawKernels hν (k+1) i (t.val-s)
        (WeaklySingular.extendPath (Jet (k+1)) hT u s)) =
      ∫ s in 0..t.val, rawKernels hν k i (t.val-s)
        (WeaklySingular.extendPath (Jet k) hT (directionalPath k v T u) s) := by
  apply map_integral_eq (BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k v)
    (rawKernel_path_integrable hT hν (k+1) u i t)
  intro s
  exact (rawKernels_directional hν k v i (t.val-s) _).trans
    (congrArg (rawKernels hν k i (t.val-s)) (extendPath_directional hT k v u s).symm)

private theorem gradient_convolve_C1 {t : ℝ} (ht : 0 < t) {f : Plane → ℝ}
    (hf : ContDiff ℝ 1 f) (j : Fin 2) (C D : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ D) (x : Plane) :
    BoundedKernel.convolve Plane ℝ volume (PlaneHeat.kernelDerivative t j) f x =
      BoundedKernel.convolve Plane ℝ volume (PlaneHeat.kernel t)
        (fun y => fderiv ℝ f y (Pi.single j 1)) x := by
  have he : PlaneHeat.heatConvolution ℝ t f =
      BoundedKernel.convolve Plane ℝ volume (PlaneHeat.kernel t) f :=
    funext (PlaneHeat.heatConvolution_eq ℝ t f)
  have hi := BoundedKernel.integrand_integrable Plane (Plane →L[ℝ] ℝ) volume
    (PlaneHeat.kernel t) (fderiv ℝ f) (PlaneHeat.kernel_integrable ht)
    (hf.continuous_fderiv (by norm_num)) D hD x
  rw [← PlaneHeat.fderiv_heatConvolution_basis ℝ ht f hf.continuous C hC x j, he,
    BoundedKernel.fderiv_convolve Plane ℝ volume (PlaneHeat.kernel t) f
      (PlaneHeat.kernel_integrable ht) hf C D hC hD x,
    ContinuousLinearMap.integral_apply hi]
  rfl

/-- On finite jets, a Gaussian gradient acting on the input equals heat acting on its derivative. -/
theorem gradientKernel_eq_heatDerivative {ν : ℝ} (hν : 0 < ν) (k : ℕ)
    (j : Fin 2) (r : ℝ) (J : Jet (k+1)) :
    gradientKernel hν k j r (BoundedSpatialJets.truncateCLM Plane ℝ k (k+1) (by omega) J) =
      rawHeatKernel hν k r
        (BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k (Pi.single j 1) J) := by
  by_cases hr : 0 < r
  · rw [gradientKernel_pos hν k j hr, rawHeatKernel_pos hν k hr]
    apply BoundedSpatialJets.function_injective Plane ℝ k
    ext x
    rw [PlaneHeat.gradientOperator_apply, PlaneHeat.heatOperator_apply]
    have hd : ∀ y, ‖fderiv ℝ (BoundedSpatialJets.function Plane ℝ (k+1) J) y‖ ≤ ‖J‖ := by
      intro y
      rw [← BoundedSpatialJets.function_derivative Plane ℝ k J y]
      exact (BoundedSpatialJets.norm_function_le Plane (Plane →L[ℝ] ℝ) k
        (BoundedSpatialJets.derivative Plane ℝ k J) y).trans
        (BoundedSpatialJets.norm_derivative_le Plane ℝ k J)
    have hh := gradient_convolve_C1 (mul_pos hν hr)
      ((BoundedSpatialJets.function_contDiff Plane ℝ (k+1) J).of_le (by simp))
      j ‖J‖ ‖J‖ (BoundedSpatialJets.norm_function_le Plane ℝ (k+1) J) hd x
    have htr (y : Plane) : BoundedSpatialJets.function Plane ℝ k
        (BoundedSpatialJets.truncateCLM Plane ℝ k (k+1) (by omega) J) y =
        BoundedSpatialJets.function Plane ℝ (k+1) J y :=
      BoundedSpatialJets.function_truncate Plane ℝ k (k+1) (by omega) J y
    simpa only [BoundedKernel.convolve, BoundedSpatialJets.function_directionalDerivativeCLM,
      htr] using hh
  · simp only [gradientKernel_nonpos hν k j (not_lt.mp hr),
      rawHeatKernel_nonpos hν k (not_lt.mp hr), zero_apply]

end ForcedComputation.PlaneScalarMild

end

end OAI
