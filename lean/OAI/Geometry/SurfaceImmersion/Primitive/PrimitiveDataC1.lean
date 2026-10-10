import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveAmplitudeParameterBounds

namespace OAI

/-! First derivatives of finite primitive data are bounded componentwise. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance finiteDataFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance finiteDataFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance finiteDataDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance finiteDataDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance finiteDataCovectorNormed : NormedAddCommGroup (Plane →L[ℝ] ℝ) := inferInstance
local instance finiteDataCovectorSpace : NormedSpace ℝ (Plane →L[ℝ] ℝ) := inferInstance
local instance finiteDataFiberT2 : T2Space TensorFiber := inferInstance
local instance finiteDataDualT2 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance finiteDataCovectorT2 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]
local instance finiteDataNormed : NormedAddCommGroup (PrimitiveAmplitudeData ι) := inferInstance
local instance finiteDataSpace : NormedSpace ℝ (PrimitiveAmplitudeData ι) := inferInstance
local instance finiteDataT2 : T2Space (PrimitiveAmplitudeData ι) := inferInstance

theorem primitive_data_fderiv_bound
    (q : ι → JetPolynomial.Base → TensorFiber →L[ℝ] ℝ)
    (w : ι → JetPolynomial.Base → ℝ)
    (v : ι → JetPolynomial.Base → Plane →L[ℝ] ℝ)
    (H : JetPolynomial.Base → TensorFiber) (x : JetPolynomial.Base)
    (hq : ∀ a, DifferentiableAt ℝ (q a) x)
    (hw : ∀ a, DifferentiableAt ℝ (w a) x)
    (hv : ∀ a, DifferentiableAt ℝ (v a) x) (hH : DifferentiableAt ℝ H x)
    {D : ℝ} (hD : 0 ≤ D)
    (hbq : ∀ a, ‖fderiv ℝ (q a) x‖ ≤ D)
    (hbw : ∀ a, ‖fderiv ℝ (w a) x‖ ≤ D)
    (hbv : ∀ a, ‖fderiv ℝ (v a) x‖ ≤ D) (hbH : ‖fderiv ℝ H x‖ ≤ D) :
    ‖fderiv ℝ (fun y => (((((fun a => q a y),fun a => w a y),fun a => v a y),H y) :
      PrimitiveAmplitudeData ι)) x‖ ≤ D := by
  have hq' := hasFDerivAt_pi.mpr (fun a => (hq a).hasFDerivAt)
  have hw' := hasFDerivAt_pi.mpr (fun a => (hw a).hasFDerivAt)
  have hv' := hasFDerivAt_pi.mpr (fun a => (hv a).hasFDerivAt)
  have he := ((hq'.prodMk hw').prodMk hv').prodMk hH.hasFDerivAt
  change ‖fderiv ℝ (fun y => ((((fun a => q a y),fun a => w a y),fun a => v a y),H y)) x‖ ≤ D
  rw [he.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ hD
  intro y
  have hqy : ‖fun a => fderiv ℝ (q a) x y‖ ≤ D*‖y‖ :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg hD (norm_nonneg y))).mpr
      (fun a => ((fderiv ℝ (q a) x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (hbq a) (norm_nonneg y)))
  have hwy : ‖fun a => fderiv ℝ (w a) x y‖ ≤ D*‖y‖ :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg hD (norm_nonneg y))).mpr
      (fun a => ((fderiv ℝ (w a) x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (hbw a) (norm_nonneg y)))
  have hvy : ‖fun a => fderiv ℝ (v a) x y‖ ≤ D*‖y‖ :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg hD (norm_nonneg y))).mpr
      (fun a => ((fderiv ℝ (v a) x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (hbv a) (norm_nonneg y)))
  have hHy := ((fderiv ℝ H x).le_opNorm y).trans (mul_le_mul_of_nonneg_right hbH (norm_nonneg y))
  exact max_le (max_le (max_le hqy hwy) hvy) hHy

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
