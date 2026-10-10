import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveAmplitudeParameterBounds

namespace OAI

/-! The ordinary chain-rule estimate used for each actual amplitude chart. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance ampChainFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance ampChainFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance ampChainTensorDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance ampChainTensorDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance ampChainPlaneDualNormed : NormedAddCommGroup (Plane →L[ℝ] ℝ) := inferInstance
local instance ampChainPlaneDualSpace : NormedSpace ℝ (Plane →L[ℝ] ℝ) := inferInstance
local instance ampChainFiberT2 : T2Space TensorFiber := inferInstance
local instance ampChainTensorDualT2 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance ampChainPlaneDualT2 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]
local instance ampChainDataNormed : NormedAddCommGroup (PrimitiveAmplitudeData ι) := inferInstance
local instance ampChainDataSpace : NormedSpace ℝ (PrimitiveAmplitudeData ι) := inferInstance
local instance ampChainDataDualNormed : NormedAddCommGroup (PrimitiveAmplitudeData ι →L[ℝ] ℝ) := inferInstance
local instance ampChainDataDualSpace : NormedSpace ℝ (PrimitiveAmplitudeData ι →L[ℝ] ℝ) := inferInstance
local instance ampChainDataT2 : T2Space (PrimitiveAmplitudeData ι) := inferInstance

theorem primitive_amplitude_chain_bound (a : ι)
    (F : JetPolynomial.Base → PrimitiveAmplitudeData ι) (x : JetPolynomial.Base)
    (hF : ContDiffAt ℝ ∞ F x) (hi : (primitiveDataOperator (F x).1).IsInvertible)
    (hp : 0 < primitiveParameterCoefficient a (F x))
    {R D : ℝ} (hR : ‖fderiv ℝ (primitiveParameterAmplitude a) (F x)‖ ≤ R)
    (hD : ‖fderiv ℝ F x‖ ≤ D) :
    ‖fderiv ℝ (primitiveParameterAmplitude a ∘ F) x‖ ≤ R*D := by
  have ho := primitiveParameterAmplitude_smoothAt a hi hp
  have hRp : 0 ≤ R := (norm_nonneg (fderiv ℝ (primitiveParameterAmplitude a) (F x))).trans hR
  rw [fderiv_comp x (ho.differentiableAt (by simp)) (hF.differentiableAt (by simp))]
  calc
    _ ≤ ‖fderiv ℝ (primitiveParameterAmplitude a) (F x)‖*‖fderiv ℝ F x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ R*D := mul_le_mul hR hD (norm_nonneg _) hRp

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
