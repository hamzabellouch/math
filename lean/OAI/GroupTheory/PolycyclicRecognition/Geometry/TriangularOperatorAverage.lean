import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularExponentialAverage
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI

/-! # Invertibility of an averaged operator with real triangular matrix

This is the linear-algebra part of regularity of real triangular exponential
coordinates. It applies to the adjoint operator in its given triangular basis.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory
open scoped Matrix.Norms.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

def operatorExpAverage (D : E →L[ℝ] E) : E →L[ℝ] E :=
  ∫ t in (0 : ℝ)..1, NormedSpace.exp (t • D)

theorem toMatrix_operatorExpAverage (b : Module.Basis (Fin n) ℝ E)
    (D : E →L[ℝ] E) :
    LinearMap.toMatrix b b (operatorExpAverage D).toLinearMap =
      triangularExpAverage (LinearMap.toMatrix b b D.toLinearMap) := by
  let f : (E →L[ℝ] E) →+* Matrix (Fin n) (Fin n) ℝ :=
    (LinearMap.toMatrixAlgEquiv b).toRingHom.comp ContinuousLinearMap.toLinearMapRingHom
  let fL : (E →L[ℝ] E) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)
  let : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _
  let : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have he (t : ℝ) : fL (NormedSpace.exp (t • D)) =
      NormedSpace.exp (t • fL D) := by
    have h := NormedSpace.map_exp f fL.continuous_of_finiteDimensional (t • D)
    exact h.trans (congrArg NormedSpace.exp (fL.map_smul t D))
  have hc : Continuous (fun t : ℝ => NormedSpace.exp (t • D)) :=
    NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  change fL.toContinuousLinearMap (∫ t in (0 : ℝ)..1, NormedSpace.exp (t • D)) = _
  exact (fL.toContinuousLinearMap.intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := volume) 0 1)).symm.trans
      (intervalIntegral.integral_congr (fun t _ => he t))

theorem operatorExpAverage_injective (b : Module.Basis (Fin n) ℝ E)
    (D : E →L[ℝ] E) (hD : (LinearMap.toMatrix b b D.toLinearMap).IsUpperTriangular) :
    Function.Injective (operatorExpAverage D) := by
  have hunit := triangularExpAverage_isUnit (LinearMap.toMatrix b b D.toLinearMap) hD
  rw [← toMatrix_operatorExpAverage b D] at hunit
  change IsUnit ((LinearMap.toMatrixAlgEquiv b) (operatorExpAverage D).toLinearMap) at hunit
  have hu : IsUnit (operatorExpAverage D).toLinearMap := by
    simpa only [AlgEquiv.symm_apply_apply] using
      hunit.map (LinearMap.toMatrixAlgEquiv b).symm
  exact LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot _).mp hu)

end PolycyclicRecognition

end

end OAI
