import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftDiagonal
import OAI.Analysis.IrrationalRotation.Spectral.PolarFactor

namespace OAI

noncomputable section
namespace Invariant233.WeightedShift

local instance weightedShiftPolarIdentificationRealModule : Module ℝ (Hilbert →L[ℂ] Hilbert) :=
  Module.complexToReal (Hilbert →L[ℂ] Hilbert)

local instance weightedShiftPolarIdentificationFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℝ (Hilbert →L[ℂ] Hilbert) IsSelfAdjoint := by
  infer_instance

theorem abs_operator_of_nonneg (w : Weight) (a : ℤ → ℝ)
    (hw : ∀ k, w k = (a k : ℂ)) (ha : ∀ k, 0 ≤ a k) :
    CFC.abs (operator w) = diagonal w := by
  let U : unitary (Hilbert →L[ℂ] Hilbert) :=
    Unitary.linearIsometryEquiv.symm (shift 1)
  exact PolarFactor.abs_unitary_mul_of_nonneg U (diagonal w)
    (diagonal_nonneg_of_real_coordinates w a hw ha)

theorem polar_unitary_unique (w : Weight) (a : ℤ → ℝ)
    (hw : ∀ k, w k = (a k : ℂ)) (ha : ∀ k, 0 ≤ a k)
    (hne : ∀ k, w k ≠ 0) (V : unitary (Hilbert →L[ℂ] Hilbert))
    (hV : (V : Hilbert →L[ℂ] Hilbert) * CFC.abs (operator w) = operator w) :
    (V : Hilbert →L[ℂ] Hilbert) = (shift 1).toLinearIsometry.toContinuousLinearMap := by
  let U : unitary (Hilbert →L[ℂ] Hilbert) :=
    Unitary.linearIsometryEquiv.symm (shift 1)
  have h : (V : Hilbert →L[ℂ] Hilbert) * diagonal w =
      (U : Hilbert →L[ℂ] Hilbert) * diagonal w := by
    change (V : Hilbert →L[ℂ] Hilbert) * diagonal w = operator w
    rw [abs_operator_of_nonneg w a hw ha] at hV
    exact hV
  have hVU := PolarFactor.unitary_factor_unique_of_nonneg_ker_eq_bot V U
    (diagonal_nonneg_of_real_coordinates w a hw ha) (diagonal_ker_eq_bot w hne) h
  exact congrArg Subtype.val hVU

end Invariant233.WeightedShift

end

end OAI
