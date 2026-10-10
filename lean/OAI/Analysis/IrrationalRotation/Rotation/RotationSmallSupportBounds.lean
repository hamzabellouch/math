import OAI.Analysis.IrrationalRotation.Rotation.RotationSmallSupport

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.RotationSmallSupport
open Rotation

theorem norm_orbitCutoff_fourierCoordinate_sq (θ : ℝ) (s : Set Circle)
    (hs : MeasurableSet s) (m n : ℤ) :
    ‖orbitCutoff θ s hs (fourierCoordinate m n)‖ ^ 2 = circleMeasure.real s := by
  rw [orbitCutoff_fourierCoordinate, SmallSupport.norm_cutoff_sq]
  have hf : ∀ᵐ x ∂circleMeasure, ‖fourierCoordinate m n x‖ ^ 2 = (1 : ℝ) := by
    filter_upwards [fourierCoordinate_ae m n] with x hx
    rw [hx, norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    simp [fourier_apply]
  calc
    (∫ x in (action θ m) ⁻¹' s, ‖fourierCoordinate m n x‖ ^ 2 ∂circleMeasure) =
        ∫ _x in (action θ m) ⁻¹' s, (1 : ℝ) ∂circleMeasure :=
      integral_congr_ae (ae_restrict_of_ae hf)
    _ = circleMeasure.real ((action θ m) ⁻¹' s) := by simp
    _ = circleMeasure.real s := by
      exact congrArg ENNReal.toReal
        ((action_measurePreserving θ m).measure_preimage hs.nullMeasurableSet)

theorem norm_orbitCutoff_fourierCoordinate (θ : ℝ) (s : Set Circle)
    (hs : MeasurableSet s) (m n : ℤ) :
    ‖orbitCutoff θ s hs (fourierCoordinate m n)‖ = Real.sqrt (circleMeasure.real s) := by
  have h := congrArg Real.sqrt (norm_orbitCutoff_fourierCoordinate_sq θ s hs m n)
  simpa only [Real.sqrt_sq (norm_nonneg _)] using h

theorem norm_error_fourierCoordinate_le (θ : ℝ) (s : Set Circle)
    (hs : MeasurableSet s) (A B : Hilbert →L[ℂ] Hilbert) {C : ℝ}
    (hbound : ‖A - B‖ ≤ C)
    (hsupport : (A - B) * (1 - orbitCutoff θ s hs) = 0) (m n : ℤ) :
    ‖A (fourierCoordinate m n) - B (fourierCoordinate m n)‖ ≤
      C * Real.sqrt (circleMeasure.real s) := by
  simpa only [norm_orbitCutoff_fourierCoordinate] using
    SmallSupport.norm_error_le_of_right_supported A B (orbitCutoff θ s hs)
      hbound hsupport (fourierCoordinate m n)

end Invariant233.RotationSmallSupport

end

end OAI
