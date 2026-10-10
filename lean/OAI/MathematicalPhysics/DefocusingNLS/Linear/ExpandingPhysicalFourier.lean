import OAI.MathematicalPhysics.DefocusingNLS.Linear.FourierBoundedMultiplier
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusPhysicalL2

namespace OAI

/-! # The unweighted physical Fourier vector and volume-normalized mass -/

open MeasureTheory
open scoped ENNReal

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance expandingPhysicalFourierMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance expandingPhysicalFourierProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable def expandingPhysicalFourier (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) : FourierL2 →L[ℂ] FourierL2 :=
  fourierBoundedMultiplier ‖expandingObservationVector a k L ha ha1 hk hL‖ (norm_nonneg _)
    (fun n => ((expandingSobolevWeight a k L n)⁻¹ : ℝ))
    (fun n => lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (expandingObservationVector a k L ha ha1 hk hL) n)

@[simp] theorem expandingPhysicalFourier_apply (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) (n : frequencyLattice) :
    expandingPhysicalFourier a k L ha ha1 hk hL f n = expandingFourierCoefficient a k L f n := rfl

theorem expandingPhysicalFourier_isometry (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    torusFourierIsometry (expandingPhysicalFourier a k L ha ha1 hk hL f) =
      (expandingUnitTorusFunction a k L f).toLp 2 volume ℂ := by
  apply torusFourierIsometry_eq_continuous
  intro n
  exact expandingUnitTorusFunction_coefficient a k L ha ha1 hk hL f n

noncomputable def expandingPhysicalMassVector (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) : FourierL2 :=
  ((2 * Real.pi * L) ^ 6 : ℝ) • expandingPhysicalFourier a k L ha ha1 hk hL f

@[simp] theorem expandingPhysicalMassVector_apply (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) (n : frequencyLattice) :
    expandingPhysicalMassVector a k L ha ha1 hk hL f n =
      ((2 * Real.pi * L) ^ 6 : ℝ) • expandingFourierCoefficient a k L f n := rfl

theorem expandingPhysicalMassVector_isometry (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    torusFourierIsometry (expandingPhysicalMassVector a k L ha ha1 hk hL f) =
      torusPhysicalL2Value L (expandingUnitTorusFunction a k L f) := by
  have hs := (torusFourierIsometry.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).map_smul
    ((2 * Real.pi * L) ^ 6) (expandingPhysicalFourier a k L ha ha1 hk hL f)
  change torusFourierIsometry ((2 * Real.pi * L) ^ 6 •
    expandingPhysicalFourier a k L ha ha1 hk hL f) =
    (2 * Real.pi * L) ^ 6 • torusFourierIsometry (expandingPhysicalFourier a k L ha ha1 hk hL f) at hs
  rw [expandingPhysicalMassVector, hs, expandingPhysicalFourier_isometry]
  rfl

end DefocusingNLS

end OAI
