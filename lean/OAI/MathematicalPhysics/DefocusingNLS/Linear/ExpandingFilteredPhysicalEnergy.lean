import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOrderedPhysicalSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFilteredDerivatives
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusOrderedEnergy

namespace OAI

/-! # Physical realization of a filtered ordered derivative -/

open MeasureTheory

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance filteredPhysicalEnergyMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance filteredPhysicalEnergyProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem expandingOrderedFourierEnergy_smoothLow (a L R : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L) (hR : 0 < R)
    (j : Fin N → Fin 12) (f : FourierL2) :
    expandingOrderedFourierEnergy a L N hL j (expandingSmoothLow L R hR f) =
      expandingPhysicalMassVector a N L ha ha1 hN hL
        (expandingSmoothDerivative L R hR N j f) := by
  ext n
  rw [expandingOrderedFourierEnergy_physical, expandingPhysicalMassVector_apply]
  simp only [expandingFourierCoefficient, expandingSmoothLow_apply,
    expandingSmoothDerivative_apply, Complex.real_smul]
  push_cast
  ring

theorem expandingOrderedPhysicalEnergy_smoothLow (a L R : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L) (hR : 0 < R)
    (j : Fin N → Fin 12) (f : FourierL2) :
    expandingOrderedPhysicalEnergy a L N hL j (expandingSmoothLow L R hR f) =
      torusPhysicalL2Value L (expandingUnitTorusFunction a N L
        (expandingSmoothDerivative L R hR N j f)) := by
  change torusFourierIsometry (expandingOrderedFourierEnergy a L N hL j
    (expandingSmoothLow L R hR f)) = _
  rw [expandingOrderedFourierEnergy_smoothLow a L R N ha ha1 hN hL hR,
    expandingPhysicalMassVector_isometry]

theorem torusL2Product_physical (L : ℝ) (V f : C(T, ℂ)) :
    torusL2Product V (torusPhysicalL2Value L f) = torusPhysicalL2Value L (V * f) := by
  have hs := ((torusL2Product V).restrictScalars ℝ).map_smul
    ((2 * Real.pi * L) ^ 6) (f.toLp 2 volume ℂ)
  change torusL2Product V ((2 * Real.pi * L) ^ 6 • f.toLp 2 volume ℂ) =
    (2 * Real.pi * L) ^ 6 • torusL2Product V (f.toLp 2 volume ℂ) at hs
  rw [torusPhysicalL2Value, hs, torusL2Product_continuous]
  rfl

end DefocusingNLS

end OAI
