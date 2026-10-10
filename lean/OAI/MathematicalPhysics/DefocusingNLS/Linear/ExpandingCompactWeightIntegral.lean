import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusCompactWeightIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.UnitTorusPhysical

namespace OAI

/-! # Physical L² identity for the actual sampled torus coefficient -/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance expandingCompactWeightMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance expandingCompactWeightProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem expandingCompactWeight_integral (a k L R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (hLR : 2 * R < 2 * Real.pi * L) (K : 𝓢(E, ℂ))
    (hK : ∀ y : E, R < ‖y‖ → K y = 0) (f : FourierL2) :
    (2 * Real.pi * L) ^ 12 * (∫ x : T,
      ‖expandingUnitTorusFunction a k L
          (schwartzTorusSample a k L ha1 hk hL (radianFourierKernel K)) x *
        expandingUnitTorusFunction a k L f x‖ ^ 2) =
      ∫ y : E, ‖K y * expandingPhysicalContinuous a k L ha ha1 hk hL f y‖ ^ 2 := by
  rw [expandingUnitTorusFunction_sample a k L ha ha1 hk hL]
  rw [separatedSchwartz_torus_weighted_integral L R (by linarith) hLR K hK]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [expandingUnitTorusFunction_physical a k L ha ha1 hk hL]

end DefocusingNLS

end OAI
