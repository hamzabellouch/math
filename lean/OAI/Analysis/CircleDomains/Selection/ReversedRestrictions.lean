import OAI.Analysis.CircleDomains.Probability.ReversedPhysicalOccupation
import OAI.Analysis.CircleDomains.Probability.AffinePhysicalTimeMeasure

namespace OAI

/-! Reversing an actual affine restriction exchanges its two cuts and
preserves its exact physical cost. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem symm_affinePathTime (a b t : PathTime) :
    unitInterval.symm (affinePathTime (unitInterval.symm b) (unitInterval.symm a) t) =
      affinePathTime a b (unitInterval.symm t) := by
  apply Subtype.ext
  simp only [unitInterval.symm, affinePathTime_coe]
  change 1 - (((1 - (a : ℝ)) - (1 - (b : ℝ))) * (t : ℝ) + (1 - (b : ℝ))) =
    ((b : ℝ) - (a : ℝ)) * (1 - (t : ℝ)) + (a : ℝ)
  ring

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem affineFinitePhysicalPath_reversed {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    {a b : PathTime} (hab : a < b) :
    affineFinitePhysicalPath e hU y₀ (reversedFinitePhysicalPath e y₀ γ)
      (unitInterval.symm_lt_symm.mpr hab) =
      reversedFinitePhysicalPath e y₀ (affineFinitePhysicalPath e hU y₀ γ hab) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change γ.val (unitInterval.symm (affinePathTime (unitInterval.symm b) (unitInterval.symm a) t)) =
    γ.val (affinePathTime a b (unitInterval.symm t))
  rw [symm_affinePathTime]

end CircleDomainRigidity

end

end OAI
