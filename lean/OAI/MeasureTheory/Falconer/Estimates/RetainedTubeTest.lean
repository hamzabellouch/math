import OAI.MeasureTheory.Falconer.Estimates.TroublesomePair
import Mathlib.Probability.ConditionalProbability

namespace OAI

/-! # Retained pairs control the original full parent-cell tube mass -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem tube_mass_of_not_troublesome (μ : Measure (Space d)) (c z x : Space d)
    (r D B W : ℝ) (F : ℝ≥0∞)
    (hnot : (z,x) ∉ troublesomePair μ c r D B W F)
    (hsep : r ≤ ‖c-x‖) (hne : z ≠ x) (hD : ‖z-c‖ ≤ D) (hB : ‖z‖ ≤ B) :
    radialTubeMass μ W (z,x) ≤ F := by
  by_contra! hmass
  exact hnot ⟨hsep,hne,hD,hB,hmass⟩

theorem original_tube_test_of_not_troublesome (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (Q : Set (Space d)) (hQ : MeasurableSet Q) (c z x : Space d)
    (r D B W : ℝ) (F : ℝ≥0∞)
    (hnot : (z,x) ∉ troublesomePair (ProbabilityTheory.cond μ Q) c r D B W F)
    (hsep : r ≤ ‖c-x‖) (hne : z ≠ x) (hD : ‖z-c‖ ≤ D) (hB : ‖z‖ ≤ B) :
    μ (Q ∩ {y | ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ W}) ≤ F*μ Q := by
  have hm := tube_mass_of_not_troublesome (ProbabilityTheory.cond μ Q) c z x r D B W F
    hnot hsep hne hD hB
  rw [← ProbabilityTheory.cond_mul_eq_inter hQ _ μ]
  exact mul_le_mul' hm le_rfl

end Falconer

end OAI
