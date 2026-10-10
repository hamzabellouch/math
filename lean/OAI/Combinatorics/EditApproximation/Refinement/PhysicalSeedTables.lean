import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSeedPass
import OAI.Combinatorics.EditApproximation.Probability.AdaptiveSeedLaw
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Finite clamped seed tables and the exact table returned by a median pass. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory





def physicalSeedGood {α : Type*} {M J N : ℕ} (source target : List α) (A : ℚ)
    (seed : ClampedPhysicalSeed M J target.length N) : Prop :=
  ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ clampedSeedNat seed state ∧
    (clampedSeedNat seed state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2

noncomputable def physicalMedianUpdateTable {α Ω : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ) (a S copies : ℕ)
    (choices : Ω → PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (draws : Fin copies → Ω) :
    ClampedPhysicalSeed M J target.length N := fun state =>
  ⟨physicalMedianUpdate source target U N P F A T delta a S copies choices draws state,
    Nat.lt_succ_of_le (min_le_left _ _)⟩

@[simp] theorem physicalMedianUpdateTable_value {α Ω : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ) (a S copies : ℕ)
    (choices : Ω → PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (draws : Fin copies → Ω)
    (state : PhysicalEntry M J target.length) :
    clampedSeedNat (physicalMedianUpdateTable source target U N P F A T delta a S copies choices draws) state =
      physicalMedianUpdate source target U N P F A T delta a S copies choices draws state := rfl

theorem physicalMedianUpdateTable_good_iff {α Ω : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ) (a S copies : ℕ)
    (choices : Ω → PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (draws : Fin copies → Ω) :
    physicalSeedGood source target (4 * a : ℚ)
      (physicalMedianUpdateTable source target U N P F A T delta a S copies choices draws) ↔
      ∀ state : PhysicalEntry M J target.length,
        stateEditCost (physicalSource source state.1) target state.2 ≤
          physicalMedianUpdate source target U N P F A T delta a S copies choices draws state ∧
        physicalMedianUpdate source target U N P F A T delta a S copies choices draws state ≤
          4 * a * stateEditCost (physicalSource source state.1) target state.2 := by
  unfold physicalSeedGood
  simp only [physicalMedianUpdateTable_value]
  constructor
  · intro h state
    exact ⟨(h state).1, by exact_mod_cast (h state).2⟩
  · intro h state
    exact ⟨(h state).1, by exact_mod_cast (h state).2⟩

end EditApproximation

end OAI
