import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryWork
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSeedPass
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A seed entry is computed by querying the previous pass at the same
physical node in each copy, then applying the literal clamped median.
The copy coordinate never changes the dependency rank. -/

namespace EditApproximation



theorem previousPassRequest_progress {M J ny : ℕ} (T S copy : ℕ)
    (parent : PhysicalTableRequest M J ny) (hpass : 0 < parent.pass) (state : TargetInterval ny) :
    (previousPassRequest T S copy parent state).remainingDepth = parent.remainingDepth ∧
      (previousPassRequest T S copy parent state).rank T S < parent.rank T S := by
  refine ⟨rfl, ?_⟩
  exact PhysicalTableRequest.rank_lt_previous_pass T S parent _ (by
    change parent.pass - 1 < parent.pass
    omega) le_rfl





theorem physicalMedianSeedQuery_value {M J ny : ℕ} (N T S copies multiplier : ℕ)
    (parent : PhysicalTableRequest M J ny) (hpass : 0 < parent.pass) (state : TargetInterval ny)
    (values : PhysicalTableRequest M J ny → ℚ) :
    (physicalMedianSeedQuery N T S copies multiplier parent hpass state).value
      (fun child => values child.val) =
    (min N (upperMedian (List.ofFn fun copy : Fin copies =>
      ⌈(multiplier : ℚ) * values (previousPassRequest T S copy.val parent state)⌉₊)) : ℕ) := by
  unfold physicalMedianSeedQuery
  rw [FiniteQuery.collect_value]
  simp only [previousPassRead, FiniteQuery.value, List.map_map, List.ofFn_eq_map, Function.comp_def]

theorem physicalMedianSeedQuery_cost {M J ny : ℕ} (N T S copies multiplier : ℕ)
    (parent : PhysicalTableRequest M J ny) (hpass : 0 < parent.pass) (state : TargetInterval ny)
    (oracle : {child : PhysicalTableRequest M J ny //
      child.combinedRank T S < parent.combinedRank T S} → ℚ) :
    (physicalMedianSeedQuery N T S copies multiplier parent hpass state).cost oracle (fun _ => 1) = copies := by
  unfold physicalMedianSeedQuery
  rw [FiniteQuery.cost_collect]
  simp only [previousPassRead, FiniteQuery.cost, Nat.add_zero, List.map_const',
    List.length_finRange, List.sum_replicate, smul_eq_mul, Nat.mul_one]

theorem physicalMedianSeedQuery_eq_update {α Ω : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ) (a S copies : ℕ)
    (choices : Ω → PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (draws : Fin copies → Ω)
    (parent : PhysicalTableRequest M J target.length) (hpass : 0 < parent.pass)
    (state : TargetInterval target.length) (values : PhysicalTableRequest M J target.length → ℚ)
    (hvalues : ∀ copy : Fin copies,
      values (previousPassRequest T S copy.val parent state) =
        physicalRefinement source target U N P F A T delta (choices (draws copy)) parent.node S state) :
    (physicalMedianSeedQuery N T S copies a parent hpass state).value (fun child => values child.val) =
      (physicalMedianUpdate source target U N P F A T delta a S copies choices draws (parent.node, state) : ℚ) := by
  rw [physicalMedianSeedQuery_value]
  simp only [hvalues, physicalMedianUpdate, finiteMedianSeed, physicalScaledCopy]

end EditApproximation

end OAI
