import OAI.Combinatorics.EditApproximation.Geometry.ComparisonLift
import OAI.Combinatorics.EditApproximation.Refinement.StageTerminal
import OAI.Combinatorics.EditApproximation.Geometry.ComparisonAccounting

namespace OAI

/-! The time and comparison-tree telescope for the actual clipped refinement values. -/

namespace EditApproximation

open Finset

theorem comparisonPhysicalLift_mono {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table table' : PhysicalEntry M J target.length → ℝ) (hle : table ≤ table')
    (rootQ : TargetInterval target.length) (d : ℕ) (path : TreeLayer M d) :
    comparisonPhysicalLift source target hM P hP table rootQ d path ≤
      comparisonPhysicalLift source target hM P hP table' rootQ d path := by
  classical
  unfold comparisonPhysicalLift stoppedComparisonValue
  generalize comparisonFrontier source target hM P hP
    (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path = state
  cases state with
  | none => exact le_rfl
  | some state =>
    rcases state with ⟨parent, q⟩
    dsimp only
    split_ifs
    · exact le_rfl
    · exact hle _
    · exact le_rfl

section Refinement

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (rootQ : TargetInterval target.length)

noncomputable def physicalClippedTable (t : ℕ) (state : PhysicalEntry M J target.length) : ℝ :=
  max (stateEditCost (physicalSource source state.1) target state.2)
    (physicalRefinement source target U N P F A T delta choices state.1 t state.2 : ℝ)

noncomputable def physicalClippedLift (t d : ℕ) (path : TreeLayer M d) : ℝ :=
  comparisonPhysicalLift source target hM P hP
    (physicalClippedTable source target U N P F A T delta choices t) rootQ d path

local notation "lifted" => physicalClippedLift source target hM U N P F A hP T delta choices rootQ
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

 theorem physicalClippedLift_antitone (d : ℕ) (path : TreeLayer M d) : Antitone (fun t => lifted t d path) := by
  apply antitone_nat_of_succ_le
  intro t
  apply comparisonPhysicalLift_mono
  intro state
  apply max_le_max_left
  exact Rat.cast_le.mpr (physicalRefinement_nonincreasing source target U N P F A T delta choices state.1 t state.2)

include hsize hF hA hseed hT in
 theorem physicalClippedLift_root (t : ℕ) : lifted t 0 PUnit.unit =
    max (stateEditCost source target rootQ : ℝ)
      (physicalRefinement source target U N P F A T delta choices
        (⟨⟨0, by omega⟩, PUnit.unit⟩ : PhysicalNode M J) t rootQ : ℝ) := by
  have h := comparisonPhysicalLift_root source target hM P hP
    (physicalClippedTable source target U N P F A T delta choices t)
    (fun node q hstop => by
      have heq := physicalRefinement_at_stopped source target hM U N P F A hsize hP hF hA hseed
        T hT delta choices node t q hstop
      simp only [physicalClippedTable, heq, Rat.cast_natCast, max_self]) rootQ
  simpa only [physicalClippedLift, physicalClippedTable, physicalSource, physicalSourceInterval,
    sourceIntervalAt, substring, List.take_length, List.drop_zero] using h

 theorem physicalClippedLift_terminal (t : ℕ) (hcapacity : source.length ≤ M ^ J) (path : TreeLayer M J) :
    lifted t J path = comparisonStateCost source target (frontier J path) :=
  comparisonPhysicalLift_terminal source target hM P hP _ rootQ hcapacity path

include hsize hF hA hseed hT in
 theorem physical_tree_regret_time (S : ℕ) (hcapacity : source.length ≤ M ^ J)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (S : ℝ) * max (stateEditCost source target rootQ : ℝ)
      (physicalRefinement source target U N P F A T delta choices
        (⟨⟨0, by omega⟩, PUnit.unit⟩ : PhysicalNode M J) S rootQ : ℝ) ≤
      (S : ℝ) * ((1 + (8 * (M : ℝ) + 512 * F) * J / P) * stateEditCost source target rootQ) +
        ∑ t ∈ range S, ∑ d ∈ range J, ∑ path : TreeLayer M d,
          (lifted (t + 1) d path - (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path) -
            ∑ i : Fin M, lifted (t + 1) (d + 1) (path, i)) := by
  let D : ℝ := stateEditCost source target rootQ
  let charge := fun d (path : TreeLayer M d) => (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path)
  let terminal := (1 + 8 * (M : ℝ) * J / P) * D
  have hrootCost : comparisonStateCost source target
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) = D := by
    simp only [comparisonStateCost, sourceIntervalAt, substring, List.take_length, List.drop_zero, D]
  have hterminal (t : ℕ) (_ht : t < S) : (∑ path : TreeLayer M J, lifted (t + 1) J path) ≤ terminal := by
    simp_rw [physicalClippedLift_terminal source target hM U N P F A hP T delta choices rootQ (t + 1) hcapacity]
    have h := comparison_frontier_cost_slack source target hM P hP
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J hsmall
    rw [hrootCost] at h
    exact h
  have htime := tree_regret_time_bound M J S lifted charge terminal
    (fun t ht => physicalClippedLift_antitone source target hM U N P F A hP T delta choices rootQ
      0 PUnit.unit (by omega)) hterminal
  rw [physicalClippedLift_root source target hM U N P F A hsize hP hF hA hseed T hT delta choices rootQ S] at htime
  have hmovement := comparison_total_movement_bound source target hM P hP
    (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J hsmall
  rw [hrootCost] at hmovement
  have hcharge : (∑ d ∈ range J, ∑ path : TreeLayer M d, charge d path) ≤ 512 * F * J * D / P := by
    dsimp only [charge]
    simp only [← mul_sum]
    have h := mul_le_mul_of_nonneg_left hmovement
      (show (0 : ℝ) ≤ 128 * F from mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    convert h using 1
    ring
  have hterm : terminal + (∑ d ∈ range J, ∑ path : TreeLayer M d, charge d path) ≤
      (1 + (8 * (M : ℝ) + 512 * F) * J / P) * D := by
    calc
      _ ≤ terminal + 512 * F * J * D / P := add_le_add_right hcharge terminal
      _ = _ := by dsimp only [terminal]; ring
  exact htime.trans (add_le_add_left (mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg S)) _)

end Refinement

end EditApproximation

end OAI
