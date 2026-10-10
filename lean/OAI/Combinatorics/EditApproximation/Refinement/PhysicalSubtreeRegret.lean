import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSubtree
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalTreeRegret

namespace OAI

/-! The actual clipped refinement telescope below any original physical label. -/

namespace EditApproximation

open Finset

section Refinement

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (root : PhysicalNode M J) (rootQ : TargetInterval target.length)

noncomputable def subtreeClippedLift (t d : ℕ) (path : TreeLayer M d) : ℝ :=
  comparisonSubtreeLift source target hM P hP
    (physicalClippedTable source target U N P F A T delta choices t) root rootQ d path

local notation "lifted" => subtreeClippedLift source target hM U N P F A hP T delta choices root rootQ
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))

 theorem subtreeClippedLift_antitone (d : ℕ) (path : TreeLayer M d) : Antitone (fun t => lifted t d path) := by
  apply antitone_nat_of_succ_le
  intro t
  apply comparisonSubtreeLift_mono
  intro state
  apply max_le_max_left
  exact Rat.cast_le.mpr (physicalRefinement_nonincreasing source target U N P F A T delta choices state.1 t state.2)

include hsize hF hA hseed hT in
 theorem subtreeClippedLift_root (t : ℕ) : lifted t 0 PUnit.unit =
    max (stateEditCost (physicalSource source root) target rootQ : ℝ)
      (physicalRefinement source target U N P F A T delta choices
        root t rootQ : ℝ) := by
  have h := comparisonSubtreeLift_root source target hM P hP
    (physicalClippedTable source target U N P F A T delta choices t)
    (fun node q hstop => by
      have heq := physicalRefinement_at_stopped source target hM U N P F A hsize hP hF hA hseed
        T hT delta choices node t q hstop
      simp only [physicalClippedTable, heq, Rat.cast_natCast, max_self]) root rootQ
  simpa only [subtreeClippedLift, physicalClippedTable] using h

 theorem subtreeClippedLift_terminal (t K : ℕ) (hheight : root.1.val + K = J) (hcapacity : source.length ≤ M ^ J) (path : TreeLayer M K) :
    lifted t K path = comparisonStateCost source target (frontier K path) :=
  comparisonSubtreeLift_terminal source target hM P hP _ root rootQ K hheight hcapacity path

include hsize hF hA hseed hT in
 theorem subtree_regret_time (K : ℕ) (hheight : root.1.val + K = J) (S : ℕ) (hcapacity : source.length ≤ M ^ J)
    (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (S : ℝ) * max (stateEditCost (physicalSource source root) target rootQ : ℝ)
      (physicalRefinement source target U N P F A T delta choices
        root S rootQ : ℝ) ≤
      (S : ℝ) * ((1 + (8 * (M : ℝ) + 512 * F) * K / P) * stateEditCost (physicalSource source root) target rootQ) +
        ∑ t ∈ range S, ∑ d ∈ range K, ∑ path : TreeLayer M d,
          (lifted (t + 1) d path - (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path) -
            ∑ i : Fin M, lifted (t + 1) (d + 1) (path, i)) := by
  let D : ℝ := stateEditCost (physicalSource source root) target rootQ
  let charge := fun d (path : TreeLayer M d) => (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path)
  let terminal := (1 + 8 * (M : ℝ) * K / P) * D
  have hrootCost : comparisonStateCost source target
      (some (physicalSourceInterval source.length root, rootQ)) = D := by
    rfl
  have hterminal (t : ℕ) (_ht : t < S) : (∑ path : TreeLayer M K, lifted (t + 1) K path) ≤ terminal := by
    simp_rw [subtreeClippedLift_terminal source target hM U N P F A hP T delta choices root rootQ (t + 1) K hheight hcapacity]
    have h := comparison_frontier_cost_slack source target hM P hP
      (some (physicalSourceInterval source.length root, rootQ)) K hsmall
    rw [hrootCost] at h
    exact h
  have htime := tree_regret_time_bound M K S lifted charge terminal
    (fun t ht => subtreeClippedLift_antitone source target hM U N P F A hP T delta choices root rootQ
      0 PUnit.unit (by omega)) hterminal
  rw [subtreeClippedLift_root source target hM U N P F A hsize hP hF hA hseed T hT delta choices root rootQ S] at htime
  have hmovement := comparison_total_movement_bound source target hM P hP
    (some (physicalSourceInterval source.length root, rootQ)) K hsmall
  rw [hrootCost] at hmovement
  have hcharge : (∑ d ∈ range K, ∑ path : TreeLayer M d, charge d path) ≤ 512 * F * K * D / P := by
    dsimp only [charge]
    simp only [← mul_sum]
    have h := mul_le_mul_of_nonneg_left hmovement
      (show (0 : ℝ) ≤ 128 * F from mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    convert h using 1
    ring
  have hterm : terminal + (∑ d ∈ range K, ∑ path : TreeLayer M d, charge d path) ≤
      (1 + (8 * (M : ℝ) + 512 * F) * K / P) * D := by
    calc
      _ ≤ terminal + 512 * F * K * D / P := add_le_add_right hcharge terminal
      _ = _ := by dsimp only [terminal]; ring
  exact htime.trans (add_le_add_left (mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg S)) _)

end Refinement

end EditApproximation

end OAI
