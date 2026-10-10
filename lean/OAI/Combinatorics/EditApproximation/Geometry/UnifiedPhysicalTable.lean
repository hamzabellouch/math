import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalRefinement

namespace OAI

/-! The cache's unified index uses warmup indices through T and then
refinement indices T+t. Refinement zero is exactly warmup T, including
terminal physical nodes and short source intervals. -/

namespace EditApproximation

theorem physicalLocalWarmup_terminal {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (node : PhysicalNode M J) (t : ℕ)
    (q : TargetInterval target.length)
    (hterminal : ¬ node.1.val < J ∨
      (physicalSourceInterval source.length node).hi - (physicalSourceInterval source.length node).lo ≤ 1) :
    physicalLocalWarmup source target U N P F A t (node, q) =
      stageInitial source target U N P F A (node, q) := by
  cases t with
  | zero => rfl
  | succ t =>
    rw [physicalLocalWarmup]
    rcases hterminal with hdepth | hwidth
    · rw [dite_eq_right hdepth]
    · split_ifs <;> rfl

theorem physicalLocalRefinement_zero {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent Q : ℕ) (A tau delta : ℚ) (T : ℕ)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (online : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
      TargetInterval target.length → List (PhysicalRationalAction M target.length))
    (node : PhysicalNode M J) (q : TargetInterval target.length) :
    physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online node 0 q =
      physicalLocalWarmup source target U N P F A T (node, q) := by
  rw [physicalLocalRefinement]
  split_ifs with hbelow hleaf
  · exact (physicalLocalWarmup_terminal source target U N P F A node T q (Or.inr hleaf)).symm
  · rfl
  · exact (physicalLocalWarmup_terminal source target U N P F A node T q (Or.inl hbelow)).symm

section Unified

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent Q : ℕ) (A tau delta : ℚ) (T : ℕ)
  (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
  (online : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
    TargetInterval target.length → List (PhysicalRationalAction M target.length))

def unifiedPhysicalValue (node : PhysicalNode M J) (index : ℕ) (q : TargetInterval target.length) : ℚ :=
  if index ≤ T then physicalLocalWarmup source target U N P F A index (node, q)
  else physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online node (index - T) q

theorem unifiedPhysicalValue_warmup (node : PhysicalNode M J) (index : ℕ)
    (hi : index ≤ T) (q : TargetInterval target.length) :
    unifiedPhysicalValue source target U N P F exponent Q A tau delta T draw online node index q =
      physicalLocalWarmup source target U N P F A index (node, q) := ite_eq_left hi

theorem unifiedPhysicalValue_refinement (node : PhysicalNode M J) (t : ℕ)
    (q : TargetInterval target.length) :
    unifiedPhysicalValue source target U N P F exponent Q A tau delta T draw online node (T + t) q =
      physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online node t q := by
  cases t with
  | zero =>
    rw [Nat.add_zero, unifiedPhysicalValue_warmup source target U N P F exponent Q A tau delta T draw online node T le_rfl]
    exact (physicalLocalRefinement_zero source target U N P F exponent Q A tau delta T draw online node q).symm
  | succ t =>
    unfold unifiedPhysicalValue
    rw [ite_eq_right (by omega : ¬ T + (t + 1) ≤ T), Nat.add_sub_cancel_left]

end Unified

end EditApproximation

end OAI
