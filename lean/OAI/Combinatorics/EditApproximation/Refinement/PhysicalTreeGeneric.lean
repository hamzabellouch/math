import OAI.Combinatorics.EditApproximation.Refinement.PhysicalGenericRegret
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalTreeRegret
import OAI.Combinatorics.EditApproximation.Refinement.StageComparisonBad

namespace OAI

/-! Generic cumulative regret at actual comparison-tree slots, including stopped slots. -/

namespace EditApproximation

open Finset

section Tree

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))
local notation "lifted" => physicalClippedLift source target hM U N P F A hP T delta choices rootQ

noncomputable def physicalComparisonTreeRegret (t : ℕ) (d : Fin J) (path : TreeLayer M d.val) : ℝ :=
  lifted (t + 1) d.val path - (128 * (F : ℝ)) * comparisonMovement source target P (frontier d.val path) -
    ∑ i : Fin M, lifted (t + 1) (d.val + 1) (path, i)

include hM hsize hP hF hA hseed hT in
 theorem physicalClippedTable_at_stopped (node : PhysicalNode M J) (q : TargetInterval target.length)
    (hstop : comparisonStopped source target (physicalSourceInterval source.length node) q) (t : ℕ) :
    physicalClippedTable source target U N P F A T delta choices t (node, q) =
      stateEditCost (physicalSource source node) target q := by
  have h := physicalRefinement_at_stopped source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q hstop
  simp only [physicalClippedTable, h, Rat.cast_natCast, max_self]

 theorem physicalComparisonTreeRegret_none (t : ℕ) (d : Fin J) (path : TreeLayer M d.val)
    (heq : frontier d.val path = none) :
    physicalComparisonTreeRegret source target hM U N P F A hP T delta choices rootQ t d path = 0 := by
  have hnext (i : Fin M) : frontier (d.val + 1) (path, i) = none := by
    change comparisonStep source target hM P hP (frontier d.val path) i = none
    rw [heq]
    rfl
  simp only [physicalComparisonTreeRegret, physicalClippedLift, comparisonPhysicalLift, heq, hnext,
    stoppedComparisonValue, comparisonMovement, mul_zero, sub_self, sum_const_zero]

 theorem physicalComparisonTreeRegret_stopped (t : ℕ) (d : Fin J) (path : TreeLayer M d.val)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : frontier d.val path = some (parent, q)) (hstop : comparisonStopped source target parent q) :
    physicalComparisonTreeRegret source target hM U N P F A hP T delta choices rootQ t d path = 0 := by
  classical
  have hpoint (i : Fin M) : lifted (t + 1) (d.val + 1) (path, i) =
      if i = ⟨0, hM⟩ then (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) else 0 := by
    unfold physicalClippedLift comparisonPhysicalLift
    change stoppedComparisonValue source target _
      (comparisonStep source target hM P hP (frontier d.val path) i) = _
    rw [heq]
    simp only [comparisonStep, dite_eq_left hstop]
    split_ifs <;> simp only [stoppedComparisonValue, ite_eq_left hstop]
  unfold physicalComparisonTreeRegret
  simp_rw [hpoint]
  simp only [physicalClippedLift, comparisonPhysicalLift, heq, stoppedComparisonValue, ite_eq_left hstop,
    comparisonMovement, mul_zero, sub_zero, sum_ite_eq', mem_univ, ite_true, sub_self]

include hsize hF hA hseed hT in
 theorem physicalComparisonTreeRegret_active (t : ℕ) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (q : TargetInterval target.length)
    (heq : frontier node.1.val node.2 = some (physicalSourceInterval source.length node, q))
    (hactive : ¬ comparisonStopped source target (physicalSourceInterval source.length node) q) :
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      unfold comparisonStopped at hactive
      omega
    let r := roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)) P) q
    physicalComparisonTreeRegret source target hM U N P F A hP T delta choices rootQ t ⟨node.1.val, hbelow⟩ node.2 =
      max (stateEditCost (physicalSource source node) target q : ℝ)
        (physicalRefinement source target U N P F A T delta choices node (t + 1) q : ℝ) -
          (128 * (F : ℝ)) * targetEndpointDistance q r -
          physicalComparisonClipped source target U N P F A T delta choices node hbelow
            (comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc) (t + 1) := by
  classical
  dsimp only
  have hnext (i : Fin M) := comparisonPhysicalLift_step_active source target hM P hP
    (physicalClippedTable source target U N P F A T delta choices (t + 1))
    (fun label s hstop => physicalClippedTable_at_stopped source target hM U N P F A hsize hP hF hA hseed
      T hT delta choices label s hstop (t + 1)) rootQ node hbelow q heq hactive i
  have hcurrent : comparisonPhysicalLift source target hM P hP
      (physicalClippedTable source target U N P F A T delta choices (t + 1)) rootQ node.1.val node.2 =
      physicalClippedTable source target U N P F A T delta choices (t + 1) (node, q) := by
    unfold comparisonPhysicalLift
    rw [heq]
    simp only [stoppedComparisonValue, ite_eq_right hactive]
    rw [dite_eq_left (by omega : node.1.val ≤ J)]
  have hmovement : comparisonMovement source target P (frontier node.1.val node.2) =
      targetEndpointDistance q (roundInterval (seedGridSpacing
        (2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)) P) q) := by
    rw [heq]
    simp only [comparisonMovement, ite_eq_right hactive]
    rfl
  unfold physicalComparisonTreeRegret physicalClippedLift
  rw [hcurrent, hmovement]
  simp_rw [hnext]
  rfl

include hsize hF hA hseed hT in
 theorem physicalComparisonTreeRegret_generic (hMP : 4 * (M : ℝ) / P ≤ 1)
    (S : ℕ) (d : Fin J) (path : TreeLayer M d.val) :
    (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta choices rootQ t d path) ≤
      4 * F * comparisonActiveCost source target (frontier d.val path) := by
  classical
  generalize heq : frontier d.val path = state
  cases state with
  | none =>
    simp only [physicalComparisonTreeRegret_none source target hM U N P F A hP T delta choices rootQ
      _ d path heq, sum_const_zero, comparisonActiveCost, mul_zero, le_refl]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · simp only [physicalComparisonTreeRegret_stopped source target hM U N P F A hP T delta choices rootQ
        _ d path parent q heq hstop, sum_const_zero, comparisonActiveCost, ite_eq_left hstop, mul_zero, le_refl]
    · have hp := comparisonFrontier_active_source source target hM P hP rootQ d.val path parent q heq hstop
      let node : PhysicalNode M J := ⟨⟨d.val, by omega⟩, path⟩
      have hp' : parent = physicalSourceInterval source.length node := hp
      subst parent
      have hc : 0 < stateEditCost (physicalSource source node) target q := by
        change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
          (physicalSourceInterval source.length node).hi) target q
        change ¬ ((physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1 ∨
            stateEditCost (substring source (physicalSourceInterval source.length node).lo
              (physicalSourceInterval source.length node).hi) target q = 0) at hstop
        omega
      have hleaf : ¬ (physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1 := fun h => hstop (Or.inl h)
      have h := physicalNode_generic_regret_upper source target hM U N P F A hsize hP hF hA hseed T hT
        delta choices node d.isLt hleaf q hc hMP S
      have hpoint (t : ℕ) : physicalComparisonTreeRegret source target hM U N P F A hP T delta choices rootQ t d path = _ :=
        physicalComparisonTreeRegret_active source target hM U N P F A hsize hP hF hA hseed
          T hT delta choices rootQ t node d.isLt q heq hstop
      simp_rw [hpoint]
      simpa only [comparisonActiveCost, ite_eq_right hstop, physicalSource, physicalSourceInterval, node] using h

include hsize hF hA hseed hT in
 theorem physicalComparisonBadRegret_bound (ratio : ℝ) (hratio : 0 ≤ ratio)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) (S : ℕ) :
    (∑ v : (Σ d : Fin J, TreeLayer M d.val) with
      comparisonActiveScale source target (frontier v.1.val v.2) <
        ratio * (stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).1 ∨
      comparisonActiveScale source target (frontier v.1.val v.2) <
        ratio * (stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).2,
      ∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta choices rootQ t v.1 v.2) ≤
      40000 * ratio * (F : ℝ) ^ 2 * (1 + (J : ℝ) / P + (J : ℝ) / T) *
        comparisonStateCost source target (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) := by
  classical
  have htotal := stageComparisonBadCost_bound source target hM U N P F A hsize hP hF hA hseed
    T hT rootQ ratio hratio hscale hcapacity hsmall
  have hpoint := fun (v : Σ d : Fin J, TreeLayer M d.val) =>
    physicalComparisonTreeRegret_generic source target hM U N P F A hsize hP hF hA hseed
      T hT delta choices rootQ hMP S v.1 v.2
  apply (sum_le_sum (fun v _ => hpoint v)).trans
  rw [← mul_sum]
  have h := mul_le_mul_of_nonneg_left htotal (show (0 : ℝ) ≤ 4 * F by positivity)
  unfold stageComparisonBadCost at h
  convert h using 1
  ring

end Tree

end EditApproximation

end OAI
