import OAI.Combinatorics.EditApproximation.Refinement.PhysicalGenericRegret
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSubtreeRegret
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalTreeGeneric
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSubtreeBad

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
    (stageRepresentatives source target U N P F A)) (root : PhysicalNode M J) (K : ℕ) (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))
local notation "lifted" => subtreeClippedLift source target hM U N P F A hP T delta choices root rootQ

noncomputable def subtreeComparisonTreeRegret (t : ℕ) (d : Fin K) (path : TreeLayer M d.val) : ℝ :=
  lifted (t + 1) d.val path - (128 * (F : ℝ)) * comparisonMovement source target P (frontier d.val path) -
    ∑ i : Fin M, lifted (t + 1) (d.val + 1) (path, i)

 theorem subtreeComparisonTreeRegret_none (t : ℕ) (d : Fin K) (path : TreeLayer M d.val)
    (heq : frontier d.val path = none) :
    subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t d path = 0 := by
  have hnext (i : Fin M) : frontier (d.val + 1) (path, i) = none := by
    change comparisonStep source target hM P hP (frontier d.val path) i = none
    rw [heq]
    rfl
  simp only [subtreeComparisonTreeRegret, subtreeClippedLift, comparisonSubtreeLift, heq, hnext,
    stoppedComparisonValue, comparisonMovement, mul_zero, sub_self, sum_const_zero]

 theorem subtreeComparisonTreeRegret_stopped (t : ℕ) (d : Fin K) (path : TreeLayer M d.val)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : frontier d.val path = some (parent, q)) (hstop : comparisonStopped source target parent q) :
    subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t d path = 0 := by
  classical
  have hpoint (i : Fin M) : lifted (t + 1) (d.val + 1) (path, i) =
      if i = ⟨0, hM⟩ then (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) else 0 := by
    unfold subtreeClippedLift comparisonSubtreeLift
    change stoppedComparisonValue source target _
      (comparisonStep source target hM P hP (frontier d.val path) i) = _
    rw [heq]
    simp only [comparisonStep, dite_eq_left hstop]
    split_ifs <;> simp only [stoppedComparisonValue, ite_eq_left hstop]
  unfold subtreeComparisonTreeRegret
  simp_rw [hpoint]
  simp only [subtreeClippedLift, comparisonSubtreeLift, heq, stoppedComparisonValue, ite_eq_left hstop,
    comparisonMovement, mul_zero, sub_zero, sum_ite_eq', mem_univ, ite_true, sub_self]

include hsize hF hA hseed hT in
 theorem subtreeComparisonTreeRegret_active (t : ℕ) (d : Fin K) (path : TreeLayer M d.val)
    (q : TargetInterval target.length)
    (heq : frontier d.val path = some
      (physicalSourceInterval source.length (physicalSubtreeNode root d.val path (by omega)), q))
    (hactive : ¬ comparisonStopped source target
      (physicalSourceInterval source.length (physicalSubtreeNode root d.val path (by omega))) q) :
    let node := physicalSubtreeNode root d.val path (by omega)
    let hbelow : node.1.val < J := by dsimp only [node, physicalSubtreeNode]; omega
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      dsimp only [node]
      unfold comparisonStopped at hactive
      omega
    let r := roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)) P) q
    subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t d path =
      max (stateEditCost (physicalSource source node) target q : ℝ)
        (physicalRefinement source target U N P F A T delta choices node (t + 1) q : ℝ) -
          (128 * (F : ℝ)) * targetEndpointDistance q r -
          physicalComparisonClipped source target U N P F A T delta choices node hbelow
            (comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc) (t + 1) := by
  classical
  dsimp only
  have hnext (i : Fin M) := comparisonSubtreeLift_step_active source target hM P hP
    (physicalClippedTable source target U N P F A T delta choices (t + 1))
    (fun label s hstop => physicalClippedTable_at_stopped source target hM U N P F A hsize hP hF hA hseed
      T hT delta choices label s hstop (t + 1)) root rootQ d.val path (by omega) q heq hactive i
  have hcurrent : comparisonSubtreeLift source target hM P hP
      (physicalClippedTable source target U N P F A T delta choices (t + 1)) root rootQ d.val path =
      physicalClippedTable source target U N P F A T delta choices (t + 1)
        (physicalSubtreeNode root d.val path (by omega), q) := by
    unfold comparisonSubtreeLift
    rw [heq]
    simp only [stoppedComparisonValue, ite_eq_right hactive]
    rw [dite_eq_left (by omega : root.1.val + d.val ≤ J)]
  have hmovement : comparisonMovement source target P (frontier d.val path) =
      targetEndpointDistance q (roundInterval (seedGridSpacing
        (2 ^ Nat.log 2 (stateEditCost (physicalSource source (physicalSubtreeNode root d.val path (by omega))) target q)) P) q) := by
    rw [heq]
    simp only [comparisonMovement, ite_eq_right hactive]
    rfl
  unfold subtreeComparisonTreeRegret subtreeClippedLift
  rw [hcurrent, hmovement]
  simp_rw [hnext]
  rfl

include hsize hF hA hseed hT hheight in
 theorem subtreeComparisonTreeRegret_generic (hMP : 4 * (M : ℝ) / P ≤ 1)
    (S : ℕ) (d : Fin K) (path : TreeLayer M d.val) :
    (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t d path) ≤
      4 * F * comparisonActiveCost source target (frontier d.val path) := by
  classical
  generalize heq : frontier d.val path = state
  cases state with
  | none =>
    simp only [subtreeComparisonTreeRegret_none source target hM U N P F A hP T delta choices root K rootQ
      _ d path heq, sum_const_zero, comparisonActiveCost, mul_zero, le_refl]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · simp only [subtreeComparisonTreeRegret_stopped source target hM U N P F A hP T delta choices root K rootQ
        _ d path parent q heq hstop, sum_const_zero, comparisonActiveCost, ite_eq_left hstop, mul_zero, le_refl]
    · have hp := comparisonSubtree_active_source source target hM P hP root rootQ d.val path parent q heq hstop
      let node : PhysicalNode M J := physicalSubtreeNode root d.val path (by omega)
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
        delta choices node (by dsimp only [node, physicalSubtreeNode]; omega) hleaf q hc hMP S
      have hpoint (t : ℕ) : subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t d path = _ :=
        subtreeComparisonTreeRegret_active source target hM U N P F A hsize hP hF hA hseed
          T hT delta choices root K hheight rootQ t d path q heq hstop
      simp_rw [hpoint]
      have hstop' : ¬ comparisonStopped source target
          (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)) q := hstop
      simpa only [comparisonActiveCost, ite_eq_right hstop', physicalSource, physicalSourceInterval,
        node, physicalSubtreeNode] using h

include hsize hF hA hseed hT in
 theorem subtreeComparisonBadRegret_bound (ratio : ℝ) (hratio : 0 ≤ ratio)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) (S : ℕ) :
    (∑ v : (Σ d : Fin K, TreeLayer M d.val) with
      comparisonActiveScale source target (frontier v.1.val v.2) <
        ratio * (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).1 ∨
      comparisonActiveScale source target (frontier v.1.val v.2) <
        ratio * (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).2,
      ∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t v.1 v.2) ≤
      40000 * ratio * (F : ℝ) ^ 2 * (1 + (K : ℝ) / P + (K : ℝ) / T) *
        comparisonStateCost source target (some (physicalSourceInterval source.length root, rootQ)) := by
  classical
  have htotal := subtreeComparisonBadCost_bound source target hM U N P F A hsize hP hF hA hseed
    T hT root K hheight rootQ ratio hratio hscale hcapacity hsmall
  have hpoint := fun (v : Σ d : Fin K, TreeLayer M d.val) =>
    subtreeComparisonTreeRegret_generic source target hM U N P F A hsize hP hF hA hseed
      T hT delta choices root K hheight rootQ hMP S v.1 v.2
  apply (sum_le_sum (fun v _ => hpoint v)).trans
  rw [← mul_sum]
  have h := mul_le_mul_of_nonneg_left htotal (show (0 : ℝ) ≤ 4 * F by positivity)
  unfold subtreeComparisonBadCost at h
  convert h using 1
  ring

end Tree

end EditApproximation

end OAI
