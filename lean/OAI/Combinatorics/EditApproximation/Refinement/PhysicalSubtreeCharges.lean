import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSubtreeMass
import OAI.Combinatorics.EditApproximation.Refinement.StageComparisonCharges
import OAI.Combinatorics.EditApproximation.Refinement.StageComparisonEnergy
import OAI.Combinatorics.EditApproximation.Refinement.StageParameterBounds

namespace OAI

/-! Curvature and discrepancy are computed from the actual comparison-tree warmup masses. -/

namespace EditApproximation

open Finset

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (root : PhysicalNode M J) (K : ℕ)
  (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)

local notation "mass" => subtreeComparisonMass source target hM U N P F A hP T root rootQ
local notation "energy" => subtreeComparisonEnergy source target hM U N P F A hP T root rootQ
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))

noncomputable def subtreeComparisonCharges (d : Fin K) (path : TreeLayer M d.val) : ℝ × ℝ := by
  classical
  exact match frontier d.val path with
  | none => (0, 0)
  | some (parent, q) => if hstop : comparisonStopped source target parent q then (0, 0) else
      let hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q := by
        unfold comparisonStopped at hstop
        omega
      let node : PhysicalNode M J := physicalSubtreeNode root d.val path (by omega)
      let child := fun i s => (stageWarmupMass source target U N P F A T (physicalChild node (by dsimp only [node, physicalSubtreeNode]; omega) i, s) : ℝ)
      let b := 2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)
      let r := roundInterval (seedGridSpacing b P) q
      let action := comparisonChildren source target hM P hP parent q hc
      let hnonempty : wideActionList M parent r b P ≠ [] := by
        have hmem : action ∈ wideActionList M parent r b P :=
          (comparisonChildren_spec source target hM P hP parent q hc).1
        intro heq
        rw [heq] at hmem
        exact List.not_mem_nil hmem
      (comparisonActionCurvature source target parent r action child,
        comparisonActionMass action child - wideActionMinimum parent r b P hnonempty child)

include hsize hF hA hseed hT in
 theorem subtreeComparisonCharges_local (hscale : 2 * (refinementFactor A F : ℝ) ≤ P)
    (d : Fin K) (path : TreeLayer M d.val) :
    let charges := subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ d path
    let R := mass d.val path - ∑ i : Fin M, mass (d.val + 1) (path, i)
    let E := (∑ i : Fin M, energy (d.val + 1) (path, i)) - energy d.val path
    let movement := comparisonMovement source target P (frontier d.val path)
    let cost := comparisonActiveCost source target (frontier d.val path)
    0 ≤ charges.1 ∧ 0 ≤ charges.2 ∧
      R + charges.2 ≤ (128 * (F : ℝ)) * movement + (2 * F / (T : ℝ)) * cost ∧
      charges.1 ≤ E + 3 * movement + 2 * max (-R) 0 := by
  classical
  dsimp only
  generalize heq : frontier d.val path = state
  cases state with
  | none =>
    have hzero := subtreeComparison_step_none source target hM U N P F A hP T root rootQ d.val path heq
    have hcharges : subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ d path = (0, 0) := by
      unfold subtreeComparisonCharges
      rw [heq]
    rw [hcharges, hzero.1, hzero.2.1, hzero.2.2.1, hzero.2.2.2]
    simp only [comparisonMovement, comparisonActiveCost, sub_self, neg_zero, max_self,
      mul_zero, add_zero, le_refl, and_self]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · have hm := subtreeComparisonMass_step_stopped source target hM U N P F A hP T root rootQ d.val path parent q heq hstop
      have he := subtreeComparisonEnergy_step_stopped source target hM U N P F A hP T root rootQ d.val path parent q heq hstop
      have hcharges : subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ d path = (0, 0) := by
        unfold subtreeComparisonCharges
        rw [heq]
        simp only [dite_eq_left hstop]
      rw [hcharges, hm, he]
      simp only [comparisonMovement, comparisonActiveCost, ite_eq_left hstop, sub_self, neg_zero,
        max_self, mul_zero, add_zero, le_refl, and_self]
    · have hp := comparisonSubtree_active_source source target hM P hP root rootQ d.val path parent q heq hstop
      subst parent
      let node : PhysicalNode M J := physicalSubtreeNode root d.val path (by omega)
      have hbelow : node.1.val < J := by dsimp only [node, physicalSubtreeNode]; omega
      have hc : 0 < stateEditCost (physicalSource source node) target q := by
        change 0 < stateEditCost (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
          (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q
        unfold comparisonStopped at hstop
        omega
      have hleaf : ¬ (physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1 := fun h => hstop (Or.inl h)
      let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
      let r := roundInterval (seedGridSpacing b P) q
      let action := comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc
      let child := fun i s => (stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s) : ℝ)
      let mp := (stageWarmupMass source target U N P F A T (node, q) : ℝ)
      let W := comparisonActionMass action child
      let curvature := comparisonActionCurvature source target (physicalSourceInterval source.length node) r action child
      obtain ⟨hnonempty, hK, hG, hslack, henergy⟩ :=
        stageComparison_energy source target hM U N P F A hsize hP hF hA hseed T hT node hbelow q hc hleaf hscale
      let Z := wideActionMinimum (physicalSourceInterval source.length node) r b P hnonempty child
      have hcharges : subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ d path = (curvature, W - Z) := by
        unfold subtreeComparisonCharges
        rw [heq]
        dsimp only
        rw [dite_eq_right hstop]
        rfl
      have hparent : mass d.val path = mp := by
        unfold subtreeComparisonMass comparisonSubtreeLift
        rw [dite_eq_left (by omega : root.1.val + d.val ≤ J), heq]
        simp only [stoppedComparisonValue, ite_eq_right hstop]
        rfl
      have hchild (i : Fin M) : mass (d.val + 1) (path, i) = child i (action i) :=
        subtreeComparisonMass_step_active source target hM U N P F A hsize hP hF hA hseed T hT root rootQ
          d.val path (by omega) q heq hstop i
      have hparentEnergy : energy d.val path = (stateLengthGap (physicalSource source node) target q) ^ 2 / mp := by
        unfold subtreeComparisonEnergy
        rw [heq, hparent]
        rfl
      have hchildEnergy (i : Fin M) : energy (d.val + 1) (path, i) =
          (stateLengthGap (physicalSource source (physicalChild node hbelow i)) target (action i)) ^ 2 /
            child i (action i) :=
        subtreeComparisonEnergy_step_active source target hM U N P F A hsize hP hF hA hseed T hT root rootQ
          d.val path (by omega) q heq hstop i
      rw [hcharges, hparent, hparentEnergy]
      simp_rw [hchild, hchildEnergy]
      simp only [comparisonMovement, comparisonActiveCost, ite_eq_right hstop]
      change 0 ≤ curvature ∧ 0 ≤ W - Z ∧
        mp - W + (W - Z) ≤ (128 * (F : ℝ)) * targetEndpointDistance q r +
          (2 * F / (T : ℝ)) * stateEditCost (physicalSource source node) target q ∧
        curvature ≤ ((∑ i, (stateLengthGap (physicalSource source (physicalChild node hbelow i)) target
          (action i)) ^ 2 / child i (action i)) -
            (stateLengthGap (physicalSource source node) target q) ^ 2 / mp) +
              3 * targetEndpointDistance q r + 2 * max (-(mp - W)) 0
      have hu := (stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT (node, q)).2.2.2
      have huR : (stageInitial source target U N P F A (node, q) : ℝ) ≤
          2 * F * stateEditCost (physicalSource source node) target q := by exact_mod_cast hu
      have hdiv := div_le_div_of_nonneg_right huR (Nat.cast_nonneg (α := ℝ) T)
      have hid : (2 * (F : ℝ) * stateEditCost (physicalSource source node) target q) / T =
          (2 * F / (T : ℝ)) * stateEditCost (physicalSource source node) target q := by ring
      rw [hid] at hdiv
      exact ⟨hK, hG, hslack.trans (add_le_add_right hdiv _), henergy⟩

include hsize hF hA hseed hT in
 theorem subtreeComparisonCharges_total (hscale : 2 * (refinementFactor A F : ℝ) ≤ P)
    (hcapacity : source.length ≤ M ^ J)
    (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ v : (Σ d : Fin K, TreeLayer M d.val),
      ((subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).1 +
        (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).2)) ≤
      5000 * F * (1 + (K : ℝ) / P + (K : ℝ) / T) *
        comparisonStateCost source target (some (physicalSourceInterval source.length root, rootQ)) := by
  let ι := Σ d : Fin K, TreeLayer M d.val
  let D := comparisonStateCost source target (some (physicalSourceInterval source.length root, rootQ))
  let curvatures : ι → ℝ := fun v => (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).1
  let G : ι → ℝ := fun v => (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).2
  let R : ι → ℝ := fun v => mass v.1.val v.2 - ∑ i : Fin M, mass (v.1.val + 1) (v.2, i)
  let E : ι → ℝ := fun v => (∑ i : Fin M, energy (v.1.val + 1) (v.2, i)) - energy v.1.val v.2
  let movement : ι → ℝ := fun v => comparisonMovement source target P (frontier v.1.val v.2)
  let slack : ι → ℝ := fun v => (128 * (F : ℝ)) * movement v +
    (2 * F / (T : ℝ)) * comparisonActiveCost source target (frontier v.1.val v.2)
  have hlocal (v : ι) := subtreeComparisonCharges_local source target hM U N P F A hsize hP hF hA hseed
    T hT root K hheight rootQ hscale v.1 v.2
  have hroot := (subtreeComparisonMass_bounds source target hM U N P F A hsize hP hF hA hseed T hT root rootQ
    0 PUnit.unit).1
  have hterminal : (∑ path : TreeLayer M K, mass K path) ≤ 2 * D := by
    simp_rw [subtreeComparisonMass_terminal source target hM U N P F A hP T root rootQ K hheight hcapacity]
    exact comparison_frontier_cost_le_twice source target hM P hP _ K K le_rfl hsmall
  have hconservation : (∑ v : ι, R v) = mass 0 PUnit.unit - ∑ path : TreeLayer M K, mass K path := by
    dsimp only [R, ι]
    have h := treeLayer_sigma_sum M K (fun d path => mass d path - ∑ i : Fin M, mass (d + 1) (path, i))
    exact h.trans (tree_frontier_telescope M K mass)
  have henergy : (∑ v : ι, E v) ≤ 2 * D := by
    dsimp only [E, ι]
    have h := treeLayer_sigma_sum M K (fun d path => (∑ i : Fin M, energy (d + 1) (path, i)) - energy d path)
    apply h.le.trans
    exact subtreeComparisonEnergy_telescope source target hM U N P F A hsize hP hF hA hseed T hT root rootQ
      K hheight hcapacity hsmall
  have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg _
  have hslack (v : ι) : 0 ≤ slack v := by
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hF0)
      (comparisonMovement_nonneg source target P _))
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hF0) (Nat.cast_nonneg _))
        (comparisonActiveCost_bounds source target _).1)
  have htotal := curvature_total_from_telescope (univ : Finset ι) curvatures G R movement slack E D
    (mass 0 PUnit.unit) (∑ path : TreeLayer M K, mass K path) hroot hterminal hconservation henergy
    (fun v _ => (hlocal v).2.1) (fun v _ => hslack v)
    (fun v _ => (hlocal v).2.2.1) (fun v _ => (hlocal v).2.2.2)
  have hmove : (∑ v : ι, movement v) ≤ 4 * ((K : ℝ) / P) * D := by
    dsimp only [movement, ι]
    have heq := treeLayer_sigma_sum M K (fun d path => comparisonMovement source target P (frontier d path))
    apply heq.le.trans
    have h := comparison_total_movement_bound source target hM P hP
      (some (physicalSourceInterval source.length root, rootQ)) K hsmall
    convert h using 1
    ring
  have hactive : (∑ v : ι, comparisonActiveCost source target (frontier v.1.val v.2)) ≤ 2 * K * D := by
    dsimp only [ι]
    have heq := treeLayer_sigma_sum M K (fun d path => comparisonActiveCost source target (frontier d path))
    apply heq.le.trans
    exact comparison_total_active_cost_bound source target hM P hP _ K hsmall
  have hslackSum : (∑ v : ι, slack v) ≤
      512 * F * ((K : ℝ) / P) * D + 4 * F * ((K : ℝ) / T) * D := by
    dsimp only [slack]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have hm := mul_le_mul_of_nonneg_left hmove (show 0 ≤ 128 * (F : ℝ) from mul_nonneg (by norm_num) hF0)
    have ha := mul_le_mul_of_nonneg_left hactive (show 0 ≤ 2 * (F : ℝ) / (T : ℝ) from
      div_nonneg (mul_nonneg (by norm_num) hF0) (Nat.cast_nonneg _))
    calc
      _ ≤ (128 * (F : ℝ)) * (4 * ((K : ℝ) / P) * D) + (2 * F / (T : ℝ)) * (2 * K * D) := add_le_add hm ha
      _ = _ := by ring
  exact curvature_total_parameter_bound (comparisonStateCost_nonneg source target _)
    (by exact_mod_cast hF) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) htotal hmove hslackSum

end Stage

end EditApproximation

end OAI
