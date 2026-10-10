import OAI.Combinatorics.EditApproximation.Refinement.PhysicalTreeGeneric
import OAI.Combinatorics.EditApproximation.Refinement.StageComparisonPrediction

namespace OAI

/-! Actual non-bad nodes with near-unit length-gap prediction have small regret. -/

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
local notation "charges" => stageComparisonCharges source target hM U N P F A hP T rootQ
local notation "prediction" => stageComparisonPrediction source target hM U N P F A hP T rootQ

include hsize hF hA hseed hT in
 theorem physicalComparisonTreeRegret_near (ratio : ℝ) (hratio : 0 < ratio)
    (tau : ℚ) (htau : 0 ≤ tau)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (S : ℕ) (d : Fin J) (path : TreeLayer M d.val)
    (hnotbad : ¬ (comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).1 ∨
      comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).2))
    (hnear : 1 - tau < |prediction d path|) :
    (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta choices rootQ t d path) ≤
      (1 / ratio + 4 * (tau : ℝ) * F) * comparisonActiveCost source target (frontier d.val path) := by
  classical
  generalize heq : frontier d.val path = state at hnotbad ⊢
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
      change ¬ comparisonStopped source target (physicalSourceInterval source.length node) q at hstop
      have hc : 0 < stateEditCost (physicalSource source node) target q := by
        change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
          (physicalSourceInterval source.length node).hi) target q
        change ¬ ((physicalSourceInterval source.length node).hi - (physicalSourceInterval source.length node).lo ≤ 1 ∨
          stateEditCost (substring source (physicalSourceInterval source.length node).lo
            (physicalSourceInterval source.length node).hi) target q = 0) at hstop
        omega
      let b : ℕ := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
      let r := roundInterval (seedGridSpacing b P) q
      let action := comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc
      let child := physicalBandChildMassTable source target U N P F A T node d.isLt
      have hspec := comparisonChildren_spec source target hM P hP (physicalSourceInterval source.length node) q hc
      have hn : wideActionList M (physicalSourceInterval source.length node) r b P ≠ [] := by
        intro hnil
        have hmem := hspec.1
        change action ∈ wideActionList M (physicalSourceInterval source.length node) r b P at hmem
        rw [hnil] at hmem
        exact List.not_mem_nil hmem
      have hcharges := stageComparisonCharges_active source target hM U N P F A hP T rootQ d path q heq hstop hc hn
      have hprediction := stageComparisonPrediction_active source target hM U N P F A hP T rootQ d path q heq hstop hn
      have hG := (nonbad_charge_bounds _ ratio _ _ hratio hnotbad).2
      change (charges d path).2 ≤ comparisonActiveScale source target
        (some (physicalSourceInterval source.length node, q)) / ratio at hG
      have hscaleEq : comparisonActiveScale source target
          (some (physicalSourceInterval source.length node, q)) = (b : ℝ) := by
        simp only [comparisonActiveScale, ite_eq_right hstop]
        rfl
      rw [hscaleEq, hcharges] at hG
      have hb : (b : ℝ) ≤ stateEditCost (physicalSource source node) target q := by
        exact_mod_cast (cost_dyadicScale _ _ hc le_rfl).2.1
      have hGcost : comparisonActionMass action (fun i s => (child i s : ℝ)) -
          wideActionMinimum (physicalSourceInterval source.length node) r b P hn (fun i s => (child i s : ℝ)) ≤
          (1 / ratio) * stateEditCost (physicalSource source node) target q := by
        have h := hG.trans (div_le_div_of_nonneg_right hb hratio.le)
        simpa only [one_div_mul_eq_div, action, child, r, b, node,
          physicalSource, physicalSourceInterval] using h
      rw [hprediction] at hnear
      have hleaf : ¬ (physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1 := fun h => hstop (Or.inl h)
      have h := physicalNode_near_length_gap_regret source target hM U N P F A hsize hP hF hA hseed T hT
        delta choices node d.isLt hleaf q hc hscale hMP hn tau htau hnear (1 / ratio) hGcost S
      have hpoint (t : ℕ) : physicalComparisonTreeRegret source target hM U N P F A hP T delta choices rootQ t d path = _ :=
        physicalComparisonTreeRegret_active source target hM U N P F A hsize hP hF hA hseed
          T hT delta choices rootQ t node d.isLt q heq hstop
      simp_rw [hpoint]
      have hstop' : ¬ comparisonStopped source target (sourceIntervalAt M source.length d.val path) q := hstop
      simpa only [comparisonActiveCost, ite_eq_right hstop', physicalSource, physicalSourceInterval, node] using h

include hsize hF hA hseed hT in
 theorem physicalComparisonNearRegret_bound (ratio : ℝ) (hratio : 0 < ratio)
    (tau : ℚ) (htau : 0 ≤ tau)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) (S : ℕ) :
    (∑ v : (Σ d : Fin J, TreeLayer M d.val) with
      (¬ (comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).1 ∨
        comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).2)) ∧
      1 - tau < |prediction v.1 v.2|,
      ∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta choices rootQ t v.1 v.2) ≤
      2 * (J : ℝ) * (1 / ratio + 4 * (tau : ℝ) * F) *
        comparisonStateCost source target (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) := by
  classical
  let coefficient : ℝ := 1 / ratio + 4 * (tau : ℝ) * F
  have hcoef : 0 ≤ coefficient := add_nonneg (div_nonneg zero_le_one hratio.le)
    (mul_nonneg (mul_nonneg (by norm_num) ((Rat.cast_nonneg (K := ℝ)).mpr htau)) (Nat.cast_nonneg _))
  have hcost : (∑ v : (Σ d : Fin J, TreeLayer M d.val), comparisonActiveCost source target (frontier v.1.val v.2)) ≤
      2 * J * comparisonStateCost source target (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) := by
    have heq := treeLayer_sigma_sum M J (fun (d : ℕ) (path : TreeLayer M d) =>
      comparisonActiveCost source target (frontier d path))
    exact heq.le.trans (comparison_total_active_cost_bound source target hM P hP
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J hsmall)
  apply (sum_le_sum (fun v hv => physicalComparisonTreeRegret_near source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices rootQ ratio hratio tau htau hscale hMP S v.1 v.2
      (mem_filter.mp hv).2.1 (mem_filter.mp hv).2.2)).trans
  rw [← mul_sum]
  have hsub : (∑ v : (Σ d : Fin J, TreeLayer M d.val) with
      (¬ (comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).1 ∨
        comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).2)) ∧
      1 - tau < |prediction v.1 v.2|,
      comparisonActiveCost source target (frontier v.1.val v.2)) ≤
      ∑ v : (Σ d : Fin J, TreeLayer M d.val), comparisonActiveCost source target (frontier v.1.val v.2) := by
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun v _ _ => (comparisonActiveCost_bounds source target _).1)
  have h := mul_le_mul_of_nonneg_left (hsub.trans hcost) hcoef
  convert h using 1
  ring

end Tree

end EditApproximation

end OAI
