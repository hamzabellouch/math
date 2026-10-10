import OAI.Combinatorics.EditApproximation.Refinement.PhysicalTreeNear
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalTreeExpectation

namespace OAI

/-! Summing the three actual comparison-node classes in the expected telescope. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem finite_three_region_budget {ι : Type*} [Fintype ι]
    (cost regret : ι → ℝ) (bad near : ι → Prop) [DecidablePred bad] [DecidablePred near]
    (badBudget nearBudget coefficient costBudget : ℝ)
    (hbad : (∑ i with bad i, regret i) ≤ badBudget)
    (hnear : (∑ i with ¬ bad i ∧ near i, regret i) ≤ nearBudget)
    (hgood : ∀ i, ¬ bad i → ¬ near i → regret i ≤ coefficient * cost i)
    (hcoef : 0 ≤ coefficient) (hcost : ∀ i, 0 ≤ cost i)
    (htotal : (∑ i, cost i) ≤ costBudget) :
    (∑ i, regret i) ≤ badBudget + nearBudget + coefficient * costBudget := by
  classical
  have hsplit : (∑ i, regret i) = (∑ i with bad i, regret i) +
      (∑ i with ¬ bad i ∧ near i, regret i) +
      (∑ i with ¬ bad i ∧ ¬ near i, regret i) := by
    simp only [sum_filter]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    by_cases hb : bad i <;> by_cases hn : near i <;> simp only [hb, hn, not_true_eq_false,
      not_false_eq_true, and_false, and_true, ite_true, ite_false, add_zero, zero_add]
  have hgoodSum : (∑ i with ¬ bad i ∧ ¬ near i, regret i) ≤ coefficient * costBudget := by
    apply (sum_le_sum (fun i hi => hgood i (mem_filter.mp hi).2.1 (mem_filter.mp hi).2.2)).trans
    rw [← mul_sum]
    apply mul_le_mul_of_nonneg_left _ hcoef
    apply le_trans _ htotal
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => hcost i)
  rw [hsplit]
  linarith only [hbad, hnear, hgoodSum]

section Tree

variable {α Ω : Type*} [DecidableEq α] [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {M J : ℕ} (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : Ω → PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (rootQ : TargetInterval target.length)
  (μ : Measure Ω) [IsProbabilityMeasure μ]

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))
local notation "charges" => stageComparisonCharges source target hM U N P F A hP T rootQ
local notation "prediction" => stageComparisonPrediction source target hM U N P F A hP T rootQ
local notation "D" => comparisonStateCost source target
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

include hsize hF hA hseed hT in
 theorem physical_comparison_expected_regret_sum (ratio : ℝ) (hratio : 0 < ratio)
    (tau : ℚ) (htau : 0 ≤ tau)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2)
    (S : ℕ) (coefficient : ℝ) (hcoef : 0 ≤ coefficient)
    (hgood : ∀ (d : Fin J) (path : TreeLayer M d.val),
      ¬ (comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).1 ∨
        comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).2) →
      |prediction d path| ≤ 1 - tau →
      (∫ ω, (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta
        (choices ω) rootQ t d path) ∂μ) ≤ coefficient * comparisonActiveCost source target (frontier d.val path)) :
    (∑ v : (Σ d : Fin J, TreeLayer M d.val),
      ∫ ω, (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta
        (choices ω) rootQ t v.1 v.2) ∂μ) ≤
      (40000 * ratio * (F : ℝ) ^ 2 * (1 + (J : ℝ) / P + (J : ℝ) / T) +
        2 * J * (1 / ratio + 4 * (tau : ℝ) * F + coefficient)) * D := by
  classical
  let cost := fun (v : Σ d : Fin J, TreeLayer M d.val) => comparisonActiveCost source target (frontier v.1.val v.2)
  let regret := fun (v : Σ d : Fin J, TreeLayer M d.val) =>
    ∫ ω, (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta
      (choices ω) rootQ t v.1 v.2) ∂μ
  let bad := fun (v : Σ d : Fin J, TreeLayer M d.val) =>
    comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).1 ∨
      comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).2
  let near := fun (v : Σ d : Fin J, TreeLayer M d.val) => 1 - tau < |prediction v.1 v.2|
  have hbad : (∑ v with bad v, regret v) ≤
      40000 * ratio * (F : ℝ) ^ 2 * (1 + (J : ℝ) / P + (J : ℝ) / T) * D := by
    rw [← integral_finsetSum _ (by intro v hv; exact .of_finite)]
    have h := integral_mono (μ := μ) (.of_finite) (integrable_const _) (fun ω =>
      physicalComparisonBadRegret_bound source target hM U N P F A hsize hP hF hA hseed
        T hT delta (choices ω) rootQ ratio hratio.le hscale hMP hcapacity hsmall S)
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hnear : (∑ v with ¬ bad v ∧ near v, regret v) ≤
      2 * J * (1 / ratio + 4 * (tau : ℝ) * F) * D := by
    rw [← integral_finsetSum _ (by intro v hv; exact .of_finite)]
    have h := integral_mono (μ := μ) (.of_finite) (integrable_const _) (fun ω =>
      physicalComparisonNearRegret_bound source target hM U N P F A hsize hP hF hA hseed
        T hT delta (choices ω) rootQ ratio hratio tau htau hscale hMP hsmall S)
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hcost : (∑ v, cost v) ≤ 2 * J * D := by
    have heq := treeLayer_sigma_sum M J (fun (d : ℕ) (path : TreeLayer M d) =>
      comparisonActiveCost source target (frontier d path))
    exact heq.le.trans (comparison_total_active_cost_bound source target hM P hP
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J hsmall)
  have h := finite_three_region_budget cost regret bad near _ _ coefficient (2 * J * D)
    hbad hnear (fun v hb hn => hgood v.1 v.2 hb (le_of_not_gt hn)) hcoef
    (fun v => (comparisonActiveCost_bounds source target _).1) hcost
  convert h using 1
  ring

include hsize hF hA hseed hT in
 theorem physical_tree_expected_excess_of_good_nodes (ratio : ℝ) (hratio : 0 < ratio)
    (tau : ℚ) (htau : 0 ≤ tau)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2)
    (S : ℕ) (hS : 0 < S) (coefficient : ℝ) (hcoef : 0 ≤ coefficient)
    (hgood : ∀ (d : Fin J) (path : TreeLayer M d.val),
      ¬ (comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).1 ∨
        comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).2) →
      |prediction d path| ≤ 1 - tau →
      (∫ ω, (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta
        (choices ω) rootQ t d path) ∂μ) ≤ coefficient * comparisonActiveCost source target (frontier d.val path)) :
    (∫ ω, max ((physicalRefinement source target U N P F A T delta (choices ω)
        (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J) S rootQ : ℝ) -
      stateEditCost source target rootQ) 0 ∂μ) ≤
      ((8 * (M : ℝ) + 512 * F) * J / P +
        (40000 * ratio * (F : ℝ) ^ 2 * (1 + (J : ℝ) / P + (J : ℝ) / T) +
          2 * J * (1 / ratio + 4 * (tau : ℝ) * F + coefficient)) / S) *
        stateEditCost source target rootQ := by
  classical
  let budget := fun (d : ℕ) (path : TreeLayer M d) => if hd : d < J then
    ∫ ω, (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta
      (choices ω) rootQ t ⟨d, hd⟩ path) ∂μ else 0
  have hnode (d : ℕ) (hd : d < J) (path : TreeLayer M d) :
      (∫ ω, (∑ t ∈ range S,
        (physicalClippedLift source target hM U N P F A hP T delta (choices ω) rootQ (t + 1) d path -
          (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path) -
          ∑ i : Fin M, physicalClippedLift source target hM U N P F A hP T delta
            (choices ω) rootQ (t + 1) (d + 1) (path, i))) ∂μ) ≤ budget d path := by
    simp only [budget, dite_eq_left hd, physicalComparisonTreeRegret, le_refl]
  have htelescope := physical_tree_expected_excess source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices rootQ μ S hS hcapacity hsmall budget hnode
  have hsum := physical_comparison_expected_regret_sum source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices rootQ μ ratio hratio tau htau hscale hMP hcapacity hsmall S coefficient hcoef hgood
  have heq : (∑ d ∈ range J, ∑ path : TreeLayer M d, budget d path) =
      ∑ v : (Σ d : Fin J, TreeLayer M d.val),
        ∫ ω, (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta
          (choices ω) rootQ t v.1 v.2) ∂μ := by
    rw [← treeLayer_sigma_sum M J budget]
    apply sum_congr rfl
    intro v _
    simp only [budget, dite_eq_left v.1.isLt]
  rw [heq] at htelescope
  have hroot : D = (stateEditCost source target rootQ : ℝ) := by
    simp only [comparisonStateCost, sourceIntervalAt, substring, List.take_length, List.drop_zero]
  rw [hroot] at hsum
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg (α := ℝ) S)
  calc
    _ ≤ _ := htelescope
    _ ≤ ((8 * (M : ℝ) + 512 * F) * J / P) * stateEditCost source target rootQ +
        ((40000 * ratio * (F : ℝ) ^ 2 * (1 + (J : ℝ) / P + (J : ℝ) / T) +
          2 * J * (1 / ratio + 4 * (tau : ℝ) * F + coefficient)) *
            stateEditCost source target rootQ) / S := add_le_add_right hdiv _
    _ = _ := by ring

end Tree

end EditApproximation

end OAI
