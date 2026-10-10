import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSubtreeNear
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSubtreeExpectation
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalTreeBudget

namespace OAI

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

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
    (stageRepresentatives source target U N P F A)) (root : PhysicalNode M J) (K : ℕ) (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)
  (μ : Measure Ω) [IsProbabilityMeasure μ]

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))
local notation "charges" => subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ
local notation "prediction" => subtreeComparisonPrediction source target hM U N P F A hP T root K hheight rootQ
local notation "D" => comparisonStateCost source target
  (some (physicalSourceInterval source.length root, rootQ))

include hsize hF hA hseed hT in
 theorem subtree_comparison_expected_regret_sum (ratio : ℝ) (hratio : 0 < ratio)
    (tau : ℚ) (htau : 0 ≤ tau)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2)
    (S : ℕ) (coefficient : ℝ) (hcoef : 0 ≤ coefficient)
    (hgood : ∀ (d : Fin K) (path : TreeLayer M d.val),
      ¬ (comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).1 ∨
        comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).2) →
      |prediction d path| ≤ 1 - tau →
      (∫ ω, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
        (choices ω) root K rootQ t d path) ∂μ) ≤ coefficient * comparisonActiveCost source target (frontier d.val path)) :
    (∑ v : (Σ d : Fin K, TreeLayer M d.val),
      ∫ ω, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
        (choices ω) root K rootQ t v.1 v.2) ∂μ) ≤
      (40000 * ratio * (F : ℝ) ^ 2 * (1 + (K : ℝ) / P + (K : ℝ) / T) +
        2 * K * (1 / ratio + 4 * (tau : ℝ) * F + coefficient)) * D := by
  classical
  let cost := fun (v : Σ d : Fin K, TreeLayer M d.val) => comparisonActiveCost source target (frontier v.1.val v.2)
  let regret := fun (v : Σ d : Fin K, TreeLayer M d.val) =>
    ∫ ω, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
      (choices ω) root K rootQ t v.1 v.2) ∂μ
  let bad := fun (v : Σ d : Fin K, TreeLayer M d.val) =>
    comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).1 ∨
      comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).2
  let near := fun (v : Σ d : Fin K, TreeLayer M d.val) => 1 - tau < |prediction v.1 v.2|
  have hbad : (∑ v with bad v, regret v) ≤
      40000 * ratio * (F : ℝ) ^ 2 * (1 + (K : ℝ) / P + (K : ℝ) / T) * D := by
    rw [← integral_finsetSum _ (by intro v hv; exact .of_finite)]
    have h := integral_mono (μ := μ) (.of_finite) (integrable_const _) (fun ω =>
      subtreeComparisonBadRegret_bound source target hM U N P F A hsize hP hF hA hseed
        T hT delta (choices ω) root K hheight rootQ ratio hratio.le hscale hMP hcapacity hsmall S)
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hnear : (∑ v with ¬ bad v ∧ near v, regret v) ≤
      2 * K * (1 / ratio + 4 * (tau : ℝ) * F) * D := by
    rw [← integral_finsetSum _ (by intro v hv; exact .of_finite)]
    have h := integral_mono (μ := μ) (.of_finite) (integrable_const _) (fun ω =>
      subtreeComparisonNearRegret_bound source target hM U N P F A hsize hP hF hA hseed
        T hT delta (choices ω) root K hheight rootQ ratio hratio tau htau hscale hMP hsmall S)
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hcost : (∑ v, cost v) ≤ 2 * K * D := by
    have heq := treeLayer_sigma_sum M K (fun (d : ℕ) (path : TreeLayer M d) =>
      comparisonActiveCost source target (frontier d path))
    exact heq.le.trans (comparison_total_active_cost_bound source target hM P hP
      (some (physicalSourceInterval source.length root, rootQ)) K hsmall)
  have h := finite_three_region_budget cost regret bad near _ _ coefficient (2 * K * D)
    hbad hnear (fun v hb hn => hgood v.1 v.2 hb (le_of_not_gt hn)) hcoef
    (fun v => (comparisonActiveCost_bounds source target _).1) hcost
  convert h using 1
  ring

include hsize hF hA hseed hT in
 theorem subtree_expected_excess_of_good_nodes (ratio : ℝ) (hratio : 0 < ratio)
    (tau : ℚ) (htau : 0 ≤ tau)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2)
    (S : ℕ) (hS : 0 < S) (coefficient : ℝ) (hcoef : 0 ≤ coefficient)
    (hgood : ∀ (d : Fin K) (path : TreeLayer M d.val),
      ¬ (comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).1 ∨
        comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).2) →
      |prediction d path| ≤ 1 - tau →
      (∫ ω, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
        (choices ω) root K rootQ t d path) ∂μ) ≤ coefficient * comparisonActiveCost source target (frontier d.val path)) :
    (∫ ω, max ((physicalRefinement source target U N P F A T delta (choices ω)
        root S rootQ : ℝ) -
      stateEditCost (physicalSource source root) target rootQ) 0 ∂μ) ≤
      ((8 * (M : ℝ) + 512 * F) * K / P +
        (40000 * ratio * (F : ℝ) ^ 2 * (1 + (K : ℝ) / P + (K : ℝ) / T) +
          2 * K * (1 / ratio + 4 * (tau : ℝ) * F + coefficient)) / S) *
        stateEditCost (physicalSource source root) target rootQ := by
  classical
  let budget := fun (d : ℕ) (path : TreeLayer M d) => if hd : d < K then
    ∫ ω, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
      (choices ω) root K rootQ t ⟨d, hd⟩ path) ∂μ else 0
  have hnode (d : ℕ) (hd : d < K) (path : TreeLayer M d) :
      (∫ ω, (∑ t ∈ range S,
        (subtreeClippedLift source target hM U N P F A hP T delta (choices ω) root rootQ (t + 1) d path -
          (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path) -
          ∑ i : Fin M, subtreeClippedLift source target hM U N P F A hP T delta
            (choices ω) root rootQ (t + 1) (d + 1) (path, i))) ∂μ) ≤ budget d path := by
    simp only [budget, dite_eq_left hd, subtreeComparisonTreeRegret, le_refl]
  have htelescope := subtree_expected_excess source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices root K hheight rootQ μ S hS hcapacity hsmall budget hnode
  have hsum := subtree_comparison_expected_regret_sum source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices root K hheight rootQ μ ratio hratio tau htau hscale hMP hcapacity hsmall S coefficient hcoef hgood
  have heq : (∑ d ∈ range K, ∑ path : TreeLayer M d, budget d path) =
      ∑ v : (Σ d : Fin K, TreeLayer M d.val),
        ∫ ω, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
          (choices ω) root K rootQ t v.1 v.2) ∂μ := by
    rw [← treeLayer_sigma_sum M K budget]
    apply sum_congr rfl
    intro v _
    simp only [budget, dite_eq_left v.1.isLt]
  rw [heq] at htelescope
  have hroot : D = (stateEditCost (physicalSource source root) target rootQ : ℝ) := by
    rfl
  rw [hroot] at hsum
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg (α := ℝ) S)
  calc
    _ ≤ _ := htelescope
    _ ≤ ((8 * (M : ℝ) + 512 * F) * K / P) * stateEditCost (physicalSource source root) target rootQ +
        ((40000 * ratio * (F : ℝ) ^ 2 * (1 + (K : ℝ) / P + (K : ℝ) / T) +
          2 * K * (1 / ratio + 4 * (tau : ℝ) * F + coefficient)) *
            stateEditCost (physicalSource source root) target rootQ) / S := add_le_add_right hdiv _
    _ = _ := by ring

end Tree

end EditApproximation

end OAI
