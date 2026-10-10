import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSubtreeCharges
import OAI.Combinatorics.EditApproximation.Refinement.StageComparisonBad

namespace OAI

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

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))

noncomputable def subtreeComparisonBadCost (ratio : ℝ) : ℝ := by
  classical
  exact ∑ v : (Σ d : Fin K, TreeLayer M d.val) with
    comparisonActiveScale source target (frontier v.1.val v.2) <
      ratio * (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).1 ∨
    comparisonActiveScale source target (frontier v.1.val v.2) <
      ratio * (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).2,
    comparisonActiveCost source target (frontier v.1.val v.2)

include hsize hF hA hseed hT in
 theorem subtreeComparisonBadCost_bound (ratio : ℝ) (hratio : 0 ≤ ratio)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hcapacity : source.length ≤ M ^ J)
    (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    subtreeComparisonBadCost source target hM U N P F A hP T root K hheight rootQ ratio ≤
      10000 * ratio * F * (1 + (K : ℝ) / P + (K : ℝ) / T) *
        comparisonStateCost source target (some (physicalSourceInterval source.length root, rootQ)) := by
  classical
  let ι := Σ d : Fin K, TreeLayer M d.val
  let cost : ι → ℝ := fun v => comparisonActiveCost source target (frontier v.1.val v.2)
  let scale : ι → ℝ := fun v => comparisonActiveScale source target (frontier v.1.val v.2)
  let curvature : ι → ℝ := fun v => (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).1
  let G : ι → ℝ := fun v => (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).2
  have h := bad_node_cost_from_curvature (univ : Finset ι) cost scale curvature G ratio _ hratio
    (fun v _ => (comparisonActiveCost_scale source target _).2)
    (fun v _ => (subtreeComparisonCharges_local source target hM U N P F A hsize hP hF hA hseed
      T hT root K hheight rootQ hscale v.1 v.2).1)
    (fun v _ => (subtreeComparisonCharges_local source target hM U N P F A hsize hP hF hA hseed
      T hT root K hheight rootQ hscale v.1 v.2).2.1)
    (subtreeComparisonCharges_total source target hM U N P F A hsize hP hF hA hseed
      T hT root K hheight rootQ hscale hcapacity hsmall)
  change subtreeComparisonBadCost source target hM U N P F A hP T root K hheight rootQ ratio ≤ _ at h
  convert h using 1
  ring

end Stage

end EditApproximation

end OAI
