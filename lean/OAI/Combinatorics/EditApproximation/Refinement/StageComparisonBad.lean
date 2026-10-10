import OAI.Combinatorics.EditApproximation.Refinement.StageComparisonCharges

namespace OAI

/-! Exceptional comparison-node costs are bounded by the actual global curvature charge. -/

namespace EditApproximation

open Finset

noncomputable def comparisonActiveScale {α : Type*} (source target : List α) :
    ComparisonState source.length target.length → ℝ := by
  classical
  exact fun state => match state with
    | none => 0
    | some (parent, q) => if comparisonStopped source target parent q then 0 else
        (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q) : ℕ)

theorem comparisonActiveCost_scale {α : Type*} (source target : List α)
    (state : ComparisonState source.length target.length) :
    comparisonActiveScale source target state ≤ comparisonActiveCost source target state ∧
      comparisonActiveCost source target state ≤ 2 * comparisonActiveScale source target state := by
  classical
  cases state with
  | none => simp only [comparisonActiveScale, comparisonActiveCost, mul_zero, le_refl, and_self]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · simp only [comparisonActiveScale, comparisonActiveCost, ite_eq_left hstop, mul_zero, le_refl, and_self]
    · have hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q := by
        unfold comparisonStopped at hstop
        omega
      have hb := cost_dyadicScale _ _ hc le_rfl
      simp only [comparisonActiveScale, comparisonActiveCost, ite_eq_right hstop]
      exact ⟨by exact_mod_cast hb.2.1, by exact_mod_cast hb.2.2.le⟩

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

noncomputable def stageComparisonBadCost (ratio : ℝ) : ℝ := by
  classical
  exact ∑ v : (Σ d : Fin J, TreeLayer M d.val) with
    comparisonActiveScale source target (frontier v.1.val v.2) <
      ratio * (stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).1 ∨
    comparisonActiveScale source target (frontier v.1.val v.2) <
      ratio * (stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).2,
    comparisonActiveCost source target (frontier v.1.val v.2)

include hsize hF hA hseed hT in
 theorem stageComparisonBadCost_bound (ratio : ℝ) (hratio : 0 ≤ ratio)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hcapacity : source.length ≤ M ^ J)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    stageComparisonBadCost source target hM U N P F A hP T rootQ ratio ≤
      10000 * ratio * F * (1 + (J : ℝ) / P + (J : ℝ) / T) *
        comparisonStateCost source target (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) := by
  classical
  let ι := Σ d : Fin J, TreeLayer M d.val
  let cost : ι → ℝ := fun v => comparisonActiveCost source target (frontier v.1.val v.2)
  let scale : ι → ℝ := fun v => comparisonActiveScale source target (frontier v.1.val v.2)
  let K : ι → ℝ := fun v => (stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).1
  let G : ι → ℝ := fun v => (stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).2
  have h := bad_node_cost_from_curvature (univ : Finset ι) cost scale K G ratio _ hratio
    (fun v _ => (comparisonActiveCost_scale source target _).2)
    (fun v _ => (stageComparisonCharges_local source target hM U N P F A hsize hP hF hA hseed
      T hT rootQ hscale v.1 v.2).1)
    (fun v _ => (stageComparisonCharges_local source target hM U N P F A hsize hP hF hA hseed
      T hT rootQ hscale v.1 v.2).2.1)
    (stageComparisonCharges_total source target hM U N P F A hsize hP hF hA hseed
      T hT rootQ hscale hcapacity hsmall)
  change stageComparisonBadCost source target hM U N P F A hP T rootQ ratio ≤ _ at h
  convert h using 1
  ring

end Stage

end EditApproximation

end OAI
