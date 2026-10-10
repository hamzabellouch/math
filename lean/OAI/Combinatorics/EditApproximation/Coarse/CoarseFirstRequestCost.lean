import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseWidthCost
import OAI.Combinatorics.EditApproximation.Probability.FreshCoordinateCost
import OAI.Combinatorics.EditApproximation.Coarse.CoarseGlobalSeed

namespace OAI

/-! First-request work for a complete independent coarse source. The
query is adaptive; each entry is charged only on its first appearance.
No conditioning on seed correctness occurs in this estimate. -/

namespace EditApproximation

open MeasureTheory

section FirstRequest

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
  (N B : ℕ) [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : ι → ℕ) (x y : ι → List α) (query : FiniteQuery ι)

noncomputable def coarseFirstRequestWork (draw : CoarseFullSeedDraws B depth x y) : ℝ :=
  ∑ i, selectionIndicator (i ∈ query.keys
    (fun j => (coarseFullSeedTable N B depth x y draw j : ℚ))) *
      (coarseInitialArrayWork B (depth i) (initialThresholdQ N) (initialLambda N) (x i) (y i) (draw i) : ℝ)

theorem coarseFirstRequestWork_expected_le
    (hB : B = (integerParameters N).B) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hdepth : ∀ i, depth i = computedCoarseDepth N (coarseEntryWidth (x i) (y i)))
    (hsize : ∀ i, coarseEntryWidth (x i) (y i) ≤ N)
    (hinverse : coarseInverseAllowanceFactor B (initialThresholdQ N) (initialLambda N) ≤
      (inputHeight N : ℝ) ^ 8)
    (budget : ℝ)
    (hbudget : ∀ draw : CoarseFullSeedDraws B depth x y,
      ((query.cost (fun i => (coarseFullSeedTable N B depth x y draw i : ℚ))
        (fun i => (x i).length) : ℕ) : ℝ) ≤ budget) :
    (∫ draw, coarseFirstRequestWork N B depth x y query draw
      ∂coarseFullSeedMeasure B depth x y) ≤ budget * computedCoarseWidthOverhead N := by
  let μ := fun i => coarseInitialMeasure B (depth i) (coarseEntryWidth (x i) (y i))
  let answer := fun i draw =>
    (coarseInitialValue B (depth i) (initialThresholdQ N) (initialLambda N) N (x i) (y i) draw : ℚ)
  let cost := fun i draw =>
    (coarseInitialArrayWork B (depth i) (initialThresholdQ N) (initialLambda N) (x i) (y i) draw : ℝ)
  have hcost (i) : (∫ value, cost i value ∂μ i) ≤
      ((x i).length : ℝ) * computedCoarseWidthOverhead N :=
    computed_coarse_expected_source_width N B hB hN hell hinverse (x i) (y i)
      (depth i) (hdepth i) (hsize i)
  have hselected (draw : CoarseFullSeedDraws B depth x y) :
      (∑ i, selectionIndicator (i ∈ query.keys (fun j => answer j (draw j))) *
        ((x i).length : ℝ)) ≤ budget := by
    have hs := sum_selected_nat_weights_le (query.keys (fun j => answer j (draw j)))
      (fun i => (x i).length)
    have hb := hbudget draw
    rw [FiniteQuery.cost_eq_sum] at hb
    exact hs.trans hb
  have h := finiteQuery_fresh_expected_cost_le μ query answer cost
    (fun i => ((x i).length : ℝ)) (computedCoarseWidthOverhead N) budget
    (Nat.cast_nonneg _) hcost hselected
  exact h

end FirstRequest

end EditApproximation

end OAI
