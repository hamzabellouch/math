import OAI.Analysis.LipschitzHilbert.Trees.SourceGoodPathSet

namespace OAI

/-! The full weighted good set supplies the precise bad-probability
budget in every actual angular root cell. -/

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable
variable {ι X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem eventually_source_good_path_budget (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ (base : Set X) (tops cell : Finset ι)
      (weight : ι → X → ℝ) (bad : ι → Set X),
      cell ⊆ tops → (∀ t x, 0 ≤ weight t x) →
    ∀ (x : X), x ∈ sourceGoodPathSet base tops weight bad L →
    ∀ α : ℝ, 1 ≤ α → α ≤ 3 →
      (1+(L^C)^(Real.sqrt L)*(L^A+1)^(α-1))*
        (∑ t ∈ cell.filter (fun t => x ∈ bad t), weight t x) ≤ 1/2 := by
  filter_upwards [eventually_source_stop_cost_small C A hC hA,
    eventually_ge_atTop (1:ℝ)] with L hcost hL
  intro base tops cell weight bad hcell hw x hx α hα hα3
  have hsum : (∑ t ∈ cell.filter (fun t => x ∈ bad t), weight t x) ≤ Real.exp (-L) := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ hcell) (fun t _ _ => hw t x)).trans
    rw [← sourceBadPathMass_eq_filter tops weight bad x]
    exact hx.2
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans (hcost α hα hα3)

end LipschitzHilbert

end

end OAI
