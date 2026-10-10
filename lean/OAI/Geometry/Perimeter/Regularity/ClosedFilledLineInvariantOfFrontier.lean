import OAI.Geometry.Perimeter.Regularity.ExistsMinimizingDensityLimit

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack

theorem closed_filled_line_invariant_of_frontier {n : ℕ} {F : Set (Euc n)}
    (hF : IsClosed F) (c : Euc n)
    (hline : ∀ (t : ℝ) (x : Euc n), x ∈ frontier F → x+t • c ∈ frontier F) :
    ∀ (t : ℝ) (x : Euc n), x ∈ F → x+t • c ∈ F := by
  intro t x hx
  by_cases hxfr : x ∈ frontier F
  · exact hF.closure_eq ▸ frontier_subset_closure (hline t x hxfr)
  have hxint : x ∈ interior F := by
    by_contra hxi
    apply hxfr
    rw [frontier, hF.closure_eq]
    exact ⟨hx, hxi⟩
  let L : Set (Euc n) := Set.range (fun s : ℝ ↦ x+s • c)
  have hLfr : Disjoint L (frontier F) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨s, rfl⟩ hy
    apply hxfr
    have hh := hline (-s) (x+s • c) hy
    convert hh using 1
    module
  have hLsub : L ⊆ interior F ∪ Fᶜ := by
    intro y hy
    by_cases hyF : y ∈ F
    · apply Or.inl
      by_contra hyi
      exact (Set.disjoint_left.mp hLfr hy) (by rw [frontier, hF.closure_eq]; exact ⟨hyF, hyi⟩)
    · exact Or.inr hyF
  have hLc : IsPreconnected L := by
    exact isPreconnected_range (by fun_prop : Continuous (fun s : ℝ ↦ x+s • c))
  have hLInt : L ⊆ interior F := hLc.subset_left_of_subset_union isOpen_interior hF.isOpen_compl
    (Set.disjoint_left.mpr fun y hy hyc ↦ hyc (interior_subset hy)) hLsub
    ⟨x, ⟨0, by simp⟩, hxint⟩
  exact interior_subset (hLInt ⟨t, rfl⟩)

theorem minimizing_cone_tangent_filled_line_invariant {n : ℕ} (hn : 1 < n)
    {E F : Set (Euc n)} (hE : IsLocallyPerimeterMinimizing E) (hcone : IsCone E)
    (hF : IsLocallyPerimeterMinimizing F) (hFc : IsClosed F)
    (hFfront : frontier F = perimeterSupport F) (c : Euc n)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (htr : Tendsto r atTop (𝓝 0))
    (hconv : ∀ (x : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (blownUpSet E c (r i)) F ∩ Metric.closedBall x R))
        atTop (𝓝 0)) :
    ∀ (t : ℝ) (x : Euc n), x ∈ F → x + t • c ∈ F := by
  apply closed_filled_line_invariant_of_frontier hFc c
  intro t x hx
  rw [hFfront] at hx ⊢
  exact minimizing_cone_tangent_support_line_invariant hn hE hcone hF c r hr htr hconv t x hx

end RPISingularHarnack

end

end OAI
