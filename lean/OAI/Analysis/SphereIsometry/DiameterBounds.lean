import Mathlib.Topology.MetricSpace.Bounded

namespace OAI

/-! # Pairwise diameter bounds

The predicate records the distance between every pair of points. It does not
use the real-valued diameter of a possibly unbounded set.
-/

namespace Tingley

variable {E : Type*} [PseudoMetricSpace E]

/-- Every pair of points in a set is at distance at most the given radius. -/
def DiameterLE (A : Set E) (δ : ℝ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ δ

namespace DiameterLE

variable {A B : Set E} {δ ε : ℝ}

theorem mono_set (h : DiameterLE B δ) (hAB : A ⊆ B) : DiameterLE A δ :=
  fun x hx y hy => h x (hAB hx) y (hAB hy)

theorem mono_radius (h : DiameterLE A δ) (hδε : δ ≤ ε) : DiameterLE A ε :=
  fun x hx y hy => (h x hx y hy).trans hδε

theorem closure (h : DiameterLE A δ) : DiameterLE (closure A) δ := by
  intro x hx y hy
  exact isClosed_Iic.closure_subset
    (map_mem_closure₂ continuous_dist hx hy (fun _ ha _ hb => h _ ha _ hb))

end DiameterLE

end Tingley

end OAI
