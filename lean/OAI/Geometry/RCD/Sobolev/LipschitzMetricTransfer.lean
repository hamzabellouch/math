import OAI.Analysis.RCDHeat.Foundations
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-! # Transferring Lipschitz functions across approximate metric coordinates

The infimum extension has the exact target Lipschitz constant. An additive
metric error only changes its values on the coordinate image by that error.
This supplies continuous functions on a common Euclidean domain for local
harmonic compactness.
-/

open Set
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [PseudoMetricSpace Y]

theorem exists_lipschitz_metric_transfer {s : Set X} (hs : s.Nonempty)
    (u : X → ℝ) (v : X → Y) (L : ℝ≥0) {A δ : ℝ} (hδ : 0 ≤ δ)
    (hLower : ∀ x ∈ s, -A ≤ u x)
    (hApprox : ∀ x ∈ s, ∀ z ∈ s, |u x-u z| ≤ L*dist (v x) (v z)+δ) :
    ∃ g : Y → ℝ, LipschitzWith L g ∧ ∀ x ∈ s, |g (v x)-u x| ≤ δ := by
  let : Nonempty s := hs.to_subtype
  let g : Y → ℝ := fun y => ⨅ x : s, u x+L*dist y (v x)
  have hB (y : Y) : BddBelow (range fun x : s => u x+L*dist y (v x)) := by
    refine ⟨-A,?_⟩
    rintro z ⟨x,rfl⟩
    exact (hLower x x.property).trans (le_add_of_nonneg_right (by positivity))
  have hUpper (y : Y) (x : s) : g y ≤ u x+L*dist y (v x) := ciInf_le (hB y) x
  refine ⟨g,LipschitzWith.of_le_add_mul L ?_,?_⟩
  · intro y z
    rw [← sub_le_iff_le_add]
    apply le_ciInf
    intro x
    have hh := hUpper y x
    have ht := mul_le_mul_of_nonneg_left (dist_triangle y z (v x)) L.coe_nonneg
    linarith
  · intro x hx
    have hu : g (v x) ≤ u x := by
      simpa only [dist_self,mul_zero,add_zero] using hUpper (v x) ⟨x,hx⟩
    have hl : u x-δ ≤ g (v x) := by
      apply le_ciInf
      intro z
      have hh := (le_abs_self (u x-u z)).trans (hApprox x hx z z.property)
      linarith
    exact abs_le.mpr ⟨by linarith,by linarith⟩

end RegularPointCoordinates

end

end OAI
