import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map

namespace OAI

/-! # A density of a subtype law vanishes outside the subtype -/

open Set Filter MeasureTheory
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem subtype_density_zero_off {S : Set X} (hS : MeasurableSet S)
    (m : Measure X) (ν : Measure S) (ρ : X → ℝ) (hρ : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x)
    (hν : ν.map Subtype.val = m.withDensity (fun x => ENNReal.ofReal (ρ x))) :
    ∀ᵐ x ∂m, x ∉ S → ρ x = 0 := by
  have hs : ∀ᵐ x ∂m.withDensity (fun x => ENNReal.ofReal (ρ x)), x ∈ S := by
    rw [← hν]
    apply (ae_map_iff measurable_subtype_coe.aemeasurable hS).mpr
    exact Eventually.of_forall fun x => x.property
  have hh := (ae_withDensity_iff hρ.ennreal_ofReal).mp hs
  filter_upwards [hh] with x hx hxs
  have hz : ENNReal.ofReal (ρ x) = 0 := by
    by_contra hn
    exact hxs (hx hn)
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hz) (hρ0 x)

end RegularPointCoordinates

end OAI
