import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.NestedCutCalculus

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section LiftedTranslationOrbits

variable {A G H : Type*} [CommGroup A] [Group G] [Group H]

theorem lifted_translation_orbit_independent (q : A →* G) (t : A →* H)
    (x : G) (y : H)
    (hc : ∀ k, Commute (q k) x → Commute (t k) y)
    (u v : A) (h : q u*x*(q u)⁻¹ = q v*x*(q v)⁻¹) :
    t u*y*(t u)⁻¹ = t v*y*(t v)⁻¹ := by
  have hc₀ : Commute (q (v⁻¹*u)) x := by
    simpa only [map_mul,map_inv] using (commute_ratio_of_conjugation h).symm
  have hc₁ : Commute (t v⁻¹*t u) y := by
    simpa only [map_mul,map_inv] using hc (v⁻¹*u) hc₀
  calc
    t u*y*(t u)⁻¹ = t v*((t v⁻¹*t u)*y)*(t u)⁻¹ := by rw [map_inv]; group
    _ = t v*(y*(t v⁻¹*t u))*(t u)⁻¹ := by rw [hc₁.eq]
    _ = t v*y*(t v)⁻¹ := by rw [map_inv]; group

end LiftedTranslationOrbits

end SimpleAmenable
end
end

end OAI
