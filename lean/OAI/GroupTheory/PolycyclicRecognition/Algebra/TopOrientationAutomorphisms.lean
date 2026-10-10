import OAI.GroupTheory.PolycyclicRecognition.Algebra.RankOneCharacter
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

namespace OAI

/-! # The top orientation character is preserved by automorphisms -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem topOrientation_character_aut (R : Rep ℤ G) (eR : R.V ≃ₗ[ℤ] ℤ) (d : ℕ)
    (x : groupHomology R d) (hx : x ≠ 0)
    (hdetect : ∀ A : Rep ℤ G, Nonempty (A.V ≃ₗ[ℤ] ℤ) →
      (∃ y : groupHomology A d, y ≠ 0) → Nonempty (R ≅ A))
    (e : G ≃* G) :
    (rankOneCharacter R eR).comp e.toMonoidHom = rankOneCharacter R eR := by
  let A := Rep.res e.toMonoidHom R
  let E : groupHomology A d ≅ groupHomology R d :=
    groupHomology.mapIso (A := A) (B := R) e (LinearEquiv.refl ℤ R.V)
      (by intro g; rfl) d
  have hi : Function.Injective E.inv := (ModuleCat.mono_iff_injective _).mp inferInstance
  have hy : E.inv x ≠ 0 := fun h => hx (hi (h.trans (map_zero E.inv.hom).symm))
  obtain ⟨i⟩ := hdetect A ⟨eR⟩ ⟨E.inv x, hy⟩
  have h := rankOneCharacter_eq_of_iso R A eR eR i
  exact h.symm

end PolycyclicRecognition

end

end OAI
