import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

namespace OAI

/-! # Restriction along a group isomorphism -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G J : Type} [Group G] [Group J]

def restrictionRoundtripIso (e : G ≃* J) (A : Rep k G) :
    Rep.res e.toMonoidHom (Rep.res e.symm.toMonoidHom A) ≅ A :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl k A) fun g => by
    ext a
    simp)

def restrictionEquivalence (e : G ≃* J) : Rep k J ≌ Rep k G where
  functor := Rep.resFunctor e.toMonoidHom
  inverse := Rep.resFunctor e.symm.toMonoidHom
  unitIso := NatIso.ofComponents (fun A => (restrictionRoundtripIso k e.symm A).symm)
    (by intro A B f; ext a; rfl)
  counitIso := NatIso.ofComponents (fun A => restrictionRoundtripIso k e A)
    (by intro A B f; ext a; rfl)
  functor_unitIso_comp A := by ext a; rfl

end PolycyclicRecognition

end

end OAI
