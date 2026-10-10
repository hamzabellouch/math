import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegerExtensionHomologyBound
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

namespace OAI

/-! # Transporting a homology bound through a group isomorphism -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2

theorem homology_bound_of_equiv {G J : Type} [Group G] [Group J]
    (e : G ≃* J) (d : ℕ)
    (hG : ∀ A : Rep ℤ G, ∀ i, d < i → IsZero (groupHomology A i)) :
    ∀ A : Rep ℤ J, ∀ i, d < i → IsZero (groupHomology A i) := by
  intro A i hi
  let E := groupHomology.mapIso (A := Rep.res e.toMonoidHom A) (B := A)
    e (LinearEquiv.refl ℤ A.V) (by intro g; rfl) i
  exact IsZero.of_iso (hG (Rep.res e.toMonoidHom A) i hi) E.symm

end PolycyclicRecognition

end

end OAI
