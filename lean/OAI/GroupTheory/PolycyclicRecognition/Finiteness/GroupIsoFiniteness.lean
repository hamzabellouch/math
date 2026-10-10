import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteRestriction
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CyclicExtensionFiniteness

namespace OAI

/-! # Finite projective resolutions transported through a group isomorphism -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G J : Type} [Group G] [Group J]

theorem HasFiniteProjectiveResolution.of_equiv
    (hG : HasFiniteProjectiveResolution G) (e : G ≃* J) :
    HasFiniteProjectiveResolution J := by
  obtain ⟨P, d, hP, hd⟩ := hG
  let F : Rep ℤ G ⥤ Rep ℤ J := Rep.resFunctor e.symm.toMonoidHom
  let : F.IsEquivalence := (restrictionEquivalence ℤ e.symm).isEquivalence_functor
  let Q := F.mapProjectiveResolution P
  refine ⟨Q, d, ?_, ?_⟩
  · intro i
    let : Module.Finite ℤ[G] (P.complex.X i).ρ.asModule := hP i
    exact finite_restriction_of_surjective ℤ e.symm.toMonoidHom (P.complex.X i) e.symm.surjective
  · intro i hi
    exact F.map_isZero (hd i hi)

end PolycyclicRecognition

end

end OAI
