import OAI.GroupTheory.PolycyclicRecognition.Algebra.InducedTranslation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InductionCochains

namespace OAI

/-! # Frobenius reciprocity and the chain-level quotient translation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal]

theorem inducedSemilinearMap_frobenius (t : G) (A B : Rep k N) (C : Rep k G)
    (b : A ⟶ Rep.res (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom B)
    (f : Rep.ind N.subtype B ⟶ C) (a : A) :
    (Rep.indResHomEquiv N.subtype A C (inducedSemilinearMap k N t A B b ≫ f)).hom a =
      C.ρ t ((Rep.indResHomEquiv N.subtype B C f).hom (b.hom a)) := by
  change f.hom ((inducedSemilinearMap k N t A B b).hom (IndV.mk N.subtype A.ρ 1 a)) =
    C.ρ t (f.hom (IndV.mk N.subtype B.ρ 1 (b.hom a)))
  rw [inducedSemilinearMap_mk, mul_one]
  have h := Rep.hom_comm_apply f t (IndV.mk N.subtype B.ρ 1 (b.hom a))
  simpa only [Rep.ind, Representation.ind_mk, one_mul] using h

theorem inducedTranslation_frobenius (t : G)
    (P : ProjectiveResolution (Rep.trivial k N k)) (C : Rep k G) (i : ℕ)
    (f : Rep.ind N.subtype (P.complex.X i) ⟶ C) (a : P.complex.X i) :
    (Rep.indResHomEquiv N.subtype (P.complex.X i) C
      ((inducedTranslation k N t P).f i ≫ f)).hom a =
        C.ρ t ((Rep.indResHomEquiv N.subtype (P.complex.X i) C f).hom
          (((conjugationResolutionLift k N t P).f i).hom a)) :=
  inducedSemilinearMap_frobenius k N t _ _ C _ f a

end PolycyclicRecognition

end

end OAI
