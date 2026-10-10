import OAI.GroupTheory.PolycyclicRecognition.Algebra.InducedTranslation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.InductionTrivial

namespace OAI

/-! # The induced translation lifts right translation on the quotient module -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal]

def inducedTrivialTranslation (t : G) :
    Rep.ind N.subtype (Rep.trivial k N k) ⟶ Rep.ind N.subtype (Rep.trivial k N k) :=
  inducedSemilinearMap k N t _ _ (𝟙 _)

def quotientRightTranslation (t : G) :
    Rep.res (QuotientGroup.mk' N) (Rep.leftRegular k (G ⧸ N)) ⟶
      Rep.res (QuotientGroup.mk' N) (Rep.leftRegular k (G ⧸ N)) :=
  Rep.ofHom ⟨MonoidAlgebra.mapDomainLinearMap k k (fun q => q * QuotientGroup.mk' N t),
    fun g => by
      apply MonoidAlgebra.lhom_ext'
      intro c
      apply LinearMap.ext_ring
      simp [mul_assoc]⟩

@[simp] theorem inducedTrivialTranslation_mk (t g : G) (a : k) :
    (inducedTrivialTranslation k N t).hom
      (IndV.mk N.subtype (Rep.trivial k N k).ρ g a) =
        IndV.mk N.subtype (Rep.trivial k N k).ρ (t⁻¹ * g) a := by
  exact inducedSemilinearMap_mk k N t (Rep.trivial k N k) (Rep.trivial k N k)
    (𝟙 (Rep.trivial k N k)) g a

@[simp] theorem quotientRightTranslation_single (t : G) (c : G ⧸ N) (a : k) :
    (quotientRightTranslation k N t).hom (MonoidAlgebra.single c a) =
      MonoidAlgebra.single (c * QuotientGroup.mk' N t) a := by
  simp [quotientRightTranslation]

theorem inducedTrivialTranslation_quotient (t : G) :
    inducedTrivialTranslation k N t ≫ (inductionTrivialIso k N).hom =
      (inductionTrivialIso k N).hom ≫ quotientRightTranslation k N t := by
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change inductionTrivialLinearEquiv k N
      ((inducedTrivialTranslation k N t).hom (IndV.mk N.subtype (Rep.trivial k N k).ρ g a)) =
    (quotientRightTranslation k N t).hom
      (inductionTrivialLinearEquiv k N (IndV.mk N.subtype (Rep.trivial k N k).ρ g a))
  rw [inducedTrivialTranslation_mk, inductionTrivialLinearEquiv_mk,
    inductionTrivialLinearEquiv_mk, quotientRightTranslation_single]
  congr 1
  rw [map_mul, map_inv, mul_inv_rev, inv_inv]

theorem conjugatedResolution_augmentation_zero (t : G)
    (P : ProjectiveResolution (Rep.trivial k N k)) :
    (conjugatedResolution k N t P).π.f 0 =
      Rep.resMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom (P.π.f 0) := by
  rfl

theorem inducedTranslation_augmentation_zero (t : G)
    (P : ProjectiveResolution (Rep.trivial k N k)) :
    (inducedTranslation k N t P).f 0 ≫ Rep.indMap N.subtype (P.π.f 0) =
      Rep.indMap N.subtype (P.π.f 0) ≫ inducedTrivialTranslation k N t := by
  change inducedSemilinearMap k N t _ _ ((conjugationResolutionLift k N t P).f 0) ≫
      Rep.indMap N.subtype (P.π.f 0) =
    Rep.indMap N.subtype (P.π.f 0) ≫
      inducedSemilinearMap k N t (Rep.trivial k N k) (Rep.trivial k N k)
        (𝟙 (Rep.trivial k N k))
  have h := ProjectiveResolution.lift_commutes_zero (𝟙 (Rep.trivial k N k)) P
    (conjugatedResolution k N t P)
  rw [conjugatedResolution_augmentation_zero] at h
  change (conjugationResolutionLift k N t P).f 0 ≫
      Rep.resMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom (P.π.f 0) =
        P.π.f 0 ≫ 𝟙 (Rep.trivial k N k) at h
  calc
    _ = inducedSemilinearMap k N t (P.complex.X 0) (Rep.trivial k N k)
        ((conjugationResolutionLift k N t P).f 0 ≫
          Rep.resMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom (P.π.f 0)) :=
      semilinear_comp_inductionMap k N t
        (A := P.complex.X 0) (B := P.complex.X 0) (C := Rep.trivial k N k) _ _
    _ = inducedSemilinearMap k N t (P.complex.X 0) (Rep.trivial k N k)
        (P.π.f 0 ≫ 𝟙 (Rep.trivial k N k)) :=
      congrArg (inducedSemilinearMap k N t (P.complex.X 0) (Rep.trivial k N k)) h
    _ = _ := (inductionMap_comp_semilinear k N t
      (A := P.complex.X 0) (B := Rep.trivial k N k) (C := Rep.trivial k N k) (P.π.f 0)
      (𝟙 (Rep.trivial k N k))).symm

end PolycyclicRecognition

end

end OAI
