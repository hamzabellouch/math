import OAI.GroupTheory.PolycyclicRecognition.Algebra.InductionSemilinear
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

namespace OAI

/-! # The chain-level translation associated to a lift of a quotient generator -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits Representation
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal]

theorem inductionMap_comp_semilinear (t : G) {A B C : Rep k N} (u : A ⟶ B)
    (b : B ⟶ Rep.res (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom C) :
    Rep.indMap N.subtype u ≫ inducedSemilinearMap k N t B C b =
      inducedSemilinearMap k N t A C (u ≫ b) := by
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change (inducedSemilinearMap k N t B C b).hom
      ((Rep.indMap N.subtype u).hom (IndV.mk N.subtype A.ρ g a)) =
    (inducedSemilinearMap k N t A C (u ≫ b)).hom (IndV.mk N.subtype A.ρ g a)
  rw [normalInductionMap_mk, inducedSemilinearMap_mk, inducedSemilinearMap_mk]
  rfl

theorem semilinear_comp_inductionMap (t : G) {A B C : Rep k N}
    (b : A ⟶ Rep.res (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom B) (u : B ⟶ C) :
    inducedSemilinearMap k N t A B b ≫ Rep.indMap N.subtype u =
      inducedSemilinearMap k N t A C
        (b ≫ Rep.resMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom u) := by
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change (Rep.indMap N.subtype u).hom
      ((inducedSemilinearMap k N t A B b).hom (IndV.mk N.subtype A.ρ g a)) =
    (inducedSemilinearMap k N t A C
      (b ≫ Rep.resMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom u)).hom
        (IndV.mk N.subtype A.ρ g a)
  rw [inducedSemilinearMap_mk, normalInductionMap_mk, inducedSemilinearMap_mk]
  rfl

def conjugatedResolution (t : G) (P : ProjectiveResolution (Rep.trivial k N k)) :
    ProjectiveResolution (Rep.trivial k N k) := by
  let e := MulAut.conjNormal (H := N) t⁻¹
  let F : Rep k N ⥤ Rep k N := Rep.resFunctor e.toMonoidHom
  let : F.IsEquivalence := (restrictionEquivalence k e).isEquivalence_functor
  exact F.mapProjectiveResolution P

def conjugationResolutionLift (t : G) (P : ProjectiveResolution (Rep.trivial k N k)) :
    P.complex ⟶ (conjugatedResolution k N t P).complex :=
  ProjectiveResolution.lift (𝟙 _) P (conjugatedResolution k N t P)

def inducedTranslation (t : G) (P : ProjectiveResolution (Rep.trivial k N k)) :
    (normalInducedResolution k N P).complex ⟶ (normalInducedResolution k N P).complex where
  f i := inducedSemilinearMap k N t (P.complex.X i) (P.complex.X i)
    ((conjugationResolutionLift k N t P).f i)
  comm' i j _ := by
    change inducedSemilinearMap k N t _ _ ((conjugationResolutionLift k N t P).f i) ≫
        Rep.indMap N.subtype (P.complex.d i j) =
      Rep.indMap N.subtype (P.complex.d i j) ≫
        inducedSemilinearMap k N t _ _ ((conjugationResolutionLift k N t P).f j)
    erw [inductionMap_comp_semilinear, semilinear_comp_inductionMap]
    congr 1
    exact (conjugationResolutionLift k N t P).comm i j

end PolycyclicRecognition

end

end OAI
