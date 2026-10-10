import OAI.GroupTheory.PolycyclicRecognition.Algebra.InducedTranslation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RepCochainMaps

namespace OAI

/-! # The automorphism of kernel cohomology induced by conjugation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable (k : Type) [CommRing k] {H : Type} [Group H]

def restrictionHomEquiv (e : H ≃* H) (A B : Rep k H) :
    (A ⟶ B) ≃ₗ[k] (Rep.res e.toMonoidHom A ⟶ Rep.res e.toMonoidHom B) where
  toFun := Rep.resMap e.toMonoidHom
  invFun := Rep.liftHomOfSurj e.toMonoidHom e.surjective
  left_inv f := by apply Rep.hom_ext; apply IntertwiningMap.ext; rfl
  right_inv f := by apply Rep.hom_ext; apply IntertwiningMap.ext; rfl
  map_add' f g := by apply Rep.hom_ext; apply IntertwiningMap.ext; rfl
  map_smul' r f := by apply Rep.hom_ext; apply IntertwiningMap.ext; rfl

def restrictionCochainsIso (e : H ≃* H) (P : ChainComplex (Rep k H) ℕ) (A : Rep k H) :
    P.linearYonedaObj k A ≅
      ChainComplex.linearYonedaObj (((Rep.resFunctor e.toMonoidHom).mapHomologicalComplex _).obj P) k
        (Rep.res e.toMonoidHom A) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (restrictionHomEquiv k e (P.X i) A).toModuleIso) (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      rfl)

def regularRestrictionIso (e : H ≃* H) :
    Rep.res e.toMonoidHom (Rep.leftRegular k H) ≅ Rep.leftRegular k H :=
  Rep.mkIso (Representation.Equiv.mk (MonoidAlgebra.domCongr k k e.symm).toLinearEquiv
    (fun h => by
      apply MonoidAlgebra.lhom_ext'
      intro a
      apply LinearMap.ext_ring
      simp [map_mul]))

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def conjugationCoefficientCochainsIso (t : G)
    (P : ProjectiveResolution (Rep.trivial k N k)) :
    P.complex.linearYonedaObj k (Rep.leftRegular k N) ≅
      (conjugatedResolution k N t P).complex.linearYonedaObj k (Rep.leftRegular k N) :=
  restrictionCochainsIso k (MulAut.conjNormal (H := N) t⁻¹) P.complex _ ≪≫
    repCochainPostcompIso k _
      (regularRestrictionIso k (MulAut.conjNormal (H := N) t⁻¹))

def conjugationCochainEquiv (t : G) (P : ProjectiveResolution (Rep.trivial k N k)) :
    HomotopyEquiv (P.complex.linearYonedaObj k (Rep.leftRegular k N))
      (P.complex.linearYonedaObj k (Rep.leftRegular k N)) :=
  (HomotopyEquiv.ofIso (conjugationCoefficientCochainsIso k N t P)).trans
    (repCochainHomotopyEquiv k
      (ProjectiveResolution.homotopyEquiv P (conjugatedResolution k N t P)) _)

def conjugationCohomologyIso (t : G) (P : ProjectiveResolution (Rep.trivial k N k)) (i : ℕ) :
    (P.complex.linearYonedaObj k (Rep.leftRegular k N)).homology i ≅
      (P.complex.linearYonedaObj k (Rep.leftRegular k N)).homology i :=
  (conjugationCochainEquiv k N t P).toHomologyIso i

theorem conjugationCochainEquiv_apply (t : G)
    (P : ProjectiveResolution (Rep.trivial k N k)) (i : ℕ)
    (f : P.complex.X i ⟶ Rep.leftRegular k N) (a : P.complex.X i) :
    ((((conjugationCochainEquiv k N t P).hom.f i).hom f).hom a) =
      (MonoidAlgebra.domCongr k k (MulAut.conjNormal (H := N) t⁻¹).symm)
        (f.hom (((conjugationResolutionLift k N t P).f i).hom a)) := rfl

end PolycyclicRecognition

end

end OAI
