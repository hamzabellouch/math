import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntegerInducedTranslation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FinsuppCohomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BilateralCochainShift

namespace OAI

/-! # Integer coordinates on the induced resolution and its cohomology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)
  (P : ProjectiveResolution (Rep.trivial ℤ q.ker ℤ))
  (hP : ∀ i, Module.Finite ℤ[q.ker] (P.complex.X i).ρ.asModule)

def integerInducedCochainsIso :
    (normalInducedResolution ℤ q.ker P).complex.linearYonedaObj ℤ (Rep.leftRegular ℤ G) ≅
      ((moduleFinsuppFunctor ℤ ℤ).mapHomologicalComplex _).obj
        (P.complex.linearYonedaObj ℤ (Rep.leftRegular ℤ q.ker)) :=
  normalInductionCochainsIso q.ker P _ ≪≫
    repCochainPostcompIso ℤ P.complex (integerRestrictedRegularIso ℤ q t ht) ≪≫
      (finsuppCochainsIso ℤ q.ker ℤ P hP (Rep.leftRegular ℤ q.ker)).symm

theorem integerInducedCochainsIso_apply (i : ℕ)
    (f : Rep.ind q.ker.subtype (P.complex.X i) ⟶ Rep.leftRegular ℤ G) :
    ((integerInducedCochainsIso q t ht P hP).hom.f i).hom f =
      letI := hP i
      integerInducedHomEquiv ℤ q t ht (P.complex.X i) f := rfl

theorem integerInducedCochainsIso_translation :
    repCochainPrecomp ℤ (inducedTranslation ℤ q.ker t P) (Rep.leftRegular ℤ G) ≫
        (integerInducedCochainsIso q t ht P hP).hom =
      (integerInducedCochainsIso q t ht P hP).hom ≫
        bilateralCochainTwist ℤ (P.complex.linearYonedaObj ℤ (Rep.leftRegular ℤ q.ker))
          (conjugationCochainEquiv ℤ q.ker t P).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  let := hP i
  change integerInducedHomEquiv ℤ q t ht (P.complex.X i)
      ((inducedTranslation ℤ q.ker t P).f i ≫ f) =
    Finsupp.mapRange.linearMap ((conjugationCochainEquiv ℤ q.ker t P).hom.f i).hom
      (bilateralTranslation ℤ (P.complex.X i ⟶ Rep.leftRegular ℤ q.ker)
        (Multiplicative.ofAdd 1) (integerInducedHomEquiv ℤ q t ht (P.complex.X i) f))
  exact integerInducedHomEquiv_translation ℤ q t ht P i f

def integerInducedCohomologyIso (i : ℕ) :
    ((normalInducedResolution ℤ q.ker P).complex.linearYonedaObj ℤ
      (Rep.leftRegular ℤ G)).homology i ≅
        (moduleFinsuppFunctor ℤ ℤ).obj
          ((P.complex.linearYonedaObj ℤ (Rep.leftRegular ℤ q.ker)).homology i) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (integerInducedCochainsIso q t ht P hP) ≪≫
    bilateralCohomologyIso ℤ _ i

theorem integerInducedCohomologyIso_translation (i : ℕ) :
    HomologicalComplex.homologyMap
        (repCochainPrecomp ℤ (inducedTranslation ℤ q.ker t P) (Rep.leftRegular ℤ G)) i ≫
        (integerInducedCohomologyIso q t ht P hP i).hom =
      (integerInducedCohomologyIso q t ht P hP i).hom ≫
        (bilateralFunctorTranslation ℤ (Multiplicative.ofAdd 1)).app
          ((P.complex.linearYonedaObj ℤ (Rep.leftRegular ℤ q.ker)).homology i) ≫
            (moduleFinsuppFunctor ℤ ℤ).map (conjugationCohomologyIso ℤ q.ker t P i).hom := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f i)
    (integerInducedCochainsIso_translation q t ht P hP)
  simp only [HomologicalComplex.homologyMap_comp] at h
  change _ ≫ ((HomologicalComplex.homologyMap _ i) ≫
      (bilateralCohomologyIso ℤ _ i).hom) = _
  rw [← Category.assoc, h, Category.assoc, bilateralCohomologyIso_twist]
  rfl

end PolycyclicRecognition

end

end OAI
