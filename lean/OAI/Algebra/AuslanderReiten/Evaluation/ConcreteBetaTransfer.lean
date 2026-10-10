import OAI.Algebra.AuslanderReiten.Resolutions.ConcreteNativeResolution
import OAI.Algebra.AuslanderReiten.Bar.ConcreteBarFreeAugmentation
import OAI.Algebra.AuslanderReiten.Coordinates.TensorNormalizedTop
import OAI.Algebra.AuslanderReiten.Evaluation.TensorTwistEvaluation
import OAI.Algebra.AuslanderReiten.Resolutions.EvaluatedResolutionTerms

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
private theorem precompose_factor {C : Type*} [Category C]
    {P Q R S T : C} {f : P ⟶ Q} {g : Q ⟶ R} {h : R ⟶ S}
    {p : Q ⟶ T} {e : T ⟶ S} {j : P ⟶ T}
    (h₁ : g ≫ h = p ≫ e) (h₂ : f ≫ p = j) :
    (f ≫ g) ≫ h = j ≫ e := by
  rw [Category.assoc, h₁, ← Category.assoc, h₂]

universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (hq : 1+q ≠ 0)

def evaluatedFreeCoordinate :
    (simpleOrdinaryResolution q).complex.X 0 ⟶ ModuleCat.of (A k q) (A k q) :=
  (simpleNativeBarIso q).hom.f 0 ≫ simpleBarFreeCoordinate q hq

theorem evaluatedFreeCoordinate_augmentation :
    evaluatedFreeCoordinate q hq ≫ ModuleCat.ofHom (A.augmentation q) =
      (simpleOrdinaryResolution q).π.f 0 ≫ (evaluatedBaseZeroEquiv q).toModuleIso.hom := by
  apply (cancel_mono (nativeToCanonicalSimple q).hom).mp
  change ((simpleNativeBarIso q).hom.f 0 ≫ simpleBarFreeCoordinate q hq) ≫
    ModuleCat.ofHom (A.augmentation q) ≫ (nativeToCanonicalSimple q).hom = _
  erw [Category.assoc, Category.assoc, simpleBarFreeCoordinate_augmentation]
  exact simpleNativeBarIso_augmentation q

theorem evaluatedFreeCoordinate_augmentation_linear :
    (A.augmentation q).comp (evaluatedFreeCoordinate q hq).hom =
      (evaluatedBaseZeroEquiv q).toLinearMap.comp
        (TwoCone.evaluatedBaseQuotient (k := k) (R := A k q) (bimoduleTwoConeData q)
          (bimodule_term_finite_k q) (A.simpleFiniteModule q) 0) := by
  have h := congrArg ModuleCat.Hom.hom (evaluatedFreeCoordinate_augmentation q hq)
  exact h

def simpleResolutionTermIso (n : ℕ) : (simpleOrdinaryResolution q).complex.X n ≅
    TwoCone.evaluatedRawTerm (k := k) (R := A k q) (bimoduleTwoConeData q) (bimodule_term_finite_k q)
      (A.simpleFiniteModule q) n :=
  TwoCone.evaluatedResolutionTermIso (k := k) (R := A k q) (bimoduleTwoConeData q) (bimodule_term_finite_k q)
    (A.simpleFiniteModule q) (bimodule_exact q) (baseTail_right_projective q)
    (bimodule_term_projective q) n

def freeCoordinateRaw : TwoCone.evaluatedRawTerm (k := k) (R := A k q) (bimoduleTwoConeData q)
    (bimodule_term_finite_k q) (A.simpleFiniteModule q) 0 →ₗ[A k q] A k q :=
  (evaluatedFreeCoordinate q hq).hom.comp (simpleResolutionTermIso q 0).inv.hom

theorem freeCoordinateRaw_augmentation :
    (A.augmentation q).comp (freeCoordinateRaw q hq) =
      (evaluatedBaseZeroEquiv q).toLinearMap.comp
        (TwoCone.evaluatedBaseQuotient (k := k) (R := A k q) (bimoduleTwoConeData q)
          (bimodule_term_finite_k q) (A.simpleFiniteModule q) 0) := by
  have ht := TwoCone.evaluatedResolutionTermIso_augmentation (k := k) (R := A k q)
    (bimoduleTwoConeData q) (bimodule_term_finite_k q) (A.simpleFiniteModule q) (bimodule_exact q)
    (baseTail_right_projective q) (bimodule_term_projective q)
  have h := precompose_factor (evaluatedFreeCoordinate_augmentation q hq) ht
  exact congrArg ModuleCat.Hom.hom h

def betaTransferRaw : (evaluatedBaseModule q 1).carrier →ₗ[A k q] A k q :=
  (freeCoordinateRaw q hq).comp
    (TwoCone.evaluatedBaseInclusion (k := k) (R := A k q) (bimoduleTwoConeData q)
      (bimodule_term_finite_k q) (bimodule_exact q) (A.simpleFiniteModule q) 0)

theorem betaTransferRaw_mem (z : (evaluatedBaseModule q 1).carrier) :
    betaTransferRaw q hq z ∈ A.augmentationIdeal q := by
  rw [← A.augmentation_kernel q hq]
  change A.augmentation q (betaTransferRaw q hq z) = 0
  have he := (TwoCone.evaluatedBaseCover_exact (k := k) (R := A k q) (bimoduleTwoConeData q)
    (bimodule_term_finite_k q) (bimodule_exact q) (baseTail_right_projective q)
    (A.simpleFiniteModule q) 0).2.2
  have hz := (he _).2 ⟨z, rfl⟩
  have h := LinearMap.congr_fun (freeCoordinateRaw_augmentation q hq)
    (TwoCone.evaluatedBaseInclusion (k := k) (R := A k q) (bimoduleTwoConeData q)
      (bimodule_term_finite_k q) (bimodule_exact q) (A.simpleFiniteModule q) 0 z)
  change A.augmentation q (freeCoordinateRaw q hq
    (TwoCone.evaluatedBaseInclusion (k := k) (R := A k q) (bimoduleTwoConeData q)
      (bimodule_term_finite_k q) (bimodule_exact q) (A.simpleFiniteModule q) 0 z)) =
    evaluatedBaseZeroEquiv q (TwoCone.evaluatedBaseQuotient (k := k) (R := A k q)
      (bimoduleTwoConeData q) (bimodule_term_finite_k q) (A.simpleFiniteModule q) 0
      (TwoCone.evaluatedBaseInclusion (k := k) (R := A k q) (bimoduleTwoConeData q)
        (bimodule_term_finite_k q) (bimodule_exact q) (A.simpleFiniteModule q) 0 z)) at h
  rw [hz, map_zero] at h
  exact h

def betaTransfer : (evaluatedBaseModule q 1).carrier →ₗ[A k q] A.augmentationIdeal q :=
  (betaTransferRaw q hq).codRestrict (A.augmentationIdeal q) (betaTransferRaw_mem q hq)

end ArExplicit.T

end

end OAI
