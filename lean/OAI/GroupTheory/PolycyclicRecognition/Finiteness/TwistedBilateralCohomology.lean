import OAI.GroupTheory.PolycyclicRecognition.Algebra.TwistedBilateralRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InfiniteCyclicDuality

namespace OAI

/-! # Cohomology of the cyclic quotient with its twisted direct-sum module -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] Finsupp.module
attribute [local instance 2200] Submodule.module

variable (M : Type) [AddCommGroup M] [Module ℤ M]

abbrev bilateralGenerator : Multiplicative ℤ := Multiplicative.ofAdd 1

def bilateralHomAugmentation (e : M ≃ₗ[ℤ] M) :
    ModuleCat.of ℤ (Rep.leftRegular ℤ (Multiplicative ℤ) ⟶ twistedBilateralRep ℤ M e) ⟶
      ModuleCat.of ℤ M :=
  ModuleCat.ofHom ((twistedBilateralSum ℤ M e).comp
    (Rep.leftRegularHomEquiv (twistedBilateralRep ℤ M e)).toLinearMap)

theorem bilateralHomAugmentation_surjective (e : M ≃ₗ[ℤ] M) :
    Function.Surjective (bilateralHomAugmentation M e).hom :=
  (twistedBilateralSum_surjective ℤ M e).comp
    (Rep.leftRegularHomEquiv (twistedBilateralRep ℤ M e)).surjective

theorem bilateralHomAugmentation_exact (e : M ≃ₗ[ℤ] M) :
    Function.Exact (Linear.leftComp ℤ (twistedBilateralRep ℤ M e)
      (cyclicDifference (Multiplicative ℤ) bilateralGenerator))
      (bilateralHomAugmentation M e).hom := by
  let E : (Rep.leftRegular ℤ (Multiplicative ℤ) ⟶ twistedBilateralRep ℤ M e) ≃ₗ[ℤ]
      (ℤ →₀ M) := Rep.leftRegularHomEquiv (twistedBilateralRep ℤ M e)
  have hdiff (y : Rep.leftRegular ℤ (Multiplicative ℤ) ⟶ twistedBilateralRep ℤ M e) :
      E (cyclicDifference (Multiplicative ℤ) bilateralGenerator ≫ y) =
        twistedBilateralDifference ℤ M e (E y) := by
    have h := leftRegularHomEquiv_precomp_difference (Multiplicative ℤ) bilateralGenerator
      (twistedBilateralRep ℤ M e) y
    change E (cyclicDifference (Multiplicative ℤ) bilateralGenerator ≫ y) =
      twistedBilateralRepresentation ℤ M e bilateralGenerator (E y) - E y at h
    change E (cyclicDifference (Multiplicative ℤ) bilateralGenerator ≫ y) =
      twistedBilateralShift ℤ M e (E y) - E y
    simpa only [twistedBilateralRepresentation_generator] using h
  intro x
  change twistedBilateralSum ℤ M e (E x) = 0 ↔ _
  rw [← LinearMap.mem_ker, twistedBilateralSum_ker_eq_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨E.symm y, ?_⟩
    apply E.injective
    change E (cyclicDifference (Multiplicative ℤ) bilateralGenerator ≫ E.symm y) = E x
    rw [hdiff, LinearEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨y, rfl⟩
    refine ⟨E y, ?_⟩
    exact (hdiff y).symm

theorem twistedBilateral_cohomology_zero (e : M ≃ₗ[ℤ] M) :
    IsZero (groupCohomology (twistedBilateralRep ℤ M e) 0) := by
  refine IsZero.of_iso ?_ (groupCohomology.H0Iso (twistedBilateralRep ℤ M e))
  apply ModuleCat.isZero_of_iff_subsingleton.mpr
  have hz (x : (twistedBilateralRepresentation ℤ M e).invariants) : x = 0 := by
    apply Subtype.ext
    apply twistedBilateralDifference_injective ℤ M e
    change twistedBilateralDifference ℤ M e (x : ℤ →₀ M) = twistedBilateralDifference ℤ M e 0
    rw [map_zero]
    change twistedBilateralShift ℤ M e x - x = 0
    rw [← twistedBilateralRepresentation_generator, x.property bilateralGenerator, sub_self]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

def twistedBilateral_cohomology_one_iso (e : M ≃ₗ[ℤ] M) :
    groupCohomology (twistedBilateralRep ℤ M e) 1 ≅ ModuleCat.of ℤ M := by
  let A := twistedBilateralRep ℤ M e
  let K := infiniteCyclicCochains (Multiplicative ℤ) bilateralGenerator A
  let S := K.sc' 0 1 2
  have hf : S.f = ModuleCat.ofHom (Linear.leftComp ℤ A
      (cyclicDifference (Multiplicative ℤ) bilateralGenerator)) := by
    change ModuleCat.ofHom (Linear.leftComp ℤ A
      ((infiniteCyclicComplex (Multiplicative ℤ) bilateralGenerator).d 1 0)) = _
    rw [show (infiniteCyclicComplex (Multiplicative ℤ) bilateralGenerator).d 1 0 =
      cyclicDifference (Multiplicative ℤ) bilateralGenerator from
        ChainComplex.of_d (infiniteCyclicObjects (Multiplicative ℤ))
          (infiniteCyclicDifferentials (Multiplicative ℤ) bilateralGenerator) 0]
    rfl
  have hz : S.g = 0 := infiniteCyclicCochains_d_one_two _ _ A
  have he : Function.Exact S.f.hom (bilateralHomAugmentation M e).hom := by
    rw [hf]
    exact bilateralHomAugmentation_exact M e
  let c := CokernelCofork.ofπ (f := S.f) (bilateralHomAugmentation M e)
    (by ext x; exact he.apply_apply_eq_zero x)
  let hc : IsColimit c := ModuleCat.isColimitCokernelCofork S.f
    (bilateralHomAugmentation M e) he (bilateralHomAugmentation_surjective M e)
  let data := ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork S hz c hc
  exact groupCohomologyIso A 1 (infiniteCyclicResolution (Multiplicative ℤ)
      bilateralGenerator multiplicativeInt_generator) ≪≫
    K.homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫ data.homologyIso

theorem twistedBilateral_cohomology_above_one (e : M ≃ₗ[ℤ] M)
    (i : ℕ) (hi : 1 < i) : IsZero (groupCohomology (twistedBilateralRep ℤ M e) i) :=
  infiniteCyclic_cohomology_above_one (Multiplicative ℤ) bilateralGenerator
    multiplicativeInt_generator _ i hi

end PolycyclicRecognition

end

end OAI
