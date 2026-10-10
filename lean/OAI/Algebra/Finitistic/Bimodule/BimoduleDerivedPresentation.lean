import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalPresentation
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleDerivedTensor
import OAI.Algebra.Finitistic.Bimodule.BoundedBimoduleDerived

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace LittleFinitistic.BimoduleTotalPresentation

section
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (BimoduleTotal.right k B P) (p i))]

/-- The coefficient presentations have exactly the same right module structure. -/
instance ordinaryProjective : ∀ i, Module.Projective Bᵐᵒᵖ
    (ComplexTensor.rightTerm k B (BimoduleComplexTensor.rightComplex k B B P) (p i)) :=
  fun i => inferInstanceAs (Module.Projective Bᵐᵒᵖ
    (ComplexTensor.rightTerm k B (BimoduleTotal.right k B P) (p i)))

/-- The already proved chain comparison descends through the actual localization. -/
def derivedIso : BimoduleComplexTensor.derivedTotal k B B P p hp ≅
    BimoduleTotal.derived k B P p hp :=
  (Localization.fullyFaithfulWhiskeringLeft (DerivedCategory.Q (C := ModuleCat.{u} B))
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ))
    (DerivedCategory (ModuleCat.{u} B))).preimageIso
      (BimoduleComplexTensor.derivedTotalComparison k B B P p hp ≪≫
        Functor.isoWhiskerRight (totalFunctorIso k B P p hp) DerivedCategory.Q ≪≫
          (BimoduleTotal.derivedComparison k B P p hp).symm)

/-- Exact compatibility with the two localization comparison maps. -/
theorem derivedIso_comparison :
    whiskerLeft DerivedCategory.Q (derivedIso k B P p hp).hom ≫
      (BimoduleTotal.derivedComparison k B P p hp).hom =
    (BimoduleComplexTensor.derivedTotalComparison k B B P p hp).hom ≫
      whiskerRight (totalFunctorIso k B P p hp).hom DerivedCategory.Q := by
  have h := (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q (C := ModuleCat.{u} B))
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ))
    (DerivedCategory (ModuleCat.{u} B))).map_preimage
      ((BimoduleComplexTensor.derivedTotalComparison k B B P p hp ≪≫
        Functor.isoWhiskerRight (totalFunctorIso k B P p hp) DerivedCategory.Q ≪≫
          (BimoduleTotal.derivedComparison k B P p hp).symm).hom)
  change whiskerLeft DerivedCategory.Q (derivedIso k B P p hp).hom = _ at h
  rw [h]
  simp
end

open CategoryTheory ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B)

/-- Transport only the finite indexing type; every degree and both signed maps are unchanged. -/
def enumerationIso {l l' : ℕ} (p : Fin l → ℤ) (q : Fin l' → ℤ)
    (hp : StrictMono p) (hq : StrictMono q) (hl : l = l')
    (he : ∀ i, p i = q (Fin.cast hl i)) :
    BimoduleTotal.functor k B P p hp ≅ BimoduleTotal.functor k B P q hq := by
  subst l'
  have h : p = q := by funext i; exact he i
  subst q
  exact Iso.refl _

/-- Exact comparison of the ordinary resolution's finite list with the native interval. -/
def nonpositiveTotalFunctorIso (length : ℕ) :
    BimoduleComplexTensor.totalFunctor k B B P
      (OrdinarySimulation.TensorResolution.finiteDegrees length)
      (OrdinarySimulation.TensorResolution.finiteDegrees_strictMono length) ≅
    BimoduleTotal.functor k B P (BimoduleTotal.intervalDegrees (-(length : ℤ)) 0)
      (BimoduleTotal.intervalDegrees_strictMono (-(length : ℤ)) 0) :=
  totalFunctorIso k B P _ _ ≪≫ enumerationIso k B P _ _ _ _ (by omega) (by intro i; rfl)

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable (data : BimoduleTotal.BoundedProjective k B P)

/-- The comparison for exactly the same bounded Q and its chosen interval. -/
def boundedDerivedIso :
    (letI : ∀ i, Module.Projective Bᵐᵒᵖ
        (ComplexTensor.rightTerm k B (BimoduleTotal.right k B P) (data.degrees i)) :=
      fun i => data.projective (data.degrees i)
     BimoduleComplexTensor.derivedTotal k B B P data.degrees
       (BimoduleTotal.intervalDegrees_strictMono data.lower data.upper)) ≅ data.derived := by
  letI : ∀ i, Module.Projective Bᵐᵒᵖ
      (ComplexTensor.rightTerm k B (BimoduleTotal.right k B P) (data.degrees i)) :=
    fun i => data.projective (data.degrees i)
  exact derivedIso k B P data.degrees _
end LittleFinitistic.BimoduleTotalPresentation

end

end OAI
