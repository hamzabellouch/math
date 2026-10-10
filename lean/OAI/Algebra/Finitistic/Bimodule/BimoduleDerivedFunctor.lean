import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalUnderlying
import Mathlib.CategoryTheory.Localization.Preadditive

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (p i))]

/-- Every quasi-isomorphism becomes invertible after applying the actual B-valued total. -/
theorem inverts : (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)).IsInvertedBy
    (functor k B P p hp ⋙ DerivedCategory.Q) := by
  intro Z Z' f hf
  let : QuasiIso f := hf
  let := totalMap_quasiIso k B P p hp f
  exact (inferInstance : IsIso (DerivedCategory.Q.map (totalMap k B P p hp f)))

/-- The actual fixed bimodule tensor total descends to the native derived category of B-modules. -/
def derived : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  Localization.lift (functor k B P p hp ⋙ DerivedCategory.Q)
    (inverts k B P p hp) DerivedCategory.Q

/-- This derived endofunctor is computed by the signed tensor total on every input complex. -/
def derivedComparison : DerivedCategory.Q ⋙ derived k B P p hp ≅
    functor k B P p hp ⋙ DerivedCategory.Q :=
  Localization.fac (functor k B P p hp ⋙ DerivedCategory.Q)
    (inverts k B P p hp) DerivedCategory.Q

instance derived_additive : (derived k B P p hp).Additive := by
  rw [Localization.functor_additive_iff DerivedCategory.Qh
    (HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} B)).trW]
  let e : HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ) ⋙
      (DerivedCategory.Qh ⋙ derived k B P p hp) ≅
      functor k B P p hp ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)) _ ≪≫
        derivedComparison k B P p hp
  let := Functor.additive_of_iso e.symm
  exact Functor.additive_of_full_essSurj_comp
    (HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)) _
end LittleFinitistic.BimoduleTotal

end

end OAI
