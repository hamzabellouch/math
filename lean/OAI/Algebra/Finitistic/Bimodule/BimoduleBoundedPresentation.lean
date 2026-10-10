import OAI.Algebra.Finitistic.Bimodule.BimoduleDerivedPresentation

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace LittleFinitistic.BimoduleTotalPresentation
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B)

instance projectiveDegrees {l : ℕ} (p : Fin l → ℤ)
    [hproj : ∀ n, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (BimoduleTotal.right k B P) n)] :
    ∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (BimoduleTotal.right k B P) (p i)) :=
  fun i => hproj (p i)

variable (data : BimoduleTotal.BoundedProjective k B P) (length : ℕ)
local notation "p" => OrdinarySimulation.TensorResolution.finiteDegrees length
local notation "hp" => OrdinarySimulation.TensorResolution.finiteDegrees_strictMono length

/-- Any native bounded model with these endpoints uses exactly the ordinary finite degree list. -/
def boundedNonpositiveTotalIso (hlo : data.lower = -(length : ℤ)) (hhi : data.upper = 0) :
    BimoduleComplexTensor.totalFunctor k B B P p hp ≅
      BimoduleTotal.functor k B P data.degrees
        (BimoduleTotal.intervalDegrees_strictMono data.lower data.upper) := by
  dsimp only [BimoduleTotal.BoundedProjective.degrees]
  rw [hlo, hhi]
  exact nonpositiveTotalFunctorIso k B P length

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [hproj : ∀ n, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (BimoduleTotal.right k B P) n)]

/-- Generic bridge for a shifted P as well as Q_X. No augmentation or target module
is needed to compare two presentations of the very same bounded complex. -/
def boundedNonpositiveDerivedIso (hlo : data.lower = -(length : ℤ)) (hhi : data.upper = 0) :
    BimoduleComplexTensor.derivedTotal k B B P p hp ≅ data.derived :=
  (Localization.fullyFaithfulWhiskeringLeft (DerivedCategory.Q (C := ModuleCat.{u} B))
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ))
    (DerivedCategory (ModuleCat.{u} B))).preimageIso
      (BimoduleComplexTensor.derivedTotalComparison k B B P p hp ≪≫
        isoWhiskerRight (boundedNonpositiveTotalIso k B P data length hlo hhi) DerivedCategory.Q ≪≫
          data.comparison.symm)

/-- Exact localization compatibility for the generic bounded model. -/
theorem boundedNonpositiveDerivedIso_comparison (hlo : data.lower = -(length : ℤ)) (hhi : data.upper = 0) :
    whiskerLeft DerivedCategory.Q (boundedNonpositiveDerivedIso k B P data length hlo hhi).hom ≫
      data.comparison.hom =
    (BimoduleComplexTensor.derivedTotalComparison k B B P p hp).hom ≫
      whiskerRight (boundedNonpositiveTotalIso k B P data length hlo hhi).hom DerivedCategory.Q := by
  have h := (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q (C := ModuleCat.{u} B))
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ))
    (DerivedCategory (ModuleCat.{u} B))).map_preimage
      ((BimoduleComplexTensor.derivedTotalComparison k B B P p hp ≪≫
        isoWhiskerRight (boundedNonpositiveTotalIso k B P data length hlo hhi) DerivedCategory.Q ≪≫
          data.comparison.symm).hom)
  change whiskerLeft DerivedCategory.Q
    (boundedNonpositiveDerivedIso k B P data length hlo hhi).hom = _ at h
  rw [h]
  simp

/-- A natural endofunctor comparison identifies every actual object-function iterate. -/
def powerObjIso {C : Type*} [Category C] {F G : C ⥤ C} (e : F ≅ G) :
    (r : ℕ) → (Y : C) → (F.obj^[r]) Y ≅ (G.obj^[r]) Y
  | 0, Y => Iso.refl Y
  | r+1, Y => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact e.app _ ≪≫ G.mapIso (powerObjIso e r Y)

/-- Direct iterate transport for any same-complex bounded model on [-length,0]. -/
def boundedNonpositivePowerIso (hlo : data.lower = -(length : ℤ)) (hhi : data.upper = 0)
    (r : ℕ) (Y : DerivedCategory (ModuleCat.{u} B)) :
    ((BimoduleComplexTensor.derivedTotal k B B P p hp).obj^[r]) Y ≅
      (data.derived.obj^[r]) Y :=
  powerObjIso (boundedNonpositiveDerivedIso k B P data length hlo hhi) r Y
end LittleFinitistic.BimoduleTotalPresentation

end

end OAI
