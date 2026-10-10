import OAI.Algebra.Finitistic.Ordinary.OrdinaryFirstDerivedCompatibility
import OAI.Algebra.Finitistic.Ordinary.OrdinaryFirstComponentExact

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BlockModule
universe u
variable (L R : Type u) [Ring L] [Ring R]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} L)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (L × R))]

/-- The exact derived first-component functor on the whole product-ring derived category. -/
abbrev derivedFirstComponent := (ProductModules.firstFunctor.{u,u} L R).mapDerivedCategory

def firstComplexComponentIso : firstComplexFunctor L R ⋙
    (ProductModules.firstFunctor L R).mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex (ModuleCat.{u} L) ℤ) :=
  Functor.mapHomologicalComplexCompIso (ProductModules.firstInflationComponentIso L R) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (ModuleCat.{u} L) (.up ℤ)

/-- On chain representatives, the composite is the identity localization. -/
def derivedFirstComponentFactors : DerivedCategory.Q ⋙ derivedFirst L R ⋙
    derivedFirstComponent L R ≅ (DerivedCategory.Q : CochainComplex (ModuleCat.{u} L) ℤ ⥤ _) :=
  (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight (derivedFirstComparison L R) _ ≪≫
    Functor.associator .. ≪≫
    Functor.isoWhiskerLeft _ (ProductModules.firstFunctor L R).mapDerivedCategoryFactors ≪≫
    (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight (firstComplexComponentIso L R) _ ≪≫ Functor.leftUnitor _

/-- Taking the first component recovers every derived object, naturally. -/
def derivedFirstRetraction : derivedFirst L R ⋙ derivedFirstComponent L R ≅
    𝟭 (DerivedCategory (ModuleCat.{u} L)) := by
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} L) (.up ℤ)) DerivedCategory.Q
      (derivedFirst L R ⋙ derivedFirstComponent L R) := ⟨derivedFirstComponentFactors L R⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} L) (.up ℤ))
    DerivedCategory.Q DerivedCategory.Q _ _ (Iso.refl _)

/-- The same retraction for mathlib's exact derived inflation. -/
def exactFirstRetraction : (ProductModules.firstInflation L R).mapDerivedCategory ⋙
    derivedFirstComponent L R ≅ 𝟭 (DerivedCategory (ModuleCat.{u} L)) :=
  Functor.isoWhiskerRight (derivedFirstIso L R).symm _ ≪≫ derivedFirstRetraction L R

instance derivedFirst_additive : (derivedFirst L R).Additive :=
  Functor.additive_of_iso (derivedFirstIso L R).symm

/-- No derived object becomes zero merely by putting it in the first block. -/
theorem derivedFirst_isZero_iff (Y : DerivedCategory (ModuleCat.{u} L)) :
    IsZero ((derivedFirst L R).obj Y) ↔ IsZero Y := by
  constructor
  · intro h
    exact ((derivedFirstRetraction L R).app Y).isZero_iff.mp
      ((derivedFirstComponent L R).map_isZero h)
  · exact (derivedFirst L R).map_isZero

theorem exactFirst_isZero_iff (Y : DerivedCategory (ModuleCat.{u} L)) :
    IsZero ((ProductModules.firstInflation L R).mapDerivedCategory.obj Y) ↔ IsZero Y :=
  ((derivedFirstIso L R).app Y).isZero_iff.symm.trans (derivedFirst_isZero_iff L R Y)
end LittleFinitistic.BlockModule

end

end OAI
