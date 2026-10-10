import OAI.Algebra.Finitistic.Ordinary.OrdinaryBlockDerived
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BlockModule
universe u
variable (L R : Type u) [Ring L] [Ring R]

/-- First-block inflation is exact for arbitrary, possibly noncommutative rings. -/
instance firstInflation_preservesFiniteLimits :
    PreservesFiniteLimits (ProductModules.firstInflation.{u,u} L R) := by
  let := RestrictionHomology.preservesHomology (RingHom.fst L R)
  exact Functor.preservesFiniteLimits_of_preservesHomology _

instance firstInflation_preservesFiniteColimits :
    PreservesFiniteColimits (ProductModules.firstInflation.{u,u} L R) := by
  let := RestrictionHomology.preservesHomology (RingHom.fst L R)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} L)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (L × R))]

instance derivedFirst_lifting : Localization.Lifting DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} L) (.up ℤ))
    (firstComplexFunctor L R ⋙ DerivedCategory.Q) (derivedFirst L R) :=
  ⟨derivedFirstComparison L R⟩

/-- The ordinary localization model is naturally the exact derived inflation. -/
def derivedFirstIso : derivedFirst L R ≅ (ProductModules.firstInflation L R).mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} L) (.up ℤ))
    (firstComplexFunctor L R ⋙ DerivedCategory.Q)
    (firstComplexFunctor L R ⋙ DerivedCategory.Q)
    (derivedFirst L R) (ProductModules.firstInflation L R).mapDerivedCategory (Iso.refl _)

/-- The comparison agrees with both specified localization comparison maps. -/
@[reassoc (attr := simp)]
theorem derivedFirstIso_hom_app_Q (Z : CochainComplex (ModuleCat.{u} L) ℤ) :
    (derivedFirstIso L R).hom.app (DerivedCategory.Q.obj Z) ≫
      (ProductModules.firstInflation L R).mapDerivedCategoryFactors.hom.app Z =
    (derivedFirstComparison L R).hom.app Z := by
  simp only [derivedFirstIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  change ((derivedFirstComparison L R).hom.app Z ≫
    (ProductModules.firstInflation L R).mapDerivedCategoryFactors.inv.app Z) ≫
    (ProductModules.firstInflation L R).mapDerivedCategoryFactors.hom.app Z = _
  simp

/-- Transport the coherent integer shift structure of the exact derived functor. -/
instance derivedFirst_commShift : (derivedFirst L R).CommShift ℤ :=
  Functor.CommShift.ofIso (derivedFirstIso L R).symm ℤ

instance derivedFirstIso_inv_commShift : NatTrans.CommShift (derivedFirstIso L R).inv ℤ :=
  Functor.CommShift.ofIso_compatibility (derivedFirstIso L R).symm ℤ

instance derivedFirstIso_hom_commShift : NatTrans.CommShift (derivedFirstIso L R).hom ℤ := by
  let : NatTrans.CommShift (derivedFirstIso L R).symm.hom ℤ :=
    derivedFirstIso_inv_commShift L R
  exact NatTrans.CommShift.of_iso_inv (derivedFirstIso L R).symm ℤ

instance derivedFirst_isTriangulated : (derivedFirst L R).IsTriangulated :=
  Functor.isTriangulated_of_iso (derivedFirstIso L R).symm
end LittleFinitistic.BlockModule

end

end OAI
