import OAI.Algebra.Finitistic.Ordinary.OrdinaryRestrictionHomology
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import OAI.Algebra.Finitistic.Selected.SelectedBaseIterates
import OAI.Algebra.Finitistic.Selected.SelectedDerivedFunctor
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedFirstBlockFamily
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
open SelectedOrdinaryAlgebra SelectedFixedDiagram QuadraticEncoding
local instance : HasDerivedCategory.{1} (ModuleCat.{0} (B P)) :=
  HasDerivedCategory.standard (ModuleCat.{0} (B P))
local instance : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- The actual exact inflation functor from B-modules to the first D-block. -/
abbrev inflation : ModuleCat.{0} (B P) ⥤ ModuleCat.{0} D := ModuleCat.restrictScalars SelectedOrdinaryModules.firstProjection
instance inflation_preservesFiniteLimits : PreservesFiniteLimits inflation := by
  have h : PreservesFiniteLimits inflation ∧ PreservesFiniteColimits inflation :=
    ((Functor.exact_tfae inflation).out 2 4).mp
      (RestrictionHomology.mapsExact SelectedOrdinaryModules.firstProjection)
  exact h.1
instance inflation_preservesFiniteColimits : PreservesFiniteColimits inflation := by
  have h : PreservesFiniteLimits inflation ∧ PreservesFiniteColimits inflation :=
    ((Functor.exact_tfae inflation).out 2 4).mp
      (RestrictionHomology.mapsExact SelectedOrdinaryModules.firstProjection)
  exact h.2
abbrev derivedInflation := inflation.mapDerivedCategory

instance derivedInflation_additive : derivedInflation.Additive := by
  rw [Localization.functor_additive_iff DerivedCategory.Qh
    (HomotopyCategory.subcategoryAcyclic (ModuleCat.{0} (B P))).trW]
  exact Functor.additive_of_iso inflation.mapDerivedCategoryFactorsh.symm

/-- This is the original selected input, with precisely its constructed D-action. -/
def moduleIso (Y : FiniteSelectionFamily.S.{0}) :
    inflation.obj (FiniteSelectionFamily.module Y) ≅ SelectedBaseIterates.input Y :=
  Iso.refl _

abbrev derived (Y : FiniteSelectionFamily.S.{0}) :=
  (DerivedCategory.singleFunctor (ModuleCat D) 0).obj (SelectedBaseIterates.input Y)

/-- Exact inflation on derived categories agrees with the selected first-block stalk. -/
def stalkIso (Y : FiniteSelectionFamily.S.{0}) :
    derivedInflation.obj (FiniteSelectionFamily.derived Y) ≅ derived Y :=
  (inflation.mapDerivedCategorySingleFunctor 0).app (FiniteSelectionFamily.module Y) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat D) 0).mapIso (moduleIso Y)

theorem module_zero (Y : FiniteSelectionFamily.S.{0}) :
    IsZero (SelectedBaseIterates.input Y) ↔ Subsingleton Y.val := by
  rw [← FiniteSelectionFamily.module_zero Y]
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  rfl

theorem derived_zero (Y : FiniteSelectionFamily.S.{0}) :
    IsZero (derived Y) ↔ Subsingleton Y.val := by
  rw [← module_zero Y]
  constructor
  · intro h
    exact ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat D) 0).app
      (SelectedBaseIterates.input Y)).isZero_iff.mp
        ((DerivedCategory.homologyFunctor (ModuleCat D) 0).map_isZero h)
  · exact (DerivedCategory.singleFunctor (ModuleCat D) 0).map_isZero

/-- The already proved Phi realization, transported by the actual first-block
inflation, with no ordinary F² identity assumed or asserted. -/
def inflated_realization (Y : FiniteSelectionFamily.S.{0}) :
    derivedInflation.obj (SelectedDerivedFunctor.Phi.obj (FiniteSelectionFamily.derived Y)) ≅
      derived (FiniteSelectionFamily.H Y) ⊞ (derived (FiniteSelectionFamily.H Y))⟦(3 : ℤ)⟧ :=
  derivedInflation.mapIso (SelectedDerivedFunctor.comparison Y ≪≫ FiniteSelectionFamily.realization Y) ≪≫
    derivedInflation.mapBiprod _ _ ≪≫
      biprod.mapIso (stalkIso _) ((derivedInflation.commShiftIso (3 : ℤ)).app _ ≪≫
        (shiftFunctor _ (3 : ℤ)).mapIso (stalkIso _))
end LittleFinitistic.SelectedFirstBlockFamily

end

end OAI
