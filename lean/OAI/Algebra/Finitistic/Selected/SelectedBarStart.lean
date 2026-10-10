import OAI.Algebra.Finitistic.Selected.SelectedFirstBlockFamily
import OAI.Algebra.Finitistic.Bar.IntegerStalk

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedBarStart
open SelectedOrdinaryAlgebra SelectedBaseIterates
local instance : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- Bar iteration starts at exactly the same first-block derived stalk as the
ordinary simulation, through the actual extension and localization isomorphisms. -/
def startIso (Y : FiniteSelectionFamily.S.{0}) :
    object Y 0 ≅ SelectedFirstBlockFamily.derived Y :=
  DerivedBar.IterateSupport.resolvedModelIso ℂ D X (input Y) 0 ≪≫
    DerivedBar.integerStalkIso D (input Y)

theorem start_zero (Y : FiniteSelectionFamily.S.{0}) :
    IsZero (object Y 0) ↔ Subsingleton Y.val :=
  (startIso Y).isZero_iff.trans (SelectedFirstBlockFamily.derived_zero Y)

/-- The selected first-block stalk family has the exact original H-extinction. -/
theorem firstBlock_extinction (m : ℕ) [NeZero m] :
    (∀ j < m, ¬ IsZero (SelectedFirstBlockFamily.derived
      ((FiniteSelectionFamily.H^[j]) (FiniteSelectionFamily.test m)))) ∧
    IsZero (SelectedFirstBlockFamily.derived
      ((FiniteSelectionFamily.H^[m]) (FiniteSelectionFamily.test m))) := by
  simpa only [SelectedFirstBlockFamily.derived_zero, FiniteSelectionFamily.derived_zero] using
    FiniteSelectionFamily.extinction m
end LittleFinitistic.SelectedBarStart

end

end OAI
