import OAI.Algebra.Finitistic.Selected.SelectedPDBarConsumer
import OAI.Algebra.Finitistic.Selected.SelectedPDResidueProjection
import OAI.Algebra.Finitistic.Selected.SelectedCountCohomology

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedPDDetection
open SelectedOrdinaryAlgebra SelectedOrdinaryModules
local instance : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- A supplied inclusion/retraction of the original count summand into the
actual full bar converts native iterate survival directly into the pd bound.
Native supplies the proved nonzero degree; no shift/amplitude proof is duplicated. -/
theorem lower_bound_of_surviving_count (Y : FiniteSelectionFamily.S.{0}) (r : ℕ)
    (h : ¬ IsZero (SelectedBaseIterates.object Y r))
    (i : SelectedCountCohomology.count Y r ⟶ PDBarQuotient.baseDerived augmentation (Inflated Y))
    (p : PDBarQuotient.baseDerived augmentation (Inflated Y) ⟶ SelectedCountCohomology.count Y r)
    (hip : i ≫ p = 𝟙 (SelectedCountCohomology.count Y r)) :
    r ≤ projectiveDimension (module Y) := by
  obtain ⟨n,hrn,_,hn⟩ := SelectedCountCohomology.nonzero_degree Y r h
  exact lower_bound_of_base_derived_bar Y _ _ (Iso.refl _) i p hip r n hrn hn
end LittleFinitistic.SelectedPDDetection

end

end OAI
