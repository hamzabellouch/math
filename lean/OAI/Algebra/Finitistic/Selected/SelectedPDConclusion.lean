import OAI.Algebra.Finitistic.Selected.SelectedPDUpperConsumer
import OAI.Algebra.Finitistic.Bar.CountTorBounds
import OAI.Algebra.Finitistic.Selected.SelectedCountExtinction

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedPDConclusion
open SelectedOrdinaryAlgebra SelectedOrdinaryModules
local instance : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- The canonical base-change Tor is computed by the actual selected bar,
independently of which compatible field-scalar instance presents that bar. -/
def baseTorIso (Y : FiniteSelectionFamily.S.{0}) (n : ℕ) :
    ((DerivedBar.Balanced.tensorFunctor augmentation).leftDerived n).obj (module Y) ≅
      (SelectedPDDetection.baseBar Y).homology n :=
  DerivedBar.Balanced.tensorBarHomologyIso augmentation (Inflated Y) n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat D) (.down ℕ) n).mapIso
      (DerivedBar.tensorBarIso ℂ A D (Inflated Y) augmentation)

/-- Actual tensor extinction implies finite projective dimension over the
one fixed square-zero algebra A. The bar bounds and minimal detector are proved. -/
theorem finite_pd_of_extinction (Y : FiniteSelectionFamily.S.{0}) (t : ℕ)
    (h : IsZero (SelectedBaseIterates.object Y t)) :
    projectiveDimension (module Y) < ⊤ := by
  apply SelectedPDDetection.finite_pd_of_bounded_base_bar Y
  refine ⟨t * (3 * length + 5), fun n hn => ?_⟩
  have hc := DerivedBar.ParityBridge.baseChangeTor_bounded_of_counts ℂ D X
    (SelectedBaseIterates.input Y) (t * (3 * length + 5))
    (fun r n hn => SelectedCountExtinction.uniform_homology_zero Y t h r (-(n : ℤ))
      (Or.inl (by omega))) n hn
  exact hc.of_iso (baseTorIso Y n).symm

/-- A surviving actual derived iterate supplies a nonzero original count
class and hence the manuscript's projective-dimension lower bound. -/
theorem lower_bound_of_survival (Y : FiniteSelectionFamily.S.{0}) (r : ℕ)
    (h : ¬ IsZero (SelectedBaseIterates.object Y r)) :
    (r : WithBot ℕ∞) ≤ projectiveDimension (module Y) := by
  obtain ⟨n,hrn,_,hn⟩ := SelectedCountCohomology.nonzero_degree Y r h
  have hc := DerivedBar.ParityBridge.baseChangeTor_nonzero_of_count ℂ D X
    (SelectedBaseIterates.input Y) r n hn
  apply SelectedPDDetection.lower_bound_of_base_bar Y r n hrn
  intro hz
  exact hc (hz.of_iso (baseTorIso Y n))

/-- Both conclusions of the manuscript's projective-dimension detector for
the actual finite selected family; no bar comparison or pd bound is a premise. -/
theorem detection (Y : FiniteSelectionFamily.S.{0}) :
    (∀ t, IsZero (SelectedBaseIterates.object Y t) → projectiveDimension (module Y) < ⊤) ∧
    (∀ r, ¬ IsZero (SelectedBaseIterates.object Y r) →
      (r : WithBot ℕ∞) ≤ projectiveDimension (module Y)) :=
  ⟨finite_pd_of_extinction Y, lower_bound_of_survival Y⟩
end LittleFinitistic.SelectedPDConclusion

end

end OAI
