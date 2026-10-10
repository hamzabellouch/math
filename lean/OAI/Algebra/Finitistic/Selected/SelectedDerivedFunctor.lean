import OAI.Algebra.Finitistic.Localization.NativeSingleEvaluation
import OAI.Algebra.Finitistic.Selected.SelectedWindow
import OAI.Algebra.Finitistic.Selected.SelectedIteration

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.SelectedDerivedFunctor
open SelectedFixedDiagram QuadraticEncoding FiniteSelectionFamily

/-- One fixed genuine derived tensor functor, chosen before any test module. -/
def model : BimoduleTotal.BoundedProjective ℂ (B P) SelectedRectification.bimodule :=
  BimoduleTotal.nativeProjectiveModel SelectedRectification.bimodule
    (SelectedWindow.lo-2) SelectedWindow.hi SelectedWindow.bounded SelectedWindow.verified.projective

abbrev Phi := model.derived

/-- The previously explicit stalk-comparison premise is now discharged for the
actual fixed selecting bimodule and its actual derived tensor endofunctor. -/
def comparison (Y : S.{0}) : Phi.obj (derived Y) ≅
    SelectedTensorSplitting.object (representation Y).Evaluation :=
  model.nativeSingleEvaluation (representation Y).Evaluation

/-- The actual full B-linear binomial formula for the genuine tensor functor. -/
def iteration (j : ℕ) (Y : S.{0}) :
    (Phi.obj^[j]) (derived Y) ≅
      ⨁ fun q : Fin (j+1) => ⨁ fun _ : Fin (Nat.choose j q.val) =>
        (derived ((H^[j]) Y))⟦(3 : ℤ)*(q.val : ℤ)⟧ :=
  SelectedIteration.iteration Phi comparison j Y

theorem isZero_iff (j : ℕ) (Y : S.{0}) :
    IsZero ((Phi.obj^[j]) (derived Y)) ↔ Subsingleton (selectionIterate Y.val j) :=
  SelectedIteration.isZero_iff Phi comparison j Y

/-- Exact arbitrarily long finite extinction for one fixed actual tensor functor. -/
theorem extinction (m : ℕ) [NeZero m] :
    (∀ j < m, ¬ IsZero ((Phi.obj^[j]) (derived (test m)))) ∧
      IsZero ((Phi.obj^[m]) (derived (test m))) :=
  SelectedIteration.extinction Phi comparison m
end LittleFinitistic.SelectedDerivedFunctor

end

end OAI
