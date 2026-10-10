import OAI.Algebra.Finitistic.Selected.SelectedOrdinaryAlgebra
import OAI.Algebra.Finitistic.Selected.SelectedDerivedFunctor
import OAI.Algebra.Finitistic.Ordinary.OrdinaryShiftDerivedTensor

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.SelectedShiftedRealization
open SelectedFixedDiagram QuadraticEncoding SelectedOrdinaryAlgebra
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- The actual shifted selecting bimodule, with its full B actions. -/
abbrev shifted := SelectedRectification.bimodule⟦b⟧

def model : BimoduleTotal.BoundedProjective ℂ (B P) shifted where
  lower := -(length : ℤ)
  upper := 0
  bounded := OrdinarySimulation.shifted_support _ b length a endpoints support
  projective n := by
    exact SelectedOrdinaryAlgebra.term_projective (n+b)

abbrev G := model.derived

/-- Tensoring a selected stalk by the shifted fixed bimodule shifts the already
verified full B-linear tensor complex. -/
def comparison (Y : FiniteSelectionFamily.S.{0}) :
    G.obj (FiniteSelectionFamily.derived Y) ≅
      (SelectedTensorSplitting.object (FiniteSelectionFamily.representation Y).Evaluation)⟦b⟧ :=
  model.nativeSingleEvaluation (FiniteSelectionFamily.representation Y).Evaluation ≪≫
    DerivedCategory.Q.mapIso
      ((((BimoduleBalancedTensor.functor ℂ (B P)
        (FiniteSelectionFamily.representation Y).Evaluation).mapHomologicalComplex (.up ℤ)).commShiftIso b).app
          SelectedRectification.bimodule) ≪≫
    (DerivedCategory.Q.commShiftIso b).app _

/-- The concrete two summands for one application of the actual shifted tensor. -/
def realizationNested (Y : FiniteSelectionFamily.S.{0}) :
    G.obj (FiniteSelectionFamily.derived Y) ≅
      (FiniteSelectionFamily.derived (FiniteSelectionFamily.H Y))⟦b⟧ ⊞
        ((FiniteSelectionFamily.derived (FiniteSelectionFamily.H Y))⟦(3 : ℤ)⟧)⟦b⟧ :=
  comparison Y ≪≫ (shiftFunctor _ b).mapIso (FiniteSelectionFamily.realization Y) ≪≫
    (shiftFunctor _ b).mapBiprod _ _

/-- The source convention places the two summands in shifts b and b+3. -/
def realization (Y : FiniteSelectionFamily.S.{0}) :
    G.obj (FiniteSelectionFamily.derived Y) ≅
      (FiniteSelectionFamily.derived (FiniteSelectionFamily.H Y))⟦b⟧ ⊞
        (FiniteSelectionFamily.derived (FiniteSelectionFamily.H Y))⟦b+3⟧ :=
  realizationNested Y ≪≫ biprod.mapIso (Iso.refl _)
    ((shiftAdd _ (3 : ℤ) b).symm ≪≫ eqToIso (by rw [add_comm (3 : ℤ) b]))

def iteration (j : ℕ) (Y : FiniteSelectionFamily.S.{0}) :
    (G.obj^[j]) (FiniteSelectionFamily.derived Y) ≅
      ExternalTensor.Binomial.binomialObject b 3 j
        (FiniteSelectionFamily.derived ((FiniteSelectionFamily.H^[j]) Y)) :=
  ExternalTensor.Binomial.binomialIteration G FiniteSelectionFamily.derived
    FiniteSelectionFamily.H b 3 realization j Y

theorem isZero_iff (j : ℕ) (Y : FiniteSelectionFamily.S.{0}) :
    IsZero ((G.obj^[j]) (FiniteSelectionFamily.derived Y)) ↔
      Subsingleton (selectionIterate Y.val j) :=
  (ExternalTensor.Binomial.iteration_isZero_iff G FiniteSelectionFamily.derived
    FiniteSelectionFamily.H b 3 realization j Y).trans
    ((FiniteSelectionFamily.derived_zero _).trans
      (by rw [FiniteSelectionFamily.iterate_val]))

theorem extinction (m : ℕ) [NeZero m] :
    (∀ j < m, ¬ IsZero ((G.obj^[j]) (FiniteSelectionFamily.derived (FiniteSelectionFamily.test m)))) ∧
      IsZero ((G.obj^[m]) (FiniteSelectionFamily.derived (FiniteSelectionFamily.test m))) := by
  constructor
  · intro j hj hz
    have hs := (isZero_iff j (FiniteSelectionFamily.test m)).mp hz
    exact @not_subsingleton _ (selectionIterate_test_nontrivial m j hj) hs
  · exact (isZero_iff m (FiniteSelectionFamily.test m)).mpr (selectionIterate_test_subsingleton m)
end LittleFinitistic.SelectedShiftedRealization

end

end OAI
