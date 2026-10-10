import OAI.Algebra.Finitistic.Selected.SelectedReferenceCohomology
import OAI.Algebra.Finitistic.Selected.SelectedTensorSplitting
import OAI.Algebra.Finitistic.Selected.SelectedChainAction

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.SelectedRealization
open SelectedFixedDiagram QuadraticEncoding SelectedNativeEvaluation
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

local instance selectedModule : Module SelectionRing (H (Y := Y)) :=
  inferInstanceAs (Module SelectionRing (selectionStep (ModuleCat.of SelectionRing Y)))
local instance selectedTower : IsScalarTower ℂ SelectionRing (H (Y := Y)) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

abbrev input := (SelectedChainHomology.representation (Y := Y)).Evaluation
abbrev selectedRepresentation := SourceActionEvaluation.representation (Y := H (Y := Y)) encoding
abbrev reference := EvaluationVertexDiagram.module (selectedRepresentation (Y := Y))

omit [FiniteDimensional ℂ Y] in
lemma selected_action (a : Fin (encoding.generators+1)) :
    EvaluationVertexDiagram.action (Y := H (Y := Y)) (selectedRepresentation (Y := Y)) a =
      HAction (Y := Y) (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [HAction_apply]
  refine Fin.cases ?_ (fun j => ?_) a
  · change x = (1 : SelectionRing) • x
    rw [one_smul]
  · rfl

def coordinates (n : ℤ) (hn : n = 0 ∨ n = -3) :
    ∀ v : Fin 3, (SelectedTensor.source (input (Y := Y)) v).homology n ≅ H (Y := Y) :=
  Fin.cases (SelectedChainHomology.D0Iso n hn)
    (Fin.cases (SelectedChainHomology.D1Iso n hn)
      (fun _ => SelectedChainHomology.D2Iso n hn))

lemma coordinates01 (a : Fin (encoding.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = -3) :
    homologyMap (((BalancedTensor.tensorFunctor ℂ (B P) (input (Y := Y))).mapHomologicalComplex (.up ℤ)).map
      (SelectedRectification.f a)) n ≫ (coordinates (Y := Y) n hn 1).hom =
      (coordinates (Y := Y) n hn 0).hom ≫ EvaluationVertexDiagram.action (Y := H (Y := Y)) (selectedRepresentation (Y := Y)) a := by
  erw [selected_action (Y := Y)]
  exact SelectedChainHomology.fixed_arrow01 a n hn

lemma coordinates12 (a : Fin (encoding.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = -3) :
    homologyMap (((BalancedTensor.tensorFunctor ℂ (B P) (input (Y := Y))).mapHomologicalComplex (.up ℤ)).map
      (SelectedRectification.g a)) n ≫ (coordinates (Y := Y) n hn 2).hom =
      (coordinates (Y := Y) n hn 1).hom ≫ EvaluationVertexDiagram.action (Y := H (Y := Y)) (selectedRepresentation (Y := Y)) a := by
  erw [selected_action (Y := Y)]
  exact SelectedChainHomology.fixed_arrow12 a n hn

/-- The entire cohomology B-module is the manuscript's M(H(Y)), in both degrees. -/
def cohomology (n : ℤ) (hn : n = 0 ∨ n = -3) :
    (SelectedTensor.complex (input (Y := Y))).homology n ≅ reference (Y := Y) :=
  SelectedReferenceCohomology.iso _ (selectedRepresentation (Y := Y)) n (coordinates (Y := Y) n hn)
    (fun a => coordinates01 a n hn) (fun a => coordinates12 a n hn)

lemma source_zero (n : ℤ) (hn0 : n ≠ 0) (hn3 : n ≠ -3) (v : Fin 3) :
    IsZero ((SelectedTensor.source (input (Y := Y)) v).homology n) := by
  fin_cases v
  · exact SelectedChainHomology.D0_zero n hn0 hn3
  · exact SelectedChainHomology.D1_zero n hn0 hn3
  · exact SelectedChainHomology.D2_zero n hn0 hn3

/-- The one fixed selecting bimodule realizes H on every finite-dimensional Y.
This is an isomorphism in the full B-module derived category. -/
def realization :
    SelectedTensorSplitting.object (input (Y := Y)) ≅
      (DerivedCategory.singleFunctor (ModuleCat (B P)) 0).obj (reference (Y := Y)) ⊞
        ((DerivedCategory.singleFunctor (ModuleCat (B P)) 0).obj (reference (Y := Y)))⟦(3 : ℤ)⟧ :=
  SelectedTensorSplitting.split _ _ (cohomology 0 (Or.inl rfl))
    (cohomology (-3) (Or.inr rfl)) source_zero
end LittleFinitistic.SelectedRealization

end

end OAI
