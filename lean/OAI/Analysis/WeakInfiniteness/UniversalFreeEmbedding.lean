import Mathlib
import OAI.Analysis.WeakInfiniteness.FullGroupAlgebra

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology

namespace WeakPureInfiniteness

structure ContractionRepresentation where
  hilbert : ComplexHilbert.{0}
  [nontrivial : Nontrivial hilbert]
  operator : hilbert →L[ℂ] hilbert
  norm_operator_le_one : ‖operator‖ ≤ 1

attribute [instance] ContractionRepresentation.nontrivial

def ContractionAmbient : Type 1 :=
  lp (fun π : ContractionRepresentation => π.hilbert →L[ℂ] π.hilbert) ∞

instance : CStarAlgebra ContractionAmbient := by
  unfold ContractionAmbient
  exact { }

instance : CoeFun ContractionAmbient
    (fun _ => ∀ π : ContractionRepresentation, π.hilbert →L[ℂ] π.hilbert) :=
  ⟨fun z => z.val⟩

noncomputable def universalOperator : ContractionAmbient :=
  ⟨fun π => π.operator, memℓp_infty ⟨1, by
    rintro _ ⟨π, rfl⟩
    exact π.norm_operator_le_one⟩⟩

noncomputable def universalContractionSubalgebra : StarSubalgebra ℂ ContractionAmbient :=
  closedStarSpan {universalOperator}

def UniversalContraction : Type 1 := universalContractionSubalgebra

instance : CStarAlgebra UniversalContraction := closedStarSpanCStar _

noncomputable def universalContractionGenerator : UniversalContraction :=
  ⟨universalOperator, subset_closedStarSpan _ (Set.mem_singleton _)⟩

noncomputable def contractionEvaluation (π : ContractionRepresentation) :
    UniversalContraction →⋆ₐ[ℂ] (π.hilbert →L[ℂ] π.hilbert) where
  toFun x := x.val π
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_one' := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
lemma contractionEvaluation_star (π : ContractionRepresentation) (x : UniversalContraction) :
    contractionEvaluation π (star x) = star (contractionEvaluation π x) := rfl

@[simp]
lemma contractionEvaluation_smul (π : ContractionRepresentation) (c : ℂ) (x : UniversalContraction) :
    contractionEvaluation π (c • x) = c • contractionEvaluation π x := rfl

@[simp]
lemma contractionEvaluation_generator (π : ContractionRepresentation) :
    contractionEvaluation π universalContractionGenerator = π.operator := rfl

lemma norm_universalContractionGenerator_le_one : ‖universalContractionGenerator‖ ≤ 1 := by
  change ‖(universalOperator : ContractionAmbient)‖ ≤ 1
  apply lp.norm_le_of_forall_le zero_le_one
  exact fun π => π.norm_operator_le_one

end WeakPureInfiniteness
end

end OAI
