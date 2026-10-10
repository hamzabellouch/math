import OAI.Analysis.FiniteFactor.CrossedProduct.HilbertSeparable
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.Basic

namespace OAI

namespace FiniteFactor
open TopologicalSpace
noncomputable section

abbrev SourceAlgebraSpace (θ : SourceCoordinate → ℝ) := (sourceAlgebra θ).toStarSubalgebra

def sourceAlgebraInclusion (θ : SourceCoordinate → ℝ) :
    SourceAlgebraSpace θ →L[ℂ] (SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :=
  (sourceAlgebra θ).toStarSubalgebra.toSubmodule.subtypeL

/-- An actual vector functional restricted to the original source algebra. -/
def sourceVectorFunctional (θ : SourceCoordinate → ℝ)
    (ξ η : SourceHilbert SourceCoordinate) : StrongDual ℂ (SourceAlgebraSpace θ) :=
  (innerSL ℂ ξ).comp ((ContinuousLinearMap.apply ℂ (SourceHilbert SourceCoordinate) η).comp
    (sourceAlgebraInclusion θ))

@[simp] theorem sourceVectorFunctional_apply (θ : SourceCoordinate → ℝ)
    (ξ η : SourceHilbert SourceCoordinate) (A : SourceAlgebraSpace θ) :
    sourceVectorFunctional θ ξ η A = inner ℂ ξ ((A : SourceHilbert SourceCoordinate →L[ℂ]
      SourceHilbert SourceCoordinate) η) := rfl

theorem sourceVectorFunctional_norm (θ : SourceCoordinate → ℝ)
    (ξ η : SourceHilbert SourceCoordinate) :
    ‖sourceVectorFunctional θ ξ η‖ ≤ ‖ξ‖*‖η‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro A
  change ‖inner ℂ ξ ((A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) η)‖ ≤ _
  calc
    _ ≤ ‖ξ‖ * ‖(A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) η‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * (‖A‖ * ‖η‖) := mul_le_mul_of_nonneg_left
      ((A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate).le_opNorm η) (norm_nonneg _)
    _ = (‖ξ‖*‖η‖)*‖A‖ := by ring

theorem sourceVectorFunctional_continuous (θ : SourceCoordinate → ℝ) :
    Continuous (fun z : SourceHilbert SourceCoordinate × SourceHilbert SourceCoordinate =>
      sourceVectorFunctional θ z.1 z.2) := by
  unfold sourceVectorFunctional
  fun_prop

/-- The norm-closed span of actual vector functionals. This constructs a
Banach space; identifying its whole dual with the source algebra is a
separate surjectivity theorem, not part of this definition. -/
abbrev sourceNormalFunctionalSpace (θ : SourceCoordinate → ℝ) :
    Submodule ℂ (StrongDual ℂ (SourceAlgebraSpace θ)) :=
  (Submodule.span ℂ (Set.range (fun z : SourceHilbert SourceCoordinate × SourceHilbert SourceCoordinate =>
    sourceVectorFunctional θ z.1 z.2))).topologicalClosure

instance sourceNormalFunctionalSpace_complete (θ : SourceCoordinate → ℝ) :
    CompleteSpace (sourceNormalFunctionalSpace θ) := by
  unfold sourceNormalFunctionalSpace
  infer_instance

instance sourceNormalFunctionalSpace_separable (θ : SourceCoordinate → ℝ) :
    SeparableSpace (sourceNormalFunctionalSpace θ) := by
  let : NormedAddCommGroup (StrongDual ℂ (SourceAlgebraSpace θ)) := inferInstance
  apply TopologicalSpace.IsSeparable.separableSpace
  change IsSeparable (closure (Submodule.span ℂ (Set.range
    (fun z : SourceHilbert SourceCoordinate × SourceHilbert SourceCoordinate =>
      sourceVectorFunctional θ z.1 z.2)) : Set (StrongDual ℂ (SourceAlgebraSpace θ))))
  exact (isSeparable_range (sourceVectorFunctional_continuous θ)).span.closure

theorem sourceVectorFunctional_mem (θ : SourceCoordinate → ℝ)
    (ξ η : SourceHilbert SourceCoordinate) : sourceVectorFunctional θ ξ η ∈ sourceNormalFunctionalSpace θ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(ξ,η),rfl⟩)

/-- A named carrier keeps the inherited Banach-space structures coherent in
iterated continuous duals. Its underlying set is exactly the closed span. -/
def SourceNormalPredualSpace (θ : SourceCoordinate → ℝ) : Type :=
  sourceNormalFunctionalSpace θ

instance sourceNormalPredualSpace_normedGroup (θ : SourceCoordinate → ℝ) :
    NormedAddCommGroup (SourceNormalPredualSpace θ) := by
  unfold SourceNormalPredualSpace
  exact Submodule.normedAddCommGroup (E := StrongDual ℂ (SourceAlgebraSpace θ))
    (sourceNormalFunctionalSpace θ)

instance sourceNormalPredualSpace_normedSpace (θ : SourceCoordinate → ℝ) :
    NormedSpace ℂ (SourceNormalPredualSpace θ) := by
  unfold SourceNormalPredualSpace
  exact Submodule.normedSpace (𝕜 := ℂ) (E := StrongDual ℂ (SourceAlgebraSpace θ))
    (sourceNormalFunctionalSpace θ)

instance sourceNormalPredualSpace_complete (θ : SourceCoordinate → ℝ) :
    CompleteSpace (SourceNormalPredualSpace θ) :=
  inferInstanceAs (CompleteSpace (sourceNormalFunctionalSpace θ))

instance sourceNormalPredualSpace_separable (θ : SourceCoordinate → ℝ) :
    SeparableSpace (SourceNormalPredualSpace θ) :=
  inferInstanceAs (SeparableSpace (sourceNormalFunctionalSpace θ))

/-- Evaluation by each actual algebra element on the constructed space. -/
def sourceNormalEvaluation (θ : SourceCoordinate → ℝ) (A : SourceAlgebraSpace θ) :
    StrongDual ℂ (SourceNormalPredualSpace θ) := by
  exact (ContinuousLinearMap.apply ℂ ℂ A).comp
    (sourceNormalFunctionalSpace θ).subtypeL

@[simp] theorem sourceNormalEvaluation_vector (θ : SourceCoordinate → ℝ) (A : SourceAlgebraSpace θ)
    (ξ η : SourceHilbert SourceCoordinate) :
    sourceNormalEvaluation θ A ⟨sourceVectorFunctional θ ξ η,sourceVectorFunctional_mem θ ξ η⟩ =
      inner ℂ ξ ((A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) η) := rfl

/-- The constructed functionals separate the original algebra elements. -/
theorem sourceNormalEvaluation_injective (θ : SourceCoordinate → ℝ) :
    Function.Injective (sourceNormalEvaluation θ) := by
  intro A B h
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro η
  apply ext_inner_left ℂ
  intro ξ
  exact congrArg (fun F : StrongDual ℂ (SourceNormalPredualSpace θ) =>
    F ⟨sourceVectorFunctional θ ξ η,sourceVectorFunctional_mem θ ξ η⟩) h

end
end FiniteFactor

end OAI
