import OAI.Algebra.Finitistic.Rectification.VertexTensorEvaluation
import OAI.Algebra.Finitistic.Localization.TensorEvaluationComparison

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.QuadraticEncoding
open IdempotentTensor BalancedTensor Representation
universe u v
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The manuscript's actual right vertex projectives. -/
def vertexModule (i : Fin 3) : ModuleCat.{u} (B P)ᵐᵒᵖ :=
  ModuleCat.of (B P)ᵐᵒᵖ (rightIdeal (vertexId (P := P) i))

def arrowModule01 (h : Fin (d+1)) : vertexModule P 0 ⟶ vertexModule P 1 :=
  ModuleCat.ofHom (leftMultiply (arrow01 P h) (arrow01_target h))
def arrowModule12 (h : Fin (d+1)) : vertexModule P 1 ⟶ vertexModule P 2 :=
  ModuleCat.ofHom (leftMultiply (arrow12 P h) (arrow12_target h))

variable {P} {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

/-- The natural identifications for the actual tensor functor. -/
def evaluationVertexEquiv (i : Fin 3) :
    (tensorFunctor k (B P) X.Evaluation).obj (vertexModule P i) ≃ₗ[k] Y :=
  (tensorFunctorEquiv (rightIdeal (vertexId (P := P) i)) X.Evaluation).trans (X.vertexTensorEquiv i)

theorem evaluation_arrow01 (h : Fin (d+1)) (y : Y) :
    evaluationVertexEquiv X 1
      ((tensorFunctor k (B P) X.Evaluation).map (arrowModule01 P h)
        ((evaluationVertexEquiv X 0).symm y)) =
      (Fin.cases (motive := fun _ => Module.End k Y) 1 X.generator h) y := by
  change X.projection 1 ((arrow01 P h * vertexId (P := P) 0) • X.inclusion 0 y) = _
  rw [arrow01_source]
  erw [X.arrow01_smul]
  rfl

theorem evaluation_arrow12 (h : Fin (d+1)) (y : Y) :
    evaluationVertexEquiv X 2
      ((tensorFunctor k (B P) X.Evaluation).map (arrowModule12 P h)
        ((evaluationVertexEquiv X 1).symm y)) =
      (Fin.cases (motive := fun _ => Module.End k Y) 1 X.generator h) y := by
  change X.projection 2 ((arrow12 P h * vertexId (P := P) 1) • X.inclusion 1 y) = _
  rw [arrow12_source]
  erw [X.arrow12_smul]
  rfl

/-- Tensor evaluation sends s to an actual isomorphism, conjugate to id_Y. -/
theorem evaluation_s_isIso : IsIso ((tensorFunctor k (B P) X.Evaluation).map (arrowModule01 P 0)) := by
  let e := (evaluationVertexEquiv X 0).trans (evaluationVertexEquiv X 1).symm
  have he : (tensorFunctor k (B P) X.Evaluation).map (arrowModule01 P 0) = e.toModuleIso.hom := by
    ext z
    apply (evaluationVertexEquiv X 1).injective
    have h := evaluation_arrow01 X 0 (evaluationVertexEquiv X 0 z)
    simpa [e] using h
  rw [he]
  infer_instance

theorem evaluation_s'_isIso : IsIso ((tensorFunctor k (B P) X.Evaluation).map (arrowModule12 P 0)) := by
  let e := (evaluationVertexEquiv X 1).trans (evaluationVertexEquiv X 2).symm
  have he : (tensorFunctor k (B P) X.Evaluation).map (arrowModule12 P 0) = e.toModuleIso.hom := by
    ext z
    apply (evaluationVertexEquiv X 2).injective
    have h := evaluation_arrow12 X 0 (evaluationVertexEquiv X 1 z)
    simpa [e] using h
  rw [he]
  infer_instance
end LittleFinitistic.QuadraticEncoding

end

end OAI
