import OAI.Analysis.IrrationalRotation.Analysis.ConcretePredualRepresentation
import OAI.Analysis.IrrationalRotation.Analysis.ConcretePredualEvaluation
import OAI.Analysis.IrrationalRotation.Analysis.ConcretePredualSeparable

namespace OAI

noncomputable section
namespace Invariant233.ConcretePredual

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance completedPredualNormedAddCommGroup (M : VonNeumannAlgebra H) :
    NormedAddCommGroup (predual M) := (predual M).normedAddCommGroup
local instance completedPredualNormedSpace (M : VonNeumannAlgebra H) :
    NormedSpace ℂ (predual M) := (predual M).normedSpace

def evaluationLinearIsometryEquiv (M : VonNeumannAlgebra H) :
    M ≃ₗᵢ[ℂ] StrongDual ℂ (predual M) :=
  LinearIsometryEquiv.ofSurjective (evaluationLinearIsometry M)
    (evaluation_surjective M)

@[simp]
theorem evaluationLinearIsometryEquiv_apply (M : VonNeumannAlgebra H) (A : M) :
    evaluationLinearIsometryEquiv M A = evaluation M A := rfl

theorem hasSeparablePredual (M : VonNeumannAlgebra H)
    [TopologicalSpace.SeparableSpace H] : HasSeparablePredual M := by
  let : CompleteSpace (predual M) := by
    unfold predual
    infer_instance
  exact ⟨predual M, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(evaluationLinearIsometryEquiv M).symm⟩⟩

end Invariant233.ConcretePredual

end

end OAI
