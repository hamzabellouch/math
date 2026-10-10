import OAI.Analysis.Pureness.AlmostDivisibility
import OAI.Analysis.Pureness.Operators.FaithfulHilbertChoice
import OAI.Analysis.Pureness.Tensor.SpatialTraceAgreement

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped CStarAlgebra
variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (ρ : FaithfulHilbertRepresentation A)

def manuscriptStabilizationEquiv :=
  CuntzComparison.spatialEquiv ρ.hom.toNonUnitalStarAlgHom ρ.injective

lemma manuscriptStabilizationEquiv_stage (n : ℕ) (M : FinMatrix A n) :
    manuscriptStabilizationEquiv A ρ (matrixLimitStage n M)=
      CuntzComparison.spatialStage ρ.hom.toNonUnitalStarAlgHom n M := rfl

theorem manuscript_has_spatial_model :
    ∃ ρ : FaithfulHilbertRepresentation A, ∀ (n : ℕ) (M : FinMatrix A n),
      manuscriptStabilizationEquiv A ρ (matrixLimitStage n M)=
        CuntzComparison.spatialStage ρ.hom.toNonUnitalStarAlgHom n M :=
  (nonempty_faithfulHilbertRepresentation A).elim (fun σ => ⟨σ,fun _ _ => rfl⟩)
end CuntzPureness

end

end OAI
