import OAI.Analysis.Pureness.Divisibility.ContinuousCutTraceEnvelope
import OAI.Analysis.Pureness.Completion.CompletedUniformComparison
import OAI.Analysis.Pureness.Completion.CompletedSharedTrace

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_completedFinite_trace_envelope (k : ℕ) (M : Positive (FinMatrix A k))
    (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ F : TracialState A → ℝ≥0∞, Continuous F ∧ ∀ τ,
      completedRootRank τ (completedMatrixInclude A k (Positive.cut δ M).1) ≤ F τ ∧
      F τ ≤ completedRootRank τ (completedMatrixInclude A k M.1) := by
  let F : TracialState A → ℝ≥0∞ := fun τ =>
    ENNReal.ofReal (matrixTrace τ (positiveRamp M δ).1).re
  refine ⟨F, ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp
    (continuous_matrixTrace_eval _)), fun τ => ?_⟩
  have h := trace_ramp_envelope ((completedExtendedTrace τ).pullback (completedMatrixInclude A k))
    M δ hδ
  have hr (N : Positive (FinMatrix A k)) :
      ((completedExtendedTrace τ).pullback (completedMatrixInclude A k)).rank N=
        completedRootRank τ (completedMatrixInclude A k N.1) := by
    rw [ExtendedTrace.rank_pullback,completedExtendedTrace_rank]
    rfl
  have hf : ((completedExtendedTrace τ).pullback (completedMatrixInclude A k)) (positiveRamp M δ)=F τ :=
    completedDiagonalWeight_include τ k (positiveRamp M δ).1 (positiveRamp M δ).2
  rwa [hr,hr,hf] at h
end CuntzPureness

end

end OAI
