import OAI.Analysis.Pureness.Divisibility.NuclearFiniteComparison
import OAI.Analysis.Pureness.Completion.CompletedUniformComparison

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped ENNReal
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

theorem nuclear_completedFiniteComparison (hsimple : TopologicallySimple A)
    (hA : IsNuclear.{u,0} A)
    (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
      (k+1) • u ≤ k • v → u ≤ v)
    (k l : ℕ) (M : Positive (FinMatrix A k)) (N : Positive (FinMatrix A l))
    (hN : N.1 ≠ 0)
    (hgap : ∀ τ : TracialState A,
      completedRootRank τ (completedMatrixInclude A k M.1) <
        completedRootRank τ (completedMatrixInclude A l N.1)) :
    CuntzSubequiv (completedMatrixInclude A k M.1) (completedMatrixInclude A l N.1) := by
  let L := max k l
  let M' := Positive.map (cornerHom (A := A) (le_max_left k l)) M
  let N' := Positive.map (cornerHom (A := A) (le_max_right k l)) N
  have hN' : N'.1 ≠ 0 := by
    intro hz
    apply hN
    exact (corner_isometry (A := A) (le_max_right k l)).injective
      (hz.trans (map_zero (cornerHom (A := A) (le_max_right k l))).symm)
  have h := nuclear_finiteComparison_of_tracialRanks hsimple hA hAU L M' N' hN' (fun τ => by
    rw [sharedExtendedTrace_rank,sharedExtendedTrace_rank]
    change completedRootRank τ (sharedMatrixEquiv (matrixLimitStage L M'.1)) <
      completedRootRank τ (sharedMatrixEquiv (matrixLimitStage L N'.1))
    rw [sharedMatrixEquiv_stage,sharedMatrixEquiv_stage]
    change completedRootRank τ (completedMatrixInclude A L (corner (le_max_left k l) M.1)) <
      completedRootRank τ (completedMatrixInclude A L (corner (le_max_right k l) N.1))
    simpa only [completedMatrixInclude_corner] using hgap τ)
  have hi := (cuntzSubequiv_completedMatrixInclude_iff A L M'.1 N'.1).mpr h
  change CuntzSubequiv (completedMatrixInclude A L (corner (le_max_left k l) M.1))
    (completedMatrixInclude A L (corner (le_max_right k l) N.1)) at hi
  simpa only [completedMatrixInclude_corner] using hi
end CuntzPureness

end

end OAI
