import OAI.Analysis.Pureness.Completion.CompletedSharedTrace
import OAI.Analysis.Pureness.Completion.CompletedOrthogonalRanks
import OAI.Analysis.Pureness.Stabilization.MatrixAdditionAssoc

namespace OAI
open scoped CStarAlgebra
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma shared_rank_parity (τ : TracialState A) (r : Fin 2) (a : Positive (CuntzTrace.MatrixLimit A)) :
    completedRootRank τ (sharedMatrixEquiv (matrixParity r a.1)) =
      completedRootRank τ (sharedMatrixEquiv a.1) := by
  have h := congrArg (sharedExtendedTrace τ).cuntzRank (matrixParity_cuntzClass r a)
  simpa only [ExtendedTrace.cuntzRank_mk, sharedExtendedTrace_rank, Positive.map] using h

theorem shared_rank_block (τ : TracialState A) (a b : Positive (CuntzTrace.MatrixLimit A)) :
    (sharedExtendedTrace τ).rank (matrixBlockPositive a b) =
      (sharedExtendedTrace τ).rank a + (sharedExtendedTrace τ).rank b := by
  rw [sharedExtendedTrace_rank, sharedExtendedTrace_rank, sharedExtendedTrace_rank]
  change completedRootRank τ (sharedMatrixEquiv (matrixEven a.1 + matrixOdd b.1)) = _
  rw [map_add, completedRootRank_add_orthogonal τ _ _
    (map_nonneg sharedMatrixEquiv (map_nonneg matrixEven a.2))
    (map_nonneg sharedMatrixEquiv (map_nonneg matrixOdd b.2)) (by
      rw [← map_mul, matrixEven_mul_matrixOdd, map_zero])]
  have he := shared_rank_parity τ 0 a
  have ho := shared_rank_parity τ 1 b
  simpa [matrixParity] using congrArg₂ (· + ·) he ho

def sharedRankHom (τ : TracialState A) : CuntzTrace.CuntzClass (CuntzTrace.MatrixLimit A) →+ ℝ≥0∞ where
  toFun := (sharedExtendedTrace τ).cuntzRank
  map_zero' := by
    change (sharedExtendedTrace τ).rank Positive.zero = 0
    rw [sharedExtendedTrace_rank]
    change completedRootRank τ (sharedMatrixEquiv 0) = 0
    simp
  map_add' x y := by
    induction x using Quotient.inductionOn with | h a =>
    induction y using Quotient.inductionOn with | h b =>
    exact shared_rank_block τ a b

@[simp] theorem sharedRankHom_mk (τ : TracialState A) (a : Positive (CuntzTrace.MatrixLimit A)) :
    sharedRankHom τ (CuntzTrace.CuntzClass.mk a) = completedRootRank τ (sharedMatrixEquiv a.1) :=
  sharedExtendedTrace_rank τ a

theorem sharedRankHom_nsmul (τ : TracialState A) (n : ℕ)
    (x : CuntzTrace.CuntzClass (CuntzTrace.MatrixLimit A)) :
    sharedRankHom τ (n • x) = (n : ℝ≥0∞) * sharedRankHom τ x := by
  rw [map_nsmul, nsmul_eq_mul]
end CuntzPureness

end

end OAI
