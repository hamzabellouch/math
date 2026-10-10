import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.SharedMatrixBridge
import OAI.Analysis.JiangSu.TraceCone.Pullback
import OAI.Analysis.JiangSu.CStarAlgebras.CompletedRootRank

namespace OAI


open scoped CStarAlgebra

noncomputable section
namespace Pureness
open Filter Topology TraceCone
open scoped ENNReal NNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem completedExtendedTrace_rank (τ : TracialState A) (a : Positive (CornerCompletion A)) :
    (completedExtendedTrace τ).rank a = completedRootRank τ a.1 := by
  change liminf (fun n : ℕ => completedDiagonalWeight τ
    (CFC.nnrpow a.1 (1 / ((n : ℝ≥0) + 1)))) atTop = _
  simpa only [one_div] using (completed_root_trace_tendsto_rank τ a.1 a.2).liminf_eq

theorem sharedExtendedTrace_stage (τ : TracialState A) (k : ℕ) (a : Positive (MatrixStage A k)) :
    sharedExtendedTrace τ (Positive.map (TraceCone.matrixLimitStage k) a) =
      ENNReal.ofReal (matrixTrace τ a.1).re := by
  change completedDiagonalWeight τ (sharedMatrixEquiv (TraceCone.matrixLimitStage k a.1)) = _
  rw [sharedMatrixEquiv_stage]
  exact completedDiagonalWeight_include τ k a.1 a.2

theorem sharedExtendedTrace_rank (τ : TracialState A) (a : Positive (TraceCone.MatrixLimit A)) :
    (sharedExtendedTrace τ).rank a = completedRootRank τ (sharedMatrixEquiv a.1) := by
  rw [sharedExtendedTrace, ExtendedTrace.rank_pullback, completedExtendedTrace_rank]
  rfl

end Pureness

end

end OAI
