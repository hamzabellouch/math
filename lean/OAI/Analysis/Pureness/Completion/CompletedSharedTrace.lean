import OAI.Analysis.Pureness.Completion.CompletedRootRank
import OAI.Analysis.Pureness.Stabilization.RankFunctorial
import OAI.Analysis.Pureness.Stabilization.MatrixPositive
import OAI.Analysis.Pureness.Completion.SharedMatrixBridge

namespace OAI
open scoped CStarAlgebra
noncomputable section
namespace CuntzPureness
open Filter Topology CuntzTrace
open scoped ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def completedExtendedTrace (τ : TracialState A) : ExtendedTrace (CornerCompletion A) where
  toFun a := completedDiagonalWeight τ a.1
  map_zero := completedDiagonalWeight_zero τ
  map_add a b := completedDiagonalWeight_add τ a.1 b.1 a.2 b.2
  map_smul r a := by
    simpa only [Positive.smul, ENNReal.ofReal_coe_nnreal] using completedDiagonalWeight_smul τ (r : ℝ) r.2 a.1
  tracial := completedDiagonalWeight_tracial τ
  lowerSemicontinuous := by
    change LowerSemicontinuous (fun a : Positive (CornerCompletion A) =>
      ⨆ k, completedTraceValue τ k a.1)
    exact lowerSemicontinuous_iSup fun k =>
      ((completedTraceValue_continuous τ k).comp continuous_subtype_val).lowerSemicontinuous

theorem completedExtendedTrace_rank (τ : TracialState A) (a : Positive (CornerCompletion A)) :
    (completedExtendedTrace τ).rank a = completedRootRank τ a.1 := by
  change liminf (fun n : ℕ => completedDiagonalWeight τ
    (CFC.nnrpow a.1 (1 / ((n : ℝ≥0) + 1)))) atTop = _
  simpa only [one_div] using (completed_root_trace_tendsto_rank τ a.1 a.2).liminf_eq

def sharedExtendedTrace (τ : TracialState A) : ExtendedTrace (CuntzTrace.MatrixLimit A) :=
  (completedExtendedTrace τ).pullback sharedMatrixEquiv.toNonUnitalStarAlgHom

theorem sharedExtendedTrace_stage (τ : TracialState A) (k : ℕ) (a : Positive (MatrixStage A k)) :
    sharedExtendedTrace τ (Positive.map (CuntzTrace.matrixLimitStage k) a) =
      ENNReal.ofReal (matrixTrace τ a.1).re := by
  change completedDiagonalWeight τ (sharedMatrixEquiv (CuntzTrace.matrixLimitStage k a.1)) = _
  rw [sharedMatrixEquiv_stage]
  exact completedDiagonalWeight_include τ k a.1 a.2

theorem sharedExtendedTrace_rank (τ : TracialState A) (a : Positive (CuntzTrace.MatrixLimit A)) :
    (sharedExtendedTrace τ).rank a = completedRootRank τ (sharedMatrixEquiv a.1) := by
  rw [sharedExtendedTrace, ExtendedTrace.rank_pullback, completedExtendedTrace_rank]
  rfl
end CuntzPureness

end

end OAI
