import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI


noncomputable section
namespace Pureness
open Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[simp] theorem sharedMatrixEquiv_stage (k : ℕ) (a : MatrixStage A k) :
    sharedMatrixEquiv (TraceCone.matrixLimitStage k a) = completedMatrixInclude A k a :=
  sharedMatrixToCompletion_stage k a

end Pureness
end

end OAI
