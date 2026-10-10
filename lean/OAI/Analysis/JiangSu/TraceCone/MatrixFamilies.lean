import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI


noncomputable section
open scoped ENNReal Topology CStarAlgebra
open Filter

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma matrixStage_isometry (n : ℕ) : Isometry (matrixStage (A := A) n) :=
  AddMonoidHomClass.isometry_of_norm (matrixStage (A := A) n) (matrixStage_norm n)

end TraceCone
end

end OAI
