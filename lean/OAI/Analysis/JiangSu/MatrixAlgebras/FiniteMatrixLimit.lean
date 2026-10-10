import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI

section

namespace Pureness
variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma finiteMatrixInclude_injective (k : ℕ) : Function.Injective (finiteMatrixInclude A k) :=
  (AddMonoidHomClass.isometry_of_norm _ (finiteMatrixInclude_norm A k)).injective

lemma finiteMatrixInclude_isometry (k : ℕ) : Isometry (finiteMatrixInclude A k) :=
  AddMonoidHomClass.isometry_of_norm _ (finiteMatrixInclude_norm A k)

end Pureness
end

end OAI
