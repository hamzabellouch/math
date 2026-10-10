import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI

section

noncomputable section
namespace Pureness
open Filter Topology
open scoped ComplexOrder

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma completedCornerCut_cuntz (k : ℕ) (a : CornerCompletion A) :
    CuntzSubequiv (completedCornerCut A k a) a := by
  simpa only [completedCornerCut, completedProjection_star] using
    cuntzSubequiv_conjugate a (completedProjection A k)

end Pureness
end
end

end OAI
