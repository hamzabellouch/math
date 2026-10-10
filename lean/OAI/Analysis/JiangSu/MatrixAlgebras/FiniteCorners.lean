import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI

section

namespace Pureness
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {k l m : ℕ}

lemma corner_isometry (h : k ≤ l) : Isometry (cornerHom (A := A) h) :=
  NonUnitalStarAlgHom.isometry _ (corner_injective h)

lemma corner_nonneg (h : k ≤ l) (a : CStarMatrix (Fin k) (Fin k) A) (ha : 0 ≤ a) :
    0 ≤ corner h a := by
  exact map_nonneg (cornerHom h) ha

end Pureness
end

end OAI
