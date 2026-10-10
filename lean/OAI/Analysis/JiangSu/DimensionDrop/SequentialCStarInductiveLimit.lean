import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI

section

noncomputable section
open Filter
open scoped ENNReal Topology CStarAlgebra

namespace SequentialCStar
variable (C : ℕ → Type*) [∀ n, CStarAlgebra (C n)] [∀ n, Nontrivial (C n)]
open TraceCone

namespace System
variable {C} (S : System C)

lemma stage_isometry (n : ℕ) : Isometry (S.stage n) :=
  AddMonoidHomClass.isometry_of_norm _ (S.stage_norm n)

@[simp] lemma inclusion_compatible {n m} (h : n≤ m) (a : C n) :
    S.inclusion m (S.map h a)=S.inclusion n a := Subtype.ext (S.stage_compatible h a)

end System
end SequentialCStar

end
end

end OAI
