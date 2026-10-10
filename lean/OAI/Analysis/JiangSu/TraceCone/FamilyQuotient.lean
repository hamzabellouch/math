import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI


noncomputable section
open scoped ENNReal Topology
open Filter Metric

namespace TraceCone
variable (A : ℕ → Type*) [∀ n, NonUnitalCStarAlgebra (A n)]

namespace FamilyQuotient
open BoundedFamilies

variable {A}

@[simp] lemma mk_add (x y : BoundedFamilies A) : mk (x+y) = mk x+mk y :=
  Submodule.Quotient.mk_add (vanishing (A := A))

@[simp] lemma mk_sub (x y : BoundedFamilies A) : mk (x-y) = mk x-mk y :=
  Submodule.Quotient.mk_sub (vanishing (A := A))
@[simp] lemma mk_smul (c : ℂ) (x : BoundedFamilies A) : mk (c • x) = c • mk x :=
  Submodule.Quotient.mk_smul (vanishing (A := A)) c x
@[simp] lemma mk_zero : mk (0 : BoundedFamilies A) = 0 :=
  Submodule.Quotient.mk_zero (vanishing (A := A))

end FamilyQuotient
end TraceCone
end

end OAI
