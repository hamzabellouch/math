import Mathlib.LinearAlgebra.Matrix.Rank
import OAI.Computability.PerfectCompleteness.Foundations.ManyGoodRowsLemmas

namespace OAI

section

namespace PerfectCompleteness.ProductEvaluationRank

open ProductEvaluation MixedSupport CanonicalKeys

noncomputable section

variable {n : Nat} {C Z : Type*} {Row : C → Type*}

theorem extension_productMatrix_rank_le_one
    (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
    (rows : (c : C) → Row c → Assignment slots → F2)
    (other : Assignment slots → Z) (hone : (1 : Assignment slots → F2) ∈ H)
    (hproducts : ∀ c u v, rows c u * rows c v ∈ H)
    (P : Label slots (displayedJoint rows other)) (z : Module.Dual F2 H)
    (hz : z.comp (productSpan H rows hone hproducts).subtype =
      labelFunctional slots H rows other hone hproducts P)
    (c : C) [Fintype (Row c)] :
    Matrix.rank (fun u v : Row c => z ⟨rows c u * rows c v, hproducts c u v⟩) ≤ 1 := by
  rw [extension_productMatrix slots H rows other hone hproducts P z hz c]
  exact Matrix.rank_vecMulVec_le (restoredRows slots rows other P c)
    (restoredRows slots rows other P c)

end
end PerfectCompleteness.ProductEvaluationRank

end

end OAI
