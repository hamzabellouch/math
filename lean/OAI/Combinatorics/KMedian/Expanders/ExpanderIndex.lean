import Mathlib
import OAI.Combinatorics.KMedian.Expanders.ExpanderFamily

namespace OAI

section Inline_PCPExpanderIndex
namespace MetricKMedian.PCP.ExpanderFamily
open scoped Classical

noncomputable def vertexEquiv : (n : ℕ) → Vertex n ≃ Fin ((Fintype.card Branch)^n)
  | 0 => (Equiv.ofUnique Unit (Fin 1)).trans (finCongr (pow_zero (Fintype.card Branch)).symm)
  | n+1 => ((vertexEquiv n).prodCongr (Fintype.equivFin Branch)).trans
      (finProdFinEquiv.trans (finCongr (pow_succ _ _).symm))
lemma vertexEquiv_succ (n : ℕ) (v : Vertex n) (b : Branch) :
    (vertexEquiv (n+1) (v,b)).val=(vertexEquiv n v).val*Fintype.card Branch+(Fintype.equivFin Branch b).val := by
  change (Fintype.equivFin Branch b).val+Fintype.card Branch*(vertexEquiv n v).val=_
  simp only [Nat.mul_comm, Nat.add_comm]
end MetricKMedian.PCP.ExpanderFamily

end Inline_PCPExpanderIndex

end OAI
