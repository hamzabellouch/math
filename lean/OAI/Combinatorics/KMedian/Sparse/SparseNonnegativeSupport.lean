import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseIntegerLaw

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem zero_nonnegative (μ : SparseIntegerLaw α) (f : α → ℚ)
    (hf : ∀ i : Fin μ.length, 0 ≤ f μ.states[i.val])
    (hz : μ.moment f=0) (a : Fin μ.length)
    (ha : 0 < μ.law.rational.weight a) : f μ.states[a.val]=0 := by
  have hh := single_le_sum (s := univ)
    (f := fun i : Fin μ.length => μ.law.rational.weight i*f μ.states[i.val])
    (fun i _ => mul_nonneg (μ.law.rational.nonneg i) (hf i)) (mem_univ a)
  change _ ≤ μ.moment f at hh
  rw [hz] at hh
  have hn := hf a
  nlinarith only [hh,ha,hn]

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
