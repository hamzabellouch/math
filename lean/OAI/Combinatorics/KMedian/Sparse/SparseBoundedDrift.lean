import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseHistories

namespace OAI

section
section
namespace MetricKMedian.SparseHistories
open Finset
variable {α : Type}

theorem accumulated_drift_up_to (κ : ℕ → α → SparseIntegerLaw α) (a : α)
    (V : ℕ → History α → ℝ) (E : ℕ → ℝ) (T : ℕ)
    (hstep : ∀ t < T, ∀ i : Fin (tree κ a t).length,
      (κ t (tree κ a t).states[i.val].1).expectation
        (fun s => V (t+1) (extend (tree κ a t).states[i.val] s)) ≤
          V t (tree κ a t).states[i.val]+E t) :
    (tree κ a T).expectation (V T) ≤ V 0 (a,[])+∑ t∈range T,E t := by
  induction T with
  | zero => simp only [tree,SparseIntegerLaw.expectation_dirac,range_zero,sum_empty,add_zero,le_refl]
  | succ t ih =>
    have hi := ih (fun r hr => hstep r (hr.trans (Nat.lt_succ_self t)))
    rw [expectation_step]
    have hs := SparseIntegerLaw.expectation_mono (tree κ a t)
      (fun z => (κ t z.1).expectation (fun s => V (t+1) (extend z s)))
      (fun z => V t z+E t) (hstep t (Nat.lt_succ_self t))
    rw [SparseIntegerLaw.expectation_add,SparseIntegerLaw.expectation_const] at hs
    exact hs.trans (by rw [sum_range_succ]; linarith only [hi])

end MetricKMedian.SparseHistories
end
end

end OAI
