import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseHistories

namespace OAI

section
section
namespace MetricKMedian.SparseHistories
open Finset
variable {α : Type}

theorem history_contraction (κ : ℕ → α → SparseIntegerLaw α) (a : α)
    (V : ℕ → History α → ℝ) (r : ℝ) (hr : 0 ≤ r) (T : ℕ)
    (hstep : ∀ t < T, ∀ i : Fin (tree κ a t).length,
      (κ t (tree κ a t).states[i.val].1).expectation
        (fun s => V (t+1) (extend (tree κ a t).states[i.val] s)) ≤
          r*V t (tree κ a t).states[i.val]) :
    (tree κ a T).expectation (V T) ≤ r^T*V 0 (a,[]) := by
  induction T with
  | zero => simp only [tree,SparseIntegerLaw.expectation_dirac,pow_zero,one_mul,le_refl]
  | succ t ih =>
    have hi := ih (fun u hu => hstep u (hu.trans (Nat.lt_succ_self t)))
    rw [expectation_step]
    have hs := SparseIntegerLaw.expectation_mono (tree κ a t)
      (fun z => (κ t z.1).expectation (fun s => V (t+1) (extend z s)))
      (fun z => r*V t z) (hstep t (Nat.lt_succ_self t))
    have he : (tree κ a t).expectation (fun z => r*V t z)=
        r*(tree κ a t).expectation (V t) := FiniteLaw.expect_mul _ _ _
    rw [he] at hs
    exact hs.trans ((mul_le_mul_of_nonneg_left hi hr).trans_eq (by rw [pow_succ]; ring))

end MetricKMedian.SparseHistories
end
end

end OAI
