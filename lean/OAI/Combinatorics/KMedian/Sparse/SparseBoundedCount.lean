import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseHistories

namespace OAI

section
section
namespace MetricKMedian.SparseHistories
open Finset
variable {α : Type}

theorem count_tail_up_to (κ : ℕ → α → SparseIntegerLaw α) (a : α)
    (size : α → ℝ) (c ρ : ℝ)
    (T : ℕ)
    (hstep : ∀ t < T, ∀ i : ℕ, ∀ hi : i < (tree κ a t).length,
      (κ t (tree κ a t).states[i].1).expectation
        (fun s => if size (tree κ a t).states[i].1+c < size s then 1 else 0) ≤ ρ)
    :
    (tree κ a T).expectation (fun h => if size a+(T:ℝ)*c < size h.1 then 1 else 0) ≤
      (T:ℝ)*ρ := by
  classical
  induction T with
  | zero => simp only [tree,SparseIntegerLaw.expectation_dirac,Nat.cast_zero,zero_mul,add_zero,
      lt_self_iff_false,ite_false,le_refl]
  | succ t ih =>
    have hi := ih (fun r hr => hstep r (hr.trans (Nat.lt_succ_self t)))
    rw [expectation_step]
    have hs : ∀ i : Fin (tree κ a t).length,
        (κ t (tree κ a t).states[i.val].1).expectation
          (fun s => if size a+((t+1:ℕ):ℝ)*c < size s then 1 else 0) ≤
        (if size a+(t:ℝ)*c < size (tree κ a t).states[i.val].1 then 1 else 0)+ρ := by
      intro i
      let z := (tree κ a t).states[i.val].1
      have hp : ∀ s, (if size a+((t+1:ℕ):ℝ)*c < size s then (1:ℝ) else 0) ≤
          (if size a+(t:ℝ)*c < size z then 1 else 0)+
            (if size z+c < size s then 1 else 0) := by
        intro s
        split_ifs <;> push_cast at * <;> linarith
      have he := SparseIntegerLaw.expectation_mono (κ t z)
        (fun s => if size a+((t+1:ℕ):ℝ)*c < size s then 1 else 0)
        (fun s => (if size a+(t:ℝ)*c < size z then 1 else 0)+
          (if size z+c < size s then 1 else 0)) (fun b => hp _)
      rw [SparseIntegerLaw.expectation_add,SparseIntegerLaw.expectation_const] at he
      exact he.trans (add_le_add le_rfl (hstep t (Nat.lt_succ_self t) i.val i.isLt))
    have he := SparseIntegerLaw.expectation_mono (tree κ a t)
      (fun z => (κ t z.1).expectation
        (fun s => if size a+((t+1:ℕ):ℝ)*c < size s then 1 else 0))
      (fun z => (if size a+(t:ℝ)*c < size z.1 then 1 else 0)+ρ) hs
    rw [SparseIntegerLaw.expectation_add,SparseIntegerLaw.expectation_const] at he
    exact he.trans (by push_cast; nlinarith only [hi])

end MetricKMedian.SparseHistories
end
end

end OAI
