import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseHistories

namespace OAI

section
section
namespace MetricKMedian.SparseHistories
open Finset
variable {α : Type}

theorem accumulated_drift (κ : ℕ → α → SparseIntegerLaw α) (a : α)
    (V : ℕ → History α → ℝ) (E : ℕ → ℝ)
    (hstep : ∀ t i : ℕ, ∀ hi : i < (tree κ a t).length,
      (κ t (tree κ a t).states[i].1).expectation
        (fun s => V (t+1) (extend (tree κ a t).states[i] s)) ≤
          V t (tree κ a t).states[i]+E t) (T : ℕ) :
    (tree κ a T).expectation (V T) ≤ V 0 (a,[])+∑ t∈range T,E t := by
  induction T with
  | zero => simp only [tree,SparseIntegerLaw.expectation_dirac,range_zero,sum_empty,add_zero,le_refl]
  | succ t ih =>
    rw [expectation_step]
    have hs := SparseIntegerLaw.expectation_mono (tree κ a t)
      (fun z => (κ t z.1).expectation (fun s => V (t+1) (extend z s)))
      (fun z => V t z+E t) (fun i => hstep t i.val i.isLt)
    rw [SparseIntegerLaw.expectation_add,SparseIntegerLaw.expectation_const] at hs
    exact hs.trans (by rw [sum_range_succ]; linarith only [ih])

theorem survival (κ : ℕ → α → SparseIntegerLaw α) (a : α)
    (y : α → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hstep : ∀ t i : ℕ, ∀ hi : i < (tree κ a t).length,
      (κ t (tree κ a t).states[i].1).expectation y ≤ r*y (tree κ a t).states[i].1)
    (T : ℕ) :
    (tree κ a T).expectation (fun h => y h.1) ≤ r^T*y a := by
  induction T with
  | zero => simp only [tree,SparseIntegerLaw.expectation_dirac,pow_zero,one_mul,le_refl]
  | succ t ih =>
    rw [expectation_step]
    have hs := SparseIntegerLaw.expectation_mono (tree κ a t)
      (fun z => (κ t z.1).expectation y)
      (fun z => r*y z.1) (fun i => hstep t i.val i.isLt)
    have he : (tree κ a t).expectation (fun z => r*y z.1)=
        r*(tree κ a t).expectation (fun z => y z.1) := FiniteLaw.expect_mul _ _ _
    rw [he] at hs
    exact hs.trans ((mul_le_mul_of_nonneg_left ih hr).trans_eq (by rw [pow_succ]; ring))

theorem count_tail (κ : ℕ → α → SparseIntegerLaw α) (a : α)
    (size : α → ℝ) (c ρ : ℝ)
    (hstep : ∀ t i : ℕ, ∀ hi : i < (tree κ a t).length,
      (κ t (tree κ a t).states[i].1).expectation
        (fun s => if size (tree κ a t).states[i].1+c < size s then 1 else 0) ≤ ρ)
    (T : ℕ) :
    (tree κ a T).expectation (fun h => if size a+(T:ℝ)*c < size h.1 then 1 else 0) ≤
      (T:ℝ)*ρ := by
  classical
  induction T with
  | zero => simp only [tree,SparseIntegerLaw.expectation_dirac,Nat.cast_zero,zero_mul,add_zero,
      lt_self_iff_false,ite_false,le_refl]
  | succ t ih =>
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
      exact he.trans (add_le_add le_rfl (hstep t i.val i.isLt))
    have he := SparseIntegerLaw.expectation_mono (tree κ a t)
      (fun z => (κ t z.1).expectation
        (fun s => if size a+((t+1:ℕ):ℝ)*c < size s then 1 else 0))
      (fun z => (if size a+(t:ℝ)*c < size z.1 then 1 else 0)+ρ) hs
    rw [SparseIntegerLaw.expectation_add,SparseIntegerLaw.expectation_const] at he
    exact he.trans (by push_cast; nlinarith only [ih])

end MetricKMedian.SparseHistories
end
end

end OAI
