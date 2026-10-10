import Mathlib
import OAI.Analysis.FreeWords.CutAlgebra
import OAI.Analysis.FreeWords.TupleCombinatorics

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators

noncomputable section

variable {R α : Type*} [Semiring R] [Fintype α] [DecidableEq α]

omit [Semiring R] in
theorem ofFn_take_add {m n : ℕ} (f : Fin (m+n) → R) :
    (List.ofFn f).take m = List.ofFn (fun i => f (i.castAdd n)) := by
  rw [List.ofFn_add]
  have he : (fun i : Fin m => f (Fin.castLE (Nat.le_add_right m n) i)) =
      (fun i : Fin m => f (i.castAdd n)) := by
    funext i
    congr 1
  rw [he]
  simpa only [List.length_ofFn] using
    (List.take_left (l₁ := List.ofFn (fun i : Fin m => f (i.castAdd n)))
      (l₂ := List.ofFn (fun i : Fin n => f (Fin.natAdd m i))))

omit [Semiring R] in
theorem ofFn_drop_add {m n : ℕ} (f : Fin (m+n) → R) :
    (List.ofFn f).drop m = List.ofFn (fun i => f (Fin.natAdd m i)) := by
  rw [List.ofFn_add]
  have he : (fun i : Fin m => f (Fin.castLE (Nat.le_add_right m n) i)) =
      (fun i : Fin m => f (i.castAdd n)) := by
    funext i
    congr 1
  rw [he]
  simpa only [List.length_ofFn] using
    (List.drop_left (l₁ := List.ofFn (fun i : Fin m => f (i.castAdd n)))
      (l₂ := List.ofFn (fun i : Fin n => f (Fin.natAdd m i))))

omit [Fintype α] [DecidableEq α] in
theorem tupleLabels_append {m n : ℕ} (a : Fin m → α) (b : Fin n → α) :
    tupleLabels (Fin.append a b) = tupleLabels a + tupleLabels b := by
  simp only [tupleLabels, List.ofFn_fin_append, Multiset.coe_add]

def tupleProduct {n : ℕ} (C : Fin n → α → R) (a : Fin n → α) : R :=
  (List.ofFn (fun j => C j (a j))).prod

theorem sum_noPresCut (p q : ℕ) (W : Multiset α)
    (C D : Fin (q+p) → α → R) :
    (∑ a : Fin (q+p) → α, if tupleLabels a = W then
      noPresCut (fun j => C j (a j)) (fun j => D j (a j)) q else 0) =
    ∑ a : Fin q → α, ∑ b : Fin p → α,
      tupleProduct (fun j => C (j.castAdd p)) a *
        (if tupleLabels a + tupleLabels b = W then 1 else 0) *
          tupleProduct (fun j => D (Fin.natAdd q j)) b := by
  rw [← Equiv.sum_comp (Fin.appendEquiv q p)]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  change (if tupleLabels (Fin.append a b) = W then
    noPresCut (fun j => C j ((Fin.append a b) j))
      (fun j => D j ((Fin.append a b) j)) q else 0) = _
  simp only [tupleLabels_append, noPresCut,
    ofFn_take_add, ofFn_drop_add, Fin.append_left, Fin.append_right, tupleProduct]
  split_ifs <;> simp

theorem sum_presCut (p q : ℕ) (W : Multiset α)
    (C D K : Fin (q+(p+1)) → α → R) :
    (∑ a : Fin (q+(p+1)) → α, if tupleLabels a = W then
      presCut (fun j => C j (a j)) (fun j => D j (a j)) (fun j => K j (a j))
        (Fin.natAdd q 0) else 0) =
    ∑ a : Fin q → α, ∑ b : Fin p → α,
      tupleProduct (fun j => C (j.castAdd (p+1))) a *
        (∑ c : α, if tupleLabels a + {c} + tupleLabels b = W then
          K (Fin.natAdd q 0) c else 0) *
          tupleProduct (fun j => D (Fin.natAdd q j.succ)) b := by
  rw [← Equiv.sum_comp (Fin.appendEquiv q (p+1))]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (p+1) => α))]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  change (if tupleLabels (Fin.append a (Fin.cons c b)) = W then
    presCut (fun j => C j ((Fin.append a (Fin.cons c b)) j))
      (fun j => D j ((Fin.append a (Fin.cons c b)) j))
      (fun j => K j ((Fin.append a (Fin.cons c b)) j)) (Fin.natAdd q 0) else 0) = _
  have he : presCut (fun j => C j ((Fin.append a (Fin.cons c b)) j))
      (fun j => D j ((Fin.append a (Fin.cons c b)) j))
      (fun j => K j ((Fin.append a (Fin.cons c b)) j)) (Fin.natAdd q 0) =
      tupleProduct (fun j => C (j.castAdd (p+1))) a * K (Fin.natAdd q 0) c *
      tupleProduct (fun j => D (Fin.natAdd q j.succ)) b := by
    dsimp only [presCut]
    rw [Fin.append_right, Fin.cons_zero]
    change ((List.ofFn (fun j => C j ((Fin.append a (Fin.cons c b)) j))).take q).prod *
      K (Fin.natAdd q 0) c *
      ((List.ofFn (fun j => D j ((Fin.append a (Fin.cons c b)) j))).drop (q+1)).prod = _
    have hd : (List.ofFn (fun j => D j ((Fin.append a (Fin.cons c b)) j))).drop (q+1) =
        List.ofFn (fun j => D (Fin.natAdd q j.succ) (b j)) := by
      rw [← List.drop_drop, ofFn_drop_add, List.ofFn_succ]
      simp only [Fin.append_right, List.drop_succ_cons, List.drop_zero, Fin.cons_succ]
    rw [hd, ofFn_take_add]
    simp only [Fin.append_left, tupleProduct]
  rw [he, tupleLabels_append, tupleLabels_cons, ← add_assoc]
  split_ifs <;> simp

end

end KKFreeWords
end

end OAI
