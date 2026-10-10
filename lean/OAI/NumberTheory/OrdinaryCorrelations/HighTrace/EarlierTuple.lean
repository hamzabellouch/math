import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.PivotSummation
open Finset Classical

def earlierTuple {P : Type*} {n : ℕ} (x : Fin n → P) (i : Fin n) : Fin i.val → P :=
  fun j => x ⟨j.val,lt_trans j.isLt i.isLt⟩

lemma prefix_cons {P : Type*} {n : ℕ} (p : P) (x : Fin n → P) (i : Fin n) :
    earlierTuple (Fin.cons p x) i.succ = Fin.cons p (earlierTuple x i) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rfl
  · rfl

theorem triangular_product_sum {P : Type*} [Fintype P] (n : ℕ)
    (F : ∀ i : Fin n, (Fin i.val → P) → P → ℝ) (K : Fin n → ℝ)
    (hF : ∀ i pre p, 0 ≤ F i pre p)
    (hK : ∀ i, 0 ≤ K i)
    (hrow : ∀ i pre, ∑ p, F i pre p ≤ K i) :
    (∑ x : Fin n → P, ∏ i, F i (earlierTuple x i) (x i)) ≤ ∏ i, K i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he := (Fin.consEquiv (fun _ : Fin (n+1) => P)).sum_comp
      (fun x : Fin (n+1) → P => ∏ i, F i (earlierTuple x i) (x i))
    have hm : (∑ x : Fin (n+1) → P, ∏ i, F i (earlierTuple x i) (x i)) =
        ∑ p : P, F 0 (fun i => Fin.elim0 i) p *
          ∑ y : Fin n → P, ∏ i, F i.succ (Fin.cons p (earlierTuple y i)) (y i) := by
      rw [← he,Fintype.sum_prod_type]
      apply sum_congr rfl
      intro p hp
      rw [mul_sum]
      apply sum_congr rfl
      intro y hy
      change (∏ i, F i (earlierTuple (Fin.cons p y) i) ((Fin.cons p y : Fin (n+1) → P) i)) = _
      rw [Fin.prod_univ_succ]
      congr 1
      · congr 1
        funext i
        exact Fin.elim0 i
      · apply prod_congr rfl
        intro i hi
        rw [prefix_cons]
        rfl
    rw [hm,Fin.prod_univ_succ]
    calc
      _ ≤ ∑ p : P, F 0 (fun i => Fin.elim0 i) p * ∏ i : Fin n, K i.succ := by
        apply sum_le_sum
        intro p hp
        apply mul_le_mul_of_nonneg_left _ (hF _ _ _)
        apply ih (fun i pre q => F i.succ (Fin.cons p pre) q) (fun i => K i.succ)
        · exact fun i pre q => hF _ _ _
        · exact fun i => hK _
        · exact fun i pre => hrow _ _
      _ = (∑ p : P, F 0 (fun i => Fin.elim0 i) p) * ∏ i : Fin n, K i.succ := by
        rw [sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow _ _) (prod_nonneg (fun i _ => hK _))

end OrdinaryCorrelations.PivotSummation

end

end OAI
