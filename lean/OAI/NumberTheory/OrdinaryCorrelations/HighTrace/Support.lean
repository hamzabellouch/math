import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.TaggedPrimeGroups
variable {P : Type*} [Fintype P] [DecidableEq P]

def support {m : ℕ} (x : Fin m → P) : Finset P := univ.image x

def weight (W : P → ℝ) {m : ℕ} (x : Fin m → P) : ℝ := ∏ p ∈ support x, W p

omit [Fintype P] in
lemma weight_nonneg (W : P → ℝ) (hW : ∀ p, 0 ≤ W p) {m : ℕ} (x : Fin m → P) :
    0 ≤ weight W x := prod_nonneg (fun p _ => hW p)

omit [Fintype P] in
lemma support_cons {m : ℕ} (p : P) (x : Fin m → P) :
    support (Fin.cons p x) = insert p (support x) := by
  ext q
  simp only [support,mem_image,mem_univ,true_and,mem_insert]
  constructor
  · rintro ⟨i,hi⟩
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi; exact Or.inl hi.symm
    · intro hi; exact Or.inr ⟨j,hi⟩
  · rintro (rfl | ⟨j,hj⟩)
    · exact ⟨0,Fin.cons_zero _ _⟩
    · exact ⟨j.succ,by simpa only [Fin.cons_succ] using hj⟩

omit [Fintype P] in
lemma weight_cons (W : P → ℝ) {m : ℕ} (p : P) (x : Fin m → P) :
    weight W (Fin.cons p x) = (if p ∈ support x then 1 else W p) * weight W x := by
  unfold weight
  rw [support_cons]
  by_cases hp : p ∈ support x
  · rw [ite_eq_left hp,insert_eq_of_mem hp,one_mul]
  · rw [ite_eq_right hp,prod_insert hp]

lemma repeat_or_new (W : P → ℝ) (hW : ∀ p, 0 ≤ W p) {m : ℕ} (x : Fin m → P) :
    (∑ p : P, weight W (Fin.cons p x)) ≤
      ((m : ℝ) + ∑ p : P, W p) * weight W x := by
  simp_rw [weight_cons]
  rw [← sum_mul]
  apply mul_le_mul_of_nonneg_right _ (weight_nonneg W hW x)
  calc
    _ ≤ ∑ p : P, ((if p ∈ support x then (1 : ℝ) else 0) + W p) := by
      apply sum_le_sum
      intro p hp
      split_ifs <;> linarith [hW p]
    _ = ((support x).card : ℝ) + ∑ p : P, W p := by
      rw [sum_add_distrib]
      congr 1
      simp only [← sum_filter]
      simp
    _ ≤ _ := by
      have hcard : (support x).card ≤ m := by
        simpa only [support,card_univ,Fintype.card_fin] using card_image_le (s := univ) (f := x)
      have hr : ((support x).card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hcard
      linarith

theorem grouped_prime_sum (W : P → ℝ) (hW : ∀ p, 0 ≤ W p) (m : ℕ) :
    (∑ x : Fin m → P, weight W x) ≤ ∏ i ∈ range m, ((i : ℝ) + ∑ p : P, W p) := by
  induction m with
  | zero => simp [weight,support]
  | succ m ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (m+1) => P)).sum_comp (weight W),
      Fintype.sum_prod_type,prod_range_succ]
    change (∑ p : P, ∑ x : Fin m → P, weight W (Fin.cons p x)) ≤ _
    rw [sum_comm]
    calc
      _ ≤ ∑ x : Fin m → P, ((m : ℝ) + ∑ p : P, W p) * weight W x :=
        sum_le_sum (fun x hx => repeat_or_new W hW x)
      _ = ((m : ℝ) + ∑ p : P, W p) * ∑ x : Fin m → P, weight W x := mul_sum .. |>.symm
      _ ≤ ((m : ℝ) + ∑ p : P, W p) * ∏ i ∈ range m, ((i : ℝ) + ∑ p : P, W p) :=
        mul_le_mul_of_nonneg_left ih (add_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun p _ => hW p)))
      _ = _ := mul_comm _ _

end OrdinaryCorrelations.TaggedPrimeGroups

end

end OAI
