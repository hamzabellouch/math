import Mathlib

namespace OAI

/-!
# Exact local factorial sums for the companion's initial multipliers

These are the four brackets in the manuscript's exact initialization
formula. The full-pair case reduces to an explicitly evaluated quadratic
sum, so the rational initializer uses no factorial evaluation oracle.
-/

namespace ContingencyTables.InitializationBrackets

open scoped BigOperators
open Nat

noncomputable def bracket (b u v : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (b-u-v+1),
    ((b-u-v).choose k:ℝ)*((k+v)!:ℝ)*((b-u-v-k+v)!:ℝ))/(b !:ℝ)

private lemma choose_factorial (n k : ℕ) (hk : k≤n) :
    (n.choose k:ℝ)*(k !:ℝ)*((n-k)!:ℝ)=(n !:ℝ) := by
  exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk

private lemma shifted_choose_factorial (n k : ℕ) (hk : k≤n) :
    (n.choose k:ℝ)*((k+1)!:ℝ)*((n-k+1)!:ℝ)=
      (n !:ℝ)*((k:ℝ)+1)*((n-k:ℕ)+1:ℝ) := by
  rw [Nat.factorial_succ,Nat.factorial_succ]
  push_cast
  calc
    _ = ((n.choose k:ℝ)*(k !:ℝ)*((n-k)!:ℝ))*((k:ℝ)+1)*((n-k:ℕ)+1:ℝ) := by ring
    _ = _ := by rw [choose_factorial n k hk]

private lemma linear_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), ((k:ℝ)+1))=((n:ℝ)+1)*((n:ℝ)+2)/2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    push_cast
    ring

private lemma quadratic_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), ((k:ℝ)+1)*((n-k:ℕ)+1:ℝ))=
      ((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)/6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hterms :
        (∑ k ∈ Finset.range (n+1), ((k:ℝ)+1)*((n+1-k:ℕ)+1:ℝ))=
        (∑ k ∈ Finset.range (n+1), ((k:ℝ)+1)*((n-k:ℕ)+1:ℝ))+
          ∑ k ∈ Finset.range (n+1), ((k:ℝ)+1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have he : n+1-k=(n-k)+1 := by have := Finset.mem_range.mp hk; omega
      rw [he]
      push_cast
      ring
    rw [hterms,ih,linear_sum]
    simp only [Nat.sub_self,Nat.cast_zero,zero_add]
    push_cast
    ring

private lemma unshifted_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*(k !:ℝ)*((n-k)!:ℝ))=
      ((n:ℝ)+1)*(n !:ℝ) := by
  calc
    _ = ∑ _k ∈ Finset.range (n+1), (n !:ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact choose_factorial n k (by have := Finset.mem_range.mp hk; omega)
    _ = _ := by simp

private lemma shifted_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*((k+1)!:ℝ)*((n-k+1)!:ℝ))=
      (n !:ℝ)*(((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)/6) := by
  calc
    _ = ∑ k ∈ Finset.range (n+1), (n !:ℝ)*(((k:ℝ)+1)*((n-k:ℕ)+1:ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [shifted_choose_factorial n k (by have := Finset.mem_range.mp hk; omega)]
      ring
    _ = _ := by rw [← Finset.mul_sum,quadratic_sum]

theorem bracket_neither (b : ℕ) : bracket b 0 0=(b:ℝ)+1 := by
  unfold bracket
  simp only [Nat.sub_zero,Nat.add_zero]
  rw [unshifted_sum]
  exact mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b))

theorem bracket_hole (n : ℕ) : bracket (n+1) 1 0=1 := by
  unfold bracket
  simp only [Nat.add_sub_cancel,Nat.sub_zero,Nat.add_zero]
  rw [unshifted_sum,Nat.factorial_succ]
  push_cast
  exact div_self (mul_ne_zero (by positivity) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))

theorem bracket_full (n : ℕ) :
    bracket (n+1) 0 1=((n:ℝ)+2)*((n:ℝ)+3)/6 := by
  unfold bracket
  simp only [Nat.sub_zero,Nat.add_sub_cancel]
  rw [shifted_sum,Nat.factorial_succ]
  push_cast
  have hf : (n !:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : (n:ℝ)+1≠0 := by positivity
  field_simp [hf,hn]

theorem bracket_both (n : ℕ) : bracket (n+2) 1 1=((n:ℝ)+3)/6 := by
  unfold bracket
  have he : n+2-1-1=n := by omega
  rw [he,shifted_sum]
  rw [show n+2=(n+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
  push_cast
  have hf : (n !:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : (n:ℝ)+1≠0 := by positivity
  have hn' : (n:ℝ)+2≠0 := by positivity
  field_simp [hf,hn,hn']
  ring

end ContingencyTables.InitializationBrackets

end OAI
