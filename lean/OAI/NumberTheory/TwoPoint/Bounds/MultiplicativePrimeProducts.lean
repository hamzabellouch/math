import OAI.NumberTheory.TwoPoint.Basic
import Mathlib.Data.Nat.GCD.BigOperators

namespace OAI

/-! Finite squarefree products of an ordinary multiplicative function,
and the elementary defect inequality used in selecting raw divisors. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma Multiplicative.prime_product {f : ℕ → ℂ} (hf : Multiplicative f)
    (hf1 : f 1 = 1) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    f (∏ p ∈ S, p) = ∏ p ∈ S, f p := by
  induction S using Finset.induction_on with
  | empty => simp [hf1]
  | @insert p S hp ih =>
    have hprime : p.Prime := hS p (mem_insert_self _ _)
    have hsub : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ S, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (Nat.coprime_primes hprime (hsub q hq)).mpr (by
        intro he
        exact hp (he ▸ hq))
    rw [prod_insert hp, hf p _ hprime.pos (prod_pos (fun q hq => (hsub q hq).pos)) hcop,
      ih hsub, prod_insert hp]

lemma one_sub_prod_le_sum {ι : Type*} (S : Finset ι) (r : ι → ℝ)
    (h0 : ∀ i ∈ S, 0 ≤ r i) (h1 : ∀ i ∈ S, r i ≤ 1) :
    1 - ∏ i ∈ S, r i ≤ ∑ i ∈ S, (1 - r i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hs0 : ∀ j ∈ S, 0 ≤ r j := fun j hj => h0 j (mem_insert_of_mem hj)
    have hs1 : ∀ j ∈ S, r j ≤ 1 := fun j hj => h1 j (mem_insert_of_mem hj)
    have hp := prod_le_one₀ hs0 hs1
    have hr := h1 i (mem_insert_self _ _)
    have hm := mul_le_of_le_one_left (sub_nonneg.mpr hp) hr
    rw [prod_insert hi, sum_insert hi]
    have hh := ih hs0 hs1
    nlinarith

lemma multiplicative_prime_product_defect {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1)
    (hf : OneBounded f) (hg : OneBounded g)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    1 - ‖f (∏ p ∈ S, p) * g (∏ p ∈ S, p)‖ ≤
      ∑ p ∈ S, (1 - ‖f p * g p‖) := by
  rw [hfm.prime_product hf1 S hS, hgm.prime_product hg1 S hS,
    ← prod_mul_distrib, norm_prod]
  apply one_sub_prod_le_sum
  · intro p _
    positivity
  · intro p hp
    rw [norm_mul]
    exact (mul_le_mul (hf p (hS p hp).pos) (hg p (hS p hp).pos)
      (norm_nonneg _) zero_le_one).trans (by norm_num)

lemma prime_product_pair_defect {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g) (p : ℕ) (hp : 0 < p) :
    1 - ‖f p * g p‖ ≤ (1 - ‖f p‖) + (1 - ‖g p‖) := by
  rw [norm_mul]
  nlinarith [mul_nonneg (sub_nonneg.mpr (hf p hp)) (sub_nonneg.mpr (hg p hp))]

end TwoPointCorrelations

end OAI
