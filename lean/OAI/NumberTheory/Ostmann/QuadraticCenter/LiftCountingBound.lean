import OAI.NumberTheory.Ostmann.QuadraticCenter.LiftCountingBasic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem bounded_congruent_integer_card_le (S : Finset ℤ) (H q : ℕ)
    (hbound : ∀ n ∈ S, -(H : ℤ) ≤ n ∧ n ≤ H)
    (hdiv : ∀ n ∈ S, ∀ m ∈ S, (q : ℤ) ∣ n - m) :
    S.card ≤ 2 * H / q + 1 := by
  classical
  have hh := Finset.card_le_card_of_injOn (s := S) (t := Finset.range (2 * H / q + 1))
    (fun n : ℤ => (n + H).toNat / q) ?_ ?_
  · simpa only [Finset.card_range] using hh
  · intro n hn
    apply Finset.mem_range.mpr
    have hb := hbound n hn
    have hu : (n + H).toNat ≤ 2 * H := by omega
    exact lt_of_le_of_lt (Nat.div_le_div_right hu) (Nat.lt_succ_self _)
  · intro n hn m hm he
    have hn0 : 0 ≤ n + (H : ℤ) := by have := (hbound n hn).1; omega
    have hm0 : 0 ≤ m + (H : ℤ) := by have := (hbound m hm).1; omega
    have hd : Int.ModEq (q : ℤ) (n + H) (m + H) := by
      apply Int.modEq_iff_dvd.mpr
      convert hdiv m hm n hn using 1; ring
    have hnat : Nat.ModEq q (n + H).toNat (m + H).toNat := by
      apply Int.natCast_modEq_iff.mp
      simpa only [Int.toNat_of_nonneg hn0, Int.toNat_of_nonneg hm0] using hd
    change (n + H).toNat % q = (m + H).toNat % q at hnat
    change (n + H).toNat / q = (m + H).toNat / q at he
    have hnq := Nat.mod_add_div (n + H).toNat q
    have hmq := Nat.mod_add_div (m + H).toNat q
    rw [hnat, he] at hnq
    have heq := hnq.symm.trans hmq
    omega

theorem boundedSubsetLifts_card_le {U : Finset ℕ}
    (hU : ∀ p ∈ U, Nat.Prime p) (a : ℤ) (t : ℕ → ℤ) (H : ℕ) :
    (boundedSubsetLifts U a t H).card ≤ 2 * H / (∏ p ∈ U, p) + 1 := by
  apply bounded_congruent_integer_card_le
  · intro n hn
    exact ⟨(mem_boundedSubsetLifts.mp hn).1, (mem_boundedSubsetLifts.mp hn).2.1⟩
  · intro n hn m hm
    exact Int.natCast_dvd.mpr (boundedSubsetLifts_prod_dvd_sub hU hn hm)

theorem sum_matching_descFactorial_le {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (a : ℤ) (t : ℕ → ℤ)
    (H k Z : ℕ) (hZ : 0 < Z) (hlarge : ∀ p ∈ P, Z ≤ p) :
    (∑ n ∈ Finset.Icc (-(H : ℤ)) H, (matchingPrimes P a n t).card.descFactorial k) ≤
      P.card ^ k * (2 * H / Z ^ k + 1) := by
  rw [sum_matching_descFactorial_eq]
  have hsum : (∑ U ∈ P.powersetCard k, (boundedSubsetLifts U a t H).card) ≤
      (Nat.choose P.card k) * (2 * H / Z ^ k + 1) := by
    calc
      _ ≤ ∑ U ∈ P.powersetCard k, (2 * H / Z ^ k + 1) := by
        apply Finset.sum_le_sum
        intro U hU
        obtain ⟨hUP, hUk⟩ := Finset.mem_powersetCard.mp hU
        apply (boundedSubsetLifts_card_le (fun p hp => hP p (hUP hp)) a t H).trans
        apply Nat.add_le_add_right
        apply Nat.div_le_div_left
        · calc
            Z ^ k = ∏ _p ∈ U, Z := by simp [hUk]
            _ ≤ ∏ p ∈ U, p := Finset.prod_le_prod (fun p hp => hlarge p (hUP hp))
        · exact pow_pos hZ k
      _ = _ := by simp
  calc
    _ ≤ k.factorial * (Nat.choose P.card k * (2 * H / Z ^ k + 1)) := Nat.mul_le_mul_left _ hsum
    _ = P.card.descFactorial k * (2 * H / Z ^ k + 1) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.descFactorial_le_pow P.card k)

end Ostmann.QuadraticCenter

end

end OAI
