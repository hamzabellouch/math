import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeDivisors
import OAI.NumberTheory.Ostmann.Quadratic.CommonCenter

namespace OAI

/-! # Intersections of the matching-prime sets attached to integer lifts -/

namespace Ostmann

open scoped BigOperators

def matchingPrimes (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (n : ℤ) : Finset ℕ :=
  P.filter fun p => (p : ℤ) ∣ n - a * t p

theorem matchingPrimes_inter_dvd (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (n m : ℤ)
    {p : ℕ} (hp : p ∈ matchingPrimes P a t n ∩ matchingPrimes P a t m) :
    p ∣ (n - m).natAbs := by
  obtain ⟨hn, hm⟩ := Finset.mem_inter.mp hp
  have hd := dvd_sub (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hm).2
  have heq : (n - a * t p) - (m - a * t p) = n - m := by ring
  rw [heq] at hd
  exact Int.natCast_dvd.mp hd

/-- Distinct lifts cannot share more than `k` large prime congruences. -/
theorem matchingPrimes_inter_card_le (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ)
    (n m : ℤ) (hnm : n ≠ m) (k : ℕ) (B : ℝ) (hB : 0 < B)
    (hprime : ∀ p ∈ P, p.Prime) (hlog : ∀ p ∈ P, B ≤ Real.log (p : ℝ))
    (hdiff : Real.log ((n - m).natAbs : ℝ) < (k + 1 : ℕ) * B) :
    (matchingPrimes P a t n ∩ matchingPrimes P a t m).card ≤ k := by
  let S := matchingPrimes P a t n ∩ matchingPrimes P a t m
  have hsub : S ⊆ P := fun p hp => (Finset.mem_filter.mp (Finset.mem_inter.mp hp).1).1
  have hpos : 0 < (n - m).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hnm)
  have hbudget := sum_log_prime_divisors_le S hpos
    (fun p hp => hprime p (hsub hp)) (fun p hp => matchingPrimes_inter_dvd P a t n m hp)
  have hlow : (S.card : ℝ) * B ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
    calc
      _ = ∑ _p ∈ S, B := by simp
      _ ≤ _ := Finset.sum_le_sum fun p hp => hlog p (hsub hp)
  have hcard : (S.card : ℝ) < (k + 1 : ℕ) := by nlinarith
  have : S.card < k + 1 := by exact_mod_cast hcard
  exact Nat.lt_succ_iff.mp this

/-- A common integer lift determines the same rational center in every matching prime field. -/
theorem matchingPrimes_modEq (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (n : ℤ)
    {p : ℕ} (hp : p ∈ matchingPrimes P a t n) : n ≡ a * t p [ZMOD (p : ℤ)] := by
  apply Int.modEq_iff_dvd.mpr
  simpa only [neg_sub] using dvd_neg.mpr (Finset.mem_filter.mp hp).2

end Ostmann

end OAI
