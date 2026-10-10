import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

namespace QuantitativeVanDerWaerden

open scoped BigOperators

/-- The primes up to the short-period cutoff. -/
def dilationPrimes (h₀ : ℕ) : Finset ℕ :=
  (Finset.Icc 1 h₀).filter Nat.Prime

@[simp] theorem mem_dilationPrimes {p h₀ : ℕ} :
    p ∈ dilationPrimes h₀ ↔ Nat.Prime p ∧ p ≤ h₀ := by
  simp only [dilationPrimes, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.one_lt.le, h.2⟩, h.1⟩⟩

def dilation (h₀ M : ℕ) : ℕ :=
  ∏ p ∈ dilationPrimes h₀, p ^ Nat.log p (2 * M)

theorem dilation_pos (h₀ M : ℕ) : 0 < dilation h₀ M := by
  apply Nat.pos_of_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (mem_dilationPrimes.mp hp).1.ne_zero

theorem dilation_ne_zero (h₀ M : ℕ) : dilation h₀ M ≠ 0 :=
  (dilation_pos h₀ M).ne'

theorem prime_pow_dvd_dilation {h₀ M p a h : ℕ}
    (hp : p.Prime) (hp₀ : p ≤ h₀) (hh : 0 < h)
    (hmax : h ≤ 2 * M) (hpow : p ^ a ∣ h) :
    p ^ a ∣ dilation h₀ M := by
  have ha : a ≤ Nat.log p (2 * M) :=
    Nat.le_log_of_pow_le hp.one_lt ((Nat.le_of_dvd hh hpow).trans hmax)
  exact (pow_dvd_pow p ha).trans
    (Finset.dvd_prod_of_mem (fun p => p ^ Nat.log p (2 * M))
      (mem_dilationPrimes.mpr ⟨hp, hp₀⟩))

theorem primary_part_dvd_dilation {h₀ M p h : ℕ}
    (hp : p.Prime) (hp₀ : p ≤ h₀) (hh : 0 < h)
    (hmax : h ≤ 2 * M) :
    p ^ h.factorization p ∣ dilation h₀ M :=
  prime_pow_dvd_dilation hp hp₀ hh hmax (Nat.ordProj_dvd h p)

/-- Every positive period up to the cutoff is killed by the dilation. -/
theorem short_period_dvd_dilation {h₀ M h : ℕ}
    (hh : 0 < h) (hshort : h ≤ h₀) (hmax : h ≤ 2 * M) :
    h ∣ dilation h₀ M := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd (dilation h₀ M) h).mpr
  intro p a hp hpow
  by_cases ha : a = 0
  · simp [ha]
  have hph : p ∣ h := (dvd_pow_self p ha).trans hpow
  exact prime_pow_dvd_dilation hp ((Nat.le_of_dvd hh hph).trans hshort) hh hmax hpow

/-- The natural-number bound that yields `log λ ≤ h₀ * log (2M)`. -/
theorem dilation_le_pow {h₀ M : ℕ} (hM : 0 < M) :
    dilation h₀ M ≤ (2 * M) ^ h₀ := by
  have hcard : (dilationPrimes h₀).card ≤ h₀ := by
    simpa [dilationPrimes] using
      (Finset.card_filter_le (s := Finset.Icc 1 h₀) (p := Nat.Prime))
  have hfactor : ∀ p ∈ dilationPrimes h₀, p ^ Nat.log p (2 * M) ≤ 2 * M := by
    intro p _
    exact Nat.pow_log_le_self p (by omega)
  exact (Finset.prod_le_pow_card _ _ _ hfactor).trans
    (Nat.pow_le_pow_right (by omega) hcard)

/-- The explicit logarithmic size bound from the dilation lemma. -/
theorem log_dilation_le {h₀ M : ℕ} (hM : 0 < M) :
    Real.log (dilation h₀ M) ≤ (h₀ : ℝ) * Real.log (2 * M) := by
  have hpos : (0 : ℝ) < dilation h₀ M := by
    exact_mod_cast dilation_pos h₀ M
  have hle : (dilation h₀ M : ℝ) ≤ (2 * (M : ℝ)) ^ h₀ := by
    exact_mod_cast dilation_le_pow (h₀ := h₀) hM
  simpa only [Real.log_pow] using Real.log_le_log hpos hle

/-- Large prime powers are relatively prime to the dilation. -/
theorem dilation_coprime_prime_pow {h₀ M P a : ℕ}
    (hP : P.Prime) (hlarge : h₀ < P) :
    Nat.Coprime (dilation h₀ M) (P ^ a) := by
  unfold dilation
  refine Finset.prod_induction _ (fun n => Nat.Coprime n (P ^ a))
    (fun _ _ hm hn => Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩)
    (Nat.coprime_one_left _) ?_
  intro p hp
  obtain ⟨hpprime, hple⟩ := mem_dilationPrimes.mp hp
  exact Nat.coprime_pow_primes _ _ hpprime hP (by omega)

/-- If a multiplier contains every small primary part of the period, reducing
the resulting fraction removes every small prime from its denominator. -/
theorem prime_dvd_reducedDenominator_gt_of_primary_parts
    {h h₀ L t : ℕ} (hh : 0 < h)
    (hL : ∀ p : ℕ, p.Prime → p ≤ h₀ → p ^ h.factorization p ∣ L)
    {p : ℕ} (hp : p.Prime) (hpd : p ∣ h / Nat.gcd h (L * t)) : h₀ < p := by
  have hgpos : 0 < Nat.gcd h (L * t) := Nat.gcd_pos_of_pos_left _ hh
  have hqpos : 0 < h / Nat.gcd h (L * t) :=
    Nat.div_pos (Nat.le_of_dvd hh (Nat.gcd_dvd_left h (L * t))) hgpos
  by_contra hnot
  have hple : p ≤ h₀ := Nat.le_of_not_gt hnot
  have hpowg : p ^ h.factorization p ∣ Nat.gcd h (L * t) :=
    Nat.dvd_gcd (Nat.ordProj_dvd h p)
      ((hL p hp hple).trans (dvd_mul_right L t))
  have hval : h.factorization p ≤ (Nat.gcd h (L * t)).factorization p :=
    (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hgpos)).mp hpowg
  have hz : (h / Nat.gcd h (L * t)).factorization p = 0 := by
    rw [Nat.factorization_div (Nat.gcd_dvd_left h (L * t)),
      Finsupp.tsub_apply, Nat.sub_eq_zero_of_le hval]
  have hone : 1 ≤ (h / Nat.gcd h (L * t)).factorization p :=
    (hp.dvd_iff_one_le_factorization (Nat.ne_of_gt hqpos)).mp hpd
  rw [hz] at hone
  exact Nat.not_succ_le_zero 0 hone

theorem reducedDenominator_eq_one_or_gt_of_primary_parts
    {h h₀ L t : ℕ} (hh : 0 < h)
    (hL : ∀ p : ℕ, p.Prime → p ≤ h₀ → p ^ h.factorization p ∣ L) :
    h / Nat.gcd h (L * t) = 1 ∨ h₀ < h / Nat.gcd h (L * t) := by
  by_cases hq1 : h / Nat.gcd h (L * t) = 1
  · exact Or.inl hq1
  · apply Or.inr
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hq1
    have hgpos : 0 < Nat.gcd h (L * t) := Nat.gcd_pos_of_pos_left _ hh
    have hqpos : 0 < h / Nat.gcd h (L * t) :=
      Nat.div_pos (Nat.le_of_dvd hh (Nat.gcd_dvd_left h (L * t))) hgpos
    exact (prime_dvd_reducedDenominator_gt_of_primary_parts hh hL hp hpd).trans_le
      (Nat.le_of_dvd hqpos hpd)

/-- Dilation removes every small prime from a reduced denominator. -/
theorem prime_dvd_dilatedDenominator_gt {h₀ M h p : ℕ} (t : ℤ)
    (hh : 0 < h) (hmax : h ≤ 2 * M) (hp : p.Prime)
    (hpd : p ∣ h / Int.gcd (h : ℤ) ((dilation h₀ M : ℤ) * t)) : h₀ < p := by
  apply prime_dvd_reducedDenominator_gt_of_primary_parts (t := t.natAbs) hh
    (fun p hp hp₀ => primary_part_dvd_dilation hp hp₀ hh hmax) hp
  simpa [Int.gcd_def, Int.natAbs_mul] using hpd

theorem dilatedDenominator_eq_one_or_gt {h₀ M h : ℕ} (t : ℤ)
    (hh : 0 < h) (hmax : h ≤ 2 * M) :
    h / Int.gcd (h : ℤ) ((dilation h₀ M : ℤ) * t) = 1 ∨
      h₀ < h / Int.gcd (h : ℤ) ((dilation h₀ M : ℤ) * t) := by
  simpa [Int.gcd_def, Int.natAbs_mul] using
    (reducedDenominator_eq_one_or_gt_of_primary_parts (t := t.natAbs) hh
      (fun p hp hp₀ => primary_part_dvd_dilation hp hp₀ hh hmax))

end QuantitativeVanDerWaerden

end OAI
