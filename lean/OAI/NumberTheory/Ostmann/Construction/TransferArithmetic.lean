import Mathlib.Data.Nat.Prime.Basic
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticSupport

namespace OAI

/-! # The arithmetic separation of diagonal and transferred terms -/

namespace Ostmann

/-- A nonzero transferred frequency rules out a shared prime between
the two inherited products. All such primes exceed the frequency. -/
theorem transferred_products_coprime (HL HR : ℕ) (v w s P : ℤ) (hs : s ≠ 0)
    (hrel : v * HR - w * HL = s * P)
    (hsmall : ∀ q, q.Prime → q ∣ HL → q ∣ HR → s.natAbs < q)
    (hunit : ∀ q, q.Prime → q ∣ HL → q ∣ HR → IsCoprime (q : ℤ) P) :
    HL.Coprime HR := by
  apply Nat.coprime_of_dvd
  intro q hq hqL hqR
  have hL : (q : ℤ) ∣ (HL : ℤ) := Int.natCast_dvd_natCast.mpr hqL
  have hR : (q : ℤ) ∣ (HR : ℤ) := Int.natCast_dvd_natCast.mpr hqR
  have hN : (q : ℤ) ∣ v * HR - w * HL :=
    dvd_sub (dvd_mul_of_dvd_right hR v) (dvd_mul_of_dvd_right hL w)
  rw [hrel] at hN
  have hqs : (q : ℤ) ∣ s := (hunit q hq hqL hqR).dvd_of_dvd_mul_right hN
  have hle := Int.natAbs_le_of_dvd_ne_zero hqs hs
  simp only [Int.natAbs_natCast] at hle
  exact (not_le_of_gt (hsmall q hq hqL hqR)) hle

theorem large_prime_factors_coprime_frequency (H : ℕ) (v : ℤ) (hv : v ≠ 0)
    (hlarge : ∀ q, q.Prime → q ∣ H → v.natAbs < q) : H.Coprime v.natAbs := by
  apply Nat.coprime_of_dvd
  intro q hq hqH hqv
  exact (not_le_of_gt (hlarge q hq hqH))
    (Nat.le_of_dvd (Int.natAbs_pos.mpr hv) hqv)

/-- The zero numerator has only the equal-product, equal-frequency
diagonal when prime factors exceed the frequencies. -/
theorem diagonal_products_equal (HL HR : ℕ) (hHL : 0 < HL) (v w : ℤ)
    (hv : v ≠ 0) (hw : w ≠ 0) (hrel : v * HR = w * HL)
    (hL : ∀ q, q.Prime → q ∣ HL → v.natAbs < q)
    (hR : ∀ q, q.Prime → q ∣ HR → w.natAbs < q) : HL = HR ∧ v = w := by
  have hvH := large_prime_factors_coprime_frequency HL v hv hL
  have hwH := large_prime_factors_coprime_frequency HR w hw hR
  have habs := congrArg Int.natAbs hrel
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at habs
  have hdL : HL ∣ HR := hvH.dvd_of_dvd_mul_left (by
    rw [habs]
    exact dvd_mul_left HL w.natAbs)
  have hdR : HR ∣ HL := hwH.dvd_of_dvd_mul_left (by
    rw [← habs]
    exact dvd_mul_left HR v.natAbs)
  have heq : HL = HR := Nat.dvd_antisymm hdL hdR
  refine ⟨heq, ?_⟩
  rw [← heq] at hrel
  exact mul_right_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hHL) : (HL : ℤ) ≠ 0) hrel

/-- Regrouping a nonzero numerator by the new signed frequency is
one-to-one, exactly as in the transfer substitution. -/
theorem unique_transferred_frequency (N P : ℤ) (hN : N ≠ 0) (hP : P ≠ 0)
    (hdiv : P ∣ N) : ∃! s : ℤ, s ≠ 0 ∧ N = s * P := by
  obtain ⟨s, hs⟩ := hdiv
  refine ⟨s, ⟨?_, by simpa only [mul_comm] using hs⟩, ?_⟩
  · intro hz
    simp only [hz, mul_zero] at hs
    exact hN hs
  · intro t ht
    apply mul_right_cancel₀ hP
    rw [← ht.2, hs, mul_comm]

end Ostmann

end OAI
