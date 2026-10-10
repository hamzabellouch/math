import OAI.NumberTheory.TwoPoint.Bounds.PrimeDegreeTail

namespace OAI

/-! Positive tuple/padding edge weights are unchanged when the origin
is moved to the other endpoint. Both signs of the shift are included. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma dvd_add_multiple_iff (d : ℕ) (n c : ℤ) :
    (d : ℤ) ∣ n + (d : ℤ) * c ↔ (d : ℤ) ∣ n := by
  have hc : (d : ℤ) ∣ (d : ℤ) * c := dvd_mul_right _ _
  constructor
  · intro hn
    simpa only [add_sub_cancel_right] using dvd_sub hn hc
  · intro hn
    exact dvd_add hn hc

lemma positivePrimeWeight_add_multiple (d : ℕ) (n c : ℤ) :
    positivePrimeWeight d.primeFactors (n + (d : ℤ) * c) =
      positivePrimeWeight d.primeFactors n := by
  unfold positivePrimeWeight
  apply prod_congr rfl
  intro p hp
  have hpd : (p : ℤ) ∣ (d : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
  have hc : (p : ℤ) ∣ (d : ℤ) * c := dvd_mul_of_dvd_left hpd c
  have he : (p : ℤ) ∣ n + (d : ℤ) * c ↔ (p : ℤ) ∣ n := by
    constructor
    · intro hn
      simpa only [add_sub_cancel_right] using dvd_sub hn hc
    · intro hn
      exact dvd_add hn hc
  simp only [he]

lemma positive_divisor_endpoint (d q : ℕ) (n c : ℤ) (bad : ℤ → Prop) :
    actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
      (if (q : ℤ) ∣ n ∧ bad (n + (d * q : ℕ) * c) then 1 else 0) =
    actualPaddingCoefficient q * positivePrimeWeight d.primeFactors (n + (d * q : ℕ) * c) *
      (if (q : ℤ) ∣ n + (d * q : ℕ) * c ∧ bad (n + (d * q : ℕ) * c) then 1 else 0) := by
  have hd : (d * q : ℕ) * c = (d : ℤ) * ((q : ℤ) * c) := by push_cast; ring
  have hq : (d * q : ℕ) * c = (q : ℤ) * ((d : ℤ) * c) := by push_cast; ring
  rw [hd, positivePrimeWeight_add_multiple]
  have he : (q : ℤ) ∣ n + (d : ℤ) * ((q : ℤ) * c) ↔ (q : ℤ) ∣ n := by
    rw [← hd, hq]
    exact dvd_add_multiple_iff q n ((d : ℤ) * c)
  simp only [he]

end TwoPointCorrelations

end OAI
