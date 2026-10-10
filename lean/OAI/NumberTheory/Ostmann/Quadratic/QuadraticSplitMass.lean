import OAI.NumberTheory.Ostmann.Quadratic.QuadraticKernelBias

namespace OAI

/-! # Converting a signed quadratic sum to retained split-prime mass -/

namespace Ostmann

open scoped BigOperators Classical

theorem jacobi_ne_zero_of_prime_not_dvd (d : ℤ) {p : ℕ} (hp : p.Prime)
    (hpd : ¬p ∣ d.natAbs) : jacobiSym d p ≠ 0 := by
  apply jacobiSym.ne_zero
  rw [Int.gcd_eq_natAbs]
  exact (hp.coprime_iff_not_dvd.mpr hpd).symm

/-- All losses are expressed in the original nonnegative weights. In the
application w(p)=log(p)/p^s, and the removed divisor is 2*m*abs(d). -/
theorem quadratic_split_mass_bound (P : Finset ℕ) (d : ℤ) (D Q : ℕ)
    (hdD : d.natAbs ∣ D) (hP : ∀ p ∈ P, p.Prime) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (L B T E : ℝ)
    (htotal : L ≤ ∑ p ∈ P, w p)
    (hsigned : -B ≤ ∑ p ∈ P, w p * (jacobiSym d p : ℝ))
    (htail : (∑ p ∈ P.filter (fun p => Q < p), w p) ≤ T)
    (hdiv : (∑ p ∈ P.filter (fun p => p ∣ D), w p) ≤ E) :
    (L - B) / 2 - T - E ≤
      ∑ p ∈ P.filter (fun p => p ≤ Q ∧ ¬p ∣ D ∧ jacobiSym d p = 1), w p := by
  have hp (p : ℕ) (hp : p ∈ P) :
      w p * (1 + (jacobiSym d p : ℝ)) ≤
        2 * (if p ≤ Q ∧ ¬p ∣ D ∧ jacobiSym d p = 1 then w p else 0) +
        2 * (if Q < p then w p else 0) + 2 * (if p ∣ D then w p else 0) := by
    have hn := hw p hp
    rcases jacobiSym.trichotomy d p with hz | ho | hm
    · have hpd : p ∣ D := by
        by_contra hnD
        have hnd : ¬p ∣ d.natAbs := fun h => hnD (dvd_trans h hdD)
        exact jacobi_ne_zero_of_prime_not_dvd d (hP p hp) hnd hz
      simp only [hz, Int.cast_zero, add_zero, mul_one, hpd, ite_true]
      split_ifs <;> linarith
    · by_cases hq : p ≤ Q <;> by_cases hd : p ∣ D <;>
        simp [ho, hq, hd, show Q < p ↔ ¬p ≤ Q by omega] <;> linarith
    · simp only [hm, Int.cast_neg, Int.cast_one, add_neg_cancel, mul_zero]
      positivity
  have hh := Finset.sum_le_sum hp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter] at hh
  have hid : (∑ p ∈ P, w p * (1 + (jacobiSym d p : ℝ))) =
      (∑ p ∈ P, w p) + ∑ p ∈ P, w p * (jacobiSym d p : ℝ) := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib]
  rw [hid] at hh
  linarith

end Ostmann

end OAI
