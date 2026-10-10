import OAI.NumberTheory.JointDickman.Amplification.ArithmeticCandidateRoots

namespace OAI

/-! # The next digit at a coefficient prime remains uniform -/

namespace JointDickman
open Finset Classical

/-- Cancellation of one known prime factor leaves the next-digit test. -/
theorem prime_square_affine_digit {p : ℕ} (hp : p ≠ 0) {z c t : ℤ}
    (hz : (p : ℤ) ∣ z) :
    (p : ℤ)^2 ∣ z+(p : ℤ)*c*t ↔ (p : ℤ) ∣ z/p+c*t := by
  obtain ⟨k,rfl⟩ := hz
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  rw [Int.mul_ediv_cancel_left _ hp0, pow_two]
  have he : (p : ℤ)*k+(p : ℤ)*c*t = (p : ℤ)*(k+c*t) := by ring
  rw [he,Int.mul_dvd_mul_iff_left hp0]

noncomputable def higherDigitRoot (p : ℕ) [Fact p.Prime] (z c : ℤ) : ZMod p :=
  -(z/p : ℤ)/(c : ZMod p)

/-- The actual second-digit divisibility condition is one residue class;
no conditioning on absence of squares is used. -/
theorem prime_square_digit_root {p : ℕ} [Fact p.Prime] {z c : ℤ}
    (hz : (p : ℤ) ∣ z) (hc : ¬ (p : ℤ) ∣ c) (t : ZMod p) :
    ((p : ℤ)^2 ∣ z+(p : ℤ)*c*(t.val : ℤ)) ↔ t = higherDigitRoot p z c := by
  rw [prime_square_affine_digit (Fact.out : p.Prime).ne_zero hz]
  have hc0 : (c : ZMod p) ≠ 0 :=
    fun h => hc ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, higherDigitRoot, eq_div_iff hc0]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val]
  constructor <;> intro h <;> linear_combination h

/-- Given any first digit compatible with the coefficient, the probability
of the quotient prime test over its unconditioned next digit is exactly 1/p. -/
theorem prime_square_digit_probability {p : ℕ} [Fact p.Prime] {z c : ℤ}
    (hz : (p : ℤ) ∣ z) (hc : ¬ (p : ℤ) ∣ c) :
    (∑ t : ZMod p, if (p : ℤ)^2 ∣ z+(p : ℤ)*c*(t.val : ℤ)
      then (1 : ℝ) else 0)/(p : ℝ) = 1/(p : ℝ) := by
  simp_rw [prime_square_digit_root hz hc]
  simp

/-- Equivalent form for an affine numerator at a fixed site. -/
theorem affine_numerator_digit_probability {p : ℕ} [Fact p.Prime]
    (c b r i : ℤ) (hz : (p : ℤ) ∣ c*(r+i)-b) (hc : ¬ (p : ℤ) ∣ c) :
    (∑ t : ZMod p, if (p : ℤ)^2 ∣ c*(r+(p : ℤ)*(t.val : ℤ)+i)-b
      then (1 : ℝ) else 0)/(p : ℝ) = 1/(p : ℝ) := by
  have he (t : ZMod p) :
      c*(r+(p : ℤ)*(t.val : ℤ)+i)-b = (c*(r+i)-b)+(p : ℤ)*c*(t.val : ℤ) := by ring
  simp_rw [he]
  exact prime_square_digit_probability hz hc

/-- An incompatible first digit gives probability zero; the uniform bound
therefore holds without a first-digit compatibility hypothesis. -/
theorem prime_square_digit_probability_le {p : ℕ} [Fact p.Prime] (z c : ℤ)
    (hc : ¬ (p : ℤ) ∣ c) :
    (∑ t : ZMod p, if (p : ℤ)^2 ∣ z+(p : ℤ)*c*(t.val : ℤ)
      then (1 : ℝ) else 0)/(p : ℝ) ≤ 1/(p : ℝ) := by
  by_cases hz : (p : ℤ) ∣ z
  · exact (prime_square_digit_probability hz hc).le
  · have hn (t : ZMod p) : ¬ (p : ℤ)^2 ∣ z+(p : ℤ)*c*(t.val : ℤ) := by
      intro h
      have hpz : (p : ℤ) ∣ z+(p : ℤ)*c*(t.val : ℤ) :=
        (dvd_pow_self _ (by omega : 2 ≠ 0)).trans h
      have hpt : (p : ℤ) ∣ (p : ℤ)*c*(t.val : ℤ) := by
        exact ⟨c*(t.val : ℤ),by ring⟩
      exact hz (by simpa using dvd_sub hpz hpt)
    simp only [hn,ite_false,sum_const_zero,zero_div]
    positivity

end JointDickman

end OAI
