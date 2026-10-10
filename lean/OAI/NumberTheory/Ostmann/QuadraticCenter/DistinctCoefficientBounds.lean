import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter

theorem paired_binomial_coefficient_le {k j m J S : ℕ}
    (hj : 2 * j ≤ k) (hm : m ≤ J) :
    k.factorial * m.choose j * S.choose (k - 2 * j) ≤
      k ^ (2 * j) * J ^ j * S ^ (k - 2 * j) := by
  have hid : k.factorial * m.choose j * S.choose (k - 2 * j) =
      k.descFactorial (2 * j) * m.choose j * S.descFactorial (k - 2 * j) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose S,
      ← Nat.factorial_mul_descFactorial hj]
    ring
  rw [hid]
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul (Nat.descFactorial_le_pow _ _)
      ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hm _))
  · exact Nat.descFactorial_le_pow _ _

theorem pow_le_descFactorial_add (S k : ℕ) :
    S ^ k ≤ S.descFactorial k + k ^ 2 * S ^ (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      by_cases hk : k = 0
      · subst k
        simp
      have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hp : S * S ^ (k - 1) = S ^ k := by
        rw [← pow_succ', Nat.sub_add_cancel hkpos]
      have hrec : S * S.descFactorial k ≤
          S.descFactorial (k + 1) + k * S.descFactorial k := by
        rw [Nat.descFactorial_succ]
        have hs : S ≤ S - k + k := by omega
        nlinarith [Nat.mul_le_mul_right (S.descFactorial k) hs]
      have hih := Nat.mul_le_mul_left S ih
      have hdesc := Nat.mul_le_mul_left k (Nat.descFactorial_le_pow S k)
      rw [pow_succ']
      rw [show k + 1 - 1 = k by omega]
      have hp' : S * (k ^ 2 * S ^ (k - 1)) = k ^ 2 * S ^ k := by
        rw [← hp]
        ring
      rw [Nat.mul_add, hp'] at hih
      nlinarith

theorem abs_descFactorial_sub_pow_le {S J k : ℕ}
    (hSJ : S ≤ J) (hk : 2 ≤ k) :
    |(S.descFactorial k : ℝ) - (S : ℝ) ^ k| ≤
      (k : ℝ) ^ 2 * J * (S : ℝ) ^ (k - 2) := by
  have hdesc : (S.descFactorial k : ℝ) ≤ (S : ℝ) ^ k := by
    exact_mod_cast Nat.descFactorial_le_pow S k
  rw [abs_of_nonpos (sub_nonpos.mpr hdesc)]
  have herr : (S : ℝ) ^ k ≤ (S.descFactorial k : ℝ) + (k : ℝ) ^ 2 * (S : ℝ) ^ (k - 1) := by
    exact_mod_cast pow_le_descFactorial_add S k
  have hp : (S : ℝ) ^ (k - 1) = S * (S : ℝ) ^ (k - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hp] at herr
  have hSJr : (S : ℝ) ≤ J := by exact_mod_cast hSJ
  have hscale := mul_le_mul_of_nonneg_right hSJr
    (mul_nonneg (sq_nonneg (k : ℝ)) (pow_nonneg (Nat.cast_nonneg S) (k - 2)))
  nlinarith

theorem paired_binomial_coefficient_real_le {k j m J S : ℕ}
    (hj : 2 * j ≤ k) (hm : m ≤ J) :
    (k.factorial : ℝ) * m.choose j * S.choose (k - 2 * j) ≤
      ((k : ℝ) ^ 2 * J) ^ j * (S : ℝ) ^ (k - 2 * j) := by
  have hb := paired_binomial_coefficient_le (S := S) hj hm
  have hc : (k.factorial : ℝ) * m.choose j * S.choose (k - 2 * j) ≤
      (k : ℝ) ^ (2 * j) * (J : ℝ) ^ j * (S : ℝ) ^ (k - 2 * j) := by
    exact_mod_cast hb
  simpa only [mul_pow, pow_mul] using hc

end Ostmann.QuadraticCenter

end OAI
