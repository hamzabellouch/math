import Mathlib.Tactic

namespace OAI

/-! The integer reduction in the balanced-Weyl-moment argument.
Volume is normalized so that the Euler identity is
`2 + n + m = volume * (1 + P + Q)`. -/

namespace PositiveEinsteinFour

noncomputable section

/-- The characteristic identities, two gaps, and upper volume estimate leave
only the ordered exceptional pair `(n₊, n₋) = (2, 1)` if the counts differ. -/
theorem ordered_harmonic_counts (n m : ℕ) (P Q volume : ℝ)
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (horder : Q ≤ P) (hsum : P + Q < 4)
    (hvolume : 0 < volume)
    (hupper : volume ≤ 2 * (1 - 3 / 40 * (P + Q)))
    (heuler : 2 + (n : ℝ) + (m : ℝ) = volume * (1 + P + Q))
    (hsignature : (n : ℝ) - (m : ℝ) = 2 / 3 * volume * (P - Q)) :
    n = m ∨ n = 2 ∧ m = 1 := by
  have hnm : m ≤ n := by
    have hdiff : 0 ≤ (n : ℝ) - (m : ℝ) := by
      rw [hsignature]
      exact mul_nonneg (mul_nonneg (by norm_num) hvolume.le) (sub_nonneg.mpr horder)
    exact_mod_cast sub_nonneg.mp hdiff
  have hchi : 2 + (n : ℝ) + (m : ℝ) < 7 := by
    have hmul := mul_le_mul_of_nonneg_right hupper
      (show 0 ≤ 1 + P + Q by linarith)
    have hstrict : 0 < (4 - (P + Q)) * (25 - 3 * (P + Q)) := by
      apply mul_pos <;> linarith
    nlinarith [heuler]
  have hratio : 15 * ((n : ℝ) - (m : ℝ)) < 4 * (2 + (n : ℝ) + (m : ℝ)) := by
    have hlin : 10 * (P - Q) < 4 * (1 + P + Q) := by linarith
    have hmul := mul_lt_mul_of_pos_left hlin hvolume
    nlinarith [heuler, hsignature]
  have hnat_sum : 2 + n + m < 7 := by exact_mod_cast hchi
  have hnat_ratio : 15 * (n - m) < 4 * (2 + n + m) := by
    have hcast : (15 * (n - m) : ℕ) < (4 * (2 + n + m) : ℕ) := by
      exact_mod_cast (show 15 * ((n - m : ℕ) : ℝ) <
          4 * (((2 + n + m : ℕ) : ℝ)) by
        push_cast
        rw [Nat.cast_sub hnm]
        exact hratio)
    exact hcast
  omega

/-- In the exceptional count pair, the larger second moment is fixed by the
smaller one. This is the exact `13/7` relation used before the two-moment
obstruction. -/
theorem exceptional_moment_relation (P Q volume : ℝ)
    (heuler : 5 = volume * (1 + P + Q))
    (hsignature : 1 = 2 / 3 * volume * (P - Q)) :
    P = (13 * Q + 3) / 7 := by
  have hvolume_ne : volume ≠ 0 := by
    intro hzero
    simp [hzero] at heuler
  have hprod : volume * (7 * P - 13 * Q - 3) = 0 := by
    nlinarith [heuler, hsignature]
  have := (mul_eq_zero.mp hprod).resolve_left hvolume_ne
  linarith

/-- Integrating `v² ≤ (2-b)²` with the exceptional relation yields the second
constraint of the scalar moment obstruction. `mean` is the mean of `b`. -/
theorem exceptional_moment_constraint (P Q mean : ℝ)
    (hrelation : P = (13 * Q + 3) / 7)
    (hpointwise_integral : P ≤ 4 - 4 * mean + Q) :
    28 * mean + 6 * Q ≤ 25 := by
  linarith

end

end PositiveEinsteinFour

end OAI
