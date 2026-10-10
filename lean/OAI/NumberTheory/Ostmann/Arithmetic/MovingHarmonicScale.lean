import OAI.NumberTheory.Ostmann.Arithmetic.MovingBadHarmonicScale

namespace OAI

/-! # The full counterpart normalization grows only exponentially in bulk size -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_moving_harmonic_scale (n s k : ℕ) (hk : 0 < k)
    (C a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hbudget : 4 * C * s ≤ ε * (k : ℝ) ^ 4) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ mass : MovingRegularSlot n s m → ℝ,
      (∀ j : TreeLeafIndex n × Fin s, Real.exp (-C * L) ≤ mass (j.1, .inl j.2)) →
      (∀ j : TreeLeafIndex n × Fin m, a * L ≤ mass (j.1, .inr j.2)) →
      ((Fintype.card (MovingRegularSlot n s m)).factorial : ℝ) * (∏ i, (mass i)⁻¹) ≤
        Real.exp ((Real.log 2 + Real.log ((k : ℝ) ^ 4 / a) +
          Real.log (2 ^ n : ℕ) + ε) * (2 ^ n * m : ℕ)) := by
  filter_upwards [eventual_moving_nonbulk_cost n s k hk C ε hε hbudget,
    eventually_gt_atTop (0 : ℝ)] with L hcost hL
  dsimp only
  intro mass hsmall hbulk
  have hscale : (spectatorBulkCount k L : ℝ) ≤ ((k : ℝ) ^ 4 / a) * (a * L) := by
    convert spectatorBulkCount_upper k L hL.le using 1; field_simp
  have hid : -(C / a) * (a * L) = -C * L := by field_simp
  have he := movingRegular_factorial_harmonic_bound n s (spectatorBulkCount k L) mass
    (a * L) ((k : ℝ) ^ 4 / a) (C / a) (mul_pos ha hL) (by positivity) hscale
    (by simpa only [hid] using hsmall) hbulk
  have hid' : (C / a) * (a * L) = C * L := by field_simp
  rw [hid'] at he
  have hA : (1 : ℝ) ≤ (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by positivity :
      (2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) ≠ 0))
  have hpre : (2 : ℝ) ^ (2 ^ n * s) * ((2 ^ n * s).factorial : ℝ) *
      Real.exp (C * L * (2 ^ n * s : ℕ)) ≤
      movingNonbulkCost n s * Real.exp (C * L * (2 ^ n * s : ℕ)) := by
    have hh := mul_le_mul_of_nonneg_right hA (show 0 ≤
      (2 : ℝ) ^ (2 ^ n * s) * ((2 ^ n * s).factorial : ℝ) *
        Real.exp (C * L * (2 ^ n * s : ℕ)) by positivity)
    simpa only [movingNonbulkCost, one_mul, mul_assoc] using hh
  apply he.trans
  apply (mul_le_mul_of_nonneg_right (hpre.trans hcost) (Real.exp_nonneg _)).trans_eq
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

end Ostmann

end OAI
