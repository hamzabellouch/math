import OAI.NumberTheory.Ostmann.Arithmetic.MovingBadHarmonicScale
import OAI.NumberTheory.Ostmann.Construction.DiagonalGapBudget

namespace OAI

/-! # The bad part of the actual logarithmic diagonal at the chosen gaps -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_moving_bad_diagonal_rate (n s k : ℕ) (hk : 0 < k)
    (Bs BD Bz B C a ε εdiag : ℝ) (ha : 0 < a) (hε : 0 < ε) (hεdiag : 0 ≤ εdiag)
    (hbudget : 4 * C * s ≤ ε * (k : ℝ) ^ 4) (hBz : 9 ≤ Bz)
    (hBD : Bs + 2 * B + (Real.log 2 - Real.log a + 5 / 4 + ε + Real.log 12 + 1 + εdiag) + 6 ≤ BD) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let z := (k : ℝ) ^ 4
      let r : ℝ := (2 ^ n : ℕ)
      let Δ := spectatorBaseGap Bs z m
      ∀ mass : MovingRegularSlot n s m → ℝ,
      (∀ j : TreeLeafIndex n × Fin s, Real.exp (-C * L) ≤ mass (j.1, .inl j.2)) →
      (∀ j : TreeLeafIndex n × Fin m, a * L ≤ mass (j.1, .inr j.2)) →
      ∀ arch : ℝ, arch ≤ Real.exp (-spectatorStepGap BD Bz z r m) →
      arch *
        (((((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
          Real.exp (r * m * (-(3 / 4 : ℝ) * Real.log r + 5 / 4))) *
            (((Fintype.card (MovingRegularSlot n s m)).factorial : ℝ) * (∏ i, (mass i)⁻¹))) *
        Real.exp (r * Δ + (Real.log 12 + 1) * r * m + εdiag * m) ≤
          Real.exp (-(2 * B + 6) * r * m) := by
  filter_upwards [eventual_moving_bad_harmonic_scale n s k hk C a ε ha hε hbudget,
    eventually_gt_atTop (0 : ℝ)] with L hmass hL
  dsimp only at hmass ⊢
  intro mass hsmall hbulk arch harch
  let m := spectatorBulkCount k L
  let z := (k : ℝ) ^ 4
  let r : ℝ := (2 ^ n : ℕ)
  have hr : 1 ≤ r := by dsimp [r]; exact_mod_cast (Nat.one_le_two_pow)
  have hz : 1 ≤ z := by
    dsimp [z]
    exact one_le_pow₀ (by exact_mod_cast hk)
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hlog : Real.log ((k : ℝ) ^ 4 / a) = Real.log z - Real.log a :=
    Real.log_div (by positivity) ha.ne'
  have hnorm := hmass mass hsmall hbulk
  rw [hlog] at hnorm
  have hp : (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) := by simp
  rw [hp] at hnorm
  have hmass0 : 0 ≤ ∏ i, (mass i)⁻¹ := by
    apply Finset.prod_nonneg
    rintro ⟨j, i | i⟩ _
    · exact inv_nonneg.mpr ((Real.exp_pos _).le.trans (hsmall (j, i)))
    · exact inv_nonneg.mpr ((mul_pos ha hL).le.trans (hbulk (j, i)))
  have hdiag : r * spectatorBaseGap Bs z m + (Real.log 12 + 1) * r * m + εdiag * m ≤
      r * spectatorBaseGap Bs z m + (Real.log 12 + 1 + εdiag) * r * m := by
    nlinarith [mul_le_mul_of_nonneg_right hr (mul_nonneg hεdiag hm)]
  have hgap := spectator_diagonal_exponent_bound Bs BD Bz z r m
    (Real.log 2 - Real.log a + 5 / 4 + ε + Real.log 12 + 1 + εdiag) B
    hz hr hm hBz hBD
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul harch hnorm (mul_nonneg (by positivity)
      (mul_nonneg (Nat.cast_nonneg _) hmass0)) (Real.exp_nonneg _)) (Real.exp_nonneg _)).trans
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp only [r] at hdiag hgap ⊢
  push_cast at hdiag hgap ⊢
  nlinarith only [hdiag, hgap]

end Ostmann

end OAI
