import OAI.NumberTheory.Ostmann.Arithmetic.MovingHarmonicMassBudget
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # The bad-arrangement saving in the complete diagonal normalization -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def movingNonbulkCost (n s : ℕ) : ℝ :=
  (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
    (2 : ℝ) ^ (2 ^ n * s) * ((2 ^ n * s).factorial : ℝ)

theorem moving_bad_full_harmonic_bound (n s m : ℕ)
    (mass : MovingRegularSlot n s m → ℝ) (L z C : ℝ) (hL : 0 < L) (hz : 0 < z)
    (hm : (m : ℝ) ≤ z * L)
    (hsmall : ∀ j : TreeLeafIndex n × Fin s, Real.exp (-C * L) ≤ mass (j.1, .inl j.2))
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, L ≤ mass (j.1, .inr j.2)) :
    ((((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
      Real.exp ((2 ^ n : ℝ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4))) *
        (((Fintype.card (MovingRegularSlot n s m)).factorial : ℝ) * (∏ i, (mass i)⁻¹)) ≤
      movingNonbulkCost n s * Real.exp (C * L * (2 ^ n * s : ℕ)) *
        Real.exp ((Real.log 2 + Real.log z + Real.log (2 ^ n : ℕ) / 4 + 5 / 4) * (2 ^ n * m : ℕ)) := by
  have h := mul_le_mul_of_nonneg_left
    (movingRegular_factorial_harmonic_bound n s m mass L z C hL hz hm hsmall hbulk)
    (show 0 ≤ (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
      Real.exp ((2 ^ n : ℝ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) by positivity)
  apply h.trans_eq
  unfold movingNonbulkCost
  rw [show ((2 ^ n : ℝ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) =
    ((2 ^ n * m : ℕ) : ℝ) * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4) by push_cast; ring]
  have he : Real.exp (((2 ^ n * m : ℕ) : ℝ) * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) *
      Real.exp ((Real.log 2 + Real.log z + Real.log (2 ^ n : ℕ)) * (2 ^ n * m : ℕ)) =
      Real.exp ((Real.log 2 + Real.log z + Real.log (2 ^ n : ℕ) / 4 + 5 / 4) * (2 ^ n * m : ℕ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = movingNonbulkCost n s * Real.exp (C * L * (2 ^ n * s : ℕ)) *
        (Real.exp (((2 ^ n * m : ℕ) : ℝ) * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) *
        Real.exp ((Real.log 2 + Real.log z + Real.log (2 ^ n : ℕ)) * (2 ^ n * m : ℕ))) := by
      unfold movingNonbulkCost
      ring
    _ = _ := by rw [he]; rfl

theorem eventual_moving_nonbulk_cost (n s k : ℕ) (hk : 0 < k) (C ε : ℝ)
    (hε : 0 < ε) (hbudget : 4 * C * s ≤ ε * (k : ℝ) ^ 4) :
    ∀ᶠ L : ℝ in atTop,
      movingNonbulkCost n s * Real.exp (C * L * (2 ^ n * s : ℕ)) ≤
        Real.exp (ε * (2 ^ n : ℕ) * (spectatorBulkCount k L : ℝ)) := by
  let F := movingNonbulkCost n s
  let r : ℝ := (2 ^ n : ℕ)
  have hr : 0 < r := by dsimp [r]; positivity
  have hF : 0 < F := by dsimp [F, movingNonbulkCost]; positivity
  have hk4 : 0 < (k : ℝ) ^ 4 := by positivity
  have ht := (spectatorBulkCount_tendsto k hk).eventually
    (eventually_ge_atTop (2 * Real.log F / (ε * r)))
  filter_upwards [ht, eventually_ge_atTop (4 / (k : ℝ) ^ 4), eventually_ge_atTop (0 : ℝ)]
    with L hL hscale hL0
  have hscale' : 4 ≤ (k : ℝ) ^ 4 * L := by
    simpa only [mul_comm L] using (div_le_iff₀ hk4).mp hscale
  have hhalf := spectatorBulkCount_half k L hscale'
  have hc : C * L * (2 ^ n * s : ℕ) ≤ ε / 2 * r * (spectatorBulkCount k L : ℝ) := by
    have hb := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbudget hL0) hr.le
    have hm := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hε.le hr.le)
    dsimp only [r] at hm hb ⊢
    push_cast at hm hb ⊢
    nlinarith
  have hlog : Real.log F ≤ ε / 2 * r * (spectatorBulkCount k L : ℝ) := by
    have hh := (div_le_iff₀ (mul_pos hε hr)).mp hL
    nlinarith
  change F * _ ≤ _
  rw [← Real.exp_log hF, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

end Ostmann

end OAI
