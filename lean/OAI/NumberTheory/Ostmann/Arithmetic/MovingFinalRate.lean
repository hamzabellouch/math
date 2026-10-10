import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyBudget
import OAI.NumberTheory.Ostmann.Arithmetic.MovingStatisticDecay

namespace OAI

/-! # Specializing the final decay to the actual frequency rate -/

namespace Ostmann
open Filter

theorem eventually_moving_frequency_rate_margin (Bs BD Bz B : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      movingFrequencyRate Bs BD Bz ((k : ℝ) ^ 4) k +
        (2 : ℝ) ^ k * (-(3 / 4 : ℝ) * Real.log ((2 : ℝ) ^ k) + 5 / 4) +
        ((2 : ℝ) ^ k * (Bs + 8 * Real.log ((k : ℝ) ^ 4)) +
          (Real.log 12 + 1) * (2 : ℝ) ^ k + 1) <
        -((2 * B + 1) * (2 : ℝ) ^ k) := by
  filter_upwards [eventually_moving_final_gap Bs BD Bz (Real.log 12 + 21 / 4) B] with k hk
  have hr : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hh := mul_lt_mul_of_pos_left hk (show 0 < (2 : ℝ) ^ k by positivity)
  unfold movingFrequencyRate
  nlinarith only [hh, hr]

theorem bulk_exponential_lower_contradicts_decay (B r m : ℝ) (hm : 0 < m) (hr : 0 < r)
    (η : ℂ) (hlower : Real.exp (-B * r * m) ≤ ‖η‖)
    (hupper : ‖η‖ ^ 2 ≤ Real.exp (-((2 * B + 1) * r) * m)) : False := by
  have hs := pow_le_pow_left₀ (Real.exp_pos (-B * r * m)).le hlower 2
  have heq : Real.exp (-B * r * m) ^ 2 = Real.exp (-(2 * B * r) * m) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hs
  have hlt : Real.exp (-((2 * B + 1) * r) * m) < Real.exp (-(2 * B * r) * m) :=
    Real.exp_lt_exp.mpr (by nlinarith [mul_pos hr hm])
  exact (not_lt_of_ge (hs.trans hupper)) hlt

/-- The precise numerical upper bound already proved for the selected-prior
statistic contradicts the lower bound preserved by the transfer iteration. -/
theorem eventually_moving_numeric_contradiction (Bs BD Bz B C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop, ∀ᶠ L : ℝ in atTop,
      let m := spectatorBulkCount k L
      let r : ℝ := (2 : ℝ) ^ k
      let z : ℝ := (k : ℝ) ^ 4
      let A := movingFrequencyRate Bs BD Bz z k
      let D := Bs + 8 * Real.log z
      ∀ V : ℕ, (V : ℝ) ≤ Real.exp (A * m) → 0 ≤ A →
      ∀ Δ : ℝ, Δ ≤ D * m → ∀ η : ℂ,
      Real.exp (-B * r * m) ≤ ‖η‖ →
      ‖η‖ ^ 2 ≤ C * (2 * V + 1 : ℕ) * Real.exp 2 *
        (((((2 ^ k + 1) * (2 ^ k) ^ (2 * 2 ^ k) : ℕ) : ℝ)) *
          Real.exp (r * m * (-(3 / 4 : ℝ) * Real.log ((2 : ℝ) ^ k) + 5 / 4)) *
            (Real.exp (r * Δ + (Real.log 12 + 1) * r * m + m) +
              5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
          Real.exp (-(A + (2 * B + 1) * r + 1) * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) → False := by
  filter_upwards [eventually_moving_frequency_rate_margin Bs BD Bz B,
    eventually_ge_atTop (1 : ℕ)] with k hmargin hk
  let A := movingFrequencyRate Bs BD Bz ((k : ℝ) ^ 4) k
  by_cases hA : 0 ≤ A
  · have hd := eventually_moving_statistic_decay_with_base k hk ((2 : ℝ) ^ k) C
      (((2 ^ k + 1) * (2 ^ k) ^ (2 * 2 ^ k) : ℕ) : ℝ) A
      (-(3 / 4 : ℝ) * Real.log ((2 : ℝ) ^ k) + 5 / 4)
      (Bs + 8 * Real.log ((k : ℝ) ^ 4)) 1 (A + (2 * B + 1) * (2 : ℝ) ^ k + 1)
      ((2 * B + 1) * (2 : ℝ) ^ k) (by positivity) hC (by positivity) hA hmargin (by dsimp only [A]; linarith)
    filter_upwards [hd, (spectatorBulkCount_tendsto k hk).eventually (eventually_gt_atTop (0 : ℝ))]
      with L hd hm
    dsimp only
    intro V hV _ Δ hΔ η hlower hupper
    apply bulk_exponential_lower_contradicts_decay B ((2 : ℝ) ^ k)
      (spectatorBulkCount k L) hm (by positivity) η hlower
    apply hd V hV Δ hΔ η
    simpa only [one_mul] using hupper
  · exact Filter.Eventually.of_forall (fun L V _ hA' => (hA hA').elim)

end Ostmann

end OAI
