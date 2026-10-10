import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # Exponential decay of the full selected-statistic bound at fixed depth -/

namespace Ostmann
open Filter

/-- Fixed constants are absorbed by a strict linear-exponent margin. -/
theorem eventually_bulk_exp_margin (k : ℕ) (hk : 0 < k) (K a b : ℝ)
    (hK : 0 ≤ K) (hab : a < b) :
    ∀ᶠ L : ℝ in atTop, K * Real.exp (a * spectatorBulkCount k L) ≤
      Real.exp (b * spectatorBulkCount k L) := by
  filter_upwards [(spectatorBulkCount_tendsto k hk).eventually
    (eventually_ge_atTop (Real.log (K + 1) / (b - a)))] with L hL
  have hmargin := (div_le_iff₀ (sub_pos.mpr hab)).mp hL
  calc
    _ ≤ (K + 1) * Real.exp (a * spectatorBulkCount k L) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = Real.exp (Real.log (K + 1) + a * spectatorBulkCount k L) := by
      rw [Real.exp_add, Real.exp_log (by linarith)]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- The retained arithmetic error beats every fixed exponential in the bulk size. -/
theorem eventually_bulk_arithmetic_error (k : ℕ) (T : ℝ) :
    ∀ᶠ L : ℝ in atTop, Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) ≤
      Real.exp (-T * spectatorBulkCount k L) := by
  let C := max T 0 * (k : ℝ) ^ 4
  have hC : 0 ≤ C := mul_nonneg (le_max_right _ _) (by positivity)
  filter_upwards [arithmetic_exponent_absorption 0 (12 / 10000) 0 C 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  have hm : T * spectatorBulkCount k L ≤ C * L := by
    apply (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)).trans
    exact (mul_le_mul_of_nonneg_left (spectatorBulkCount_upper k L hL0)
      (le_max_right _ _)).trans_eq (by dsimp only [C]; ring)
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one, one_mul] at hL
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hC hL0]

theorem eventually_scaled_bulk_arithmetic_error (k : ℕ) (hk : 0 < k)
    (K a T : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop,
      K * Real.exp (a * spectatorBulkCount k L) *
        Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) ≤
      Real.exp (-T * spectatorBulkCount k L) := by
  filter_upwards [eventually_bulk_arithmetic_error k (a + T + 1),
    eventually_bulk_exp_margin k hk K (-(T + 1)) (-T) hK (by linarith)] with L herror hmargin
  apply le_trans (mul_le_mul_of_nonneg_left herror
    (mul_nonneg hK (Real.exp_pos _).le))
  have heq : K * Real.exp (a * spectatorBulkCount k L) *
      Real.exp (-(a + T + 1) * spectatorBulkCount k L) =
      K * Real.exp (-(T + 1) * spectatorBulkCount k L) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rwa [heq]

/-- This is the numerical bound occurring in the selected-prior theorem,
including the root-frequency mass and all five arithmetic errors. -/
theorem eventually_moving_statistic_decay (k : ℕ) (hk : 0 < k)
    (C K A badRate diagRate gain T : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hbad : A + badRate + diagRate < -T) (hgood : A - gain < -T) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ V : ℕ, (V : ℝ) ≤ Real.exp (A * m) → ∀ η : ℂ,
      ‖η‖ ^ 2 ≤ C * (2 * V + 1 : ℕ) * Real.exp 2 *
        (K * Real.exp (badRate * m) *
          (Real.exp (diagRate * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
          Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) →
      ‖η‖ ^ 2 ≤ Real.exp (-T * m) := by
  let K₀ := 3 * C * Real.exp 2
  have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  filter_upwards [eventually_bulk_exp_margin k hk (4 * K₀ * K)
      (A + badRate + diagRate) (-T) (by positivity) hbad,
    eventually_bulk_exp_margin k hk (4 * K₀) (A - gain) (-T) (by positivity) hgood,
    eventually_scaled_bulk_arithmetic_error k hk (4 * (5 * K₀ * K)) (A + badRate) T (by positivity),
    eventually_scaled_bulk_arithmetic_error k hk (4 * (5 * K₀)) A T (by positivity)]
    with L h₁ h₃ h₂ h₄
  dsimp only
  intro V hV η hη
  let m := spectatorBulkCount k L
  have hmass : ((2 * V + 1 : ℕ) : ℝ) ≤ 3 * Real.exp (A * m) := by
    have he : 1 ≤ Real.exp (A * m) := Real.one_le_exp (mul_nonneg hA (Nat.cast_nonneg _))
    push_cast
    dsimp only [m] at he ⊢
    linarith
  have hupper := hη.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hC) (Real.exp_pos _).le)
    (by positivity))
  have heq : C * (3 * Real.exp (A * m)) * Real.exp 2 *
        (K * Real.exp (badRate * m) *
          (Real.exp (diagRate * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
          Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) =
      K₀ * K * Real.exp ((A + badRate + diagRate) * m) +
      5 * K₀ * K * Real.exp ((A + badRate) * m) * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) +
      K₀ * Real.exp ((A - gain) * m) +
      5 * K₀ * Real.exp (A * m) * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
    dsimp only [K₀]
    simp only [add_mul, sub_mul, Real.exp_add, Real.exp_sub, Real.exp_neg, neg_mul]
    ring
  change ‖η‖ ^ 2 ≤ C * (3 * Real.exp (A * m)) * Real.exp 2 * _ at hupper
  rw [heq] at hupper
  dsimp only [m] at hupper
  nlinarith only [hupper, h₁, h₂, h₃, h₄]

/-- Substitute the original bottom gap before applying the exponential margin. -/
theorem eventually_moving_statistic_decay_with_base (k : ℕ) (hk : 0 < k)
    (r C K A badRate D ε gain T : ℝ)
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hbad : A + r * badRate + (r * D + (Real.log 12 + 1) * r + ε) < -T)
    (hgood : A - gain < -T) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ V : ℕ, (V : ℝ) ≤ Real.exp (A * m) → ∀ Δ : ℝ, Δ ≤ D * m → ∀ η : ℂ,
      ‖η‖ ^ 2 ≤ C * (2 * V + 1 : ℕ) * Real.exp 2 *
        (K * Real.exp (r * m * badRate) *
          (Real.exp (r * Δ + (Real.log 12 + 1) * r * m + ε * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
          Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) →
      ‖η‖ ^ 2 ≤ Real.exp (-T * m) := by
  filter_upwards [eventually_moving_statistic_decay k hk C K A (r * badRate)
    (r * D + (Real.log 12 + 1) * r + ε) gain T hC hK hA hbad hgood] with L hd
  dsimp only at hd ⊢
  rw [show (r * badRate) * (spectatorBulkCount k L : ℝ) =
    r * spectatorBulkCount k L * badRate by ring] at hd
  intro V hV Δ hΔ η hη
  have hb : Real.exp (r * Δ + (Real.log 12 + 1) * r * spectatorBulkCount k L +
      ε * spectatorBulkCount k L) ≤
      Real.exp ((r * D + (Real.log 12 + 1) * r + ε) * spectatorBulkCount k L) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hΔ hr]
  let err := 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))
  have hi := mul_le_mul_of_nonneg_left (add_le_add hb (le_refl err))
    (mul_nonneg hK (Real.exp_pos (r * spectatorBulkCount k L * badRate)).le)
  have hi' := add_le_add
    (add_le_add hi (le_refl (Real.exp (-gain * spectatorBulkCount k L)))) (le_refl err)
  exact hd V hV η (hη.trans (mul_le_mul_of_nonneg_left hi'
    (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (Real.exp_pos 2).le)))

end Ostmann

end OAI
