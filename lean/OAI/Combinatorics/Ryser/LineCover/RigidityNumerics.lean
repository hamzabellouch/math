import OAI.Combinatorics.Ryser.LineCover.TailNumerics
import Mathlib.Tactic.FieldSimp

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

def rigidityBudget (D : ℕ) (κ q : ℝ) : ℝ :=
  2 * q ^ (3 / 2 + κ / 10) + ((D : ℝ) + 2) * q

theorem rigidityBudget_eq_errors (D : ℕ) {κ q : ℝ} (hq : 0 < q) :
    rigidityBudget D κ q =
      q ^ (3 / 2 + κ / 10) + q * ((D : ℝ) + q ^ (1 / 2 + κ / 10)) + 2 * q := by
  have hmul : q * q ^ (1 / 2 + κ / 10) = q ^ (3 / 2 + κ / 10) := by
    calc
      _ = q ^ (1 : ℝ) * q ^ (1 / 2 + κ / 10) := by rw [Real.rpow_one]
      _ = q ^ ((1 : ℝ) + (1 / 2 + κ / 10)) := (Real.rpow_add hq _ _).symm
      _ = _ := by congr 1; ring
  unfold rigidityBudget
  rw [mul_add, hmul]
  ring

theorem rigidityBudget_nonneg (D : ℕ) (κ : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ rigidityBudget D κ q := by
  unfold rigidityBudget
  positivity

theorem rigidityBudget_le (D : ℕ) {κ q : ℝ} (hκ : 0 ≤ κ) (hq : 1 ≤ q) :
    rigidityBudget D κ q ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10) := by
  have hpow : q ≤ q ^ (3 / 2 + κ / 10) := by
    calc
      q = q ^ (1 : ℝ) := (Real.rpow_one q).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (D : ℝ) + 2 by positivity)
  unfold rigidityBudget
  nlinarith only [hmul]

private theorem eventually_mul_rpow_le_mul (C c a b : ℝ)
    (hc : 0 < c) (hab : a < b) :
    ∀ᶠ q : ℝ in atTop, C * q ^ a ≤ c * q ^ b := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hgap).eventually_ge_atTop (C / c)] with q hq hlarge
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hC : C ≤ q ^ (b - a) * c := (div_le_iff₀ hc).mp hlarge
  calc
    C * q ^ a ≤ (q ^ (b - a) * c) * q ^ a :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hqpos.le _)
    _ = c * q ^ b := by
      rw [mul_comm (q ^ (b - a)) c, mul_assoc, ← Real.rpow_add hqpos]
      rw [show b - a + a = b by ring]

private theorem eventually_rigidityBudget_div_le (D : ℕ) {δ c κ : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hκ : 0 ≤ κ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop, rigidityBudget D κ q / (δ * q) ≤ c * q / 2 := by
  have hsmall := eventually_mul_rpow_le_mul ((D : ℝ) + 4) (δ * c / 2)
    (3 / 2 + κ / 10) 2 (by positivity) (by linarith)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall] with q hq hsmallq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  apply (div_le_iff₀ (mul_pos hδ hqpos)).2
  calc
    rigidityBudget D κ q ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10) :=
      rigidityBudget_le D hκ hq
    _ ≤ (δ * c / 2) * q ^ (2 : ℝ) := hsmallq
    _ = (c * q / 2) * (δ * q) := by rw [Real.rpow_two]; ring

theorem eventually_rigidityBudget_div_le_min (D : ℕ) {δ ρ κ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hκ : 0 < κ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop,
      rigidityBudget D κ q / (δ * q) ≤ min (q / 2) (ρ * q / 2) := by
  filter_upwards [eventually_rigidityBudget_div_le D hδ zero_lt_one hκ.le hκmax,
    eventually_rigidityBudget_div_le D hδ hρ hκ.le hκmax] with q hleft hright
  exact le_min (by simpa only [one_mul] using hleft) hright

theorem eventually_rigidity_heavy_bounds (D : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop,
      1 < q ^ (1 / 2 - κ / 3) ∧
        rigidityBudget D κ q / (q ^ (1 / 2 - κ / 3) - 1) ≤ q ^ (1 + κ) := by
  have hd : 0 < (1 / 2 : ℝ) - κ / 3 := by linarith
  have hgap : (3 / 2 : ℝ) + κ / 10 < (1 + κ) + (1 / 2 - κ / 3) := by
    linarith
  have hsmall := eventually_mul_rpow_le_mul (2 * ((D : ℝ) + 4)) 1
    (3 / 2 + κ / 10) ((1 + κ) + (1 / 2 - κ / 3)) zero_lt_one hgap
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hd).eventually_ge_atTop 2, hsmall]
      with q hq hT hsmallq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [one_mul, Real.rpow_add hqpos (1 + κ) (1 / 2 - κ / 3)] at hsmallq
  have hscaled := mul_le_mul_of_nonneg_left hT
    (Real.rpow_nonneg hqpos.le (1 + κ))
  constructor
  · linarith
  · apply (div_le_iff₀ (by linarith : 0 < q ^ (1 / 2 - κ / 3) - 1)).2
    calc
      rigidityBudget D κ q ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10) :=
        rigidityBudget_le D hκ.le hq
      _ ≤ q ^ (1 + κ) * (q ^ (1 / 2 - κ / 3) - 1) := by
        nlinarith only [hsmallq, hscaled]

theorem eventually_line_error_le_half {δ κ : ℝ}
    (hδ : 0 < δ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop, q ^ (1 / 2 + κ / 10) ≤ δ * q / 2 := by
  have hsmall := eventually_mul_rpow_le_mul 1 (δ / 2) (1 / 2 + κ / 10) 1
    (by positivity) (by linarith)
  filter_upwards [hsmall] with q hsmallq
  calc
    q ^ (1 / 2 + κ / 10) ≤ (δ / 2) * q ^ (1 : ℝ) := by
      simpa only [one_mul] using hsmallq
    _ = δ * q / 2 := by rw [Real.rpow_one]; ring

theorem pair_mass_ratio_le_coarse (D : ℕ) {q κ m B R P : ℝ}
    (hq : 1 ≤ q)
    (hB : B ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10))
    (hR : R ≤ q ^ (1 / 2 + κ / 4)) (hm : q / 2 ≤ m)
    (hP : P ≤ q ^ (1 / 2 - κ / 3) * B + R * q ^ (3 / 2 - κ)) :
    P / m ^ 2 ≤
      4 * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4))) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have he₁ : (1 / 2 - κ / 3) + (3 / 2 + κ / 10) = 2 - 7 * κ / 30 := by ring
  have he₂ : (1 / 2 + κ / 4) + (3 / 2 - κ) = 2 - 3 * κ / 4 := by ring
  have hnum : P ≤ ((D : ℝ) + 4) * q ^ (2 - 7 * κ / 30) +
      q ^ (2 - 3 * κ / 4) := by
    calc
      P ≤ q ^ (1 / 2 - κ / 3) * B + R * q ^ (3 / 2 - κ) := hP
      _ ≤ q ^ (1 / 2 - κ / 3) * (((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10)) +
          q ^ (1 / 2 + κ / 4) * q ^ (3 / 2 - κ) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hqpos.le _))
          (mul_le_mul_of_nonneg_right hR (Real.rpow_nonneg hqpos.le _))
      _ = _ := by
        rw [mul_left_comm (q ^ (1 / 2 - κ / 3)) ((D : ℝ) + 4)
          (q ^ (3 / 2 + κ / 10))]
        simp only [← Real.rpow_add hqpos, he₁, he₂]
  have hden : (q / 2) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by positivity) hm 2
  have hdiv (a : ℝ) : q ^ a / q ^ 2 = q ^ (a - 2) :=
    (Real.rpow_sub_natCast hqpos.ne' a 2).symm
  calc
    P / m ^ 2 ≤
        (((D : ℝ) + 4) * q ^ (2 - 7 * κ / 30) + q ^ (2 - 3 * κ / 4)) /
          (q / 2) ^ 2 :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 4 * (((D : ℝ) + 4) * (q ^ (2 - 7 * κ / 30) / q ^ 2) +
        q ^ (2 - 3 * κ / 4) / q ^ 2) := by
      field_simp [hqpos.ne']
      ring
    _ = _ := by
      rw [hdiv (2 - 7 * κ / 30), hdiv (2 - 3 * κ / 4),
        show (2 - 7 * κ / 30) - 2 = -(7 * κ / 30) by ring,
        show (2 - 3 * κ / 4) - 2 = -(3 * κ / 4) by ring]

theorem rigidity_pair_ratio_le (D : ℕ) {q κ m E R P : ℝ}
    (hq : 1 ≤ q) (hκ : 0 ≤ κ) (hm : q / 2 ≤ m)
    (hR : R ≤ q ^ (1 / 2 + κ / 4)) (hE : E ≤ rigidityBudget D κ q)
    (hpair : P ≤ q ^ (1 / 2 - κ / 3) * E + R * q ^ (3 / 2 - κ)) :
    P / m ^ 2 ≤
      4 * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4))) :=
  pair_mass_ratio_le_coarse D hq (hE.trans (rigidityBudget_le D hκ hq)) hR hm hpair

end RyserCoveringCounterexample.LineCover

end

end OAI
