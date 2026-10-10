import OAI.NumberTheory.Ostmann.QuadraticCenter.RankinExponentialBound

namespace OAI

/-! # Specializing the high-weight Rankin parameter at the manuscript's exponents -/

namespace Ostmann

open Filter Asymptotics

theorem rankin_parameter_budget (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ u : ℝ, 2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      Real.log u ≤ Real.log T / 100000 ∧
      Real.log u + Real.log T / 4 + C * u ^ 2 * T ^ (1 / 4 : ℝ) * (1 + Real.log T) ≤
        T ^ (9999999 / 10000000 : ℝ) := by
  let μ : ℝ := 1 / 1000000
  let a : ℝ := 1 / 4 + 2 * μ
  let κ : ℝ := 9999999 / 10000000
  let D : ℝ := 1 + 16 * C
  have hD : 0 < D := by dsimp [D]; positivity
  have hδ : 0 < κ - a := by norm_num [κ, a, μ]
  have hlog := (isLittleO_log_rpow_atTop hδ).bound (show 0 < 1 / (2 * D) by positivity)
  have hpow := (tendsto_rpow_atTop hδ).eventually_ge_atTop (2 * D)
  have hloglarge := Real.tendsto_log_atTop.eventually_ge_atTop (1000000 : ℝ)
  filter_upwards [hlog, hpow, hloglarge, eventually_ge_atTop (1 : ℝ)] with T hl hp hlbig hT u hu huU
  have hT0 : 0 < T := by linarith
  have hu0 : 0 < u := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hulog : Real.log u ≤ 3 + μ * Real.log T := by
    calc
      _ ≤ Real.log (4 * T ^ μ) := Real.log_le_log hu0 huU
      _ = Real.log 4 + μ * Real.log T := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hT0 μ).ne', Real.log_rpow hT0]
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hlu : Real.log u ≤ Real.log T / 100000 := by
    dsimp [μ] at hulog
    linarith
  refine ⟨hlu, ?_⟩
  have hTa : 1 ≤ T ^ a := Real.one_le_rpow hT (by dsimp [a, μ]; positivity)
  have hsquare : u ^ 2 * T ^ (1 / 4 : ℝ) ≤ 16 * T ^ a := by
    calc
      _ ≤ (4 * T ^ μ) ^ 2 * T ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu0.le huU 2) (by positivity)
      _ = 16 * (T ^ μ * T ^ μ * T ^ (1 / 4 : ℝ)) := by ring
      _ = 16 * T ^ a := by
        rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
        congr 2
        dsimp [a]
        ring
  have hupper : Real.log u + Real.log T / 4 + C * u ^ 2 * T ^ (1 / 4 : ℝ) * (1 + Real.log T) ≤
      D * T ^ a * (1 + Real.log T) := by
    have hlogu : Real.log u + Real.log T / 4 ≤ 1 + Real.log T := by
      dsimp [μ] at hulog
      nlinarith
    have hlin : 1 + Real.log T ≤ T ^ a * (1 + Real.log T) := by
      exact le_mul_of_one_le_left (by positivity) hTa
    have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare hC)
      (show 0 ≤ 1 + Real.log T by positivity)
    calc
      _ ≤ (1 + Real.log T) + C * (16 * T ^ a) * (1 + Real.log T) := by
        convert add_le_add hlogu he using 1
        ring
      _ ≤ T ^ a * (1 + Real.log T) + C * (16 * T ^ a) * (1 + Real.log T) :=
        add_le_add_left hlin _
      _ = D * T ^ a * (1 + Real.log T) := by dsimp [D]; ring
  have hl' : Real.log T ≤ 1 / (2 * D) * T ^ (κ - a) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogT,
      abs_of_nonneg (Real.rpow_nonneg hT0.le _)] using hl
  have hc' : (1 : ℝ) ≤ 1 / (2 * D) * T ^ (κ - a) := by
    rw [one_div_mul_eq_div]
    exact (one_le_div (by positivity : 0 < 2 * D)).mpr hp
  apply hupper.trans
  calc
    _ ≤ D * T ^ a * (1 / D * T ^ (κ - a)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have he : 1 / D * T ^ (κ - a) =
          1 / (2 * D) * T ^ (κ - a) + 1 / (2 * D) * T ^ (κ - a) := by
        field_simp
        ring
      have hh : 1 + Real.log T ≤ 1 / D * T ^ (κ - a) := by linarith
      exact hh
    _ = T ^ κ := by
      have hprod : T ^ a * T ^ (κ - a) = T ^ κ := by
        rw [← Real.rpow_add hT0]
        congr 1
        ring
      calc
        _ = T ^ a * T ^ (κ - a) := by field_simp
        _ = _ := hprod

end Ostmann

end OAI
