import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace OAI

/-! # The numerical contradiction between coverage and contraction -/
namespace Ostmann

 theorem coverage_energy_size_bound (S c U X α T r D m : ℝ)
    (_hS : 0 ≤ S) (hc : 0 ≤ c) (hU : 0 ≤ U) (hX : 0 ≤ X) (_hα : 0 ≤ α)
    (hT : 0 ≤ T) (hr : 0 ≤ r) (_hD : 0 ≤ D)
    (hcover : c * U * X ≤ T * S)
    (henergy : α ^ 2 * S ^ 2 ≤ r ^ 2 * D ^ 2 * m)
    (hsize : α ^ 2 * m ≤ D ^ 2) :
    c * U * X * α ^ 2 ≤ T * r * D ^ 2 := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    (c * U * X * α ^ 2) ^ 2 ≤ (T * S * α ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right hcover (sq_nonneg _)) 2
    _ = T ^ 2 * α ^ 2 * (α ^ 2 * S ^ 2) := by ring
    _ ≤ T ^ 2 * α ^ 2 * (r ^ 2 * D ^ 2 * m) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = T ^ 2 * r ^ 2 * D ^ 2 * (α ^ 2 * m) := by ring
    _ ≤ T ^ 2 * r ^ 2 * D ^ 2 * D ^ 2 :=
      mul_le_mul_of_nonneg_left hsize (by positivity)
    _ = (T * r * D ^ 2) ^ 2 := by ring

open Filter

theorem eventual_sparse_coverage_margin (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      18432 * Real.exp (L - (8 / 5 : ℝ) * ((17 / 25 : ℝ) * L) +
        2 * L ^ (3 / 4 : ℝ)) < c := by
  have hs := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).eventually_le_const
    (show (0 : ℝ) < 11 / 500 by norm_num)
  have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop (show (0 : ℝ) < 11 / 250 by norm_num))).eventually_lt_const
      (show 0 < c / 18432 by positivity)
  filter_upwards [hs, he, eventually_ge_atTop (1 : ℝ)] with L hsmall hexp hL
  have hLp : 0 < L := by linarith
  have hpow : L ^ (3 / 4 : ℝ) = L * L ^ (-(1 / 4 : ℝ)) := by
    nth_rw 2 [← Real.rpow_one L]
    rw [← Real.rpow_add hLp]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hsmall hLp.le
  have hbound : L - (8 / 5 : ℝ) * ((17 / 25 : ℝ) * L) + 2 * L ^ (3 / 4 : ℝ) ≤
      -(11 / 250 : ℝ) * L := by
    rw [hpow]
    linarith
  calc
    _ ≤ 18432 * Real.exp (-(11 / 250 : ℝ) * L) := by
      gcongr
    _ < c := by
      have hh := mul_lt_mul_of_pos_left hexp (show (0 : ℝ) < 18432 by norm_num)
      simpa only [Function.comp_apply, id_eq, neg_mul, mul_div_cancel₀ _ (by norm_num : (18432 : ℝ) ≠ 0)] using hh

end Ostmann

end OAI
