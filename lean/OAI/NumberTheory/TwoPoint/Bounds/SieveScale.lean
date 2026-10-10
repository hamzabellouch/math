import OAI.NumberTheory.TwoPoint.Bounds.SieveBoundary
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! The logarithmic truncation length is negligible compared with the
physical interval exponent in the finite rough sieve. -/

namespace TwoPointCorrelations

open Filter

/-- Any fixed `exp(O(L^.99 log L))` counting cost is absorbed by the
interval length `exp(L^.995)`, with the explicit power needed below. -/
theorem eventually_sieve_boundary_exponent (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (K * L ^ (99 / 100 : ℝ) * Real.log L - L ^ (199 / 200 : ℝ)) ≤
        L ^ (-100 : ℝ) := by
  have hden : 0 < K + 100 := by linarith
  have hs := (isLittleO_log_rpow_atTop
    (show 0 < (1 / 200 : ℝ) by norm_num)).bound (show 0 < 1 / (K + 100) by positivity)
  filter_upwards [eventually_ge_atTop 1, hs] with L hL hsL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hsL
  have hc : Real.log L * (K + 100) ≤ L ^ (1 / 200 : ℝ) := by
    apply (le_div_iff₀ hden).mp
    convert hsL using 1
    ring
  have hm := mul_le_mul_of_nonneg_right hc
    (Real.rpow_nonneg hLp.le (99 / 100 : ℝ))
  have he : L ^ (1 / 200 : ℝ) * L ^ (99 / 100 : ℝ) = L ^ (199 / 200 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  rw [he] at hm
  have hx : 1 ≤ L ^ (99 / 100 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hlogx : 100 * Real.log L ≤ 100 * L ^ (99 / 100 : ℝ) * Real.log L := by
    have hh := mul_le_mul_of_nonneg_right hx (show 0 ≤ 100 * Real.log L by positivity)
    nlinarith only [hh]
  rw [Real.rpow_def_of_pos hLp (-100 : ℝ)]
  apply Real.exp_le_exp.mpr
  nlinarith

end TwoPointCorrelations

end OAI
