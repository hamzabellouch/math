import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandParameters

namespace OAI

/-! The actual number of original bands costs only a small logarithmic
power in the inclusion-exclusion cofactor estimate. -/
namespace TwoPointCorrelations

open Filter

theorem halasz_band_power_cost :
    ∀ᶠ L : ℝ in atTop, ∀ (Q : ℝ) (J : ℕ), 1 ≤ Real.log Q →
      Real.log (mrtBandUpper Q J) ≤ 2*Real.sqrt L →
      (2:ℝ)^J ≤ L^(1/1000:ℝ) := by
  filter_upwards [eventually_ge_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000*Real.exp 1000))]
    with L hL hlogL
  intro Q J hQ hU
  have hL0 : 0 < L := by linarith
  have hsqrt : 2*Real.sqrt L ≤ L := by
    have hh : Real.sqrt L ≤ L/2 := (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩
    linarith
  have hlog2u : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hJ : (J:ℝ)*Real.log 2 ≤ Real.log L/1000 := by
    by_cases hj : (J:ℝ) ≤ Real.exp 1000
    · calc
        _ ≤ (J:ℝ) := mul_le_of_le_one_right (Nat.cast_nonneg _) hlog2u
        _ ≤ Real.exp 1000 := hj
        _ ≤ _ := by linarith
    · have hjbig : Real.exp 1000 ≤ (J:ℝ) := le_of_not_ge hj
      have hj0 : (0:ℝ) < J := (Real.exp_pos _).trans_le hjbig
      have hj1 : (1:ℝ) ≤ J :=
        (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1000)).trans hjbig
      have hjlog : 1000 ≤ Real.log (J:ℝ) := by
        simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1000) hjbig
      have hjpow : (J:ℝ)^J ≤ Real.log (mrtBandUpper Q J) := by
        rw [mrtBandUpper,Real.log_exp]
        calc
          _ ≤ (J:ℝ)^(4*J+2) := pow_le_pow_right₀ hj1 (by omega)
          _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hQ)
      have hJlog : (J:ℝ)*Real.log (J:ℝ) ≤ Real.log L := by
        have hh := Real.log_le_log (pow_pos hj0 J)
          (hjpow.trans (hU.trans hsqrt))
        simpa only [Real.log_pow] using hh
      have hh := mul_le_mul_of_nonneg_left hjlog (Nat.cast_nonneg J : (0:ℝ) ≤ J)
      nlinarith
  rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
    Real.rpow_def_of_pos hL0]
  apply Real.exp_le_exp.mpr
  nlinarith

end TwoPointCorrelations

end OAI
