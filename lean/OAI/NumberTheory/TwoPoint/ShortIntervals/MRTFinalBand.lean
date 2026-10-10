import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMaximalBand
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFinalSampleScale

namespace OAI

/-! The actual finite band family ending below exp(sqrt(log N)). Its
final lower endpoint is large enough for the optimized sample estimate. -/

namespace TwoPointCorrelations

open Filter Finset

lemma mrt_eventually_final_band_target :
    ∀ᶠ L : ℝ in atTop, (200*Real.log L+1)^3 ≤ Real.sqrt L := by
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/6 by norm_num)).bound
    (show (0:ℝ)<1/400 by norm_num)
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<1/6 by norm_num)).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [hb,hp,eventually_ge_atTop (1:ℝ)] with L hb hp hL
  have hL0 : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hL),Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hb
  have hh : 200*Real.log L+1 ≤ L^(1/6:ℝ) := by linarith
  calc
    _ ≤ (L^(1/6:ℝ))^3 := pow_le_pow_left₀ (by positivity) hh 3
    _ = Real.sqrt L := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le,Real.sqrt_eq_rpow]
      norm_num

/-- P and Q may vary with L. The disjunction handles the possible
one-band family without assuming a large second band exists. -/
theorem mrt_final_band_geometry :
    ∀ᶠ L : ℝ in atTop, ∀ P Q : ℝ,
    1 ≤ Real.log P → 1 ≤ Real.log Q → Real.log Q ≤ Real.sqrt L →
    (200*Real.log L+1 ≤ Real.log P ∨
      Real.log (mrtBandUpper Q 2) ≤ Real.sqrt L) →
    ∃ J : ℕ, 1 ≤ J ∧
      200*Real.log L+1 ≤ Real.log (mrtBandLower P Q J) ∧
      Real.sqrt L < Real.log (mrtBandUpper Q (J+1)) ∧
      ∀ j ∈ Icc 1 J, Real.log (mrtBandUpper Q j) ≤ Real.sqrt L := by
  filter_upwards [mrt_eventually_final_band_target] with L hL
  intro P Q hP hQ hQupper hfirst
  exact mrt_maximal_band_lower hP hQ hQupper hL hfirst

/-- For fixed initial bands, the second-band alternative eventually
holds. Thus no growing initial lower endpoint is needed in this case. -/
theorem mrt_final_band_geometry_fixed (P Q : ℝ)
    (hP : 1 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) :
    ∀ᶠ L : ℝ in atTop, ∃ J : ℕ, 1 ≤ J ∧
      200*Real.log L+1 ≤ Real.log (mrtBandLower P Q J) ∧
      Real.sqrt L < Real.log (mrtBandUpper Q (J+1)) ∧
      ∀ j ∈ Icc 1 J, Real.log (mrtBandUpper Q j) ≤ Real.sqrt L := by
  have hs := Real.tendsto_sqrt_atTop.eventually
    (eventually_ge_atTop (max (Real.log Q) (Real.log (mrtBandUpper Q 2))))
  filter_upwards [mrt_final_band_geometry,hs] with L hL hs
  exact hL P Q hP hQ ((le_max_left _ _).trans hs)
    (Or.inr ((le_max_right _ _).trans hs))

end TwoPointCorrelations

end OAI
