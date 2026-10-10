import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCommonFinalBand

namespace OAI

/-! The existing MRT first-band budget supplies the alternative needed
for the common final-band construction. No separate second-band-size
hypothesis is required. -/

namespace TwoPointCorrelations

open Filter Finset

lemma mrt_final_band_budget_alternative :
    ∀ᶠ L : ℝ in atTop, ∀ P Q : ℝ, 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      400*Real.log L+1 ≤ Real.log P ∨
        Real.log (mrtBandUpper Q 2) ≤ Real.sqrt L := by
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<249/500 by norm_num)).eventually
    (eventually_ge_atTop (1024:ℝ))
  filter_upwards [hp,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with L hp hL hlogL
  have hL0 : 0 < L := by linarith
  intro P Q hQ hbudget
  by_cases hfirst : 400*Real.log L+1 ≤ Real.log P
  · exact Or.inl hfirst
  right
  have hnot : Real.log P < 400*Real.log L+1 := lt_of_not_ge hfirst
  have hsmall : Real.log (Real.log Q) ≤ Real.log L/1000 := by linarith
  have hQ0 : 0 < Real.log Q := by linarith
  have hq : Real.log Q ≤ L^(1/1000:ℝ) := by
    calc
      _ = Real.exp (Real.log (Real.log Q)) := (Real.exp_log hQ0).symm
      _ ≤ Real.exp (Real.log L/1000) := Real.exp_le_exp.mpr hsmall
      _ = _ := by rw [Real.rpow_def_of_pos hL0]; congr 1; ring
  have hu : Real.log (mrtBandUpper Q 2) ≤ 1024*L^(1/500:ℝ) := by
    have hs := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log Q) hq 2
    have he : (L^(1/1000:ℝ))^2=L^(1/500:ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
      norm_num
    rw [he] at hs
    have hm := mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤1024)
    have heq : Real.log (mrtBandUpper Q 2)=1024*(Real.log Q)^2 := by
      norm_num [mrtBandUpper]
    rw [heq]
    exact hm
  apply hu.trans
  calc
    1024*L^(1/500:ℝ) ≤ L^(249/500:ℝ)*L^(1/500:ℝ) :=
      mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hL0.le _)
    _ = Real.sqrt L := by rw [← Real.rpow_add hL0,Real.sqrt_eq_rpow]; norm_num

theorem mrt_common_final_band_from_budget :
    ∀ᶠ N : ℕ in atTop, ∀ P Q : ℝ,
      1 ≤ Real.log P → 1 ≤ Real.log Q → Real.log Q ≤ Real.sqrt (Real.log N) →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      ∃ J : ℕ, 1 ≤ J ∧
        Real.sqrt (Real.log N) < Real.log (mrtBandUpper Q (J+1)) ∧
        ∀ k ∈ ({N,2*N} : Finset ℕ),
          200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
          ∀ i ∈ Icc 1 J, mrtBandUpper Q i ≤ Real.exp (Real.sqrt (Real.log k)) := by
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [mrt_common_final_band_geometry,hlog.eventually mrt_final_band_budget_alternative]
    with N hgeometry hbudget
  intro P Q hP hQ hQu hsize
  exact hgeometry P Q hP hQ hQu (hbudget P Q hQ hsize)

end TwoPointCorrelations

end OAI
