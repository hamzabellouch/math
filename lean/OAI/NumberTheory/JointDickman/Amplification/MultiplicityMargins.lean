import OAI.NumberTheory.JointDickman.Amplification.LargeMultiplicityExponent
import OAI.NumberTheory.JointDickman.Amplification.MultiplicityParameters

namespace OAI

/-! # Compatible small and large multiplicity parameters -/

namespace JointDickman
open Filter
open scoped Topology

theorem largeMultiplicityLoss_tendsto (Δ δ ε : ℝ) :
    Tendsto (fun τ : ℝ => largeMultiplicityLoss Δ δ τ ε) (𝓝 0) (𝓝 (3*Δ+2*δ+5*ε)) := by
  have h := (((tendsto_const_nhds (x := 3*Δ+2*δ)).add
    (tendsto_id.const_mul (Real.log 2-Real.log (2*δ)))).add_const (5*ε)).add
      (highOmissionExponent_tendsto.const_mul 2)
  simpa [largeMultiplicityLoss] using h

/-- A common arbitrarily small positive tolerance preserves both the
small-addition exponent and the large-addition margin. -/
theorem exists_common_multiplicity_tolerance {L : ℕ} (hL : 10000 ≤ L)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
      smallMultiplicityExponent L τ < 8/1000 ∧
      largeMultiplicityLoss (1/(L : ℝ)) (1/200) τ (1/1000) < 4/100 := by
  have hLr : (10000 : ℝ) ≤ L := by exact_mod_cast hL
  have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hsmall : (6 : ℝ)/L*Real.log 2 < 8/1000 := by
    have hd : (6 : ℝ)/L ≤ 6/10000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hLr
    have hp : 0 ≤ (6 : ℝ)/L := div_nonneg (by norm_num) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hlog hp]
  have hlarge : 3*(1/(L : ℝ))+2*(1/200 : ℝ)+5*(1/1000) < 4/100 := by
    have hd : (1 : ℝ)/L ≤ 1/10000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hLr
    linarith
  have hnear := ((smallMultiplicityExponent_tendsto L).eventually (Iio_mem_nhds hsmall)).and
    ((largeMultiplicityLoss_tendsto (1/(L : ℝ)) (1/200) (1/1000)).eventually (Iio_mem_nhds hlarge))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let τ := min (r/2) (min cap samplingTau)
  have hτ : 0 < τ := lt_min (by positivity) (lt_min hcap samplingTau_pos)
  have hτr : τ < r := (min_le_left _ _).trans_lt (by linarith)
  have hp := hball (show dist τ 0 < r by simpa only [Real.dist_eq,sub_zero,abs_of_pos hτ] using hτr)
  exact ⟨τ,hτ,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _),hp.1,hp.2⟩

/-- Every fixed logarithmic polynomial is negligible compared to the
strict power saving in the large-class estimate. -/
theorem log_add_one_cube_div_rpow_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun B : ℝ => (Real.log B+1)^3/B^c) atTop (𝓝 0) := by
  have ht : Tendsto (fun B : ℝ => 8*(Real.log B)^3/B^c) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast,mul_zero,mul_div_assoc] using
      (log_power_div_power_tendsto_zero (3 : ℕ) hc).const_mul 8
  apply squeeze_zero' _ _ ht
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0 : ℝ)] with B hlog hB
    positivity
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0 : ℝ)] with B hlog hB
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hB.le _)
    have hh : Real.log B+1 ≤ 2*Real.log B := by linarith
    have hp := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log B+1) hh 3
    nlinarith

end JointDickman

end OAI
