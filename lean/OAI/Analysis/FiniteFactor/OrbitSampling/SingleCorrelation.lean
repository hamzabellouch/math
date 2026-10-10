import OAI.Analysis.FiniteFactor.OrbitSampling.PairMoments
import OAI.Analysis.FiniteFactor.Sampling.MixedCorrelation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

/-- The source powers make the single-phase relative error at most m^-80. -/
theorem sourceSampling_single_phase_budget (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n : ℤ) (hn : n ∈ sourceSamplingPowers stage) :
    1/((n : ℝ)*sourceAngleUnit i) ≤ (sourceBlockSize stage : ℝ)^(-80 : ℝ) := by
  let m : ℝ := sourceBlockSize stage
  have hm : 0 < m := sourceBlockSize_pos stage
  have hm2 : 2 ≤ m := by dsimp [m]; exact_mod_cast (show 2 ≤ sourceBlockSize stage by omega)
  have hspec := (sourceSamplingPowers_spec stage hs).1 n hn
  have hQ : m^(83 : ℝ) ≤ samplingQ (sourceBlockSize stage) := by
    unfold samplingQ
    change m^(83 : ℝ) ≤ m^((7/10 : ℝ)*m)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by
      have hh : (200000 : ℝ) ≤ m := by dsimp [m]; exact_mod_cast hs
      linarith)
  have hN : (sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K ≤ m^2 := by
    have hh : (sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K ≤
        (sourceBlockSize stage : ℝ)*(sourceStageState stage).K := by exact_mod_cast sourceFrequencyScale_monotone hi
    have hK : ((sourceStageState stage).K : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (sourceStage stage).m_ge_K
    dsimp [m]
    nlinarith
  have hp : 0 < (n : ℝ) := by exact_mod_cast hspec.2.2
  have h82 : m^(82 : ℝ) ≤ (n : ℝ) := by
    have he : m^(83 : ℝ) = m^(82 : ℝ)*m := by
      rw [show (83 : ℝ) = 82+1 by norm_num,Real.rpow_add hm,Real.rpow_one]
    have hh : 2*m^(82 : ℝ) ≤ m^(83 : ℝ) := by rw [he]; nlinarith [Real.rpow_pos_of_pos hm (82 : ℝ)]
    nlinarith [hspec.1]
  have hlen : m^(80 : ℝ) ≤ (n : ℝ)*sourceAngleUnit i := by
    unfold sourceAngleUnit
    rw [mul_one_div,le_div_iff₀ (mul_pos (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1))]
    calc
      _ ≤ m^(80 : ℝ)*m^2 := mul_le_mul_of_nonneg_left hN (by positivity)
      _ = m^(82 : ℝ) := by rw [← Real.rpow_natCast,← Real.rpow_add hm]; norm_num
      _ ≤ _ := h82
  have he := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hm (80 : ℝ)) hlen
  simpa only [m,one_div,Real.rpow_neg (sourceBlockSize_pos stage).le] using he

/-- Actual full-angle single-phase test, with all source sampling hypotheses. -/
theorem sourceSampling_single_phase_relative (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n : ℤ) (hn : n ∈ sourceSamplingPowers stage)
    (g : ℝ → ℝ) (hg : ∀ t, 0 ≤ g t) (hgm : Measurable g) (hgi : Integrable g unitIntervalMeasure) :
    |(∫ θ, g (Int.fract ((n : ℝ)*θ i)) ∂sourceAngleLaw)-(∫ t, g t ∂unitIntervalMeasure)| ≤
      (sourceBlockSize stage : ℝ)^(-80 : ℝ)*(∫ t, g t ∂unitIntervalMeasure) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast ((sourceSamplingPowers_spec stage hs).1 n hn).2.2
  have hh := sourceAngle_single_phase_test i (n : ℝ) hnp (sourceSampling_phase_length stage hs i hi n hn) g hg hgm hgi
  have hm : Measurable (fun t : ℝ => g (Int.fract ((n : ℝ)*t))) :=
    hgm.comp (sourceFract_measurable.comp (measurable_const.mul measurable_id))
  rw [← sourceAngleLaw_coordinate i,integral_map (measurable_pi_apply i).aemeasurable hm.aestronglyMeasurable] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (sourceSampling_single_phase_budget stage hs i hi n hn) (integral_nonneg hg))

/-- The actual mixed q_n/Z_l^0 coordinate factor, for every orientation and
all measurable tests, has error at most 5*m^-80. -/
theorem sourceSampling_coordinate_mixed_error (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n : ℤ) (hn : n ∈ sourceSamplingPowers stage)
    (r b : Bool) (E G : Set ℝ) (hE : MeasurableSet E) (hG : MeasurableSet G) :
    |(∫ s, samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s *
        (∫ θ, samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
          E G s (Int.fract ((n : ℝ)*θ i)) ∂sourceAngleLaw) ∂unitIntervalMeasure)-
      (∫ s, samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s^2 ∂unitIntervalMeasure)| ≤
      5*(sourceBlockSize stage : ℝ)^(-80 : ℝ) := by
  let u := samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G
  let C := max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage))
  have hp := sourceSampling_parameters stage
  have hu : Measurable (fun p : ℝ × ℝ => u p.1 p.2) := samplingOrientedWeight_measurable r b _ _ E G hE hG
  have hb : ∀ s t, 0 ≤ u s t ∧ u s t ≤ C := samplingOrientedWeight_bounds r b _ _ E G hp.1 hp.2.2
  have he := sampling_integrated_mixed_error sourceAngleLaw (fun θ => Int.fract ((n : ℝ)*θ i))
    (sourceFract_measurable.comp (measurable_const.mul (measurable_pi_apply i)))
    u hu C ((sourceBlockSize stage : ℝ)^(-80 : ℝ)) hb (fun s =>
      sourceSampling_single_phase_relative stage hs i hi n hn (u s) (fun t => (hb s t).1)
        (hu.comp (measurable_const.prodMk measurable_id))
        (sampling_integrable_bounded unitIntervalMeasure (u s)
          (hu.comp (measurable_const.prodMk measurable_id)) C (fun t => by
            rw [abs_of_nonneg (hb s t).1]; exact (hb s t).2)))
  apply he.trans
  have hA := (sourceSampling_oriented_moment stage r b E G hE hG).2
  have hm1 : (1 : ℝ) ≤ sourceBlockSize stage := by
    have h := (sourceStage stage).m_ge_100
    exact_mod_cast (show 1 ≤ sourceBlockSize stage by omega)
  have hpow : (sourceBlockSize stage : ℝ)^(-6/5 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm1 (by norm_num)
  have hA5 : (∫ s, (∫ t, u s t ∂unitIntervalMeasure)^2 ∂unitIntervalMeasure) ≤ 5 := by
    exact hA.trans (by linarith)
  nlinarith [Real.rpow_nonneg (sourceBlockSize_pos stage).le (-80 : ℝ)]

end
end FiniteFactor

end OAI
