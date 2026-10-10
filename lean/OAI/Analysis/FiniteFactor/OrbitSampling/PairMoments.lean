import OAI.Analysis.FiniteFactor.OrbitSampling.SecondCorrelation
import OAI.Analysis.FiniteFactor.Sampling.SecondTriangular
import OAI.Analysis.FiniteFactor.Sampling.IntegratedCorrelation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

/-- All four actual tested coordinate cases have the same pair-error budget. -/
theorem sourceSampling_oriented_pair_error (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n n' : ℤ)
    (hn : n ∈ sourceSamplingPowers stage) (hn' : n' ∈ sourceSamplingPowers stage) (hne : n ≠ n')
    (r b : Bool) (a c a' c' s : ℝ) (hsx : s ∈ Set.Ioo (0 : ℝ) 1) :
    |(∫ θ, samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (Set.Icc a c) (Set.Icc a' c') s (Int.fract ((n : ℝ)*θ i)) *
        samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (Set.Icc a c) (Set.Icc a' c') s (Int.fract ((n' : ℝ)*θ i)) ∂sourceAngleLaw) -
      samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (Set.Icc a c) (Set.Icc a' c') s ^ 2| ≤
      104*(sourceBlockSize stage : ℝ)^(-74 : ℝ) := by
  have hm1 : (1 : ℝ) ≤ sourceBlockSize stage := by
    have h := (sourceStage stage).m_ge_100
    exact_mod_cast (by omega : 1 ≤ sourceBlockSize stage)
  cases r
  · have hb := sourceSampling_first_pair_error stage hs i hi n n' hn hn' hne b
      (Set.Icc a c) a' c' s ⟨hsx.1.le,hsx.2⟩
    exact hb.trans (by nlinarith [Real.rpow_nonneg (sourceBlockSize_pos stage).le (-74 : ℝ)])
  · cases b
    · exact sourceSampling_second_pair_error stage hs i hi n n' hn hn' hne
        (Set.Icc a' c') measurableSet_Icc a c s ⟨hsx.1.le,hsx.2⟩
    · have := sourceSampling_phase_null_singletons stage hs i hi n hn
      have := sourceSampling_phase_null_singletons stage hs i hi n' hn'
      have hm (k : ℤ) : Measurable (fun θ : SourceCoordinate → ℝ => Int.fract ((k : ℝ)*θ i)) :=
        sourceFract_measurable.comp (measurable_const.mul (measurable_pi_apply i))
      have hp := sourceSampling_parameters stage
      have hb := samplingSecondTriangular_pair_bound sourceAngleLaw
        (fun θ => Int.fract ((n : ℝ)*θ i)) (fun θ => Int.fract ((n' : ℝ)*θ i)) (hm n) (hm n')
        (Eventually.of_forall (fun θ => ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩))
        (Eventually.of_forall (fun θ => ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩))
        _ (by positivity) (sourceSampling_rectangle_bound stage hs i hi n n' hn hn' hne)
        _ _ (Set.Icc a' c') a c s hp.1 hp.2.1 hp.2.2 hsx
      apply hb.trans
      have he := Real.rpow_le_rpow_of_exponent_le hm1 (show (-80 : ℝ) ≤ -74 by norm_num)
      nlinarith [Real.rpow_nonneg (sourceBlockSize_pos stage).le (-74 : ℝ)]

theorem sourceSampling_coordinate_pair_error (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n n' : ℤ)
    (hn : n ∈ sourceSamplingPowers stage) (hn' : n' ∈ sourceSamplingPowers stage) (hne : n ≠ n')
    (r b : Bool) (a c a' c' : ℝ) :
    |(∫ s, ∫ θ, samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (Set.Icc a c) (Set.Icc a' c') s (Int.fract ((n : ℝ)*θ i)) *
        samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (Set.Icc a c) (Set.Icc a' c') s (Int.fract ((n' : ℝ)*θ i)) ∂sourceAngleLaw ∂unitIntervalMeasure) -
      (∫ s, samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (Set.Icc a c) (Set.Icc a' c') s ^ 2 ∂unitIntervalMeasure)| ≤
      104*(sourceBlockSize stage : ℝ)^(-74 : ℝ) := by
  have hp := sourceSampling_parameters stage
  apply sampling_integrated_pair_error sourceAngleLaw
    (fun θ => Int.fract ((n : ℝ)*θ i)) (fun θ => Int.fract ((n' : ℝ)*θ i))
    (sourceFract_measurable.comp (measurable_const.mul (measurable_pi_apply i)))
    (sourceFract_measurable.comp (measurable_const.mul (measurable_pi_apply i)))
    (samplingOrientedWeight r b _ _ (Set.Icc a c) (Set.Icc a' c'))
    (samplingOrientedWeight_measurable r b _ _ _ _ measurableSet_Icc measurableSet_Icc)
    (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage))) _
    (samplingOrientedWeight_bounds r b _ _ _ _ hp.1 hp.2.2)
  have : NullSingletonClass unitIntervalMeasure := by unfold unitIntervalMeasure; infer_instance
  filter_upwards [self_mem_ae_restrict measurableSet_Ico,
    ae_iff.mpr (show unitIntervalMeasure {s | ¬s ≠ 0} = 0 by simp)] with s hsx hs0
  exact sourceSampling_oriented_pair_error stage hs i hi n n' hn hn' hne r b a c a' c' s
    ⟨lt_of_le_of_ne hsx.1 (Ne.symm hs0),hsx.2⟩

end
end FiniteFactor

end OAI
