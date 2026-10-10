import OAI.Analysis.FiniteFactor.Sampling.SecondDiscrepancy
import OAI.Analysis.FiniteFactor.OrbitSampling.FirstCorrelation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

/-- Uniform source height bound, for either marginal orientation. -/
theorem sourceSampling_max_height (stage : ℕ) :
    max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)) ≤
      (sourceBlockSize stage : ℝ)^(3 : ℝ) := by
  have hm := sourceBlockSize_pos stage
  have hm1 : (1 : ℝ) ≤ sourceBlockSize stage := by
    have hh : (100 : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (sourceStage stage).m_ge_100
    linarith
  apply max_le
  · exact Real.one_le_rpow hm1 (by norm_num)
  · have he : 1/(sourceSamplingWidth stage*sourceSamplingCutoff stage) =
        (sourceBlockSize stage : ℝ)^(13/5 : ℝ) := by
      unfold sourceSamplingWidth sourceSamplingCutoff
      rw [← Real.rpow_add hm]
      norm_num
      rw [Real.rpow_neg hm.le,inv_inv]
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)

/-- Actual second-diagonal pair error for the selected source powers.
All phase support, atomlessness and discrepancy hypotheses are discharged. -/
theorem sourceSampling_second_pair_error (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n n' : ℤ)
    (hn : n ∈ sourceSamplingPowers stage) (hn' : n' ∈ sourceSamplingPowers stage) (hne : n ≠ n')
    (G : Set ℝ) (hG : MeasurableSet G) (a c s : ℝ) (hsx : s ∈ Set.Ico (0 : ℝ) 1) :
    |(∫ θ, samplingTestedSecondWeight (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (Set.Icc a c) G s (Int.fract ((n : ℝ)*θ i)) *
        samplingTestedSecondWeight (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (Set.Icc a c) G s (Int.fract ((n' : ℝ)*θ i)) ∂sourceAngleLaw) -
      samplingTestedSecondDensity (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (Set.Icc a c) G s ^ 2| ≤
      104*(sourceBlockSize stage : ℝ)^(-74 : ℝ) := by
  have := sourceSampling_phase_null_singletons stage hs i hi n hn
  have := sourceSampling_phase_null_singletons stage hs i hi n' hn'
  have hm (k : ℤ) : Measurable (fun θ : SourceCoordinate → ℝ => Int.fract ((k : ℝ)*θ i)) :=
    sourceFract_measurable.comp (measurable_const.mul (measurable_pi_apply i))
  have hsupport (k : ℤ) : ∀ᵐ t ∂sourceAngleLaw.map (fun θ => Int.fract ((k : ℝ)*θ i)),
      t ∈ Set.Ico (0 : ℝ) 1 := by
    apply (ae_map_iff (hm k).aemeasurable
      (show MeasurableSet {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1} from measurableSet_Ico)).mpr
    exact Eventually.of_forall (fun θ => ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩)
  have hp := sourceSampling_parameters stage
  have hb := samplingTestedSecond_pair_bound sourceAngleLaw
    (fun θ => Int.fract ((n : ℝ)*θ i)) (fun θ => Int.fract ((n' : ℝ)*θ i))
    (hm n) (hm n') (hsupport n) (hsupport n') _
    (sourceSampling_rectangle_bound stage hs i hi n n' hn hn' hne)
    _ _ G a c s hp.1 hp.2.1 hp.2.2 hG hsx
  let m : ℝ := sourceBlockSize stage
  let C := max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage))
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hC2 : C^2 ≤ m^(6 : ℝ) := by
    calc
      _ ≤ (m^(3 : ℝ))^2 := by nlinarith [sourceSampling_max_height stage,Real.rpow_nonneg (sourceBlockSize_pos stage).le (3 : ℝ)]
      _ = _ := by dsimp [m]; rw [← Real.rpow_natCast,← Real.rpow_mul (sourceBlockSize_pos stage).le]; norm_num
  apply hb.trans
  change (4*(26*m^(-80 : ℝ)))*C^2 ≤ 104*m^(-74 : ℝ)
  calc
    _ ≤ (4*(26*m^(-80 : ℝ)))*m^(6 : ℝ) := mul_le_mul_of_nonneg_left hC2 (by positivity)
    _ = _ := by rw [mul_assoc, mul_assoc,← Real.rpow_add (sourceBlockSize_pos stage)]; norm_num; ring

end
end FiniteFactor

end OAI
