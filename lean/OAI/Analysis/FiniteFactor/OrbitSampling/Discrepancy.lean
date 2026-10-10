import OAI.Analysis.FiniteFactor.Sampling.Rectangle
import OAI.Analysis.FiniteFactor.OrbitSampling.Fourier
import OAI.Analysis.FiniteFactor.Sampling.Periodization

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset Filter
open scoped ENNReal Topology
noncomputable section

/-- Every constructed power is long enough for density at most two on
every coordinate in the sampling prefix. -/
theorem sourceSampling_phase_length (s : ℕ) (hs : 200000 ≤ sourceBlockSize s)
    (i : SourceCoordinate) (hi : i.1 ≤ s) (n : ℤ) (hn : n ∈ sourceSamplingPowers s) :
    1 ≤ (n : ℝ)*sourceAngleUnit i := by
  have hm : (200000 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast hs
  have hm0 := sourceBlockSize_pos s
  have hspec := (sourceSamplingPowers_spec s hs).1 n hn
  have hQ : (sourceBlockSize s : ℝ)^3 ≤ samplingQ (sourceBlockSize s) := by
    unfold samplingQ
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
  have hN : (sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K ≤ (sourceBlockSize s : ℝ)^2 := by
    have hh : (sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K ≤
        (sourceBlockSize s : ℝ)*(sourceStageState s).K := by exact_mod_cast sourceFrequencyScale_monotone hi
    have hK : ((sourceStageState s).K : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_K
    nlinarith
  have hnp : (sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K ≤ (n : ℝ) := by
    nlinarith [hspec.1,sq_nonneg (sourceBlockSize s : ℝ)]
  unfold sourceAngleUnit
  rw [mul_one_div,le_div_iff₀ (mul_pos (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1)),one_mul]
  exact hnp

theorem sourceSampling_phase_domination (s : ℕ) (hs : 200000 ≤ sourceBlockSize s)
    (i : SourceCoordinate) (hi : i.1 ≤ s) (n : ℤ) (hn : n ∈ sourceSamplingPowers s) :
    sourceAngleLaw.map (fun θ => Int.fract ((n : ℝ)*θ i)) ≤
      (2 : ℝ≥0∞) • unitIntervalMeasure := by
  have hp : Measurable (fun t : ℝ => Int.fract ((n : ℝ)*t)) :=
    sourceFract_measurable.comp (measurable_const.mul measurable_id)
  have he : sourceAngleLaw.map (fun θ => Int.fract ((n : ℝ)*θ i)) =
      (sourceAngleMarginal i).map (fun t => Int.fract ((n : ℝ)*t)) := by
    rw [← sourceAngleLaw_coordinate i,Measure.map_map hp (measurable_pi_apply i)]
    rfl
  rw [he]
  have hnp : (0 : ℝ) < n := by exact_mod_cast ((sourceSamplingPowers_spec s hs).1 n hn).2.2
  have hh := (sourceAngle_phase_sandwich i (n : ℝ) hnp).2
  apply hh.trans
  have hlen := sourceSampling_phase_length s hs i hi n hn
  have hiR : 1/(n*sourceAngleUnit i) ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlen
  have heps : ENNReal.ofReal (1+1/(n*sourceAngleUnit i)) ≤ (2 : ℝ≥0∞) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show 1+1/(n*sourceAngleUnit i) ≤ (2 : ℝ) by linarith)
  gcongr

theorem samplingCharacter_pair_expression (v w : ℤ) (a b : ℝ) :
    samplingCharacter v a*samplingCharacter w b =
      Complex.exp (2*Real.pi*Complex.I*((v : ℂ)*(a : ℂ)+(w : ℂ)*(b : ℂ))) := by
  unfold samplingCharacter
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Rectangle discrepancy for the actual pair law of the deterministic
selected powers, with every probabilistic hypothesis discharged. -/
theorem sourceSampling_rectangle_bound (s : ℕ) (hs : 200000 ≤ sourceBlockSize s)
    (i : SourceCoordinate) (hi : i.1 ≤ s) (n n' : ℤ)
    (hn : n ∈ sourceSamplingPowers s) (hn' : n' ∈ sourceSamplingPowers s) (hne : n ≠ n')
    (a b a' b' : ℝ) :
    |(sourceAngleLaw {θ | Int.fract ((n : ℝ)*θ i) ∈ Set.Icc a b ∧
        Int.fract ((n' : ℝ)*θ i) ∈ Set.Icc a' b'}).toReal -
      (unitIntervalMeasure (Set.Icc a b)).toReal*(unitIntervalMeasure (Set.Icc a' b')).toReal| ≤
      26*(sourceBlockSize s : ℝ)^(-80 : ℝ) := by
  let m := sourceBlockSize s
  have hm0 : (0 : ℝ) < m := sourceBlockSize_pos s
  have hm1 : (1 : ℝ) ≤ m := by
    have hm : (200000 : ℝ) ≤ m := by exact_mod_cast hs
    linarith
  let δ : ℝ := (m : ℝ)^(-80 : ℝ)
  let ε : ℝ := Real.pi⁻¹*(m : ℝ)^(-1000 : ℝ)
  have hH : 0 < samplingH m := pow_pos (by exact_mod_cast hm0) 300
  have hphase (n : ℤ) : Measurable (fun θ : SourceCoordinate → ℝ => Int.fract ((n : ℝ)*θ i)) :=
    sourceFract_measurable.comp (measurable_const.mul (measurable_pi_apply i))
  have hh := sampling_rectangle_discrepancy sourceAngleLaw _ _ (hphase n) (hphase n')
    (sourceSampling_phase_domination s hs i hi n hn) (sourceSampling_phase_domination s hs i hi n' hn')
    (samplingH m) hH a b a' b' δ ε (by dsimp [δ]; positivity) (by dsimp [ε]; positivity)
    (fun v w hv hw hne' => by
      simp_rw [samplingCharacter_pair_expression]
      exact sourceSampling_pair_fourier_bound s hs i hi n n' hn hn' hne v w hv.le hw.le hne')
  apply hh.trans
  have htail : 1/(2*(samplingH m : ℝ)*δ^2) = (1/2 : ℝ)*(m : ℝ)^(-140 : ℝ) := by
    dsimp [samplingH,δ]
    norm_num [Real.rpow_neg,Real.rpow_ofNat,hm0.le]
    field_simp
  have hfour : (samplingH m : ℝ)^2*ε = Real.pi⁻¹*(m : ℝ)^(-400 : ℝ) := by
    dsimp [samplingH,ε]
    norm_num [Real.rpow_neg,Real.rpow_ofNat,hm0.le]
    field_simp
  rw [htail,hfour]
  have h140 : (m : ℝ)^(-140 : ℝ) ≤ δ := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have h400 : (m : ℝ)^(-400 : ℝ) ≤ δ := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have hpi : Real.pi⁻¹ ≤ 1 := by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (show 1 ≤ Real.pi by linarith [Real.two_le_pi])
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hp0 : 0 ≤ (m : ℝ)^(-400 : ℝ) := by positivity
  change 24*δ+1/2*(m : ℝ)^(-140 : ℝ)+Real.pi⁻¹*(m : ℝ)^(-400 : ℝ) ≤ 26*δ
  nlinarith

end
end FiniteFactor

end OAI
