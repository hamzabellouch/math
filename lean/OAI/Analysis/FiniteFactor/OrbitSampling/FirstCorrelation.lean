import OAI.Analysis.FiniteFactor.Sampling.FirstDiscrepancy

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

theorem sourceSampling_first_height_bound (stage : ℕ) (b : Bool) (s : ℝ) :
    0 ≤ samplingFirstHeight b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) s ∧
    samplingFirstHeight b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) s ≤
      (sourceBlockSize stage : ℝ)^(13/5 : ℝ) := by
  have hp := sourceSampling_parameters stage
  have hm := sourceBlockSize_pos stage
  have hm1 : (1 : ℝ) ≤ sourceBlockSize stage := by
    have hh : (100 : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (sourceStage stage).m_ge_100
    linarith
  cases b
  · unfold samplingFirstHeight
    simp only [Bool.false_eq_true,ite_false]
    split_ifs with hc
    · have hd : 0 < samplingDistance s := hp.2.2.trans_le hc
      refine ⟨one_div_nonneg.mpr (mul_nonneg hp.1.le hd.le),?_⟩
      calc
        _ ≤ 1/(sourceSamplingWidth stage*sourceSamplingCutoff stage) :=
          one_div_le_one_div_of_le (mul_pos hp.1 hp.2.2) (mul_le_mul_of_nonneg_left hc hp.1.le)
        _ = _ := by
          unfold sourceSamplingWidth sourceSamplingCutoff
          rw [← Real.rpow_add hm]
          norm_num
          rw [Real.rpow_neg hm.le,inv_inv]
    · exact ⟨le_rfl,by positivity⟩
  · exact ⟨by norm_num [samplingFirstHeight],Real.one_le_rpow hm1 (by norm_num)⟩

/-- Explicit first-oriented pair correlation error for every prefix coordinate,
every rectangle endpoint and both source coordinate types. -/
theorem sourceSampling_first_pair_error (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n n' : ℤ)
    (hn : n ∈ sourceSamplingPowers stage) (hn' : n' ∈ sourceSamplingPowers stage) (hne : n ≠ n')
    (b : Bool) (E : Set ℝ) (a c s : ℝ) (hsx : s ∈ Set.Ico (0 : ℝ) 1) :
    |(∫ θ, samplingTestedFirstWeight b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        E (Set.Icc a c) s (Int.fract ((n : ℝ)*θ i)) *
        samplingTestedFirstWeight b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        E (Set.Icc a c) s (Int.fract ((n' : ℝ)*θ i)) ∂sourceAngleLaw) -
      samplingTestedFirstDensity b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E (Set.Icc a c) s ^ 2| ≤
      26*(sourceBlockSize stage : ℝ)^(-74 : ℝ) := by
  let m : ℝ := sourceBlockSize stage
  let C := if s ∈ E then samplingFirstHeight b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) s else 0
  have hm : 0 < m := sourceBlockSize_pos stage
  have hm1 : 1 ≤ m := by
    have hh : (200000 : ℝ) ≤ (sourceBlockSize stage : ℝ) := by exact_mod_cast hs
    dsimp [m]
    linarith
  have hheight := sourceSampling_first_height_bound stage b s
  have hC : 0 ≤ C ∧ C ≤ m^(3 : ℝ) := by
    dsimp [C]
    split_ifs
    · exact ⟨hheight.1,hheight.2.trans (Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num))⟩
    · exact ⟨le_rfl,by positivity⟩
  have hC2 : C^2 ≤ m^(6 : ℝ) := by
    calc
      C^2 ≤ (m^(3 : ℝ))^2 := by nlinarith [hC.1,hC.2,Real.rpow_nonneg hm.le (3 : ℝ)]
      _ = _ := by rw [← Real.rpow_natCast,← Real.rpow_mul hm.le]; norm_num
  apply (sourceSampling_first_pair_bound stage hs i hi n n' hn hn' hne b E a c s hsx).trans
  change (26*m^(-80 : ℝ))*C^2 ≤ 26*m^(-74 : ℝ)
  calc
    _ ≤ (26*m^(-80 : ℝ))*m^(6 : ℝ) := mul_le_mul_of_nonneg_left hC2 (by positivity)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hm]; norm_num

end
end FiniteFactor

end OAI
