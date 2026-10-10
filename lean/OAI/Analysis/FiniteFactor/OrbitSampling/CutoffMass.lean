import OAI.Analysis.FiniteFactor.OrbitSampling.DiagonalIntegral

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

/-- Exact whole-circle first density, including the retained cutoff. -/
theorem samplingTestedFirstDensity_whole (b : Bool) (h α s : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    samplingTestedFirstDensity b h α (Set.Icc 0 1) (Set.Icc 0 1) s =
      if b then 1-s else if α ≤ samplingDistance s then 1 else 0 := by
  have he : samplingTestedFirstDensity b h α (Set.Icc 0 1) (Set.Icc 0 1) s =
      ∫ t, samplingWeight b h α s t ∂unitIntervalMeasure := by
    apply integral_congr_ae
    filter_upwards [] with t
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.le⟩
    have ht' : Int.fract (s+t) ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
    simp only [samplingTestedFirstWeight,hs',ht',and_self,ite_true]
  exact he.trans (samplingWeight_first_integral b h α s hh hh1 hα hs)

/-- The exact lost mass of one untested diagonal coordinate is 2α. -/
theorem sampling_diagonal_whole_mass (h α : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hα1 : α ≤ 1/2) :
    (∫ s, samplingTestedFirstDensity false h α (Set.Icc 0 1) (Set.Icc 0 1) s ∂unitIntervalMeasure) = 1-2*α := by
  have he : samplingTestedFirstDensity false h α (Set.Icc 0 1) (Set.Icc 0 1) =ᵐ[unitIntervalMeasure]
      (Set.Icc α (1-α)).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
    rw [samplingTestedFirstDensity_whole false h α s hh hh1 hα hs]
    have hc : α ≤ samplingDistance s ↔ s ∈ Set.Icc α (1-α) := by
      simp only [samplingDistance,le_min_iff,Set.mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
    simp only [Bool.false_eq_true,ite_false,hc,Set.indicator_apply]
  rw [integral_congr_ae he,integral_indicator measurableSet_Icc,integral_const]
  have hsub : Set.Icc α (1-α) ⊆ Set.Ico (0 : ℝ) 1 := by
    intro s hs
    exact ⟨hα.le.trans hs.1,hs.2.trans_lt (by linarith)⟩
  simp only [measureReal_def,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,
    smul_eq_mul,mul_one]
  unfold unitIntervalMeasure
  rw [Measure.restrict_apply measurableSet_Icc,Set.inter_eq_left.mpr hsub,Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]
  ring

/-- The total cutoff budget tends to zero despite the growing dimension. -/
theorem sourceSampling_cutoff_budget_tendsto :
    Tendsto (fun stage => 2*((sourceSamplingPrefix stage).card : ℝ)*sourceSamplingCutoff stage)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun stage => (101/50 : ℝ)*(sourceBlockSize stage : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)).const_mul (101/50 : ℝ)
  apply squeeze_zero (fun stage => by have := (sourceSampling_parameters stage).2.2; positivity) _ ht
  intro stage
  have hm := sourceBlockSize_pos stage
  calc
    _ ≤ 2*((101/100 : ℝ)*sourceBlockSize stage)*sourceSamplingCutoff stage := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sourceSamplingPrefix_card_bound stage) (by norm_num))
        (sourceSampling_parameters stage).2.2.le
    _ = (101/50 : ℝ)*(sourceBlockSize stage : ℝ)⁻¹ := by
      simp only [sourceSamplingCutoff,Real.rpow_neg hm.le,Real.rpow_two]
      field_simp
      ring

/-- Any subset of untested coordinates retains asymptotically all its mass.
The estimate uses its actual varying cardinality, bounded by the prefix. -/
theorem sourceSampling_untested_mass_tendsto (k : ℕ → ℕ)
    (hk : ∀ stage, k stage ≤ (sourceSamplingPrefix stage).card) :
    Tendsto (fun stage => (1-2*sourceSamplingCutoff stage)^(k stage)) atTop (𝓝 1) := by
  have he : ∀ stage, |(1-2*sourceSamplingCutoff stage)^(k stage)-1| ≤
      2*((sourceSamplingPrefix stage).card : ℝ)*sourceSamplingCutoff stage := by
    intro stage
    have hα := (sourceSampling_parameters stage).2.2
    have hα1 := sourceSamplingCutoff_le_half stage
    have hlo : 0 ≤ 1-2*sourceSamplingCutoff stage := by linarith
    have hup : (1-2*sourceSamplingCutoff stage)^(k stage) ≤ 1 := pow_le_one₀ hlo (by linarith)
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(2*sourceSamplingCutoff stage) by linarith) (k stage)
    have hk' : (k stage : ℝ) ≤ (sourceSamplingPrefix stage).card := by exact_mod_cast hk stage
    rw [abs_of_nonpos (by linarith)]
    have hm := mul_le_mul_of_nonneg_right hk' (show 0 ≤ 2*sourceSamplingCutoff stage by positivity)
    simp only [mul_neg,← sub_eq_add_neg] at hb
    nlinarith
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun stage => abs_nonneg _) he sourceSampling_cutoff_budget_tendsto

end
end FiniteFactor

end OAI
