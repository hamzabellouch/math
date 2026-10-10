import OAI.Analysis.FiniteFactor.OrbitSampling.RationalTests
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingWidth_tendsto : Tendsto sourceSamplingWidth atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3/5)).comp
    (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)
  convert hh using 1
  funext stage
  simp only [sourceSamplingWidth,Function.comp_apply]
  congr 1; norm_num

theorem sourceSamplingCutoff_tendsto : Tendsto sourceSamplingCutoff atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp
    (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)
  exact hh

theorem sampling_interval_small_displacement (s a c t : ℝ)
    (_ha : s ≠ a) (hc : s ≠ c) (ht : 0 ≤ t)
    (hta : t < |s-a|) (htc : t < |s-c|) :
    s+t ∈ Set.Icc a c ↔ s ∈ Set.Icc a c := by
  have hleft : a ≤ s+t ↔ a ≤ s := by
    by_cases h : a ≤ s
    · constructor
      · exact fun _ => h
      · intro _; linarith
    · rw [abs_of_neg (by linarith : s-a < 0)] at hta
      constructor <;> intro hh <;> linarith
  have hright : s+t ≤ c ↔ s ≤ c := by
    by_cases h : s ≤ c
    · have hsc : s < c := lt_of_le_of_ne h hc
      rw [abs_of_neg (by linarith : s-c < 0)] at htc
      constructor <;> intro hh <;> linarith
    · constructor <;> intro hh <;> linarith
  exact and_congr hleft hright

/-- Away from the interval endpoints, a sufficiently short retained diagonal
step has exactly the same interval test as its starting coordinate. -/
theorem samplingTestedFirstDensity_diagonal_exact (h α s a c : ℝ) (E : Set ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hcut : α ≤ samplingDistance s)
    (ha : s ≠ a) (hc : s ≠ c) (hha : h < |s-a|) (hhc : h < |s-c|) :
    samplingTestedFirstDensity false h α E (Set.Icc a c) s =
      if s ∈ E ∧ s ∈ Set.Icc a c then 1 else 0 := by
  have he (t : ℝ) : samplingTestedFirstWeight false h α E (Set.Icc a c) s t =
      if s ∈ E ∧ s ∈ Set.Icc a c then samplingWeight false h α s t else 0 := by
    by_cases hw : samplingWeight false h α s t = 0
    · simp [samplingTestedFirstWeight,hw]
    · have ho := samplingWeight_orders false h α s t hh hh1 hα hs hw
      have hsp : 0 < t ∧ t < h*samplingDistance s := by
        unfold samplingWeight at hw
        simp only [Bool.false_eq_true,ite_false] at hw
        split_ifs at hw with hcond
        · exact hcond.2
        · exact False.elim (hw rfl)
      have hd : samplingDistance s ≤ 1 := (min_le_right s (1-s)).trans (by linarith [hs.1])
      have hth : t < h := hsp.2.trans_le (by nlinarith)
      have hmem := sampling_interval_small_displacement s a c t ha hc hsp.1.le
        (hth.trans hha) (hth.trans hhc)
      simp only [samplingTestedFirstWeight,ho.1,hmem]
  unfold samplingTestedFirstDensity
  simp_rw [he]
  by_cases htest : s ∈ E ∧ s ∈ Set.Icc a c
  · simp only [ite_eq_left htest]
    simpa only [Bool.false_eq_true,ite_false,ite_eq_left hcut] using
      samplingWeight_first_integral false h α s hh hh1 hα hs
  · simp only [ite_eq_right htest,integral_zero]

/-- At each interior starting point away from the two tested endpoints, the
actual diagonal density eventually equals the uniform diagonal test. -/
theorem sourceSampling_diagonal_eventually (s a c : ℝ) (E : Set ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (ha : s ≠ a) (hc : s ≠ c) :
    ∀ᶠ stage in atTop,
      samplingTestedFirstDensity false (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        E (Set.Icc a c) s = if s ∈ E ∧ s ∈ Set.Icc a c then 1 else 0 := by
  have hd : 0 < samplingDistance s := lt_min hs.1 (by linarith [hs.2])
  have hcut := sourceSamplingCutoff_tendsto.eventually (gt_mem_nhds hd)
  have hwa := sourceSamplingWidth_tendsto.eventually (gt_mem_nhds (abs_pos.mpr (sub_ne_zero.mpr ha)))
  have hwc := sourceSamplingWidth_tendsto.eventually (gt_mem_nhds (abs_pos.mpr (sub_ne_zero.mpr hc)))
  filter_upwards [hcut,hwa,hwc] with stage hcut hwa hwc
  have hp := sourceSampling_parameters stage
  exact samplingTestedFirstDensity_diagonal_exact _ _ s a c E hp.1 hp.2.1 hp.2.2
    ⟨hs.1.le,hs.2⟩ hcut.le ha hc hwa hwc

end
end FiniteFactor

end OAI
