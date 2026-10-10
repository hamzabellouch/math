import OAI.Analysis.KadisonKastler.CoreFrequencyCovariance
import OAI.Analysis.KadisonKastler.CoreFrequencyUnitWindow

namespace OAI

/-! # A nonzero half-window and inclusions between core frequency cuts -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularFrequencyWindow_mul_of_subset (a b c d : ℝ)
    (h : Set.Ioc a b ⊆ Set.Ioc c d) :
    regularFrequencyWindow (H := H) a b * regularFrequencyWindow c d =
      regularFrequencyWindow a b := by
  unfold regularFrequencyWindow
  rw [← map_mul, regularIndicatorProjection_mul_of_subset _ _
    measurableSet_Ioc measurableSet_Ioc h]

def halfFrequencyScalar : Lp ℂ 2 (volume : Measure ℝ) :=
  indicatorConstLp (s := Set.Ioc (0 : ℝ) (1 / 2)) 2 measurableSet_Ioc
    (measure_Ioc_lt_top (μ := volume)).ne (1 : ℂ)

theorem halfFrequencyScalar_norm_pos : 0 < ‖halfFrequencyScalar‖ := by
  rw [halfFrequencyScalar, norm_indicatorConstLp (by norm_num) (by norm_num)]
  have h : 0 < (volume : Measure ℝ).real (Set.Ioc (0 : ℝ) (1 / 2)) := by
    norm_num [measureReal_def, Real.volume_Ioc]
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos h _)

theorem halfFrequencyScalar_fixed :
    regularIndicatorProjection (Set.Ioc (0 : ℝ) (1 / 2)) measurableSet_Ioc
      halfFrequencyScalar = halfFrequencyScalar := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae _ measurableSet_Ioc halfFrequencyScalar,
    (indicatorConstLp_coeFn (p := 2) (s := Set.Ioc (0 : ℝ) (1 / 2))
      (μ := volume) (hs := measurableSet_Ioc)
      (hμs := (measure_Ioc_lt_top (μ := volume)).ne) (c := (1 : ℂ)))] with t hp hf
  change regularIndicatorProjection _ _ halfFrequencyScalar t = halfFrequencyScalar t
  rw [hp]
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) (1 / 2)
  · exact Set.indicator_of_mem ht _
  · rw [Set.indicator_of_notMem ht, show halfFrequencyScalar t = 0 from
      hf.trans (Set.indicator_of_notMem ht _)]

theorem regularFrequencyWindow_half_ne_zero [Nontrivial H] :
    regularFrequencyWindow (H := H) 0 (1 / 2) ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have hfix : regularFrequencyWindow 0 (1 / 2)
      (regularFrequencyPacket halfFrequencyScalar v) =
      regularFrequencyPacket halfFrequencyScalar v := by
    rw [regularFrequencyWindow_packet, halfFrequencyScalar_fixed]
  intro hz
  rw [hz, zero_apply] at hfix
  have hn := norm_regularFrequencyPacket halfFrequencyScalar v
  rw [← hfix, norm_zero] at hn
  have hpos : 0 < ‖halfFrequencyScalar‖ * ‖v‖ :=
    mul_pos halfFrequencyScalar_norm_pos (norm_pos_iff.mpr hv)
  exact hpos.ne' hn.symm

end

end KadisonKastler

end OAI
