import OAI.Analysis.KadisonKastler.CoreFrequencyVectors

namespace OAI

/-! # A nonzero bounded frequency window in the modular core

The unit interval supplies an explicit isometric family of vectors fixed by
its frequency projection. No trace or finiteness assertion is used here.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitFrequencyScalar : Lp ℂ 2 (volume : Measure ℝ) :=
  indicatorConstLp (s := Set.Ioc (0 : ℝ) 1) 2 measurableSet_Ioc
    (measure_Ioc_lt_top (μ := volume)).ne (1 : ℂ)

@[simp] theorem norm_unitFrequencyScalar : ‖unitFrequencyScalar‖ = 1 := by
  rw [unitFrequencyScalar, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [measureReal_def, Real.volume_Ioc]

theorem unitFrequencyScalar_fixed :
    regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc unitFrequencyScalar =
      unitFrequencyScalar := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae _ measurableSet_Ioc unitFrequencyScalar,
    (indicatorConstLp_coeFn (p := 2) (s := Set.Ioc (0 : ℝ) 1)
      (μ := volume) (hs := measurableSet_Ioc)
      (hμs := (measure_Ioc_lt_top (μ := volume)).ne) (c := (1 : ℂ)))] with t hp hf
  change regularIndicatorProjection _ _ unitFrequencyScalar t = unitFrequencyScalar t
  rw [hp]
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
  · exact Set.indicator_of_mem ht _
  · rw [Set.indicator_of_notMem ht, show unitFrequencyScalar t = 0 from
      hf.trans (Set.indicator_of_notMem ht _)]

def unitFrequencyVector (ξ : H) : RegularCoreHilbert H :=
  regularFrequencyPacket unitFrequencyScalar ξ

@[simp] theorem norm_unitFrequencyVector (ξ : H) : ‖unitFrequencyVector ξ‖ = ‖ξ‖ := by
  rw [unitFrequencyVector, norm_regularFrequencyPacket, norm_unitFrequencyScalar, one_mul]

theorem unitFrequencyVector_fixed (ξ : H) :
    regularFrequencyWindow 0 1 (unitFrequencyVector ξ) = unitFrequencyVector ξ := by
  rw [unitFrequencyVector, regularFrequencyWindow_packet, unitFrequencyScalar_fixed]

theorem regularFrequencyWindow_unit_ne_zero [Nontrivial H] :
    regularFrequencyWindow (H := H) 0 1 ≠ 0 := by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : H)
  intro hz
  have hfix := unitFrequencyVector_fixed ξ
  rw [hz, zero_apply] at hfix
  have hn := norm_unitFrequencyVector ξ
  rw [← hfix, norm_zero] at hn
  exact hξ (norm_eq_zero.mp hn.symm)

end

end KadisonKastler

end OAI
