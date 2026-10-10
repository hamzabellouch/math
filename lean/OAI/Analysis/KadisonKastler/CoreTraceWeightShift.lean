import OAI.Analysis.KadisonKastler.CoreTraceFrequencyVector
import OAI.Analysis.KadisonKastler.RegularCoreRepresentation

namespace OAI

/-! # Translation covariance of the clipped exponential trace weight -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem coreTraceFrequencyFunction_shift (a t : ℝ) :
    (Set.Ioc (0 : ℝ) 1).indicator (fun s => coreTraceFrequencyFunction (s + a)) t =
      (Real.exp (Real.pi * a) : ℂ) *
        (Set.Ioc (-a) (1 - a)).indicator coreTraceFrequencyFunction t := by
  have hmem : t ∈ Set.Ioc (-a) (1 - a) ↔ t + a ∈ Set.Ioc (0 : ℝ) 1 := by
    simp only [Set.mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem ht]
    by_cases ha : t + a ∈ Set.Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem (hmem.mpr ha)]
      simp only [coreTraceFrequencyFunction, Set.indicator_of_mem ht,
        Set.indicator_of_mem ha, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    · rw [Set.indicator_of_notMem (mt hmem.mp ha)]
      simp [coreTraceFrequencyFunction, ha]
  · rw [Set.indicator_of_notMem ht]
    by_cases ha : t ∈ Set.Ioc (-a) (1 - a) <;>
      simp [coreTraceFrequencyFunction, ht, ha]

theorem coreTraceFrequencyScalar_shift (a : ℝ) :
    regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
      (regularTranslateApply a coreTraceFrequencyScalar) =
      (Real.exp (Real.pi * a) : ℂ) •
        regularIndicatorProjection (Set.Ioc (-a) (1 - a)) measurableSet_Ioc
          coreTraceFrequencyScalar := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae (Set.Ioc (0 : ℝ) 1)
      measurableSet_Ioc (regularTranslateApply a coreTraceFrequencyScalar),
    regularTranslateApply_ae a coreTraceFrequencyScalar,
    (measurePreserving_add_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae_eq_comp
      coreTraceFrequencyScalar_apply_ae,
    regularIndicatorProjection_apply_ae (Set.Ioc (-a) (1 - a)) measurableSet_Ioc
      coreTraceFrequencyScalar,
    coreTraceFrequencyScalar_apply_ae,
    Lp.coeFn_smul (Real.exp (Real.pi * a) : ℂ)
      (regularIndicatorProjection (Set.Ioc (-a) (1 - a)) measurableSet_Ioc
        coreTraceFrequencyScalar)] with t hp ht hw hq hv hs
  simp only [Function.comp_def] at hw
  rw [hp, hs, Pi.smul_apply, hq]
  by_cases hti : t ∈ Set.Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hti, ht, hw]
    by_cases hta : t ∈ Set.Ioc (-a) (1 - a)
    · rw [Set.indicator_of_mem hta, hv]
      simpa only [Set.indicator_of_mem hti, Set.indicator_of_mem hta, smul_eq_mul] using
        coreTraceFrequencyFunction_shift a t
    · rw [Set.indicator_of_notMem hta]
      simpa only [Set.indicator_of_mem hti, Set.indicator_of_notMem hta, mul_zero,
        smul_zero] using coreTraceFrequencyFunction_shift a t
  · rw [Set.indicator_of_notMem hti]
    by_cases hta : t ∈ Set.Ioc (-a) (1 - a)
    · rw [Set.indicator_of_mem hta, hv]
      simp [coreTraceFrequencyFunction, hti]
    · rw [Set.indicator_of_notMem hta, smul_zero]

end

end KadisonKastler

end OAI
