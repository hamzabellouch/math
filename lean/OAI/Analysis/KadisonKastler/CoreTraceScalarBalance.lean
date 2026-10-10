import OAI.Analysis.KadisonKastler.CoreTraceSpectralBalance

namespace OAI

/-! # The trace balance on scalar L2 frequency packets -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem unitWindow_translate_conjugate (a : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    regularTranslateApply a
      (regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
        (regularTranslateApply (-a) f)) =
      regularIndicatorProjection (Set.Ioc (-a) (1-a)) measurableSet_Ioc f := by
  have hmem (t : ℝ) : t + a ∈ Set.Ioc (0 : ℝ) 1 ↔ t ∈ Set.Ioc (-a) (1-a) := by
    simp only [Set.mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  apply Lp.ext
  filter_upwards [regularTranslateApply_ae a
      (regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
        (regularTranslateApply (-a) f)),
    (measurePreserving_add_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae_eq_comp
      (regularIndicatorProjection_apply_ae (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
        (regularTranslateApply (-a) f)),
    (measurePreserving_add_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae_eq_comp
      (regularTranslateApply_ae (-a) f),
    regularIndicatorProjection_apply_ae (Set.Ioc (-a) (1-a)) measurableSet_Ioc f]
    with t ht hp hf hq
  simp only [Function.comp_def] at hp hf
  rw [ht, hp, hq]
  by_cases h : t ∈ Set.Ioc (-a) (1-a)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem t).mpr h), hf]
    congr 1
    ring
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (mt (hmem t).mp h)]

theorem coreTraceFrequencyScalar_spectral_balance
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (Real.sqrt s : ℂ) •
      regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
        (regularTranslateApply (resolventLogFrequency s / (2 * Real.pi))
          coreTraceFrequencyScalar) =
    (Real.sqrt (1-s) : ℂ) •
      regularTranslateApply (resolventLogFrequency s / (2 * Real.pi))
        (regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
          (regularTranslateApply (-(resolventLogFrequency s / (2 * Real.pi)))
            coreTraceFrequencyScalar)) := by
  rw [unitWindow_translate_conjugate, coreTraceFrequencyScalar_shift, smul_smul]
  congr 1
  rw [mul_comm]
  exact_mod_cast coreTrace_exp_sqrt_balance hs hs1

end

end KadisonKastler

end OAI
