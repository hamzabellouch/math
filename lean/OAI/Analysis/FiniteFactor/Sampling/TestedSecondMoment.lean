import OAI.Analysis.FiniteFactor.Sampling.SecondDensity

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

/-- Exact x- and y-tests in the second diagonal orientation. -/
def samplingTestedSecondWeight (h α : ℝ) (E G : Set ℝ) (s t : ℝ) : ℝ := by
  classical
  exact if Int.fract (s-t) ∈ E ∧ s ∈ G then samplingSecondWeight h α s t else 0

def samplingTestedSecondDensity (h α : ℝ) (E G : Set ℝ) (s : ℝ) : ℝ :=
  ∫ t, samplingTestedSecondWeight h α E G s t ∂unitIntervalMeasure

theorem samplingTestedSecondWeight_measurable (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (fun p : ℝ × ℝ => samplingTestedSecondWeight h α E G p.1 p.2) := by
  unfold samplingTestedSecondWeight
  exact Measurable.ite ((hE.preimage (sourceFract_measurable.comp
    (measurable_fst.sub measurable_snd))).inter (hG.preimage measurable_fst))
    (samplingSecondWeight_measurable h α) measurable_const

theorem samplingTestedSecondWeight_bounds (h α : ℝ) (E G : Set ℝ) (s t : ℝ)
    (hh : 0 < h) (hα : 0 < α) :
    0 ≤ samplingTestedSecondWeight h α E G s t ∧
      samplingTestedSecondWeight h α E G s t ≤ samplingSecondWeight h α s t := by
  have hn : 0 ≤ samplingSecondWeight h α s t := (samplingWeight_bounds false h α _ t hh hα).1
  unfold samplingTestedSecondWeight
  split_ifs <;> simp [hn]

theorem samplingTestedSecondDensity_measurable (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (samplingTestedSecondDensity h α E G) :=
  (samplingTestedSecondWeight_measurable h α E G hE hG).stronglyMeasurable.integral_prod_right.measurable

theorem samplingTestedSecondDensity_bounds (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hα : 0 < α) (hE : MeasurableSet E) (hG : MeasurableSet G) (s : ℝ) :
    0 ≤ samplingTestedSecondDensity h α E G s ∧
      samplingTestedSecondDensity h α E G s ≤ samplingSecondDensity h α s := by
  have hm : Measurable (samplingTestedSecondWeight h α E G s) :=
    (samplingTestedSecondWeight_measurable h α E G hE hG).comp (measurable_const.prodMk measurable_id)
  have hi := (samplingSecondWeight_integrable h α s hh hα).mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingTestedSecondWeight_bounds h α E G s t hh hα).1]
      exact (samplingTestedSecondWeight_bounds h α E G s t hh hα).2))
  exact ⟨integral_nonneg (fun t => (samplingTestedSecondWeight_bounds h α E G s t hh hα).1),
    integral_mono_ae hi (samplingSecondWeight_integrable h α s hh hα)
      (Eventually.of_forall (fun t => (samplingTestedSecondWeight_bounds h α E G s t hh hα).2))⟩

theorem samplingTestedSecondDensity_square (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∀ᵐ s ∂unitIntervalMeasure, 0 ≤ samplingTestedSecondDensity h α E G s ∧
      samplingTestedSecondDensity h α E G s ≤ 1/(1-h)) ∧
    (∫ s, samplingTestedSecondDensity h α E G s^2 ∂unitIntervalMeasure) ≤ 1+h^2/(1-h)^2 := by
  let f := samplingTestedSecondDensity h α E G
  let q := samplingIdealSecond h
  let C := 1/(1-h)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hf := samplingTestedSecondDensity_measurable h α E G hE hG
  have hq := samplingIdealSecond_measurable h hh
  have hnon (s : ℝ) : 0 ≤ f s := (samplingTestedSecondDensity_bounds h α E G hh hα hE hG s).1
  have hle : ∀ᵐ s ∂unitIntervalMeasure, f s ≤ q s :=
    (samplingSecondDensity_le_ideal h α hh hh1 hα).mono (fun s hs =>
      (samplingTestedSecondDensity_bounds h α E G hh hα hE hG s).2.trans hs)
  have hqb (s : ℝ) : 0 ≤ q s ∧ q s ≤ C := (samplingIdealSecond_bounds h s hh hh1).imp_right And.left
  have hq2 (s : ℝ) : q s^2 ≤ C^2 := by nlinarith [(hqb s).1,(hqb s).2]
  have hf2 : ∀ᵐ s ∂unitIntervalMeasure, f s^2 ≤ q s^2 := hle.mono (fun s hs => by nlinarith [hnon s,(hqb s).1])
  have hfi : Integrable (fun s => f s^2) unitIntervalMeasure :=
    (integrable_const (C^2)).mono' (hf.pow_const 2).aestronglyMeasurable (hf2.mono (fun s hs => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hs.trans (hq2 s)))
  have hqi : Integrable (fun s => q s^2) unitIntervalMeasure :=
    (integrable_const (C^2)).mono' (hq.pow_const 2).aestronglyMeasurable (Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hq2 s))
  exact ⟨hle.mono (fun s hs => ⟨hnon s,hs.trans (hqb s).2⟩),
    (integral_mono_ae hfi hqi hf2).trans (samplingIdealSecond_square h hh hh1).2⟩

end
end FiniteFactor

end OAI
