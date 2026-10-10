import OAI.Analysis.FiniteFactor.Sampling.SelfMoment
import OAI.Analysis.FiniteFactor.Sampling.TestedSecondMoment

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- A bounded measurable real function has an integrable square on a finite measure. -/
theorem sampling_square_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (f : Ω → ℝ) (C : ℝ) (hm : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ C) : Integrable (fun x => f x ^ 2) μ := by
  apply (integrable_const (C^2)).mono' (hm.pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (f x))]
    nlinarith [(hb x).1,(hb x).2])

/-- Squared weights are integrable jointly, permitting the source's Fubini step. -/
theorem samplingWeight_square_integrable (b : Bool) (h α : ℝ) (hh : 0 < h) (hα : 0 < α) :
    Integrable (fun p : ℝ × ℝ => samplingWeight b h α p.1 p.2 ^ 2)
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
  sampling_square_integrable _ _ (max 1 (1/(h*α))) (samplingWeight_measurable b h α)
    (fun p => samplingWeight_bounds b h α p.1 p.2 hh hα)

/-- Haar translation preserves the untested self-pair moment in the second
orientation, with the source's order of both integrations. -/
theorem samplingSecondWeight_square_integral (h α : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hα : 0 < α) (hα1 : α ≤ 1/2) :
    (∫ s, ∫ t, samplingSecondWeight h α s t ^ 2
      ∂unitIntervalMeasure ∂unitIntervalMeasure) = (2/h)*Real.log (1/(2*α)) := by
  have hi : Integrable (fun p : ℝ × ℝ => samplingSecondWeight h α p.1 p.2 ^ 2)
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
    sampling_square_integrable _ _ (max 1 (1/(h*α))) (samplingSecondWeight_measurable h α)
      (fun p => samplingWeight_bounds false h α (Int.fract (p.1-p.2)) p.2 hh hα)
  rw [integral_integral_swap hi]
  calc
    _ = ∫ t, ∫ s, samplingWeight false h α s t ^ 2 ∂unitIntervalMeasure ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [] with t
      have hm : AEStronglyMeasurable (fun s => samplingWeight false h α s t ^ 2) unitIntervalMeasure :=
        (((samplingWeight_measurable false h α).comp (measurable_id.prodMk measurable_const)).pow_const 2).aestronglyMeasurable
      have hp := unitInterval_rotate_preserving (-t)
      have he := integral_map hp.measurable.aemeasurable (show AEStronglyMeasurable
        (fun s => samplingWeight false h α s t ^ 2) (unitIntervalMeasure.map (fun s => Int.fract (s+ -t))) from
          hp.map_eq.symm ▸ hm)
      rw [hp.map_eq] at he
      simpa [samplingSecondWeight,sub_eq_add_neg] using he.symm
    _ = _ := by
      rw [← integral_integral_swap (samplingWeight_square_integrable false h α hh hα),
        samplingWeight_square_integral h α hh hh1 hα hα1]

/-- Tests decrease the diagonal self-pair moment in the first orientation. -/
theorem samplingTestedFirstWeight_square_integral (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hα1 : α ≤ 1/2)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, ∫ t, samplingTestedFirstWeight false h α E G s t ^ 2
      ∂unitIntervalMeasure ∂unitIntervalMeasure) ≤ (2/h)*Real.log (1/(2*α)) := by
  have hb (s t : ℝ) := samplingTestedFirstWeight_bounds false h α E G s t hh hα
  have hm := samplingTestedFirstWeight_measurable false h α E G hE hG
  have hbig := samplingWeight_square_integrable false h α hh hα
  have hsmall : Integrable (fun p : ℝ × ℝ => samplingTestedFirstWeight false h α E G p.1 p.2 ^ 2)
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
    sampling_square_integrable _ _ (max 1 (1/(h*α))) hm
      (fun p => ⟨(hb p.1 p.2).1,(hb p.1 p.2).2.trans (samplingWeight_bounds false h α p.1 p.2 hh hα).2⟩)
  rw [← samplingWeight_square_integral h α hh hh1 hα hα1,
    ← integral_prod _ hsmall,← integral_prod _ hbig]
  apply integral_mono_ae hsmall hbig
  exact Eventually.of_forall (fun p => by
    nlinarith [(hb p.1 p.2).1,(hb p.1 p.2).2,
      (samplingWeight_bounds false h α p.1 p.2 hh hα).1])

/-- Tests decrease the diagonal self-pair moment in the second orientation. -/
theorem samplingTestedSecondWeight_square_integral (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hα1 : α ≤ 1/2)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, ∫ t, samplingTestedSecondWeight h α E G s t ^ 2
      ∂unitIntervalMeasure ∂unitIntervalMeasure) ≤ (2/h)*Real.log (1/(2*α)) := by
  have hb (s t : ℝ) := samplingTestedSecondWeight_bounds h α E G s t hh hα
  have hm := samplingTestedSecondWeight_measurable h α E G hE hG
  have hbig : Integrable (fun p : ℝ × ℝ => samplingSecondWeight h α p.1 p.2 ^ 2)
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
    sampling_square_integrable _ _ (max 1 (1/(h*α))) (samplingSecondWeight_measurable h α)
      (fun p => samplingWeight_bounds false h α (Int.fract (p.1-p.2)) p.2 hh hα)
  have hsmall : Integrable (fun p : ℝ × ℝ => samplingTestedSecondWeight h α E G p.1 p.2 ^ 2)
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
    sampling_square_integrable _ _ (max 1 (1/(h*α))) hm
      (fun p => ⟨(hb p.1 p.2).1,(hb p.1 p.2).2.trans
        (samplingWeight_bounds false h α (Int.fract (p.1-p.2)) p.2 hh hα).2⟩)
  rw [← samplingSecondWeight_square_integral h α hh hh1 hα hα1,
    ← integral_prod _ hsmall,← integral_prod _ hbig]
  apply integral_mono_ae hsmall hbig
  exact Eventually.of_forall (fun p => by
    nlinarith [(hb p.1 p.2).1,(hb p.1 p.2).2,
      (samplingWeight_bounds false h α (Int.fract (p.1-p.2)) p.2 hh hα).1])

end
end FiniteFactor

end OAI
