import OAI.Analysis.FiniteFactor.Sampling.SecondLevelAE

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

theorem sampling_level_pair_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (r t : ℝ) :
    (∫ x, (if r ≤ f x then (1 : ℝ) else 0)*(if t ≤ g x then (1 : ℝ) else 0) ∂μ) =
      (μ {x | r ≤ f x ∧ t ≤ g x}).toReal := by
  have hs : MeasurableSet {x | r ≤ f x ∧ t ≤ g x} :=
    (measurableSet_le measurable_const hf).inter (measurableSet_le measurable_const hg)
  have he : (fun x => (if r ≤ f x then (1 : ℝ) else 0)*(if t ≤ g x then (1 : ℝ) else 0)) =
      {x | r ≤ f x ∧ t ≤ g x}.indicator (fun _ => (1 : ℝ)) := by
    funext x; simp only [Set.indicator,Set.mem_ofPred_eq]; split_ifs <;> simp_all
  rw [he,integral_indicator hs]
  simp [measureReal_def]

/-- The actual second-oriented reciprocal inherits rectangle discrepancy,
including both monotone pieces, cutoff jumps and reflected interval tests. -/
theorem samplingTestedSecond_pair_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    [NullSingletonClass (μ.map X)] [NullSingletonClass (μ.map Y)]
    (hXs : ∀ᵐ x ∂μ.map X, x ∈ Set.Ico (0 : ℝ) 1)
    (hYs : ∀ᵐ x ∂μ.map Y, x ∈ Set.Ico (0 : ℝ) 1)
    (δ : ℝ) (hrect : ∀ a b c d : ℝ,
      |(μ {x | X x ∈ Set.Icc a b ∧ Y x ∈ Set.Icc c d}).toReal -
        (unitIntervalMeasure (Set.Icc a b)).toReal*(unitIntervalMeasure (Set.Icc c d)).toReal| ≤ δ)
    (h α : ℝ) (G : Set ℝ) (a c s : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hG : MeasurableSet G)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    |(∫ x, samplingTestedSecondWeight h α (Set.Icc a c) G s (X x)*
        samplingTestedSecondWeight h α (Set.Icc a c) G s (Y x) ∂μ)-
      samplingTestedSecondDensity h α (Set.Icc a c) G s^2| ≤
      (4*δ)*(max 1 (1/(h*α)))^2 := by
  let w := samplingTestedSecondWeight h α (Set.Icc a c) G s
  let C := max 1 (1/(h*α))
  have hw : Measurable w := (samplingTestedSecondWeight_measurable h α _ G measurableSet_Icc hG).comp
    (measurable_const.prodMk measurable_id)
  have hwb (t : ℝ) : 0 ≤ w t ∧ w t ≤ C :=
    ⟨(samplingTestedSecondWeight_bounds h α _ G s t hh hα).1,
      (samplingTestedSecondWeight_bounds h α _ G s t hh hα).2.trans
        (samplingWeight_bounds false h α _ t hh hα).2⟩
  have : NullSingletonClass unitIntervalMeasure := by unfold unitIntervalMeasure; infer_instance
  have hu : ∀ᵐ t ∂unitIntervalMeasure, t ∈ Set.Ico (0 : ℝ) 1 :=
    self_mem_ae_restrict measurableSet_Ico
  have hl (r t : ℝ) (hr : 0 < r) (_hrC : r ≤ C) (ht : 0 < t) (_htC : t ≤ C) :
      |(μ {x | r ≤ w (X x) ∧ t ≤ w (Y x)}).toReal -
        (unitIntervalMeasure.prod unitIntervalMeasure {p : ℝ × ℝ | r ≤ w p.1 ∧ t ≤ w p.2}).toReal| ≤ 4*δ := by
    obtain ⟨A,B,hAB⟩ := samplingTestedSecond_level_exists h α G a c s r hh hh1 hα hs hr
    obtain ⟨D,E,hDE⟩ := samplingTestedSecond_level_exists h α G a c s t hh hh1 hα hs ht
    have hx := ae_of_ae_map hX.aemeasurable (hAB (μ.map X) hXs)
    have hy := ae_of_ae_map hY.aemeasurable (hDE (μ.map Y) hYs)
    have hpair : (∫ x, (if r ≤ w (X x) then (1 : ℝ) else 0)*
        (if t ≤ w (Y x) then (1 : ℝ) else 0) ∂μ) =
        ∫ x, (∑ j, samplingClosedIndicator (A j) (B j) (X x))*
          (∑ k, samplingClosedIndicator (D k) (E k) (Y x)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hx,hy] with x hx hy
      rw [hx,hy]
    have hmeanr := integral_congr_ae (hAB unitIntervalMeasure hu)
    have hmeant := integral_congr_ae (hDE unitIntervalMeasure hu)
    rw [← sampling_level_pair_integral μ (fun x => w (X x)) (fun x => w (Y x)) (hw.comp hX) (hw.comp hY) r t,hpair,
      ← sampling_level_pair_integral (unitIntervalMeasure.prod unitIntervalMeasure) (fun p => w p.1) (fun p => w p.2)
        (hw.comp measurable_fst) (hw.comp measurable_snd) r t]
    rw [integral_prod_mul (fun x => if r ≤ w x then (1 : ℝ) else 0)
      (fun x => if t ≤ w x then (1 : ℝ) else 0)]
    change |_- (∫ x, if r ≤ w x then (1 : ℝ) else 0 ∂unitIntervalMeasure)*
      (∫ x, if t ≤ w x then (1 : ℝ) else 0 ∂unitIntervalMeasure)| ≤ _
    rw [hmeanr,hmeant]
    exact sampling_two_intervals_pair μ X Y hX hY δ hrect A B D E
  have hc := sampling_layer_discrepancy μ (unitIntervalMeasure.prod unitIntervalMeasure)
    (fun x => w (X x)) (fun x => w (Y x)) (fun p => w p.1) (fun p => w p.2)
    (hw.comp hX) (hw.comp hY) (hw.comp measurable_fst) (hw.comp measurable_snd)
    C (4*δ) (le_trans (by norm_num) (le_max_left _ _))
    (fun x => hwb (X x)) (fun x => hwb (Y x)) (fun p => hwb p.1) (fun p => hwb p.2) hl
  rw [integral_prod_mul w w] at hc
  simpa only [w,C,samplingTestedSecondDensity,pow_two] using hc

end
end FiniteFactor

end OAI
