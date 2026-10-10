import OAI.Analysis.FiniteFactor.Sampling.LayerDiscrepancy

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

def samplingClosedIndicator (a b t : ℝ) : ℝ :=
  (Set.Icc a b).indicator (fun _ => 1) t

theorem samplingClosedIndicator_measurable (a b : ℝ) :
    Measurable (samplingClosedIndicator a b) := measurable_const.indicator measurableSet_Icc

theorem samplingClosedIndicator_bounds (a b t : ℝ) :
    0 ≤ samplingClosedIndicator a b t ∧ samplingClosedIndicator a b t ≤ 1 := by
  simp only [samplingClosedIndicator,Set.indicator]; split_ifs <;> norm_num

theorem samplingClosedIndicator_integral (a b : ℝ) :
    (∫ t, samplingClosedIndicator a b t ∂unitIntervalMeasure) =
      (unitIntervalMeasure (Set.Icc a b)).toReal := by
  unfold samplingClosedIndicator
  rw [integral_indicator measurableSet_Icc]
  simp [measureReal_def]

theorem samplingClosedIndicator_pair {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (a b c d : ℝ) :
    (∫ x, samplingClosedIndicator a b (X x)*samplingClosedIndicator c d (Y x) ∂μ) =
      (μ {x | X x ∈ Set.Icc a b ∧ Y x ∈ Set.Icc c d}).toReal := by
  have hs : MeasurableSet {x | X x ∈ Set.Icc a b ∧ Y x ∈ Set.Icc c d} :=
    (measurableSet_Icc.preimage hX).inter (measurableSet_Icc.preimage hY)
  have he : (fun x => samplingClosedIndicator a b (X x)*samplingClosedIndicator c d (Y x)) =
      {x | X x ∈ Set.Icc a b ∧ Y x ∈ Set.Icc c d}.indicator (fun _ => (1 : ℝ)) := by
    funext x
    simp only [samplingClosedIndicator,Set.indicator,Set.mem_ofPred_eq]
    split_ifs <;> simp_all
  rw [he,integral_indicator hs]
  simp [measureReal_def]

/-- Two intervals in each variable cost four rectangle discrepancies. -/
theorem sampling_two_intervals_pair {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (δ : ℝ)
    (hrect : ∀ a b c d : ℝ,
      |(μ {x | X x ∈ Set.Icc a b ∧ Y x ∈ Set.Icc c d}).toReal -
        (unitIntervalMeasure (Set.Icc a b)).toReal*(unitIntervalMeasure (Set.Icc c d)).toReal| ≤ δ)
    (a b c d : Fin 2 → ℝ) :
    |(∫ x, (∑ j, samplingClosedIndicator (a j) (b j) (X x))*
        (∑ k, samplingClosedIndicator (c k) (d k) (Y x)) ∂μ) -
      (∫ t, ∑ j, samplingClosedIndicator (a j) (b j) t ∂unitIntervalMeasure)*
      (∫ t, ∑ k, samplingClosedIndicator (c k) (d k) t ∂unitIntervalMeasure)| ≤ 4*δ := by
  let f (j : Fin 2) := samplingClosedIndicator (a j) (b j)
  let g (k : Fin 2) := samplingClosedIndicator (c k) (d k)
  have hi (j k : Fin 2) : Integrable (fun x => f j (X x)*g k (Y x)) μ := by
    apply sampling_integrable_bounded μ _
      (((samplingClosedIndicator_measurable _ _).comp hX).mul
        ((samplingClosedIndicator_measurable _ _).comp hY)) 1
    intro x
    have h1 := samplingClosedIndicator_bounds (a j) (b j) (X x)
    have h2 := samplingClosedIndicator_bounds (c k) (d k) (Y x)
    simp only [Pi.mul_apply,Function.comp_apply]
    rw [abs_of_nonneg (mul_nonneg h1.1 h2.1)]
    nlinarith
  have hif (j : Fin 2) : Integrable (f j) unitIntervalMeasure :=
    integrable_unit_bounded _ _ (samplingClosedIndicator_measurable _ _) (samplingClosedIndicator_bounds _ _)
  have hig (k : Fin 2) : Integrable (g k) unitIntervalMeasure :=
    integrable_unit_bounded _ _ (samplingClosedIndicator_measurable _ _) (samplingClosedIndicator_bounds _ _)
  change |(∫ x, (∑ j, f j (X x))*(∑ k, g k (Y x)) ∂μ) -
    (∫ t, ∑ j, f j t ∂unitIntervalMeasure)*(∫ t, ∑ k, g k t ∂unitIntervalMeasure)| ≤ _
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi j k))]
  simp_rw [integral_finsetSum _ (fun k _ => hi _ k)]
  rw [integral_finsetSum _ (fun j _ => hif j),integral_finsetSum _ (fun k _ => hig k)]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin 2, ∑ k : Fin 2,
        |(∫ x, f j (X x)*g k (Y x) ∂μ)-
          (∫ t, f j t ∂unitIntervalMeasure)*(∫ t, g k t ∂unitIntervalMeasure)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _j : Fin 2, ∑ _k : Fin 2, δ := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      simpa only [f,g,samplingClosedIndicator_pair μ X Y hX hY,
        samplingClosedIndicator_integral] using hrect (a j) (b j) (c k) (d k)
    _ = _ := by simp; ring

end
end FiniteFactor

end OAI
