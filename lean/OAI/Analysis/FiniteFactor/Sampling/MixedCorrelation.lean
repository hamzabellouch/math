import OAI.Analysis.FiniteFactor.Sampling.IntegratedCorrelation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

/-- A bounded nonnegative coordinate kernel has a measurable bounded mean. -/
theorem sampling_kernel_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : ℝ → Ω → ℝ)
    (hu : Measurable (fun p : ℝ × Ω => u p.1 p.2)) (C : ℝ)
    (hb : ∀ s t, 0 ≤ u s t ∧ u s t ≤ C) :
    Measurable (fun s => ∫ t, u s t ∂μ) ∧
    ∀ s, 0 ≤ (∫ t, u s t ∂μ) ∧ (∫ t, u s t ∂μ) ≤ C := by
  refine ⟨hu.stronglyMeasurable.integral_prod_right.measurable,?_⟩
  intro s
  have hi : Integrable (u s) μ := sampling_integrable_bounded μ _
    (hu.comp (measurable_const.prodMk measurable_id)) C
    (fun t => by rw [abs_of_nonneg (hb s t).1]; exact (hb s t).2)
  exact ⟨integral_nonneg (fun t => (hb s t).1),by
    simpa using integral_mono_ae hi (integrable_const C) (Eventually.of_forall (fun t => (hb s t).2))⟩

/-- The mixed coordinate factor inherits a relative one-phase error.
The ideal moment may vanish; no division by it occurs. -/
theorem sampling_integrated_mixed_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (u : ℝ → ℝ → ℝ) (hu : Measurable (fun p : ℝ × ℝ => u p.1 p.2))
    (C ε : ℝ) (hb : ∀ s t, 0 ≤ u s t ∧ u s t ≤ C)
    (he : ∀ s, |(∫ x, u s (X x) ∂μ)-(∫ t, u s t ∂unitIntervalMeasure)| ≤
      ε*(∫ t, u s t ∂unitIntervalMeasure)) :
    |(∫ s, (∫ t, u s t ∂unitIntervalMeasure)*(∫ x, u s (X x) ∂μ) ∂unitIntervalMeasure)-
      (∫ s, (∫ t, u s t ∂unitIntervalMeasure)^2 ∂unitIntervalMeasure)| ≤
      ε*(∫ s, (∫ t, u s t ∂unitIntervalMeasure)^2 ∂unitIntervalMeasure) := by
  let a := fun s => ∫ t, u s t ∂unitIntervalMeasure
  let b := fun s => ∫ x, u s (X x) ∂μ
  have ha := sampling_kernel_mean unitIntervalMeasure u hu C hb
  have hbu : Measurable (fun p : ℝ × Ω => u p.1 (X p.2)) :=
    hu.comp (measurable_fst.prodMk (hX.comp measurable_snd))
  have hbb := sampling_kernel_mean μ (fun s x => u s (X x)) hbu C (fun s x => hb s (X x))
  have hai : Integrable (fun s => a s^2) unitIntervalMeasure := by
    simpa only [pow_two] using sampling_bounded_product_integrable unitIntervalMeasure a a ha.1 ha.1 C ha.2 ha.2
  have habi := sampling_bounded_product_integrable unitIntervalMeasure a b ha.1 hbb.1 C ha.2 hbb.2
  change |(∫ s, a s*b s ∂unitIntervalMeasure)-(∫ s, a s^2 ∂unitIntervalMeasure)| ≤
    ε*(∫ s, a s^2 ∂unitIntervalMeasure)
  rw [← integral_sub habi hai,← integral_const_mul]
  apply (show |(∫ s, a s*b s-a s^2 ∂unitIntervalMeasure)| ≤
      ∫ s, ε*a s^2 ∂unitIntervalMeasure from ?_)
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (hai.const_mul ε)
  apply Eventually.of_forall
  intro s
  rw [Real.norm_eq_abs]
  calc
    |a s*b s-a s^2| = a s*|b s-a s| := by
      rw [show a s*b s-a s^2 = a s*(b s-a s) by ring,abs_mul,abs_of_nonneg (ha.2 s).1]
    _ ≤ a s*(ε*a s) := mul_le_mul_of_nonneg_left (he s) (ha.2 s).1
    _ = ε*a s^2 := by ring

end
end FiniteFactor

end OAI
