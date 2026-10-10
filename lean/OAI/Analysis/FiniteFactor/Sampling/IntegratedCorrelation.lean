import OAI.Analysis.FiniteFactor.Sampling.LayerCake

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

/-- Bounded nonnegative products are integrable, uniformly in their parameters. -/
theorem sampling_bounded_product_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (C : ℝ) (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ C) (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ C) :
    Integrable (fun x => f x*g x) μ := by
  apply sampling_integrable_bounded μ (fun x => f x*g x) (hf.mul hg) (C^2)
  intro x
  rw [abs_of_nonneg (mul_nonneg (hfb x).1 (hgb x).1)]
  calc
    f x*g x ≤ C*C := mul_le_mul (hfb x).2 (hgb x).2 (hgb x).1 ((hfb x).1.trans (hfb x).2)
    _ = C^2 := by ring

/-- Integrate the actual pointwise pair error over the marginal coordinate. -/
theorem sampling_integrated_pair_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (u : ℝ → ℝ → ℝ) (hu : Measurable (fun p : ℝ × ℝ => u p.1 p.2))
    (C ε : ℝ) (hb : ∀ s t, 0 ≤ u s t ∧ u s t ≤ C)
    (he : ∀ᵐ s ∂unitIntervalMeasure,
      |(∫ x, u s (X x)*u s (Y x) ∂μ)-(∫ t, u s t ∂unitIntervalMeasure)^2| ≤ ε) :
    |(∫ s, ∫ x, u s (X x)*u s (Y x) ∂μ ∂unitIntervalMeasure)-
      (∫ s, (∫ t, u s t ∂unitIntervalMeasure)^2 ∂unitIntervalMeasure)| ≤ ε := by
  have hmX : Measurable (fun p : ℝ × Ω => u p.1 (X p.2)) :=
    hu.comp (measurable_fst.prodMk (hX.comp measurable_snd))
  have hmY : Measurable (fun p : ℝ × Ω => u p.1 (Y p.2)) :=
    hu.comp (measurable_fst.prodMk (hY.comp measurable_snd))
  have hi := sampling_bounded_product_integrable (unitIntervalMeasure.prod μ)
    (fun p => u p.1 (X p.2)) (fun p => u p.1 (Y p.2)) hmX hmY C
    (fun p => hb p.1 (X p.2)) (fun p => hb p.1 (Y p.2))
  have hmean (s : ℝ) : 0 ≤ (∫ t, u s t ∂unitIntervalMeasure) ∧
      (∫ t, u s t ∂unitIntervalMeasure) ≤ C := by
    have hmi : Integrable (u s) unitIntervalMeasure := sampling_integrable_bounded _ _
      (hu.comp (measurable_const.prodMk measurable_id)) C
      (fun t => by rw [abs_of_nonneg (hb s t).1]; exact (hb s t).2)
    exact ⟨integral_nonneg (fun t => (hb s t).1),by
      simpa using integral_mono_ae hmi (integrable_const C) (Eventually.of_forall (fun t => (hb s t).2))⟩
  have hm : Measurable (fun s => ∫ t, u s t ∂unitIntervalMeasure) :=
    hu.stronglyMeasurable.integral_prod_right.measurable
  have hi₂ : Integrable (fun s => (∫ t, u s t ∂unitIntervalMeasure)^2) unitIntervalMeasure := by
    simpa only [pow_two] using sampling_bounded_product_integrable unitIntervalMeasure _ _ hm hm C hmean hmean
  rw [← integral_sub hi.integral_prod_left hi₂]
  have hbound : ∀ᵐ s ∂unitIntervalMeasure,
      ‖(∫ x, u s (X x)*u s (Y x) ∂μ)-(∫ t, u s t ∂unitIntervalMeasure)^2‖ ≤ ε := by
    simpa only [Real.norm_eq_abs] using he
  simpa [Real.norm_eq_abs,measureReal_def] using norm_integral_le_of_norm_le_const hbound

end
end FiniteFactor

end OAI
