import OAI.Probability.SpanningForest.FiniteTiltLimit

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

namespace Problem336
namespace FiniteTiltLimit

variable {S : Type*} [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

theorem sum_real_singleton_eq_one (μ : Measure S) [IsProbabilityMeasure μ] :
    ∑ s, μ.real {s} = 1 := by
  simp

theorem mean_measure_eq_integral_ratio (μ : Measure S) [IsFiniteMeasure μ]
    (w f : S → ℝ) :
    mean (fun s => μ.real {s}) w f =
      (∫ s, w s * f s ∂μ) / (∫ s, w s ∂μ) := by
  simp only [mean, partition, integral_fintype (Integrable.of_finite), smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact mul_assoc _ _ _

omit [Fintype S] [MeasurableSingletonClass S] in

theorem tendsto_real_singleton {μ : ℕ → Measure S} {ν : Measure S}
    [IsFiniteMeasure ν]
    (h : ∀ s, Tendsto (fun n => μ n {s}) atTop (nhds (ν {s}))) (s : S) :
    Tendsto (fun n => (μ n).real {s}) atTop (nhds (ν.real {s})) :=
  (ENNReal.tendsto_toReal (measure_ne_top ν {s})).comp (h s)

theorem tendsto_integral_ratio {μ : ℕ → Measure S} {ν : Measure S}
    [∀ n, IsFiniteMeasure (μ n)] [IsProbabilityMeasure ν]
    (h : ∀ s, Tendsto (fun n => μ n {s}) atTop (nhds (ν {s})))
    (w f : S → ℝ) (hw : ∀ s, 0 < w s) :
    Tendsto (fun n => (∫ s, w s * f s ∂μ n) / (∫ s, w s ∂μ n))
      atTop (nhds ((∫ s, w s * f s ∂ν) / (∫ s, w s ∂ν))) := by
  simpa only [mean_measure_eq_integral_ratio] using
    tendsto_mean_of_probability (tendsto_real_singleton h)
      (fun s => measureReal_nonneg) (sum_real_singleton_eq_one ν) hw

theorem integral_ratio_response_le {μ : ℕ → Measure S} {ν : Measure S}
    [∀ n, IsFiniteMeasure (μ n)] [IsProbabilityMeasure ν]
    (h : ∀ s, Tendsto (fun n => μ n {s}) atTop (nhds (ν {s})))
    (w w' f : S → ℝ) (hw : ∀ s, 0 < w s) (hw' : ∀ s, 0 < w' s)
    {d : ℝ} (hresponse : ∀ n,
      |(∫ s, w s * f s ∂μ n) / (∫ s, w s ∂μ n) -
        (∫ s, w' s * f s ∂μ n) / (∫ s, w' s ∂μ n)| ≤ d) :
    |(∫ s, w s * f s ∂ν) / (∫ s, w s ∂ν) -
      (∫ s, w' s * f s ∂ν) / (∫ s, w' s ∂ν)| ≤ d := by
  exact le_of_tendsto
    (((tendsto_integral_ratio h w f hw).sub
      (tendsto_integral_ratio h w' f hw')).abs)
    (Eventually.of_forall hresponse)

theorem mean_statistic_eq_integral_ratio {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (R : Ω → S) (hR : Measurable R)
    (w f : S → ℝ) :
    mean (fun s => μ.real (R ⁻¹' {s})) w f =
      (∫ ω, w (R ω) * f (R ω) ∂μ) / (∫ ω, w (R ω) ∂μ) := by
  have h := mean_measure_eq_integral_ratio (μ.map R) w f
  simp only [map_measureReal_apply hR (measurableSet_singleton _)] at h
  rw [integral_map_of_stronglyMeasurable hR
      (measurable_of_finite (fun s => w s * f s)).stronglyMeasurable,
    integral_map_of_stronglyMeasurable hR
      (measurable_of_finite w).stronglyMeasurable] at h
  exact h

theorem tendsto_statistic_integral_ratio {Ω : Type*} [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω} {ν : Measure Ω}
    [∀ n, IsFiniteMeasure (μ n)] [IsProbabilityMeasure ν]
    (R : Ω → S) (hR : Measurable R)
    (h : ∀ s, Tendsto (fun n => μ n (R ⁻¹' {s})) atTop
      (nhds (ν (R ⁻¹' {s}))))
    (w f : S → ℝ) (hw : ∀ s, 0 < w s) :
    Tendsto (fun n =>
      (∫ ω, w (R ω) * f (R ω) ∂μ n) / (∫ ω, w (R ω) ∂μ n))
      atTop (nhds ((∫ ω, w (R ω) * f (R ω) ∂ν) /
        (∫ ω, w (R ω) ∂ν))) := by
  have hp : ∀ s, Tendsto (fun n => (μ n).real (R ⁻¹' {s})) atTop
      (nhds (ν.real (R ⁻¹' {s}))) := fun s =>
    (ENNReal.tendsto_toReal (measure_ne_top ν (R ⁻¹' {s}))).comp (h s)
  have hsum : ∑ s, ν.real (R ⁻¹' {s}) = 1 := by
    simpa using (sum_measureReal_preimage_singleton (μ := ν)
      (Finset.univ : Finset S) (fun s _ => hR (measurableSet_singleton s)))
  simpa only [mean_statistic_eq_integral_ratio _ R hR] using
    tendsto_mean_of_probability hp (fun s => measureReal_nonneg) hsum hw

theorem statistic_integral_ratio_response_le_of_eventually
    {Ω : Type*} [MeasurableSpace Ω] {μ : ℕ → Measure Ω} {ν : Measure Ω}
    [∀ n, IsFiniteMeasure (μ n)] [IsProbabilityMeasure ν]
    (R : Ω → S) (hR : Measurable R)
    (h : ∀ s, Tendsto (fun n => μ n (R ⁻¹' {s})) atTop
      (nhds (ν (R ⁻¹' {s}))))
    (w w' f : S → ℝ) (hw : ∀ s, 0 < w s) (hw' : ∀ s, 0 < w' s)
    {d : ℝ} (hresponse : ∀ᶠ n in atTop,
      |(∫ ω, w (R ω) * f (R ω) ∂μ n) / (∫ ω, w (R ω) ∂μ n) -
        (∫ ω, w' (R ω) * f (R ω) ∂μ n) / (∫ ω, w' (R ω) ∂μ n)| ≤ d) :
    |(∫ ω, w (R ω) * f (R ω) ∂ν) / (∫ ω, w (R ω) ∂ν) -
      (∫ ω, w' (R ω) * f (R ω) ∂ν) / (∫ ω, w' (R ω) ∂ν)| ≤ d := by
  exact le_of_tendsto
    (((tendsto_statistic_integral_ratio R hR h w f hw).sub
      (tendsto_statistic_integral_ratio R hR h w' f hw')).abs) hresponse

theorem statistic_integral_ratio_response_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω} {ν : Measure Ω}
    [∀ n, IsFiniteMeasure (μ n)] [IsProbabilityMeasure ν]
    (R : Ω → S) (hR : Measurable R)
    (h : ∀ s, Tendsto (fun n => μ n (R ⁻¹' {s})) atTop
      (nhds (ν (R ⁻¹' {s}))))
    (w w' f : S → ℝ) (hw : ∀ s, 0 < w s) (hw' : ∀ s, 0 < w' s)
    {d : ℝ} (hresponse : ∀ n,
      |(∫ ω, w (R ω) * f (R ω) ∂μ n) / (∫ ω, w (R ω) ∂μ n) -
        (∫ ω, w' (R ω) * f (R ω) ∂μ n) / (∫ ω, w' (R ω) ∂μ n)| ≤ d) :
    |(∫ ω, w (R ω) * f (R ω) ∂ν) / (∫ ω, w (R ω) ∂ν) -
      (∫ ω, w' (R ω) * f (R ω) ∂ν) / (∫ ω, w' (R ω) ∂ν)| ≤ d := by
  exact le_of_tendsto
    (((tendsto_statistic_integral_ratio R hR h w f hw).sub
      (tendsto_statistic_integral_ratio R hR h w' f hw')).abs)
    (Eventually.of_forall hresponse)

end FiniteTiltLimit
end Problem336

end

end OAI
