import OAI.Probability.InvariantIsing.Cavity.CavityLogCap

namespace OAI

/-! Integrability and separate-expectation form of the cap estimate. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_log_cap_difference_integrable {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω, x))) (ν ω))
    (hi : ∀ᵐ ω ∂P, Integrable (fun x => H (ω, x)^2) ((ν ω).tilted (fun x => H (ω, x))))
    (hmi : Integrable (fun ω => ∫ x, H (ω, x)^2 ∂(ν ω).tilted (fun x => H (ω, x))) P)
    {T : ℝ} (hT : 0 < T) :
    Integrable (fun ω => Real.log (∫ x, Real.exp (H (ω, x)) ∂ν ω) -
      Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) P := by
  have hm : Measurable (fun ω => Real.log (∫ x, Real.exp (H (ω, x)) ∂ν ω) -
      Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) :=
    (measurable_cavityWeightNormalizer ν hν _ hH.exp).log.sub
      (measurable_cavityWeightNormalizer ν hν _ (hH.min measurable_const).exp).log
  apply (hmi.div_const T).mono' hm.aestronglyMeasurable
  filter_upwards [he, hi] with ω hωe hωi
  have hb := cavity_log_cap_error_of_second_moment (ν ω) (fun x => H (ω, x))
    (hH.comp measurable_prodMk_left) hωe hT hωi
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

lemma cavity_full_log_integrable {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω, x))) (ν ω))
    (hi : ∀ᵐ ω ∂P, Integrable (fun x => H (ω, x)^2) ((ν ω).tilted (fun x => H (ω, x))))
    (hmi : Integrable (fun ω => ∫ x, H (ω, x)^2 ∂(ν ω).tilted (fun x => H (ω, x))) P)
    {T : ℝ} (hT : 0 < T)
    (hc : Integrable (fun ω => Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) P) :
    Integrable (fun ω => Real.log (∫ x, Real.exp (H (ω, x)) ∂ν ω)) P := by
  have hd := cavity_log_cap_difference_integrable P ν hν H hH he hi hmi hT
  apply (hd.add hc).congr
  filter_upwards [] with ω
  dsimp only [Pi.add_apply]
  ring

lemma cavity_log_cap_expectation_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω, x))) (ν ω))
    (hi : ∀ᵐ ω ∂P, Integrable (fun x => H (ω, x)^2) ((ν ω).tilted (fun x => H (ω, x))))
    (hmi : Integrable (fun ω => ∫ x, H (ω, x)^2 ∂(ν ω).tilted (fun x => H (ω, x))) P)
    {K T : ℝ} (hK : (∫ ω, ∫ x, H (ω, x)^2 ∂(ν ω).tilted (fun x => H (ω, x)) ∂P) ≤ K)
    (hT : 0 < T)
    (hc : Integrable (fun ω => Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) P) :
    |(∫ ω, Real.log (∫ x, Real.exp (H (ω, x)) ∂ν ω) ∂P) -
      ∫ ω, Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω) ∂P| ≤ K / T := by
  have hfull := cavity_full_log_integrable P ν hν H hH he hi hmi hT hc
  rw [← integral_sub hfull hc]
  have hb := cavity_log_cap_mean_error P ν hν H hH he hi hmi hK hT
  rw [abs_of_nonneg hb.1]
  exact hb.2

end InvariantIsing

end

end OAI
