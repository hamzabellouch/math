import OAI.Probability.GammaPassage.FiniteTilt
import OAI.Probability.GammaPassage.FirstMoment

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

lemma finiteGammaMeasure_ae_nonneg {shape rate : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ v ∂finiteGammaMeasure (ι := ι) shape rate, ∀ i, 0 ≤ v i := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) :=
    isProbabilityMeasure_gammaMeasure hs hr
  unfold finiteGammaMeasure
  rw [ae_all_iff]
  intro i
  exact ((measurePreserving_eval (fun _ : ι => gammaMeasure shape rate) i).quasiMeasurePreserving.ae (gamma_ae_pos shape rate)).mono (fun _ hu => hu.le)

/-- Nonnegative integrals factor over a finite product of probability measures. -/
private lemma finite_probability_lintegral_prod (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (f : ι → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ v, ∏ i, f i (v i) ∂Measure.pi μ) = ∏ i, ∫⁻ u, f i u ∂μ i := by
  have hi : iIndepFun (fun i (v : ι → ℝ) => f i (v i)) (Measure.pi μ) :=
    iIndepFun_pi (fun i => (hf i).aemeasurable)
  have hh := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hi
    (fun i => (hf i).comp (measurable_pi_apply i))
  rw [hh]
  apply Finset.prod_congr rfl
  intro i _
  rw [← lintegral_map (hf i) (measurable_pi_apply i),
    (measurePreserving_eval μ i).map_eq]

/-- Exact nonnegative exponential moment for the sum of all finite coordinates. -/
theorem finite_gamma_lintegral_exp_sum {shape rate t : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (ht : t < rate) :
    (∫⁻ v : ι → ℝ, ENNReal.ofReal (Real.exp (t * ∑ i, v i))
      ∂finiteGammaMeasure shape rate) =
      (ENNReal.ofReal ((rate / (rate-t)) ^ shape)) ^ Fintype.card ι := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) :=
    isProbabilityMeasure_gammaMeasure hs hr
  have he (v : ι → ℝ) : ENNReal.ofReal (Real.exp (t * ∑ i, v i)) =
      ∏ i, ENNReal.ofReal (Real.exp (t * v i)) := by
    rw [Finset.mul_sum, Real.exp_sum]
    exact ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)
  simp_rw [he]
  unfold finiteGammaMeasure
  rw [finite_probability_lintegral_prod _
    (fun _ u => ENNReal.ofReal (Real.exp (t*u))) (fun _ => by fun_prop)]
  simp only [gamma_lintegral_exp hs hr ht, Finset.prod_const, Finset.card_univ]

/-- The exponential moment of the coordinate sum is finite for every `t < rate`. -/
theorem finite_gamma_integrable_exp_sum {shape rate t : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (ht : t < rate) :
    Integrable (fun v : ι → ℝ => Real.exp (t * ∑ i, v i))
      (finiteGammaMeasure shape rate) := by
  have hm : Measurable (fun v : ι → ℝ => Real.exp (t * ∑ i, v i)) := by fun_prop
  apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun v => (Real.exp_pos _).le))).mp
  rw [finite_gamma_lintegral_exp_sum hs hr ht]
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

end GammaFPP

end OAI
