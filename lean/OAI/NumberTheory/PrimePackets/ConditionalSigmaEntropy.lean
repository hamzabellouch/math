import OAI.NumberTheory.PrimePackets.GeneratingObservationEntropy

namespace OAI

/-! # Finite observation entropy conditioned on a sigma algebra -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace PrimeDegreePackets

variable {Y α : Type*} [mY : MeasurableSpace Y] [Fintype α]

def conditionalSigmaEntropy (μ : Measure Y) (P : Y → α) (m : MeasurableSpace Y) : ℝ :=
  ∫ y, finiteShannon (fun a =>
    (μ[({z | P z = a}.indicator (fun _ => (1 : ℝ))) | m]) y) ∂μ

theorem conditionalObservationEntropy_eq_sigma
    {β : Type*} [Fintype β] (μ : Measure Y) [IsFiniteMeasure μ]
    (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    conditionalObservationEntropy μ P Q = conditionalSigmaEntropy μ P (observationSigma Q) := by
  rw [conditionalObservationEntropy_eq_integral μ P Q hP hQ]
  apply integral_congr_ae
  have H := ae_all_iff.mpr (fun a => observationConditionalProbability_ae_eq_condExp μ P Q hP hQ a)
  filter_upwards [H] with y hy
  congr 1
  exact funext hy

theorem conditionalObservationEntropy_tendsto_sigma
    {β : ℕ → Type*} [∀ n, Fintype (β n)]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a})
    (Q : ∀ n, Y → β n) (hQ : ∀ n b, MeasurableSet {y | Q n y = b})
    (hmono : Monotone (fun n => observationSigma (Q n))) :
    Tendsto (fun n => conditionalObservationEntropy μ P (Q n)) atTop
      (𝓝 (conditionalSigmaEntropy μ P (⨆ n, observationSigma (Q n)))) := by
  let ℱ : Filtration ℕ mY :=
    ⟨fun n => observationSigma (Q n), hmono, fun n => observationSigma_le (Q n) (hQ n)⟩
  let F : ℕ → Y → ℝ := fun n y =>
    finiteShannon (fun a => observationConditionalProbability μ P (Q n) a y)
  let G : Y → ℝ := fun y => finiteShannon (fun a =>
    (μ[({z | P z = a}.indicator (fun _ => (1 : ℝ))) | ⨆ n, ℱ n]) y)
  have hFint n : Integrable (F n) μ :=
    integrable_finite_values μ (Q n) (hQ n) (fun b => finiteShannon (fun a =>
      μ.real {y | (Q n y,P y) = (b,a)} / μ.real {y | Q n y = b}))
  have hbound n : ∀ᵐ y ∂μ, ‖F n y‖ ≤ Real.log (Fintype.card α) := by
    filter_upwards [observationConditionalProbability_ae_sum μ P (Q n) hP (hQ n)] with y hy
    have hn := fun a => observationConditionalProbability_nonneg μ P (Q n) a y
    change ‖finiteShannon (fun a => observationConditionalProbability μ P (Q n) a y)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (finiteShannon_nonneg hn hy)]
    exact finiteShannon_le_log_card hn hy
  have hcoord (a : α) : ∀ᵐ y ∂μ,
      Tendsto (fun n => observationConditionalProbability μ P (Q n) a y) atTop
        (𝓝 ((μ[({z | P z = a}.indicator (fun _ => (1 : ℝ))) | ⨆ n, ℱ n]) y)) := by
    have H := MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := ℱ)
      ({z | P z = a}.indicator (fun _ => (1 : ℝ)))
    have heq := ae_all_iff.mpr (fun n =>
      observationConditionalProbability_ae_eq_condExp μ P (Q n) hP (hQ n) a)
    filter_upwards [H,heq] with y hy he
    simpa only [he] using hy
  have hlim : ∀ᵐ y ∂μ, Tendsto (fun n => F n y) atTop (𝓝 (G y)) := by
    filter_upwards [ae_all_iff.mpr hcoord] with y hy
    have H := continuous_finiteShannon.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hy)
    simpa only [F,G,Function.comp_def] using H
  have H := tendsto_integral_of_dominated_convergence
    (fun _ : Y => Real.log (Fintype.card α)) (fun n => (hFint n).aestronglyMeasurable)
    (integrable_const _) hbound hlim
  have heq n : conditionalObservationEntropy μ P (Q n) = ∫ y, F n y ∂μ :=
    conditionalObservationEntropy_eq_integral μ P (Q n) hP (hQ n)
  simpa only [← heq, conditionalSigmaEntropy, G] using H

end PrimeDegreePackets

end

end OAI
