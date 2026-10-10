import OAI.NumberTheory.PrimePackets.ConditionalProbabilityExpectation

namespace OAI

/-!
# Entropy approximation by generating finite observations

The increasing sigma algebras of a generating sequence exhaust each
measurable finite observation. Martingale convergence, followed by bounded
convergence of finite Shannon entropy, makes the conditional entropy vanish.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace PrimeDegreePackets

variable {Y α : Type*} [mY : MeasurableSpace Y] [Fintype α]

omit [Fintype α] in
theorem observationConditionalProbability_tendsto
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a})
    {k : ℕ → ℕ} (Q : ∀ n, Y → Fin (k n))
    (hQ : ∀ n b, MeasurableSet {y | Q n y = b})
    (hmono : Monotone (fun n => observationSigma (Q n)))
    (hgen : (⨆ n, observationSigma (Q n)) = mY) (a : α) :
    ∀ᵐ y ∂μ, Tendsto (fun n => observationConditionalProbability μ P (Q n) a y) atTop
      (𝓝 (({z | P z = a}.indicator (fun _ => (1 : ℝ))) y)) := by
  let ℱ : Filtration ℕ mY :=
    ⟨fun n => observationSigma (Q n), hmono, fun n => observationSigma_le (Q n) (hQ n)⟩
  let g : Y → ℝ := {z | P z = a}.indicator (fun _ => 1)
  have hg : Integrable g μ := (integrable_const (1 : ℝ)).indicator (hP a)
  have hgmeas : StronglyMeasurable[⨆ n, ℱ n] g := by
    change StronglyMeasurable[⨆ n, observationSigma (Q n)] g
    rw [hgen]
    exact (measurable_const.indicator (hP a)).stronglyMeasurable
  have hlim := hg.tendsto_ae_condExp (ℱ := ℱ) hgmeas
  have heq : ∀ᵐ y ∂μ, ∀ n,
      observationConditionalProbability μ P (Q n) a y = (μ[g | ℱ n]) y := by
    apply ae_all_iff.mpr
    intro n
    exact observationConditionalProbability_ae_eq_condExp μ P (Q n) hP (hQ n) a
  filter_upwards [hlim,heq] with y hy he
  simpa only [he] using hy

theorem conditionalObservationEntropy_tendsto_zero
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a})
    {k : ℕ → ℕ} (Q : ∀ n, Y → Fin (k n))
    (hQ : ∀ n b, MeasurableSet {y | Q n y = b})
    (hmono : Monotone (fun n => observationSigma (Q n)))
    (hgen : (⨆ n, observationSigma (Q n)) = mY) :
    Tendsto (fun n => conditionalObservationEntropy μ P (Q n)) atTop (𝓝 0) := by
  let F : ℕ → Y → ℝ := fun n y =>
    finiteShannon (fun a => observationConditionalProbability μ P (Q n) a y)
  have hFint n : Integrable (F n) μ :=
    integrable_finite_values μ (Q n) (hQ n) (fun b => finiteShannon (fun a =>
      μ.real {y | (Q n y,P y) = (b,a)} / μ.real {y | Q n y = b}))
  have hbound n : ∀ᵐ y ∂μ, ‖F n y‖ ≤ Real.log (Fintype.card α) := by
    filter_upwards [observationConditionalProbability_ae_sum μ P (Q n) hP (hQ n)] with y hy
    have hn := fun a => observationConditionalProbability_nonneg μ P (Q n) a y
    change ‖finiteShannon (fun a => observationConditionalProbability μ P (Q n) a y)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (finiteShannon_nonneg hn hy)]
    exact finiteShannon_le_log_card hn hy
  have hlim : ∀ᵐ y ∂μ, Tendsto (fun n => F n y) atTop (𝓝 0) := by
    have H : ∀ᵐ y ∂μ, ∀ a,
        Tendsto (fun n => observationConditionalProbability μ P (Q n) a y) atTop
          (𝓝 (({z | P z = a}.indicator (fun _ => (1 : ℝ))) y)) :=
      ae_all_iff.mpr (fun a => observationConditionalProbability_tendsto μ P hP Q hQ hmono hgen a)
    filter_upwards [H] with y hy
    have hvec := tendsto_pi_nhds.mpr hy
    have H' := continuous_finiteShannon.continuousAt.tendsto.comp hvec
    have hz : finiteShannon (fun a => ({z | P z = a}.indicator (fun _ => (1 : ℝ))) y) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      by_cases ha : P y = a <;> simp [ha]
    change Tendsto (fun n => finiteShannon
      (fun a => observationConditionalProbability μ P (Q n) a y)) atTop (𝓝 0)
    simpa only [Function.comp_def, hz] using H'
  have H := tendsto_integral_of_dominated_convergence
    (fun _ : Y => Real.log (Fintype.card α)) (fun n => (hFint n).aestronglyMeasurable)
    (integrable_const _) hbound hlim
  have heq n : conditionalObservationEntropy μ P (Q n) = ∫ y, F n y ∂μ :=
    conditionalObservationEntropy_eq_integral μ P (Q n) hP (hQ n)
  simpa only [← heq, integral_zero] using H

end PrimeDegreePackets

end

end OAI
