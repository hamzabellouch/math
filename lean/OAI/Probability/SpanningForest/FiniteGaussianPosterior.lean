import OAI.Probability.SpanningForest.FinitePosterior
import OAI.Probability.SpanningForest.GaussianObservationKernel

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators ProbabilityTheory

namespace Problem336.FinitePosterior

variable {Θ ι : Type*} [Fintype Θ] [MeasurableSpace Θ]
    [MeasurableSingletonClass Θ] [Fintype ι]

def gaussianLikelihood (t : ℝ≥0) (signal : Θ → ι → ℝ) (θ : Θ) (y : ι → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (∑ i, (y i - (t : ℝ) / 2) * signal θ i))

omit [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ] in
lemma measurable_gaussianLikelihood (t : ℝ≥0) (signal : Θ → ι → ℝ) (θ : Θ) :
    Measurable (gaussianLikelihood t signal θ) := by
  unfold gaussianLikelihood
  fun_prop

lemma gaussianObservationKernel_eq_withDensity (t : ℝ≥0) (ht : t ≠ 0)
    (signal : Θ → ι → ℝ) (hbinary : ∀ θ i, signal θ i = 0 ∨ signal θ i = 1)
    (θ : Θ) :
    GaussianObservation.endpointKernel t signal θ =
      (Measure.pi (fun _ : ι => gaussianReal 0 t)).withDensity
        (gaussianLikelihood t signal θ) := by
  rw [GaussianObservation.endpointKernel_apply t ht signal
    (fun i => measurable_of_countable (fun θ => signal θ i)) hbinary θ]
  exact GaussianObservation.gaussian_pi_binary_shift_withDensity t ht (signal θ) (hbinary θ)

theorem gaussian_condExp_eq_exponential_ratio
    [StandardBorelSpace Θ] [Nonempty Θ]
    (π : Measure Θ) [IsProbabilityMeasure π]
    (t : ℝ≥0) (ht : t ≠ 0) (signal : Θ → ι → ℝ)
    (hbinary : ∀ θ i, signal θ i = 0 ∨ signal θ i = 1) (g : Θ → ℝ) :
    (π ⊗ₘ GaussianObservation.endpointKernel t signal)[fun z : Θ × (ι → ℝ) => g z.1 |
      (inferInstance : MeasurableSpace (ι → ℝ)).comap Prod.snd] =ᵐ[
        π ⊗ₘ GaussianObservation.endpointKernel t signal]
      fun z =>
        (∑ θ, (π {θ}).toReal *
          Real.exp (∑ i, (z.2 i - (t : ℝ) / 2) * signal θ i) * g θ) /
        (∑ θ, (π {θ}).toReal *
          Real.exp (∑ i, (z.2 i - (t : ℝ) / 2) * signal θ i)) := by
  let := GaussianObservation.endpointKernel_markov t ht signal
    (fun i => measurable_of_countable (fun θ => signal θ i)) hbinary
  have hfinite : ∀ θ y, gaussianLikelihood t signal θ y ≠ ∞ := by
    intro θ y
    exact ENNReal.ofReal_ne_top
  have hpositive : ∀ θ y, gaussianLikelihood t signal θ y ≠ 0 := by
    intro θ y
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have h := condExp_eq_likelihood_ratio π (GaussianObservation.endpointKernel t signal)
    (Measure.pi (fun _ : ι => gaussianReal 0 t)) (gaussianLikelihood t signal)
    (measurable_gaussianLikelihood t signal) hfinite
    (mixtureDensity_ne_zero_of_positive π _ hpositive)
    (gaussianObservationKernel_eq_withDensity t ht signal hbinary) g
  simpa only [mixtureDensity_toReal π _ hfinite, gaussianLikelihood,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] using h

theorem gaussian_condExp_eq_exponential_ratio_of_jointLaw
    [StandardBorelSpace Θ] [Nonempty Θ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → Θ) (Yobs : Ω → (ι → ℝ)) (hX : Measurable X) (hY : Measurable Yobs)
    (π : Measure Θ) [IsProbabilityMeasure π]
    (t : ℝ≥0) (ht : t ≠ 0) (signal : Θ → ι → ℝ)
    (hbinary : ∀ θ i, signal θ i = 0 ∨ signal θ i = 1)
    (hjoint : P.map (fun ω => (X ω, Yobs ω)) =
      π ⊗ₘ GaussianObservation.endpointKernel t signal) (g : Θ → ℝ) :
    P[fun ω => g (X ω) | (inferInstance : MeasurableSpace (ι → ℝ)).comap Yobs] =ᵐ[P]
      fun ω =>
        (∑ θ, (π {θ}).toReal *
          Real.exp (∑ i, (Yobs ω i - (t : ℝ) / 2) * signal θ i) * g θ) /
        (∑ θ, (π {θ}).toReal *
          Real.exp (∑ i, (Yobs ω i - (t : ℝ) / 2) * signal θ i)) := by
  let := GaussianObservation.endpointKernel_markov t ht signal
    (fun i => measurable_of_countable (fun θ => signal θ i)) hbinary
  have hfinite : ∀ θ y, gaussianLikelihood t signal θ y ≠ ∞ := by
    intro θ y
    exact ENNReal.ofReal_ne_top
  have hpositive : ∀ θ y, gaussianLikelihood t signal θ y ≠ 0 := by
    intro θ y
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have h := condExp_eq_likelihood_ratio_of_jointLaw P X Yobs hX hY π
    (GaussianObservation.endpointKernel t signal) hjoint
    (Measure.pi (fun _ : ι => gaussianReal 0 t)) (gaussianLikelihood t signal)
    (measurable_gaussianLikelihood t signal) hfinite
    (mixtureDensity_ne_zero_of_positive π _ hpositive)
    (gaussianObservationKernel_eq_withDensity t ht signal hbinary) g
  simpa only [mixtureDensity_toReal π _ hfinite, gaussianLikelihood,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] using h

theorem gaussian_condExp_eq_exponential_ratio_of_independent
    [StandardBorelSpace Θ] [Nonempty Θ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Θ) (noise : Ω → (ι → ℝ)) (hX : Measurable X) (hnoise : Measurable noise)
    (π : Measure Θ) [IsProbabilityMeasure π]
    (t : ℝ≥0) (ht : t ≠ 0) (signal : Θ → ι → ℝ)
    (hbinary : ∀ θ i, signal θ i = 0 ∨ signal θ i = 1)
    (hprior : P.map X = π)
    (hnoiseLaw : P.map noise = Measure.pi (fun _ : ι => gaussianReal 0 t))
    (hindep : X ⟂ᵢ[P] noise) (g : Θ → ℝ) :
    let Yobs := fun ω i => (t : ℝ) * signal (X ω) i + noise ω i
    P[fun ω => g (X ω) | (inferInstance : MeasurableSpace (ι → ℝ)).comap Yobs] =ᵐ[P]
      fun ω =>
        (∑ θ, (π {θ}).toReal *
          Real.exp (∑ i, (Yobs ω i - (t : ℝ) / 2) * signal θ i) * g θ) /
        (∑ θ, (π {θ}).toReal *
          Real.exp (∑ i, (Yobs ω i - (t : ℝ) / 2) * signal θ i)) := by
  let Yobs := fun ω i => (t : ℝ) * signal (X ω) i + noise ω i
  have hs : Measurable signal := measurable_of_countable signal
  have hY : Measurable Yobs := by
    unfold Yobs
    fun_prop
  have hjoint := GaussianObservation.hasLaw_independent_gaussian_observation P π t ht signal
    (fun i => measurable_of_countable (fun θ => signal θ i)) hbinary X noise
    ⟨hX.aemeasurable, hprior⟩ ⟨hnoise.aemeasurable, hnoiseLaw⟩ hindep
  exact gaussian_condExp_eq_exponential_ratio_of_jointLaw P X Yobs hX hY π t ht signal
    hbinary hjoint.map_eq g

end Problem336.FinitePosterior

end

end OAI
