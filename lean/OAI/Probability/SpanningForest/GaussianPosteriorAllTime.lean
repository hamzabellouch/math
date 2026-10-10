import OAI.Probability.SpanningForest.FinitePosteriorTilt

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators ProbabilityTheory

namespace Problem336.FinitePosterior

variable {Θ ι : Type*} [Fintype Θ] [MeasurableSpace Θ]
    [MeasurableSingletonClass Θ] [Fintype ι]

lemma gaussianObservationKernel_eq_withDensity_all (t : ℝ≥0)
    (signal : Θ → ι → ℝ) (hbinary : ∀ θ i, signal θ i = 0 ∨ signal θ i = 1)
    (θ : Θ) :
    GaussianObservation.endpointKernel t signal θ =
      (Measure.pi (fun _ : ι => gaussianReal 0 t)).withDensity
        (gaussianLikelihood t signal θ) := by
  rw [GaussianObservation.endpointKernel_apply_all t signal
    (fun i => measurable_of_countable (fun θ => signal θ i)) hbinary θ]
  exact GaussianObservation.gaussian_pi_binary_shift_withDensity_all t (signal θ) (hbinary θ)

theorem gaussian_condExp_eq_exponential_ratio_all
    [StandardBorelSpace Θ] [Nonempty Θ]
    (π : Measure Θ) [IsProbabilityMeasure π]
    (t : ℝ≥0) (signal : Θ → ι → ℝ)
    (hbinary : ∀ θ i, signal θ i = 0 ∨ signal θ i = 1) (g : Θ → ℝ) :
    (π ⊗ₘ GaussianObservation.endpointKernel t signal)[fun z : Θ × (ι → ℝ) => g z.1 |
      (inferInstance : MeasurableSpace (ι → ℝ)).comap Prod.snd] =ᵐ[
        π ⊗ₘ GaussianObservation.endpointKernel t signal]
      fun z =>
        (∑ θ, (π {θ}).toReal *
          Real.exp (∑ i, (z.2 i - (t : ℝ) / 2) * signal θ i) * g θ) /
        (∑ θ, (π {θ}).toReal *
          Real.exp (∑ i, (z.2 i - (t : ℝ) / 2) * signal θ i)) := by
  let := GaussianObservation.endpointKernel_markov_all t signal
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
    (gaussianObservationKernel_eq_withDensity_all t signal hbinary) g
  simpa only [mixtureDensity_toReal π _ hfinite, gaussianLikelihood,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] using h

theorem gaussian_condExp_eq_exponential_ratio_of_jointLaw_all
    [StandardBorelSpace Θ] [Nonempty Θ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → Θ) (Yobs : Ω → (ι → ℝ)) (hX : Measurable X) (hY : Measurable Yobs)
    (π : Measure Θ) [IsProbabilityMeasure π]
    (t : ℝ≥0) (signal : Θ → ι → ℝ)
    (hbinary : ∀ θ i, signal θ i = 0 ∨ signal θ i = 1)
    (hjoint : P.map (fun ω => (X ω, Yobs ω)) =
      π ⊗ₘ GaussianObservation.endpointKernel t signal) (g : Θ → ℝ) :
    P[fun ω => g (X ω) | (inferInstance : MeasurableSpace (ι → ℝ)).comap Yobs] =ᵐ[P]
      fun ω =>
        (∑ θ, (π {θ}).toReal *
          Real.exp (∑ i, (Yobs ω i - (t : ℝ) / 2) * signal θ i) * g θ) /
        (∑ θ, (π {θ}).toReal *
          Real.exp (∑ i, (Yobs ω i - (t : ℝ) / 2) * signal θ i)) := by
  let := GaussianObservation.endpointKernel_markov_all t signal
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
    (gaussianObservationKernel_eq_withDensity_all t signal hbinary) g
  simpa only [mixtureDensity_toReal π _ hfinite, gaussianLikelihood,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] using h

theorem gaussian_condExp_eq_exponential_ratio_of_independent_all
    [StandardBorelSpace Θ] [Nonempty Θ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Θ) (noise : Ω → (ι → ℝ)) (hX : Measurable X) (hnoise : Measurable noise)
    (π : Measure Θ) [IsProbabilityMeasure π]
    (t : ℝ≥0) (signal : Θ → ι → ℝ)
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
  have hjoint := GaussianObservation.hasLaw_independent_gaussian_observation_all P π t signal
    (fun i => measurable_of_countable (fun θ => signal θ i)) hbinary X noise
    ⟨hX.aemeasurable, hprior⟩ ⟨hnoise.aemeasurable, hnoiseLaw⟩ hindep
  exact gaussian_condExp_eq_exponential_ratio_of_jointLaw_all P X Yobs hX hY π t signal
    hbinary hjoint.map_eq g

theorem binaryField_gaussian_condExp_all
    {Ω I ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure (I → Bool)) [IsProbabilityMeasure ν]
    (X : Ω → (I → Bool)) (noise : Ω → (ι → ℝ))
    (hX : Measurable X) (hnoise : Measurable noise)
    (observed : ι → I) (target : I) (t : ℝ≥0)
    (hprior : P.map X = ν)
    (hnoiseLaw : P.map noise = Measure.pi (fun _ : ι => gaussianReal 0 t))
    (hindep : X ⟂ᵢ[P] noise) :
    let Yobs := fun ω j => (t : ℝ) * binaryValue (X ω (observed j)) + noise ω j
    P[fun ω => binaryValue (X ω target) |
      (inferInstance : MeasurableSpace (ι → ℝ)).comap Yobs] =ᵐ[P]
      fun ω => gaussianFiniteTilt ν observed target t (Yobs ω) := by
  classical
  let R : (I → Bool) → Bool × (ι → Bool) := binarySummary observed target
  have hR : Measurable R := measurable_binarySummary observed target
  let π := ν.map R
  let : IsProbabilityMeasure π := inferInstance
  let signal : (Bool × (ι → Bool)) → ι → ℝ := fun θ j => binaryValue (θ.2 j)
  let g : (Bool × (ι → Bool)) → ℝ := fun θ => binaryValue θ.1
  have hsignal : ∀ θ j, signal θ j = 0 ∨ signal θ j = 1 := by
    intro θ j
    exact binaryValue_binary _
  have hprior' : P.map (fun ω => R (X ω)) = π := by
    change P.map (R ∘ X) = ν.map R
    rw [← Measure.map_map hR hX, hprior]
  have hindep' : (fun ω => R (X ω)) ⟂ᵢ[P] noise := by
    simpa only [Function.comp_def, id_eq] using hindep.comp hR measurable_id
  have h := gaussian_condExp_eq_exponential_ratio_of_independent_all P
    (fun ω => R (X ω)) noise (hR.comp hX) hnoise π t signal hsignal
    hprior' hnoiseLaw hindep' g
  have hratio (y : ι → ℝ) :
      (∑ θ, (π {θ}).toReal * Real.exp (∑ j, (y j - (t : ℝ) / 2) * signal θ j) * g θ) /
        (∑ θ, (π {θ}).toReal * Real.exp (∑ j, (y j - (t : ℝ) / 2) * signal θ j)) =
      gaussianFiniteTilt ν observed target t y := by
    simpa only [π, R, signal, g, binarySummary, gaussianFiniteTilt] using
      finiteMarginal_ratio_eq_integral ν R hR
        (fun θ => Real.exp (∑ j, (y j - (t : ℝ) / 2) * signal θ j)) g
  filter_upwards [h] with ω hω
  exact hω.trans (hratio _)

theorem binaryField_finset_condExp_all
    {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ProbabilityMeasure (I → Bool))
    (X : Ω → (I → Bool)) (noise : Ω → (I → ℝ))
    (hX : Measurable X) (hnoise : Measurable noise)
    (S : Finset I) (e : I) (t : ℝ≥0)
    (hprior : P.map X = (ν : Measure (I → Bool)))
    (hnoiseLaw : P.map (fun ω (i : S) => noise ω i) =
      Measure.pi (fun _ : S => gaussianReal 0 t))
    (hindep : X ⟂ᵢ[P] noise) :
    let Y := fun ω i => (t : ℝ) * TiltLimit.bit (X ω i) + noise ω i
    P[fun ω => TiltLimit.bit (X ω e) |
      (inferInstance : MeasurableSpace (S → ℝ)).comap (fun ω (i : S) => Y ω i)] =ᵐ[P]
      fun ω => TiltLimit.finiteTiltMean ν S (fun i => Y ω i - (t : ℝ) / 2) e := by
  classical
  let restrict : (I → ℝ) → S → ℝ := fun y i => y i
  have hr : Measurable restrict := Measurable.of_eval (fun i => measurable_pi_apply (i : I))
  have hi : X ⟂ᵢ[P] (fun ω (i : S) => noise ω i) := by
    simpa only [Function.comp_def, id_eq] using hindep.comp measurable_id hr
  have h := binaryField_gaussian_condExp_all P (ν : Measure (I → Bool)) X
    (fun ω (i : S) => noise ω i) hX (hr.comp hnoise)
    (fun i : S => (i : I)) e t hprior hnoiseLaw hi
  filter_upwards [h] with ω hω
  exact hω.trans (gaussianFiniteTilt_finset_eq ν S e t
    (fun i => (t : ℝ) * binaryValue (X ω i) + noise ω i))

end Problem336.FinitePosterior

end

end OAI
