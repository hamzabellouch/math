import OAI.Probability.FreeIsing.Brownian.PathLikelihood
import OAI.Probability.FreeIsing.Conditioning.FiniteBayesCondExp

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace Problem367

def finiteBrownianObservationKernel
    {A V Omega : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Fintype V] [MeasurableSpace Omega]
    (nu : Measure Omega) (B : ℝ≥0 → Omega → ℝ)
    (_hB : IsPreBrownianReal B nu) (_hmB : ∀ t, Measurable (B t))
    (T : ℝ≥0) (s : A → V → ℝ) : Kernel A (V → Set.Iic T → ℝ) where
  toFun a := Measure.pi (fun v =>
    Measure.map (fun w (t : Set.Iic T) => (t.val : ℝ) * s a v + B t w) nu)
  measurable' := measurable_of_finite _

instance finiteBrownianObservationKernel_markov
    {A V Omega : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Fintype V] [MeasurableSpace Omega]
    (nu : Measure Omega) (B : ℝ≥0 → Omega → ℝ)
    (hB : IsPreBrownianReal B nu) (hmB : ∀ t, Measurable (B t)) (T : ℝ≥0) (s : A → V → ℝ) :
    IsMarkovKernel (finiteBrownianObservationKernel nu B hB hmB T s) := by
  let : IsProbabilityMeasure nu := hB.isGaussianProcess.isProbabilityMeasure
  constructor
  intro a
  change IsProbabilityMeasure (Measure.pi (fun v =>
    Measure.map (fun w (t : Set.Iic T) => (t.val : ℝ) * s a v + B t w) nu))
  infer_instance

theorem finiteBrownianObservation_posterior_mean
    {A V Omega : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [StandardBorelSpace A] [Nonempty A]
    [Fintype V] [MeasurableSpace Omega]
    (pi : Measure A) [IsProbabilityMeasure pi]
    (nu : Measure Omega) (B : ℝ≥0 → Omega → ℝ)
    (hB : IsPreBrownianReal B nu) (hmB : ∀ t, Measurable (B t))
    (T : ℝ≥0) (hT : T ≠ 0) (s : A → V → ℝ)
    (hs : ∀ a v, s a v ^ 2 = 1) (q : A → ℝ) :
    ∀ᵐ y ∂finiteBrownianObservationKernel nu B hB hmB T s ∘ₘ pi,
      (∫ a, q a ∂posterior (finiteBrownianObservationKernel nu B hB hmB T s) pi y) =
        (∑ a, pi.real {a} * Real.exp (∑ v, s a v * y v ⟨T, by simp⟩) * q a) /
          (∑ a, pi.real {a} * Real.exp (∑ v, s a v * y v ⟨T, by simp⟩)) := by
  let : IsProbabilityMeasure nu := hB.isGaussianProcess.isProbabilityMeasure
  apply FiniteBayes.posterior_integral_exp pi
    (finiteBrownianObservationKernel nu B hB hmB T s)
    (Measure.pi (fun _ : V => Measure.map (fun w (t : Set.Iic T) => B t w) nu))
    (fun a y => ∑ v, s a v * y v ⟨T, by simp⟩)
    (fun a => by fun_prop)
    (fun _ => Real.exp (-((T : ℝ) * Fintype.card V / 2)))
    measurable_const (fun _ => Real.exp_pos _) ?_ q
  intro a
  change Measure.pi (fun v =>
    Measure.map (fun w (t : Set.Iic T) => (t.val : ℝ) * s a v + B t w) nu) = _
  rw [preBrownian_past_spin_drift_withDensity hB hmB hT (s a) (hs a)]
  congr 1
  funext y
  rw [sub_eq_add_neg, Real.exp_add, mul_comm]

theorem finiteBrownianObservation_condExp
    {A V Omega : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [StandardBorelSpace A] [Nonempty A]
    [Fintype V] [MeasurableSpace Omega]
    (pi : Measure A) [IsProbabilityMeasure pi]
    (nu : Measure Omega) (B : ℝ≥0 → Omega → ℝ)
    (hB : IsPreBrownianReal B nu) (hmB : ∀ t, Measurable (B t))
    (T : ℝ≥0) (hT : T ≠ 0) (s : A → V → ℝ)
    (hs : ∀ a v, s a v ^ 2 = 1) (q : A → ℝ) :
    (pi ⊗ₘ finiteBrownianObservationKernel nu B hB hmB T s)[fun z : A × (V → Set.Iic T → ℝ) => q z.1 |
        (inferInstance : MeasurableSpace (V → Set.Iic T → ℝ)).comap Prod.snd]
      =ᵐ[pi ⊗ₘ finiteBrownianObservationKernel nu B hB hmB T s] fun z =>
        (∑ a, pi.real {a} * Real.exp (∑ v, s a v * z.2 v ⟨T, by simp⟩) * q a) /
          (∑ a, pi.real {a} * Real.exp (∑ v, s a v * z.2 v ⟨T, by simp⟩)) := by
  apply (FiniteBayes.condExp_state_eq_posterior_integral pi
    (finiteBrownianObservationKernel nu B hB hmB T s) q).trans
  have hp := finiteBrownianObservation_posterior_mean pi nu B hB hmB T hT s hs q
  rw [← Measure.snd_compProd pi (finiteBrownianObservationKernel nu B hB hmB T s)] at hp
  exact ae_of_ae_map measurable_snd.aemeasurable hp

end Problem367

end

end OAI
