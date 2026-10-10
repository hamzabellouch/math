import OAI.Probability.FreeIsing.Conditioning.FiniteBayesCondExp
import OAI.Probability.FreeIsing.Gaussian.Likelihood

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace Problem367

def finiteGaussianObservationKernel
    {A I : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype I] (t : ℝ≥0) (s : A → I → ℝ) : Kernel A (I → ℝ) where
  toFun a := Measure.pi (fun i => gaussianReal ((t : ℝ) * s a i) t)
  measurable' := measurable_of_finite _

instance finiteGaussianObservationKernel_isMarkov
    {A I : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype I] (t : ℝ≥0) (s : A → I → ℝ) :
    IsMarkovKernel (finiteGaussianObservationKernel t s) where
  isProbabilityMeasure a := by
    change IsProbabilityMeasure (Measure.pi (fun i => gaussianReal ((t : ℝ) * s a i) t))
    infer_instance

theorem finiteGaussianObservation_posterior_mean
    {A I : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [StandardBorelSpace A] [Nonempty A] [Fintype I]
    (mu : Measure A) [IsProbabilityMeasure mu]
    (t : ℝ≥0) (s : A → I → ℝ) (hs : ∀ a i, s a i ^ 2 = 1)
    (q : A → ℝ) :
    ∀ᵐ x ∂finiteGaussianObservationKernel t s ∘ₘ mu,
      (∫ a, q a ∂(posterior (finiteGaussianObservationKernel t s) mu) x) =
        (∑ a, mu.real {a} * Real.exp (∑ i, s a i * x i) * q a) /
          (∑ a, mu.real {a} * Real.exp (∑ i, s a i * x i)) := by
  have hlikelihood (a : A) :
      finiteGaussianObservationKernel t s a =
        (Measure.pi (fun _ : I => gaussianReal 0 t)).withDensity
          (fun x => ENNReal.ofReal
            (Real.exp (-((t : ℝ) * Fintype.card I / 2)) *
              Real.exp (∑ i, s a i * x i))) := by
    change Measure.pi (fun i => gaussianReal ((t : ℝ) * s a i) t) = _
    rw [gaussianPi_spin_withDensity t (s a) (hs a)]
    congr 1
    funext x
    rw [sub_eq_add_neg, Real.exp_add, mul_comm]
  exact FiniteBayes.posterior_integral_exp mu (finiteGaussianObservationKernel t s)
    (Measure.pi (fun _ : I => gaussianReal 0 t))
    (fun a x => ∑ i, s a i * x i)
    (fun a => Finset.measurable_sum _
      (fun i _ => measurable_const.mul (measurable_pi_apply i)))
    (fun _ => Real.exp (-((t : ℝ) * Fintype.card I / 2))) measurable_const
    (fun _ => Real.exp_pos _) hlikelihood q

theorem finiteGaussianObservation_condExp
    {A I : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [StandardBorelSpace A] [Nonempty A] [Fintype I]
    (mu : Measure A) [IsProbabilityMeasure mu]
    (t : ℝ≥0) (s : A → I → ℝ) (hs : ∀ a i, s a i ^ 2 = 1)
    (q : A → ℝ) :
    (mu ⊗ₘ finiteGaussianObservationKernel t s)[fun z : A × (I → ℝ) => q z.1 |
        (inferInstance : MeasurableSpace (I → ℝ)).comap Prod.snd]
      =ᵐ[mu ⊗ₘ finiteGaussianObservationKernel t s] fun z =>
        (∑ a, mu.real {a} * Real.exp (∑ i, s a i * z.2 i) * q a) /
          (∑ a, mu.real {a} * Real.exp (∑ i, s a i * z.2 i)) := by
  apply (FiniteBayes.condExp_state_eq_posterior_integral mu
    (finiteGaussianObservationKernel t s) q).trans
  have hp := finiteGaussianObservation_posterior_mean mu t s hs q
  rw [← Measure.snd_compProd mu (finiteGaussianObservationKernel t s)] at hp
  exact ae_of_ae_map measurable_snd.aemeasurable hp

end Problem367

end

end OAI
