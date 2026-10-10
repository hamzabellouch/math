import OAI.Probability.FreeIsing.Conditioning.FiniteBayesCondExp
import OAI.Probability.FreeIsing.Gaussian.FiniteGaussianPosterior

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace Problem367

theorem map_planted_eq_compProd
    {A B X : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace X]
    (μ : Measure A) [SFinite μ] (ν : Measure B) [SFinite ν]
    (κ : Kernel A X) [IsSFiniteKernel κ] (F : A → B → X)
    (hF : Measurable (fun z : A × B => F z.1 z.2))
    (hκ : ∀ a, ν.map (F a) = κ a) :
    (μ.prod ν).map (fun z : A × B => (z.1, F z.1 z.2)) = μ ⊗ₘ κ := by
  ext s hs
  rw [Measure.map_apply (measurable_fst.prodMk hF) hs,
    Measure.prod_apply (hs.preimage (measurable_fst.prodMk hF)), Measure.compProd_apply hs]
  apply lintegral_congr
  intro a
  have hFa : Measurable (F a) := hF.comp measurable_prodMk_left
  have hsa : MeasurableSet (Prod.mk a ⁻¹' s) := hs.preimage measurable_prodMk_left
  rw [← hκ a, Measure.map_apply hFa hsa]
  rfl

theorem gaussianPi_map_signal {I : Type*} [Fintype I]
    (t : ℝ≥0) (s : I → ℝ) :
    (Measure.pi (fun _ : I => gaussianReal 0 t)).map
      (fun x i => (t : ℝ) * s i + x i) =
        Measure.pi (fun i => gaussianReal ((t : ℝ) * s i) t) := by
  rw [Measure.pi_map_pi (μ := fun _ : I => gaussianReal 0 t)
    (f := fun i (x : ℝ) => (t : ℝ) * s i + x) (fun i => by fun_prop)]
  congr 1
  funext i
  simpa using (gaussianReal_map_const_add (μ := 0) (v := t) ((t : ℝ) * s i))

theorem finiteGaussianPlanted_joint_law
    {A I : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype I] (μ : Measure A) [IsProbabilityMeasure μ]
    (t : ℝ≥0) (s : A → I → ℝ) :
    (μ.prod (Measure.pi (fun _ : I => gaussianReal 0 t))).map
      (fun z : A × (I → ℝ) => (z.1, fun i => (t : ℝ) * s z.1 i + z.2 i)) =
        μ ⊗ₘ finiteGaussianObservationKernel t s := by
  apply map_planted_eq_compProd μ (Measure.pi (fun _ : I => gaussianReal 0 t))
    (finiteGaussianObservationKernel t s) (fun a x i => (t : ℝ) * s a i + x i)
  · exact Measurable.of_eval (fun index =>
      (measurable_const.mul
        ((measurable_of_finite (fun state => s state index)).comp measurable_fst)).add
        ((measurable_pi_apply index).comp measurable_snd))
  · intro a
    exact gaussianPi_map_signal t (s a)

theorem finiteGaussianPlanted_condExp
    {A I : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [StandardBorelSpace A] [Nonempty A] [Fintype I]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (t : ℝ≥0) (s : A → I → ℝ) (hs : ∀ a i, s a i ^ 2 = 1) (q : A → ℝ) :
    let ρ := μ.prod (Measure.pi (fun _ : I => gaussianReal 0 t))
    let Y : A × (I → ℝ) → I → ℝ := fun z i => (t : ℝ) * s z.1 i + z.2 i
    ρ[fun z => q z.1 | (inferInstance : MeasurableSpace (I → ℝ)).comap Y] =ᵐ[ρ]
      fun z => (∑ a, μ.real {a} * Real.exp (∑ i, s a i * Y z i) * q a) /
        (∑ a, μ.real {a} * Real.exp (∑ i, s a i * Y z i)) := by
  dsimp only
  refine FiniteBayes.condExp_state_eq_of_posterior_integral
    (μ.prod (Measure.pi (fun _ : I => gaussianReal 0 t))) μ
    (finiteGaussianObservationKernel t s) Prod.fst
    (fun z i => (t : ℝ) * s z.1 i + z.2 i) measurable_fst ?_
    (finiteGaussianPlanted_joint_law μ t s) q
    (fun x => (∑ a, μ.real {a} * Real.exp (∑ i, s a i * x i) * q a) /
      (∑ a, μ.real {a} * Real.exp (∑ i, s a i * x i)))
    (finiteGaussianObservation_posterior_mean μ t s hs q)
  exact Measurable.of_eval (fun index =>
      (measurable_const.mul
        ((measurable_of_finite (fun state => s state index)).comp measurable_fst)).add
        ((measurable_pi_apply index).comp measurable_snd))

end Problem367

end

end OAI
