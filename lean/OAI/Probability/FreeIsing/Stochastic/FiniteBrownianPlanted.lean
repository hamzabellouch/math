import OAI.Probability.FreeIsing.Gaussian.FiniteGaussianPlanted
import OAI.Probability.FreeIsing.Stochastic.FiniteBrownianPosterior

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace Problem367

theorem finiteBrownianPlanted_joint_law
    {A V Omega : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Fintype V] [MeasurableSpace Omega]
    (pi : Measure A) [IsProbabilityMeasure pi]
    (nu : Measure Omega) (B : ℝ≥0 → Omega → ℝ)
    (hB : IsPreBrownianReal B nu) (hmB : ∀ t, Measurable (B t))
    (T : ℝ≥0) (s : A → V → ℝ) :
    (pi.prod (Measure.pi (fun _ : V => nu))).map
      (fun z : A × (V → Omega) =>
        (z.1, fun v (t : Set.Iic T) => (t.val : ℝ) * s z.1 v + B t (z.2 v))) =
      pi ⊗ₘ finiteBrownianObservationKernel nu B hB hmB T s := by
  let : IsProbabilityMeasure nu := hB.isGaussianProcess.isProbabilityMeasure
  apply map_planted_eq_compProd pi (Measure.pi (fun _ : V => nu))
    (finiteBrownianObservationKernel nu B hB hmB T s)
    (fun a w v (t : Set.Iic T) => (t.val : ℝ) * s a v + B t (w v))
  · exact Measurable.of_eval (fun v => Measurable.of_eval (fun t =>
      (measurable_const.mul ((measurable_of_finite (fun a => s a v)).comp measurable_fst)).add
        ((hmB t).comp ((measurable_pi_apply v).comp measurable_snd))))
  · intro a
    change (Measure.pi (fun _ : V => nu)).map
      (fun w v (t : Set.Iic T) => (t.val : ℝ) * s a v + B t (w v)) = _
    rw [Measure.pi_map_pi (μ := fun _ : V => nu)
      (f := fun v w (t : Set.Iic T) => (t.val : ℝ) * s a v + B t w)
      (fun v => (Measurable.of_eval (fun (t : Set.Iic T) =>
        measurable_const.add (hmB t))).aemeasurable)]
    rfl

theorem finiteBrownianPlanted_condExp
    {A V Omega : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [StandardBorelSpace A] [Nonempty A]
    [Fintype V] [MeasurableSpace Omega]
    (pi : Measure A) [IsProbabilityMeasure pi]
    (nu : Measure Omega) [IsProbabilityMeasure nu] (B : ℝ≥0 → Omega → ℝ)
    (hB : IsPreBrownianReal B nu) (hmB : ∀ t, Measurable (B t))
    (T : ℝ≥0) (hT : T ≠ 0) (s : A → V → ℝ)
    (hs : ∀ a v, s a v ^ 2 = 1) (q : A → ℝ) :
    let rho := pi.prod (Measure.pi (fun _ : V => nu))
    let Y : A × (V → Omega) → V → Set.Iic T → ℝ :=
      fun z v t => (t.val : ℝ) * s z.1 v + B t (z.2 v)
    rho[fun z => q z.1 | (inferInstance : MeasurableSpace (V → Set.Iic T → ℝ)).comap Y]
      =ᵐ[rho] fun z =>
        (∑ a, pi.real {a} * Real.exp (∑ v, s a v * Y z v ⟨T, by simp⟩) * q a) /
          (∑ a, pi.real {a} * Real.exp (∑ v, s a v * Y z v ⟨T, by simp⟩)) := by
  dsimp only
  refine FiniteBayes.condExp_state_eq_of_posterior_integral
    (pi.prod (Measure.pi (fun _ : V => nu))) pi
    (finiteBrownianObservationKernel nu B hB hmB T s) Prod.fst
    (fun z v (t : Set.Iic T) => (t.val : ℝ) * s z.1 v + B t (z.2 v))
    measurable_fst ?_ (finiteBrownianPlanted_joint_law pi nu B hB hmB T s) q
    (fun y =>
      (∑ a, pi.real {a} * Real.exp (∑ v, s a v * y v ⟨T, by simp⟩) * q a) /
        (∑ a, pi.real {a} * Real.exp (∑ v, s a v * y v ⟨T, by simp⟩)))
    (finiteBrownianObservation_posterior_mean pi nu B hB hmB T hT s hs q)
  exact Measurable.of_eval (fun v => Measurable.of_eval (fun t =>
    (measurable_const.mul ((measurable_of_finite (fun a => s a v)).comp measurable_fst)).add
      ((hmB t).comp ((measurable_pi_apply v).comp measurable_snd))))

end Problem367

end

end OAI
