import OAI.Probability.FreeIsing.Estimates.ObservableDisintegration
import OAI.Probability.FreeIsing.Posterior.ProjectedObservationRecovery

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

private theorem measurable_time_state
    {T W X Y : Type*} [MeasurableSpace T] [MeasurableSpace W]
    [MeasurableSpace X] [MeasurableSpace Y] {F : T × X → Y}
    (hF : Measurable F) :
    Measurable (fun q : T × (W × X) => F (q.1, q.2.2)) :=
  hF.comp (by fun_prop)

theorem isFactorOfIID_of_stationary_innovation_observable
    {d : ℕ} {theta : ℝ} {A X : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (P : Measure X) [IsProbabilityMeasure P]
    (Z : X → TreeVertex d → A) (hZ : Measurable Z)
    (hinput : P.map Z = Measure.infinitePi (fun _ : TreeVertex d => nu))
    (E : X → TreeVertex d → ℕ → ℝ) (hE : Measurable E)
    (S : TreeAut d → X → X) (hS : ∀ g, MeasurePreserving (S g) P P)
    (hEeq : ∀ g x, E (S g x) = relabel g (E x))
    (hZeq : ∀ g, ∀ᵐ x ∂P, Z (S g x) = relabel g (Z x))
    (o : TreeVertex d)
    (hLaw : HasFreeIsingLaw theta (P.map (fun x => SpinRecovery.decodeArray (E x))))
    (H : ℝ≥0 → X → ℝ) (W : ℕ → (TreeVertex d → A) → ℝ)
    (hm : Measurable (Function.uncurry (fun (t : ℝ) x => Real.tanh (H t.toNNReal x))))
    (hInt : ∀ t, Integrable (fun p => (H t p.2.1 - H t p.2.2) ^ 2)
      ((P.map Z) ⊗ₘ ((ObservableDisintegration.kernel P Z) ×ₖ
        (ObservableDisintegration.kernel P Z))))
    (hzero : ∀ t, (∫ p, (H t p.2.1 - H t p.2.2) ^ 2
      ∂(P.map Z) ⊗ₘ ((ObservableDisintegration.kernel P Z) ×ₖ
        (ObservableDisintegration.kernel P Z))) = 0)
    (hInnovation : ∀ n, ∀ᵐ x ∂P,
      E x o n = W n (Z x) + nnrealTimePrimitive (fun t x => Real.tanh (H t x)) n x) :
    IsFactorOfIID d theta := by
  let kappa := ObservableDisintegration.kernel P Z
  have hproj : MeasurePreserving Prod.snd
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa) P := by
    simpa only [hinput] using ObservableDisintegration.measurePreserving_snd_kernel P hZ
  refine isFactorOfIID_of_innovation_comparison nu kappa E hE S
    (fun g => (hS g).measurable) hEeq o ?_ ?_
    (fun t p => H t p.2) W ?_ ?_ ?_ ?_
  · have hdecode : Measurable (fun x => SpinRecovery.decodeArray (E x)) :=
      SpinRecovery.measurable_decodeArray.comp hE
    change HasFreeIsingLaw theta
      (Measure.map ((fun x => SpinRecovery.decodeArray (E x)) ∘ Prod.snd)
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa))
    rw [← Measure.map_map hdecode measurable_snd, hproj.map_eq]
    exact hLaw
  · intro g
    simpa only [hinput] using ObservableDisintegration.joint_kernel_invariant P hZ
      (measurable_relabel g) (hS g) (hZeq g)
  · exact measurable_time_state hm
  · simpa only [hinput] using hInt
  · simpa only [hinput] using hzero
  · intro n
    have hsupp : ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa,
        Z p.2 = p.1 := by
      simpa only [hinput] using ObservableDisintegration.ae_observable_eq_input P hZ
    filter_upwards [hproj.quasiMeasurePreserving.ae (hInnovation n), hsupp] with p hp hs
    rw [hs] at hp
    exact hp

end Problem367

end

end OAI
