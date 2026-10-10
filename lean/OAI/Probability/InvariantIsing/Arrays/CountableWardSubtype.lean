import OAI.Probability.InvariantIsing.Arrays.CountableWardFunctional

namespace OAI

/-! Transport the principal Ward functional from a finite subtype to its
normalized restricted reference measure. -/

noncomputable section

open MeasureTheory IsingPerceptron

namespace InvariantIsing

lemma expectedReplicaWard_subtype {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) (ν : Measure X) [IsProbabilityMeasure ν]
    {S : Set X} (hS : MeasurableSet S) (hpos : ν S ≠ 0)
    (H : Ω × X → ℝ) (D₂ : Ω × (Fin 2 → X) → ℝ) (D₃ : Ω × (Fin 3 → X) → ℝ) :
    expectedReplicaWard P (subtypeReference ν S)
      (fun z : Ω × S => H (z.1,z.2))
      (fun z => D₂ (z.1, fun i => (z.2 i : X)))
      (fun z => D₃ (z.1, fun i => (z.2 i : X))) =
      expectedReplicaWard P (normalizedRestriction ν S) H D₂ D₃ := by
  have he {r : ℕ} (z : Ω) (O : (Fin r → X) → ℝ) :
      referenceReplicaMean (subtypeReference ν S) (fun s => H (z,s))
        (fun σ => O (fun i => (σ i : X))) =
      referenceReplicaMean (normalizedRestriction ν S) (fun s => H (z,s)) O :=
    referenceReplicaMean_subtype hS hpos
      (measurable_of_countable (fun s => H (z,s))) (measurable_of_countable O)
  unfold expectedReplicaWard
  congr 1
  · apply integral_congr_ae
    exact ae_of_all _ fun z => he z (fun σ => D₂ (z,σ))
  · congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun z => he z (fun σ => D₃ (z,σ))

end InvariantIsing

end

end OAI
