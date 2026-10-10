import OAI.Probability.InvariantIsing.Arrays.TensorObservableAverageLaw

namespace OAI

/-! The one-replica and direct-observable conventions agree in the actual
countable spin/leaf Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma referenceReplicaMean_zero_one {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν] (D : X → ℝ) :
    referenceReplicaMean ν (fun _ => 0) (fun σ : Fin 1 → X => D (σ 0)) =
      ∫ x, D x ∂ν := by
  rw [referenceReplicaMean_zero]
  exact (measurePreserving_eval (fun _ : Fin 1 => ν) 0).hasLaw.integral_comp
    (measurable_of_countable D).aestronglyMeasurable

lemma tensorNamespacedObservableAverage_eq_replica_one {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → (Spin N × LabeledLeaf n) → ℝ) :
    tensorNamespacedObservableAverage μ eig c I degree amp n b r h D =
      tensorNamespacedReplicaAverage μ eig c I degree amp n b r h
        (fun U (σ : Fin 1 → Spin N × LabeledLeaf n) => D U (σ 0)) := by
  unfold tensorNamespacedObservableAverage tensorNamespacedReplicaAverage
  apply integral_congr_ae
  exact ae_of_all _ fun p => (referenceReplicaMean_zero_one
    (tensorNamespacedReference eig c I degree amp n r h p) (D p.1.1)).symm

end InvariantIsing

end

end OAI
