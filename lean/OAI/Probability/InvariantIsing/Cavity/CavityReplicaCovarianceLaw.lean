import OAI.Probability.InvariantIsing.Cavity.CavityReplicaCutoff
import OAI.Probability.IsingPerceptron.EnrichedCGF

namespace OAI

/-! Equality in law of the entire countable Gaussian field transports
replica observables of every order, including their cutoff normalization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_field_functional_same_covariance {X : Type*}
    (A C : X → ℕ →₀ ℝ)
    (hcov : ∀ x y, cylinderCross (A x) (A y) = cylinderCross (C x) (C y))
    (G : (X → ℝ) → ℝ) (hG : Measurable G) :
    (∫ z, G (fun x => cylinderField (A x) z) ∂gaussianCoordinates) =
      ∫ z, G (fun x => cylinderField (C x) z) ∂gaussianCoordinates := by
  have hA : Measurable (fun z x => cylinderField (A x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField (A x))
  have hC : Measurable (fun z x => cylinderField (C x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField (C x))
  rw [← integral_map hA.aemeasurable hG.aestronglyMeasurable,
    cylinder_fields_law_eq A C hcov, integral_map hC.aemeasurable hG.aestronglyMeasurable]

theorem cavity_replica_same_covariance {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] {r : ℕ}
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (A C : X → ℕ →₀ ℝ)
    (hcov : ∀ x y, cylinderCross (A x) (A y) = cylinderCross (C x) (C y))
    (F : (Fin r → X) → ℝ) :
    (∫ z, referenceReplicaMean ν (fun x => H x + cylinderField (A x) z) F ∂gaussianCoordinates) =
      ∫ z, referenceReplicaMean ν (fun x => H x + cylinderField (C x) z) F ∂gaussianCoordinates := by
  have hm : Measurable (fun p : (X → ℝ) × X => H p.2 + p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    exact (measurable_pi_apply x : Measurable (fun w : X → ℝ => w x)).const_add (H x)
  exact cavity_field_functional_same_covariance A C hcov
    (fun w => referenceReplicaMean ν (fun x => H x + w x) F)
    (measurable_referenceReplicaMean ν hm ((measurable_of_countable F).comp measurable_snd))

theorem cavity_cutoff_same_covariance {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (A C : X → ℕ →₀ ℝ)
    (hcov : ∀ x y, cylinderCross (A x) (A y) = cylinderCross (C x) (C y))
    (s : Set X) (F : (Fin 2 → X) → ℝ) :
    (∫ z, cavityCutoffReplicaMean ν (fun x => H x + cylinderField (A x) z) s F ∂gaussianCoordinates) =
      ∫ z, cavityCutoffReplicaMean ν (fun x => H x + cylinderField (C x) z) s F ∂gaussianCoordinates := by
  have hm : Measurable (fun p : (X → ℝ) × X => H p.2 + p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    exact (measurable_pi_apply x : Measurable (fun w : X → ℝ => w x)).const_add (H x)
  exact cavity_field_functional_same_covariance A C hcov
    (fun w => cavityCutoffReplicaMean ν (fun x => H x + w x) s F)
    (measurable_cavityCutoffReplicaMean ν _ hm (fun _ => s)
      (((Set.to_countable s).measurableSet).preimage measurable_snd)
      (fun p => F p.2) ((measurable_of_countable F).comp measurable_snd))

end InvariantIsing

end

end OAI
