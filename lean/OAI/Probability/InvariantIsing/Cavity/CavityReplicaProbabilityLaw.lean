import OAI.Probability.InvariantIsing.Cavity.CavityProbabilityCovariance

namespace OAI

/-! Equality in law of random Gibbs probabilities transports the full
infinite replica sample, without integrability assumptions on tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal

namespace InvariantIsing

lemma cavity_probability_subtype_law {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω)
    (ν η : Ω → Measure X) (hν : Measurable ν) (hη : Measurable η)
    [∀ ω, IsProbabilityMeasure (ν ω)] [∀ ω, IsProbabilityMeasure (η ω)]
    (he : P.map ν = P.map η) :
    P.map (fun ω => (⟨ν ω, inferInstance⟩ : ProbabilityMeasure X)) =
      P.map (fun ω => (⟨η ω, inferInstance⟩ : ProbabilityMeasure X)) := by
  apply (MeasurableEmbedding.subtype_coe ProbabilityMeasure.measurableSet_isProbabilityMeasure).map_injective
  rw [Measure.map_map measurable_subtype_coe hν.subtype_mk,
    Measure.map_map measurable_subtype_coe hη.subtype_mk]
  exact he

theorem cavity_replica_lintegral_same_probability_law {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) (ν η : Ω → Measure X) (hν : Measurable ν) (hη : Measurable η)
    [∀ ω, IsProbabilityMeasure (ν ω)] [∀ ω, IsProbabilityMeasure (η ω)]
    (he : P.map ν = P.map η)
    (F : (ℕ → X) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, ∫⁻ σ, F σ ∂Measure.infinitePi (fun _ : ℕ => ν ω) ∂P) =
      ∫⁻ ω, ∫⁻ σ, F σ ∂Measure.infinitePi (fun _ : ℕ => η ω) ∂P := by
  let G : ProbabilityMeasure X → ℝ≥0∞ := fun μ =>
    ∫⁻ σ, F σ ∂Measure.infinitePi (fun _ : ℕ => (μ : Measure X))
  have hG : Measurable G :=
    hF.lintegral_kernel (κ := replicaKernel
      (fun μ : ProbabilityMeasure X => (μ : Measure X)) measurable_subtype_coe)
  have hh := congrArg (fun Q : Measure (ProbabilityMeasure X) => ∫⁻ μ, G μ ∂Q)
    (cavity_probability_subtype_law P ν η hν hη he)
  have hν' : Measurable (fun ω => (⟨ν ω, inferInstance⟩ : ProbabilityMeasure X)) := hν.subtype_mk
  have hη' : Measurable (fun ω => (⟨η ω, inferInstance⟩ : ProbabilityMeasure X)) := hη.subtype_mk
  exact (lintegral_map (μ := P) hG hν').symm.trans
    (hh.trans (lintegral_map (μ := P) hG hη'))

end InvariantIsing

end

end OAI
