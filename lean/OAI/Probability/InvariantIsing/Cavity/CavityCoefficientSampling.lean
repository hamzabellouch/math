import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientProbability
import OAI.Probability.InvariantIsing.Spectral.SpectralReplicaLaw

namespace OAI

/-! Sampling Gibbs replicas retains the distribution of the disorder.
Consequently the coefficient concentration estimate is unchanged when
replica coordinates are added. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_disorder_replica_fst {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] :
    MeasurePreserving Prod.fst (disorderReplicaLaw P ν hν) P := by
  refine ⟨measurable_fst, ?_⟩
  exact Measure.fst_compProd P (replicaKernel ν hν)

lemma cavity_factor_deviation_pullback {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {d n : ℕ} (P : Measure Ω) (Q : Measure Ξ) (f : Ω → Ξ)
    (hf : MeasurePreserving f P Q) (A : Ξ → CavityFactorBlocks d n)
    (hA : Measurable A) (A₀ : CavityFactorBlocks d n) (δ : ℝ) :
    P.real {ω | δ < cavityFactorDeviation (A (f ω)) A₀} =
      Q.real {x | δ < cavityFactorDeviation (A x) A₀} := by
  let : OpensMeasurableSpace (CavityFactorBlocks d n) := inferInstanceAs
    (OpensMeasurableSpace ((Fin d → Fin d → ℝ) ×
      ((Fin d → Fin n → ℝ) × (Fin n → Fin n → ℝ))))
  have hs : MeasurableSet {x | δ < cavityFactorDeviation (A x) A₀} :=
    measurableSet_lt measurable_const ((continuous_cavityFactorDeviation A₀).measurable.comp hA)
  have h := congrArg (fun μ : Measure Ξ => μ {x | δ < cavityFactorDeviation (A x) A₀}) hf.map_eq
  rw [Measure.map_apply hf.measurable hs] at h
  exact congrArg ENNReal.toReal h

theorem cavity_factor_probability_after_sampling {Ω X : ℕ → Type*}
    [∀ k, MeasurableSpace (Ω k)] [∀ k, MeasurableSpace (X k)]
    [∀ k, Countable (X k)] [∀ k, MeasurableSingletonClass (X k)]
    {d n : ℕ} (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (ν : (k : ℕ) → Ω k → Measure (X k)) (hν : ∀ k, Measurable (ν k))
    [∀ k ω, IsProbabilityMeasure (ν k ω)]
    (A : (k : ℕ) → Ω k → CavityFactorBlocks d n) (hA : ∀ k, Measurable (A k))
    (A₀ : CavityFactorBlocks d n)
    (hprob : ∀ δ > 0, Tendsto (fun k => (P k).real
      {ω | δ < cavityFactorDeviation (A k ω) A₀}) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k => (disorderReplicaLaw (P k) (ν k) (hν k)).real
      {x | δ < cavityFactorDeviation (A k x.1) A₀}) atTop (𝓝 0) := by
  apply (hprob δ hδ).congr'
  filter_upwards [] with k
  exact (cavity_factor_deviation_pullback _ _ Prod.fst
    (cavity_disorder_replica_fst (P k) (ν k) (hν k)) (A k) (hA k) A₀ δ).symm

end InvariantIsing

end

end OAI
