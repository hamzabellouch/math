import OAI.NumberTheory.PrimePackets.ConditionalSigmaEntropy
import OAI.NumberTheory.PrimePackets.FutureEntropyIncrements
import OAI.NumberTheory.PrimePackets.FiniteGeneratingObservations

namespace OAI

/-! # Metric entropy from genuine future conditional expectations -/

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal

namespace PrimeDegreePackets

variable {Y α : Type*} [MeasurableSpace Y] [Fintype α]

omit [MeasurableSpace Y] [Fintype α] in
lemma futureObservationSigma_monotone (T : Y → Y) (P : Y → α) :
    Monotone (fun n => observationSigma (futureName T P n)) := by
  intro n m hnm s hs
  obtain ⟨t,_,rfl⟩ := hs
  refine ⟨{v : Fin m → α | (fun i : Fin n => v ⟨i.val, lt_of_lt_of_le i.isLt hnm⟩) ∈ t},
    trivial, ?_⟩
  rfl

theorem observationEntropyRate_eq_futureConditional
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    observationEntropyRate μ T P =
      conditionalSigmaEntropy μ P (⨆ n, observationSigma (futureName T P n)) := by
  exact tendsto_nhds_unique (futureConditionalEntropy_tendsto_rate μ hT P hP)
    (conditionalObservationEntropy_tendsto_sigma μ P hP (futureName T P)
      (futureName_measurable_fiber hT.measurable hP) (futureObservationSigma_monotone T P))

omit [Fintype α] in
/-- The metric entropy is computed from actual conditional expectations on
the future sigma algebras of explicit finite generating observations. -/
theorem measureEntropy_eq_iSup_futureConditional
    [MeasurableSpace.CountablyGenerated Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) :
    measureEntropy μ T = ⨆ k, ENNReal.ofReal
      (conditionalSigmaEntropy μ (finiteGeneratingObservation Y k)
        (⨆ n, observationSigma (futureName T (finiteGeneratingObservation Y k) n))) := by
  rw [measureEntropy_eq_iSup_finiteGenerating Y μ hT]
  congr 1
  funext k
  rw [observationEntropyRate_eq_futureConditional μ hT _
    (fun b => (finiteGeneratingObservation_measurable Y k) (measurableSet_singleton b))]

end PrimeDegreePackets

end

end OAI
