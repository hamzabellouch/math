import OAI.NumberTheory.DukePrimeDegree.Entropy.IncreasingConditioningChain
import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureLabelBlocks

namespace OAI

/-! # Chain rules with the actual entire future -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma observationSigma_comp {Y Z α : Type*} (P : Y → α) (S : Z → Y) :
    observationSigma (P ∘ S)=MeasurableSpace.comap S (observationSigma P) := by
  unfold observationSigma
  exact MeasurableSpace.comap_comp.symm

theorem conditionalSigmaEntropy_chain_wholeFuture
    {Y α β : Type*} [MeasurableSpace Y] [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Measurable T) (Q : Y → ℕ) (hQ : Measurable Q)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (R : Y → β) (hR : ∀ b, MeasurableSet {y | R y=b}) :
    conditionalSigmaEntropy μ (fun y => (P y,R y))
        (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) =
      conditionalSigmaEntropy μ P
          (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) +
        conditionalSigmaEntropy μ R
          (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance ⊔ observationSigma P) := by
  have H := conditionalSigmaEntropy_chain_iSup_nat μ P hP R hR
    (futureLabelBlock T Q) (futureLabelBlock_measurable hT hQ)
    (futureLabelBlock_sigma_monotone T Q)
  simpa only [futureLabelBlock_sigma_generate,countableFutureSigma_eq_comap] using H

theorem conditionalSigmaEntropy_comp_preserving_wholeFuture
    {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (Q : Y → ℕ) (hQ : Measurable Q)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a}) :
    conditionalSigmaEntropy μ (P ∘ T)
        (MeasurableSpace.comap ((entireFutureObservation T Q) ∘ T) inferInstance) =
      conditionalSigmaEntropy μ P
        (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) := by
  have hmono : Monotone (fun N => observationSigma ((futureLabelBlock T Q N) ∘ T)) := by
    intro i j hij
    simp only [observationSigma_comp]
    exact MeasurableSpace.comap_mono (futureLabelBlock_sigma_monotone T Q hij)
  have H := conditionalSigmaEntropy_comp_preserving_iSup_nat μ hT P hP
    (futureLabelBlock T Q) (futureLabelBlock_measurable hT.measurable hQ)
    (futureLabelBlock_sigma_monotone T Q) hmono
  simpa only [observationSigma_comp,←MeasurableSpace.comap_iSup,
    futureLabelBlock_sigma_generate,countableFutureSigma_eq_comap,
    MeasurableSpace.comap_comp] using H

end DukePrimeDegree

end

end OAI
