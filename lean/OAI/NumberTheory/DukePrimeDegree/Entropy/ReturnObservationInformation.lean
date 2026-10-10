import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableShannonInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.RefinedReturnPartition

namespace OAI

/-! # Integrable information of the actual return partitions -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

theorem firstReturnPartitionCode_information_integrable
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hE : MeasurableEmbedding T)
    {S : Set Y} (hS : MeasurableSet S) :
    Integrable (observationInformation μ (firstReturnPartitionCode T S)) μ :=
  countable_observationInformation_integrable μ _
    (fun a => measurable_firstReturnPartitionCode hT.measurable hS
      (measurableSet_singleton a))
    (firstReturnPartitionCode_information_summable μ hT hE hS)

theorem returnRefinement_information_integrable_integral
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hE : MeasurableEmbedding T)
    {S : Set Y} (hS : MeasurableSet S)
    (K : ℕ → ℕ) (B : ∀ n, Y → Fin (K n)) (hB : ∀ n, Measurable (B n))
    (C : ℝ) (hcard : ∀ n, Real.log (K n) ≤ C*(n+1)) :
    Integrable (observationInformation μ (returnRefinement T S B)) μ ∧
      (∫ x, observationInformation μ (returnRefinement T S B) x ∂μ) =
        ∑' z, Real.negMulLog (μ.real {x | returnRefinement T S B x=z}) := by
  let : MeasurableSpace (Option (Σ n : ℕ, Fin (K n))) := ⊤
  have hm := measurable_returnRefinement hT.measurable hS B hB
  have hs := returnRefinement_information_summable μ hT hE hS K B hB C hcard
  exact ⟨countable_observationInformation_integrable μ _
      (fun a => hm (measurableSet_singleton a)) hs,
    integral_countable_observationInformation μ _
      (fun a => hm (measurableSet_singleton a)) hs⟩

end DukePrimeDegree

end

end OAI
