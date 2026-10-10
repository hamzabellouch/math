import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableFutureInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableObservationInformation

namespace OAI

/-! # Information of the countable present given its future

A binary recoding gives each individual conditional probability. Since
there are only countably many present labels, all of them hold together
outside one null set.
-/

noncomputable section
open MeasureTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets

variable {S V Y : Type*} [MeasurableSpace S] [MeasurableSpace V]
  [StandardBorelSpace V] [Nonempty V] [MeasurableSpace Y]

theorem conditionalProbability_countablePresentFutureFiber
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {Q : Y → ℕ} (hQ : Measurable Q) {T : Y → Y} (hT : Measurable T)
    {F : S × V → Y} (hF : Measurable F)
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (countableFutureFiber T Q F z) ≠ 0) (a : ℕ) :
    ρ[({z | Q (F z)=a}.indicator (fun _ => (1:ℝ))) |
      ⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))] =ᵐ[ρ]
      fun z => (ρ.condKernel z.1).real ({t | Q (F (z.1,t))=a} ∩ countableFutureFiber T Q F z) /
        (ρ.condKernel z.1).real (countableFutureFiber T Q F z) := by
  let P : Y → Fin 2 := fun y => if Q y = a then 0 else 1
  have hP : Measurable P := measurable_const.piecewise
    (hQ (measurableSet_singleton a)) measurable_const
  have H := conditionalProbability_countableFutureFiber ρ hP hQ hT hF hpos (0 : Fin 2)
  have he (y : Y) : P y = 0 ↔ Q y = a := by simp [P]
  simpa only [he] using H

theorem conditionalInformation_countablePresentFutureFiber
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {Q : Y → ℕ} (hQ : Measurable Q) {T : Y → Y} (hT : Measurable T)
    {F : S × V → Y} (hF : Measurable F)
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (countableFutureFiber T Q F z) ≠ 0) :
    conditionalInformation ρ (Q ∘ F)
      (⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))) =ᵐ[ρ]
      fun z => -Real.log
        ((ρ.condKernel z.1).real ({t | Q (F (z.1,t))=Q (F z)} ∩ countableFutureFiber T Q F z) /
          (ρ.condKernel z.1).real (countableFutureFiber T Q F z)) := by
  filter_upwards [ae_all_iff.mpr (fun a =>
    conditionalProbability_countablePresentFutureFiber ρ hQ hT hF hpos a)] with z hz
  exact congrArg (-Real.log ·) (hz (Q (F z)))

end DukePrimeDegree

end

end OAI
