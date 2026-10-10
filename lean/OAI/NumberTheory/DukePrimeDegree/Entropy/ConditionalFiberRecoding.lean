import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalMapEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.BilateralConditionalSupport
import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorSymbols

namespace OAI

/-! # Finite recoding within the fibers of a countable observation -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma observationEntropy_eq_of_ae_eq {Y α : Type*} [MeasurableSpace Y]
    [Fintype α] (ν : Measure Y) (P R : Y → α) (h : P =ᵐ[ν] R) :
    observationEntropy ν P=observationEntropy ν R := by
  unfold observationEntropy
  congr 1
  funext a
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [h] with y hy
  simp only [hy]

theorem conditionalSigmaEntropy_le_fiber_recoding
    {Y S α β : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace S] [MeasurableEq S]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F)
    (P : Y → α) (hP : Measurable P) (B : Y → β) (hB : Measurable B)
    (f : S → β → α) (hf : ∀ x, P x=f (F x) (B x)) :
    conditionalSigmaEntropy μ P (MeasurableSpace.comap F inferInstance) ≤
      conditionalSigmaEntropy μ B (MeasurableSpace.comap F inferInstance) := by
  rw [conditionalSigmaEntropy_comap_eq_integral μ F hF P
      (fun a => hP (measurableSet_singleton a)),
    conditionalSigmaEntropy_comap_eq_integral μ F hF B
      (fun a => hB (measurableSet_singleton a))]
  apply integral_mono_ae
    (integrable_kernel_entropy (μ.map F) (condDistrib id F μ) P
      (fun a => hP (measurableSet_singleton a)))
    (integrable_kernel_entropy (μ.map F) (condDistrib id F μ) B
      (fun a => hB (measurableSet_singleton a)))
  filter_upwards [ae_condDistrib_self_fiber μ F hF] with s hs
  have he : P =ᵐ[condDistrib id F μ s] (f s ∘ B) := by
    filter_upwards [hs] with y hy
    simpa only [Function.comp_apply,hy] using hf y
  rw [observationEntropy_eq_of_ae_eq _ P (f s ∘ B) he]
  apply observationEntropy_le_of_refines _ _ B
    (fun a => ((measurable_of_finite (f s)).comp hB) (measurableSet_singleton a))
    (fun a => hB (measurableSet_singleton a))
  intro x y hxy
  exact congrArg (f s) hxy

theorem predecessor_clip_conditionalEntropy_le
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (T : Y → Y) (hT : Measurable T) (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin M) (hB : Measurable B)
    (decode : ℕ → Fin M → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (L : ℕ) :
    conditionalSigmaEntropy μ (heightClip Q L)
        (MeasurableSpace.comap (Q ∘ T) inferInstance) ≤
      conditionalSigmaEntropy μ B (MeasurableSpace.comap (Q ∘ T) inferInstance) := by
  apply conditionalSigmaEntropy_le_fiber_recoding μ (Q ∘ T) (hQ.comp hT)
    (heightClip Q L) (heightClip_measurable hQ L) B hB
    (fun q b => heightClip id L (decode q b))
  intro x
  change heightClip id L (Q x)=heightClip id L (decode (Q (T x)) (B x))
  rw [hdecode]

end DukePrimeDegree

end

end OAI
