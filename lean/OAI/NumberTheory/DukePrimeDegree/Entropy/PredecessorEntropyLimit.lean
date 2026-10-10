import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorEntropySum

namespace OAI

/-! # The entropy upper bound from finite predecessor symbols

The countable terminal label has sublinear information cost. A finite
conditional chain rule and Cesaro convergence control every clipped rate.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem predecessor_word_conditional_rate
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x) :
    Tendsto (fun N : ℕ => conditionalSigmaEntropy μ (orbitName T B N)
      (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance) / N) atTop
      (𝓝 (conditionalSigmaEntropy μ B
        (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance))) := by
  have hL := conditionalSigmaEntropy_tendsto_iSup μ B
    (fun N => observationSigma (futureLabelBlock T Q N))
    (futureLabelBlock_sigma_monotone T Q)
    (fun N => (futureLabelBlock_measurable hT.measurable hQ N).comap_le)
  rw [futureLabelBlock_sigma_generate,countableFutureSigma_eq_comap] at hL
  have hs := hL.comp (tendsto_add_atTop_nat 1)
  have hc := hs.cesaro
  apply hc.congr
  intro N
  rw [predecessor_word_conditional_sum μ hT Q hQ B hB href decode hdecode]
  simp only [Function.comp_def,div_eq_mul_inv]
  rw [mul_comm]
  rfl

theorem predecessor_clipped_entropyRate_le
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (L : ℕ) :
    observationEntropyRate μ T (heightClip Q L) ≤
      conditionalSigmaEntropy μ B
        (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) := by
  apply le_of_tendsto_of_tendsto
    (conditional_boundary_entropy_rate μ hT (heightClip Q L)
      (fun a => heightClip_measurable hQ L (measurableSet_singleton a)) Q hQ)
    (predecessor_word_conditional_rate μ hT Q hQ B hB href decode hdecode)
  apply Filter.Eventually.of_forall
  intro N
  exact div_le_div_of_nonneg_right
    (predecessor_clippedWord_conditionalEntropy_le μ T hT.measurable Q hQ B hB decode hdecode N L)
    (Nat.cast_nonneg N)

theorem finite_predecessors_entropy_upper
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q) (hfinite : UniformFinitePredecessors T Q) :
    ∃ (M : ℕ) (B : Y → Fin (M+1)) (decode : ℕ → Fin (M+1) → ℕ),
      Measurable B ∧
      (∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y) ∧
      (∀ x, decode (Q (T x)) (B x)=Q x) ∧
      ∀ L : ℕ, observationEntropyRate μ T (heightClip Q L) ≤
        conditionalSigmaEntropy μ B
          (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) := by
  obtain ⟨M,B,decode,hB,href,hdecode⟩ :=
    exists_finite_predecessor_observation T hT.measurable Q hQ hfinite
  exact ⟨M,B,decode,hB,href,hdecode,
    predecessor_clipped_entropyRate_le μ hT Q hQ B hB href decode hdecode⟩

end DukePrimeDegree

end

end OAI
