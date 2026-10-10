import OAI.NumberTheory.DukePrimeDegree.Entropy.AuxiliaryPredecessorEntropy

namespace OAI

/-! # Countable auxiliary observations with finite Shannon entropy

Increasing finite clippings recover the exact combined future sigma
algebra. The entropy cost is bounded by the full countable Shannon sum.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma observationSigma_encoded_pair {Y α β : Type*} [Encodable α] [Encodable β]
    (P : Y → α) (Q : Y → β) :
    observationSigma (fun x => Encodable.encode (P x,Q x)) =
      observationSigma P ⊔ observationSigma Q := by
  rw [←observationSigma_pair_eq]
  apply le_antisymm
  · apply observationSigma_le_of_fiber_refinement
    intro x y h
    exact congrArg Encodable.encode h
  · apply observationSigma_le_of_fiber_refinement
    intro x y h
    exact Encodable.encode_injective h

lemma auxiliaryFutureSigma_eq {Y : Type*} (T : Y → Y) (Q R : Y → ℕ) (L : ℕ) :
    MeasurableSpace.comap
      (entireFutureObservation T (fun x => Encodable.encode (Q x,heightClip R L x)))
      inferInstance =
    ⨆ k : ℕ, observationSigma (fun x => Q (T^[k+1] x)) ⊔
      observationSigma (heightClip (fun x => R (T^[k+1] x)) L) := by
  rw [←countableFutureSigma_eq_comap]
  congr 1
  funext k
  exact observationSigma_encoded_pair _ _

lemma auxiliaryFutureSigma_monotone {Y : Type*} (T : Y → Y) (Q R : Y → ℕ) :
    Monotone (fun L => MeasurableSpace.comap
      (entireFutureObservation T (fun x => Encodable.encode (Q x,heightClip R L x)))
      inferInstance) := by
  intro L J hLJ
  dsimp only
  rw [auxiliaryFutureSigma_eq,auxiliaryFutureSigma_eq]
  exact iSup_mono (fun k => sup_le_sup_left (heightClip_sigma_monotone _ hLJ) _)

lemma auxiliaryFutureSigma_generate {Y : Type*} (T : Y → Y) (Q R : Y → ℕ) :
    (⨆ L, MeasurableSpace.comap
      (entireFutureObservation T (fun x => Encodable.encode (Q x,heightClip R L x)))
      inferInstance) =
    MeasurableSpace.comap
      (entireFutureObservation T (fun x => Encodable.encode (Q x,R x))) inferInstance := by
  simp_rw [auxiliaryFutureSigma_eq]
  rw [iSup_comm]
  simp_rw [iSup_sup_eq,iSup_const,heightClip_sigma_generate]
  rw [←countableFutureSigma_eq_comap]
  simp_rw [observationSigma_encoded_pair]
  rw [iSup_sup_eq]
  rfl

/-- A finite-entropy auxiliary observation may be adjoined at a cost of
its Shannon entropy, even when the main countable observation has
infinite Shannon entropy. -/
theorem predecessor_countable_auxiliary_entropyRate_le
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (R : Y → ℕ) (hR : Measurable R)
    (hfinite : Summable (fun n => Real.negMulLog (μ.real {x | R x=n})))
    (K : ℕ) :
    observationEntropyRate μ T (heightClip Q K) ≤
      conditionalSigmaEntropy μ B
        (MeasurableSpace.comap
          (entireFutureObservation T (fun x => Encodable.encode (Q x,R x))) inferInstance) +
      ∑' n, Real.negMulLog (μ.real {x | R x=n}) := by
  let m := fun L => MeasurableSpace.comap
    (entireFutureObservation T (fun x => Encodable.encode (Q x,heightClip R L x)))
    inferInstance
  have hm (L : ℕ) : m L ≤ ‹MeasurableSpace Y› :=
    (entireFutureObservation_measurable hT.measurable
      ((measurable_of_countable Encodable.encode).comp
        (hQ.prodMk (heightClip_measurable hR L)))).comap_le
  have hlim := conditionalSigmaEntropy_tendsto_iSup μ B m
    (auxiliaryFutureSigma_monotone T Q R) hm
  rw [auxiliaryFutureSigma_generate] at hlim
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (hlim.add_const _)
  apply Eventually.of_forall
  intro L
  have H := predecessor_auxiliary_entropyRate_le μ hT Q hQ B hB href decode hdecode
    (heightClip R L) (heightClip_measurable hR L) K
  have hc := finite_recode_entropy_le_countable_information μ R
    (fun n => hR (measurableSet_singleton n)) hfinite
    (heightClip (id : ℕ → ℕ) L)
    (fun a => heightClip_measurable hR L (measurableSet_singleton a))
  exact H.trans (add_le_add le_rfl hc)

end DukePrimeDegree

end

end OAI
