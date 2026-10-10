import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorEntropyLimit
import OAI.NumberTheory.DukePrimeDegree.Entropy.WholeFutureChain
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalSigmaOrder
import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableShannonInformation

namespace OAI

/-! # Finite auxiliary observations in the predecessor entropy bound -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem predecessor_factor_entropyRate_le
    {Y α : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (P : Y → α) (hP : Measurable P)
    (hfactor : ∀ x y, Q x=Q y → P x=P y) :
    observationEntropyRate μ T P ≤ conditionalSigmaEntropy μ B
      (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) := by
  apply le_of_tendsto_of_tendsto
    (conditional_boundary_entropy_rate μ hT P
      (fun a => hP (measurableSet_singleton a)) Q hQ)
    (predecessor_word_conditional_rate μ hT Q hQ B hB href decode hdecode)
  apply Eventually.of_forall
  intro N
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply conditionalSigmaEntropy_le_of_fiber_refinement μ (Q ∘ T^[N])
    (hQ.comp (hT.measurable.iterate N)) (orbitName T P N)
    (measurable_pi_iff.mpr fun i => hP.comp (hT.measurable.iterate i.val)) (orbitName T B N)
    (measurable_pi_iff.mpr fun i => hB.comp (hT.measurable.iterate i.val))
  intro x y hterm hword
  have hh := predecessor_word_recovers T Q B decode hdecode hterm
    (fun k hk => congrFun hword ⟨k,hk⟩)
  funext i
  exact hfactor _ _ (hh i.val i.isLt.le)

lemma conditionalSigmaEntropy_wholeFuture_le_observationEntropy
    {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Measurable T) (Q : Y → ℕ) (hQ : Measurable Q)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a}) :
    conditionalSigmaEntropy μ P
      (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) ≤
        observationEntropy μ P := by
  have hlim := conditionalSigmaEntropy_tendsto_iSup μ P
    (fun N => observationSigma (futureLabelBlock T Q N))
    (futureLabelBlock_sigma_monotone T Q)
    (fun N => (futureLabelBlock_measurable hT hQ N).comap_le)
  rw [futureLabelBlock_sigma_generate,countableFutureSigma_eq_comap] at hlim
  apply le_of_tendsto hlim
  exact Eventually.of_forall fun N => conditional_countable_le_observationEntropy
    μ P hP (futureLabelBlock T Q N) (futureLabelBlock_measurable hT hQ N)

/-- The finite auxiliary label contributes only its one-step Shannon
entropy; the main term is conditioned on the combined entire future. -/
theorem predecessor_auxiliary_entropyRate_le
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    {L : ℕ} (R : Y → Fin (L+1)) (hR : Measurable R) (K : ℕ) :
    observationEntropyRate μ T (heightClip Q K) ≤
      conditionalSigmaEntropy μ B
        (MeasurableSpace.comap
          (entireFutureObservation T (fun x => Encodable.encode (Q x,R x))) inferInstance) +
      observationEntropy μ R := by
  classical
  let W : Y → ℕ := fun x => Encodable.encode (Q x,R x)
  have hW : Measurable W := (measurable_of_countable Encodable.encode).comp (hQ.prodMk hR)
  let e := Fintype.equivFin (Fin (M+1) × Fin (L+1))
  let C : Y → Fin (Fintype.card (Fin (M+1) × Fin (L+1))+1) :=
    fun x => (e (B x,R x)).castSucc
  have hC : Measurable C := (measurable_of_finite (fun p => (e p).castSucc)).comp
    (hB.prodMk hR)
  have hparts {x y : Y} (h : W x=W y) : Q x=Q y ∧ R x=R y :=
    Prod.mk.inj (Encodable.encode_injective h)
  have hrefC : ∀ x y, W x=W y → W (T x)=W (T y) → C x=C y := by
    intro x y hxy hTxy
    have hh := hparts hxy
    dsimp only [C]
    rw [href x y hh.1 (hparts hTxy).1,hh.2]
  let dec : ℕ → Fin (Fintype.card (Fin (M+1) × Fin (L+1))+1) → ℕ := fun q b =>
    let p := Fin.lastCases (motive := fun _ => Fin (M+1) × Fin (L+1)) (0,0) e.symm b
    Encodable.encode (decode ((Encodable.decode (α := ℕ × Fin (L+1)) q).getD (0,0)).1 p.1,p.2)
  have hdec (x : Y) : dec (W (T x)) (C x)=W x := by
    simp only [dec,W,C,Fin.lastCases_castSucc,Equiv.symm_apply_apply,
      Encodable.encodek,Option.getD_some,hdecode]
  have hfirst := predecessor_factor_entropyRate_le μ hT W hW C hC hrefC dec hdec
    (heightClip Q K) (heightClip_measurable hQ K) (fun x y h => by
      apply Fin.ext
      change min (Q x) K=min (Q y) K
      rw [(hparts h).1])
  have hpair : Measurable (fun x => (B x,R x)) := hB.prodMk hR
  have hrec := conditionalSigmaEntropy_le_of_fiber_refinement μ
    (entireFutureObservation T W) (entireFutureObservation_measurable hT.measurable hW)
    C hC (fun x => (B x,R x)) hpair (fun x y _ h => by
      dsimp only [C]
      rw [h])
  have hchain := conditionalSigmaEntropy_chain_wholeFuture μ hT.measurable W hW
    B (fun a => hB (measurableSet_singleton a))
    R (fun a => hR (measurableSet_singleton a))
  have hcond := conditionalSigmaEntropy_antitone μ R
    (fun a => hR (measurableSet_singleton a))
    (m := MeasurableSpace.comap (entireFutureObservation T W) inferInstance)
    (n := MeasurableSpace.comap (entireFutureObservation T W) inferInstance ⊔ observationSigma B)
    le_sup_left (sup_le (entireFutureObservation_measurable hT.measurable hW).comap_le
      (observationSigma_le B (fun a => hB (measurableSet_singleton a))))
  have hobs := conditionalSigmaEntropy_wholeFuture_le_observationEntropy μ hT.measurable W hW
    R (fun a => hR (measurableSet_singleton a))
  exact hfirst.trans (hrec.trans (hchain.le.trans (add_le_add le_rfl (hcond.trans hobs))))

end DukePrimeDegree

end

end OAI
