import OAI.NumberTheory.DukePrimeDegree.Entropy.WholeFutureChain

namespace OAI

/-! # One predecessor restores exactly one level of the whole future -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

abbrev fullFutureSigma {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (r : ℕ) :
    MeasurableSpace Y :=
  ⨆ k : ℕ, observationSigma (fun x => Q (T^[r+k] x))

lemma fullFutureSigma_one {Y : Type*} (T : Y → Y) (Q : Y → ℕ) :
    fullFutureSigma T Q 1=
      MeasurableSpace.comap (entireFutureObservation T Q) inferInstance := by
  simpa only [fullFutureSigma,Nat.add_comm] using countableFutureSigma_eq_comap T Q

lemma fullFutureSigma_comap {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (r s : ℕ) :
    MeasurableSpace.comap (T^[r]) (fullFutureSigma T Q s)=fullFutureSigma T Q (r+s) := by
  unfold fullFutureSigma
  rw [MeasurableSpace.comap_iSup]
  apply iSup_congr
  intro k
  rw [←observationSigma_comp]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [←Function.iterate_add_apply]
  rw [show s+k+r=r+s+k by omega]

lemma fullFutureSigma_zero {Y : Type*} (T : Y → Y) (Q : Y → ℕ) :
    fullFutureSigma T Q 0=observationSigma Q ⊔ fullFutureSigma T Q 1 := by
  have H := (sup_iSup_nat_succ (fun k : ℕ => observationSigma (fun x => Q (T^[k] x)))).symm
  simpa only [fullFutureSigma,Nat.zero_add,Nat.add_zero,Function.iterate_zero_apply,
    Nat.add_comm] using H

lemma futureLabelBlock_shift_generate {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (r : ℕ) :
    (⨆ N, observationSigma (futureLabelBlock T Q N ∘ T^[r]))=
      fullFutureSigma T Q (r+1) := by
  simp_rw [observationSigma_comp]
  rw [←MeasurableSpace.comap_iSup,futureLabelBlock_sigma_generate,
    countableFutureSigma_eq_comap,←fullFutureSigma_one,fullFutureSigma_comap]

lemma futureLabelBlock_shift_monotone {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (r : ℕ) :
    Monotone (fun N => observationSigma (futureLabelBlock T Q N ∘ T^[r])) := by
  intro i j hij
  simp only [observationSigma_comp]
  exact MeasurableSpace.comap_mono (futureLabelBlock_sigma_monotone T Q hij)

theorem conditionalSigmaEntropy_chain_fullFuture
    {Y α β : Type*} [MeasurableSpace Y] [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Measurable T) (Q : Y → ℕ) (hQ : Measurable Q)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (R : Y → β) (hR : ∀ b, MeasurableSet {y | R y=b}) (r : ℕ) :
    conditionalSigmaEntropy μ (fun y => (P y,R y)) (fullFutureSigma T Q (r+1)) =
      conditionalSigmaEntropy μ P (fullFutureSigma T Q (r+1)) +
        conditionalSigmaEntropy μ R (fullFutureSigma T Q (r+1) ⊔ observationSigma P) := by
  have H := conditionalSigmaEntropy_chain_iSup_nat μ P hP R hR
    (fun N => futureLabelBlock T Q N ∘ T^[r])
    (fun N => (futureLabelBlock_measurable hT hQ N).comp (hT.iterate r))
    (futureLabelBlock_shift_monotone T Q r)
  simpa only [futureLabelBlock_shift_generate] using H

theorem conditionalSigmaEntropy_comp_preserving_fullFuture
    {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (Q : Y → ℕ) (hQ : Measurable Q)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a}) (r : ℕ) :
    conditionalSigmaEntropy μ (P ∘ T^[r]) (fullFutureSigma T Q (r+1)) =
      conditionalSigmaEntropy μ P (fullFutureSigma T Q 1) := by
  have H := conditionalSigmaEntropy_comp_preserving_iSup_nat μ (hT.iterate r) P hP
    (futureLabelBlock T Q) (futureLabelBlock_measurable hT.measurable hQ)
    (futureLabelBlock_sigma_monotone T Q) (futureLabelBlock_shift_monotone T Q r)
  simpa only [futureLabelBlock_shift_generate,futureLabelBlock_sigma_generate,
    countableFutureSigma_eq_comap,←fullFutureSigma_one] using H

theorem fullFutureSigma_predecessor {Y : Type*} {M : ℕ}
    (T : Y → Y) (Q : Y → ℕ) (B : Y → Fin M)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin M → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x) :
    fullFutureSigma T Q 0=fullFutureSigma T Q 1 ⊔ observationSigma B := by
  have ht : observationSigma (Q ∘ T) ≤ fullFutureSigma T Q 1 := by
    simpa only [Function.comp_def,Nat.add_zero,Function.iterate_one] using
      (le_iSup (fun k : ℕ => observationSigma (fun x => Q (T^[1+k] x))) 0)
  have hb : observationSigma B ≤ observationSigma Q ⊔ observationSigma (Q ∘ T) := by
    rw [←observationSigma_pair_eq]
    apply observationSigma_le_of_fiber_refinement
    intro x y hxy
    exact href x y (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  have hq : observationSigma Q ≤ observationSigma B ⊔ observationSigma (Q ∘ T) := by
    rw [←observationSigma_pair_eq]
    apply observationSigma_le_of_fiber_refinement
    intro x y hxy
    have hb : B x=B y := congrArg Prod.fst hxy
    have hq : Q (T x)=Q (T y) := congrArg Prod.snd hxy
    rw [←hdecode x,←hdecode y,hb,hq]
  rw [fullFutureSigma_zero]
  exact sup_le
    (hq.trans (sup_le le_sup_right (ht.trans le_sup_left))) le_sup_left |>.antisymm
      (sup_le le_sup_right (hb.trans (sup_le le_sup_left (ht.trans le_sup_right))))

theorem fullFutureSigma_predecessor_at {Y : Type*} {M : ℕ}
    (T : Y → Y) (Q : Y → ℕ) (B : Y → Fin M)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin M → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (r : ℕ) :
    fullFutureSigma T Q r=
      fullFutureSigma T Q (r+1) ⊔ observationSigma (B ∘ T^[r]) := by
  have H := congrArg (MeasurableSpace.comap (T^[r]))
    (fullFutureSigma_predecessor T Q B href decode hdecode)
  simpa only [MeasurableSpace.comap_sup,fullFutureSigma_comap,Nat.add_zero,
    ←observationSigma_comp] using H

end DukePrimeDegree

end

end OAI
