import OAI.NumberTheory.JointDickman.Probability.UniformResidueFibers
import OAI.NumberTheory.JointDickman.Amplification.OutsideCandidateMass

namespace OAI

/-! # Identifying conditional residue fibers with the candidate root model -/

namespace JointDickman
open Finset Classical

noncomputable def emptyBlockPrimeHit (M : ℕ) : (univ : Finset (Fin M)).powerset :=
  ⟨∅,by simp⟩

theorem blockPrimeHit_empty_iff (M p : ℕ) (r : ZMod p) :
    blockPrimeHit M p r = emptyBlockPrimeHit M ↔
      r ∉ univ.image (blockSiteRoot M p) := by
  constructor
  · intro h hr
    obtain ⟨i,_,hi⟩ := mem_image.mp hr
    have hm : i ∈ (blockPrimeHit M p r).val := by
      change i ∈ rootHitSet univ (blockSiteRoot M p) r
      simp [rootHitSet,hi]
    rw [h] at hm
    simp only [emptyBlockPrimeHit,Finset.notMem_empty] at hm
  · intro hr
    apply Subtype.ext
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hi' : blockSiteRoot M p i = r := (mem_filter.mp hi).2
    exact hr (mem_image.mpr ⟨i,mem_univ _,hi'⟩)

theorem blockPrimeFiber_empty (M p : ℕ) [NeZero p] :
    uniformFiber (blockPrimeHit M p) (emptyBlockPrimeHit M) =
      univ \ univ.image (blockSiteRoot M p) := by
  ext r
  simp only [uniformFiber,mem_filter,mem_univ,true_and,mem_sdiff,
    blockPrimeHit_empty_iff]

theorem emptyBlockPrimeFiber_pos {M p : ℕ} [NeZero p] (hp : M < p) :
    0 < (uniformFiber (blockPrimeHit M p) (emptyBlockPrimeHit M)).card := by
  rw [blockPrimeFiber_empty,card_sdiff_of_subset (subset_univ _),card_univ,
    ZMod.card,blockForbidden_card hp]
  omega

theorem blockPrimeImageMass (M p : ℕ) [NeZero p] (hp : M < p)
    (H : (univ : Finset (Fin M)).powerset) :
    uniformImageMass (blockPrimeHit M p) H =
      categoricalSubsetMass univ (fun _ : Fin M => 1/(p : ℝ)) H.val := by
  rw [uniformImageMass_eq_push]
  simpa only [ZMod.card] using congrFun (blockPrimeHit_pushMass M p hp) H

noncomputable def maskedCandidatePrimeHit {M : ℕ}
    (I : Finset (BlockCandidateIndex M)) (p : ℕ) [Fact p.Prime]
    (H : (univ : Finset (Fin M)).powerset) (r : ZMod p) : I.powerset :=
  if H = emptyBlockPrimeHit M then rootHitType I (candidateModRoot p) r else
    ⟨∅,by simp⟩

/-- At the empty site pattern, the conditional root law is exactly the
uniform residue law outside the forbidden classes. -/
theorem emptySite_candidate_push {M p : ℕ} [Fact p.Prime]
    (I : Finset (BlockCandidateIndex M)) (hp : M < p) (R : I.powerset) :
    finitePushMass (totalUniformConditionalMass (blockPrimeHit M p) (emptyBlockPrimeHit M))
      (rootHitType I (candidateModRoot p)) R = outsideCandidatePrimeMass I p R := by
  have hpos := emptyBlockPrimeFiber_pos hp
  have hn : (uniformFiber (blockPrimeHit M p) (emptyBlockPrimeHit M)).card ≠ 0 := hpos.ne'
  have hn' : (univ \ univ.image (blockSiteRoot M p)).card ≠ 0 := by
    rwa [blockPrimeFiber_empty] at hn
  have he (r : ZMod p) :
      totalUniformConditionalMass (blockPrimeHit M p) (emptyBlockPrimeHit M) r =
      if r ∈ univ \ univ.image (blockSiteRoot M p) then
        1/((univ \ univ.image (blockSiteRoot M p)).card : ℝ) else 0 := by
    simp only [totalUniformConditionalMass,blockPrimeFiber_empty,hn',ite_false,uniformConditionalMass,
      blockPrimeHit_empty_iff,blockPrimeFiber_empty,mem_sdiff,mem_univ,true_and]
  unfold outsideCandidatePrimeMass restrictedRootMass finitePushMass
  simp only [he]
  rw [sum_coe_sort (univ \ univ.image (blockSiteRoot M p))
    (fun r => if rootHitType I (candidateModRoot p) r = R then
      1/((univ \ univ.image (blockSiteRoot M p)).card : ℝ) else 0)]
  have hU : univ.filter (fun r : ZMod p => r ∈ univ \ univ.image (blockSiteRoot M p)) =
      univ \ univ.image (blockSiteRoot M p) := by ext r; simp
  have hs := sum_filter (s := univ)
    (p := fun r : ZMod p => r ∈ univ \ univ.image (blockSiteRoot M p))
    (f := fun r => if rootHitType I (candidateModRoot p) r = R then
      1/((univ \ univ.image (blockSiteRoot M p)).card : ℝ) else 0)
  rw [hU] at hs
  rw [hs]
  apply sum_congr rfl
  intro r _
  by_cases hr : r ∈ univ.image (blockSiteRoot M p) <;>
    by_cases hh : rootHitType I (candidateModRoot p) r = R <;> simp [hr,hh]

/-- Occupied classes have zero masked tests; empty classes retain their
actual conditional residue law. Both branches are exact identities. -/
theorem maskedCandidatePrimeHit_push {M p : ℕ} [Fact p.Prime]
    (I : Finset (BlockCandidateIndex M)) (hp : M < p)
    (H : (univ : Finset (Fin M)).powerset) (R : I.powerset) :
    finitePushMass (totalUniformConditionalMass (blockPrimeHit M p) H)
      (maskedCandidatePrimeHit I p H) R =
    if H = emptyBlockPrimeHit M then outsideCandidatePrimeMass I p R else
      (if R.val = ∅ then 1 else 0) := by
  by_cases hH : H = emptyBlockPrimeHit M
  · subst H
    have hf : maskedCandidatePrimeHit I p (emptyBlockPrimeHit M) =
        rootHitType I (candidateModRoot p) := by funext r; simp [maskedCandidatePrimeHit]
    rw [hf,ite_eq_left rfl]
    exact emptySite_candidate_push I hp R
  · simp only [maskedCandidatePrimeHit,hH,ite_false,finitePushMass]
    have he : (⟨∅,by simp⟩ : I.powerset) = R ↔ R.val = ∅ := by
      constructor
      · intro h; exact (congrArg Subtype.val h).symm
      · intro h; exact Subtype.ext h.symm
    simp only [he]
    by_cases hR : R.val = ∅
    · simp only [hR,ite_true]
      exact totalUniformConditionalMass_sum _ _
    · simp [hR]

end JointDickman

end OAI
