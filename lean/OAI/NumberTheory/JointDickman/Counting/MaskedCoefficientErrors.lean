import OAI.NumberTheory.JointDickman.Counting.CoefficientDigitEvents
import OAI.NumberTheory.JointDickman.Amplification.TrimmedCandidateRoots

namespace OAI

/-! # Restoring coefficient-prime tests in the masked comparison model -/

namespace JointDickman
open Finset PublishedInputs Classical

theorem maskedPrimeHit_probability {M p : ℕ} [Fact p.Prime]
    (I : Finset (BlockCandidateIndex M)) (H : (univ : Finset (Fin M)).powerset)
    (hp : M < p) (hhalf : 2*M ≤ p) {e : BlockCandidateIndex M} (he : e ∈ I) :
    finiteProbability (totalUniformConditionalMass (blockPrimeHit M p) H)
      (fun r => e ∈ (maskedCandidatePrimeHit I p H r).val) ≤ 2/(p : ℝ) := by
  rw [← finitePushMass_probability _ (maskedCandidatePrimeHit I p H)
    (fun R : I.powerset => e ∈ R.val)]
  have hm : finitePushMass (totalUniformConditionalMass (blockPrimeHit M p) H)
      (maskedCandidatePrimeHit I p H) =
      (fun R => if H = emptyBlockPrimeHit M then outsideCandidatePrimeMass I p R
        else (if R.val = ∅ then 1 else 0)) := by
    funext R
    exact maskedCandidatePrimeHit_push I hp H R
  rw [hm]
  by_cases hH : H = emptyBlockPrimeHit M
  · simp only [hH,ite_true]
    have hh := restrictedRootMass_hit_le I (candidateModRoot p)
      (univ \ univ.image (blockSiteRoot M p)) he
    have hc : (univ \ univ.image (blockSiteRoot M p)).card = p-M := by
      rw [card_sdiff_of_subset (subset_univ _),card_univ,ZMod.card,blockForbidden_card hp]
    rw [hc] at hh
    exact hh.trans (unoccupied_reciprocal_estimates p M hp hhalf).1
  · simp only [hH,ite_false,finiteProbability]
    have hz : (∑ R : I.powerset, if e ∈ R.val then (if R.val = ∅ then (1 : ℝ) else 0) else 0) = 0 := by
      apply sum_eq_zero
      intro R _
      by_cases hr : R.val = ∅ <;> simp [hr]
    rw [hz]
    positivity

noncomputable def conditionalResidueMass {B M : ℕ}
    [∀ p : auxiliaryPrimes B, NeZero p.val] (H : BlockPrimePatterns B M)
    (r : ∀ p : auxiliaryPrimes B, ZMod p.val) : ℝ :=
  finiteProductMass (fun p : auxiliaryPrimes B => totalUniformConditionalMass (blockPrimeHit M p.val) (H p)) r

noncomputable def maskedCoefficientTest {B M : ℕ} (I : Finset (BlockCandidateIndex M))
    (H : BlockPrimePatterns B M) (e : BlockCandidateIndex M) (p : ℕ)
    (r : ∀ p : auxiliaryPrimes B, ZMod p.val) : Prop :=
  if hp : p ∈ auxiliaryPrimes B then
    e ∈ (@maskedCandidatePrimeHit M I p ⟨auxiliaryPrimes_prime B p hp⟩ (H ⟨p,hp⟩) (r ⟨p,hp⟩)).val
  else False

theorem masked_coefficient_single_bound {B M p : ℕ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (I : Finset (BlockCandidateIndex M)) (H : BlockPrimePatterns B M)
    {e : BlockCandidateIndex M} (he : e ∈ I) (hp : p ∈ auxiliaryPrimes B)
    (hsize : M < p) (hhalf : 2*M ≤ p) :
    finiteProbability (conditionalResidueMass H) (maskedCoefficientTest I H e p) ≤ 2/(p : ℝ) := by
  let q : auxiliaryPrimes B := ⟨p,hp⟩
  let : Fact p.Prime := ⟨auxiliaryPrimes_prime B p hp⟩
  let a := fun q : auxiliaryPrimes B => totalUniformConditionalMass (blockPrimeHit M q.val) (H q)
  let f := fun r : ZMod p => if e ∈ (maskedCandidatePrimeHit I p (H q) r).val then (1 : ℝ) else 0
  have ha : ∀ q : auxiliaryPrimes B, ∑ r, a q r = 1 := fun q => totalUniformConditionalMass_sum _ _
  have hb : finiteExpectation (a q) f ≤ 2/(p : ℝ) := by
    have h := maskedPrimeHit_probability I (H q) hsize hhalf he
    rw [finiteProbability_eq_indicator_mean] at h
    convert h using 1
    apply congrArg (finiteExpectation (a q))
    funext r
    by_cases hr : e ∈ (maskedCandidatePrimeHit I p (H q) r).val <;> simp [f,hr]
  have hc := (finiteProduct_expectation_coordinate a ha q f).trans_le hb
  rw [finiteProbability_eq_indicator_mean]
  convert hc using 1
  apply congrArg (finiteExpectation (conditionalResidueMass H))
  funext r
  have ht : maskedCoefficientTest I H e p r ↔
      e ∈ (maskedCandidatePrimeHit I p (H q) (r q)).val := by
    simp [maskedCoefficientTest,hp,q]
  by_cases hr : e ∈ (maskedCandidatePrimeHit I p (H q) (r q)).val <;> simp [f,ht,hr]

def MaskedCoefficientEvent {B M : ℕ} (I : Finset (BlockCandidateIndex M))
    (H : BlockPrimePatterns B M) (r : ∀ p : auxiliaryPrimes B, ZMod p.val) : Prop :=
  ∃ e ∈ I, ∃ p ∈ candidateCoefficientPrimes B e, maskedCoefficientTest I H e p r

theorem masked_coefficient_event_bound {B L T H M : ℕ} {τ C : ℝ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B) (I : Finset (BlockCandidateIndex M))
    (he : ∀ e ∈ I, BlockCandidateAdmissible B L T H τ C e)
    (hsize : ∀ p ∈ auxiliaryPrimes B, M < p) (hhalf : ∀ p ∈ auxiliaryPrimes B, 2*M ≤ p)
    (S : BlockPrimePatterns B M) :
    finiteProbability (conditionalResidueMass S) (MaskedCoefficientEvent I S) ≤
      24*(I.card : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
  have hw : ∀ r, 0 ≤ conditionalResidueMass S r :=
    finiteProductMass_nonneg _ (fun _ => totalUniformConditionalMass_nonneg _ _)
  calc
    _ ≤ ∑ e ∈ I, finiteProbability (conditionalResidueMass S)
        (fun r => ∃ p ∈ candidateCoefficientPrimes B e, maskedCoefficientTest I S e p r) :=
      finiteProbability_exists_mem _ hw I _
    _ ≤ ∑ e ∈ I, ∑ p ∈ candidateCoefficientPrimes B e,
        finiteProbability (conditionalResidueMass S) (maskedCoefficientTest I S e p) :=
      sum_le_sum (fun e _ => finiteProbability_exists_mem _ hw _ _)
    _ ≤ ∑ e ∈ I, ∑ p ∈ candidateCoefficientPrimes B e, 2/(p : ℝ) := by
      apply sum_le_sum
      intro e hei
      apply sum_le_sum
      intro p hp
      have hpa := ((mem_candidateCoefficientPrimes e).mp hp).1
      exact masked_coefficient_single_bound I S hei hpa (hsize p hpa) (hhalf p hpa)
    _ = ∑ e ∈ I, 2*(∑ p ∈ candidateCoefficientPrimes B e, 1/(p : ℝ)) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro e _
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ ∑ _e ∈ I, 2*(12*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)) :=
      sum_le_sum (fun e hei => mul_le_mul_of_nonneg_left
        (candidateCoefficientPrimes_mass hB hT hM hP (he e hei)) (by norm_num))
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

end JointDickman

end OAI
