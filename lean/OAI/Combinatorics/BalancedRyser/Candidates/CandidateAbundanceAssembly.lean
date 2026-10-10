import OAI.Combinatorics.BalancedRyser.Candidates.CandidateAbundance
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateConstituentTail
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateOppositeTransport
import OAI.Combinatorics.BalancedRyser.Candidates.CandidatePairMoments
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateValidityAssembly

namespace OAI

namespace Balanced.CandidateAbundanceAssembly

noncomputable section
open scoped Classical Topology
open Filter MeasureTheory TupleAlignment CandidateValidityAssembly CandidatePairs

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance abundanceAssemblyMeasurableSpace : MeasurableSpace F := ⊤

omit [DecidableEq F] in
private theorem measureReal_eq_offset (E : Set (MergedPairs F)) :
    (offsetLaw F).toMeasure.real E = offsetEventProbability E := by
  rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply _
    (Set.toFinite E).measurableSet]
  rfl

def slotLinearConstant : ℝ := 25 / pairLinearThreshold

theorem slotLinearConstant_pos : 0 < slotLinearConstant :=
  div_pos (by norm_num) pairLinearThreshold_pos

section Limits
variable (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
  [∀ n, DecidableEq (F n)]

omit [∀ n, DecidableEq (F n)] in
private theorem tendsto_good_of_bad (G B : ∀ n, Set (MergedPairs (F n)))
    (hcompl : ∀ n, G n = (B n)ᶜ)
    (hbad : Tendsto (fun n => offsetEventProbability (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => offsetEventProbability (G n)) atTop (𝓝 1) := by
  have heq (n : ℕ) : offsetEventProbability (G n) =
      1 - offsetEventProbability (B n) := by
    rw [hcompl n, offsetEventProbability, pmf_outerReal_compl]
    rfl
  simpa only [heq, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub hbad

theorem tendsto_successful_roots
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∀ g, 8 * Fintype.card (F n) ≤ rootSuccessCount g M}) atTop (𝓝 1) := by
  simpa only [measureReal_eq_offset,
    CandidateExposure.successfulTupleCount_eq_rootSuccessCount] using
      CandidateExposure.successfulTupleCount_all_tendsto_one F hq

theorem tendsto_square_fibers
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∀ g, (rootFiberSquareCount M g : ℝ) ≤
        pairLinearThreshold * Fintype.card (F n)}) atTop (𝓝 1) := by
  have hqR : Tendsto (fun n => (Fintype.card (F n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hbad : Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∃ g, pairLinearThreshold * Fintype.card (F n) <
        (rootFiberSquareCount M g : ℝ)}) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) ?_
      (hqR.const_div_atTop (2 * pairCenteredMomentConstant 0 2))
    intro n
    simpa only [measureReal_eq_offset, offsetEventProbability] using
      (rootFiberSquareCount_any_upper_tail (F := F n))
  apply tendsto_good_of_bad F _ _ (fun n => ?_) hbad
  ext M
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_lt]

theorem tendsto_constituent_losses
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∀ g, (CandidatePrescribed.constituentTargetCodes M g).card ≤ Fintype.card (F n)})
      atTop (𝓝 1) := by
  have hbad : Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∃ g, Fintype.card (F n) < (CandidatePrescribed.constituentTargetCodes M g).card})
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) ?_
      (CandidateConstituentTail.tendsto_some_direction_tail F hq)
    intro n
    apply pmf_outerReal_mono (offsetLaw (F n))
    rintro M ⟨g, hg⟩
    refine ⟨g, ?_⟩
    have hq1 : (1 : ℝ) ≤ Fintype.card (F n) := by
      exact_mod_cast Fintype.card_pos (α := F n)
    have hp : (Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ) ≤ Fintype.card (F n) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (1 / 100 : ℝ) ≤ 1)
    exact hp.trans (by exact_mod_cast le_of_lt hg)
  apply tendsto_good_of_bad F _ _ (fun n => ?_) hbad
  ext M
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_lt]

theorem tendsto_candidateSlots_of_witness_tails
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    (hopp : Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∃ g, Fintype.card (F n) < (oppositeFailures M g).card}) atTop (𝓝 0))
    (hext : Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∃ g, Fintype.card (F n) < (externalFailures M g).card}) atTop (𝓝 0)) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∀ s, slotLinearConstant * Fintype.card (F n) ≤ ((candidateSlot M s).card : ℝ) ∧
        (candidateSlot M s).card ≤ Fintype.card (F n)}) atTop (𝓝 1) := by
  let H (n : ℕ) : Set (MergedPairs (F n)) :=
    {M | ∀ g, 8 * Fintype.card (F n) ≤ rootSuccessCount g M}
  let Y (n : ℕ) : Set (MergedPairs (F n)) :=
    {M | ∀ g, (rootFiberSquareCount M g : ℝ) ≤ pairLinearThreshold * Fintype.card (F n)}
  let C (n : ℕ) : Set (MergedPairs (F n)) :=
    {M | ∀ g, (CandidatePrescribed.constituentTargetCodes M g).card ≤ Fintype.card (F n)}
  let O (n : ℕ) : Set (MergedPairs (F n)) :=
    {M | ∀ g, (oppositeFailures M g).card ≤ Fintype.card (F n)}
  let E (n : ℕ) : Set (MergedPairs (F n)) :=
    {M | ∀ g, (externalFailures M g).card ≤ Fintype.card (F n)}
  have hO : Tendsto (fun n => offsetEventProbability (O n)) atTop (𝓝 1) := by
    apply tendsto_good_of_bad F _ _ (fun n => ?_) hopp
    ext M
    simp only [O, Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_lt]
  have hE : Tendsto (fun n => offsetEventProbability (E n)) atTop (𝓝 1) := by
    apply tendsto_good_of_bad F _ _ (fun n => ?_) hext
    ext M
    simp only [E, Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_lt]
  have hHY := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    H Y (tendsto_successful_roots F hq) (tendsto_square_fibers F hq)
  have hHYC := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun n => H n ∩ Y n) C hHY (tendsto_constituent_losses F hq)
  have hHYCO := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun n => (H n ∩ Y n) ∩ C n) O hHYC hO
  have hall := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun n => ((H n ∩ Y n) ∩ C n) ∩ O n) E hHYCO hE
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hall tendsto_const_nhds
  · intro n
    apply pmf_outerReal_mono (offsetLaw (F n))
    rintro M ⟨⟨⟨⟨hH, hY⟩, hC⟩, hO⟩, hE⟩ s
    exact ⟨candidateSlot_lower_bound_of_failures M s pairLinearThreshold_pos
      (hH s.1) (hC s.1) (hO s.1) (hE s.1) (hY s.1), candidateSlot_card_le M s⟩
  · intro n
    change offsetEventProbability (F := F n) _ ≤ 1
    rw [← measureReal_eq_offset]
    exact measureReal_le_one

theorem tendsto_candidateSlots_of_external_tail
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    (hext : Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∃ g, Fintype.card (F n) < (externalFailures M g).card}) atTop (𝓝 0)) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∀ s, slotLinearConstant * Fintype.card (F n) ≤ ((candidateSlot M s).card : ℝ) ∧
        (candidateSlot M s).card ≤ Fintype.card (F n)}) atTop (𝓝 1) :=
  tendsto_candidateSlots_of_witness_tails F hq
    (tendsto_oppositeFailures_some_large F hq) hext

end Limits
end
end Balanced.CandidateAbundanceAssembly

end OAI
