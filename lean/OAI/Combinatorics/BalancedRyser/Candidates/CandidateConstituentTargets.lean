import OAI.Combinatorics.BalancedRyser.Candidates.CandidatePrescribedLine
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateValidityWitness

namespace OAI

namespace Balanced.CandidateConstituent

noncomputable section
open scoped Classical BigOperators
open CandidatePrescribed CandidateValidityWitness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem mem_successfulCodes_iff (M : MergedPairs F) (l : Line F) (c : Code F) :
    c ∈ successfulCodes M l ↔ SuccessfulOn M ⟨c.1, c.2⟩ l := by
  simp only [successfulCodes, alignedCodes, Finset.mem_filter, Finset.mem_univ,
    true_and]
  simp only [CandidatePrescribed.Eligible, SuccessfulOn]
  tauto

def constituentTargetCodes (M : MergedPairs F) (g : Direction F) : Finset (Code F) :=
  successfulCodes M (constituent M g false) ∪
    successfulCodes M (constituent M g true)

theorem mem_constituentTargetCodes_iff (M : MergedPairs F) (g : Direction F)
    (c : Code F) : c ∈ constituentTargetCodes M g ↔
    ∃ l : Line F, l.1 = g ∧ SuccessfulOn M ⟨c.1, c.2⟩ l ∧ l ∈ constituentLines M := by
  constructor
  · intro hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact ⟨constituent M g false, rfl, (mem_successfulCodes_iff M _ c).mp hc,
        Finset.mem_image.mpr ⟨(g, false), Finset.mem_univ _, rfl⟩⟩
    · exact ⟨constituent M g true, rfl, (mem_successfulCodes_iff M _ c).mp hc,
        Finset.mem_image.mpr ⟨(g, true), Finset.mem_univ _, rfl⟩⟩
  · rintro ⟨l, hdir, hs, hline⟩
    obtain ⟨s, heq⟩ := (constituent_target_iff M l).mp hline
    rw [hdir] at heq
    rw [heq] at hs
    cases s
    · exact Finset.mem_union_left _ ((mem_successfulCodes_iff M _ c).mpr hs)
    · exact Finset.mem_union_right _ ((mem_successfulCodes_iff M _ c).mpr hs)

theorem expected_random_constituent_eq_of_mem (old : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (hg : g ∈ old) (s : Bool) :
    (∑ M : MergedPairs F, (exposedLaw old a M).toReal *
      ((successfulCodes M (constituent M g s)).card : ℝ)) =
    ∑ M : MergedPairs F, (exposedLaw old a M).toReal *
      ((successfulCodes M (constituent a g s)).card : ℝ) := by
  apply Finset.sum_congr rfl
  intro M _
  by_cases hM : ∀ d, d ∈ old → M d = a d
  · have hline : constituent M g s = constituent a g s := by
      simp only [constituent, hM g hg]
    rw [hline]
  · have hz : exposedLaw old a M = 0 :=
      PMF.filter_apply_eq_zero_of_notMem (PartialAlignment.canonical_exposure_supported old a) hM
    simp only [hz, ENNReal.toReal_zero, zero_mul]

theorem expected_random_constituent_le_of_mem (old : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (hg : g ∈ old) (s : Bool)
    (m : ℕ) (hm : old.card ≤ m) :
    (∑ M : MergedPairs F, (exposedLaw old a M).toReal *
      ((successfulCodes M (constituent M g s)).card : ℝ)) ≤
      20480 * ((m : ℝ) + 1)^4 := by
  rw [expected_random_constituent_eq_of_mem old a g hg s]
  exact expected_successfulCodes_le_of_card_le old a (constituent a g s) m hm

theorem expected_constituentTargetCodes_le_of_mem (old : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (hg : g ∈ old)
    (m : ℕ) (hm : old.card ≤ m) :
    (∑ M : MergedPairs F, (exposedLaw old a M).toReal *
      ((constituentTargetCodes M g).card : ℝ)) ≤
      40960 * ((m : ℝ) + 1)^4 := by
  have hf := expected_random_constituent_le_of_mem old a g hg false m hm
  have ht := expected_random_constituent_le_of_mem old a g hg true m hm
  calc
    _ ≤ ∑ M : MergedPairs F, (exposedLaw old a M).toReal *
        (((successfulCodes M (constituent M g false)).card : ℝ) +
          ((successfulCodes M (constituent M g true)).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro M _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact_mod_cast Finset.card_union_le
        (successfulCodes M (constituent M g false))
        (successfulCodes M (constituent M g true))
    _ = (∑ M : MergedPairs F, (exposedLaw old a M).toReal *
        ((successfulCodes M (constituent M g false)).card : ℝ)) +
        (∑ M : MergedPairs F, (exposedLaw old a M).toReal *
        ((successfulCodes M (constituent M g true)).card : ℝ)) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ _ := by linarith

end
end Balanced.CandidateConstituent

end OAI
