import OAI.Combinatorics.BalancedRyser.Candidates.CandidatePrescribedLine

namespace OAI

namespace Balanced.CandidatePrescribed

noncomputable section
open scoped Classical
open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def constituentTargetCodes (M : MergedPairs F) (g : Direction F) : Finset (Code F) :=
  successfulCodes M (constituent M g false) ∪
    successfulCodes M (constituent M g true)

theorem exposedLaw_apply_eq_zero_of_ne (old : Finset (Direction F))
    (a M : MergedPairs F) (g : Direction F) (hg : g ∈ old)
    (hne : M g ≠ a g) : exposedLaw old a M = 0 := by
  apply PMF.filter_apply_eq_zero_of_notMem
  intro h
  exact hne (h g hg)

theorem expected_constituentTargetCodes_le (old : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (hg : g ∈ old) :
    (∑ M : MergedPairs F,
      (exposedLaw old a M).toReal * ((constituentTargetCodes M g).card : ℝ)) ≤
        40960 * ((old.card : ℝ) + 1) ^ 4 := by
  have hpoint (M : MergedPairs F) :
      (exposedLaw old a M).toReal * ((constituentTargetCodes M g).card : ℝ) ≤
      (exposedLaw old a M).toReal *
        (((successfulCodes M (constituent a g false)).card : ℝ) +
          ((successfulCodes M (constituent a g true)).card : ℝ)) := by
    by_cases he : M g = a g
    · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      have h := Finset.card_union_le
        (successfulCodes M (constituent M g false))
        (successfulCodes M (constituent M g true))
      simpa only [constituentTargetCodes, constituent, he, Nat.cast_add] using
        (show (((successfulCodes M (constituent M g false) ∪
          successfulCodes M (constituent M g true)).card : ℕ) : ℝ) ≤
          ((successfulCodes M (constituent M g false)).card : ℝ) +
          ((successfulCodes M (constituent M g true)).card : ℝ) by exact_mod_cast h)
    · rw [exposedLaw_apply_eq_zero_of_ne old a M g hg he]
      simp
  calc
    _ ≤ ∑ M : MergedPairs F, (exposedLaw old a M).toReal *
        (((successfulCodes M (constituent a g false)).card : ℝ) +
          ((successfulCodes M (constituent a g true)).card : ℝ)) :=
      Finset.sum_le_sum (fun M _ => hpoint M)
    _ = (∑ M : MergedPairs F, (exposedLaw old a M).toReal *
        ((successfulCodes M (constituent a g false)).card : ℝ)) +
        ∑ M : MergedPairs F, (exposedLaw old a M).toReal *
          ((successfulCodes M (constituent a g true)).card : ℝ) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ 20480 * ((old.card : ℝ) + 1) ^ 4 +
        20480 * ((old.card : ℝ) + 1) ^ 4 :=
      add_le_add (expected_successfulCodes_le old a (constituent a g false))
        (expected_successfulCodes_le old a (constituent a g true))
    _ = _ := by ring

theorem expected_constituentTargetCodes_le_of_card_le (old : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (hg : g ∈ old)
    (m : ℕ) (hm : old.card ≤ m) :
    (∑ M : MergedPairs F,
      (exposedLaw old a M).toReal * ((constituentTargetCodes M g).card : ℝ)) ≤
        40960 * ((m : ℝ) + 1) ^ 4 := by
  apply (expected_constituentTargetCodes_le old a g hg).trans
  gcongr

end
end Balanced.CandidatePrescribed

end OAI
