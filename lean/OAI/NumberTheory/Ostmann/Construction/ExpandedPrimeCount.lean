import OAI.NumberTheory.Ostmann.Construction.ExpandedPrimeReplay
import OAI.NumberTheory.Ostmann.Construction.WordPrimeBounds

namespace OAI

/-! # The complete Y-prime check count is polynomial in the original word size -/

namespace Ostmann

open scoped Classical

theorem expandedYPrimeCoordinates_length {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth n M : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable V depth))
    (hc : ∀ i, (current i).length ≤ M) :
    (expandedYPrimeCoordinates role depth n current).length ≤
      3 ^ n * Fintype.card I * M := by
  have hY : Fintype.card (CopyScheduleY role n) ≤ 3 ^ n * Fintype.card I := by
    rw [← copyScheduleVertex_card n]
    exact Fintype.card_subtype_le _
  apply (list_flatMap_length_bound _ _ M (fun i _ =>
    (expandedOriginalWord_length _).trans (hc ⟨.inr i.val, i.property⟩))).trans
  simpa only [Finset.length_toList, Finset.card_univ] using Nat.mul_le_mul_right M hY

theorem expandedSchedulePrimes_count_bounded {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth n M : ℕ) (hn : n ≤ depth) (hM : 1 ≤ M)
    (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable V depth))
    (hc : ∀ i, (current i).length ≤ M) :
    (expandedSchedulePrimes role depth n path current).CountBounded
      (3 ^ depth * Fintype.card I * M) := by
  induction n generalizing path with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_, ih (by omega) _ _ (reverseCopyLabelMap_list_length role n true _ current M hM hc),
      ih (by omega) _ _ (reverseCopyLabelMap_list_length role n false _ current M hM hc)⟩
    exact (expandedYPrimeCoordinates_length role depth n M current hc).trans
      (Nat.mul_le_mul_right M (Nat.mul_le_mul_right (Fintype.card I)
        (Nat.pow_le_pow_right (by omega) (by omega))))

theorem expandedRootPrimes_count {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n M : ℕ) (hM : 1 ≤ M)
    (words : CopyScheduleAtoms role n → List V) (hw : ∀ i, (words i).length ≤ M) :
    (expandedSchedulePrimes role n n [] (fun i => (words i).map Sum.inl)).count ≤
      (3 ^ n * Fintype.card I * M) * (2 ^ n - 1) := by
  exact WordPrimeDecoration.count_le _ _
    (expandedSchedulePrimes_count_bounded role n n M le_rfl hM [] _
      (fun i => by simpa only [List.length_map] using hw i))

end Ostmann

end OAI
