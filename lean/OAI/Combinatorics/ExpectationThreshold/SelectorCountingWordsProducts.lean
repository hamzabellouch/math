import OAI.Combinatorics.ExpectationThreshold.SelectorCountingWords
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace OAI

/-!
# Products of counting-word weights

An arbitrary finite collection of row profiles has total counting-word weight
at most one when the nonnegative color weights have total mass at most one.
The coefficients are the actual cardinalities of words with each profile.
-/

open scoped BigOperators

namespace TalagrandThreshold

private theorem sum_prod_le_prod_sum_of_support {I A : Type*} [Fintype I]
    (S : I → Finset A) (w : I → A → ℝ)
    (hw : ∀ i a, 0 ≤ w i a)
    (hz : ∀ i a, a ∉ S i → w i a = 0) (E : Finset (I → A)) :
    (∑ n ∈ E, ∏ i, w i (n i)) ≤ ∏ i, ∑ a ∈ S i, w i a := by
  classical
  let P : Finset (I → A) := Fintype.piFinset S
  have hzero (n : I → A) (hn : n ∉ P) : (∏ i, w i (n i)) = 0 := by
    have hn' : ¬ ∀ i, n i ∈ S i := by
      simpa only [P, Fintype.mem_piFinset] using hn
    obtain ⟨i, hi⟩ := not_forall.mp hn'
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hz i (n i) hi)
  calc
    (∑ n ∈ E, ∏ i, w i (n i)) = ∑ n ∈ E ∩ P, ∏ i, w i (n i) := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro n hn hnot
      apply hzero n
      intro hnP
      exact hnot (Finset.mem_inter.mpr ⟨hn, hnP⟩)
    _ ≤ ∑ n ∈ P, ∏ i, w i (n i) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun n _ _ => Finset.prod_nonneg fun i _ => hw i (n i))
    _ = ∏ i, ∑ a ∈ S i, w i a := (Finset.prod_univ_sum S w).symm

/-- Summing the literal counting-word weights over any finite set of row
profiles is bounded by one. Neither the row type nor the color type needs
to be nonempty. -/
theorem sum_prod_wordCount_weight_le_one {I H : Type*} [Fintype I]
    [Fintype H] [DecidableEq H] (t : I → ℕ) (E : Finset (I → H → ℕ))
    (π : H → ℝ) (hπ : ∀ h, 0 ≤ π h) (hπsum : (∑ h, π h) ≤ 1) :
    (∑ n ∈ E, ∏ i, ((wordCount (t i) (n i) : ℝ) * ∏ h, π h ^ (n i h))) ≤ 1 := by
  classical
  have hπsum_nonneg : 0 ≤ ∑ h, π h := Finset.sum_nonneg fun h _ => hπ h
  calc
    (∑ n ∈ E, ∏ i, ((wordCount (t i) (n i) : ℝ) * ∏ h, π h ^ (n i h))) ≤
        ∏ i, ∑ n ∈ wordProfiles H (t i),
          (wordCount (t i) n : ℝ) * ∏ h, π h ^ (n h) := by
      refine sum_prod_le_prod_sum_of_support (I := I) (A := H → ℕ)
        (fun i => wordProfiles H (t i))
        (fun i (n : H → ℕ) => (wordCount (t i) n : ℝ) * ∏ h, π h ^ n h) ?_ ?_ E
      · intro i n
        exact mul_nonneg (Nat.cast_nonneg _)
          (Finset.prod_nonneg fun h _ => pow_nonneg (hπ h) _)
      · intro i n hn
        rw [wordCount_eq_zero_of_not_mem_wordProfiles (t i) n hn]
        simp
    _ = ∏ i, (∑ h, π h) ^ (t i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact sum_wordCount_weight (t i) π
    _ ≤ 1 := Finset.prod_le_one₀
      (fun i _ => pow_nonneg hπsum_nonneg (t i))
      (fun _ _ => pow_le_one₀ hπsum_nonneg hπsum)

end TalagrandThreshold

end OAI
