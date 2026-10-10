import OAI.NumberTheory.Ostmann.Construction.ConstituentPairComplexity
import OAI.NumberTheory.Ostmann.Construction.WordRootRange

namespace OAI

/-! # Counts for the actual ranges, including the reciprocal-product cutoff -/

namespace Ostmann
open scoped Classical

/-- The added root cutoff costs one test; all inherited tests are counted
on their actual binary history tree. -/
theorem expandedRootRanges_count_le {I σ : Type*}
    (role : I → CopyScheduleRole) (n K : ℕ)
    (words : CopyScheduleAtoms role n → List σ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (hK : ∀ j ≤ n, (ranges j).length ≤ K) :
    (expandedRootRanges role n words ranges).count ≤ K * (2 ^ (n + 1) - 1) := by
  exact WordRangeDecoration.count_le _ K
    (expandedScheduleRanges_count_bounded role _ ranges n K hK [] _)

theorem expandedRootRanges_cutoff_count_le {I σ : Type*}
    (role : I → CopyScheduleRole) (n K : ℕ)
    (words : CopyScheduleAtoms role n → List σ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (hK : ∀ j ≤ n, (ranges j).length ≤ K)
    (r : WordRange (ExpandedScheduledVariable σ n)) :
    ((expandedRootRanges role n words ranges).prependRoot r).count ≤
      K * (2 ^ (n + 1) - 1) + 1 := by
  rw [WordRangeDecoration.prependRoot_count]
  exact Nat.add_le_add_right (expandedRootRanges_count_le role n K words ranges hK) 1

/-- Both histories, with the extra cutoff on the left, share one constant
range-count bound and hence the linear bound used in the numerical estimate. -/
theorem expandedRootRanges_pair_linear_count {I σ : Type*}
    (role : I → CopyScheduleRole) (n K : ℕ)
    (words words' : CopyScheduleAtoms role n → List σ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (hK : ∀ j ≤ n, (ranges j).length ≤ K)
    (r : WordRange (ExpandedScheduledVariable σ n)) (m : ℝ) (hm : 0 ≤ m) :
    (((expandedRootRanges role n words ranges).prependRoot r).count : ℝ) ≤
      (K * (2 ^ (n + 1) - 1) + 1 : ℕ) * (1 + m) ∧
    ((expandedRootRanges role n words' ranges).count : ℝ) ≤
      (K * (2 ^ (n + 1) - 1) + 1 : ℕ) * (1 + m) := by
  have hL : (((expandedRootRanges role n words ranges).prependRoot r).count : ℝ) ≤
      (K * (2 ^ (n + 1) - 1) + 1 : ℕ) := by
    exact_mod_cast expandedRootRanges_cutoff_count_le role n K words ranges hK r
  have hR : ((expandedRootRanges role n words' ranges).count : ℝ) ≤
      (K * (2 ^ (n + 1) - 1) + 1 : ℕ) := by
    exact_mod_cast (expandedRootRanges_count_le role n K words' ranges hK).trans (Nat.le_add_right _ 1)
  have hb : ((K * (2 ^ (n + 1) - 1) + 1 : ℕ) : ℝ) ≤
      (K * (2 ^ (n + 1) - 1) + 1 : ℕ) * (1 + m) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)
  exact ⟨hL.trans hb, hR.trans hb⟩

/-- With linear atom sizes, the concrete word budget stays linear. -/
theorem constituent_word_budget_linear {I : Type*} [Fintype I]
    (n A S : ℕ) (s m : ℝ) (hs : (S : ℝ) ≤ s * (1 + m)) (hm : 0 ≤ m) :
    ((2 * 3 ^ n * Fintype.card I * S + A * S + 4 : ℕ) : ℝ) ≤
      (((2 * 3 ^ n * Fintype.card I + A : ℕ) : ℝ) * s + 4) * (1 + m) := by
  have hmult := mul_le_mul_of_nonneg_left hs
    (Nat.cast_nonneg (2 * 3 ^ n * Fintype.card I + A))
  push_cast at hmult ⊢
  nlinarith only [hm, hmult]

end Ostmann

end OAI
