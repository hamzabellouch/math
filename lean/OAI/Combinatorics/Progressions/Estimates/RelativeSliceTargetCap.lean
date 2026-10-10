import OAI.Combinatorics.Progressions.Probability.RelativeFullSliceLaw

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem RelativePatchSliceConclusion.target_lt_one_on_box
    {X : Type*} [Fintype X] [DecidableEq X] {s : ℕ} {N : X → ℕ}
    {f : (X → ℤ) → ℝ} {target cost : ℝ} {rankBound : ℕ}
    (h : RelativePatchSliceConclusion s N f target rankBound cost)
    (hf : ∀ x ∈ integerBox N, f x ≤ 1) : target < 1 := by
  obtain ⟨q,_,S,d,A,_,_,_,hscore⟩ := h
  by_contra hnot
  have ht : 1 ≤ target := le_of_not_gt hnot
  have hnonpos : relativePatchSliceScore S f target A ≤ 0 := by
    unfold relativePatchSliceScore
    rw [Finset.expect_eq_sum_div_card]
    apply div_nonpos_of_nonpos_of_nonneg
    · apply Finset.sum_nonpos
      intro u _
      apply mul_nonpos_of_nonpos_of_nonneg _ (A.value_mem_Icc _).1
      have hfu := hf _ (S.fullSlicePointInIntegerBox u).property
      change f (fun i => ((S.point u i).val : ℤ)) ≤ 1 at hfu
      linarith
    · exact Nat.cast_nonneg _
  exact (not_le_of_gt (Real.exp_pos (-cost))) (hscore.trans hnonpos)

end Erdos3

end

end OAI
