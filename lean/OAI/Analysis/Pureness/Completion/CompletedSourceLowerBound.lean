import OAI.Analysis.Pureness.Completion.CompletedSourceIncrements

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma positive_matrix_eq_zero_of_diagonal_sum_eq_zero {k : ℕ} (M : MatrixStage A k)
    (hM : 0 ≤ M) (hs : (∑ i : Fin k, M i i) = 0) : M = 0 := by
  have hd (i : Fin k) : M i i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => matrix_entry_nonneg M hM i)).mp hs i (Finset.mem_univ i)
  obtain ⟨x, hx⟩ := positive_square_factor M hM
  have hx0 : x = 0 := by
    ext j i
    have ht : (∑ j : Fin k, star (x j i) * x j i) = 0 := by
      simpa only [← hx, CStarMatrix.mul_apply, CStarMatrix.star_apply] using hd i
    have he : star (x j i) * x j i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => star_mul_self_nonneg (x j i))).mp ht j (Finset.mem_univ j)
    apply norm_eq_zero.mp
    have hn := congrArg norm he
    rw [CStarRing.norm_star_mul_self, norm_zero] at hn
    nlinarith [norm_nonneg (x j i)]
  rw [← hx, hx0, star_zero, zero_mul]

theorem exists_completedSourceU_ne_zero (a : CornerCompletion A) (ha : 0 ≤ a) (ha0 : a ≠ 0) :
    ∃ J : ℕ, completedSourceU a J ≠ 0 := by
  by_contra hn
  push Not at hn
  have hnpos := nonUnitalNormalize_nonneg a ha
  have hn0 : nonUnitalNormalize a ≠ 0 :=
    smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr ha0)) ha0
  obtain ⟨K, hK⟩ := completedCompression_eventually_ne_zero (nonUnitalNormalize a) hn0
  have hr0 : nonUnitalRoot a 0 = nonUnitalNormalize a := by
    simp only [nonUnitalRoot, Nat.cast_zero, zero_add, inv_one, CFC.nnrpow_eq_pow, CFC.nnrpow_one _ hnpos]
  have hsum : completedDiagonalSum (K + 1) (nonUnitalNormalize a) = 0 := by
    apply le_antisymm _ (completedDiagonalSum_nonneg _ _ hnpos)
    calc
      _ = completedDiagonalSum (K + 1) (nonUnitalRoot a 0) := by rw [hr0]
      _ ≤ completedDiagonalSum (K + 1) (nonUnitalRoot a K) :=
        completedDiagonalSum_mono _ (nonUnitalRoot_monotone a ha (Nat.zero_le K))
      _ = 0 := hn (K + 1)
  have hz := positive_matrix_eq_zero_of_diagonal_sum_eq_zero _
    (completedCompress_nonneg (K + 1) _ hnpos) hsum
  have hc0 : completedCornerCut A (K + 1) (nonUnitalNormalize a) = 0 := by
    rw [← include_completedCompress, hz, map_zero]
  exact hK K le_rfl hc0

theorem completedSourceU_uniform_lower_bound (hsimple : TopologicallySimple A)
    (hT : Nonempty (TracialState A)) (a : CornerCompletion A) (ha : 0 ≤ a) (ha0 : a ≠ 0) :
    ∃ J : ℕ, ∃ m : ℝ, 0 < m ∧
      (∀ τ : TracialState A, m ≤ (τ.functional (completedSourceU a J)).re) ∧
      ∀ τ : TracialState A, ENNReal.ofReal m ≤ completedRootRank τ a := by
  obtain ⟨J, hJ⟩ := exists_completedSourceU_ne_zero a ha ha0
  obtain ⟨m, hm, hb⟩ := uniform_positive_trace_lower_bound hsimple hT
    (completedSourceU a J) (completedSourceU_nonneg a J) hJ
  exact ⟨J, m, hm, hb, fun τ =>
    (ENNReal.ofReal_le_ofReal (hb τ)).trans (completedSourceU_trace_le τ a J)⟩
end CuntzPureness

end

end OAI
