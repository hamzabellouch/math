import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.FinOneMatrixTransport
import OAI.Analysis.JiangSu.CStarAlgebras.CompletedRootRank

namespace OAI

section

noncomputable section
namespace Pureness
open Filter Topology
open scoped ComplexOrder ENNReal NNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma completedRoot_tendsto {a : ℕ → CornerCompletion A} {b : CornerCompletion A}
    (ha : ∀ n, 0 ≤ a n) (hb : 0 ≤ b) (hb0 : b ≠ 0)
    (ht : Tendsto a atTop (𝓝 b)) (j : ℕ) :
    Tendsto (fun n => nonUnitalRoot (a n) j) atTop (𝓝 (nonUnitalRoot b j)) := by
  have hn : Tendsto (fun n => nonUnitalNormalize (a n)) atTop (𝓝 (nonUnitalNormalize b)) :=
    (ht.norm.inv₀ (norm_ne_zero_iff.mpr hb0)).smul ht
  have hw : Tendsto (fun n => nonUnitalNormalize (a n)) atTop
      (𝓝[{x : CornerCompletion A | 0 ≤ x}] (nonUnitalNormalize b)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hn, Eventually.of_forall (fun n => nonUnitalNormalize_nonneg _ (ha n))⟩
  have hc : Tendsto (fun x : CornerCompletion A => CFC.nnrpow x (((j : ℝ≥0) + 1)⁻¹))
      (𝓝[{x : CornerCompletion A | 0 ≤ x}] (nonUnitalNormalize b)) (𝓝 (nonUnitalRoot b j)) :=
    (CFC.continuousOn_nnrpow (((j : ℝ≥0) + 1)⁻¹)).continuousWithinAt (nonUnitalNormalize_nonneg b hb)
  exact hc.comp hw

theorem completedRootRank_le_of_tendsto (τ : TracialState A) {a : ℕ → CornerCompletion A}
    {b : CornerCompletion A} {r : ℝ≥0∞} (ha : ∀ n, 0 ≤ a n) (hb : 0 ≤ b)
    (ht : Tendsto a atTop (𝓝 b)) (hr : ∀ n, completedRootRank τ (a n) ≤ r) :
    completedRootRank τ b ≤ r := by
  by_cases hb0 : b = 0
  · simp only [hb0, completedRootRank_zero, zero_le]
  apply iSup_le
  intro j
  exact completedDiagonalWeight_le_of_tendsto τ (completedRoot_tendsto ha hb hb0 ht j)
    (fun n => (le_iSup (fun j => completedDiagonalWeight τ (nonUnitalRoot (a n) j)) j).trans (hr n))

theorem completedRootRank_cut_le_size (τ : TracialState A) (k : ℕ) (a : CornerCompletion A) (ha : 0 ≤ a) :
    completedRootRank τ (completedCornerCut A (k + 1) a) ≤ (k + 1 : ℕ) := by
  rw [← include_completedCompress, completedRootRank_include τ (k + 1) _ (completedCompress_nonneg _ a ha)]
  calc
    _ ≤ (k + 1 : ℕ) * (1 : ℝ≥0∞) := by
      unfold matrixRank
      simp only [Fintype.card_fin]
      gcongr
      exact normalizedRootRank_le_one _ _ (completedCompress_nonneg _ a ha)
    _ = _ := mul_one _

lemma completedRootRank_cut_monotone (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    Monotone (fun k : ℕ => completedRootRank τ (completedCornerCut A (k + 1) a)) := by
  intro k l h
  dsimp only
  rw [← include_completedCompress, ← include_completedCompress,
    completedRootRank_include τ (k + 1) _ (completedCompress_nonneg _ a ha),
    completedRootRank_include τ (l + 1) _ (completedCompress_nonneg _ a ha)]
  exact completedCompression_rank_monotone τ a ha h

theorem completedRootRank_le_iSup_cuts (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    completedRootRank τ a ≤ ⨆ k : ℕ, completedRootRank τ (completedCornerCut A (k + 1) a) := by
  have hs : Tendsto (fun k : ℕ => k + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b, fun k hk => hk.trans (Nat.le_succ k)⟩
  exact completedRootRank_le_of_tendsto τ (fun k => completedCornerCut_nonneg A (k + 1) a ha) ha
    ((completedCornerCut_tendsto A a).comp hs) (fun k => le_iSup (fun j : ℕ => completedRootRank τ (completedCornerCut A (j + 1) a)) k)

end Pureness

end
end

end OAI
