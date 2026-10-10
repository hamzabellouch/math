import OAI.Analysis.Pureness.Completion.CompletedRankExhaustion
import OAI.Analysis.Pureness.Traces.UniformTraceBounds

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma continuous_matrixTrace_eval {k : ℕ} (a : MatrixStage A k) :
    Continuous (fun τ : TracialState A => matrixTrace τ a) := by
  simp only [matrixTrace_apply]
  exact continuous_finsetSum _ fun i _ => TracialState.continuous_eval (a i i)

lemma continuous_completedTraceValue_eval (k : ℕ) (a : CornerCompletion A) :
    Continuous (fun τ : TracialState A => completedTraceValue τ k a) :=
  ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_matrixTrace_eval _))

theorem lowerSemicontinuous_completedRootRank (a : CornerCompletion A) :
    LowerSemicontinuous (fun τ : TracialState A => completedRootRank τ a) := by
  unfold completedRootRank completedDiagonalWeight
  apply lowerSemicontinuous_iSup
  intro j
  apply lowerSemicontinuous_iSup
  intro k
  exact (continuous_completedTraceValue_eval k _).lowerSemicontinuous

lemma isOpen_lt_completedRootRank (a : CornerCompletion A) (F : TracialState A → ℝ≥0∞)
    (hF : Continuous F) : IsOpen {τ : TracialState A | F τ < completedRootRank τ a} := by
  have ho : IsOpen (⋃ j : ℕ, ⋃ k : ℕ, {τ : TracialState A |
      F τ < completedTraceValue τ k (nonUnitalRoot a j)}) :=
    isOpen_iUnion fun j => isOpen_iUnion fun k => isOpen_lt hF (continuous_completedTraceValue_eval k _)
  convert ho using 2
  ext τ
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, completedRootRank, completedDiagonalWeight, lt_iSup_iff]

theorem uniform_completedCompression_index (a : CornerCompletion A) (ha : 0 ≤ a)
    (F : TracialState A → ℝ≥0∞) (hF : Continuous F)
    (hgap : ∀ τ, F τ < completedRootRank τ a) :
    ∃ k : ℕ, ∀ τ, F τ < completedRootRank τ (completedCornerCut A (k + 1) a) := by
  apply uniform_strict_index F (fun k τ => completedRootRank τ (completedCornerCut A (k + 1) a))
  · intro k
    exact isOpen_lt_completedRootRank _ F hF
  · intro τ
    exact completedRootRank_cut_monotone τ a ha
  · intro τ
    rw [← completedRootRank_eq_iSup_cuts τ a ha]
    exact hgap τ

lemma completedCompression_eventually_ne_zero (a : CornerCompletion A) (ha0 : a ≠ 0) :
    ∃ K : ℕ, ∀ k ≥ K, completedCornerCut A (k + 1) a ≠ 0 := by
  have hs : Tendsto (fun k : ℕ => k + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b, fun k hk => hk.trans (Nat.le_succ k)⟩
  have ht := (completedCornerCut_tendsto A a).comp hs
  have he : ∀ᶠ k in atTop, completedCornerCut A (k + 1) a ≠ 0 :=
    ht.eventually (isOpen_compl_singleton.mem_nhds ha0)
  exact eventually_atTop.mp he

theorem exists_nonzero_completedCompression_rank_gap (w : CornerCompletion A)
    (hw : 0 ≤ w) (hw0 : w ≠ 0) (F : TracialState A → ℝ≥0∞) (hF : Continuous F)
    (hgap : ∀ τ, F τ < completedRootRank τ w) :
    ∃ k : ℕ, completedCornerCut A (k + 1) w ≠ 0 ∧
      ∀ τ, F τ < completedRootRank τ (completedCornerCut A (k + 1) w) := by
  obtain ⟨k, hk⟩ := uniform_completedCompression_index w hw F hF hgap
  obtain ⟨K, hK⟩ := completedCompression_eventually_ne_zero w hw0
  refine ⟨max k K, hK _ (le_max_right _ _), fun τ => ?_⟩
  exact (hk τ).trans_le (completedRootRank_cut_monotone τ w hw (le_max_left k K))
end CuntzPureness

end

end OAI
