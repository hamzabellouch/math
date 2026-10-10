import OAI.Analysis.Pureness.Divisibility.ExtendedSandwichRanks
import OAI.Analysis.Pureness.Divisibility.SharedRankAddition
import OAI.Analysis.Pureness.Cuntz.SharedCuntzBridge

namespace OAI
noncomputable section
open scoped CStarAlgebra ENNReal
namespace CuntzPureness
open CuntzTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[simp] theorem sharedRankHom_completed (τ : TracialState A) (a : Positive (CornerCompletion A)) :
    sharedRankHom τ (completedSharedClass a) = completedRootRank τ a.1 := by
  rw [completedSharedClass, sharedRankHom_mk]
  exact congrArg (completedRootRank τ) (sharedMatrixEquiv.apply_symm_apply a.1)

theorem exists_completed_repetition (a : Positive (CornerCompletion A)) (n : ℕ) :
    ∃ c : Positive (CornerCompletion A), completedSharedClass c = n • completedSharedClass a ∧
      ∀ τ : TracialState A, completedRootRank τ c.1 = (n : ℝ≥0∞)*completedRootRank τ a.1 := by
  obtain ⟨c,hc⟩ := completedSharedClass_surjective (n • completedSharedClass a)
  refine ⟨c,hc,fun τ => ?_⟩
  have h := congrArg (sharedRankHom τ) hc
  simpa only [sharedRankHom_completed, sharedRankHom_nsmul] using h

theorem exists_shared_sandwich_compression_gaps (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hT : Nonempty (TracialState A))
    (a : Positive (CornerCompletion A)) (ha0 : a.1 ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ∃ b c d : Positive (CornerCompletion A), b.1 ≠ 0 ∧ d.1 ≠ 0 ∧
      completedSharedClass c = n • completedSharedClass b ∧
      completedSharedClass d = (n+1) • completedSharedClass b ∧
      ∀ (τ : TracialState A) (k : ℕ),
        completedRootRank τ (completedCornerCut A (k+1) c.1) < completedRootRank τ a.1 ∧
        completedRootRank τ (completedCornerCut A (k+1) a.1) < completedRootRank τ d.1 := by
  obtain ⟨b,hb,hb0,hr⟩ := exists_completed_strict_sandwich_ranks hsimple hinf hT a.1 a.2 ha0 n hn
  let bp : Positive (CornerCompletion A) := ⟨b,hb⟩
  obtain ⟨c,hc,hcr⟩ := exists_completed_repetition bp n
  obtain ⟨d,hd,hdr⟩ := exists_completed_repetition bp (n+1)
  have hg (τ : TracialState A) (k : ℕ) :
      completedRootRank τ (completedCornerCut A (k+1) c.1) < completedRootRank τ a.1 ∧
      completedRootRank τ (completedCornerCut A (k+1) a.1) < completedRootRank τ d.1 := by
    by_cases ht : completedRootRank τ a.1 = ⊤
    · have hdt : completedRootRank τ d.1 = ⊤ := by
        rw [hdr, (hr τ).1.mp ht]
        simp
      constructor
      · rw [ht]
        exact (completedRootRank_cut_le_size τ k c.1 c.2).trans_lt (by simp)
      · rw [hdt]
        exact (completedRootRank_cut_le_size τ k a.1 a.2).trans_lt (by simp)
    · obtain ⟨h1,h2⟩ := (hr τ).2 ht
      constructor
      · apply (completedRootRank_cut_le τ (k+1) c.1 c.2).trans_lt
        rw [hcr]
        exact h1
      · apply (completedRootRank_cut_le τ (k+1) a.1 a.2).trans_lt
        rw [hdr]
        exact h2
  have hd0 : d.1 ≠ 0 := by
    intro hz
    obtain ⟨τ⟩ := hT
    have h := (hg τ 0).2
    simp [hz] at h
  exact ⟨bp,c,d,hb0,hd0,hc,hd,hg⟩
end CuntzPureness

end

end OAI
