import OAI.Combinatorics.BalancedRyser.Incidence.AffineDirectionCounting
import OAI.Combinatorics.BalancedRyser.Probability.TupleExposure

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem card_targets_with_fixed_position_le_one (M : MergedPairs F) (T : FourTuple F)
    (old : Finset (Direction F)) (p : Point F) (i : Fin 4)
    (hi : i ∈ fixedGeneratorPositions (oldGeneratorIndices T old))
    (haway : tuplePoint M T i ≠ p) :
    (Finset.univ.filter (fun g : Direction F =>
      ∃ N : MergedPairs F, (∀ d ∈ old, ∀ b, M d b = N d b) ∧
        ∀ k : Fin 4, OnLine (tuplePoint N T k) (lineThrough g p))).card ≤ 1 := by
  have hsub :
      Finset.univ.filter (fun g : Direction F =>
        ∃ N : MergedPairs F, (∀ d ∈ old, ∀ b, M d b = N d b) ∧
          ∀ k : Fin 4, OnLine (tuplePoint N T k) (lineThrough g p)) ⊆
        Finset.univ.filter (fun g => OnLine (tuplePoint M T i) (lineThrough g p)) := by
    intro g hg
    obtain ⟨_, N, hMN, halign⟩ := Finset.mem_filter.mp hg
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [tuplePoint_eq_of_fixedGeneratorPosition M N T old hMN i hi]
    exact halign i
  exact (Finset.card_le_card hsub).trans_eq
    (card_directions_to_point p (tuplePoint M T i) haway.symm)

end
end Balanced

end OAI
