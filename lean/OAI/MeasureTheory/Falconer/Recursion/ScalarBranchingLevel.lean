import OAI.MeasureTheory.Falconer.Incidence.ScalarBlockPruning

namespace OAI

/-! The geometric data retained by scalar regularization at each block.
 Subsequent coarser pruning preserves this data exactly. -/
namespace Falconer.Regularization

structure ScalarBranchingLevel (L : Finset (CellPath 1)) (a b k n : ℕ) : Prop where
  exponent_le : k ≤ b-a
  level_lo : a ≤ n
  level_hi : n ≤ b
  children_card : ∀ p ∈ L.image (List.take a), (prefixChildren L a b p).card = 2^k
  fork_geometry : ∀ p ∈ L.image (List.take a), k = 0 ∨
    (a+3 < n ∧ n+6 ≤ b ∧
      (∀ q ∈ prefixChildren L a b p, ∀ r ∈ prefixChildren L a b p,
        q ≠ r → 8*(1/2:ℝ)^n < |scalarPathCenter q-scalarPathCenter r|) ∧
      ∃ q ∈ prefixChildren L a b p, ∃ r ∈ prefixChildren L a b p,
        q ≠ r ∧ |scalarPathCenter q-scalarPathCenter r| ≤ 16*(1/2:ℝ)^n)

 theorem ScalarBranchingLevel.prune {L : Finset (CellPath 1)} {a b k n c d : ℕ}
    (h : ScalarBranchingLevel L a b k n) (hcd : c ≤ d) (hda : d ≤ a)
    (K : CellPath 1 → Finset (CellPath 1)) :
    ScalarBranchingLevel (scalarPruneLeaves L c d K) a b k n := by
  classical
  refine ⟨h.exponent_le,h.level_lo,h.level_hi,?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rw [scalarPruneLeaves_lower_children L hcd hda K hq]
    exact h.children_card _ (Finset.mem_image_of_mem _ (scalarPruneLeaves_subset L c d K hq))
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rw [scalarPruneLeaves_lower_children L hcd hda K hq]
    exact h.fork_geometry _ (Finset.mem_image_of_mem _ (scalarPruneLeaves_subset L c d K hq))

 theorem scalar_block_pruning_level {N a b : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (hab : a ≤ b) (hb : b ≤ N)
    (m : ℕ) (hm : ∀ c ∈ L.image (List.take b), (prefixFiber L b c).card = m) :
    ∃ K : CellPath 1 → Finset (CellPath 1), ∃ k n : ℕ,
      let Q := scalarPruneLeaves L a b K
      Q.Nonempty ∧ Q ⊆ L ∧ L.card ≤ 2050*(b-a+1)^2*Q.card ∧
      ScalarBranchingLevel Q a b k n ∧
      ∀ p ∈ Q.image (List.take a), (prefixFiber Q a p).card = 2^k*m := by
  classical
  obtain ⟨K,k,n,hne',hsub,hcard,hdata⟩ := scalar_block_pruning L hL hne hab hb m hm
  let Q := scalarPruneLeaves L a b K
  obtain ⟨q,hq⟩ := hne'
  have hp := Finset.mem_image_of_mem (List.take a) hq
  have hd := (hdata _ hp).1
  refine ⟨K,k,n,⟨q,hq⟩,hsub,hcard,?_,fun p hp => (hdata p hp).2.2⟩
  refine ⟨hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1,?_,?_⟩
  · intro p hp
    rw [(hdata p hp).2.1]
    exact (hdata p hp).1.2.1
  · intro p hp
    rw [(hdata p hp).2.1]
    exact (hdata p hp).1.2.2.2.2.2.2

end Falconer.Regularization

end OAI
