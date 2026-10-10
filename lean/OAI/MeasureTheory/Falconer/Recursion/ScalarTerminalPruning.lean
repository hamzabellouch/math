import OAI.MeasureTheory.Falconer.Estimates.ScalarGreedyPorousGain

namespace OAI

/-! Retaining one actual leaf per terminal cell removes a final run of
 nonporous levels. Its cost is the exact product of their branch counts. -/
namespace Falconer.Regularization

 theorem ScalarBranchingLevel.prune_upper {L : Finset (CellPath 1)} {a b k n c d : ℕ}
    (h : ScalarBranchingLevel L a b k n) (hab : a ≤ b) (hbc : b ≤ c)
    (F : CellPath 1 → Finset (CellPath 1))
    (hF : ∀ p ∈ L.image (List.take c), (F p).Nonempty ∧ F p ⊆ prefixChildren L c d p) :
    ScalarBranchingLevel (scalarPruneLeaves L c d F) a b k n := by
  classical
  refine ⟨h.exponent_le,h.level_lo,h.level_hi,?_,?_⟩
  · intro p hp
    rw [scalarPruneLeaves_upper_children L hab hbc F hF]
    exact h.children_card p (Finset.image_subset_image (scalarPruneLeaves_subset L c d F) hp)
  · intro p hp
    rw [scalarPruneLeaves_upper_children L hab hbc F hF]
    exact h.fork_geometry p (Finset.image_subset_image (scalarPruneLeaves_subset L c d F) hp)

 theorem scalar_terminal_pruning {N M t : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (d k n : ℕ → ℕ)
    (hd : Monotone d) (hdM : d M = N) (ht : t ≤ M)
    (hlevel : ∀ i < M, ScalarBranchingLevel L (d i) (d (i+1)) (k i) (n i)) :
    ∃ Q : Finset (CellPath 1), Q ⊆ L ∧ Q.Nonempty ∧
      L.card = 2^(∑ i ∈ Finset.Ico t M, k i)*Q.card ∧
      (∀ p ∈ Q.image (List.take (d t)), (prefixFiber Q (d t) p).card = 1) ∧
      (∀ i < t, ScalarBranchingLevel Q (d i) (d (i+1)) (k i) (n i)) := by
  classical
  have hm : ∀ p ∈ L.image (List.take (d M)), (prefixFiber L (d M) p).card = 1 := by
    rw [hdM]
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have hlen := (mem_cubePaths 1 N q).mp (hL hq)
    have htake : q.take N = q := by rw [← hlen,List.take_length]
    rw [htake,prefixFiber_leaf hL hq]
    simp
  obtain ⟨F,hF,hQne,hcost,_,hmQ⟩ := scalar_trimmed_uniform_block L hL hne d k hd
    (a := t) (c := t) le_rfl ht hdM.le
    (fun i hi => (hlevel i hi).children_card) hm 0
    (fun _ _ _ _ _ _ _ => abs_nonneg _)
  let Q := scalarPruneLeaves L (d t) (d M) F
  have hFn : ∀ p ∈ L.image (List.take (d t)),
      (F p).Nonempty ∧ F p ⊆ prefixChildren L (d t) (d M) p := by
    intro p hp
    exact ⟨Finset.card_pos.mp (by rw [(hF p hp).2]; omega),(hF p hp).1⟩
  refine ⟨Q,scalarPruneLeaves_subset L _ _ F,hQne,hcost,?_,?_⟩
  · simpa only [Finset.Ico_self,Finset.sum_empty,pow_zero,one_mul] using hmQ
  · intro i hi
    exact (hlevel i (hi.trans_le ht)).prune_upper (hd (Nat.le_succ i))
      (hd (by omega)) F hFn

end Falconer.Regularization

end OAI
