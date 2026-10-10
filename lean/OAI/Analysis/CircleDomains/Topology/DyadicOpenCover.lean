import OAI.Analysis.CircleDomains.Selection.DyadicPartition

namespace OAI

/-! A countable cover of an open time set by closed dyadic intervals inside it. -/

open Set
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_dyadicCell_mem (n : ℕ) (t : PathTime) :
    ∃ i : Fin (2 ^ n), t ∈ Icc (dyadicLeft n i) (dyadicRight n i) := by
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    have hl : dyadicLeft 0 0 = ⊥ := (dyadicNode_left 0 0).symm.trans (dyadicNode_zero 0)
    have hr : dyadicRight 0 0 = ⊤ := (dyadicNode_right 0 0).symm.trans (dyadicNode_last 0)
    rw [hl, hr, Icc_bot_top]
    exact mem_univ t
  | succ n ih =>
    obtain ⟨i, hi⟩ := ih
    rw [dyadicCell_split] at hi
    rcases hi with hi | hi
    · exact ⟨dyadicEven n i, hi⟩
    · exact ⟨dyadicOdd n i, hi⟩

abbrev DyadicInside (V : Set PathTime) :=
  {p : (Σ n : ℕ, Fin (2 ^ n)) // Icc (dyadicLeft p.1 p.2) (dyadicRight p.1 p.2) ⊆ V}

def insideDyadicCell {V : Set PathTime} (p : DyadicInside V) : Set PathTime :=
  Icc (dyadicLeft p.val.1 p.val.2) (dyadicRight p.val.1 p.val.2)

theorem iUnion_insideDyadicCell {V : Set PathTime} (hV : IsOpen V) :
    (⋃ p : DyadicInside V, insideDyadicCell p) = V := by
  apply Subset.antisymm
  · exact iUnion_subset fun p => p.property
  · intro t ht
    obtain ⟨n, hn⟩ := exists_dyadic_cells_inside hV (a := t) (b := t) (by simpa)
    obtain ⟨i, hi⟩ := exists_dyadicCell_mem n t
    have hgood := hn i ⟨t, hi, by simp⟩
    exact mem_iUnion.mpr ⟨⟨⟨n, i⟩, hgood⟩, hi⟩

end CircleDomainRigidity

end

end OAI
